/-
# The share-budget lifting theorem: a heavy share buys a dominating subset through its atom

The single new selection rule this module lands: if one atom's SHARE
`s_a = t_a·ℓ_a` (weight times leverage, the chart diagonal of
`Gtz.projectionOfDesign`) meets the budget

    (rank − 1) + t_a  ≤  rank · s_a,

then a dominating `rank`-subset THROUGH that atom exists — conditionally on
weighted GTZ one rank down, and hence unconditionally at ranks 2 and 3, where
`Gtz.gtz_rank_one` and `Gtz.gtz_rank_two` close the downstairs obligation.

The mechanism, exactly (verified by exact rational arithmetic on 620 random
designs, the shipped witness corpus, and the external EPOINT minimizers before
landing): deflate at the pivot with `Gtz.exists_pivot_deflation`; the survivors'
projections onto the pivot's orthocomplement form an exact Parseval design one
dimension down at ANY positive weights (`Gtz.boostedPlaneDesign`), and the
weights are chosen BOOSTED,

    u_c  =  t_c · (E + (rank−1)·β_c²) / E,      E = ℓ_a − 1,   β_c = ⟨u_a, g_c⟩,

so that each downstairs weight prices in the cross term its atom will owe at
the lift.  The budget hypothesis is EXACTLY `∑ u_c ≤ 1` (the Parseval row law
`∑_c t_c β_c² = 1` makes the boost total `(rank−1)(1−s_a)/E`), so the boosted
weights, topped up by the leftover slack, are a legal weight vector; weighted
GTZ one rank down hands a dominating selection, and the per-term identity
`β_c² = (E/(rank−1) + β_c²)·(1 − t_c/u_c)` turns its margin into the
inverse-free discriminant certificate that
`Gtz.dominates_insert_of_projection_certificates` consumes.  No inverse, no
square root beyond the deflation scale, no eigenvalue.

Honest scope.  The budget at rank 3 reads `s_a ≥ (2 + t_a)/3 ≥ 13/18` at weight
`1/6` — the `ℚ(√5)` uniform tie's heaviest share is `11/18`, so this theorem
does NOT reach the balanced core of the open `(6,3)` cell; it closes the heavy-
share band from the top.  At the shipped boundary witnesses the hypothesis
fires with EQUALITY (`Gtz.splitSevenDesign` at share `3/4`, weight `1/4`;
`Gtz.orthoSplitDesign` at share `4/5`, weight `2/5`) and the conclusion holds
tight there, so the constant is sharp against the corpus.  The naive unboosted
lift (weights `t` downstairs, no correction) is FALSE — the tree records the
exact refutation in `Gtz.not_compressionLiftClaim` — which is why the boost is
load-bearing and priced exactly, not an estimate.

Relation to the shipped frontier objects: this is a PROVED instance of the
selection content that `Gtz.LiftingLemma` leaves open — the lemma's
pivot/subset data are produced here whenever one share clears the budget; the
open cell is exactly the regime where every share is below it.  The chart-side
reading of the same inequality is the block form of
`Gtz.dominates_iff_posSemidef_projectionBlock_finset` at the deflated point
`Gtz.deflatedChartMatrix`.
-/
import Mathlib
import Gtz.Reduction.LiftingLemma

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! ## Two scalar bricks: the AM–GM cross bound and the budgeted Cauchy–Schwarz -/

/-- The product-form AM–GM: a cross term whose square is dominated by a product
of nonnegatives is dominated by their sum.  The scalar heart of every
off-diagonal estimate below. -/
theorem two_mul_le_add_of_sq_le_mul {leftTerm rightTerm crossTerm : ℝ}
    (hleftNonneg : 0 ≤ leftTerm) (hrightNonneg : 0 ≤ rightTerm)
    (hsquareLe : crossTerm ^ 2 ≤ leftTerm * rightTerm) :
    2 * crossTerm ≤ leftTerm + rightTerm := by
  nlinarith [sq_nonneg (leftTerm - rightTerm), sq_nonneg (leftTerm + rightTerm),
    sq_nonneg (leftTerm + rightTerm - 2 * crossTerm)]

/-- **The budgeted Cauchy–Schwarz inequality.**  If every selected index pays
its own square against the shared budget through its slack rate —
`β_c² ≤ (H + β_c²)·ρ_c` — then the selection's cross sum obeys the
discriminant bound with total budget `∑ (H + β_c²)` and total slack
`∑ ρ_c γ_c²`.  Pointwise on ORDERED pairs after symmetrisation, so no
square roots and no case split on vanishing slack rates. -/
theorem sum_mul_sq_le_budget_mul {size : ℕ} (selection : Finset (Fin size))
    (budgetShare : ℝ) (overlap planeValue slackRate : Fin size → ℝ)
    (hbudgetNonneg : 0 ≤ budgetShare)
    (hslackNonneg : ∀ index ∈ selection, 0 ≤ slackRate index)
    (hperTerm : ∀ index ∈ selection,
      overlap index ^ 2 ≤ (budgetShare + overlap index ^ 2) * slackRate index) :
    (∑ index ∈ selection, overlap index * planeValue index) ^ 2
      ≤ (∑ index ∈ selection, (budgetShare + overlap index ^ 2))
          * (∑ index ∈ selection, slackRate index * planeValue index ^ 2) := by
  have hpointwise : ∀ leftIndex ∈ selection, ∀ rightIndex ∈ selection,
      2 * ((overlap leftIndex * planeValue leftIndex)
          * (overlap rightIndex * planeValue rightIndex))
        ≤ (budgetShare + overlap leftIndex ^ 2)
            * (slackRate rightIndex * planeValue rightIndex ^ 2)
          + (budgetShare + overlap rightIndex ^ 2)
            * (slackRate leftIndex * planeValue leftIndex ^ 2) := by
    intro leftIndex hleft rightIndex hright
    have hleftFactorNonneg : 0 ≤ (budgetShare + overlap leftIndex ^ 2)
        * (slackRate rightIndex * planeValue rightIndex ^ 2) :=
      mul_nonneg (by positivity)
        (mul_nonneg (hslackNonneg rightIndex hright) (sq_nonneg _))
    have hrightFactorNonneg : 0 ≤ (budgetShare + overlap rightIndex ^ 2)
        * (slackRate leftIndex * planeValue leftIndex ^ 2) :=
      mul_nonneg (by positivity)
        (mul_nonneg (hslackNonneg leftIndex hleft) (sq_nonneg _))
    have hbudgetProduct : overlap leftIndex ^ 2 * overlap rightIndex ^ 2
        ≤ ((budgetShare + overlap leftIndex ^ 2) * slackRate leftIndex)
          * ((budgetShare + overlap rightIndex ^ 2) * slackRate rightIndex) :=
      mul_le_mul (hperTerm leftIndex hleft) (hperTerm rightIndex hright)
        (sq_nonneg _) (le_trans (sq_nonneg _) (hperTerm leftIndex hleft))
    refine two_mul_le_add_of_sq_le_mul hleftFactorNonneg hrightFactorNonneg ?_
    calc ((overlap leftIndex * planeValue leftIndex)
            * (overlap rightIndex * planeValue rightIndex)) ^ 2
        = (overlap leftIndex ^ 2 * overlap rightIndex ^ 2)
            * (planeValue leftIndex ^ 2 * planeValue rightIndex ^ 2) := by ring
      _ ≤ (((budgetShare + overlap leftIndex ^ 2) * slackRate leftIndex)
            * ((budgetShare + overlap rightIndex ^ 2) * slackRate rightIndex))
            * (planeValue leftIndex ^ 2 * planeValue rightIndex ^ 2) :=
          mul_le_mul_of_nonneg_right hbudgetProduct
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = ((budgetShare + overlap leftIndex ^ 2)
            * (slackRate rightIndex * planeValue rightIndex ^ 2))
          * ((budgetShare + overlap rightIndex ^ 2)
            * (slackRate leftIndex * planeValue leftIndex ^ 2)) := by ring
  have hdouble : 2 * (∑ index ∈ selection, overlap index * planeValue index) ^ 2
      ≤ 2 * ((∑ index ∈ selection, (budgetShare + overlap index ^ 2))
          * (∑ index ∈ selection, slackRate index * planeValue index ^ 2)) := by
    calc 2 * (∑ index ∈ selection, overlap index * planeValue index) ^ 2
        = ∑ leftIndex ∈ selection, ∑ rightIndex ∈ selection,
            2 * ((overlap leftIndex * planeValue leftIndex)
              * (overlap rightIndex * planeValue rightIndex)) := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun leftIndex _ => Finset.mul_sum _ _ _
      _ ≤ ∑ leftIndex ∈ selection, ∑ rightIndex ∈ selection,
            ((budgetShare + overlap leftIndex ^ 2)
                * (slackRate rightIndex * planeValue rightIndex ^ 2)
              + (budgetShare + overlap rightIndex ^ 2)
                * (slackRate leftIndex * planeValue leftIndex ^ 2)) :=
          Finset.sum_le_sum fun leftIndex hleft =>
            Finset.sum_le_sum fun rightIndex hright =>
              hpointwise leftIndex hleft rightIndex hright
      _ = ∑ leftIndex ∈ selection, ∑ rightIndex ∈ selection,
            (budgetShare + overlap leftIndex ^ 2)
              * (slackRate rightIndex * planeValue rightIndex ^ 2)
          + ∑ leftIndex ∈ selection, ∑ rightIndex ∈ selection,
            (budgetShare + overlap rightIndex ^ 2)
              * (slackRate leftIndex * planeValue leftIndex ^ 2) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun leftIndex _ => Finset.sum_add_distrib
      _ = 2 * ((∑ index ∈ selection, (budgetShare + overlap index ^ 2))
          * (∑ index ∈ selection, slackRate index * planeValue index ^ 2)) := by
          rw [← Finset.sum_mul_sum]
          rw [Finset.sum_comm (s := selection) (t := selection)
            (f := fun leftIndex rightIndex => (budgetShare + overlap rightIndex ^ 2)
              * (slackRate leftIndex * planeValue leftIndex ^ 2))]
          rw [← Finset.sum_mul_sum]
          ring
  linarith

/-! ## The Parseval row law at an arbitrary probe -/

/-- **Parseval as a quadratic form**: the weighted squared overlaps of the whole
design against any probe resolve the probe's squared norm.  Specialised at a
scaled atom this is the row law `∑_c t_c β_c² = 1` the budget accounting
consumes. -/
theorem sum_weight_mul_sq_dotProduct {m k : ℕ} (D : WeightedDesign m k)
    (probe : Fin k → ℝ) :
    ∑ atomIndex, D.weight atomIndex * (D.atom atomIndex ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ probe := by
  calc ∑ atomIndex, D.weight atomIndex * (D.atom atomIndex ⬝ᵥ probe) ^ 2
      = ∑ atomIndex, probe ⬝ᵥ ((D.weight atomIndex • atomMatrix (D.atom atomIndex))
          *ᵥ probe) := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
          atom_form_eq_sq]
    _ = probe ⬝ᵥ ((∑ atomIndex, D.weight atomIndex • atomMatrix (D.atom atomIndex))
          *ᵥ probe) := by
        rw [Matrix.sum_mulVec, dotProduct_sum]
    _ = probe ⬝ᵥ probe := by rw [D.isParseval, Matrix.one_mulVec]

/-! ## The boosted plane design -/

/-- **The boosted plane design**: deflate every surviving atom along a
coisometry that kills the pivot, and carry ANY positive weight vector summing
to one on the survivors.  Parseval one dimension down is unconditional — the
deflated pivot contributes nothing, and each survivor's atom is rescaled by
`√(t_c/u_c)` so its weighted rank-one square is the original `t_c`-weighted
projected square.  The weight freedom is the whole point: the share-budget
theorem instantiates it at the boosted weights that price the lift. -/
noncomputable def boostedPlaneDesign {m k : ℕ} (D : WeightedDesign (m + 1) (k + 2))
    (pivot : Fin (m + 1)) (deflator : Matrix (Fin (k + 1)) (Fin (k + 2)) ℝ)
    (hcoisometry : deflator * deflatorᵀ = 1)
    (hkill : deflator *ᵥ D.atom pivot = 0)
    (downWeight : Fin (m + 1) → ℝ)
    (hdownPos : ∀ survivor : Fin m, 0 < downWeight (pivot.succAbove survivor))
    (hdownSum : ∑ survivor : Fin m, downWeight (pivot.succAbove survivor) = 1) :
    WeightedDesign m (k + 1) where
  atom survivor :=
    Real.sqrt (D.weight (pivot.succAbove survivor)
        / downWeight (pivot.succAbove survivor))
      • (deflator *ᵥ D.atom (pivot.succAbove survivor))
  weight survivor := downWeight (pivot.succAbove survivor)
  weight_pos := hdownPos
  weight_sum_one := hdownSum
  isParseval := by
    have hterm : ∀ survivor : Fin m,
        downWeight (pivot.succAbove survivor)
            • atomMatrix (Real.sqrt (D.weight (pivot.succAbove survivor)
                / downWeight (pivot.succAbove survivor))
              • (deflator *ᵥ D.atom (pivot.succAbove survivor)))
          = D.weight (pivot.succAbove survivor)
            • atomMatrix (deflator *ᵥ D.atom (pivot.succAbove survivor)) := by
      intro survivor
      rw [atomMatrix_smul, smul_smul,
        Real.sq_sqrt (div_nonneg (D.weight_pos _).le (hdownPos survivor).le),
        mul_div_cancel₀ _ (hdownPos survivor).ne']
    rw [Finset.sum_congr rfl fun survivor _ => hterm survivor]
    have hpivotTerm : D.weight pivot • atomMatrix (deflator *ᵥ D.atom pivot) = 0 := by
      rw [hkill]
      have hzeroAtom : atomMatrix (0 : Fin (k + 1) → ℝ) = 0 := by
        ext rowIndex colIndex
        simp [atomMatrix, Matrix.vecMulVec_apply]
      rw [hzeroAtom, smul_zero]
    have hsplit := Fin.sum_univ_succAbove
      (fun atomIndex => D.weight atomIndex • atomMatrix (deflator *ᵥ D.atom atomIndex))
      pivot
    have hconjugated : ∑ atomIndex, D.weight atomIndex
        • atomMatrix (deflator *ᵥ D.atom atomIndex)
        = deflator * (∑ atomIndex, D.weight atomIndex
            • atomMatrix (D.atom atomIndex)) * deflatorᵀ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun atomIndex _ => ?_
      rw [atomMatrix_conj, Matrix.mul_smul, Matrix.smul_mul]
    have hwhole : ∑ atomIndex, D.weight atomIndex
        • atomMatrix (deflator *ᵥ D.atom atomIndex) = 1 := by
      rw [hconjugated, D.isParseval, Matrix.mul_one, hcoisometry]
    rw [← sub_eq_zero]
    have hassembled := hsplit.symm.trans hwhole
    rw [hpivotTerm, zero_add] at hassembled
    rw [hassembled, sub_self]

/-! ## The share-budget theorem -/

/-- **THE SHARE-BUDGET LIFTING THEOREM** (general rank, conditional one rank
down).  If some atom's share `s_a = t_a·ℓ_a` clears the budget
`(rank−1) + t_a ≤ rank·s_a`, then weighted GTZ one rank down (at the exact
survivor count) produces a dominating `rank`-subset through that atom.  The
downstairs design is `Gtz.boostedPlaneDesign` at the boosted weights
`u_c = t_c(E + (rank−1)β_c²)/E`; the budget hypothesis is exactly `∑ u_c ≤ 1`;
the per-term identity `β_c² = (E/(rank−1) + β_c²)(1 − t_c/u_c)` feeds the
budgeted Cauchy–Schwarz, and `Gtz.dominates_insert_of_projection_certificates`
closes.  Verified adversarially by exact arithmetic before landing: 805
hypothesis firings across 620 exact rational designs plus the shipped corpus,
zero failures, with equality cases at `Gtz.splitSevenDesign` and
`Gtz.orthoSplitDesign`. -/
theorem exists_dominating_insert_of_share_budget {m k : ℕ}
    (D : WeightedDesign (m + 1) (k + 2)) (pivot : Fin (m + 1))
    (hdown : GtzWeighted m (k + 1))
    (hbudget : (k : ℝ) + 1 + D.weight pivot
      ≤ ((k : ℝ) + 2) * (D.weight pivot * leverageOf (D.atom pivot))) :
    ∃ C : Finset (Fin (m + 1)), C.card = k + 2 ∧ pivot ∈ C ∧ Dominates D C := by
  classical
  have hsurvivorCount : 0 < m := by
    have hrankLe := rank_le_of_design D
    omega
  have hrankPos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hweightPos := D.weight_pos pivot
  have hweightLt : D.weight pivot < 1 := by
    have hsplit := Fin.sum_univ_succAbove D.weight pivot
    have hfirstSurvivor : (0 : ℝ)
        < D.weight (pivot.succAbove ⟨0, hsurvivorCount⟩) := D.weight_pos _
    have hsurvivorLower : D.weight (pivot.succAbove ⟨0, hsurvivorCount⟩)
        ≤ ∑ survivor : Fin m, D.weight (pivot.succAbove survivor) :=
      Finset.single_le_sum (fun survivor _ => (D.weight_pos _).le)
        (Finset.mem_univ _)
    have htotal := D.weight_sum_one
    rw [hsplit] at htotal
    linarith
  have hleverageGt : 1 < leverageOf (D.atom pivot) := by
    by_contra hnot
    have hleverageLe : leverageOf (D.atom pivot) ≤ 1 := not_lt.mp hnot
    have hshareLe : D.weight pivot * leverageOf (D.atom pivot) ≤ D.weight pivot :=
      mul_le_of_le_one_right hweightPos.le hleverageLe
    nlinarith
  set excess := leverageOf (D.atom pivot) - 1 with hexcessDef
  have hexcessPos : 0 < excess := by rw [hexcessDef]; linarith
  have hatomNe : D.atom pivot ≠ 0 := by
    intro hzero
    have hlevZero : leverageOf (D.atom pivot) = 0 := by
      rw [hzero, leverageOf]
      simp
    linarith
  obtain ⟨scale, deflator, hscalePos, hcoisometry, hkill, hsplitCompletion,
    hunitNorm⟩ := exists_pivot_deflation D pivot hatomNe
  have hdotSelf : D.atom pivot ⬝ᵥ D.atom pivot = leverageOf (D.atom pivot) :=
    (dotProduct_self_eq_sum_sq (D.atom pivot)).trans rfl
  have hscaleSq : scale * (scale * leverageOf (D.atom pivot)) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hdotSelf]
      at hunitNorm
    exact hunitNorm
  have hpivotOverlapSq : ((scale • D.atom pivot) ⬝ᵥ D.atom pivot) ^ 2
      = leverageOf (D.atom pivot) := by
    rw [smul_dotProduct, smul_eq_mul, hdotSelf]
    nlinarith [hscaleSq]
  have hweightOverlapSum : ∑ atomIndex, D.weight atomIndex
      * ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2 = 1 := by
    have hflip : ∀ atomIndex : Fin (m + 1),
        ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2
          = (D.atom atomIndex ⬝ᵥ (scale • D.atom pivot)) ^ 2 := fun atomIndex => by
      rw [dotProduct_comm]
    rw [Finset.sum_congr rfl fun atomIndex _ => by rw [hflip]]
    rw [sum_weight_mul_sq_dotProduct D (scale • D.atom pivot)]
    exact hunitNorm
  have hsurvivorOverlapSum : ∑ survivor : Fin m,
      D.weight (pivot.succAbove survivor)
        * ((scale • D.atom pivot) ⬝ᵥ D.atom (pivot.succAbove survivor)) ^ 2
      = 1 - D.weight pivot * leverageOf (D.atom pivot) := by
    have hsplit := Fin.sum_univ_succAbove
      (fun atomIndex => D.weight atomIndex
        * ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2) pivot
    rw [hweightOverlapSum] at hsplit
    rw [hpivotOverlapSq] at hsplit
    linarith
  -- the boosted weights, their slack, and the downstairs weight vector
  set boost : Fin (m + 1) → ℝ := fun atomIndex =>
    D.weight atomIndex * (excess + ((k : ℝ) + 1)
      * ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2) / excess with hboostDef
  have hboostGe : ∀ atomIndex, D.weight atomIndex ≤ boost atomIndex := by
    intro atomIndex
    rw [hboostDef]
    rw [le_div_iff₀ hexcessPos]
    have hcrossNonneg : 0 ≤ ((k : ℝ) + 1)
        * ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2 :=
      mul_nonneg hrankPos.le (sq_nonneg _)
    nlinarith [(D.weight_pos atomIndex).le]
  have hboostPos : ∀ atomIndex, 0 < boost atomIndex := fun atomIndex =>
    lt_of_lt_of_le (D.weight_pos atomIndex) (hboostGe atomIndex)
  have hboostSum : ∑ survivor : Fin m, boost (pivot.succAbove survivor)
      = ((1 - D.weight pivot) * excess
          + ((k : ℝ) + 1) * (1 - D.weight pivot * leverageOf (D.atom pivot)))
        / excess := by
    rw [hboostDef]
    simp only
    rw [← Finset.sum_div]
    congr 1
    have hsurvivorWeightSum : ∑ survivor : Fin m,
        D.weight (pivot.succAbove survivor) = 1 - D.weight pivot := by
      have hsplit := Fin.sum_univ_succAbove D.weight pivot
      have htotal := D.weight_sum_one
      rw [hsplit] at htotal
      linarith
    have hexpand : ∀ survivor : Fin m,
        D.weight (pivot.succAbove survivor) * (excess + ((k : ℝ) + 1)
            * ((scale • D.atom pivot) ⬝ᵥ D.atom (pivot.succAbove survivor)) ^ 2)
          = D.weight (pivot.succAbove survivor) * excess
            + ((k : ℝ) + 1) * (D.weight (pivot.succAbove survivor)
              * ((scale • D.atom pivot) ⬝ᵥ D.atom (pivot.succAbove survivor)) ^ 2) :=
      fun survivor => by ring
    rw [Finset.sum_congr rfl fun survivor _ => hexpand survivor,
      Finset.sum_add_distrib, ← Finset.sum_mul, hsurvivorWeightSum,
      ← Finset.mul_sum, hsurvivorOverlapSum]
  set slack := 1 - ∑ survivor : Fin m, boost (pivot.succAbove survivor)
    with hslackDef
  have hslackNonneg : 0 ≤ slack := by
    rw [hslackDef, hboostSum, sub_nonneg, div_le_one hexcessPos]
    nlinarith [hbudget]
  set downWeight : Fin (m + 1) → ℝ := fun atomIndex =>
    boost atomIndex + slack / (m : ℝ) with hdownDef
  have hcastPos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hsurvivorCount
  have hspreadNonneg : 0 ≤ slack / (m : ℝ) := div_nonneg hslackNonneg hcastPos.le
  have hdownGeBoost : ∀ atomIndex, boost atomIndex ≤ downWeight atomIndex := by
    intro atomIndex
    rw [hdownDef]
    linarith [hspreadNonneg]
  have hdownGeWeight : ∀ atomIndex, D.weight atomIndex ≤ downWeight atomIndex :=
    fun atomIndex => (hboostGe atomIndex).trans (hdownGeBoost atomIndex)
  have hdownPos : ∀ survivor : Fin m,
      0 < downWeight (pivot.succAbove survivor) := fun survivor =>
    lt_of_lt_of_le (D.weight_pos _) (hdownGeWeight _)
  have hdownSum : ∑ survivor : Fin m, downWeight (pivot.succAbove survivor) = 1 := by
    rw [hdownDef]
    simp only
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hcastPos.ne',
      hslackDef]
    ring
  -- the downstairs design and its dominating selection
  obtain ⟨downSelection, hdownCard, hdownDominates⟩ :=
    hdown (boostedPlaneDesign D pivot deflator hcoisometry hkill downWeight
      hdownPos hdownSum)
  set subset := downSelection.image pivot.succAbove with hsubsetDef
  have hinjective : Function.Injective pivot.succAbove :=
    Fin.succAbove_right_injective
  have hnotMem : pivot ∉ subset := by
    rw [hsubsetDef]
    intro hmem
    obtain ⟨survivor, _, hcontra⟩ := Finset.mem_image.mp hmem
    exact Fin.succAbove_ne pivot survivor hcontra
  have hsubsetCard : subset.card = k + 1 := by
    rw [hsubsetDef, Finset.card_image_of_injective _ hinjective, hdownCard]
  have himageSum : ∀ valueAt : Fin (m + 1) → ℝ,
      ∑ atomIndex ∈ subset, valueAt atomIndex
        = ∑ survivor ∈ downSelection, valueAt (pivot.succAbove survivor) := by
    intro valueAt
    rw [hsubsetDef]
    exact Finset.sum_image fun _ _ _ _ hagree => hinjective hagree
  -- the downstairs domination, in projected coordinates
  have hdownForm : ∀ testVec : Fin (k + 1) → ℝ, testVec ⬝ᵥ testVec
      ≤ ∑ survivor ∈ downSelection,
          (D.weight (pivot.succAbove survivor)
              / downWeight (pivot.succAbove survivor))
            * ((deflator *ᵥ D.atom (pivot.succAbove survivor)) ⬝ᵥ testVec) ^ 2 := by
    intro testVec
    have hraw := sum_sq_ge_of_dominates hdownDominates testVec
    refine hraw.trans_eq (Finset.sum_congr rfl fun survivor _ => ?_)
    show ((Real.sqrt (D.weight (pivot.succAbove survivor)
        / downWeight (pivot.succAbove survivor))
        • (deflator *ᵥ D.atom (pivot.succAbove survivor))) ⬝ᵥ testVec) ^ 2 = _
    rw [smul_dotProduct, smul_eq_mul, mul_pow,
      Real.sq_sqrt (div_nonneg (D.weight_pos _).le (hdownPos survivor).le)]
  -- certificate 1: the projected subset dominates
  have hprojected : ∀ testVec : Fin (k + 1) → ℝ, testVec ⬝ᵥ testVec
      ≤ ∑ atomIndex ∈ subset, ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2 := by
    intro testVec
    refine (hdownForm testVec).trans ?_
    rw [himageSum fun atomIndex =>
      ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2]
    refine Finset.sum_le_sum fun survivor _ => ?_
    have hratioLe : D.weight (pivot.succAbove survivor)
        / downWeight (pivot.succAbove survivor) ≤ 1 :=
      (div_le_one (hdownPos survivor)).mpr (hdownGeWeight _)
    nlinarith [sq_nonneg ((deflator *ᵥ D.atom (pivot.succAbove survivor)) ⬝ᵥ testVec),
      hratioLe]
  -- certificate 2: the leverage floor
  have hfloor : 0 ≤ ((scale • D.atom pivot) ⬝ᵥ D.atom pivot) ^ 2
      + (∑ atomIndex ∈ subset,
          ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2) - 1 := by
    have hsquares : 0 ≤ ∑ atomIndex ∈ subset,
        ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2 :=
      Finset.sum_nonneg fun atomIndex _ => sq_nonneg _
    rw [hpivotOverlapSq]
    linarith
  -- certificate 3: the discriminant bound, from the budgeted Cauchy–Schwarz
  have hdiscriminant : ∀ testVec : Fin (k + 1) → ℝ,
      (∑ atomIndex ∈ subset, ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex)
          * ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec)) ^ 2
        ≤ (((scale • D.atom pivot) ⬝ᵥ D.atom pivot) ^ 2
              + (∑ atomIndex ∈ subset,
                  ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2) - 1)
            * ((∑ atomIndex ∈ subset,
                ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2)
              - testVec ⬝ᵥ testVec) := by
    intro testVec
    have hbudgetShareNonneg : 0 ≤ excess / ((k : ℝ) + 1) :=
      div_nonneg hexcessPos.le hrankPos.le
    have hslackRateNonneg : ∀ atomIndex ∈ subset,
        0 ≤ 1 - D.weight atomIndex / downWeight atomIndex := by
      intro atomIndex hmem
      have hdownPosHere : 0 < downWeight atomIndex := by
        obtain ⟨survivor, _, hagree⟩ := Finset.mem_image.mp (hsubsetDef ▸ hmem)
        rw [← hagree]
        exact hdownPos survivor
      have hratioLe : D.weight atomIndex / downWeight atomIndex ≤ 1 :=
        (div_le_one hdownPosHere).mpr (hdownGeWeight _)
      linarith
    have hperTerm : ∀ atomIndex ∈ subset,
        ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2
          ≤ (excess / ((k : ℝ) + 1)
              + ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2)
            * (1 - D.weight atomIndex / downWeight atomIndex) := by
      intro atomIndex hmem
      have hdownPosHere : 0 < downWeight atomIndex := by
        obtain ⟨survivor, _, hagree⟩ := Finset.mem_image.mp (hsubsetDef ▸ hmem)
        rw [← hagree]
        exact hdownPos survivor
      have hexact : (excess / ((k : ℝ) + 1)
            + ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2)
          * (1 - D.weight atomIndex / boost atomIndex)
          = ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2 := by
        rw [hboostDef]
        have hdenNe : excess + ((k : ℝ) + 1)
            * ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2 ≠ 0 := by
          positivity
        have hweightNe : D.weight atomIndex ≠ 0 := (D.weight_pos atomIndex).ne'
        field_simp
        ring
      have hratioMono : D.weight atomIndex / downWeight atomIndex
          ≤ D.weight atomIndex / boost atomIndex := by
        gcongr
        · exact (D.weight_pos atomIndex).le
        · exact hboostPos atomIndex
        · exact hdownGeBoost atomIndex
      have hfactorNonneg : 0 ≤ excess / ((k : ℝ) + 1)
          + ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2 := by positivity
      calc ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2
          = (excess / ((k : ℝ) + 1)
              + ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2)
            * (1 - D.weight atomIndex / boost atomIndex) := hexact.symm
        _ ≤ (excess / ((k : ℝ) + 1)
              + ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2)
            * (1 - D.weight atomIndex / downWeight atomIndex) := by
            refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
            linarith [hratioMono]
    have hkey := sum_mul_sq_le_budget_mul subset (excess / ((k : ℝ) + 1))
      (fun atomIndex => (scale • D.atom pivot) ⬝ᵥ D.atom atomIndex)
      (fun atomIndex => (deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec)
      (fun atomIndex => 1 - D.weight atomIndex / downWeight atomIndex)
      hbudgetShareNonneg hslackRateNonneg hperTerm
    have hbudgetTotal : ∑ atomIndex ∈ subset, (excess / ((k : ℝ) + 1)
          + ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2)
        = excess + ∑ atomIndex ∈ subset,
            ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, hsubsetCard, nsmul_eq_mul]
      have hcastNe : ((k : ℝ) + 1) ≠ 0 := hrankPos.ne'
      push_cast
      field_simp
    have hslackTotal : ∑ atomIndex ∈ subset,
          (1 - D.weight atomIndex / downWeight atomIndex)
            * ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2
        ≤ (∑ atomIndex ∈ subset,
            ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2)
          - testVec ⬝ᵥ testVec := by
      have hsplitTerms : ∑ atomIndex ∈ subset,
          (1 - D.weight atomIndex / downWeight atomIndex)
            * ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2
          = (∑ atomIndex ∈ subset,
              ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2)
            - ∑ atomIndex ∈ subset,
              (D.weight atomIndex / downWeight atomIndex)
                * ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2 := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun atomIndex _ => by ring
      rw [hsplitTerms,
        himageSum fun atomIndex => (D.weight atomIndex / downWeight atomIndex)
          * ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2]
      linarith [hdownForm testVec]
    have hbudgetTotalNonneg : 0 ≤ excess + ∑ atomIndex ∈ subset,
        ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2 :=
      add_nonneg hexcessPos.le
        (Finset.sum_nonneg fun atomIndex _ => sq_nonneg _)
    have hchain : (∑ atomIndex ∈ subset,
          ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex)
            * ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec)) ^ 2
        ≤ (excess + ∑ atomIndex ∈ subset,
            ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2)
          * ((∑ atomIndex ∈ subset,
              ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2)
            - testVec ⬝ᵥ testVec) := by
      calc (∑ atomIndex ∈ subset,
            ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex)
              * ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec)) ^ 2
          ≤ (∑ atomIndex ∈ subset, (excess / ((k : ℝ) + 1)
              + ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2))
            * (∑ atomIndex ∈ subset,
                (1 - D.weight atomIndex / downWeight atomIndex)
                  * ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2) := hkey
        _ ≤ (excess + ∑ atomIndex ∈ subset,
              ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2)
            * ((∑ atomIndex ∈ subset,
                ((deflator *ᵥ D.atom atomIndex) ⬝ᵥ testVec) ^ 2)
              - testVec ⬝ᵥ testVec) := by
            rw [hbudgetTotal]
            exact mul_le_mul_of_nonneg_left hslackTotal hbudgetTotalNonneg
    have hfloorForm : ((scale • D.atom pivot) ⬝ᵥ D.atom pivot) ^ 2
        + (∑ atomIndex ∈ subset,
            ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2) - 1
        = excess + ∑ atomIndex ∈ subset,
            ((scale • D.atom pivot) ⬝ᵥ D.atom atomIndex) ^ 2 := by
      rw [hpivotOverlapSq, hexcessDef]
      ring
    rw [hfloorForm]
    exact hchain
  refine ⟨insert pivot subset, ?_, Finset.mem_insert_self pivot subset, ?_⟩
  · rw [Finset.card_insert_of_notMem hnotMem, hsubsetCard]
  · exact dominates_insert_of_projection_certificates D pivot hsplitCompletion
      hkill subset hnotMem hprojected hfloor hdiscriminant

/-- **The rank-3 instance, unconditional**: a share above `(2 + t_a)/3` buys a
dominating triple through its atom — the downstairs obligation is closed by
the shipped `Gtz.gtz_rank_two`.  This is a proved selection rule inside the
open rank-3 cell: only designs with EVERY share below the budget can remain
counterexample candidates. -/
theorem exists_dominating_triple_of_share_budget {m : ℕ}
    (D : WeightedDesign (m + 1) 3) (pivot : Fin (m + 1))
    (hbudget : 2 + D.weight pivot
      ≤ 3 * (D.weight pivot * leverageOf (D.atom pivot))) :
    ∃ C : Finset (Fin (m + 1)), C.card = 3 ∧ pivot ∈ C ∧ Dominates D C :=
  exists_dominating_insert_of_share_budget (k := 1) D pivot (gtz_rank_two m)
    (by push_cast; linarith)

/-- **The rank-2 instance, unconditional**: a share above `(1 + t_a)/2` buys a
dominating pair through its atom, via the shipped `Gtz.gtz_rank_one`.  Not new
as a cell (rank 2 is closed by `Gtz.gtz_rank_two`), but it pins the budget
constant's behaviour one rank below the frontier. -/
theorem exists_dominating_pair_of_share_budget {m : ℕ}
    (D : WeightedDesign (m + 1) 2) (pivot : Fin (m + 1))
    (hbudget : 1 + D.weight pivot
      ≤ 2 * (D.weight pivot * leverageOf (D.atom pivot))) :
    ∃ C : Finset (Fin (m + 1)), C.card = 2 ∧ pivot ∈ C ∧ Dominates D C :=
  exists_dominating_insert_of_share_budget (k := 0) D pivot (gtz_rank_one m)
    (by push_cast; linarith)

end Gtz
