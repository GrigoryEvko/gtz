/-
# The uniform slice IS the 1997 statement at `n = 6`

`Gtz.spreadFloorCertificate_sizeInv_iff_uniform` collapses obligation two of
`Gtz.gtzWeightedAll_three_of_branches`, read at the right endpoint of the proved
weight-floor window, to a statement about UNIFORM-weight designs, and
`Gtz.subsetSum_univ_eq_size_smul_one_of_weight_eq_sizeInv` reads a uniform design as a
tight frame with frame constant `size`.  This file names the resulting obligation.

**It is `Gtz.GtzOriginal 6 3`** — the 1997 conjecture at its FIRST OPEN SHAPE.
`Gtz.gtz_original_of_le_five` closes every `n ≤ 5`, so `n = 6, k = 3` is the smallest
matrix shape for which the original problem is open, and the right-endpoint spread
obligation is exactly it, in both directions.

## Why this is not already in the tree

Both halves of the uniform bridge ship: `Gtz.original_of_weighted_single` sends
weighted GTZ at size `n` to the 1997 statement at `n` through `Gtz.rowDesign`, and
`Gtz.exists_dominates_of_gtzOriginal_uniform` sends the 1997 statement back to the
uniform designs.  What is missing is the observation that the FIRST of those needs only
the uniform designs — its hypothesis `Gtz.GtzWeighted n k` is used exactly once, on
`Gtz.rowDesign`, whose weights are definitionally `1/n`.  Weakening that hypothesis
turns the pair into a fixed-size equivalence, and the equivalence is what lets the
right-endpoint collapse be named.

`Gtz/Reduction/ConverseBridge.lean` states in terms that "NOTHING here proves or
disproves a fixed-size arrow `GtzOriginal n k → GtzWeighted n k`".  That remains true
and is not touched: the arrow proved here lands on the UNIFORM designs at size `n`, not
on all of them.

## What the identification buys

* The obligation is a question about a point of `Gr(3, ℝ⁶)`: NINE dimensions, against
  fourteen for the full `(6,3)` cell.
* It is CLOSED AND BOUNDED.  `Gtz.leverage_le_size_of_weight_eq_sizeInv` caps every
  leverage at `size`, and the tree's own
  `Gtz.spreadFloorCertificate_sixThree_sizeInv_of_closedResidue` already removes the
  parallel-pair hypothesis, so the region carries no open condition.  A margin-based
  branch and bound is therefore not excluded by non-compactness — only by the tie
  stratum inside, where the margin is exactly zero
  (`Gtz.uniformTieDesign_isTie`, uniform weight `1/6`).
* The complement of a triple is a triple, so `Gtz.dominates_iff_posSemidef_smul_one_sub_subsetSum_compl`
  applies to BOTH members of every 3–3 split: at this size the mirror law is total.

## Honest scope

This is a naming, not a discharge.  `Gtz.GtzOriginal 6 3` is open, and it is strictly
WEAKER than `Gtz.GtzWeighted 6 3` — the tree's `Gtz.gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three`
needs the 1997 statement at EVERY size, not at six.  The right-endpoint collapse also
carries the degeneracy the shipped correction records: whatever leaves the spread branch
arrives in the dust branch, which at this floor is weighted GTZ on the non-uniform
designs.  So this file sharpens what obligation two is, and says nothing about whether
the split at the right endpoint is a good idea.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.MirrorLaw
import Gtz.Reduction.Reductions
import Gtz.Reduction.ConverseBridge
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.WeightFloorWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The fixed-size uniform equivalence -/

/-- **The 1997 statement at size `n` follows from its uniform slice.**  The shipped
`Gtz.original_of_weighted_single` consumes `Gtz.GtzWeighted n k` at exactly one design,
`Gtz.rowDesign`, whose weights are definitionally `1/n`; the body below is that proof
with the hypothesis weakened to the uniform designs and nothing else changed. -/
theorem gtzOriginal_of_forall_uniform_dominates {n k : ℕ} (hn : 0 < n)
    (huniform : ∀ D : WeightedDesign n k, (∀ atomLabel : Fin n, D.weight atomLabel = (n : ℝ)⁻¹) →
      ∃ C : Finset (Fin n), C.card = k ∧ Dominates D C) :
    GtzOriginal n k := by
  intro A hortho
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨C, hcard, hdom⟩ := huniform (rowDesign hn A hortho) (fun _ => rfl)
  refine ⟨C.orderEmbOfFin hcard, (C.orderEmbOfFin hcard).injective, ?_⟩
  have himage : Finset.univ.image (C.orderEmbOfFin hcard) = C := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  have hsubmatrix : (A.submatrix (C.orderEmbOfFin hcard) id)ᵀ
        * (A.submatrix (C.orderEmbOfFin hcard) id)
      = ∑ rowLabel ∈ C, atomMatrix (A rowLabel) := by
    rw [transpose_mul_self_eq_sum_rows]
    conv_rhs => rw [← himage]
    rw [Finset.sum_image fun left _ right _ hlr => (C.orderEmbOfFin hcard).injective hlr]
    rfl
  have hsubset : subsetSum (rowDesign hn A hortho) C
      = (n : ℝ) • ∑ rowLabel ∈ C, atomMatrix (A rowLabel) := by
    rw [subsetSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun rowLabel _ => ?_
    show atomMatrix (Real.sqrt (n : ℝ) • A rowLabel) = (n : ℝ) • atomMatrix (A rowLabel)
    rw [atomMatrix_smul, Real.sq_sqrt hnR.le]
  have hfinal : (A.submatrix (C.orderEmbOfFin hcard) id)ᵀ
        * (A.submatrix (C.orderEmbOfFin hcard) id) - (n : ℝ)⁻¹ • 1
      = (n : ℝ)⁻¹ • (subsetSum (rowDesign hn A hortho) C - 1) := by
    rw [hsubmatrix, hsubset, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hnR), one_smul]
  have hdomPsd : (subsetSum (rowDesign hn A hortho) C - 1).PosSemidef := hdom
  rw [hfinal]
  exact hdomPsd.smul (inv_pos.mpr hnR).le

/-- **THE UNIFORM SLICE, NAMED.**  At every size and rank the 1997 statement is
EXACTLY its own uniform slice: the weights carry no information at a fixed size, only
the atoms do.  Backward is the shipped `Gtz.exists_dominates_of_gtzOriginal_uniform`. -/
theorem gtzOriginal_iff_forall_uniform_dominates {n k : ℕ} (hn : 0 < n) :
    GtzOriginal n k
      ↔ ∀ D : WeightedDesign n k, (∀ atomLabel : Fin n, D.weight atomLabel = (n : ℝ)⁻¹) →
          ∃ C : Finset (Fin n), C.card = k ∧ Dominates D C :=
  ⟨fun horiginal D huniformWeights =>
      exists_dominates_of_gtzOriginal_uniform hn horiginal D huniformWeights,
    gtzOriginal_of_forall_uniform_dominates hn⟩

/-! ## The right-endpoint spread obligation, named -/

/-- **THE `(6,3)` IDENTIFICATION.**  Obligation two of `Gtz.gtzWeightedAll_three_of_branches`,
read at the right endpoint `weightFloor = 1/6` of the proved window, is EXACTLY the
original 1997 conjecture at `n = 6, k = 3`.

Forward consumes the shipped unconditional parallel branch
`Gtz.exists_dominating_triple_of_hasParallelPair_sixThree`, so the certificate's
`¬ HasParallelPair` hypothesis costs nothing; backward is the restriction. -/
theorem spreadFloorCertificate_sixThree_sizeInv_iff_gtzOriginal :
    SpreadFloorCertificate 6 3 (((6 : ℕ) : ℝ)⁻¹) ↔ GtzOriginal 6 3 := by
  rw [spreadFloorCertificate_sizeInv_iff_uniform (by norm_num),
    gtzOriginal_iff_forall_uniform_dominates (n := 6) (k := 3) (by norm_num)]
  refine ⟨fun hcert D huniformWeights => ?_, fun hslice D huniformWeights _ => ?_⟩
  · by_cases hparallelPair : HasParallelPair D
    · exact exists_dominating_triple_of_hasParallelPair_sixThree D hparallelPair
    · exact hcert D (by simpa using huniformWeights) hparallelPair
  · exact hslice D (by simpa using huniformWeights)

/-- **THE FIRST OPEN SHAPE.**  `Gtz.gtz_original_of_le_five` closes the 1997 statement at
every `n ≤ 5`, so the obligation named above sits at the smallest matrix shape for which
the original problem is open.  Stated as the pair so the boundary is visible in one
place. -/
theorem gtzOriginal_five_three_and_spreadFloorCertificate_iff :
    GtzOriginal 5 3
      ∧ (SpreadFloorCertificate 6 3 (((6 : ℕ) : ℝ)⁻¹) ↔ GtzOriginal 6 3) :=
  ⟨gtz_original_of_le_five 5 3 (by norm_num) (by norm_num) (by norm_num),
    spreadFloorCertificate_sixThree_sizeInv_iff_gtzOriginal⟩

/-! ## The slice is closed and bounded, and the mirror on it is total -/

/-- **THE SLICE IS BOUNDED.**  At uniform weight every leverage lies in `[0, size]`, so
the uniform designs form a bounded set of atom families — the shipped leverage cap read
as the two-sided statement the region needs.  With
`Gtz.spreadFloorCertificate_sixThree_sizeInv_of_closedResidue` removing the parallel-pair
hypothesis, the residue's region carries no open condition. -/
theorem leverage_mem_Icc_of_weight_eq_sizeInv {m k : ℕ} (D : WeightedDesign m k)
    (hsizePos : 0 < m) (huniform : ∀ atomLabel : Fin m, D.weight atomLabel = (m : ℝ)⁻¹)
    (atomLabel : Fin m) : leverageOf (D.atom atomLabel) ∈ Set.Icc (0 : ℝ) (m : ℝ) :=
  ⟨Finset.sum_nonneg fun _ _ => sq_nonneg _,
    leverage_le_size_of_weight_eq_sizeInv D hsizePos huniform atomLabel⟩

/-- **THE MIRROR IS TOTAL AT `(6,3)`.**  The complement of a triple is a triple, so the
shipped ceiling reading of domination applies to BOTH members of every 3–3 split: a
uniform `(6,3)` design dominates `C` exactly when its complement's raw atom sum is capped
at `5`.  So the slice's question — some triple with `λ_min(S_C) ≥ 1`— is equivalently
some triple with `λ_max(S_C) ≤ 5`. -/
theorem dominates_iff_posSemidef_five_smul_one_sub_subsetSum_compl_sixThree
    (D : WeightedDesign 6 3) (huniform : ∀ atomLabel : Fin 6, D.weight atomLabel = (6 : ℝ)⁻¹)
    (selected : Finset (Fin 6)) :
    Dominates D selected ↔ ((5 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - subsetSum D selectedᶜ).PosSemidef := by
  have hceiling := dominates_iff_posSemidef_smul_one_sub_subsetSum_compl D huniform selected
  rw [hceiling]
  norm_num

end Gtz
