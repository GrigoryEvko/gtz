/-
# The self-dual cell is `size = 2 * rank`, at every rank

## What this module proves

At a UNIFORM weight the whole unweighted atom sum is `size · I`, so a selection
and its complement carry complementary information.  Reading the complement
through the Naimark dual turns domination inside out:

  **`Gtz.dominates_iff_dominates_naimarkDual_compl_of_uniform`**:
  a `rank`-selection dominates the design exactly when its COMPLEMENT dominates
  the Naimark dual, which is a design of rank `size - rank` on the same labels
  and the same weights.

  **`Gtz.isTie_naimarkDual_iff_of_uniform`**: the design is an exact tie exactly
  when its Naimark dual is.

## Why this is the structural reason for the band's lower endpoint

`Gtz.naimark_rank_eq_iff_size_eq_two_mul` says the dual has the SAME rank exactly
when `size = 2 * rank`.  So:

* below `2 * rank` the dual has rank STRICTLY BELOW `rank`, and every tie question
  at the cell is a tie question at a LOWER rank, where the campaign already knows
  more.  Rank two is a theorem, and `Gtz.simplexTieDesign` inhabits every cell at
  every rank, so nothing forces a parallel pair there.  Indeed the hinge is FALSE
  at size `rank + 1` at every rank (`Gtz.not_hingeHoldsAtSize_succ_rank`).
* at `size = 2 * rank` the dual sits at the SAME cell.  The descent stops.  That
  cell is exactly the lower endpoint of
  `Skeleton.obligationSubThresholdBandHinge`.

The campaign carried this involution ONLY at `(6,3)` and only through the chart
dual: `Gtz.dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree` and
`Gtz.isTie_chartDual_iff_isTie_of_uniformWeight`, with
`Gtz.selfDual_ne_top_of_ne_three` recording that the THRESHOLD cell is self-dual
only at rank three.  What no file records is that the SELF-DUAL cell is
`2 * rank` at every rank, and that this is the band's lower endpoint.  At rank
three the two coincide, because `2 * 3 = 3 * 4 / 2`, and that coincidence is why
the pattern stayed invisible.

## What it does NOT prove

Self-duality does not prove the hinge.  It says the first band cell is the first
cell whose dual does not descend, which is a reason to expect the change of
behaviour there, and it matches the measurement: parallel-free exact ties are
abundant at `(5,4)`, `(6,4)` and `(7,4)` and were never reached at `(8,4)`,
`(9,4)` or `(6,3)`.  Refer to scratchpad/NOTES-rankfour-exact.txt.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.SplitTransfer
import Gtz.Quantitative.SelfDualInvolution
import Gtz.Wave.NaimarkDualDesign
import Gtz.Wave.NaimarkDualExistence
import Gtz.Wave.StressFreeCapRefutation
import Gtz.Wave.BandTieTower

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m k r : ℕ}

/-! ## 1. The uniform-weight readings -/

/-- **THE SELF-DUAL CELL.**  The Naimark dual carries the same rank exactly at
`size = 2 * rank`. -/
theorem naimark_rank_eq_iff_size_eq_two_mul {D : WeightedDesign m k} (N : NaimarkDual D r) :
    r = k ↔ m = 2 * k := by
  have hadd := N.rankAdd
  omega

/-- Under a uniform weight the whole unweighted atom sum is `size` times the
identity. -/
theorem subsetSum_univ_of_uniform (D : WeightedDesign m k)
    (huniform : ∀ c, D.weight c = (m : ℝ)⁻¹) :
    subsetSum D Finset.univ = (m : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hpos : 0 < m := pos_of_weightedDesign D
  have hcast : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hparseval := D.isParseval
  have hrewrite : ∑ c : Fin m, D.weight c • atomMatrix (D.atom c)
      = (m : ℝ)⁻¹ • subsetSum D Finset.univ := by
    rw [subsetSum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [huniform c]
  rw [hrewrite] at hparseval
  have hscale : (m : ℝ) • ((m : ℝ)⁻¹ • subsetSum D Finset.univ)
      = (m : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) := by rw [hparseval]
  rwa [smul_smul, mul_inv_cancel₀ hcast, one_smul] at hscale

/-- The atom sums of a selection and of its complement resolve the whole. -/
theorem subsetSum_add_compl (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    subsetSum D selected + subsetSum D selectedᶜ = subsetSum D Finset.univ := by
  classical
  rw [subsetSum, subsetSum, subsetSum]
  exact Finset.sum_add_sum_compl selected _

/-- Under a uniform weight the inverse-weight diagonal of any selection is `size`
times the identity. -/
theorem naimarkInvWeight_of_uniform (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) (huniform : ∀ c, D.weight c = (m : ℝ)⁻¹) :
    naimarkInvWeight D pick = (m : ℝ) • (1 : Matrix (Fin size) (Fin size) ℝ) := by
  have hpos : 0 < m := pos_of_weightedDesign D
  have hcast : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  ext a b
  rw [naimarkInvWeight, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, huniform, inv_inv, if_pos rfl, mul_one]
  · rw [Matrix.diagonal_apply_ne _ hab, if_neg hab, mul_zero]

/-- The image of the order embedding of a selection is the selection. -/
theorem image_orderEmbOfFin_univ {size : ℕ} {selected : Finset (Fin m)}
    (hcard : selected.card = size) :
    Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
  classical
  refine Finset.eq_of_subset_of_card_le (fun label hlabel => ?_) ?_
  · rw [Finset.mem_image] at hlabel
    obtain ⟨slot, _, hslot⟩ := hlabel
    rw [← hslot]
    exact Finset.orderEmbOfFin_mem _ _ _
  · rw [Finset.card_image_of_injective _ (selected.orderEmbOfFin hcard).injective,
      Finset.card_univ, Fintype.card_fin, hcard]

/-! ## 2. The two gram readings of a selection, primal and dual

`Gtz.dominates_iff_naimarkGram` (Gtz/Wave/NaimarkDualDesign.lean) is the weak
half.  The strict half is the same rewriting against the definite comparison. -/

/-- **THE STRICT GRAM READING.**  A `rank`-selection dominates strictly exactly
when its Gram clears the identity strictly. -/
theorem posDef_gap_iff_naimarkGram (D : WeightedDesign m k) {pick : Fin k → Fin m}
    (hpick : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef
      ↔ (naimarkGram D pick - 1).PosDef := by
  have hgram : selectedAtomRows D pick * (selectedAtomRows D pick)ᵀ = naimarkGram D pick := by
    ext a b
    simp only [naimarkGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      selectedAtomRows, dotProduct]
  rw [← transpose_mul_selectedAtomRows D pick hpick,
    posDef_transpose_mul_sub_one_comm (selectedAtomRows D pick), hgram]

/-- The dual design reads the dual Gram of a selection. -/
theorem naimarkGram_dual_eq_coGram {D : WeightedDesign m k} (N : NaimarkDual D r) {size : ℕ}
    (pick : Fin size → Fin m) : naimarkGram N.dual pick = naimarkCoGram N pick := rfl

/-! ## 3. The complementation law -/

/-- The complement gap of a selection, under a uniform weight, is the level
`size - 1` minus the outer square of the complement's atom rows. -/
theorem gap_eq_smul_one_sub_transpose_mul (D : WeightedDesign m k)
    (huniform : ∀ c, D.weight c = (m : ℝ)⁻¹)
    {selected : Finset (Fin m)} {pickOutside : Fin r → Fin m}
    (houtside : Function.Injective pickOutside)
    (hcompl : Finset.image pickOutside Finset.univ = selectedᶜ) :
    subsetSum D selected - 1
      = ((m : ℝ) - 1) • (1 : Matrix (Fin k) (Fin k) ℝ)
        - (selectedAtomRows D pickOutside)ᵀ * selectedAtomRows D pickOutside := by
  have hrows := transpose_mul_selectedAtomRows D pickOutside houtside
  have hsplit := subsetSum_add_compl D selected
  rw [subsetSum_univ_of_uniform D huniform] at hsplit
  rw [hrows, hcompl]
  have hshift : ((m : ℝ) - 1) • (1 : Matrix (Fin k) (Fin k) ℝ)
      = (m : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) - 1 := by
    rw [sub_smul, one_smul]
  rw [hshift]
  have : subsetSum D selected = (m : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ)
      - subsetSum D selectedᶜ := by
    rw [← hsplit]; abel
  rw [this]
  abel

/-- **THE GALE COMPLEMENTATION LAW, AT EVERY RANK AND EVERY SIZE.**  At a uniform
weight a `rank`-selection dominates the design exactly when its complement
dominates the Naimark dual. -/
theorem dominates_iff_dominates_naimarkDual_compl_of_uniform {D : WeightedDesign m k}
    (N : NaimarkDual D r) (huniform : ∀ c, D.weight c = (m : ℝ)⁻¹) (hsize : 2 ≤ m)
    {selected : Finset (Fin m)} {pickOutside : Fin r → Fin m}
    (houtside : Function.Injective pickOutside)
    (hcompl : Finset.image pickOutside Finset.univ = selectedᶜ) :
    Dominates D selected ↔ Dominates N.dual selectedᶜ := by
  have hlevel : (0 : ℝ) < (m : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hsize
    linarith
  have hgram : selectedAtomRows D pickOutside * (selectedAtomRows D pickOutside)ᵀ
      = naimarkGram D pickOutside := by
    ext a b
    simp only [naimarkGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      selectedAtomRows, dotProduct]
  have hco : naimarkGram D pickOutside
      = (m : ℝ) • (1 : Matrix (Fin r) (Fin r) ℝ) - naimarkCoGram N pickOutside := by
    have hadd := naimark_gram_add_coGram N houtside
    rw [naimarkInvWeight_of_uniform D pickOutside huniform] at hadd
    rw [← hadd]
    abel
  have hshape : ((m : ℝ) - 1) • (1 : Matrix (Fin r) (Fin r) ℝ)
      - selectedAtomRows D pickOutside * (selectedAtomRows D pickOutside)ᵀ
      = naimarkCoGram N pickOutside - 1 := by
    rw [hgram, hco, sub_smul, one_smul]
    abel
  rw [Dominates, gap_eq_smul_one_sub_transpose_mul D huniform houtside hcompl,
    posSemidef_smul_one_sub_transpose_comm hlevel (selectedAtomRows D pickOutside),
    hshape, ← naimarkGram_dual_eq_coGram N pickOutside,
    ← dominates_iff_naimarkGram N.dual houtside, hcompl]

/-- **THE STRICT COMPLEMENTATION LAW.** -/
theorem posDef_gap_iff_posDef_gap_naimarkDual_compl_of_uniform {D : WeightedDesign m k}
    (N : NaimarkDual D r) (huniform : ∀ c, D.weight c = (m : ℝ)⁻¹) (hsize : 2 ≤ m)
    {selected : Finset (Fin m)} {pickOutside : Fin r → Fin m}
    (houtside : Function.Injective pickOutside)
    (hcompl : Finset.image pickOutside Finset.univ = selectedᶜ) :
    (subsetSum D selected - 1).PosDef ↔ (subsetSum N.dual selectedᶜ - 1).PosDef := by
  have hlevel : (0 : ℝ) < (m : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hsize
    linarith
  have hgram : selectedAtomRows D pickOutside * (selectedAtomRows D pickOutside)ᵀ
      = naimarkGram D pickOutside := by
    ext a b
    simp only [naimarkGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      selectedAtomRows, dotProduct]
  have hco : naimarkGram D pickOutside
      = (m : ℝ) • (1 : Matrix (Fin r) (Fin r) ℝ) - naimarkCoGram N pickOutside := by
    have hadd := naimark_gram_add_coGram N houtside
    rw [naimarkInvWeight_of_uniform D pickOutside huniform] at hadd
    rw [← hadd]
    abel
  have hshape : ((m : ℝ) - 1) • (1 : Matrix (Fin r) (Fin r) ℝ)
      - selectedAtomRows D pickOutside * (selectedAtomRows D pickOutside)ᵀ
      = naimarkCoGram N pickOutside - 1 := by
    rw [hgram, hco, sub_smul, one_smul]
    abel
  rw [gap_eq_smul_one_sub_transpose_mul D huniform houtside hcompl,
    posDef_smul_one_sub_transpose_comm hlevel (selectedAtomRows D pickOutside),
    hshape, ← naimarkGram_dual_eq_coGram N pickOutside,
    ← posDef_gap_iff_naimarkGram N.dual houtside, hcompl]

/-! ## 4. The tie involution -/

/-- Cards line up: the complement of a `rank`-selection has card `size - rank`,
which is the dual rank. -/
theorem card_compl_of_naimark {D : WeightedDesign m k} (N : NaimarkDual D r)
    {selected : Finset (Fin m)} (hcard : selected.card = k) : selectedᶜ.card = r := by
  have hadd := N.rankAdd
  rw [Finset.card_compl, hcard, Fintype.card_fin]
  omega

/-- **A TIE PASSES TO THE NAIMARK DUAL**, at a uniform weight, at every rank and
every size. -/
theorem isTie_naimarkDual_of_isTie_of_uniform {D : WeightedDesign m k} (N : NaimarkDual D r)
    (huniform : ∀ c, D.weight c = (m : ℝ)⁻¹) (hsize : 2 ≤ m) (htie : IsTie D) :
    IsTie N.dual := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨selected, hcard, hdom⟩ := htie.1
    refine ⟨selectedᶜ, card_compl_of_naimark N hcard, ?_⟩
    have hcompl := image_orderEmbOfFin_univ (card_compl_of_naimark N hcard)
    exact (dominates_iff_dominates_naimarkDual_compl_of_uniform N huniform hsize
      (selectedᶜ.orderEmbOfFin (card_compl_of_naimark N hcard)).injective hcompl).mp hdom
  · intro outside hcardOutside hposDef
    have hcardInside : outsideᶜ.card = k := by
      have hadd := N.rankAdd
      rw [Finset.card_compl, hcardOutside, Fintype.card_fin]
      omega
    have hback : outsideᶜᶜ = outside := compl_compl outside
    have hcompl : Finset.image (outside.orderEmbOfFin hcardOutside) Finset.univ = outsideᶜᶜ := by
      rw [hback]
      exact image_orderEmbOfFin_univ hcardOutside
    refine htie.2 outsideᶜ hcardInside ?_
    refine (posDef_gap_iff_posDef_gap_naimarkDual_compl_of_uniform N huniform hsize
      (outside.orderEmbOfFin hcardOutside).injective hcompl).mpr ?_
    rwa [hback]

/-- The flip of a Naimark dual returns the original design on the nose. -/
theorem naimark_flip_dual_eq {D : WeightedDesign m k} (N : NaimarkDual D r) :
    N.flip.dual = D := rfl

/-- **THE TIE INVOLUTION.**  At a uniform weight the design is an exact tie
exactly when its Naimark dual is. -/
theorem isTie_naimarkDual_iff_of_uniform {D : WeightedDesign m k} (N : NaimarkDual D r)
    (huniform : ∀ c, D.weight c = (m : ℝ)⁻¹) (hsize : 2 ≤ m) :
    IsTie D ↔ IsTie N.dual := by
  refine ⟨isTie_naimarkDual_of_isTie_of_uniform N huniform hsize, fun htie => ?_⟩
  have hdualUniform : ∀ c, N.dual.weight c = (m : ℝ)⁻¹ := huniform
  have hback := isTie_naimarkDual_of_isTie_of_uniform N.flip hdualUniform hsize htie
  rwa [naimark_flip_dual_eq N] at hback

/-! ## 5. The self-dual cell -/

/-- **AT `size = 2 * rank` THE DUAL SITS AT THE SAME CELL.**  Its rank is the
design's rank, so the tie involution is an involution of ONE cell.  That cell is
the lower endpoint of `Skeleton.obligationSubThresholdBandHinge`. -/
theorem isTie_iff_isTie_naimarkDual_selfDualCell {rank : ℕ} (hrank : 1 ≤ rank)
    {D : WeightedDesign (2 * rank) rank} (N : NaimarkDual D rank)
    (huniform : ∀ c, D.weight c = ((2 * rank : ℕ) : ℝ)⁻¹) :
    IsTie D ↔ IsTie N.dual :=
  isTie_naimarkDual_iff_of_uniform N huniform (by omega)

/-- **BELOW THE SELF-DUAL CELL THE DUAL RANK IS STRICTLY SMALLER.**  Every tie
question at a cell with `size < 2 * rank` is a tie question at a strictly lower
rank. -/
theorem naimark_rank_lt_of_size_lt_two_mul {D : WeightedDesign m k} (N : NaimarkDual D r)
    (hsize : m < 2 * k) : r < k := by
  have hadd := N.rankAdd
  omega

/-- **ABOVE THE SELF-DUAL CELL THE DUAL RANK IS STRICTLY LARGER.** -/
theorem naimark_rank_gt_of_two_mul_lt {D : WeightedDesign m k} (N : NaimarkDual D r)
    (hsize : 2 * k < m) : k < r := by
  have hadd := N.rankAdd
  omega

/-- The involution exists at every cell, because every design has a Naimark
dual. -/
theorem exists_naimarkDual_isTie_iff_of_uniform (D : WeightedDesign m k)
    (hrank : k + r = m) (huniform : ∀ c, D.weight c = (m : ℝ)⁻¹) (hsize : 2 ≤ m) :
    ∃ E : WeightedDesign m r, (IsTie D ↔ IsTie E) := by
  obtain ⟨N⟩ := exists_naimarkDual D hrank
  exact ⟨N.dual, isTie_naimarkDual_iff_of_uniform N huniform hsize⟩

end Gtz
