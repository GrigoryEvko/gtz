/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Quantitative.SixThreeMinimalityLayer

/-!
# A witness that the minimality layer is proper over the ALL-HEAVY class

`Gtz.MinimalityLayerIsProperOverShape` records, as an unproved `Prop` carrying an exact
witness in its docstring, that some design satisfying all TEN conjuncts of
`Gtz.IsSixThreeShapeCandidate` fails the covering law.  That statement is still measured
rather than mechanized.  This file proves the corresponding statement over the FIRST of
those ten conjuncts alone, `Gtz.AllHeavy`, in the kernel:

  `Gtz.minimalityLayerIsProperOverAllHeavy` -- there is an ALL-HEAVY `(6,3)` design whose
  argmax family carries neither three blocks nor a covering,

together with `Gtz.exists_allHeavy_not_hasCoveringArgmaxFamily`,
`Gtz.exists_allHeavy_not_hasSupportedCoveringArgmaxFamily` and
`Gtz.exists_allHeavy_not_hasThreeArgmaxBlocks`.

## Why all-heaviness is the conjunct worth isolating

`Gtz.rank_three_of_heavy_six_three` carries the whole of rank three off the ALL-HEAVY
box alone, so all-heaviness is the shape conjunct the campaign actually leans on.  A
minimality conjunct that all-heaviness already implied would shrink nothing where it
matters; these theorems say it does not.

## The witness

`Gtz.heavySpikeDesign`: with `s = sqrt (6/5)`, the six atoms are `2s e_0, 2s e_1, 2s e_2`
and `s e_0, s e_1, s e_2`, all at the uniform weight `1/6`.  Parseval holds because
`4 s^2 + s^2 = 5 s^2 = 6`, and every leverage is `24/5` or `6/5`, both above one, so the
design is all-heavy.  Its chart is RATIONAL even though its atoms are not: the uniform
weight makes `P = (1/6) Gram`, and `Gtz.heavySpikeGap_apply` gives the gap
`W = P - diag t` entry by entry, with `19/30` on the three heavy diagonal entries,
`1/30` on the three light ones and `2/5` on the three heavy-light pairs.

The three heavy atoms are orthogonal, so `W` restricted to `{0,1,2}` is exactly
`(19/30) . 1` and that block value is `19/30`; every block meeting a light atom has a
diagonal entry `1/30`, so its least eigenvalue is at most `1/30`.  Hence the argmax
family is the single block `{0,1,2}`
(`Gtz.heavySpike_chartArgmaxFamily_subset`), which covers three of the six atoms.

## What this does NOT establish

The witness is NOT a shape candidate.  `2s e_0` and `s e_0` are parallel, so it has a
parallel pair, and its three heavy atoms are pairwise orthogonal, so it also fails the
box's no-orthogonal-triple clause.  Properness over the full ten-conjunct
`Gtz.IsSixThreeShapeCandidate` therefore remains exactly where `recon`-tier measurement
left it: `Gtz.MinimalityLayerIsProperOverShape`, unproved.  What is proved here is
properness over `Gtz.AllHeavy`.

And nothing here bears on `Gtz.GtzWeighted 6 3`: by
`Gtz.not_gtzWeighted_six_three_of_exists_candidate_not_satisfying`, a witness proper over
the FULL box would be a refutation of the cell, so a witness that stops short of the full
box is the most any honest run can exhibit.

## One reusable brick

`Gtz.chartBlockValue_le_chartGapRaw_diagonal` -- at every size and rank, a block's value
never exceeds the chart gap's diagonal entry at any atom of that block.  The proof never
evaluates `Finset.orderEmbOfFin`, which does not reduce in the kernel; it uses only that
the embedding's range is the block, so the coordinate certificate
`Gtz.lambdaMinMat_le_diagonal` applies at an index it never has to name.

NO SORRY, NO AXIOM, NO `native_decide`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix
open scoped BigOperators

noncomputable def heavySpikeScale : ℝ := Real.sqrt (6 / 5)

theorem heavySpikeScale_sq : heavySpikeScale ^ 2 = 6 / 5 := by
  rw [heavySpikeScale, Real.sq_sqrt]; norm_num

theorem heavySpikeScale_pos : 0 < heavySpikeScale :=
  Real.sqrt_pos.mpr (by norm_num)

theorem heavySpikeScale_abs : |heavySpikeScale| = heavySpikeScale :=
  abs_of_pos heavySpikeScale_pos

theorem heavySpikeScale_mul_self : heavySpikeScale * heavySpikeScale = 6 / 5 := by
  rw [← sq]; exact heavySpikeScale_sq

noncomputable def heavySpikeAtom : Fin 6 → (Fin 3 → ℝ) :=
  ![![2 * heavySpikeScale, 0, 0], ![0, 2 * heavySpikeScale, 0], ![0, 0, 2 * heavySpikeScale],
    ![heavySpikeScale, 0, 0], ![0, heavySpikeScale, 0], ![0, 0, heavySpikeScale]]

noncomputable def heavySpikeDesign : WeightedDesign 6 3 where
  atom := heavySpikeAtom
  weight := fun _ => 1 / 6
  weight_pos := fun _ => by norm_num
  weight_sum_one := by norm_num
  isParseval := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Fin.sum_univ_six, atomMatrix, Matrix.vecMulVec, heavySpikeAtom] <;>
      nlinarith [heavySpikeScale_sq]

theorem heavySpikeDesign_allHeavy : AllHeavy heavySpikeDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    simp [leverageOf, heavySpikeDesign, heavySpikeAtom, Fin.sum_univ_three,
      heavySpikeScale_abs] <;>
    nlinarith [heavySpikeScale_sq, heavySpikeScale_pos]

/-- The chart gap `W = P - diag t` of the witness, entry by entry. -/
noncomputable def heavySpikeGapTable : Fin 6 → Fin 6 → ℝ :=
  ![![19/30, 0, 0, 2/5, 0, 0], ![0, 19/30, 0, 0, 2/5, 0], ![0, 0, 19/30, 0, 0, 2/5],
    ![2/5, 0, 0, 1/30, 0, 0], ![0, 2/5, 0, 0, 1/30, 0], ![0, 0, 2/5, 0, 0, 1/30]]

theorem heavySpikeGap_apply (rowIndex colIndex : Fin 6) :
    chartGapRaw ((chartPointOfDesign heavySpikeDesign).chart,
        (chartPointOfDesign heavySpikeDesign).weight) rowIndex colIndex
      = heavySpikeGapTable rowIndex colIndex := by
  have hinv : (Real.sqrt 6)⁻¹ * (Real.sqrt 6)⁻¹ = 1 / 6 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
    norm_num
  have hsqrt : Real.sqrt (1 / 6 : ℝ) * Real.sqrt (1 / 6 : ℝ) = 1 / 6 :=
    Real.mul_self_sqrt (by norm_num)
  have hkey : (Real.sqrt 6)⁻¹ * (Real.sqrt 6)⁻¹ * (heavySpikeScale * heavySpikeScale)
      = 1 / 5 := by
    rw [hinv, heavySpikeScale_mul_self]; norm_num
  have hchart : (chartPointOfDesign heavySpikeDesign).chart
      = projectionOfDesign heavySpikeDesign := rfl
  have hweight : (chartPointOfDesign heavySpikeDesign).weight = heavySpikeDesign.weight := rfl
  simp only [chartGapRaw, Matrix.sub_apply, Matrix.of_apply, hchart, hweight,
    projectionOfDesign_apply, Matrix.diagonal_apply]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [heavySpikeDesign, heavySpikeAtom, dotProduct, Fin.sum_univ_three,
      heavySpikeGapTable] <;>
    nlinarith [hkey]

/-- **THE BLOCK VALUE NEVER EXCEEDS THE GAP'S DIAGONAL AT AN ATOM OF THE BLOCK.**
Reusable at every size and rank: the coordinate vector at that atom is a unit Rayleigh
direction for the block, and `Gtz.lambdaMinMat_le_diagonal` reads off the entry.  The
proof never evaluates `Finset.orderEmbOfFin`; it only uses that its range is the block. -/
theorem chartBlockValue_le_chartGapRaw_diagonal {size rank : ℕ} [Nonempty (Fin rank)]
    (config : (Fin size → Fin size → ℝ) × (Fin size → ℝ)) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) {atomIndex : Fin size} (hmem : atomIndex ∈ selected) :
    chartBlockValue rank config selected ≤ chartGapRaw config atomIndex atomIndex := by
  rw [chartBlockValue, dif_pos hcard]
  have hrange : atomIndex ∈ Set.range (selected.orderEmbOfFin hcard) := by
    rw [Finset.range_orderEmbOfFin selected hcard]
    exact_mod_cast hmem
  obtain ⟨coordinate, hcoordinate⟩ := hrange
  have hbound := lambdaMinMat_le_diagonal ((chartGapRaw config).submatrix
    (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)) coordinate
  rwa [Matrix.submatrix_apply, hcoordinate] at hbound

/-! ### The witness has a single argmax block -/

theorem heavySpikeBigBlock_card : (({0, 1, 2} : Finset (Fin 6))).card = 3 := by decide

theorem mem_heavySpikeBigBlock_iff (atomIndex : Fin 6) :
    atomIndex ∈ ({0, 1, 2} : Finset (Fin 6)) ↔ atomIndex = 0 ∨ atomIndex = 1 ∨ atomIndex = 2 := by
  revert atomIndex; decide

theorem heavySpikeGapTable_bigDiagonal {atomIndex : Fin 6}
    (hmem : atomIndex ∈ ({0, 1, 2} : Finset (Fin 6))) :
    heavySpikeGapTable atomIndex atomIndex = 19 / 30 := by
  rcases (mem_heavySpikeBigBlock_iff atomIndex).mp hmem with rfl | rfl | rfl <;>
    simp [heavySpikeGapTable]

theorem heavySpikeGapTable_bigOffDiagonal {rowIndex colIndex : Fin 6}
    (hrow : rowIndex ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hcol : colIndex ∈ ({0, 1, 2} : Finset (Fin 6))) (hne : rowIndex ≠ colIndex) :
    heavySpikeGapTable rowIndex colIndex = 0 := by
  rcases (mem_heavySpikeBigBlock_iff rowIndex).mp hrow with rfl | rfl | rfl <;>
    rcases (mem_heavySpikeBigBlock_iff colIndex).mp hcol with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | simp [heavySpikeGapTable]

theorem heavySpikeBigBlock_submatrix :
    (chartGapRaw ((chartPointOfDesign heavySpikeDesign).chart,
        (chartPointOfDesign heavySpikeDesign).weight)).submatrix
        (({0, 1, 2} : Finset (Fin 6)).orderEmbOfFin heavySpikeBigBlock_card)
        (({0, 1, 2} : Finset (Fin 6)).orderEmbOfFin heavySpikeBigBlock_card)
      = (19 / 30 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  rw [Matrix.submatrix_apply, heavySpikeGap_apply]
  have hrow := Finset.orderEmbOfFin_mem ({0, 1, 2} : Finset (Fin 6))
    heavySpikeBigBlock_card rowIndex
  have hcol := Finset.orderEmbOfFin_mem ({0, 1, 2} : Finset (Fin 6))
    heavySpikeBigBlock_card colIndex
  by_cases hsame : rowIndex = colIndex
  · subst hsame
    rw [heavySpikeGapTable_bigDiagonal hrow]
    simp
  · have hne : (({0, 1, 2} : Finset (Fin 6)).orderEmbOfFin heavySpikeBigBlock_card) rowIndex
        ≠ (({0, 1, 2} : Finset (Fin 6)).orderEmbOfFin heavySpikeBigBlock_card) colIndex :=
      fun heq => hsame ((({0, 1, 2} : Finset (Fin 6)).orderEmbOfFin
        heavySpikeBigBlock_card).injective heq)
    rw [heavySpikeGapTable_bigOffDiagonal hrow hcol hne]
    simp [hsame]

theorem heavySpikeBigBlock_value :
    (19 / 30 : ℝ) ≤ chartBlockValue 3 ((chartPointOfDesign heavySpikeDesign).chart,
      (chartPointOfDesign heavySpikeDesign).weight) ({0, 1, 2} : Finset (Fin 6)) := by
  rw [chartBlockValue, dif_pos heavySpikeBigBlock_card, heavySpikeBigBlock_submatrix]
  rw [le_lambdaMinMat_iff_posSemidef_sub_smul_one _ (by simp [Matrix.transpose_smul])]
  simpa using (Matrix.PosSemidef.zero (n := Fin 3) (R := ℝ))

theorem heavySpike_le_chartObjective :
    (19 / 30 : ℝ) ≤ chartObjective (chartPointOfDesign heavySpikeDesign) :=
  le_trans heavySpikeBigBlock_value
    (Finset.le_sup' (fun selected => chartBlockValue 3
        (((chartPointOfDesign heavySpikeDesign).chart,
          (chartPointOfDesign heavySpikeDesign).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected)
      ((mem_chartCandidates_iff 6 3 _).mpr heavySpikeBigBlock_card))

theorem heavySpike_smallAtom_block_le {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    {atomIndex : Fin 6} (hbig : atomIndex = 3 ∨ atomIndex = 4 ∨ atomIndex = 5)
    (hmem : atomIndex ∈ selected) :
    chartBlockValue 3 ((chartPointOfDesign heavySpikeDesign).chart,
      (chartPointOfDesign heavySpikeDesign).weight) selected ≤ 1 / 30 := by
  have hbound := chartBlockValue_le_chartGapRaw_diagonal
    (((chartPointOfDesign heavySpikeDesign).chart,
      (chartPointOfDesign heavySpikeDesign).weight) :
        (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) hcard hmem
  rw [heavySpikeGap_apply] at hbound
  rcases hbig with rfl | rfl | rfl <;>
    · refine le_trans hbound (le_of_eq ?_)
      simp [heavySpikeGapTable]

theorem heavySpike_atom_cases (atomIndex : Fin 6) :
    (atomIndex = 0 ∨ atomIndex = 1 ∨ atomIndex = 2)
      ∨ (atomIndex = 3 ∨ atomIndex = 4 ∨ atomIndex = 5) := by
  revert atomIndex; decide

theorem heavySpike_chartArgmaxFamily_subset :
    chartArgmaxFamily (chartPointOfDesign heavySpikeDesign)
      ⊆ {({0, 1, 2} : Finset (Fin 6))} := by
  intro block hblock
  rw [mem_chartArgmaxFamily_iff] at hblock
  obtain ⟨hcard, hvalue⟩ := hblock
  have hsubset : block ⊆ ({0, 1, 2} : Finset (Fin 6)) := by
    intro atomIndex hatom
    rcases heavySpike_atom_cases atomIndex with hlow | hhigh
    · exact (mem_heavySpikeBigBlock_iff atomIndex).mpr hlow
    · exfalso
      have hupper := heavySpike_smallAtom_block_le hcard hhigh hatom
      have hlower := heavySpike_le_chartObjective
      linarith
  rw [Finset.mem_singleton]
  exact Finset.eq_of_subset_of_card_le hsubset
    (by rw [hcard, heavySpikeBigBlock_card])

theorem heavySpikeDesign_not_hasCoveringArgmaxFamily :
    ¬ HasCoveringArgmaxFamily heavySpikeDesign := by
  intro hcovering
  obtain ⟨block, hblock, hatom⟩ := hcovering 3
  have hsingleton := heavySpike_chartArgmaxFamily_subset hblock
  rw [Finset.mem_singleton] at hsingleton
  subst hsingleton
  revert hatom
  decide

theorem heavySpikeDesign_not_hasThreeArgmaxBlocks :
    ¬ HasThreeArgmaxBlocks heavySpikeDesign := by
  intro hthree
  have hbound := Finset.card_le_card heavySpike_chartArgmaxFamily_subset
  rw [Finset.card_singleton] at hbound
  have : (3 : ℕ) ≤ 1 := le_trans hthree hbound
  omega

theorem exists_allHeavy_not_hasCoveringArgmaxFamily :
    ∃ design : WeightedDesign 6 3, AllHeavy design ∧ ¬ HasCoveringArgmaxFamily design :=
  ⟨heavySpikeDesign, heavySpikeDesign_allHeavy, heavySpikeDesign_not_hasCoveringArgmaxFamily⟩

theorem exists_allHeavy_not_hasThreeArgmaxBlocks :
    ∃ design : WeightedDesign 6 3, AllHeavy design ∧ ¬ HasThreeArgmaxBlocks design :=
  ⟨heavySpikeDesign, heavySpikeDesign_allHeavy, heavySpikeDesign_not_hasThreeArgmaxBlocks⟩

theorem minimalityLayerIsProperOverAllHeavy :
    ∃ design : WeightedDesign 6 3, AllHeavy design
      ∧ ¬ (HasThreeArgmaxBlocks design ∧ HasCoveringArgmaxFamily design) :=
  ⟨heavySpikeDesign, heavySpikeDesign_allHeavy,
    fun hboth => heavySpikeDesign_not_hasThreeArgmaxBlocks hboth.1⟩

theorem not_forall_allHeavy_hasCoveringArgmaxFamily :
    ¬ ∀ design : WeightedDesign 6 3, AllHeavy design → HasCoveringArgmaxFamily design := by
  intro hall
  exact heavySpikeDesign_not_hasCoveringArgmaxFamily (hall heavySpikeDesign
    heavySpikeDesign_allHeavy)

theorem exists_allHeavy_not_hasSupportedCoveringArgmaxFamily :
    ∃ design : WeightedDesign 6 3, AllHeavy design
      ∧ ¬ HasSupportedCoveringArgmaxFamily design :=
  ⟨heavySpikeDesign, heavySpikeDesign_allHeavy, fun hsupported =>
    heavySpikeDesign_not_hasCoveringArgmaxFamily
      (hasCoveringArgmaxFamily_of_hasSupportedCoveringArgmaxFamily hsupported)⟩

end Gtz
