import Gtz.Wave.CornerCharacteristic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The complete-pair kill — six pair atoms exhaust the corner budget

The second symmetric function of an idempotent with trace two is one, and
it equals the sum of all corner determinants.  When every slot pair
carries a dense pair atom, each corner determinant is at most the shifted
weight of its atom.  The six atoms are distinct, thus the corner budget
gives `2 <= 12 * value + 2`, against the negative value.  This kill
closes the complete-graph representative of the dense census branch under
a diagonal Gram.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.false_of_complete_pair_pattern` — **THE KILL.**

## Vacuity

The statement takes the negative value as a hypothesis, and a crux
supplies it.  It is vacuous if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE COMPLETE-PAIR KILL.**  Under a diagonal Gram, a basis in which
every slot pair carries a dense pair atom exhausts the corner budget. -/
theorem false_of_complete_pair_pattern
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hvalueNeg : value < 0)
    (basisLabel : Fin 4 → activeIndex)
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    {gramWeight : Fin 4 → ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hidempotent : M * M = M)
    (htrace : Matrix.trace M = 2)
    (hmemAll : ∀ columnIndex, basisLabel columnIndex ∈ activeSet)
    (hgramPos : ∀ slotIndex, 0 < gramWeight slotIndex)
    (hYpsd : (Matrix.diagonal gramWeight
      - M * Matrix.diagonal gramWeight).PosSemidef)
    (edgeAtom : Fin 4 → Fin 4 → Fin size)
    (hedgeSymm : ∀ firstSlot secondSlot, edgeAtom firstSlot secondSlot
      = edgeAtom secondSlot firstSlot)
    (hedgeDense : ∀ firstSlot secondSlot, firstSlot ≠ secondSlot →
      tightDir (basisLabel firstSlot) (edgeAtom firstSlot secondSlot) ≠ 0)
    (hedgeCarriers : ∀ firstSlot secondSlot, firstSlot ≠ secondSlot →
      ∀ columnIndex, columnIndex ≠ firstSlot → columnIndex ≠ secondSlot →
        tightDir (basisLabel columnIndex) (edgeAtom firstSlot secondSlot) = 0)
    (hedgeBlock : ∀ firstSlot secondSlot, firstSlot ≠ secondSlot →
      edgeAtom firstSlot secondSlot ∈ activeSubset (basisLabel firstSlot)) :
    False := by
  classical
  have hdetCap : ∀ firstSlot secondSlot : Fin 4, firstSlot ≠ secondSlot →
      M firstSlot firstSlot * M secondSlot secondSlot
        - M firstSlot secondSlot * M secondSlot firstSlot
      ≤ value + weight (edgeAtom firstSlot secondSlot) := by
    intro firstSlot secondSlot hne
    have hblockSecond : edgeAtom firstSlot secondSlot
        ∈ activeSubset (basisLabel secondSlot) := by
      rw [hedgeSymm]
      exact hedgeBlock secondSlot firstSlot (Ne.symm hne)
    have hrowFirst := two_carrier_row_reading hdata basisLabel hrepresentation hne
      (hmemAll firstSlot) (hedgeBlock firstSlot secondSlot hne)
      (hedgeCarriers firstSlot secondSlot hne)
    have hrowSecond := two_carrier_row_reading hdata basisLabel hrepresentation hne
      (hmemAll secondSlot) hblockSecond
      (hedgeCarriers firstSlot secondSlot hne)
    have hfloor := weight_ge_neg_value_of_isChartStationaryData hdata
      (edgeAtom firstSlot secondSlot)
    exact corner_det_le_of_eigen_rows hrowFirst hrowSecond
      (Or.inl (hedgeDense firstSlot secondSlot hne))
      (by linarith)
      (value_add_weight_lt_one_of_isChartStationaryData_of_neg hdata hvalueNeg
        (edgeAtom firstSlot secondSlot))
      (corner_complement_det_nonneg_of_diagonal_gram hgramPos hYpsd hne)
  have hcornerSum : ∑ firstSlot : Fin 4, ∑ secondSlot : Fin 4,
      (M firstSlot firstSlot * M secondSlot secondSlot
        - M firstSlot secondSlot * M secondSlot firstSlot) = 2 := by
    have hproductSum : ∑ firstSlot : Fin 4, ∑ secondSlot : Fin 4,
        M firstSlot firstSlot * M secondSlot secondSlot = 4 := by
      rw [← Finset.sum_mul_sum]
      have htraceSum : ∑ slotIndex : Fin 4, M slotIndex slotIndex = 2 := htrace
      rw [htraceSum]
      norm_num
    have hcrossSum : ∑ firstSlot : Fin 4, ∑ secondSlot : Fin 4,
        M firstSlot secondSlot * M secondSlot firstSlot = 2 := by
      have hMM : Matrix.trace (M * M) = 2 := by rw [hidempotent, htrace]
      have hexpand : Matrix.trace (M * M)
          = ∑ firstSlot : Fin 4, ∑ secondSlot : Fin 4,
              M firstSlot secondSlot * M secondSlot firstSlot :=
        Finset.sum_congr rfl fun slotIndex _ => Matrix.mul_apply
      rw [← hexpand, hMM]
    simp only [Finset.sum_sub_distrib]
    rw [hproductSum, hcrossSum]
    norm_num
  have hedgeMemFirst : ∀ i j k l : Fin 4, i ≠ j → k ≠ l →
      edgeAtom i j = edgeAtom k l → i ≠ k → i ≠ l → False := by
    intro i j k l hij hkl heq hik hil
    have hzero := hedgeCarriers k l hkl i hik hil
    rw [← heq] at hzero
    exact hedgeDense i j hij hzero
  have hedgeMemSecond : ∀ i j k l : Fin 4, i ≠ j → k ≠ l →
      edgeAtom i j = edgeAtom k l → j ≠ k → j ≠ l → False := by
    intro i j k l hij hkl heq hjk hjl
    have hdense : tightDir (basisLabel j) (edgeAtom i j) ≠ 0 := by
      rw [hedgeSymm]
      exact hedgeDense j i (Ne.symm hij)
    have hzero := hedgeCarriers k l hkl j hjk hjl
    rw [← heq] at hzero
    exact hdense hzero
  have hne_01_02 : edgeAtom 0 1 ≠ edgeAtom 0 2 := fun heq =>
    hedgeMemSecond 0 1 0 2 (by decide) (by decide) heq (by decide) (by decide)
  have hne_01_03 : edgeAtom 0 1 ≠ edgeAtom 0 3 := fun heq =>
    hedgeMemSecond 0 1 0 3 (by decide) (by decide) heq (by decide) (by decide)
  have hne_01_12 : edgeAtom 0 1 ≠ edgeAtom 1 2 := fun heq =>
    hedgeMemFirst 0 1 1 2 (by decide) (by decide) heq (by decide) (by decide)
  have hne_01_13 : edgeAtom 0 1 ≠ edgeAtom 1 3 := fun heq =>
    hedgeMemFirst 0 1 1 3 (by decide) (by decide) heq (by decide) (by decide)
  have hne_01_23 : edgeAtom 0 1 ≠ edgeAtom 2 3 := fun heq =>
    hedgeMemFirst 0 1 2 3 (by decide) (by decide) heq (by decide) (by decide)
  have hne_02_03 : edgeAtom 0 2 ≠ edgeAtom 0 3 := fun heq =>
    hedgeMemSecond 0 2 0 3 (by decide) (by decide) heq (by decide) (by decide)
  have hne_02_12 : edgeAtom 0 2 ≠ edgeAtom 1 2 := fun heq =>
    hedgeMemFirst 0 2 1 2 (by decide) (by decide) heq (by decide) (by decide)
  have hne_02_13 : edgeAtom 0 2 ≠ edgeAtom 1 3 := fun heq =>
    hedgeMemFirst 0 2 1 3 (by decide) (by decide) heq (by decide) (by decide)
  have hne_02_23 : edgeAtom 0 2 ≠ edgeAtom 2 3 := fun heq =>
    hedgeMemFirst 0 2 2 3 (by decide) (by decide) heq (by decide) (by decide)
  have hne_03_12 : edgeAtom 0 3 ≠ edgeAtom 1 2 := fun heq =>
    hedgeMemFirst 0 3 1 2 (by decide) (by decide) heq (by decide) (by decide)
  have hne_03_13 : edgeAtom 0 3 ≠ edgeAtom 1 3 := fun heq =>
    hedgeMemFirst 0 3 1 3 (by decide) (by decide) heq (by decide) (by decide)
  have hne_03_23 : edgeAtom 0 3 ≠ edgeAtom 2 3 := fun heq =>
    hedgeMemFirst 0 3 2 3 (by decide) (by decide) heq (by decide) (by decide)
  have hne_12_13 : edgeAtom 1 2 ≠ edgeAtom 1 3 := fun heq =>
    hedgeMemSecond 1 2 1 3 (by decide) (by decide) heq (by decide) (by decide)
  have hne_12_23 : edgeAtom 1 2 ≠ edgeAtom 2 3 := fun heq =>
    hedgeMemFirst 1 2 2 3 (by decide) (by decide) heq (by decide) (by decide)
  have hne_13_23 : edgeAtom 1 3 ≠ edgeAtom 2 3 := fun heq =>
    hedgeMemFirst 1 3 2 3 (by decide) (by decide) heq (by decide) (by decide)
  have hfifthNotMem : edgeAtom 1 3 ∉ ({edgeAtom 2 3} : Finset (Fin size)) := by
    simp [hne_13_23]
  have hfourthNotMem : edgeAtom 1 2
      ∉ ({edgeAtom 1 3, edgeAtom 2 3} : Finset (Fin size)) := by
    simp [hne_12_13, hne_12_23]
  have hthirdNotMem : edgeAtom 0 3
      ∉ ({edgeAtom 1 2, edgeAtom 1 3, edgeAtom 2 3} : Finset (Fin size)) := by
    simp [hne_03_12, hne_03_13, hne_03_23]
  have hsecondNotMem : edgeAtom 0 2
      ∉ ({edgeAtom 0 3, edgeAtom 1 2, edgeAtom 1 3, edgeAtom 2 3}
        : Finset (Fin size)) := by
    simp [hne_02_03, hne_02_12, hne_02_13, hne_02_23]
  have hfirstNotMem : edgeAtom 0 1
      ∉ ({edgeAtom 0 2, edgeAtom 0 3, edgeAtom 1 2, edgeAtom 1 3, edgeAtom 2 3}
        : Finset (Fin size)) := by
    simp [hne_01_02, hne_01_03, hne_01_12, hne_01_13, hne_01_23]
  have hweightExpand : ∑ atomIndex ∈
      ({edgeAtom 0 1, edgeAtom 0 2, edgeAtom 0 3, edgeAtom 1 2, edgeAtom 1 3,
        edgeAtom 2 3} : Finset (Fin size)), weight atomIndex
      = weight (edgeAtom 0 1) + (weight (edgeAtom 0 2) + (weight (edgeAtom 0 3)
        + (weight (edgeAtom 1 2) + (weight (edgeAtom 1 3)
          + weight (edgeAtom 2 3))))) := by
    rw [Finset.sum_insert hfirstNotMem, Finset.sum_insert hsecondNotMem,
      Finset.sum_insert hthirdNotMem, Finset.sum_insert hfourthNotMem,
      Finset.sum_insert hfifthNotMem, Finset.sum_singleton]
  have hweightBound : ∑ atomIndex ∈
      ({edgeAtom 0 1, edgeAtom 0 2, edgeAtom 0 3, edgeAtom 1 2, edgeAtom 1 3,
        edgeAtom 2 3} : Finset (Fin size)), weight atomIndex ≤ 1 := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ
        ({edgeAtom 0 1, edgeAtom 0 2, edgeAtom 0 3, edgeAtom 1 2, edgeAtom 1 3,
          edgeAtom 2 3} : Finset (Fin size)))
      (fun atomIndex _ _ => le_of_lt (hdata.weight_pos atomIndex))
    rw [hdata.weight_sum_one] at hle
    exact hle
  rw [hweightExpand] at hweightBound
  have hboundSum : ∑ firstSlot : Fin 4, ∑ secondSlot : Fin 4,
      (M firstSlot firstSlot * M secondSlot secondSlot
        - M firstSlot secondSlot * M secondSlot firstSlot)
      ≤ ∑ firstSlot : Fin 4, ∑ secondSlot : Fin 4,
          (if firstSlot = secondSlot then 0
            else value + weight (edgeAtom firstSlot secondSlot)) := by
    refine Finset.sum_le_sum fun firstSlot _ => Finset.sum_le_sum
      fun secondSlot _ => ?_
    by_cases hcase : firstSlot = secondSlot
    · rw [if_pos hcase, hcase]
      ring_nf
      exact le_refl 0
    · rw [if_neg hcase]
      exact hdetCap firstSlot secondSlot hcase
  have hboundEval : ∑ firstSlot : Fin 4, ∑ secondSlot : Fin 4,
      (if firstSlot = secondSlot then 0
        else value + weight (edgeAtom firstSlot secondSlot))
      = 12 * value + 2 * (weight (edgeAtom 0 1) + (weight (edgeAtom 0 2)
        + (weight (edgeAtom 0 3) + (weight (edgeAtom 1 2)
          + (weight (edgeAtom 1 3) + weight (edgeAtom 2 3)))))) := by
    simp +decide only [Fin.sum_univ_four, if_true, if_false]
    rw [hedgeSymm 1 0, hedgeSymm 2 0, hedgeSymm 2 1, hedgeSymm 3 0,
      hedgeSymm 3 1, hedgeSymm 3 2]
    ring
  rw [hcornerSum, hboundEval] at hboundSum
  linarith

end Gtz
