import Gtz.Wave.ConjugationTraceTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The fully-private-block kill — a private block exhausts the trace budget

Fix a private slot whose support meets no other basis column, and
enumerations of the off slots and the off atoms with these properties: the
off atoms are exactly the atoms off the private support, and each off
block contains every off atom.  Then the off corner of the coefficient
matrix intertwines with the shifted-weight diagonal through the off column
matrix, and the column matrix has a trivial kernel through the left
inverse.  The trace transfer, the diagonal pin, and the trace budget give
`value + (off count) * value + (private weight) - (private mass) = 1`.
The left side is negative, and the kill follows.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.false_of_fully_private_block` — **THE KILL.**

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
variable {basisCount offCount : ℕ}

/-- **THE FULLY-PRIVATE-BLOCK KILL.**  No stationary datum with a negative
value and the trace budget two carries a basis with a fully private slot
whose off slots all read the shifted-weight diagonal. -/
theorem false_of_fully_private_block
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hvalueNeg : value < 0)
    (basisLabel : Fin basisCount → activeIndex)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (htrace : Matrix.trace M = 2)
    {privateSlot : Fin basisCount}
    (hmemAll : ∀ columnIndex, basisLabel columnIndex ∈ activeSet)
    (hprivateBlock : ∀ atomIndex : Fin size,
      tightDir (basisLabel privateSlot) atomIndex ≠ 0 →
      ∀ columnIndex, columnIndex ≠ privateSlot →
        tightDir (basisLabel columnIndex) atomIndex = 0)
    {privateAtom : Fin size}
    (hatomMem : privateAtom ∈ activeSubset (basisLabel privateSlot))
    (hslotNe : tightDir (basisLabel privateSlot) privateAtom ≠ 0)
    (slotEnum : Fin offCount → Fin basisCount)
    (hslotInj : Function.Injective slotEnum)
    (hslotOff : ∀ offIndex, slotEnum offIndex ≠ privateSlot)
    (hslotSurj : ∀ columnIndex, columnIndex ≠ privateSlot →
      ∃ offIndex, slotEnum offIndex = columnIndex)
    (atomEnum : Fin offCount → Fin size)
    (hatomInj : Function.Injective atomEnum)
    (hatomOff : ∀ offIndex, tightDir (basisLabel privateSlot) (atomEnum offIndex) = 0)
    (hatomSurj : ∀ atomIndex, tightDir (basisLabel privateSlot) atomIndex = 0 →
      ∃ offIndex, atomEnum offIndex = atomIndex)
    (hcoverBlock : ∀ offIndex, ∀ atomIndex : Fin size,
      atomIndex ∈ activeSubset (basisLabel (slotEnum offIndex))
        ∨ tightDir (basisLabel privateSlot) atomIndex ≠ 0) :
    False := by
  classical
  have hpin : M privateSlot privateSlot = value + weight privateAtom :=
    coefficient_diagonal_eq_of_private_atom hdata basisLabel hrepresentation
      (hmemAll privateSlot) hatomMem
      (fun columnIndex hne => hprivateBlock privateAtom hslotNe columnIndex hne)
      hslotNe
  have hexpand : ∀ rowIndex colIndex : Fin offCount,
      ∑ offIndex : Fin offCount,
        tightDir (basisLabel (slotEnum offIndex)) (atomEnum rowIndex)
          * M (slotEnum offIndex) (slotEnum colIndex)
      = ∑ slotIndex : Fin basisCount,
          tightDir (basisLabel slotIndex) (atomEnum rowIndex)
            * M slotIndex (slotEnum colIndex) := by
    intro rowIndex colIndex
    have hstep : ∑ slotIndex ∈ Finset.univ.image slotEnum,
        tightDir (basisLabel slotIndex) (atomEnum rowIndex)
          * M slotIndex (slotEnum colIndex)
        = ∑ offIndex : Fin offCount,
            tightDir (basisLabel (slotEnum offIndex)) (atomEnum rowIndex)
              * M (slotEnum offIndex) (slotEnum colIndex) :=
      Finset.sum_image fun firstIndex _ secondIndex _ heq => hslotInj heq
    rw [← hstep]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro slotIndex _ hnotMem
    by_cases hprivateCase : slotIndex = privateSlot
    · rw [hprivateCase, hatomOff rowIndex, zero_mul]
    · obtain ⟨offIndex, hoff⟩ := hslotSurj slotIndex hprivateCase
      exact absurd (Finset.mem_image.mpr ⟨offIndex, Finset.mem_univ _, hoff⟩) hnotMem
  have hfull : ∀ rowIndex colIndex : Fin offCount,
      ∑ slotIndex : Fin basisCount,
        tightDir (basisLabel slotIndex) (atomEnum rowIndex)
          * M slotIndex (slotEnum colIndex)
      = (value + weight (atomEnum rowIndex))
        * tightDir (basisLabel (slotEnum colIndex)) (atomEnum rowIndex) := by
    intro rowIndex colIndex
    have hblockMem : atomEnum rowIndex ∈ activeSubset (basisLabel (slotEnum colIndex)) :=
      (hcoverBlock colIndex (atomEnum rowIndex)).resolve_right fun hcontra =>
        hcontra (hatomOff rowIndex)
    have hentry : ∑ slotIndex : Fin basisCount,
        tightDir (basisLabel slotIndex) (atomEnum rowIndex)
          * M slotIndex (slotEnum colIndex)
        = (tightBasisColumns tightDir basisLabel * M) (atomEnum rowIndex)
            (slotEnum colIndex) := by
      rw [Matrix.mul_apply]
      rfl
    have hcolumnEntry : (projection * tightBasisColumns tightDir basisLabel)
        (atomEnum rowIndex) (slotEnum colIndex)
        = (projection *ᵥ tightDir (basisLabel (slotEnum colIndex)))
            (atomEnum rowIndex) := by
      rw [Matrix.mul_apply]
      rfl
    rw [hentry, ← hrepresentation, hcolumnEntry,
      projection_mulVec_tightDir_of_mem hdata (hmemAll (slotEnum colIndex)) hblockMem]
  have hconj : (Matrix.of fun rowIndex colIndex =>
        tightDir (basisLabel (slotEnum colIndex)) (atomEnum rowIndex))
      * (Matrix.of fun rowIndex colIndex =>
          M (slotEnum rowIndex) (slotEnum colIndex))
      = Matrix.diagonal (fun offIndex => value + weight (atomEnum offIndex))
        * Matrix.of (fun rowIndex colIndex =>
            tightDir (basisLabel (slotEnum colIndex)) (atomEnum rowIndex)) := by
    ext rowIndex colIndex
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    simp only [Matrix.of_apply]
    rw [hexpand rowIndex colIndex, hfull rowIndex colIndex]
  have hker : ∀ coeffVec : Fin offCount → ℝ,
      (Matrix.of fun rowIndex colIndex =>
        tightDir (basisLabel (slotEnum colIndex)) (atomEnum rowIndex)) *ᵥ coeffVec = 0 →
      coeffVec = 0 := by
    intro coeffVec hzero
    have hBlift : tightBasisColumns tightDir basisLabel
        *ᵥ (fun columnIndex => ∑ offIndex : Fin offCount,
            if slotEnum offIndex = columnIndex then coeffVec offIndex else 0) = 0 := by
      funext atomIndex
      rw [Pi.zero_apply]
      have hswap : (tightBasisColumns tightDir basisLabel
          *ᵥ (fun columnIndex => ∑ offIndex : Fin offCount,
              if slotEnum offIndex = columnIndex then coeffVec offIndex else 0)) atomIndex
          = ∑ offIndex : Fin offCount,
              tightDir (basisLabel (slotEnum offIndex)) atomIndex
                * coeffVec offIndex := by
        calc (tightBasisColumns tightDir basisLabel
            *ᵥ (fun columnIndex => ∑ offIndex : Fin offCount,
                if slotEnum offIndex = columnIndex then coeffVec offIndex else 0))
              atomIndex
            = ∑ columnIndex : Fin basisCount,
                tightDir (basisLabel columnIndex) atomIndex
                  * ∑ offIndex : Fin offCount,
                      (if slotEnum offIndex = columnIndex then coeffVec offIndex
                        else 0) := rfl
          _ = ∑ columnIndex : Fin basisCount, ∑ offIndex : Fin offCount,
                (if slotEnum offIndex = columnIndex then
                  tightDir (basisLabel columnIndex) atomIndex * coeffVec offIndex
                  else 0) := by
              refine Finset.sum_congr rfl fun columnIndex _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun offIndex _ => ?_
              rw [mul_ite, mul_zero]
          _ = ∑ offIndex : Fin offCount, ∑ columnIndex : Fin basisCount,
                (if slotEnum offIndex = columnIndex then
                  tightDir (basisLabel columnIndex) atomIndex * coeffVec offIndex
                  else 0) := Finset.sum_comm
          _ = ∑ offIndex : Fin offCount,
                tightDir (basisLabel (slotEnum offIndex)) atomIndex
                  * coeffVec offIndex := by
              refine Finset.sum_congr rfl fun offIndex _ => ?_
              rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
      rw [hswap]
      by_cases hatomCase : tightDir (basisLabel privateSlot) atomIndex = 0
      · obtain ⟨offIndex, hoff⟩ := hatomSurj atomIndex hatomCase
        have hrow : ∑ offIndex' : Fin offCount,
            tightDir (basisLabel (slotEnum offIndex')) atomIndex * coeffVec offIndex'
            = ((Matrix.of fun rowIndex colIndex =>
                tightDir (basisLabel (slotEnum colIndex)) (atomEnum rowIndex))
                  *ᵥ coeffVec) offIndex := by
          rw [← hoff]
          rfl
        rw [hrow, hzero]
        rfl
      · refine Finset.sum_eq_zero fun offIndex _ => ?_
        rw [hprivateBlock atomIndex hatomCase (slotEnum offIndex) (hslotOff offIndex),
          zero_mul]
    have hliftZero : (fun columnIndex => ∑ offIndex : Fin offCount,
        if slotEnum offIndex = columnIndex then coeffVec offIndex else 0)
        = (0 : Fin basisCount → ℝ) := by
      have hchain : (fun columnIndex => ∑ offIndex : Fin offCount,
          if slotEnum offIndex = columnIndex then coeffVec offIndex else 0)
          = L *ᵥ (tightBasisColumns tightDir basisLabel
              *ᵥ (fun columnIndex => ∑ offIndex : Fin offCount,
                  if slotEnum offIndex = columnIndex then coeffVec offIndex else 0)) := by
        rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
      rw [hchain, hBlift, Matrix.mulVec_zero]
    funext offIndex
    have hpointZero := congrFun hliftZero (slotEnum offIndex)
    have hcollapse : (∑ offIndex' : Fin offCount,
        if slotEnum offIndex' = slotEnum offIndex then coeffVec offIndex' else 0)
        = coeffVec offIndex := by
      rw [Finset.sum_eq_single offIndex
        (fun otherIndex _ hneOther => if_neg fun heq => hneOther (hslotInj heq))
        (fun hnotMem => absurd (Finset.mem_univ _) hnotMem)]
      rw [if_pos rfl]
    rw [Pi.zero_apply, ← hcollapse]
    exact hpointZero
  have htraceEq := trace_eq_of_kernel_free_conjugation hconj hker
  have htraceOff : ∑ offIndex : Fin offCount, M (slotEnum offIndex) (slotEnum offIndex)
      = ∑ offIndex : Fin offCount, (value + weight (atomEnum offIndex)) := by
    have hleftTrace : Matrix.trace (Matrix.of fun rowIndex colIndex =>
        M (slotEnum rowIndex) (slotEnum colIndex))
        = ∑ offIndex : Fin offCount, M (slotEnum offIndex) (slotEnum offIndex) := rfl
    rw [← hleftTrace, htraceEq, Matrix.trace_diagonal]
  have hsplit : Matrix.trace M
      = M privateSlot privateSlot
        + ∑ offIndex : Fin offCount, M (slotEnum offIndex) (slotEnum offIndex) := by
    have himage : Finset.univ.image slotEnum = Finset.univ.erase privateSlot := by
      apply Finset.Subset.antisymm
      · intro columnIndex hmem
        obtain ⟨offIndex, _, rfl⟩ := Finset.mem_image.mp hmem
        exact Finset.mem_erase.mpr ⟨hslotOff offIndex, Finset.mem_univ _⟩
      · intro columnIndex hmem
        obtain ⟨offIndex, hoff⟩ :=
          hslotSurj columnIndex (Finset.mem_erase.mp hmem).1
        exact Finset.mem_image.mpr ⟨offIndex, Finset.mem_univ _, hoff⟩
    have herase : ∑ columnIndex ∈ Finset.univ.erase privateSlot,
        M columnIndex columnIndex
        = ∑ offIndex : Fin offCount, M (slotEnum offIndex) (slotEnum offIndex) := by
      rw [← himage]
      exact Finset.sum_image fun firstIndex _ secondIndex _ heq => hslotInj heq
    have htraceSum : Matrix.trace M
        = ∑ columnIndex : Fin basisCount, M columnIndex columnIndex := rfl
    rw [← herase, htraceSum,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ privateSlot)]
  have hweightOff : ∑ offIndex : Fin offCount, weight (atomEnum offIndex)
      = ∑ atomIndex ∈ Finset.univ.filter
          (fun atomIndex => ¬ tightDir (basisLabel privateSlot) atomIndex ≠ 0),
          weight atomIndex := by
    have himageAtom : Finset.univ.image atomEnum
        = Finset.univ.filter
            (fun atomIndex => ¬ tightDir (basisLabel privateSlot) atomIndex ≠ 0) := by
      apply Finset.Subset.antisymm
      · intro atomIndex hmem
        obtain ⟨offIndex, _, rfl⟩ := Finset.mem_image.mp hmem
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun hcontra => hcontra (hatomOff offIndex)⟩
      · intro atomIndex hmem
        obtain ⟨offIndex, hoff⟩ :=
          hatomSurj atomIndex (not_not.mp (Finset.mem_filter.mp hmem).2)
        exact Finset.mem_image.mpr ⟨offIndex, Finset.mem_univ _, hoff⟩
    rw [← himageAtom]
    exact (Finset.sum_image fun firstIndex _ secondIndex _ heq => hatomInj heq).symm
  have hweightTotal : ∑ atomIndex ∈ Finset.univ.filter
        (fun atomIndex => tightDir (basisLabel privateSlot) atomIndex ≠ 0),
        weight atomIndex
      + ∑ offIndex : Fin offCount, weight (atomEnum offIndex) = 1 := by
    rw [hweightOff, Finset.sum_filter_add_sum_filter_not, hdata.weight_sum_one]
  have hprivateWeightLe : weight privateAtom
      ≤ ∑ atomIndex ∈ Finset.univ.filter
          (fun atomIndex => tightDir (basisLabel privateSlot) atomIndex ≠ 0),
          weight atomIndex :=
    Finset.single_le_sum (fun atomIndex _ => le_of_lt (hdata.weight_pos atomIndex))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hslotNe⟩)
  have hoffSum : ∑ offIndex : Fin offCount, (value + weight (atomEnum offIndex))
      = (offCount : ℝ) * value
        + ∑ offIndex : Fin offCount, weight (atomEnum offIndex) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hoffNonpos : (offCount : ℝ) * value ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_lt hvalueNeg)
  rw [hsplit, hpin, htraceOff, hoffSum] at htrace
  linarith

end Gtz
