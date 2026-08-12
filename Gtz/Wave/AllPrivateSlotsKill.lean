import Gtz.Wave.CoefficientCaptureForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The all-private kill — four private atoms exhaust the trace budget

The first pattern kill of the rank-four private-atom group.  If every one
of the four basis slots owns a private atom, the diagonal pin reads
`M_ss = value + weight` at each slot, and the trace budget `tr M = 2`
gives `4 * value + (sum of four weights) = 2`.  The four private atoms are
distinct, their weights sum to at most one, thus `value >= 1/4` — against
the negative value.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.false_of_private_atoms_at_every_slot` — **THE ALL-PRIVATE KILL.**

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

/-- **THE ALL-PRIVATE KILL.**  No stationary datum with a negative value
carries a four-slot basis in which every slot owns a private atom: the four
diagonal pins exhaust the trace budget. -/
theorem false_of_private_atoms_at_every_slot
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hvalueNeg : value < 0)
    (basisLabel : Fin 4 → activeIndex)
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (htrace : Matrix.trace M = 2)
    (privateAtom : Fin 4 → Fin size)
    (hmem : ∀ slotIndex, basisLabel slotIndex ∈ activeSet)
    (hatomMem : ∀ slotIndex,
      privateAtom slotIndex ∈ activeSubset (basisLabel slotIndex))
    (hprivate : ∀ slotIndex columnIndex, columnIndex ≠ slotIndex →
      tightDir (basisLabel columnIndex) (privateAtom slotIndex) = 0)
    (hslotNe : ∀ slotIndex,
      tightDir (basisLabel slotIndex) (privateAtom slotIndex) ≠ 0) :
    False := by
  classical
  have hpin : ∀ slotIndex,
      M slotIndex slotIndex = value + weight (privateAtom slotIndex) :=
    fun slotIndex => coefficient_diagonal_eq_of_private_atom hdata basisLabel
      hrepresentation (hmem slotIndex) (hatomMem slotIndex)
      (fun columnIndex hne => hprivate slotIndex columnIndex hne)
      (hslotNe slotIndex)
  have hinjective : Function.Injective privateAtom := by
    intro firstSlot secondSlot heq
    by_contra hne
    have hzero := hprivate secondSlot firstSlot hne
    rw [← heq] at hzero
    exact hslotNe firstSlot hzero
  have htraceSum : ∑ slotIndex : Fin 4, M slotIndex slotIndex = 2 := htrace
  have hpinSum : ∑ slotIndex : Fin 4,
      (value + weight (privateAtom slotIndex)) = 2 := by
    rw [← htraceSum]
    exact Finset.sum_congr rfl fun slotIndex _ => (hpin slotIndex).symm
  rw [Finset.sum_add_distrib, Finset.sum_const] at hpinSum
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    at hpinSum
  have himageSum : ∑ slotIndex : Fin 4, weight (privateAtom slotIndex)
      = ∑ atomIndex ∈ Finset.univ.image privateAtom, weight atomIndex :=
    (Finset.sum_image fun firstSlot _ secondSlot _ heq =>
      hinjective heq).symm
  have hbound : ∑ atomIndex ∈ Finset.univ.image privateAtom, weight atomIndex
      ≤ ∑ atomIndex : Fin size, weight atomIndex :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun atomIndex _ _ => le_of_lt (hdata.weight_pos atomIndex))
  rw [hdata.weight_sum_one] at hbound
  rw [himageSum] at hpinSum
  linarith

end Gtz
