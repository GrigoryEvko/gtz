import Gtz.Design.ChartReadingLaw
import Gtz.Design.UnsignedCycleCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The kernel pointer and the chart exchange identity

At a chart point, a selection that reads nonpositively at some nonzero probe
names an outside label: the kappa-argmax of the probe readings.  Every
selection through that label reads strictly positively at the same probe.
The pointer is the chart-level exchange engine for the weak-to-strict
obligations: a non-strict selection hands every consumer an incoming label
that repairs its own failure direction.

* `directionChartGap_exchange` — the exact matrix identity for a single
  exchange of the selected set.
* `exists_outside_pointer_of_nonpos_reading` — the pointer theorem, for every
  spanning direction family and every selection of two or more labels.
* `exists_pointer_of_not_posDef` — the same package from a failed strictness
  test: the witness probe and the pointer arrive together.
* `exists_kFourPointer_of_not_posDef` — the K4 instance.

The pointer fixes ONE probe direction.  The directed probe of this module's
lane refuted the hosting conjecture (a PD tree through the pointer can fail to
exist), so the pointer is a repair step, not a selection law.
-/

namespace Gtz

open Matrix Finset

variable {size : ℕ}

/-- **The exchange identity.**  Replacing one selected label by an outside
label moves the chart gap by one incoming and one outgoing rank-one atom. -/
theorem directionChartGap_exchange (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {selected : Finset (Fin size)}
    {outLabel incLabel : Fin size} (hout : outLabel ∈ selected)
    (hinc : incLabel ∉ selected) :
    directionChartGap direction mass weight (insert incLabel (selected.erase outLabel))
      = directionChartGap direction mass weight selected
        + (mass incLabel / weight incLabel) • atomMatrix (direction incLabel)
        - (mass outLabel / weight outLabel) • atomMatrix (direction outLabel) := by
  have hincErase : incLabel ∉ selected.erase outLabel :=
    fun h => hinc (Finset.mem_of_mem_erase h)
  unfold directionChartGap
  rw [Finset.sum_insert hincErase, ← Finset.add_sum_erase _ _ hout]
  abel

/-- An exchange keeps the selection cardinality. -/
theorem directionChartGap_exchange_card {selected : Finset (Fin size)}
    {outLabel incLabel : Fin size} (hout : outLabel ∈ selected)
    (hinc : incLabel ∉ selected) :
    (insert incLabel (selected.erase outLabel)).card = selected.card := by
  have hincErase : incLabel ∉ selected.erase outLabel :=
    fun h => hinc (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hincErase, Finset.card_erase_of_mem hout]
  have hpos : 0 < selected.card := Finset.card_pos.mpr ⟨outLabel, hout⟩
  omega

/-- **THE POINTER THEOREM.**  At a chart point of a spanning family, a
selection of two or more labels that reads nonpositively at a nonzero probe
has an outside pointer label: every selection through the pointer reads
strictly positively at the same probe. -/
theorem exists_outside_pointer_of_nonpos_reading (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (hspan : ∀ probe : Fin 3 → ℝ, (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0)
    {selected : Finset (Fin size)} (hcard : 2 ≤ selected.card)
    {probe : Fin 3 → ℝ} (hprobe : probe ≠ 0)
    (hnonpos : probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe) ≤ 0) :
    ∃ pointer, pointer ∉ selected ∧
      ∀ swap : Finset (Fin size), pointer ∈ swap →
        0 < probe ⬝ᵥ (directionChartGap direction mass weight swap *ᵥ probe) := by
  rw [dotProduct_directionChartGap_mulVec_eq] at hnonpos
  have hgNonneg : ∀ label : Fin size,
      0 ≤ mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 :=
    fun label => mul_nonneg (div_nonneg (hmass label).le (hweight label).le) (sq_nonneg _)
  obtain ⟨member, hmember⟩ := Finset.card_pos.mp (by omega : 0 < selected.card)
  obtain ⟨good, -, hgoodMax⟩ := Finset.exists_max_image Finset.univ
    (fun label => mass label / weight label * (direction label ⬝ᵥ probe) ^ 2)
    ⟨member, mem_univ member⟩
  have hmaxAll : ∀ label, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
      ≤ mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 :=
    fun label => hgoodMax label (mem_univ label)
  have hreadSome : ∃ readLabel, direction readLabel ⬝ᵥ probe ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hprobe (hspan probe hall)
  obtain ⟨readLabel, hreadNe⟩ := hreadSome
  have hmaxPos : 0 < mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 := by
    refine lt_of_lt_of_le ?_ (hmaxAll readLabel)
    have hsq : 0 < (direction readLabel ⬝ᵥ probe) ^ 2 :=
      (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hreadNe))
    exact mul_pos (div_pos (hmass readLabel) (hweight readLabel)) hsq
  have hmeanLe := massReading_le_kappaReading direction mass weight hweight hsum probe hmaxAll
  have hmeanLt : (∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2)
      < mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 := by
    rcases lt_or_eq_of_le hmeanLe with hlt | heq
    · exact hlt
    · exfalso
      have hflat := kappaReading_flat_of_massReading_eq direction mass weight hweight hsum
        probe hmaxAll heq
      have hselSum : (∑ label ∈ selected,
            mass label / weight label * (direction label ⬝ᵥ probe) ^ 2)
          = selected.card * (mass good / weight good * (direction good ⬝ᵥ probe) ^ 2) := by
        rw [Finset.sum_congr rfl fun label _ => hflat label, Finset.sum_const,
          nsmul_eq_mul]
      rw [hselSum, ← heq] at hnonpos
      have hcardTwo : (2 : ℝ) ≤ (selected.card : ℝ) := by exact_mod_cast hcard
      rw [heq] at hnonpos
      nlinarith [hmaxPos]
  have hpointerOut : good ∉ selected := by
    intro hin
    have hselGe : mass good / weight good * (direction good ⬝ᵥ probe) ^ 2
        ≤ ∑ label ∈ selected, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 :=
      Finset.single_le_sum (fun label _ => hgNonneg label) hin
    linarith
  refine ⟨good, hpointerOut, fun swap hswapMem => ?_⟩
  rw [dotProduct_directionChartGap_mulVec_eq]
  have hswapGe : mass good / weight good * (direction good ⬝ᵥ probe) ^ 2
      ≤ ∑ label ∈ swap, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 :=
    Finset.single_le_sum (fun label _ => hgNonneg label) hswapMem
  linarith

/-- **The pointer from a failed strictness test.**  A selection that is not
strictly dominating at a chart point supplies a witness probe together with
its pointer: the selection reads nonpositively at the probe, and every
selection through the pointer reads strictly positively there. -/
theorem exists_pointer_of_not_posDef (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (hspan : ∀ probe : Fin 3 → ℝ, (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0)
    {selected : Finset (Fin size)} (hcard : 2 ≤ selected.card)
    (hnot : ¬ (directionChartGap direction mass weight selected).PosDef) :
    ∃ (probe : Fin 3 → ℝ) (pointer : Fin size), probe ≠ 0 ∧ pointer ∉ selected ∧
      probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe) ≤ 0 ∧
      ∀ swap : Finset (Fin size), pointer ∈ swap →
        0 < probe ⬝ᵥ (directionChartGap direction mass weight swap *ᵥ probe) := by
  have hwitness : ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
      probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe) ≤ 0 := by
    by_contra hall
    push Not at hall
    refine hnot (Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq
        (directionChartGap_transpose direction mass weight selected), fun x hx => ?_⟩)
    rw [star_trivial]
    exact hall x hx
  obtain ⟨probe, hprobe, hnonpos⟩ := hwitness
  obtain ⟨pointer, hout, hswap⟩ := exists_outside_pointer_of_nonpos_reading direction
    mass weight hmass hweight hsum hspan hcard hprobe hnonpos
  exact ⟨probe, pointer, hprobe, hout, hnonpos, hswap⟩

/-- The exchanged selection through the pointer reads strictly positively at
the witness probe, for every choice of the outgoing label. -/
theorem pointer_exchange_pos_reading (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {selected : Finset (Fin size)}
    {probe : Fin 3 → ℝ} {pointer outLabel : Fin size}
    (hswap : ∀ swap : Finset (Fin size), pointer ∈ swap →
      0 < probe ⬝ᵥ (directionChartGap direction mass weight swap *ᵥ probe)) :
    0 < probe ⬝ᵥ (directionChartGap direction mass weight
      (insert pointer (selected.erase outLabel)) *ᵥ probe) :=
  hswap _ (Finset.mem_insert_self pointer (selected.erase outLabel))

/-- **The K4 pointer.**  On the K4 chart, every non-strict selection of two or
more labels names an outside pointer whose every host selection beats the
witness probe. -/
theorem exists_kFourPointer_of_not_posDef (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} (hcard : 2 ≤ selected.card)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight selected).PosDef) :
    ∃ (probe : Fin 3 → ℝ) (pointer : Fin 6), probe ≠ 0 ∧ pointer ∉ selected ∧
      probe ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight selected
        *ᵥ probe) ≤ 0 ∧
      ∀ swap : Finset (Fin 6), pointer ∈ swap →
        0 < probe ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight swap
          *ᵥ probe) :=
  exists_pointer_of_not_posDef kFourDirection point.mass point.weight point.mass_pos
    point.weight_pos point.weight_sum_one kFourDirection_span hcard hnot

end Gtz
