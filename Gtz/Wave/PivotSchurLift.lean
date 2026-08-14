import Gtz.Wave.AtomBoundaryWitness
import Gtz.Wave.AtomProductInflation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The pivot lift of rank two to rank three

A TIGHT FRAME of six atoms in three dimensions carries a Gram matrix that is
symmetric and idempotent of trace three.  A TRIPLE DOMINATES when the shifted
Gram block of its three slots is positive definite.  This module lifts the
landed rank-two selection theorem to rank three along one pivot slot, and it
prices the lift exactly.

## The reduction

Take a pivot slot with a positive shifted diagonal.  Write the plane of the
pivot for the orthogonal complement of the pivot atom.  The SHADOW of a slot is
its part in that plane, and the CHARGE of a slot is its reading against the
pivot atom.  Three laws hold, and this module proves each one.

* The shadows are a tight frame of the plane.
* The shadow masses total the rank minus one.  At rank three the total is two,
  which is the trace of the identity of the plane.  The mass total two against
  a scale total below one is the whole strength of the rank-two theorem.
* The charge weighted shadows total zero, and the charges square to the pivot
  leverage.

The Schur complement of the shifted Gram at the pivot is then a two by two
reading.  It is the shifted shadow Gram of the two partners, minus one rank-one
term of the two charges.  That term carries the weight `scale pivot / (leverage
* shifted diagonal)`.  The dictionary is landed, and this module reads it again through
the two laws above.

## What the lift costs, and what this module adds

The rank-two theorem needs a scale total below one.  A consumer must pay the
rank-one term inside the plane scales.  The landed engine
`Gtz.exists_deflated_pair_of_live_product_inflation` asks the product law at
every LIVE pair, and a pair is live there when both pair minors are positive.
Almost every slot of a tight frame is live, so that engine pays the rank-one
term at almost every slot off the pivot.

This module weakens the demand.  The rank-two closure returns a pair of
POSITIVE shadow gaps.  A slot whose plane scale reaches its shadow mass has no
positive gap, so the closure can never return it.  The SURVIVOR test measures
the pair minor against the inflation itself.  Its division-free reading is
`shifted diagonal * extra < pair minor`.  The engine of this module asks the
product law only at the surviving pairs.  `Gtz.survivorProduct_of_liveProduct`
proves that this hypothesis is weaker than the live one.

A consumer names a KEPT set and spends `Gtz.deadSlotInflation` on every slot
outside it.  The death of one such slot costs one pair minor of the budget.  The
product law then stays inside the kept set.

The second law of this module is independent of any pivot.  The four triple
determinants that complete one fixed pair add to an explicit polynomial in six
readings of that pair.  A positive value of that polynomial gives a completion
of positive determinant, and Sylvester then gives the dominating triple.

## The two laws carry the field differently

The pivot lift consumes `Gtz.atomPairGramClosed_holds`, which is the rank-two
plane closure.  That closure is REAL, and `Gtz.blochTetra_not_dominates` shows
that its Hermitian analogue is false at four atoms.  The pivot lift carries the
realness of the cell exactly through the plane closure, and nowhere else.

The pair completion law consumes only the trace of the frame and the two row
laws of the Gram.  Those laws hold over the Hermitian field word for word.  The
pair completion cell is FIELD AGNOSTIC.  It cannot close the cell alone, because
the Hermitian analogue of the cell is false.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomGram_row_cross` — **THE CROSS ROW LAW.**  The row of one slot
  against the row of a second slot totals the Gram entry of the two slots.
* `Gtz.sum_read_smul_atom` — **THE FRAME RECONSTRUCTION.**  A vector is the
  reading weighted sum of the atoms.
* `Gtz.shadow_frame_law` — **THE SHADOW FRAME LAW.**  The shadows of a tight
  frame at a pivot are a tight frame of the plane of that pivot.
* `Gtz.sum_shadow_energy` — **THE SHADOW MASS LAW.**  The shadow masses total
  the rank minus one.
* `Gtz.sum_charge_smul_shadow` — **THE CHARGE LAW.**  The charge weighted
  shadows total zero.
* `Gtz.sum_charge_sq_off_pivot` — **THE CHARGE ENERGY.**  The squared charges
  off the pivot total the leverage minus its square.
* `Gtz.exists_heavy_leverage_slot`, `Gtz.exists_live_heavy_pivot` — **THE HEAVY
  PIVOT PIGEONHOLE.**  Some slot carries the rank share of its scale in
  leverage, and under a scale total of at most one that slot is live.
* `Gtz.atomPairMinor_pos_iff_shadow_gap`,
  `Gtz.atomTripleDet_pos_iff_deflated_pair` — the two directions of the
  dictionary, as equivalences.
* `Gtz.AtomSlotSurvives`, `Gtz.atomPairMinor_pos_of_survives`,
  `Gtz.survivorProduct_of_liveProduct` — **THE SURVIVOR TEST**, and the proof
  that it asks less than the landed live test.
* `Gtz.exists_deflated_pair_of_survivor_inflation` — **THE SURVIVOR INFLATION
  ENGINE.**  The product law at the surviving pairs only, plus one
  division-free budget, supplies a deflated pair at the pivot.
* `Gtz.exists_pivotPair_of_survivor_inflation`,
  `Gtz.exists_sylvester_of_survivor_inflation` — the engine in the two shapes
  the campaign consumes.
* `Gtz.deadSlotInflation`, `Gtz.deadSlotInflation_kills`,
  `Gtz.exists_deflated_pair_of_dropSet` — **THE DROP SET CONSUMER.**  A
  consumer names a kept set, pays one pair minor for each dropped slot, and
  asks the product law only inside the kept set.
* `Gtz.exists_deflated_pair_of_uniform_dropSet` — **THE DROP SET AT THE DOUBLED
  DEFLATION**, where the product law is free and one budget is the whole
  hypothesis.
* `Gtz.atomPairCompletion`, `Gtz.sum_atomTripleDet_eq_pairCompletion` — **THE
  PAIR COMPLETION LAW.**  The four completions of a fixed pair add to an
  explicit polynomial in six readings.
* `Gtz.exists_tripleDet_pos_of_pairCompletion`,
  `Gtz.exists_sylvester_of_pairCompletion`,
  `Gtz.exists_deflated_pair_of_pairCompletion` — **THE PAIR COMPLETION CELL.**
* `Gtz.AtomLiftBlocked`, `Gtz.AtomCompletionBlocked`,
  `Gtz.AtomLiftResidueClosed` — the residue of the two cells together.
* `Gtz.atomPivotPairClosed_of_liftResidue`,
  `Gtz.atomTripleCeilingClosed_of_liftResidue`,
  `Gtz.gtzWeighted_six_three_of_liftResidue`,
  `Gtz.gtzWeightedAll_three_of_liftResidue`,
  `Gtz.isEmpty_sixThreeCrux_of_liftResidue` — the chain to the cell.
* `Gtz.atomLiftResidueClosed_of_atomPivotPair`,
  `Gtz.atomLiftResidueClosed_iff_atomPivotPair` — **THE CONVERSE.**  The residue
  is a face of the cell and not a narrowing of its content.
* `Gtz.atomBoundaryAtom_liftBlocked`,
  `Gtz.atomBoundaryAtom_completionBlocked`,
  `Gtz.atomBoundaryAtom_spares_liftResidue` — **THE CALIBRATION.**  The doubled
  tetrahedron of scale mass exactly one blocks both cells of this module, so
  the strict scale mass is load bearing and no cell here carries a margin that
  is uniform in the mass.

## Vacuity

Every law of layers zero thru four is an unconditional statement about a family
of vectors, a family of scales, one pivot and one inflation.  The residue of
layer five is vacuous under no hypothesis, and layer six proves that the two
blocks of that residue are satisfiable at the boundary.
-/

namespace Gtz

open scoped BigOperators Matrix

/-! ## Layer 0 — the frame laws that the pivot sees -/

section FrameLaws

variable {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}

/-- **THE CROSS ROW LAW.**  The row of one slot against the row of a second
slot totals the Gram entry of the two slots.  The diagonal case is the landed
row energy law. -/
theorem atomGram_row_cross
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot colSlot : Fin slotCount) :
    (∑ slot, atomGram atom rowSlot slot * atomGram atom colSlot slot)
      = atomGram atom rowSlot colSlot := by
  have hcell : ∀ slot : Fin slotCount,
      atomGram atom rowSlot slot * atomGram atom colSlot slot
        = (atom slot ⬝ᵥ atom rowSlot) * (atom slot ⬝ᵥ atom colSlot) := by
    intro slot
    simp only [atomGram]
    rw [dotProduct_comm (atom rowSlot) (atom slot),
      dotProduct_comm (atom colSlot) (atom slot)]
  simp only [hcell]
  rw [hframe (atom rowSlot) (atom colSlot)]
  rfl

/-- **THE FRAME RECONSTRUCTION.**  Every vector is the reading weighted sum of
the atoms of a tight frame. -/
theorem sum_read_smul_atom
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (vec : Fin rank → ℝ) :
    (∑ slot, (atom slot ⬝ᵥ vec) • atom slot) = vec := by
  funext index
  have hunit : ∀ slot : Fin slotCount,
      atom slot ⬝ᵥ (Pi.single index (1 : ℝ)) = atom slot index := by
    intro slot
    rw [dotProduct_single, mul_one]
  have hread : vec ⬝ᵥ (Pi.single index (1 : ℝ)) = vec index := by
    rw [dotProduct_single, mul_one]
  have hsum := hframe vec (Pi.single index (1 : ℝ))
  rw [hread] at hsum
  simp only [hunit] at hsum
  rw [Finset.sum_apply]
  simpa only [Pi.smul_apply, smul_eq_mul] using hsum

/-- **THE SHADOW FRAME LAW.**  The shadows of a tight frame at a pivot are a
tight frame of the plane of that pivot. -/
theorem shadow_frame_law
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (pivot : Fin slotCount) (probe direction : Fin rank → ℝ)
    (hprobe : probe ⬝ᵥ atom pivot = 0) (hdirection : direction ⬝ᵥ atom pivot = 0) :
    (∑ slot, (planeShadow (atom pivot) (atom slot) ⬝ᵥ probe)
        * (planeShadow (atom pivot) (atom slot) ⬝ᵥ direction)) = probe ⬝ᵥ direction := by
  rw [← hframe probe direction]
  exact Finset.sum_congr rfl fun slot _ => by
    rw [planeShadow_dot_plane (atom pivot) (atom slot) probe hprobe,
      planeShadow_dot_plane (atom pivot) (atom slot) direction hdirection]

/-- **THE SHADOW MASS LAW.**  The shadow masses of a tight frame at a pivot
total the rank minus one.  At rank three the total is two, which is the trace of
the identity of the plane. -/
theorem sum_shadow_energy
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {pivot : Fin slotCount} (haxis : atomGram atom pivot pivot ≠ 0) :
    (∑ slot, planeShadow (atom pivot) (atom slot)
        ⬝ᵥ planeShadow (atom pivot) (atom slot)) = (rank : ℝ) - 1 := by
  have haxisNe : atom pivot ⬝ᵥ atom pivot ≠ 0 := by
    simpa only [atomGram] using haxis
  have hcell : ∀ slot : Fin slotCount,
      planeShadow (atom pivot) (atom slot) ⬝ᵥ planeShadow (atom pivot) (atom slot)
        = atomGram atom slot slot
          - atomGram atom pivot slot ^ 2 / atomGram atom pivot pivot := by
    intro slot
    rw [planeShadow_dot_shadow (atom pivot) (atom slot) (atom slot) haxisNe]
    simp only [atomGram]
    rw [dotProduct_comm (atom pivot) (atom slot)]
    ring
  simp only [hcell]
  rw [Finset.sum_sub_distrib, atomGram_trace hframe]
  have hrow : (∑ slot, atomGram atom pivot slot ^ 2 / atomGram atom pivot pivot)
      = (∑ slot, atomGram atom pivot slot ^ 2) / atomGram atom pivot pivot := by
    rw [Finset.sum_div]
  rw [hrow, atomGram_row_energy hframe pivot, div_self haxis]

/-- **THE CHARGE LAW.**  The charge weighted shadows of a tight frame at a
pivot total zero.  The charge of a slot is its Gram reading against the
pivot. -/
theorem sum_charge_smul_shadow
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {pivot : Fin slotCount} (haxis : atomGram atom pivot pivot ≠ 0) :
    (∑ slot, atomGram atom pivot slot • planeShadow (atom pivot) (atom slot)) = 0 := by
  funext index
  have hcell : ∀ slot : Fin slotCount,
      (atomGram atom pivot slot • planeShadow (atom pivot) (atom slot)) index
        = atomGram atom pivot slot * atom slot index
          - atomGram atom pivot slot ^ 2 * atom pivot index
            / atomGram atom pivot pivot := by
    intro slot
    simp only [Pi.smul_apply, smul_eq_mul, planeShadow_apply]
    rw [show (atom slot ⬝ᵥ atom pivot) = atomGram atom pivot slot from
      dotProduct_comm (atom slot) (atom pivot)]
    rw [show (atom pivot ⬝ᵥ atom pivot) = atomGram atom pivot pivot from rfl]
    field_simp
  have hrecon : (∑ slot, atomGram atom pivot slot * atom slot index)
      = atom pivot index := by
    have hbase := congrFun (sum_read_smul_atom hframe (atom pivot)) index
    rw [Finset.sum_apply] at hbase
    simp only [Pi.smul_apply, smul_eq_mul] at hbase
    rw [← hbase]
    exact Finset.sum_congr rfl fun slot _ => by
      rw [show atomGram atom pivot slot = atom slot ⬝ᵥ atom pivot from
        dotProduct_comm (atom pivot) (atom slot)]
  have hrow : (∑ slot, atomGram atom pivot slot ^ 2) = atomGram atom pivot pivot :=
    atomGram_row_energy hframe pivot
  rw [Finset.sum_apply]
  simp only [hcell]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul, hrecon, hrow,
    Pi.zero_apply]
  field_simp
  ring

/-- **THE HEAVY PIVOT PIGEONHOLE.**  Some slot carries at least the rank share
of its own scale in leverage.  The reading is division free, and the choice is
an averaging step and not a named rule. -/
theorem exists_heavy_leverage_slot
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (hcount : 0 < slotCount) :
    ∃ pivot, (rank : ℝ) * scale pivot
      ≤ (∑ slot, scale slot) * atomGram atom pivot pivot := by
  by_contra hnone
  simp only [not_exists, not_le] at hnone
  have hne : (Finset.univ : Finset (Fin slotCount)).Nonempty := by
    have : Nonempty (Fin slotCount) := Fin.pos_iff_nonempty.mp hcount
    exact Finset.univ_nonempty
  have hlt : (∑ slot, (∑ other, scale other) * atomGram atom slot slot)
      < ∑ slot, (rank : ℝ) * scale slot :=
    Finset.sum_lt_sum_of_nonempty hne fun slot _ => hnone slot
  rw [← Finset.mul_sum, ← Finset.mul_sum, atomGram_trace hframe] at hlt
  linarith [hlt]

/-- **THE HEAVY PIVOT IS LIVE.**  Under a scale total of at most one and a rank
of at least two, the heavy slot of the pigeonhole has a positive shifted
diagonal.  A consumer of the lift always has a pivot. -/
theorem exists_live_heavy_pivot
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) ≤ 1) (hrank : 2 ≤ rank) (hcount : 0 < slotCount) :
    ∃ pivot, (rank : ℝ) * scale pivot ≤ atomGram atom pivot pivot
      ∧ 0 < atomShiftedDiag atom scale pivot := by
  obtain ⟨pivot, hheavy⟩ := exists_heavy_leverage_slot hframe scale hcount
  have hdiagNonneg : 0 ≤ atomGram atom pivot pivot := atomGram_diag_nonneg atom pivot
  have hfull : (rank : ℝ) * scale pivot ≤ atomGram atom pivot pivot := by
    have : (∑ slot, scale slot) * atomGram atom pivot pivot
        ≤ atomGram atom pivot pivot := by
      nlinarith [hsmall, hdiagNonneg]
    linarith [hheavy, this]
  refine ⟨pivot, hfull, ?_⟩
  have hrankReal : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  simp only [atomShiftedDiag]
  nlinarith [hfull, hpos pivot, hrankReal]

/-- **THE CHARGE ENERGY.**  The squared charges off the pivot total the
leverage minus its square. -/
theorem sum_charge_sq_off_pivot
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (pivot : Fin slotCount) :
    (∑ slot ∈ Finset.univ.erase pivot, atomGram atom pivot slot ^ 2)
      = atomGram atom pivot pivot - atomGram atom pivot pivot ^ 2 := by
  have hsplit := Finset.sum_erase_eq_sub
    (f := fun slot => atomGram atom pivot slot ^ 2) (Finset.mem_univ pivot)
  rw [hsplit, atomGram_row_energy hframe pivot]

end FrameLaws

/-! ## Layer 1 — the dictionary, in both directions -/

section Dictionary

variable {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
  {scale : Fin slotCount → ℝ}

/-- **THE PAIR MINOR IS THE SHADOW GAP.**  At a live pivot the pair minor is
positive exactly when the shadow gap of the slot at the deflated scale is
positive. -/
theorem atomPairMinor_pos_iff_shadow_gap {pivot : Fin slotCount} (slot : Fin slotCount)
    (hdiag : atomGram atom pivot pivot ≠ 0)
    (hpivot : 0 < atomShiftedDiag atom scale pivot) :
    0 < atomPairMinor atom scale pivot slot
      ↔ 0 < (planeShadow (atom pivot) (atom slot) ⬝ᵥ planeShadow (atom pivot) (atom slot))
          - scale slot
          - (scale pivot / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slot ^ 2 := by
  have hshift : atomGram atom pivot pivot - scale pivot ≠ 0 := by
    have hval := hpivot
    simp only [atomShiftedDiag] at hval
    exact ne_of_gt hval
  rw [atomPairMinor_eq_shadow slot hdiag hshift]
  constructor
  · intro hval
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [hval, hpivot, hneg]
  · intro hval
    exact mul_pos hpivot hval

/-- **THE DEFLATION IS AN EQUIVALENCE.**  At a live pivot the triple
determinant is positive exactly when the deflated pair test holds. -/
theorem atomTripleDet_pos_iff_deflated_pair {pivot slotOne slotTwo : Fin slotCount}
    (hpivot : 0 < atomShiftedDiag atom scale pivot) :
    0 < atomTripleDet atom scale pivot slotOne slotTwo
      ↔ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
          < atomPairMinor atom scale pivot slotOne
            * atomPairMinor atom scale pivot slotTwo := by
  constructor
  · intro hdet
    have hdeflate := atomTripleDet_deflate atom scale pivot slotOne slotTwo
    nlinarith [hdeflate, mul_pos hpivot hdet]
  · intro hpair
    exact atomTripleDet_pos_of_deflated_pair hpivot hpair

end Dictionary

/-! ## Layer 2 — the survivor inflation engine -/

/-- **THE SURVIVOR TEST.**  A slot survives an inflation at a pivot when its
pair minor stays above the inflation, measured against the shifted diagonal of
the pivot.  The reading is division free.

The landed live test asks only `0 < atomPairMinor`.  The survivor test is
strictly harder to pass at a positive inflation, so a hypothesis that quantifies
over survivors is strictly weaker than one that quantifies over live slots. -/
def AtomSlotSurvives {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale extra : Fin slotCount → ℝ) (pivot slot : Fin slotCount) : Prop :=
  atomShiftedDiag atom scale pivot * extra slot
    < atomPairMinor atom scale pivot slot

/-- A survivor is live. -/
theorem atomPairMinor_pos_of_survives {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale extra : Fin slotCount → ℝ}
    {pivot slot : Fin slotCount} (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hextra : 0 ≤ extra slot) (hsurvive : AtomSlotSurvives atom scale extra pivot slot) :
    0 < atomPairMinor atom scale pivot slot := by
  have hnonneg : 0 ≤ atomShiftedDiag atom scale pivot * extra slot :=
    mul_nonneg hpivot.le hextra
  exact lt_of_le_of_lt hnonneg hsurvive

/-- **THE SURVIVOR HYPOTHESIS IS WEAKER THAN THE LIVE HYPOTHESIS.**  A product
law that holds at every live pair holds at every surviving pair.  The engine of
this module asks strictly less than the landed live engine. -/
theorem survivorProduct_of_liveProduct {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale extra : Fin 6 → ℝ} {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hextraNonneg : ∀ slot, 0 ≤ extra slot)
    (hlive : ∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot →
      slotOne ≠ slotTwo →
      0 < atomPairMinor atom scale pivot slotOne →
      0 < atomPairMinor atom scale pivot slotTwo →
      (scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
        ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
          * (extra slotOne * extra slotTwo)) :
    ∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot → slotOne ≠ slotTwo →
      AtomSlotSurvives atom scale extra pivot slotOne →
      AtomSlotSurvives atom scale extra pivot slotTwo →
      (scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
        ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
          * (extra slotOne * extra slotTwo) :=
  fun slotOne slotTwo hOne hTwo hne hsurviveOne hsurviveTwo =>
    hlive slotOne slotTwo hOne hTwo hne
      (atomPairMinor_pos_of_survives hpivot (hextraNonneg slotOne) hsurviveOne)
      (atomPairMinor_pos_of_survives hpivot (hextraNonneg slotTwo) hsurviveTwo)

/-- **THE SURVIVOR INFLATION ENGINE.**  A pivot of positive shifted diagonal, an
extra inflation that vanishes at the pivot and stays nonnegative, the product
law at the SURVIVING pairs only, and one division-free budget: together they
supply a deflated pair at that pivot.

The rank-two plane closure returns a pair of positive shadow gaps, and a slot
whose plane scale reaches its shadow mass has no positive gap.  Such a slot
fails the survivor test, so the engine never reads the product law there.  A
consumer buys the death of one slot with one pair minor of the budget. -/
theorem exists_deflated_pair_of_survivor_inflation
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale extra : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hextraNonneg : ∀ slot, 0 ≤ extra slot)
    (hextraPivot : extra pivot = 0)
    (hproduct : ∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot →
      slotOne ≠ slotTwo →
      atomShiftedDiag atom scale pivot * extra slotOne
          < atomPairMinor atom scale pivot slotOne →
      atomShiftedDiag atom scale pivot * extra slotTwo
          < atomPairMinor atom scale pivot slotTwo →
      (scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
        ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
          * (extra slotOne * extra slotTwo))
    (hbudget : ((∑ slot, scale slot) - scale pivot + ∑ slot, extra slot)
          * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  classical
  have hdiagPos : 0 < atomGram atom pivot pivot := by
    have hp := hscale pivot
    have hR := hpivot
    simp only [atomShiftedDiag] at hR
    linarith
  have hdiagNe : atomGram atom pivot pivot ≠ 0 := ne_of_gt hdiagPos
  have hRne : atomShiftedDiag atom scale pivot ≠ 0 := ne_of_gt hpivot
  have hRne' : atomGram atom pivot pivot - scale pivot ≠ 0 := by
    have hval := hpivot
    simp only [atomShiftedDiag] at hval
    exact ne_of_gt hval
  have haxisNe : atom pivot ⬝ᵥ atom pivot ≠ 0 := by
    have := hdiagPos
    simp only [atomGram] at this
    exact ne_of_gt this
  have hshadowPivot : planeShadow (atom pivot) (atom pivot) = 0 :=
    planeShadow_self_eq_zero haxisNe
  have hperp : ∀ slot : Fin 6, planeShadow (atom pivot) (atom slot) ⬝ᵥ atom pivot = 0 :=
    fun slot => planeShadow_dot_axis (atom pivot) (atom slot) haxisNe
  have hdeflNonneg : 0 ≤ scale pivot
      / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) :=
    div_nonneg (hscale pivot) (mul_nonneg hdiagPos.le hpivot.le)
  have hinflNonneg : ∀ slot : Fin 6, 0 ≤ (if slot = pivot then (0:ℝ)
      else scale slot + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2
        + extra slot) := by
    intro slot
    by_cases hcase : slot = pivot
    · rw [if_pos hcase]
    · rw [if_neg hcase]
      have hterm := mul_nonneg hdeflNonneg (sq_nonneg (atomGram atom pivot slot))
      linarith [hscale slot, hextraNonneg slot]
  have hinflSum : (∑ slot, (if slot = pivot then (0:ℝ)
      else scale slot + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2
        + extra slot)) < 1 := by
    have hsplit : (∑ slot, (if slot = pivot then (0:ℝ)
        else scale slot + (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2
          + extra slot))
        = ∑ slot ∈ Finset.univ.erase pivot, (scale slot + (scale pivot
            / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slot ^ 2 + extra slot) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ pivot)]
      rw [if_pos rfl, add_zero]
      exact Finset.sum_congr rfl fun slot hslot =>
        if_neg (Finset.mem_erase.mp hslot).1
    have hfold : (∑ slot ∈ Finset.univ.erase pivot, (scale pivot
        / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
        * atomGram atom pivot slot ^ 2)
        = (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot))
          * (atomGram atom pivot pivot - atomGram atom pivot pivot ^ 2) := by
      rw [← sum_charge_sq_off_pivot hframe pivot, Finset.mul_sum]
    have hextraSum : (∑ slot ∈ Finset.univ.erase pivot, extra slot)
        = ∑ slot, extra slot := by
      rw [Finset.sum_erase_eq_sub (f := extra) (Finset.mem_univ pivot), hextraPivot]
      ring
    rw [hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_erase_eq_sub (f := scale) (Finset.mem_univ pivot), hfold, hextraSum]
    have hcancel : scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)
        * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)
        = scale pivot :=
      div_mul_cancel₀ _ (mul_ne_zero hdiagNe hRne)
    have hcancelSq : scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)
        * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)
        * atomGram atom pivot pivot
        = scale pivot * atomGram atom pivot pivot := by
      rw [hcancel]
    nlinarith [hbudget, hpivot, hcancel, hcancelSq]
  obtain ⟨slotOne, slotTwo, hneOneTwo, hgapRaw, hdetRaw⟩ :=
    atomPairGramClosed_holds (fun slot => planeShadow (atom pivot) (atom slot))
      (fun slot => if slot = pivot then (0:ℝ)
        else scale slot + (scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2
          + extra slot)
      (atom pivot)
      (by
        have := hdiagPos
        simp only [atomGram] at this
        exact this)
      hperp hinflNonneg hinflSum
      (fun probe direction hprobe hdirection =>
        shadow_frame_law hframe pivot probe direction hprobe hdirection)
  have hOneNe : slotOne ≠ pivot := by
    intro heq
    rw [heq, hshadowPivot, if_pos rfl] at hgapRaw
    simp at hgapRaw
  have hTwoNe : slotTwo ≠ pivot := by
    intro heq
    rw [heq, hshadowPivot, if_pos rfl] at hdetRaw
    simp at hdetRaw
  rw [if_neg hOneNe] at hgapRaw hdetRaw
  rw [if_neg hTwoNe] at hdetRaw
  have hgapTwo : 0 < planeShadow (atom pivot) (atom slotTwo)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo)
      - (scale slotTwo + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2
        + extra slotTwo) := by
    nlinarith [hdetRaw, hgapRaw,
      sq_nonneg (planeShadow (atom pivot) (atom slotOne)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))]
  have hminorOne : atomPairMinor atom scale pivot slotOne
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slotOne)
            ⬝ᵥ planeShadow (atom pivot) (atom slotOne))
          - scale slotOne
          - (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slotOne ^ 2) :=
    atomPairMinor_eq_shadow slotOne hdiagNe hRne'
  have hminorTwo : atomPairMinor atom scale pivot slotTwo
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slotTwo)
            ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))
          - scale slotTwo
          - (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slotTwo ^ 2) :=
    atomPairMinor_eq_shadow slotTwo hdiagNe hRne'
  have hliveOne : atomShiftedDiag atom scale pivot * extra slotOne
      < atomPairMinor atom scale pivot slotOne := by
    rw [hminorOne]
    nlinarith [hgapRaw, hpivot]
  have hliveTwo : atomShiftedDiag atom scale pivot * extra slotTwo
      < atomPairMinor atom scale pivot slotTwo := by
    rw [hminorTwo]
    nlinarith [hgapTwo, hpivot]
  have hdefectSq : ((scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot))
        * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
      ≤ extra slotOne * extra slotTwo := by
    have hraw := hproduct slotOne slotTwo hOneNe hTwoNe hneOneTwo hliveOne hliveTwo
    have hposSq : 0 < (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot) ^ 2 :=
      pow_pos (mul_pos hdiagPos hpivot) 2
    have hrewrite : ((scale pivot / (atomGram atom pivot pivot
          * atomShiftedDiag atom scale pivot))
          * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
        = (scale pivot * (atomGram atom pivot slotOne
              * atomGram atom pivot slotTwo)) ^ 2
          / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2 := by
      field_simp
    rw [hrewrite, div_le_iff₀ hposSq]
    linarith [hraw]
  have hcore := transfer_pair_of_product_inflation
    (gapOne := planeShadow (atom pivot) (atom slotOne)
        ⬝ᵥ planeShadow (atom pivot) (atom slotOne)
      - (scale slotOne + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2
        + extra slotOne))
    (gapTwo := planeShadow (atom pivot) (atom slotTwo)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo)
      - (scale slotTwo + (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2
        + extra slotTwo))
    (cross := planeShadow (atom pivot) (atom slotOne)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))
    (defect := (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot))
      * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo))
    (hextraNonneg slotOne) (hextraNonneg slotTwo) hdefectSq hgapRaw hgapTwo hdetRaw
  have hcrossEq : atomPivotCross atom scale pivot slotOne slotTwo
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slotOne)
              ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))
          - (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot))
            * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) :=
    atomPivotCross_eq_shadow slotOne slotTwo hdiagNe hRne'
  refine ⟨slotOne, slotTwo, fun heq => hOneNe heq.symm, fun heq => hTwoNe heq.symm,
    hneOneTwo, ?_, ?_, ?_⟩
  · rw [hminorOne]
    refine mul_pos hpivot ?_
    linarith [hgapRaw, hextraNonneg slotOne]
  · rw [hminorTwo]
    refine mul_pos hpivot ?_
    linarith [hgapTwo, hextraNonneg slotTwo]
  · rw [hcrossEq, hminorOne, hminorTwo]
    have hRsq : 0 < atomShiftedDiag atom scale pivot ^ 2 := by positivity
    nlinarith [hcore, hRsq]

/-- **THE ENGINE IN PIVOT PAIR SHAPE.** -/
theorem exists_pivotPair_of_survivor_inflation
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale extra : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hextraNonneg : ∀ slot, 0 ≤ extra slot)
    (hextraPivot : extra pivot = 0)
    (hproduct : ∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot →
      slotOne ≠ slotTwo →
      atomShiftedDiag atom scale pivot * extra slotOne
          < atomPairMinor atom scale pivot slotOne →
      atomShiftedDiag atom scale pivot * extra slotTwo
          < atomPairMinor atom scale pivot slotTwo →
      (scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
        ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
          * (extra slotOne * extra slotTwo))
    (hbudget : ((∑ slot, scale slot) - scale pivot + ∑ slot, extra slot)
          * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ centre slotOne slotTwo : Fin 6,
      centre ≠ slotOne ∧ centre ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale centre
        ∧ 0 < atomPairMinor atom scale centre slotOne
        ∧ atomPivotCross atom scale centre slotOne slotTwo ^ 2
            < atomPairMinor atom scale centre slotOne
              * atomPairMinor atom scale centre slotTwo := by
  obtain ⟨slotOne, slotTwo, hone, htwo, hne, hminor, _, hdeflate⟩ :=
    exists_deflated_pair_of_survivor_inflation hframe hscale hpivot hextraNonneg
      hextraPivot hproduct hbudget
  exact ⟨pivot, slotOne, slotTwo, hone, htwo, hne, hpivot, hminor, hdeflate⟩

/-- **THE ENGINE IN SYLVESTER SHAPE.** -/
theorem exists_sylvester_of_survivor_inflation
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale extra : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hextraNonneg : ∀ slot, 0 ≤ extra slot)
    (hextraPivot : extra pivot = 0)
    (hproduct : ∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot →
      slotOne ≠ slotTwo →
      atomShiftedDiag atom scale pivot * extra slotOne
          < atomPairMinor atom scale pivot slotOne →
      atomShiftedDiag atom scale pivot * extra slotTwo
          < atomPairMinor atom scale pivot slotTwo →
      (scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
        ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
          * (extra slotOne * extra slotTwo))
    (hbudget : ((∑ slot, scale slot) - scale pivot + ∑ slot, extra slot)
          * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ centre slotOne slotTwo : Fin 6,
      centre ≠ slotOne ∧ centre ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale centre
        ∧ 0 < atomPairMinor atom scale centre slotOne
        ∧ 0 < atomTripleDet atom scale centre slotOne slotTwo := by
  obtain ⟨centre, slotOne, slotTwo, hone, htwo, hne, hdiag, hminor, hdeflate⟩ :=
    exists_pivotPair_of_survivor_inflation hframe hscale hpivot hextraNonneg
      hextraPivot hproduct hbudget
  exact ⟨centre, slotOne, slotTwo, hone, htwo, hne, hdiag, hminor,
    atomTripleDet_pos_of_deflated_pair hdiag hdeflate⟩

/-! ## Layer 3 — the drop set consumer -/

/-- **THE DEAD SLOT INFLATION.**  The inflation that a consumer spends to
remove one slot from the rank-two selection.  It is the pair minor of that slot
against the pivot, clamped at zero. -/
noncomputable def deadSlotInflation {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot slot : Fin slotCount) : ℝ :=
  max 0 (atomPairMinor atom scale pivot slot / atomShiftedDiag atom scale pivot)

theorem deadSlotInflation_nonneg {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (pivot slot : Fin slotCount) : 0 ≤ deadSlotInflation atom scale pivot slot :=
  le_max_left _ _

/-- **THE DEAD SLOT IS DEAD.**  At a live pivot the dead slot inflation defeats
the liveness test of that slot. -/
theorem deadSlotInflation_kills {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {pivot : Fin slotCount} (slot : Fin slotCount)
    (hpivot : 0 < atomShiftedDiag atom scale pivot) :
    ¬ (atomShiftedDiag atom scale pivot * deadSlotInflation atom scale pivot slot
      < atomPairMinor atom scale pivot slot) := by
  rw [not_lt, deadSlotInflation]
  rcases le_or_gt (atomPairMinor atom scale pivot slot) 0 with hle | hlt
  · have : max 0 (atomPairMinor atom scale pivot slot
        / atomShiftedDiag atom scale pivot) = 0 :=
      max_eq_left (div_nonpos_of_nonpos_of_nonneg hle hpivot.le)
    rw [this, mul_zero]
    exact hle
  · have hdiv : 0 ≤ atomPairMinor atom scale pivot slot
        / atomShiftedDiag atom scale pivot := div_nonneg hlt.le hpivot.le
    rw [max_eq_right hdiv, mul_div_cancel₀ _ (ne_of_gt hpivot)]

/-- **THE DROP SET CONSUMER.**  A consumer names a kept set, spends the dead
slot inflation on every slot outside it, and supplies the product law only
inside the kept set.  The engine then gives the deflated pair.

The budget reads the dropped slots at their pair minors and the kept slots at
their own inflation, so a dropped slot costs one pair minor and nothing
else. -/
theorem exists_deflated_pair_of_dropSet
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ} (keep : Finset (Fin 6))
    (infl : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hpivotKeep : pivot ∉ keep)
    (hinflNonneg : ∀ slot, 0 ≤ infl slot)
    (hproduct : ∀ slotOne ∈ keep, ∀ slotTwo ∈ keep, slotOne ≠ slotTwo →
      (scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
        ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
          * (infl slotOne * infl slotTwo))
    (hbudget : ((∑ slot, scale slot) - scale pivot
          + ∑ slot, (if slot ∈ keep then infl slot
              else if slot = pivot then 0 else deadSlotInflation atom scale pivot slot))
          * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  classical
  refine exists_deflated_pair_of_survivor_inflation (extra := fun slot =>
      if slot ∈ keep then infl slot
      else if slot = pivot then 0 else deadSlotInflation atom scale pivot slot)
    hframe hscale hpivot ?_ ?_ ?_ hbudget
  · intro slot
    by_cases hmem : slot ∈ keep
    · rw [if_pos hmem]; exact hinflNonneg slot
    · rw [if_neg hmem]
      by_cases hpiv : slot = pivot
      · rw [if_pos hpiv]
      · rw [if_neg hpiv]; exact deadSlotInflation_nonneg atom scale pivot slot
  · rw [if_neg hpivotKeep, if_pos rfl]
  · intro slotOne slotTwo hOneNe hTwoNe hne hliveOne hliveTwo
    have hOneKeep : slotOne ∈ keep := by
      by_contra hmem
      rw [if_neg hmem, if_neg hOneNe] at hliveOne
      exact deadSlotInflation_kills slotOne hpivot hliveOne
    have hTwoKeep : slotTwo ∈ keep := by
      by_contra hmem
      rw [if_neg hmem, if_neg hTwoNe] at hliveTwo
      exact deadSlotInflation_kills slotTwo hpivot hliveTwo
    rw [if_pos hOneKeep, if_pos hTwoKeep]
    exact hproduct slotOne hOneKeep slotTwo hTwoKeep hne

/-- **THE UNIFORM DROP SET INSTANCE.**  The doubled deflation on the kept set
obeys the product law with room to spare, by a factor of four.  A consumer of
this instance supplies one budget and nothing else.

The budget reads each kept slot at its scale plus twice its deflation, and each
dropped slot at its own pair minor.  A dropped slot of nonpositive pair minor
costs nothing at all. -/
theorem exists_deflated_pair_of_uniform_dropSet
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ} (keep : Finset (Fin 6))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot) {pivot : Fin 6}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hpivotKeep : pivot ∉ keep)
    (hbudget : ((∑ slot, scale slot) - scale pivot
          + ∑ slot, (if slot ∈ keep
              then 2 * (scale pivot / (atomGram atom pivot pivot
                    * atomShiftedDiag atom scale pivot))
                  * atomGram atom pivot slot ^ 2
              else if slot = pivot then 0
              else deadSlotInflation atom scale pivot slot))
          * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)
      < atomShiftedDiag atom scale pivot) :
    ∃ slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ 0 < atomPairMinor atom scale pivot slotTwo
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  classical
  have hdiagPos : 0 < atomGram atom pivot pivot := by
    have hp := hscale pivot
    have hR := hpivot
    simp only [atomShiftedDiag] at hR
    linarith
  have hkeyNe : atomGram atom pivot pivot * atomShiftedDiag atom scale pivot ≠ 0 :=
    ne_of_gt (mul_pos hdiagPos hpivot)
  have hcancel : scale pivot
      / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)
      * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) = scale pivot :=
    div_mul_cancel₀ _ hkeyNe
  have hdeflNonneg : 0 ≤ scale pivot
      / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) :=
    div_nonneg (hscale pivot) (mul_nonneg hdiagPos.le hpivot.le)
  refine exists_deflated_pair_of_dropSet keep
    (fun slot => 2 * (scale pivot / (atomGram atom pivot pivot
        * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slot ^ 2)
    hframe hscale hpivot hpivotKeep ?_ ?_ hbudget
  · intro slot
    have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hdeflNonneg)
      (sq_nonneg (atomGram atom pivot slot))
    linarith
  · intro slotOne _ slotTwo _ _
    have hrw : (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
        * ((2 * (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotOne ^ 2)
          * (2 * (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot)) * atomGram atom pivot slotTwo ^ 2))
        = 4 * (scale pivot / (atomGram atom pivot pivot
              * atomShiftedDiag atom scale pivot)
            * (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot)) ^ 2
          * (atomGram atom pivot slotOne ^ 2 * atomGram atom pivot slotTwo ^ 2) := by
      ring
    rw [hrw, hcancel]
    have hX : 0 ≤ scale pivot ^ 2
        * (atomGram atom pivot slotOne ^ 2 * atomGram atom pivot slotTwo ^ 2) := by
      positivity
    nlinarith [hX]

/-! ## Layer 4 — the pair completion law -/

section Completion

variable {slotCount rank : ℕ}

/-- The sum of a function over the slots that avoid two named slots. -/
theorem sum_erase_pair (value : Fin slotCount → ℝ) {first second : Fin slotCount}
    (hne : first ≠ second) :
    (∑ slot ∈ (Finset.univ.erase first).erase second, value slot)
      = (∑ slot, value slot) - value first - value second := by
  rw [Finset.sum_erase_eq_sub (f := value)
      (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ second⟩),
    Finset.sum_erase_eq_sub (f := value) (Finset.mem_univ first)]

/-- **THE PAIR COMPLETION READING.**  The explicit polynomial that the four
completions of one pair add to.  The first product is the pair minor against
the free diagonal budget of the other slots.  The remaining terms are the cost
that the two rows of the pair charge to that budget. -/
def atomPairCompletion (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (first second : Fin slotCount) : ℝ :=
  atomPairMinor atom scale first second
      * (((rank : ℝ) - atomGram atom first first - atomGram atom second second)
        - ((∑ slot, scale slot) - scale first - scale second))
    + 2 * atomGram atom first second ^ 2
        * (1 - atomGram atom first first - atomGram atom second second)
    - atomShiftedDiag atom scale first
        * (atomGram atom second second - atomGram atom second second ^ 2
          - atomGram atom first second ^ 2)
    - atomShiftedDiag atom scale second
        * (atomGram atom first first - atomGram atom first first ^ 2
          - atomGram atom first second ^ 2)

/-- **THE PAIR COMPLETION LAW.**  The triple determinants of the completions of
one fixed pair total the pair completion reading of that pair.

The proof reads the summand as a linear form in the diagonal of the third slot,
the cross row of the pair, and the two squared rows.  The three row laws of the
frame then evaluate every sum in closed form. -/
theorem sum_atomTripleDet_eq_pairCompletion
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {first second : Fin slotCount} (hne : first ≠ second) :
    (∑ slot ∈ (Finset.univ.erase first).erase second,
        atomTripleDet atom scale first second slot)
      = atomPairCompletion atom scale first second := by
  classical
  have hterm : ∀ slot : Fin slotCount, atomTripleDet atom scale first second slot
      = atomPairMinor atom scale first second * atomShiftedDiag atom scale slot
        + (2 * atomGram atom first second)
            * (atomGram atom first slot * atomGram atom second slot)
        - atomShiftedDiag atom scale first * atomGram atom second slot ^ 2
        - atomShiftedDiag atom scale second * atomGram atom first slot ^ 2 := by
    intro slot
    simp only [atomTripleDet, atomPairMinor]
    ring
  have hdiagSum : (∑ slot, atomShiftedDiag atom scale slot)
      = (rank : ℝ) - ∑ slot, scale slot := by
    simp only [atomShiftedDiag]
    rw [Finset.sum_sub_distrib, atomGram_trace hframe]
  rw [Finset.sum_congr rfl fun slot _ => hterm slot]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_erase_pair (fun slot => atomShiftedDiag atom scale slot) hne,
    sum_erase_pair (fun slot => atomGram atom first slot * atomGram atom second slot) hne,
    sum_erase_pair (fun slot => atomGram atom second slot ^ 2) hne,
    sum_erase_pair (fun slot => atomGram atom first slot ^ 2) hne,
    hdiagSum, atomGram_row_cross hframe first second]
  have hrowFirst : (∑ slot, atomGram atom first slot ^ 2) = atomGram atom first first :=
    atomGram_row_energy hframe first
  have hrowSecond : (∑ slot, atomGram atom second slot ^ 2) = atomGram atom second second :=
    atomGram_row_energy hframe second
  rw [hrowFirst, hrowSecond]
  simp only [atomPairCompletion, atomShiftedDiag, atomPairMinor,
    atomGram_comm atom second first]
  ring

/-- **THE PAIR COMPLETION CELL.**  A pair of positive completion reading has a
third slot of positive triple determinant. -/
theorem exists_tripleDet_pos_of_pairCompletion
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {first second : Fin slotCount} (hne : first ≠ second)
    (hpos : 0 < atomPairCompletion atom scale first second) :
    ∃ third : Fin slotCount, third ≠ first ∧ third ≠ second
      ∧ 0 < atomTripleDet atom scale first second third := by
  classical
  by_contra hnone
  simp only [not_exists, not_and, not_lt] at hnone
  have hsum : (∑ slot ∈ (Finset.univ.erase first).erase second,
      atomTripleDet atom scale first second slot) ≤ 0 := by
    refine Finset.sum_nonpos fun slot hslot => ?_
    have hsecond : slot ≠ second := (Finset.mem_erase.mp hslot).1
    have hfirst : slot ≠ first := (Finset.mem_erase.mp (Finset.mem_erase.mp hslot).2).1
    exact hnone slot hfirst hsecond
  rw [sum_atomTripleDet_eq_pairCompletion hframe hne] at hsum
  linarith

end Completion

/-- **THE PAIR COMPLETION CELL IN SYLVESTER SHAPE.** -/
theorem exists_sylvester_of_pairCompletion
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {first second : Fin 6} (hne : first ≠ second)
    (hdiag : 0 < atomShiftedDiag atom scale first)
    (hminor : 0 < atomPairMinor atom scale first second)
    (hpos : 0 < atomPairCompletion atom scale first second) :
    ∃ centre slotOne slotTwo : Fin 6,
      centre ≠ slotOne ∧ centre ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale centre
        ∧ 0 < atomPairMinor atom scale centre slotOne
        ∧ 0 < atomTripleDet atom scale centre slotOne slotTwo := by
  obtain ⟨third, hthirdFirst, hthirdSecond, hdet⟩ :=
    exists_tripleDet_pos_of_pairCompletion hframe hne hpos
  exact ⟨first, second, third, hne, fun heq => hthirdFirst heq.symm,
    fun heq => hthirdSecond heq.symm, hdiag, hminor, hdet⟩

/-- **THE PAIR COMPLETION CELL IN PIVOT PAIR SHAPE.** -/
theorem exists_deflated_pair_of_pairCompletion
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {first second : Fin 6} (hne : first ≠ second)
    (hdiag : 0 < atomShiftedDiag atom scale first)
    (hminor : 0 < atomPairMinor atom scale first second)
    (hpos : 0 < atomPairCompletion atom scale first second) :
    ∃ centre slotOne slotTwo : Fin 6,
      centre ≠ slotOne ∧ centre ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale centre
        ∧ 0 < atomPairMinor atom scale centre slotOne
        ∧ atomPivotCross atom scale centre slotOne slotTwo ^ 2
            < atomPairMinor atom scale centre slotOne
              * atomPairMinor atom scale centre slotTwo := by
  obtain ⟨centre, slotOne, slotTwo, hone, htwo, hnepair, hcentre, hminorOne, hdet⟩ :=
    exists_sylvester_of_pairCompletion hframe hne hdiag hminor hpos
  exact ⟨centre, slotOne, slotTwo, hone, htwo, hnepair, hcentre, hminorOne,
    (atomTripleDet_pos_iff_deflated_pair hcentre).mp hdet⟩

/-! ## Layer 5 — the residue of the two cells, and the chain to the rung -/

/-- **THE LIVE INFLATION BLOCK.**  Every pivot of positive shifted diagonal
fails the budget of the live inflation engine, at every admissible extra
inflation. -/
def AtomLiftBlocked (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) : Prop :=
  ∀ (pivot : Fin 6) (extra : Fin 6 → ℝ),
    0 < atomShiftedDiag atom scale pivot →
    (∀ slot, 0 ≤ extra slot) →
    extra pivot = 0 →
    (∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot →
      slotOne ≠ slotTwo →
      atomShiftedDiag atom scale pivot * extra slotOne
          < atomPairMinor atom scale pivot slotOne →
      atomShiftedDiag atom scale pivot * extra slotTwo
          < atomPairMinor atom scale pivot slotTwo →
      (scale pivot * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) ^ 2
        ≤ (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot) ^ 2
          * (extra slotOne * extra slotTwo)) →
    atomShiftedDiag atom scale pivot
      ≤ ((∑ slot, scale slot) - scale pivot + ∑ slot, extra slot)
          * atomShiftedDiag atom scale pivot
        + scale pivot * (1 - atomGram atom pivot pivot)

/-- **THE COMPLETION BLOCK.**  Every live pair of positive minor has a
nonpositive completion reading. -/
def AtomCompletionBlocked (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) : Prop :=
  ∀ first second : Fin 6, first ≠ second →
    0 < atomShiftedDiag atom scale first →
    0 < atomPairMinor atom scale first second →
    atomPairCompletion atom scale first second ≤ 0

/-- **THE LIFT RESIDUE.**  The pivot pair conclusion on the data that block
both cells of this module.  The residue is strictly inside the landed blocked
residues, because a blocked datum of the landed engine still admits every live
inflation and every pair completion of this module. -/
def AtomLiftResidueClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    AtomLiftBlocked atom scale →
    AtomCompletionBlocked atom scale →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo

/-- **THE RESIDUE CLOSES THE PIVOT PAIR RESIDUE.**  At every datum either the
live inflation engine fires at some pivot, or the pair completion cell fires at
some pair, or both blocks hold and the residue fires. -/
theorem atomPivotPairClosed_of_liftResidue
    (hresidue : AtomLiftResidueClosed) : AtomPivotPairClosed := by
  classical
  intro atom scale hpos hsmall hframe
  by_cases hlift : AtomLiftBlocked atom scale
  · by_cases hcomp : AtomCompletionBlocked atom scale
    · exact hresidue atom scale hpos hsmall hframe hlift hcomp
    · simp only [AtomCompletionBlocked] at hcomp
      push Not at hcomp
      obtain ⟨first, second, hne, hdiag, hminor, hposComp⟩ := hcomp
      exact exists_deflated_pair_of_pairCompletion hframe hne hdiag hminor hposComp
  · simp only [AtomLiftBlocked] at hlift
    push Not at hlift
    obtain ⟨pivot, extra, hpivot, hnonneg, hzero, hproduct, hbudget⟩ := hlift
    exact exists_pivotPair_of_survivor_inflation hframe (fun slot => (hpos slot).le)
      hpivot hnonneg hzero hproduct hbudget

/-- **THE ATOM TRIPLE CEILING FROM THE LIFT RESIDUE.** -/
theorem atomTripleCeilingClosed_of_liftResidue
    (hresidue : AtomLiftResidueClosed) : AtomTripleCeilingClosed :=
  atomTripleCeilingClosed_of_pivotPair (atomPivotPairClosed_of_liftResidue hresidue)

/-- **THE `(6,3)` CELL FROM THE LIFT RESIDUE.** -/
theorem gtzWeighted_six_three_of_liftResidue
    (hresidue : AtomLiftResidueClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_liftResidue hresidue)

/-- **THE RANK-THREE PAYOFF FROM THE LIFT RESIDUE.** -/
theorem gtzWeightedAll_three_of_liftResidue
    (hresidue : AtomLiftResidueClosed) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_liftResidue hresidue)

/-- The crux type is empty under the lift residue. -/
theorem isEmpty_sixThreeCrux_of_liftResidue
    (hresidue : AtomLiftResidueClosed) : IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_liftResidue hresidue)

/-- **THE CONVERSE.**  The pivot pair residue closes the lift residue, so the
two are the same statement and the lift residue is a FACE of the cell.  The
gain of this module is the size of the data that the two cells remove from that
face, and it is not a change of the content. -/
theorem atomLiftResidueClosed_of_atomPivotPair
    (hpivotPair : AtomPivotPairClosed) : AtomLiftResidueClosed := by
  intro atom scale hpos hsmall hframe _ _
  exact hpivotPair atom scale hpos hsmall hframe

/-- The two residues are equivalent. -/
theorem atomLiftResidueClosed_iff_atomPivotPair :
    AtomLiftResidueClosed ↔ AtomPivotPairClosed :=
  ⟨atomPivotPairClosed_of_liftResidue, atomLiftResidueClosed_of_atomPivotPair⟩

/-! ## Layer 6 — the calibration at the boundary -/

/-- **THE LIVE INFLATION ENGINE CANNOT FIRE AT THE BOUNDARY WITNESS.**  The
doubled tetrahedron of scale mass exactly one blocks the engine at every pivot
and at every admissible extra inflation.  The proof needs no arithmetic of the
witness: the engine would supply a deflated pair, and the witness carries
none. -/
theorem atomBoundaryAtom_liftBlocked :
    AtomLiftBlocked atomBoundaryAtom atomBoundaryScale := by
  intro pivot extra hpivot hnonneg hzero hproduct
  by_contra hbudget
  rw [not_le] at hbudget
  obtain ⟨slotOne, slotTwo, hone, htwo, hne, hminor, _, hdeflate⟩ :=
    exists_deflated_pair_of_survivor_inflation atomBoundaryAtom_isTightFrame
      (fun slot => (atomBoundaryScale_pos slot).le) hpivot hnonneg hzero hproduct hbudget
  exact atomBoundaryAtom_no_deflated_pair pivot slotOne slotTwo hone htwo hne
    ⟨hpivot, hminor, hdeflate⟩

/-- **THE PAIR COMPLETION CELL CANNOT FIRE AT THE BOUNDARY WITNESS.**  Every
completion reading of the doubled tetrahedron is nonpositive, because every
triple determinant of that witness is nonpositive. -/
theorem atomBoundaryAtom_completionBlocked :
    AtomCompletionBlocked atomBoundaryAtom atomBoundaryScale := by
  intro first second hne _ _
  by_contra hpos
  rw [not_le] at hpos
  obtain ⟨third, hthirdFirst, hthirdSecond, hdet⟩ :=
    exists_tripleDet_pos_of_pairCompletion atomBoundaryAtom_isTightFrame hne hpos
  exact absurd hdet (not_lt.mpr (atomBoundaryAtom_tripleDet_nonpos hne
    (Ne.symm hthirdFirst) (Ne.symm hthirdSecond)))

/-- **THE STRICT SCALE MASS IS LOAD BEARING FOR BOTH CELLS.**  The boundary
witness has positive scales, a scale mass of exactly one, the tight frame law,
and it blocks the two cells of this module at once.  It also carries no
deflated pair at any ordered triple.  No proof of the residue of this module
can relax the strict scale mass.  No cell of this module can carry a margin
that is uniform in the mass. -/
theorem atomBoundaryAtom_spares_liftResidue :
    (∀ slot : Fin 6, 0 < atomBoundaryScale slot)
      ∧ (∑ slot, atomBoundaryScale slot) = 1
      ∧ (∀ probe direction : Fin 3 → ℝ,
          (∑ slot, (atomBoundaryAtom slot ⬝ᵥ probe)
            * (atomBoundaryAtom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
      ∧ AtomLiftBlocked atomBoundaryAtom atomBoundaryScale
      ∧ AtomCompletionBlocked atomBoundaryAtom atomBoundaryScale
      ∧ ∀ pivot slotOne slotTwo : Fin 6, pivot ≠ slotOne → pivot ≠ slotTwo →
          slotOne ≠ slotTwo →
          ¬ AtomTripleDeflates atomBoundaryAtom atomBoundaryScale pivot slotOne slotTwo :=
  ⟨atomBoundaryScale_pos, atomBoundaryScale_sum, atomBoundaryAtom_isTightFrame,
    atomBoundaryAtom_liftBlocked, atomBoundaryAtom_completionBlocked,
    atomBoundaryAtom_no_deflated_pair⟩

end Gtz
