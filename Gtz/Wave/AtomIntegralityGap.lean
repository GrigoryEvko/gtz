import Gtz.Wave.AtomMarginalFoil

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The integrality gap: the residue is a landed theorem with the cover made integral

`Gtz.atomFractionalCoverClosed_holds` is unconditional: every datum of the
lane carries a family of six weights in the unit interval, of total three,
whose scaled atom operator dominates the identity.  This module proves
that the residue of the lane is EXACTLY that statement with the weights
restricted to zero and one, and it measures how much room the fractional
statement has that the integral one does not.

## The two explicit covers

* THE MARGINAL COVER, `cover slot = atomGram atom slot slot`.  It sits in
  the unit interval at every datum, and it dominates the identity by one
  Cauchy-Schwarz.
* THE SCALE COVER, `cover slot = 3 * scale slot`.  It dominates THREE
  TIMES the identity, by the frame law alone and with no inequality at
  all, and it sits in the unit interval whenever no scale exceeds one
  third.

The scale cover measures the room: the fractional problem is solved with a
factor of three to spare, while the integral problem is exactly tight at
the doubled tetrahedron.  All the content of the cell is the passage from
a cover to a triple.

## The monotone law

A cover that is pointwise above a cover is a cover.  Two consequences: a
dominating set of three slots or fewer extends to exactly three, and the
residue may always be read on a triple rather than on a smaller set.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.sum_over_triple_finset` — the three-slot sum of a Finset triple.
* `Gtz.atomCover_mono`, `Gtz.atomCover_mono_subset` — **THE MONOTONE
  LAW**, in the weight form and in the support form.
* `Gtz.atomScaleCover_energy`, `Gtz.atomScaleCover_sum`,
  `Gtz.exists_atomFractionalCover_slack` — **THE SCALE COVER**, and the
  factor-three room of the fractional statement.
* `Gtz.AtomVertexCoverClosed`,
  `Gtz.atomVertexCoverClosed_of_atomTripleOperator`,
  `Gtz.atomTripleOperatorClosed_of_atomVertexCover`,
  `Gtz.atomVertexCoverClosed_iff_atomTripleOperator`,
  `Gtz.atomVertexCoverClosed_iff_atomTripleBoundary` — **THE RESIDUE IS
  THE INTEGRAL COVER**.
* `Gtz.gtzWeighted_six_three_of_atomVertexCover` — the cell from the
  integral cover.

## Vacuity

The monotone law and the scale cover are unconditional theorems.  The
equivalences consume the landed residue on both sides, thus none of them
is vacuous.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the triple sum -/

/-- The sum over a Finset triple of distinct slots is the three-term
sum. -/
theorem sum_over_triple_finset {slotCount : ℕ} {slotOne slotTwo slotThree : Fin slotCount}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) (value : Fin slotCount → ℝ) :
    (∑ slot ∈ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)), value slot)
      = value slotOne + value slotTwo + value slotThree := by
  classical
  rw [Finset.sum_insert (by simp [honeTwo, honeThree]),
    Finset.sum_insert (by simp [htwoThree]), Finset.sum_singleton]
  ring

/-! ## Layer 1 — the monotone law of covers -/

/-- **A COVER THAT IS POINTWISE ABOVE A COVER IS A COVER.** -/
theorem atomCover_mono {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (hpos : ∀ slot, 0 < scale slot)
    {coverLow coverHigh : Fin slotCount → ℝ}
    (hle : ∀ slot, coverLow slot ≤ coverHigh slot) (direction : Fin rank → ℝ)
    (hdom : direction ⬝ᵥ direction
      ≤ ∑ slot, (coverLow slot / scale slot) * (atom slot ⬝ᵥ direction) ^ 2) :
    direction ⬝ᵥ direction
      ≤ ∑ slot, (coverHigh slot / scale slot) * (atom slot ⬝ᵥ direction) ^ 2 := by
  refine hdom.trans (Finset.sum_le_sum fun slot _ => ?_)
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact div_le_div_of_nonneg_right (hle slot) (hpos slot).le

/-- **A COVER ON A SUBSET IS A COVER ON THE SET.**  A dominating set of
slots stays dominating when it grows. -/
theorem atomCover_mono_subset {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (hpos : ∀ slot, 0 < scale slot)
    {carSmall carLarge : Finset (Fin slotCount)} (hsub : carSmall ⊆ carLarge)
    (direction : Fin rank → ℝ)
    (hdom : direction ⬝ᵥ direction
      ≤ ∑ slot ∈ carSmall, (atom slot ⬝ᵥ direction) ^ 2 / scale slot) :
    direction ⬝ᵥ direction
      ≤ ∑ slot ∈ carLarge, (atom slot ⬝ᵥ direction) ^ 2 / scale slot := by
  refine hdom.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun slot _ _ => ?_)
  exact div_nonneg (sq_nonneg _) (hpos slot).le

/-! ## Layer 2 — the scale cover and the room of the fractional statement -/

/-- **THE SCALE COVER DOMINATES THREE TIMES THE IDENTITY.**  The weights
`3 * scale` cancel the scales exactly, and the frame law does the rest.
No inequality enters. -/
theorem atomScaleCover_energy {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (hpos : ∀ slot, 0 < scale slot)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (direction : Fin rank → ℝ) :
    (∑ slot, (3 * scale slot / scale slot) * (atom slot ⬝ᵥ direction) ^ 2)
      = 3 * (direction ⬝ᵥ direction) := by
  have hcell : ∀ slot : Fin slotCount,
      (3 * scale slot / scale slot) * (atom slot ⬝ᵥ direction) ^ 2
        = 3 * (atom slot ⬝ᵥ direction) ^ 2 := by
    intro slot
    rw [mul_div_assoc, div_self (ne_of_gt (hpos slot)), mul_one]
  rw [Finset.sum_congr rfl fun slot _ => hcell slot, ← Finset.mul_sum,
    atomReading_sum atom hframe direction]

/-- The scale cover has total three at mass one. -/
theorem atomScaleCover_sum {slotCount : ℕ} (scale : Fin slotCount → ℝ)
    (hmass : (∑ slot, scale slot) = 1) : (∑ slot, 3 * scale slot) = 3 := by
  rw [← Finset.mul_sum, hmass, mul_one]

/-- **THE FRACTIONAL STATEMENT HAS A FACTOR-THREE ROOM.**  When no scale
exceeds one third, the scale cover lies in the unit interval, has total
three, and dominates THREE times the identity.  The integral statement is
exactly tight at the doubled tetrahedron, so the whole difficulty of the
cell is the passage to a triple. -/
theorem exists_atomFractionalCover_slack (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hthird : ∀ slot, scale slot ≤ 1 / 3)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ cover : Fin 6 → ℝ,
      (∀ slot, 0 ≤ cover slot) ∧ (∀ slot, cover slot ≤ 1)
        ∧ (∑ slot, cover slot) = 3
        ∧ ∀ direction : Fin 3 → ℝ,
            3 * (direction ⬝ᵥ direction)
              ≤ ∑ slot, (cover slot / scale slot) * (atom slot ⬝ᵥ direction) ^ 2 := by
  refine ⟨fun slot => 3 * scale slot, fun slot => by linarith [hpos slot],
    fun slot => by linarith [hthird slot], atomScaleCover_sum scale hmass,
    fun direction => ?_⟩
  rw [atomScaleCover_energy atom scale hpos hframe direction]

/-! ## Layer 3 — the residue is the integral cover -/

/-- **THE INTEGRAL COVER.**  The fractional cover of the lane with the six
weights restricted to zero and one: a set of exactly three slots whose
scaled atom operator dominates the identity. -/
def AtomVertexCoverClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ direction : Fin 3 → ℝ,
          direction ⬝ᵥ direction
            ≤ ∑ slot ∈ car, (atom slot ⬝ᵥ direction) ^ 2 / scale slot

/-- The operator face gives the integral cover. -/
theorem atomVertexCoverClosed_of_atomTripleOperator
    (hoperator : AtomTripleOperatorClosed) : AtomVertexCoverClosed := by
  classical
  intro atom scale hpos hmass hframe
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hdual⟩ :=
    hoperator atom scale hpos hmass hframe
  refine ⟨{slotOne, slotTwo, slotThree},
    Finset.card_eq_three.mpr ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, rfl⟩,
    fun direction => ?_⟩
  rw [sum_over_triple_finset honeTwo honeThree htwoThree
    (fun slot => (atom slot ⬝ᵥ direction) ^ 2 / scale slot)]
  exact hdual direction

/-- The integral cover gives the operator face. -/
theorem atomTripleOperatorClosed_of_atomVertexCover
    (hvertex : AtomVertexCoverClosed) : AtomTripleOperatorClosed := by
  classical
  intro atom scale hpos hmass hframe
  obtain ⟨car, hcard, hdom⟩ := hvertex atom scale hpos hmass hframe
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hcarEq⟩ :=
    Finset.card_eq_three.mp hcard
  subst hcarEq
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, fun direction => ?_⟩
  have hstep := hdom direction
  rwa [sum_over_triple_finset honeTwo honeThree htwoThree
    (fun slot => (atom slot ⬝ᵥ direction) ^ 2 / scale slot)] at hstep

/-- **THE INTEGRAL COVER IS THE OPERATOR FACE.** -/
theorem atomVertexCoverClosed_iff_atomTripleOperator :
    AtomVertexCoverClosed ↔ AtomTripleOperatorClosed :=
  ⟨atomTripleOperatorClosed_of_atomVertexCover, atomVertexCoverClosed_of_atomTripleOperator⟩

/-- **THE INTEGRALITY GAP, AS ONE STATEMENT.**  The residue of the lane is
the landed fractional cover theorem with the six weights restricted to
zero and one. -/
theorem atomVertexCoverClosed_iff_atomTripleBoundary :
    AtomVertexCoverClosed ↔ AtomTripleBoundaryClosed :=
  atomVertexCoverClosed_iff_atomTripleOperator.trans
    atomTripleOperatorClosed_iff_atomTripleBoundary

/-- **THE CELL FROM THE INTEGRAL COVER.** -/
theorem gtzWeighted_six_three_of_atomVertexCover (hvertex : AtomVertexCoverClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomTripleOperator
    (atomTripleOperatorClosed_of_atomVertexCover hvertex)

end Gtz
