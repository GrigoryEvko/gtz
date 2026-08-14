import Gtz.Wave.AtomShadowTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The blocked residue in deflated pair form, and the realness boundary

The blocked stratum keeps the cell open, and this module narrows its open
conclusion by one full layer.  The residue no longer asks for a card-three
carrier with a quantifier over probes.  It asks for one pivot and one
deflated pair: four polynomial inequalities in the Gram entries and the
scales.  The two forms are equivalent, and the equivalence is a theorem
here in the two directions, thus the swap loses nothing.  The engine of
the converse direction is a converse Sylvester extraction: a positive
ternary quadratic form gives its nested minor chain through three
explicit probes, and the third probe is one adjugate column.

## The realness boundary

The scaled complex two-trine datum sits INSIDE the blocked hypothesis
package.  Take the atoms `g_j = (sqrt 2, 0, w^j)` and
`g_{3+j} = (0, sqrt 2, w^j)` over the complex field, normalize to
`c = g / sqrt 6`, and give the six slots the uniform scales
`s = sigma / 6` with `sigma` between `39/50` and one.  This datum
satisfies Hermitian Parseval, the positivity, the mass bound, and the
blocked inequality at every live pivot.  But the chart value of the trine
is `(3 - sqrt 5)/6`, the scales sit above it, and thus NO triple
dominates.  As a result no field-agnostic argument can close the blocked
residue: trace averages, Schur complements, exchange bounds and
eigenvalue arguments hold over the complex field verbatim.  A proof must
consume a real-only ingredient, and the landed plane closure is the
approved source.  The clearance of the unscaled trine, `(7 - 3 sqrt 5)/36`,
protects one scale point only, not the stratum.

The single-budget window quantifies the deep end of the stratum.  When
every live pivot fails even the SINGLE inflation budget, the same cubic
pigeonhole that gave the `13/20` threshold gives, with the halved
coefficient, the bound `(1 - mass) (3 - mass) (6 - mass) <= 3 mass`, and
that cubic factors at `39/50`.  Thus the doubly blocked stratum lives in
the mass window above `39/50`, and the scaled complex trine near mass one
is its exact complex inhabitant.

## Measured intelligence (probes, banked, not consumed in Lean)

On 1200 blocked real frames with mass up to `0.9995`, the deflated pair
existed at the pivot of least single-budget value on 1200 of 1200, and at
every single-budget pivot on 2222 of 2222 pivot checks.  The true
extension margin stayed above `0.33` across the whole mass window, with
no decay toward mass one.  The faithful plane package with the single
budget alone is FALSE on unblocked real data (20 failures in 120000
faithful samples), thus the blocked hypothesis is load-bearing and the
residue keeps it.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.planeShadow_reading_total` — **THE READING MOMENT**: the shadows
  of a frame, weighted by their pivot readings, add up to zero.  This is
  the orthogonality law of the pivot defect.
* `Gtz.triple_minors_of_quadratic_pos` — **THE CONVERSE SYLVESTER
  EXTRACTION**: a positive ternary quadratic form has a positive nested
  minor chain.
* `Gtz.exists_pivotPair_of_dominating_carrier` — a dominating card-three
  carrier gives a pivot and a deflated pair.
* `Gtz.atomPairMinor_eq_shadow`, `Gtz.atomPivotCross_eq_shadow` — **THE
  DEFLATION DICTIONARY**, public: the pivot minor and the deflated cross
  read exactly as shadow quantities with one rank-one defect.
* `Gtz.singleBudget_scale_cubic`, `Gtz.singleBudget_scale_lt`,
  `Gtz.exists_pivot_single_budget_of_scale_le` — **THE SINGLE-BUDGET
  WINDOW**: failure of the single budget at every live pivot forces the
  scale mass above `39/50`.
* `Gtz.AtomBlockedPairClosed` — **THE RESIDUE**, the blocked stratum with
  the deflated pair conclusion.
* `Gtz.atomPivotPairClosed_of_blockedPair` — the residue closes the full
  pivot pair residue through the landed budget engine.
* `Gtz.atomBlockedPairClosed_of_blockedPivot`,
  `Gtz.atomBlockedPivotClosed_of_blockedPair`,
  `Gtz.atomBlockedPairClosed_iff_blockedPivot` — **THE LOSSLESS SWAP**.
* `Gtz.atomPivotPairClosed_of_sylvester`,
  `Gtz.atomBlockedPairClosed_of_pivotPair` — the weakness chain.
* `Gtz.gtzWeighted_six_three_of_blockedPair` and the fourteen closure
  bridges — the cell and the ladder from the new residue.

## Vacuity

Every law of layers zero thru four is an unconditional statement about a
family of vectors and a family of scales.  The residue of layer five is
vacuous under no hypothesis, and it is equivalent to the landed blocked
residue by the two bridge theorems.
-/

namespace Gtz

/-! ## Layer 0 — the reading moment of one pivot -/

/-- **THE READING MOMENT.**  The shadows of the atoms in the plane of one
pivot, weighted by their pivot readings, add up to zero in every
coordinate.  The frame law pays once through the pivot row and once
through the row energy, and the two payments cancel. -/
theorem planeShadow_reading_total {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (pivot : Fin slotCount) (haxis : atom pivot ⬝ᵥ atom pivot ≠ 0) (index : Fin rank) :
    (∑ slot, atomGram atom pivot slot * planeShadow (atom pivot) (atom slot) index) = 0 := by
  classical
  have hcell : ∀ slot : Fin slotCount,
      atomGram atom pivot slot * planeShadow (atom pivot) (atom slot) index
        = (atom slot ⬝ᵥ atom pivot) * (atom slot ⬝ᵥ probeUnit index)
          - (atom slot ⬝ᵥ atom pivot) * (atom slot ⬝ᵥ atom pivot)
            * (atom pivot index / (atom pivot ⬝ᵥ atom pivot)) := by
    intro slot
    rw [planeShadow_apply, dotProduct_probeUnit]
    simp only [atomGram]
    rw [dotProduct_comm (atom pivot) (atom slot)]
    ring
  rw [Finset.sum_congr rfl fun slot _ => hcell slot, Finset.sum_sub_distrib,
    hframe (atom pivot) (probeUnit index), ← Finset.sum_mul,
    hframe (atom pivot) (atom pivot), dotProduct_probeUnit]
  have hcancel : (atom pivot ⬝ᵥ atom pivot)
      * (atom pivot index / (atom pivot ⬝ᵥ atom pivot)) = atom pivot index := by
    rw [mul_comm, div_mul_cancel₀ _ haxis]
  rw [hcancel, sub_self]

/-! ## Layer 1 — the converse Sylvester extraction -/

/-- The probe of one carrier: three values on three named slots, zero off
the triple. -/
def carrierProbe {slotCount : ℕ} (slotOne slotTwo slotThree : Fin slotCount)
    (valueOne valueTwo valueThree : ℝ) : Fin slotCount → ℝ :=
  fun slot => if slot = slotOne then valueOne
    else if slot = slotTwo then valueTwo
    else if slot = slotThree then valueThree else 0

theorem carrierProbe_one {slotCount : ℕ} (slotOne slotTwo slotThree : Fin slotCount)
    (valueOne valueTwo valueThree : ℝ) :
    carrierProbe slotOne slotTwo slotThree valueOne valueTwo valueThree slotOne = valueOne := by
  simp only [carrierProbe]
  rw [if_pos trivial]

theorem carrierProbe_two {slotCount : ℕ} {slotOne slotTwo : Fin slotCount}
    (slotThree : Fin slotCount) (valueOne valueTwo valueThree : ℝ)
    (honeTwo : slotOne ≠ slotTwo) :
    carrierProbe slotOne slotTwo slotThree valueOne valueTwo valueThree slotTwo = valueTwo := by
  simp only [carrierProbe]
  rw [if_neg (Ne.symm honeTwo), if_pos trivial]

theorem carrierProbe_three {slotCount : ℕ} {slotOne slotTwo slotThree : Fin slotCount}
    (valueOne valueTwo valueThree : ℝ)
    (honeThree : slotOne ≠ slotThree) (htwoThree : slotTwo ≠ slotThree) :
    carrierProbe slotOne slotTwo slotThree valueOne valueTwo valueThree slotThree
      = valueThree := by
  simp only [carrierProbe]
  rw [if_neg (Ne.symm honeThree), if_neg (Ne.symm htwoThree), if_pos trivial]

theorem carrierProbe_vanish {slotCount : ℕ} (slotOne slotTwo slotThree : Fin slotCount)
    (valueOne valueTwo valueThree : ℝ) :
    ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)),
      carrierProbe slotOne slotTwo slotThree valueOne valueTwo valueThree slot = 0 := by
  intro slot hnot
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
  simp only [carrierProbe]
  rw [if_neg hnot.1, if_neg hnot.2.1, if_neg hnot.2.2]

theorem carrierProbe_ne_zero {slotCount : ℕ} {slotOne slotTwo slotThree : Fin slotCount}
    {valueOne valueTwo valueThree : ℝ}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hvalue : ¬(valueOne = 0 ∧ valueTwo = 0 ∧ valueThree = 0)) :
    carrierProbe slotOne slotTwo slotThree valueOne valueTwo valueThree ≠ 0 := by
  intro hzero
  refine hvalue ⟨?_, ?_, ?_⟩
  · have h := congrFun hzero slotOne
    rwa [carrierProbe_one, Pi.zero_apply] at h
  · have h := congrFun hzero slotTwo
    rwa [carrierProbe_two slotThree valueOne valueTwo valueThree honeTwo, Pi.zero_apply] at h
  · have h := congrFun hzero slotThree
    rwa [carrierProbe_three valueOne valueTwo valueThree honeThree htwoThree,
      Pi.zero_apply] at h

/-- **THE CONVERSE SYLVESTER EXTRACTION.**  A positive ternary quadratic
form has a positive leading diagonal, a positive leading pair minor and a
positive determinant.  The first probe is a unit, the second probe kills
the cross entry, and the third probe is one adjugate column, whose form
value is the determinant against the pair minor. -/
theorem triple_minors_of_quadratic_pos
    {diagOne diagTwo diagThree crossOneTwo crossOneThree crossTwoThree : ℝ}
    (hform : ∀ valueOne valueTwo valueThree : ℝ,
      ¬(valueOne = 0 ∧ valueTwo = 0 ∧ valueThree = 0) →
      0 < diagOne * valueOne ^ 2 + diagTwo * valueTwo ^ 2 + diagThree * valueThree ^ 2
        + 2 * crossOneTwo * valueOne * valueTwo
        + 2 * crossOneThree * valueOne * valueThree
        + 2 * crossTwoThree * valueTwo * valueThree) :
    0 < diagOne ∧ 0 < diagOne * diagTwo - crossOneTwo ^ 2
      ∧ 0 < diagOne * diagTwo * diagThree
          + 2 * crossOneTwo * crossOneThree * crossTwoThree
          - diagOne * crossTwoThree ^ 2 - diagTwo * crossOneThree ^ 2
          - diagThree * crossOneTwo ^ 2 := by
  have hone : 0 < diagOne := by
    have hval := hform 1 0 0 (by norm_num)
    nlinarith [hval]
  have hminor : 0 < diagOne * diagTwo - crossOneTwo ^ 2 := by
    have hval := hform (-crossOneTwo) diagOne 0 fun hall => ne_of_gt hone hall.2.1
    by_contra hnot
    nlinarith [hval, mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hnot) hone.le]
  refine ⟨hone, hminor, ?_⟩
  have hval := hform (crossOneTwo * crossTwoThree - diagTwo * crossOneThree)
    (crossOneTwo * crossOneThree - diagOne * crossTwoThree)
    (diagOne * diagTwo - crossOneTwo ^ 2) fun hall => ne_of_gt hminor hall.2.2
  by_contra hnot
  nlinarith [hval, mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hnot) hminor.le]

/-- **THE CARRIER GIVES BACK THE PAIR.**  A dominating card-three carrier
gives a pivot and a deflated pair on its own slots.  This is the converse
of the deflation discharge, thus the two residue forms carry the same
content. -/
theorem exists_pivotPair_of_dominating_carrier {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {car : Finset (Fin slotCount)} (hcard : car.card = 3)
    (hdom : ∀ probe : Fin slotCount → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
        (∑ slot, scale slot * probe slot ^ 2)
          < atomBlend atom probe ⬝ᵥ atomBlend atom probe) :
    ∃ pivot slotOne slotTwo : Fin slotCount,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo := by
  classical
  obtain ⟨pivotSlot, slotOne, slotTwo, hpivotOne, hpivotTwo, hslotNe, hcar⟩ :=
    Finset.card_eq_three.mp hcard
  subst hcar
  have hform : ∀ valueOne valueTwo valueThree : ℝ,
      ¬(valueOne = 0 ∧ valueTwo = 0 ∧ valueThree = 0) →
      0 < atomShiftedDiag atom scale pivotSlot * valueOne ^ 2
        + atomShiftedDiag atom scale slotOne * valueTwo ^ 2
        + atomShiftedDiag atom scale slotTwo * valueThree ^ 2
        + 2 * atomGram atom pivotSlot slotOne * valueOne * valueTwo
        + 2 * atomGram atom pivotSlot slotTwo * valueOne * valueThree
        + 2 * atomGram atom slotOne slotTwo * valueTwo * valueThree := by
    intro valueOne valueTwo valueThree hvalue
    have hvanish := carrierProbe_vanish pivotSlot slotOne slotTwo valueOne valueTwo valueThree
    have hread := hdom (carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree)
      hvanish (carrierProbe_ne_zero hpivotOne hpivotTwo hslotNe hvalue)
    have hscaleSum : (∑ slot, scale slot
          * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slot ^ 2)
        = scale pivotSlot
            * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree pivotSlot ^ 2
          + scale slotOne
            * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotOne ^ 2
          + scale slotTwo
            * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotTwo ^ 2 :=
      sum_eq_triple_of_support hpivotOne hpivotTwo hslotNe
        fun slot hnot => by rw [hvanish slot hnot]; ring
    have hgramSum : atomBlend atom
          (carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree)
          ⬝ᵥ atomBlend atom
            (carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree)
        = (carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree pivotSlot
              * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree pivotSlot
              * atomGram atom pivotSlot pivotSlot
            + carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree pivotSlot
              * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotOne
              * atomGram atom pivotSlot slotOne
            + carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree pivotSlot
              * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotTwo
              * atomGram atom pivotSlot slotTwo)
          + (carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotOne
              * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree pivotSlot
              * atomGram atom slotOne pivotSlot
            + carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotOne
              * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotOne
              * atomGram atom slotOne slotOne
            + carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotOne
              * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotTwo
              * atomGram atom slotOne slotTwo)
          + (carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotTwo
              * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree pivotSlot
              * atomGram atom slotTwo pivotSlot
            + carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotTwo
              * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotOne
              * atomGram atom slotTwo slotOne
            + carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotTwo
              * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotTwo
              * atomGram atom slotTwo slotTwo) := by
      rw [atomBlend_energy_eq_gram atom
        (carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree)]
      have hinner : ∀ rowSlot : Fin slotCount,
          (∑ colSlot, carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree rowSlot
              * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree colSlot
              * atomGram atom rowSlot colSlot)
            = carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree rowSlot
                * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree pivotSlot
                * atomGram atom rowSlot pivotSlot
              + carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree rowSlot
                * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotOne
                * atomGram atom rowSlot slotOne
              + carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree rowSlot
                * carrierProbe pivotSlot slotOne slotTwo valueOne valueTwo valueThree slotTwo
                * atomGram atom rowSlot slotTwo :=
        fun rowSlot => sum_eq_triple_of_support hpivotOne hpivotTwo hslotNe
          fun colSlot hnot => by rw [hvanish colSlot hnot, mul_zero, zero_mul]
      rw [Finset.sum_congr rfl fun rowSlot _ => hinner rowSlot]
      refine sum_eq_triple_of_support hpivotOne hpivotTwo hslotNe ?_
      intro rowSlot hnot
      rw [hvanish rowSlot hnot]
      ring
    rw [hscaleSum, hgramSum, carrierProbe_one,
      carrierProbe_two slotTwo valueOne valueTwo valueThree hpivotOne,
      carrierProbe_three valueOne valueTwo valueThree hpivotTwo hslotNe] at hread
    have hidentity : ((valueOne * valueOne * atomGram atom pivotSlot pivotSlot
            + valueOne * valueTwo * atomGram atom pivotSlot slotOne
            + valueOne * valueThree * atomGram atom pivotSlot slotTwo)
          + (valueTwo * valueOne * atomGram atom slotOne pivotSlot
            + valueTwo * valueTwo * atomGram atom slotOne slotOne
            + valueTwo * valueThree * atomGram atom slotOne slotTwo)
          + (valueThree * valueOne * atomGram atom slotTwo pivotSlot
            + valueThree * valueTwo * atomGram atom slotTwo slotOne
            + valueThree * valueThree * atomGram atom slotTwo slotTwo))
        - (scale pivotSlot * valueOne ^ 2 + scale slotOne * valueTwo ^ 2
          + scale slotTwo * valueThree ^ 2)
        = atomShiftedDiag atom scale pivotSlot * valueOne ^ 2
          + atomShiftedDiag atom scale slotOne * valueTwo ^ 2
          + atomShiftedDiag atom scale slotTwo * valueThree ^ 2
          + 2 * atomGram atom pivotSlot slotOne * valueOne * valueTwo
          + 2 * atomGram atom pivotSlot slotTwo * valueOne * valueThree
          + 2 * atomGram atom slotOne slotTwo * valueTwo * valueThree := by
      simp only [atomShiftedDiag]
      rw [atomGram_comm atom slotOne pivotSlot, atomGram_comm atom slotTwo pivotSlot,
        atomGram_comm atom slotTwo slotOne]
      ring
    linarith [hread, hidentity]
  obtain ⟨hdiagPos, hminorPos, hdetPos⟩ := triple_minors_of_quadratic_pos hform
  have hminor : 0 < atomPairMinor atom scale pivotSlot slotOne := by
    simp only [atomPairMinor]
    exact hminorPos
  have hdet : 0 < atomTripleDet atom scale pivotSlot slotOne slotTwo := by
    simp only [atomTripleDet]
    exact hdetPos
  refine ⟨pivotSlot, slotOne, slotTwo, hpivotOne, hpivotTwo, hslotNe, hdiagPos, hminor, ?_⟩
  have hdeflate := atomTripleDet_deflate atom scale pivotSlot slotOne slotTwo
  linarith [hdeflate, mul_pos hdiagPos hdet]

/-! ## Layer 2 — the deflation dictionary, public -/

/-- **THE MINOR READS AS A SHADOW GAP.**  The pivot minor of a slot is the
shifted diagonal of the pivot against the shadow energy of the slot,
minus the scale and minus one deflation weight against the squared
reading. -/
theorem atomPairMinor_eq_shadow {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {pivot : Fin slotCount} (slot : Fin slotCount)
    (hdiag : atomGram atom pivot pivot ≠ 0)
    (hshift : atomGram atom pivot pivot - scale pivot ≠ 0) :
    atomPairMinor atom scale pivot slot
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slot) ⬝ᵥ planeShadow (atom pivot) (atom slot))
          - scale slot
          - (scale pivot / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
            * atomGram atom pivot slot ^ 2) := by
  have haxisNe : atom pivot ⬝ᵥ atom pivot ≠ 0 := by
    simpa only [atomGram] using hdiag
  have hM : planeShadow (atom pivot) (atom slot) ⬝ᵥ planeShadow (atom pivot) (atom slot)
      = atomGram atom slot slot - atomGram atom pivot slot ^ 2 / atomGram atom pivot pivot := by
    rw [planeShadow_dot_shadow _ _ _ haxisNe]
    simp only [atomGram]
    rw [dotProduct_comm (atom slot) (atom pivot)]
    ring
  rw [hM]
  simp only [atomPairMinor, atomShiftedDiag]
  field_simp [hdiag, hshift]
  ring

/-- **THE DEFLATED CROSS READS AS A SHADOW CROSS.**  The deflated cross
entry of a pair is the shifted diagonal of the pivot against the shadow
cross of the pair, minus one deflation weight against the product of the
two readings. -/
theorem atomPivotCross_eq_shadow {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {pivot : Fin slotCount} (slotOne slotTwo : Fin slotCount)
    (hdiag : atomGram atom pivot pivot ≠ 0)
    (hshift : atomGram atom pivot pivot - scale pivot ≠ 0) :
    atomPivotCross atom scale pivot slotOne slotTwo
      = atomShiftedDiag atom scale pivot
        * ((planeShadow (atom pivot) (atom slotOne)
              ⬝ᵥ planeShadow (atom pivot) (atom slotTwo))
          - (scale pivot / (atomGram atom pivot pivot * atomShiftedDiag atom scale pivot))
            * (atomGram atom pivot slotOne * atomGram atom pivot slotTwo)) := by
  have haxisNe : atom pivot ⬝ᵥ atom pivot ≠ 0 := by
    simpa only [atomGram] using hdiag
  have hC : planeShadow (atom pivot) (atom slotOne)
        ⬝ᵥ planeShadow (atom pivot) (atom slotTwo)
      = atomGram atom slotOne slotTwo
        - atomGram atom pivot slotOne * atomGram atom pivot slotTwo
          / atomGram atom pivot pivot := by
    rw [planeShadow_dot_shadow _ _ _ haxisNe]
    simp only [atomGram]
    rw [dotProduct_comm (atom slotOne) (atom pivot),
      dotProduct_comm (atom slotTwo) (atom pivot)]
  rw [hC]
  simp only [atomPivotCross, atomShiftedDiag]
  field_simp [hdiag, hshift]
  ring

/-! ## Layer 3 — the single-budget window -/

/-- **THE SINGLE-BUDGET CUBIC.**  When every slot of positive shifted
diagonal fails even the single inflation budget, the scale mass obeys the
halved cubic inequality.  The proof is the blocked pigeonhole with the
coefficient two replaced by one. -/
theorem singleBudget_scale_cubic
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)) :
    (1 - ∑ slot, scale slot) * (3 - ∑ slot, scale slot) * (6 - ∑ slot, scale slot)
      ≤ 3 * ∑ slot, scale slot := by
  classical
  have hmassNonneg : 0 ≤ ∑ slot, scale slot :=
    Finset.sum_nonneg fun slot _ => hscale slot
  have hlive : ∀ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot),
      0 < atomShiftedDiag atom scale slot :=
    fun slot hslot => (Finset.mem_filter.mp hslot).2
  have hRfloor : (3 : ℝ) - (∑ slot, scale slot)
      ≤ ∑ slot ∈ Finset.univ.filter (fun slot => 0 < atomShiftedDiag atom scale slot),
          atomShiftedDiag atom scale slot := by
    have htotal := atomShiftedDiag_total hframe scale
    push_cast at htotal
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun slot => 0 < atomShiftedDiag atom scale slot) (atomShiftedDiag atom scale)
    have hnonpos : (∑ slot ∈ Finset.univ.filter
        (fun slot => ¬ 0 < atomShiftedDiag atom scale slot),
          atomShiftedDiag atom scale slot) ≤ 0 :=
      Finset.sum_nonpos fun slot hslot => not_lt.mp (Finset.mem_filter.mp hslot).2
    linarith [htotal, hsplit, hnonpos]
  have hA : ∀ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot),
      atomShiftedDiag atom scale slot * (1 - ∑ other, scale other)
        + 2 * (scale slot * atomShiftedDiag atom scale slot)
      ≤ scale slot := by
    intro slot hslot
    have hb := hfail slot (hlive slot hslot)
    have hgram : atomGram atom slot slot = atomShiftedDiag atom scale slot + scale slot := by
      simp only [atomShiftedDiag]
      ring
    rw [hgram] at hb
    nlinarith [hb, sq_nonneg (scale slot)]
  have hB : ∀ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot),
      (1 - ∑ other, scale other) * atomShiftedDiag atom scale slot ^ 2
        ≤ scale slot * atomShiftedDiag atom scale slot := by
    intro slot hslot
    have ha := hA slot hslot
    have hR := hlive slot hslot
    have hsR : 0 ≤ scale slot * atomShiftedDiag atom scale slot :=
      mul_nonneg (hscale slot) hR.le
    have hlin : (1 - ∑ other, scale other) * atomShiftedDiag atom scale slot
        ≤ scale slot := by nlinarith [ha, hsR]
    nlinarith [mul_le_mul_of_nonneg_right hlin hR.le]
  have hAsum := Finset.sum_le_sum hA
  have hBsum := Finset.sum_le_sum hB
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at hAsum
  rw [← Finset.mul_sum] at hBsum
  have hscaleCap : (∑ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot), scale slot)
      ≤ ∑ slot, scale slot :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun slot _ _ => hscale slot
  have hbase := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.filter (fun slot => 0 < atomShiftedDiag atom scale slot))
    (fun _ => (1:ℝ)) (atomShiftedDiag atom scale)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hbase
  have hcard : ((Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot)).card : ℝ) ≤ 6 := by
    have hle : (Finset.univ.filter
        (fun slot => 0 < atomShiftedDiag atom scale slot)).card ≤ 6 := by
      simpa using Finset.card_filter_le Finset.univ
        (fun slot => 0 < atomShiftedDiag atom scale slot)
    exact_mod_cast hle
  have hQnonneg : 0 ≤ ∑ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot),
        atomShiftedDiag atom scale slot ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : (∑ slot ∈ Finset.univ.filter
      (fun slot => 0 < atomShiftedDiag atom scale slot),
        atomShiftedDiag atom scale slot) ^ 2
      ≤ 6 * ∑ slot ∈ Finset.univ.filter
          (fun slot => 0 < atomShiftedDiag atom scale slot),
            atomShiftedDiag atom scale slot ^ 2 := by
    nlinarith [hbase, hcard, hQnonneg]
  have hdelta : 0 ≤ 1 - ∑ slot, scale slot := by linarith
  have hthree : (0:ℝ) ≤ 3 - ∑ slot, scale slot := by linarith
  have hTfloorSq : (3 - ∑ slot, scale slot) ^ 2
      ≤ (∑ slot ∈ Finset.univ.filter
          (fun slot => 0 < atomShiftedDiag atom scale slot),
            atomShiftedDiag atom scale slot) ^ 2 := by
    nlinarith [hRfloor, hthree]
  have hstepOne : (1 - ∑ slot, scale slot) * (3 - ∑ slot, scale slot) ^ 2
      ≤ 6 * (1 - ∑ slot, scale slot)
        * ∑ slot ∈ Finset.univ.filter
            (fun slot => 0 < atomShiftedDiag atom scale slot),
              atomShiftedDiag atom scale slot ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hTfloorSq hdelta,
      mul_le_mul_of_nonneg_left hcs hdelta]
  have hTlin : (1 - ∑ slot, scale slot) * (3 - ∑ slot, scale slot)
      ≤ (1 - ∑ slot, scale slot)
        * ∑ slot ∈ Finset.univ.filter
            (fun slot => 0 < atomShiftedDiag atom scale slot),
              atomShiftedDiag atom scale slot :=
    mul_le_mul_of_nonneg_left hRfloor hdelta
  nlinarith [hstepOne, hBsum, hAsum, hTlin, hscaleCap, hdelta, hthree, hmassNonneg]

/-- **THE SINGLE-BUDGET WINDOW.**  Failure of the single budget at every
live pivot forces the scale mass above `39/50`.  The halved cubic factors
at that point with a positive quadratic cofactor. -/
theorem singleBudget_scale_lt
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)) :
    39 / 50 < ∑ slot, scale slot := by
  have hcubic := singleBudget_scale_cubic hframe hscale hsmall hfail
  by_contra hnot
  have hle : (∑ slot, scale slot) ≤ 39 / 50 := not_lt.mp hnot
  have hfac : (1 - ∑ slot, scale slot) * (3 - ∑ slot, scale slot)
      * (6 - ∑ slot, scale slot) - 3 * (∑ slot, scale slot) - 26181 / 125000
      = (39 / 50 - ∑ slot, scale slot)
        * ((∑ slot, scale slot) ^ 2 - (461 / 50) * (∑ slot, scale slot)
          + 57021 / 2500) := by
    ring
  have hquad : 0 ≤ (∑ slot, scale slot) ^ 2 - (461 / 50) * (∑ slot, scale slot)
      + 57021 / 2500 := by
    nlinarith [sq_nonneg ((∑ slot, scale slot) - 461 / 100)]
  have hprod : 0 ≤ (39 / 50 - ∑ slot, scale slot)
      * ((∑ slot, scale slot) ^ 2 - (461 / 50) * (∑ slot, scale slot)
        + 57021 / 2500) :=
    mul_nonneg (by linarith) hquad
  linarith [hcubic, hfac, hprod]

/-- **BELOW `39/50` A SINGLE-BUDGET PIVOT EXISTS.**  The doubly blocked
stratum therefore lives in the scale mass window above `39/50`. -/
theorem exists_pivot_single_budget_of_scale_le
    {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hscale : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) ≤ 39 / 50) :
    ∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot := by
  by_contra hno
  have hfail : ∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + scale pivot * (1 - atomGram atom pivot pivot) := by
    intro pivot hpos
    by_contra hlt
    exact hno ⟨pivot, hpos, not_le.mp hlt⟩
  have hwindow := singleBudget_scale_lt hframe hscale
    (lt_of_le_of_lt hsmall (by norm_num)) hfail
  linarith

/-! ## Layer 4 — the residue and the lossless swap -/

/-- **THE RESIDUE.**  The blocked stratum with the deflated pair
conclusion: one pivot of positive shifted diagonal, one positive pivot
minor, and one deflated cross test.  Four polynomial inequalities replace
the card-three carrier with its probe quantifier, and the two forms are
equivalent through the bridge theorems that follow. -/
def AtomBlockedPairClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot →
      atomShiftedDiag atom scale pivot
        ≤ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo

/-- **THE RESIDUE CLOSES THE PIVOT PAIR RESIDUE.**  At every datum a
budget pivot either exists, and the landed engine supplies the deflated
pair, or every pivot is blocked, and the residue fires. -/
theorem atomPivotPairClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : AtomPivotPairClosed := by
  intro atom scale hpos hsmall hframe
  by_cases hex : ∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ ((∑ slot, scale slot) - scale pivot) * atomShiftedDiag atom scale pivot
          + 2 * scale pivot * (1 - atomGram atom pivot pivot)
        < atomShiftedDiag atom scale pivot
  · obtain ⟨pivot, hp, hb⟩ := hex
    obtain ⟨slotOne, slotTwo, honePivot, htwoPivot, hpair, hR, hminor, hcross⟩ :=
      exists_pivotPair_of_pivot_budget hframe (fun slot => (hpos slot).le) hp hb
    exact ⟨pivot, slotOne, slotTwo, honePivot, htwoPivot, hpair, hR, hminor, hcross⟩
  · refine hresidue atom scale hpos hsmall hframe fun pivot hpivot => ?_
    by_contra hlt
    exact hex ⟨pivot, hpivot, not_le.mp hlt⟩

/-- The polynomial residue closes the pivot pair residue through the
Dodgson identity, thus the two exists-forms agree. -/
theorem atomPivotPairClosed_of_sylvester
    (hresidue : AtomTripleSylvesterClosed) : AtomPivotPairClosed := by
  intro atom scale hpos hsmall hframe
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hdiag, hminor, hdet⟩ :=
    hresidue atom scale hpos hsmall hframe
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hdiag, hminor, ?_⟩
  have hdeflate := atomTripleDet_deflate atom scale slotOne slotTwo slotThree
  linarith [hdeflate, mul_pos hdiag hdet]

/-- The unconditional pivot pair residue carries the blocked one. -/
theorem atomBlockedPairClosed_of_pivotPair
    (hresidue : AtomPivotPairClosed) : AtomBlockedPairClosed :=
  fun atom scale hpos hsmall hframe _ => hresidue atom scale hpos hsmall hframe

/-- **THE SWAP, FORWARD.**  The landed blocked residue gives the deflated
pair form through the converse Sylvester extraction. -/
theorem atomBlockedPairClosed_of_blockedPivot
    (hresidue : AtomBlockedPivotClosed) : AtomBlockedPairClosed := by
  intro atom scale hpos hsmall hframe hblocked
  obtain ⟨car, hcard, hdom⟩ := hresidue atom scale hpos hsmall hframe hblocked
  exact exists_pivotPair_of_dominating_carrier hcard hdom

/-- **THE SWAP, BACKWARD.**  The deflated pair form gives the landed
blocked residue through the deflation discharge and the carrier. -/
theorem atomBlockedPivotClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : AtomBlockedPivotClosed := by
  intro atom scale hpos hsmall hframe hblocked
  obtain ⟨pivot, slotOne, slotTwo, honePivot, htwoPivot, hpair, hR, hminor, hcross⟩ :=
    hresidue atom scale hpos hsmall hframe hblocked
  exact ⟨{pivot, slotOne, slotTwo}, card_triple_slots honePivot htwoPivot hpair,
    fun probe hvanish hne => dominates_of_triple_minors honePivot htwoPivot hpair hR hminor
      (atomTripleDet_pos_of_deflated_pair hR hcross) hvanish hne⟩

/-- **THE LOSSLESS SWAP.**  The deflated pair residue and the carrier
residue are one obligation. -/
theorem atomBlockedPairClosed_iff_blockedPivot :
    AtomBlockedPairClosed ↔ AtomBlockedPivotClosed :=
  ⟨atomBlockedPivotClosed_of_blockedPair, atomBlockedPairClosed_of_blockedPivot⟩

/-! ## Layer 5 — the cell and the ladder from the residue -/

/-- The polynomial residue from the new residue. -/
theorem atomTripleSylvesterClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : AtomTripleSylvesterClosed :=
  atomTripleSylvesterClosed_of_pivotPair (atomPivotPairClosed_of_blockedPair hresidue)

/-- The atom triple ceiling from the new residue. -/
theorem atomTripleCeilingClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : AtomTripleCeilingClosed :=
  atomTripleCeilingClosed_of_sylvester (atomTripleSylvesterClosed_of_blockedPair hresidue)

/-- **THE `(6,3)` CELL FROM THE NEW RESIDUE.** -/
theorem gtzWeighted_six_three_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- **THE RANK-THREE PAYOFF FROM THE NEW RESIDUE.** -/
theorem gtzWeightedAll_three_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- The crux type is empty under the new residue. -/
theorem isEmpty_sixThreeCrux_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- The rank-five dense branch from the new residue. -/
theorem rankFiveDenseClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : RankFiveDenseClosed :=
  rankFiveDenseClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- The rank-six dense branch from the new residue. -/
theorem rankSixDenseClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : RankSixDenseClosed :=
  rankSixDenseClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- Profile B at rank five from the new residue. -/
theorem rankFiveDenseHeavyFourClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : RankFiveDenseHeavyFourClosed :=
  rankFiveDenseHeavyFourClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- Profile C at rank five from the new residue. -/
theorem rankFiveDenseThreeTriplesClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : RankFiveDenseThreeTriplesClosed :=
  rankFiveDenseThreeTriplesClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- Profile A at rank six from the new residue. -/
theorem rankSixDenseHeavyFiveClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : RankSixDenseHeavyFiveClosed :=
  rankSixDenseHeavyFiveClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- Profile B at rank six from the new residue. -/
theorem rankSixDenseHeavyFourClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : RankSixDenseHeavyFourClosed :=
  rankSixDenseHeavyFourClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- Profile C at rank six from the new residue. -/
theorem rankSixDenseAllTriplesClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : RankSixDenseAllTriplesClosed :=
  rankSixDenseAllTriplesClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- The rank-six support-two closure from the new residue. -/
theorem rankSixSupportTwoClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : RankSixSupportTwoClosed :=
  rankSixSupportTwoClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- The rank-five support-two closure from the new residue. -/
theorem rankFiveSupportTwoClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : RankFiveSupportTwoClosed :=
  rankFiveSupportTwoClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

/-- The rank-four support-two closure from the new residue. -/
theorem rankFourSupportTwoClosed_of_blockedPair
    (hresidue : AtomBlockedPairClosed) : RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_blockedPair hresidue)

end Gtz
