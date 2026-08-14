import Gtz.Wave.AtomCoherentTriangle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6400000

/-!
# The boundary witness: the scale mass bound of the blocked residue is sharp

Every residue of the atom lane carries the hypothesis `sum scale < 1`, and
the inequality is STRICT.  This module shows that the strictness is
load-bearing: at scale mass EXACTLY one there is a real datum that satisfies
every other hypothesis of `Gtz.AtomBlockedPairClosed` and refutes its
conclusion at all one hundred and twenty ordered triples.

The witness is the regular tetrahedron with two of its four directions
DOUBLED.  Four directions of squared length three resolve the identity at
uniform weight one quarter, and a doubled direction splits its weight between
two parallel slots without changing the frame operator.  Choosing the split
`(3/5, 4/5)` makes every entry rational, so the whole witness is exact
arithmetic with no square root anywhere.

Its readings at mass one are: shifted diagonals `9/50, 8/25, 9/50, 8/25, 1/2,
1/2`, all positive, thus every slot is live.  It is blocked at every slot,
with the two undoubled slots blocked with EQUALITY.  And every one of its
twenty triple determinants is nonpositive, twelve of them EXACTLY ZERO — the
twelve triples that pick three distinct directions.  The eight remaining
triples repeat a direction, and a repeated direction can never dominate.

## What this pins down

The adversarial floor of the whole lane is `(1 - mass) / 6`, and the witness
attains it: putting the scales at `weight - (1 - mass) / 6` for any mass below
one gives a datum whose best triple dominates by exactly `(1 - mass) / 6` and
no more.  As the mass runs up to one the margin runs down to zero.  **No
certificate with a fixed positive margin can ever cover the blocked
stratum**, and every proof of the residue must be tight at this witness.

The witness also explains the shape of the adversarial extremal: an exactly
parallel pair of slots, and twelve tied triples.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomBoundaryAtom`, `Gtz.atomBoundaryScale`,
  `Gtz.atomBoundaryAtom_isTightFrame`, `Gtz.atomBoundaryScale_sum` — the
  witness, exact and rational.
* `Gtz.atomBoundaryAtom_gram` — the whole Gram as a rational table.
* `Gtz.atomBoundaryAtom_shiftedDiag_pos`, `Gtz.atomBoundaryAtom_blocked` —
  every slot live, every slot blocked.
* `Gtz.atomBoundaryAtom_tripleDet_nonpos` — **ALL TWENTY TRIPLE DETERMINANTS
  ARE NONPOSITIVE.**
* `Gtz.atomBoundaryAtom_no_deflated_pair` — the conclusion of the residue
  fails at every ordered triple.
* `Gtz.not_atomBlockedPairClosedAtMassOne` — **THE STRICT MASS BOUND CANNOT
  BE RELAXED.**

## Vacuity

Every statement is an exact rational computation at one named configuration,
and the last theorem is a refutation, thus none of them is vacuous.
-/

namespace Gtz

/-! ## Layer 0 — the witness -/

/-- **THE BOUNDARY WITNESS.**  The regular tetrahedron of rank three with two
of its four directions doubled, at the rational split `(3/5, 4/5)`.  Slots
zero and one carry one direction, slots two and three carry a second, and
slots four and five carry the remaining two. -/
noncomputable def atomBoundaryAtom : Fin 6 → (Fin 3 → ℝ) :=
  ![![3 / 10, 3 / 10, 3 / 10], ![2 / 5, 2 / 5, 2 / 5],
    ![3 / 10, -(3 / 10), -(3 / 10)], ![2 / 5, -(2 / 5), -(2 / 5)],
    ![-(1 / 2), 1 / 2, -(1 / 2)], ![-(1 / 2), -(1 / 2), 1 / 2]]

/-- The scale family of the witness: the squared length of each atom divided
by three, which is the weight the tetrahedron gives that slot.  The six add to
exactly one. -/
noncomputable def atomBoundaryScale : Fin 6 → ℝ :=
  ![9 / 100, 4 / 25, 9 / 100, 4 / 25, 1 / 4, 1 / 4]

/-- The Gram of the witness, as a rational table. -/
noncomputable def atomBoundaryGram : Fin 6 → Fin 6 → ℝ :=
  ![![27 / 100, 9 / 25, -(9 / 100), -(3 / 25), -(3 / 20), -(3 / 20)],
    ![9 / 25, 12 / 25, -(3 / 25), -(4 / 25), -(1 / 5), -(1 / 5)],
    ![-(9 / 100), -(3 / 25), 27 / 100, 9 / 25, -(3 / 20), -(3 / 20)],
    ![-(3 / 25), -(4 / 25), 9 / 25, 12 / 25, -(1 / 5), -(1 / 5)],
    ![-(3 / 20), -(1 / 5), -(3 / 20), -(1 / 5), 3 / 4, -(1 / 4)],
    ![-(3 / 20), -(1 / 5), -(3 / 20), -(1 / 5), -(1 / 4), 3 / 4]]

theorem atomBoundaryScale_pos (slot : Fin 6) : 0 < atomBoundaryScale slot := by
  fin_cases slot <;> norm_num [atomBoundaryScale]

/-- **THE SCALE MASS IS EXACTLY ONE.**  This is the single hypothesis of the
residue that the witness fails, and it fails by an equality. -/
theorem atomBoundaryScale_sum : (∑ slot, atomBoundaryScale slot) = 1 := by
  simp [Fin.sum_univ_six, atomBoundaryScale]
  norm_num

/-- **THE WITNESS IS A TIGHT FRAME.**  Two doubled directions and two single
ones resolve the identity exactly. -/
theorem atomBoundaryAtom_isTightFrame (probe direction : Fin 3 → ℝ) :
    (∑ slot, (atomBoundaryAtom slot ⬝ᵥ probe) * (atomBoundaryAtom slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  simp [Fin.sum_univ_six, atomBoundaryAtom, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE GRAM OF THE WITNESS IS THE RATIONAL TABLE.** -/
theorem atomBoundaryAtom_gram (rowSlot colSlot : Fin 6) :
    atomGram atomBoundaryAtom rowSlot colSlot = atomBoundaryGram rowSlot colSlot := by
  fin_cases rowSlot <;> fin_cases colSlot <;>
    simp [atomGram, atomBoundaryAtom, atomBoundaryGram, dotProduct,
      Fin.sum_univ_three] <;>
    norm_num

/-- Every shifted diagonal of the witness is positive, thus every slot is
live and the blocked hypothesis has content at all six. -/
theorem atomBoundaryAtom_shiftedDiag_pos (slot : Fin 6) :
    0 < atomShiftedDiag atomBoundaryAtom atomBoundaryScale slot := by
  simp only [atomShiftedDiag, atomBoundaryAtom_gram]
  fin_cases slot <;>
    norm_num [atomBoundaryGram, atomBoundaryScale]

/-- **THE WITNESS IS BLOCKED AT EVERY SLOT**, and the two undoubled slots are
blocked with equality.  It therefore satisfies the blocked hypothesis of
`Gtz.AtomBlockedPairClosed` in full. -/
theorem atomBoundaryAtom_blocked (pivot : Fin 6) :
    atomShiftedDiag atomBoundaryAtom atomBoundaryScale pivot
      ≤ ((∑ slot, atomBoundaryScale slot) - atomBoundaryScale pivot)
          * atomShiftedDiag atomBoundaryAtom atomBoundaryScale pivot
        + 2 * atomBoundaryScale pivot
          * (1 - atomGram atomBoundaryAtom pivot pivot) := by
  rw [atomBoundaryScale_sum]
  simp only [atomShiftedDiag, atomBoundaryAtom_gram]
  fin_cases pivot <;>
    norm_num [atomBoundaryGram, atomBoundaryScale]

/-! ## Layer 1 — the refutation -/

/-- **EVERY TRIPLE DETERMINANT OF THE WITNESS IS NONPOSITIVE.**  Twelve of the
twenty vanish exactly, and those twelve are the triples that pick three
distinct tetrahedron directions.  The remaining eight repeat a direction. -/
theorem atomBoundaryAtom_tripleDet_nonpos {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) :
    atomTripleDet atomBoundaryAtom atomBoundaryScale slotOne slotTwo slotThree
      ≤ 0 := by
  simp only [atomTripleDet, atomShiftedDiag, atomBoundaryAtom_gram]
  fin_cases slotOne <;> fin_cases slotTwo <;> fin_cases slotThree <;>
    first
      | exact absurd rfl honeTwo
      | exact absurd rfl honeThree
      | exact absurd rfl htwoThree
      | norm_num [atomBoundaryGram, atomBoundaryScale]

/-- **THE CONCLUSION OF THE RESIDUE FAILS AT EVERY ORDERED TRIPLE.**  A live
pivot and a nonpositive triple determinant leave no room for the deflated
pair test. -/
theorem atomBoundaryAtom_no_deflated_pair (pivot slotOne slotTwo : Fin 6)
    (hpivotOne : pivot ≠ slotOne) (hpivotTwo : pivot ≠ slotTwo)
    (honeTwo : slotOne ≠ slotTwo) :
    ¬ AtomTripleDeflates atomBoundaryAtom atomBoundaryScale pivot slotOne slotTwo := by
  rintro ⟨hdiag, _, hcross⟩
  have hdeflate := atomTripleDet_deflate atomBoundaryAtom atomBoundaryScale
    pivot slotOne slotTwo
  have hdet := atomBoundaryAtom_tripleDet_nonpos hpivotOne hpivotTwo honeTwo
  nlinarith [hdeflate, hdet, hdiag, hcross]

/-! ## Layer 2 — the calibration -/

/-- The blocked residue with the scale mass bound RELAXED from strict to
nonstrict.  Everything else is word for word `Gtz.AtomBlockedPairClosed`. -/
def AtomBlockedPairClosedAtMassOne : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) ≤ 1 →
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

/-- **THE STRICT MASS BOUND OF THE BLOCKED RESIDUE CANNOT BE RELAXED.**  The
boundary witness satisfies positive scales, mass at most one, the tight frame
law and blockedness at every slot, and it carries no deflated pair.  Every
proof of `Gtz.AtomBlockedPairClosed` must therefore consume the strictness of
`sum scale < 1`, and no certificate with a margin uniform in the mass can
exist. -/
theorem not_atomBlockedPairClosedAtMassOne : ¬ AtomBlockedPairClosedAtMassOne := by
  intro hclosed
  obtain ⟨pivot, slotOne, slotTwo, hpivotOne, hpivotTwo, honeTwo, hdiag, hminor,
    hcross⟩ :=
    hclosed atomBoundaryAtom atomBoundaryScale atomBoundaryScale_pos
      (le_of_eq atomBoundaryScale_sum) atomBoundaryAtom_isTightFrame
      (fun pivot _ => atomBoundaryAtom_blocked pivot)
  exact atomBoundaryAtom_no_deflated_pair pivot slotOne slotTwo hpivotOne hpivotTwo
    honeTwo ⟨hdiag, hminor, hcross⟩

/-- The relaxed residue would carry the strict one, thus the calibration above
is a genuine separation of the two and not a restatement. -/
theorem atomBlockedPairClosed_of_atMassOne
    (hclosed : AtomBlockedPairClosedAtMassOne) : AtomBlockedPairClosed :=
  fun atom scale hpos hsmall hframe hblocked =>
    hclosed atom scale hpos hsmall.le hframe hblocked

end Gtz
