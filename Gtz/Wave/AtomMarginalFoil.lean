import Gtz.Wave.AtomVertexSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6400000

/-!
# The marginal foil: the free cover exists, and no order on it rounds

`Gtz.atomFractionalCoverClosed_holds` gives every datum an explicit
fractional cover of total three — the squared length of each atom — and
the residue of the lane asks for a cover carried by a TRIPLE.  The obvious
rounding takes the three slots of largest cover weight.  This module
refutes that rounding, and every rounding that reads only an order on the
slots, at one exact rational datum.

## The datum

Two parallel atoms along the first axis of squared lengths `400/841` and
`441/841`, one atom along the second axis of squared length one, and three
atoms along the third axis of squared lengths `4/9`, `4/9` and `1/9`.  The
six resolve the identity exactly, and the scale is uniform at one sixth.

Its marginals are `400/841, 1, 441/841, 4/9, 4/9, 1/9`.  The three
LARGEST belong to slots zero, one and two, and slot zero beats slot three
by `400/841 - 4/9 = 236/7569`, a strict gap.  But slots zero and two are
PARALLEL, so the triple of the three largest marginals spans a plane and
carries the kernel probe `(21, 0, -20)`.  At that probe the scale energy
is `841/6` and the blend energy is zero.

## What the datum refutes

At a uniform scale every marginal-driven order agrees: the order by the
marginal, by the marginal against the scale, by the marginal minus the
scale, and by the squared marginal against the scale all give the same
three slots.  One datum therefore kills the whole family.  This is the
sixth refuted selection rule of the lane, and the first one that reads the
free cover itself.

## What the datum does NOT refute

Four triples of the datum DO dominate: `{0,1,3}`, `{0,1,4}`, `{1,2,3}` and
`{1,2,4}`.  The datum satisfies the residue, and it is a foil for the
rounding only.

## The heavy criterion is sharp at this datum

The three largest marginals total EXACTLY two.  The heavy criterion of
`Gtz.atomTriple_values_of_heavy` asks for two plus the scale, and this
datum shows that the scale term cannot be dropped: at a marginal total of
exactly two the triple fails.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomMarginalFoilAtom`, `Gtz.atomMarginalFoilScale`,
  `Gtz.atomMarginalFoilAtom_isTightFrame`,
  `Gtz.atomMarginalFoilScale_pos`, `Gtz.atomMarginalFoilScale_sum` — the
  datum, exact and rational.
* `Gtz.atomMarginalFoilGram_*` — the Gram entries the refutation reads.
* `Gtz.atomMarginalFoil_marginal_top`, `Gtz.atomMarginalFoil_marginal_total`
  — **THE THREE LARGEST MARGINALS ARE SLOTS ZERO, ONE AND TWO**, and they
  total exactly two.
* `Gtz.atomMarginalFoil_top_fails` — **THE TOP TRIPLE FAILS**, at the
  explicit probe.
* `Gtz.atomMarginalFoil_carrier` — the datum carries a dominating triple,
  thus it is a foil and not a counterexample.
* `Gtz.AtomMarginalOrderSelectionClosed`,
  `Gtz.not_atomMarginalOrderSelectionClosed`,
  `Gtz.AtomRatioOrderSelectionClosed`,
  `Gtz.not_atomRatioOrderSelectionClosed` — **THE TWO ORDER RULES ARE
  FALSE**.
* `Gtz.not_atomTriple_values_of_marginal_total_two` — **THE HEAVY
  CRITERION NEEDS ITS SCALE TERM**.

## Vacuity

Every statement is an exact rational computation at one named datum, and
the last four are refutations, thus none of them is vacuous.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the datum -/

/-- **THE MARGINAL FOIL.**  Two parallel atoms on the first axis, one atom
on the second, and three atoms on the third. -/
noncomputable def atomMarginalFoilAtom : Fin 6 → (Fin 3 → ℝ) :=
  ![![20 / 29, 0, 0], ![0, 1, 0], ![21 / 29, 0, 0],
    ![0, 0, 2 / 3], ![0, 0, 2 / 3], ![0, 0, 1 / 3]]

/-- The scale of the foil is uniform, so every marginal-driven order on
its slots is the order by the marginal itself. -/
noncomputable def atomMarginalFoilScale : Fin 6 → ℝ := fun _ => 1 / 6

theorem atomMarginalFoilScale_pos (slot : Fin 6) : 0 < atomMarginalFoilScale slot := by
  norm_num [atomMarginalFoilScale]

theorem atomMarginalFoilScale_sum : (∑ slot, atomMarginalFoilScale slot) = 1 := by
  simp [atomMarginalFoilScale]

/-- **THE FOIL IS A TIGHT FRAME.**  The six atoms resolve the identity
exactly. -/
theorem atomMarginalFoilAtom_isTightFrame (probe direction : Fin 3 → ℝ) :
    (∑ slot, (atomMarginalFoilAtom slot ⬝ᵥ probe) * (atomMarginalFoilAtom slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  simp [Fin.sum_univ_six, atomMarginalFoilAtom, dotProduct, Fin.sum_univ_three]
  ring

/-! ## Layer 1 — the Gram entries the refutation reads -/

theorem atomMarginalFoilGram_zero_zero :
    atomGram atomMarginalFoilAtom 0 0 = 400 / 841 := by
  simp only [atomGram, show atomMarginalFoilAtom 0 = ![20 / 29, 0, 0] from rfl]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

theorem atomMarginalFoilGram_one_one : atomGram atomMarginalFoilAtom 1 1 = 1 := by
  simp only [atomGram, show atomMarginalFoilAtom 1 = ![0, 1, 0] from rfl]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

theorem atomMarginalFoilGram_two_two :
    atomGram atomMarginalFoilAtom 2 2 = 441 / 841 := by
  simp only [atomGram, show atomMarginalFoilAtom 2 = ![21 / 29, 0, 0] from rfl]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

theorem atomMarginalFoilGram_three_three : atomGram atomMarginalFoilAtom 3 3 = 4 / 9 := by
  simp only [atomGram, show atomMarginalFoilAtom 3 = ![0, 0, 2 / 3] from rfl]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

theorem atomMarginalFoilGram_four_four : atomGram atomMarginalFoilAtom 4 4 = 4 / 9 := by
  simp only [atomGram, show atomMarginalFoilAtom 4 = ![0, 0, 2 / 3] from rfl]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

theorem atomMarginalFoilGram_five_five : atomGram atomMarginalFoilAtom 5 5 = 1 / 9 := by
  simp only [atomGram, show atomMarginalFoilAtom 5 = ![0, 0, 1 / 3] from rfl]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

theorem atomMarginalFoilGram_zero_one : atomGram atomMarginalFoilAtom 0 1 = 0 := by
  simp only [atomGram, show atomMarginalFoilAtom 0 = ![20 / 29, 0, 0] from rfl,
    show atomMarginalFoilAtom 1 = ![0, 1, 0] from rfl]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

theorem atomMarginalFoilGram_zero_two :
    atomGram atomMarginalFoilAtom 0 2 = 420 / 841 := by
  simp only [atomGram, show atomMarginalFoilAtom 0 = ![20 / 29, 0, 0] from rfl,
    show atomMarginalFoilAtom 2 = ![21 / 29, 0, 0] from rfl]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

theorem atomMarginalFoilGram_one_two : atomGram atomMarginalFoilAtom 1 2 = 0 := by
  simp only [atomGram, show atomMarginalFoilAtom 1 = ![0, 1, 0] from rfl,
    show atomMarginalFoilAtom 2 = ![21 / 29, 0, 0] from rfl]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

theorem atomMarginalFoilGram_zero_three : atomGram atomMarginalFoilAtom 0 3 = 0 := by
  simp only [atomGram, show atomMarginalFoilAtom 0 = ![20 / 29, 0, 0] from rfl,
    show atomMarginalFoilAtom 3 = ![0, 0, 2 / 3] from rfl]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

theorem atomMarginalFoilGram_one_three : atomGram atomMarginalFoilAtom 1 3 = 0 := by
  simp only [atomGram, show atomMarginalFoilAtom 1 = ![0, 1, 0] from rfl,
    show atomMarginalFoilAtom 3 = ![0, 0, 2 / 3] from rfl]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

/-! ## Layer 2 — the marginal order -/

/-- **THE THREE LARGEST MARGINALS BELONG TO SLOTS ZERO, ONE AND TWO.**
Each of the three remaining slots is strictly below each of the three. -/
theorem atomMarginalFoil_marginal_top (other : Fin 6)
    (hzero : other ≠ 0) (hone : other ≠ 1) (htwo : other ≠ 2) :
    atomGram atomMarginalFoilAtom other other ≤ atomGram atomMarginalFoilAtom 0 0
      ∧ atomGram atomMarginalFoilAtom other other ≤ atomGram atomMarginalFoilAtom 1 1
      ∧ atomGram atomMarginalFoilAtom other other
          ≤ atomGram atomMarginalFoilAtom 2 2 := by
  have hcases : ∀ slot : Fin 6, slot ≠ 0 → slot ≠ 1 → slot ≠ 2 →
      slot = 3 ∨ slot = 4 ∨ slot = 5 := by decide
  rw [atomMarginalFoilGram_zero_zero, atomMarginalFoilGram_one_one,
    atomMarginalFoilGram_two_two]
  rcases hcases other hzero hone htwo with hslot | hslot | hslot
  · rw [hslot, atomMarginalFoilGram_three_three]; norm_num
  · rw [hslot, atomMarginalFoilGram_four_four]; norm_num
  · rw [hslot, atomMarginalFoilGram_five_five]; norm_num

/-- **THE THREE LARGEST MARGINALS TOTAL EXACTLY TWO.**  The heavy
criterion asks for two plus the scale, and this datum sits on its
boundary. -/
theorem atomMarginalFoil_marginal_total :
    atomGram atomMarginalFoilAtom 0 0 + atomGram atomMarginalFoilAtom 1 1
      + atomGram atomMarginalFoilAtom 2 2 = 2 := by
  rw [atomMarginalFoilGram_zero_zero, atomMarginalFoilGram_one_one,
    atomMarginalFoilGram_two_two]
  norm_num

/-! ## Layer 3 — the top triple fails -/

/-- **THE TOP TRIPLE FAILS.**  At the kernel probe `(21, 0, -20)` the
scale energy of the three heaviest slots is `841/6` and their blend energy
is zero. -/
theorem atomMarginalFoil_top_fails :
    ¬ (atomMarginalFoilScale 0 * (21 : ℝ) ^ 2 + atomMarginalFoilScale 1 * (0 : ℝ) ^ 2
          + atomMarginalFoilScale 2 * (-20 : ℝ) ^ 2
        ≤ atomGram atomMarginalFoilAtom 0 0 * (21 : ℝ) ^ 2
          + atomGram atomMarginalFoilAtom 1 1 * (0 : ℝ) ^ 2
          + atomGram atomMarginalFoilAtom 2 2 * (-20 : ℝ) ^ 2
          + 2 * atomGram atomMarginalFoilAtom 0 1 * (21 : ℝ) * (0 : ℝ)
          + 2 * atomGram atomMarginalFoilAtom 0 2 * (21 : ℝ) * (-20 : ℝ)
          + 2 * atomGram atomMarginalFoilAtom 1 2 * (0 : ℝ) * (-20 : ℝ)) := by
  rw [atomMarginalFoilGram_zero_zero, atomMarginalFoilGram_one_one,
    atomMarginalFoilGram_two_two, atomMarginalFoilGram_zero_one,
    atomMarginalFoilGram_zero_two, atomMarginalFoilGram_one_two]
  norm_num [atomMarginalFoilScale]

/-! ## Layer 4 — the datum satisfies the residue -/

/-- **THE FOIL CARRIES A DOMINATING TRIPLE.**  Slots zero, one and three
are pairwise orthogonal and each carries a marginal above one sixth, so
the datum is a foil for the rounding and not a counterexample to the
residue. -/
theorem atomMarginalFoil_values :
    ∀ valueOne valueTwo valueThree : ℝ,
      atomMarginalFoilScale 0 * valueOne ^ 2 + atomMarginalFoilScale 1 * valueTwo ^ 2
          + atomMarginalFoilScale 3 * valueThree ^ 2
        ≤ atomGram atomMarginalFoilAtom 0 0 * valueOne ^ 2
          + atomGram atomMarginalFoilAtom 1 1 * valueTwo ^ 2
          + atomGram atomMarginalFoilAtom 3 3 * valueThree ^ 2
          + 2 * atomGram atomMarginalFoilAtom 0 1 * valueOne * valueTwo
          + 2 * atomGram atomMarginalFoilAtom 0 3 * valueOne * valueThree
          + 2 * atomGram atomMarginalFoilAtom 1 3 * valueTwo * valueThree := by
  intro valueOne valueTwo valueThree
  rw [atomMarginalFoilGram_zero_zero, atomMarginalFoilGram_one_one,
    atomMarginalFoilGram_three_three, atomMarginalFoilGram_zero_one,
    atomMarginalFoilGram_zero_three, atomMarginalFoilGram_one_three]
  simp only [atomMarginalFoilScale]
  nlinarith [sq_nonneg valueOne, sq_nonneg valueTwo, sq_nonneg valueThree]

/-- The dominating triple of the foil, as a weak carrier of the residue. -/
theorem atomMarginalFoil_carrier :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, atomMarginalFoilScale slot * probe slot ^ 2)
            ≤ atomBlend atomMarginalFoilAtom probe ⬝ᵥ atomBlend atomMarginalFoilAtom probe :=
  exists_weakCarrier_of_values (by decide) (by decide) (by decide) atomMarginalFoil_values

/-! ## Layer 5 — the two order rules are false -/

/-- **SELECTION BY THE MARGINAL ORDER.**  Every triple whose three
marginals dominate the marginals of the three remaining slots is a
dominating triple. -/
def AtomMarginalOrderSelectionClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∀ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo → slotOne ≠ slotThree → slotTwo ≠ slotThree →
      (∀ other : Fin 6, other ≠ slotOne → other ≠ slotTwo → other ≠ slotThree →
        atomGram atom other other ≤ atomGram atom slotOne slotOne
          ∧ atomGram atom other other ≤ atomGram atom slotTwo slotTwo
          ∧ atomGram atom other other ≤ atomGram atom slotThree slotThree) →
      ∀ valueOne valueTwo valueThree : ℝ,
        scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
            + scale slotThree * valueThree ^ 2
          ≤ atomGram atom slotOne slotOne * valueOne ^ 2
            + atomGram atom slotTwo slotTwo * valueTwo ^ 2
            + atomGram atom slotThree slotThree * valueThree ^ 2
            + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
            + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
            + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree

/-- **THE MARGINAL ORDER DOES NOT SELECT.**  The free cover of the lane
exists at every datum, and no rounding that reads only the order of its
weights is correct. -/
theorem not_atomMarginalOrderSelectionClosed : ¬ AtomMarginalOrderSelectionClosed := by
  intro hclosed
  exact atomMarginalFoil_top_fails
    (hclosed atomMarginalFoilAtom atomMarginalFoilScale atomMarginalFoilScale_pos
      atomMarginalFoilScale_sum atomMarginalFoilAtom_isTightFrame 0 1 2
      (by decide) (by decide) (by decide)
      (fun other hzero hone htwo => atomMarginalFoil_marginal_top other hzero hone htwo)
      21 0 (-20))

/-- **SELECTION BY THE RATIO ORDER.**  The same rule with the marginal
read against the scale. -/
def AtomRatioOrderSelectionClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∀ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo → slotOne ≠ slotThree → slotTwo ≠ slotThree →
      (∀ other : Fin 6, other ≠ slotOne → other ≠ slotTwo → other ≠ slotThree →
        atomGram atom other other / scale other
            ≤ atomGram atom slotOne slotOne / scale slotOne
          ∧ atomGram atom other other / scale other
            ≤ atomGram atom slotTwo slotTwo / scale slotTwo
          ∧ atomGram atom other other / scale other
            ≤ atomGram atom slotThree slotThree / scale slotThree) →
      ∀ valueOne valueTwo valueThree : ℝ,
        scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
            + scale slotThree * valueThree ^ 2
          ≤ atomGram atom slotOne slotOne * valueOne ^ 2
            + atomGram atom slotTwo slotTwo * valueTwo ^ 2
            + atomGram atom slotThree slotThree * valueThree ^ 2
            + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
            + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
            + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree

/-- **THE RATIO ORDER DOES NOT SELECT EITHER.**  The scale of the foil is
uniform, so the ratio order is the marginal order. -/
theorem not_atomRatioOrderSelectionClosed : ¬ AtomRatioOrderSelectionClosed := by
  intro hclosed
  refine atomMarginalFoil_top_fails
    (hclosed atomMarginalFoilAtom atomMarginalFoilScale atomMarginalFoilScale_pos
      atomMarginalFoilScale_sum atomMarginalFoilAtom_isTightFrame 0 1 2
      (by decide) (by decide) (by decide) (fun other hzero hone htwo => ?_) 21 0 (-20))
  obtain ⟨hleftZero, hleftOne, hleftTwo⟩ := atomMarginalFoil_marginal_top other hzero hone htwo
  have hsix : ∀ (value : ℝ) (slot : Fin 6), value / atomMarginalFoilScale slot = 6 * value := by
    intro value slot
    simp only [atomMarginalFoilScale]
    ring
  simp only [hsix]
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ## Layer 6 — the heavy criterion needs its scale term -/

/-- **THE HEAVY CRITERION IS SHARP.**  The three heaviest slots of the
foil carry a marginal total of exactly two, and they do NOT dominate.  The
scale term of `Gtz.atomTriple_values_of_heavy` is load-bearing. -/
theorem not_atomTriple_values_of_marginal_total_two :
    ¬ ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
        (∀ slot, 0 < scale slot) →
        (∑ slot, scale slot) = 1 →
        (∀ probe direction : Fin 3 → ℝ,
          (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
        ∀ slotOne slotTwo slotThree : Fin 6,
          slotOne ≠ slotTwo → slotOne ≠ slotThree → slotTwo ≠ slotThree →
          2 ≤ atomGram atom slotOne slotOne + atomGram atom slotTwo slotTwo
            + atomGram atom slotThree slotThree →
          ∀ valueOne valueTwo valueThree : ℝ,
            scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
                + scale slotThree * valueThree ^ 2
              ≤ atomGram atom slotOne slotOne * valueOne ^ 2
                + atomGram atom slotTwo slotTwo * valueTwo ^ 2
                + atomGram atom slotThree slotThree * valueThree ^ 2
                + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
                + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
                + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree := by
  intro hclosed
  exact atomMarginalFoil_top_fails
    (hclosed atomMarginalFoilAtom atomMarginalFoilScale atomMarginalFoilScale_pos
      atomMarginalFoilScale_sum atomMarginalFoilAtom_isTightFrame 0 1 2
      (by decide) (by decide) (by decide)
      (le_of_eq atomMarginalFoil_marginal_total.symm) 21 0 (-20))

end Gtz
