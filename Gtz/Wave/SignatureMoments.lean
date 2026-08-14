import Gtz.Wave.SignatureSelection
import Gtz.Wave.InterlacingSelection
import Gtz.Wave.PlanePairSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6400000

/-!
# The flat spectral average of the gap form is universal

Six tight frame atoms of rank three and six positive scales of mass `m`
give the GAP FORM `N = P - D`, the projection of the frame minus the
scale diagonal.  Every triple of slots carries a three by three block of
that form, and every block carries three symmetric functions: the shifted
trace, the pair minor total and the triple determinant.

This module computes the FLAT AVERAGE of all three over the two hundred
and sixteen ORDERED triples, and the answer is a shock: the average does
not see the datum at all.  It is a function of the mass and of nothing
else.

  `sum over ordered triples of the shifted trace   = 108 (3 - m)`
  `sum over ordered triples of the pair minor total = 18 ((3 - m)^2 - 3)`
  `sum over ordered triples of the triple determinant = (3 - m)^3 - 9 (3 - m) + 6`

Assembled into the characteristic polynomial of the block the three laws
give one identity.  Write `u = 3 - m` for the shifted trace of the whole
gap form.  Then for every argument

  `sum over ordered triples of the characteristic polynomial`
      `= 216 ((arg - u/6)^3 - (arg - u/6)/4 - 1/36)`.

**THE FLAT AVERAGE CHARACTERISTIC POLYNOMIAL IS THE UNIVERSAL DEPRESSED
CUBIC `s^3 - s/4 - 1/36`, CENTERED AT ONE SIXTH OF THE SHIFTED TRACE.**
Two data of the same mass have the same flat spectral average, whatever
their geometry.  The sharp extremal, which carries twelve tied triples
and no strict one, and a generic design, which carries several strict
ones, are indistinguishable to it.

## What the universality buys, and what it forbids

It FORBIDS every flat averaging certificate.  At mass one the flat total
of the triple determinants is exactly minus four, so the flat average of
the determinant is negative at EVERY datum.  No argument that averages
determinants with equal weights over ordered triples can ever produce a
nonnegative one.  This is the exact form of a fact the campaign had only
measured.

It BUYS two unconditional selections.

* THE FREE PAIR PIVOT.  At mass at most one the off diagonal pair minors
  add to `6 (1 - m) + 2 (scale weighted marginal total)`, which is
  strictly positive.  So SOME pair of distinct slots carries a strictly
  positive shifted pair minor, at every datum and with no hypothesis.
  That is the two by two pivot the pair lanes need, and it is now free.
* THE MASS THRESHOLD.  The flat determinant total is strictly increasing
  in `u` on the range that a mass below one allows, and it changes sign
  at `u^3 = 9 u - 6`.  At mass at most two fifths it is at least
  `22/125`, so SOME ordered triple carries a strictly positive shifted
  triple determinant.  Above that threshold the total is negative and the
  selection dies.  The mass at which the flat determinant average
  vanishes is `3 - u` with `u` the middle root of `u^3 - 9 u + 6`, which
  is near `0.4158`.

## The isolated slot splits the cell down to rank two

A slot whose marginal is exactly one carries a unit atom orthogonal to
every other atom.  The five remaining atoms are then a tight frame of the
plane it leaves, and their scale mass drops strictly below one.  The
LANDED rank two selection theorem applies there and supplies a dominating
pair, which together with the isolated slot is a dominating triple.

That is the first passage from the rank two lane into the rank three
cell.  It closes the isolated stratum of the residue outright, and it is
exactly the stratum where the light pair criterion of the four slot rung
dies: a heavy isolated slot makes every pair of the rung criterion too
expensive.

## The two trace laws that drive everything

The whole computation rests on two laws of the Gram of a tight frame.
The squares of all its entries add to the rank, which is landed, and the
cyclic cubes of its entries add to the rank as well, which is new here.
Both follow from idempotency and the trace law.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.orderedTriple_first`, `Gtz.orderedTriple_second`,
  `Gtz.orderedTriple_third`, `Gtz.orderedTriple_pairOneTwo`,
  `Gtz.orderedTriple_pairOneThree`, `Gtz.orderedTriple_pairTwoThree` —
  the reindexing of an ordered triple sum.
* `Gtz.atomGram_cube_total` — the cube trace law of the Gram of a tight
  frame, the companion of the landed square trace law.
* `Gtz.atomFlatPairTotal_eq`, `Gtz.atomFlatMomentOne_eq`,
  `Gtz.atomFlatMomentTwo_eq`, `Gtz.atomFlatMomentThree_eq` — **THE THREE
  FLAT MOMENTS ARE FUNCTIONS OF THE MASS ALONE**.
* `Gtz.atomFlatChar_eq` — **THE FLAT AVERAGE CHARACTERISTIC POLYNOMIAL IS
  THE UNIVERSAL DEPRESSED CUBIC**.
* `Gtz.atomFlatChar_eq_of_mass_eq` — two data of the same mass have the
  same flat spectral average.
* `Gtz.atomPairMinor_diagonal`, `Gtz.atomFlatOffPairTotal_eq`,
  `Gtz.scaleMarginal_pos`, `Gtz.atomFlatOffPairTotal_pos`,
  `Gtz.exists_distinct_pair_pos_minor` — **THE FREE PAIR PIVOT**.
* `Gtz.atomFlatMomentThree_pos_of_mass_le`,
  `Gtz.exists_orderedTriple_pos_det` — **THE MASS THRESHOLD**.
* `Gtz.atomFlatMomentThree_at_mass_one`,
  `Gtz.exists_orderedTriple_neg_det`,
  `Gtz.not_flatDeterminantAveraging` — **FLAT DETERMINANT AVERAGING IS
  DEAD AT MASS ONE**, as a theorem and not as a measurement.
* `Gtz.atomCross_triple_product`, `Gtz.planeLift`, `Gtz.planeCoord`,
  `Gtz.planeCoord_dot_pair`, `Gtz.planeLift_dot`, `Gtz.planeCoord_dot`,
  `Gtz.atomGram_off_isolated`, `Gtz.planePair_atom_ne_zero`,
  `Gtz.exists_weakCarrier_of_isolated_slot` — **THE ISOLATED SLOT SPLITS
  THE CELL DOWN TO RANK TWO**, and the landed plane selection theorem
  closes that stratum.

## Vacuity

Every law here is an unconditional identity of the frame calculus, and
the two selections carry only a mass hypothesis which the residue itself
supplies.  The refutation is a strict inequality at mass one, so it is
not vacuous.  The split carries one hypothesis, a marginal of exactly
one, and the icosahedral and tetrahedral witnesses of the campaign show
that marginals reach every value in the unit interval, so the split is
not vacuous either.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the reindexing of an ordered triple sum -/

section Reindex

theorem orderedTriple_first (value : Fin 6 → ℝ) :
    (∑ first : Fin 6, ∑ _second : Fin 6, ∑ _third : Fin 6, value first)
      = 36 * ∑ slot, value slot := by
  simp [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem orderedTriple_second (value : Fin 6 → ℝ) :
    (∑ _first : Fin 6, ∑ second : Fin 6, ∑ _third : Fin 6, value second)
      = 36 * ∑ slot, value slot := by
  simp [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem orderedTriple_third (value : Fin 6 → ℝ) :
    (∑ _first : Fin 6, ∑ _second : Fin 6, ∑ third : Fin 6, value third)
      = 36 * ∑ slot, value slot := by
  simp [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem orderedTriple_pairOneTwo (value : Fin 6 → Fin 6 → ℝ) :
    (∑ first : Fin 6, ∑ second : Fin 6, ∑ _third : Fin 6, value first second)
      = 6 * ∑ rowSlot, ∑ colSlot, value rowSlot colSlot := by
  simp [Finset.mul_sum]

theorem orderedTriple_pairOneThree (value : Fin 6 → Fin 6 → ℝ) :
    (∑ first : Fin 6, ∑ _second : Fin 6, ∑ third : Fin 6, value first third)
      = 6 * ∑ rowSlot, ∑ colSlot, value rowSlot colSlot := by
  simp [Finset.mul_sum]

theorem orderedTriple_pairTwoThree (value : Fin 6 → Fin 6 → ℝ) :
    (∑ _first : Fin 6, ∑ second : Fin 6, ∑ third : Fin 6, value second third)
      = 6 * ∑ rowSlot, ∑ colSlot, value rowSlot colSlot := by
  simp [Finset.mul_sum]

end Reindex

/-! ## Layer 1 — the two trace laws of the Gram of a tight frame -/

section TraceLaws

variable {slotCount rank : ℕ}

/-- **THE CUBE TRACE LAW.**  The cyclic cubes of the Gram entries of a
tight frame add to the rank.  The Gram is idempotent, so the cube trace
is the trace. -/
theorem atomGram_cube_total (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ rowSlot, ∑ midSlot, ∑ colSlot,
        atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot
          * atomGram atom colSlot rowSlot) = (rank : ℝ) := by
  classical
  have hswap : ∀ rowSlot : Fin slotCount,
      (∑ midSlot, ∑ colSlot, atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot
          * atomGram atom colSlot rowSlot)
        = ∑ colSlot, ∑ midSlot, atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot
          * atomGram atom colSlot rowSlot := fun rowSlot => Finset.sum_comm
  have hinner : ∀ rowSlot colSlot : Fin slotCount,
      (∑ midSlot, atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot
          * atomGram atom colSlot rowSlot)
        = atomGram atom rowSlot colSlot * atomGram atom colSlot rowSlot := by
    intro rowSlot colSlot
    rw [← Finset.sum_mul, atomGram_idempotent hframe rowSlot colSlot]
  have hrow : ∀ rowSlot : Fin slotCount,
      (∑ midSlot, ∑ colSlot, atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot
          * atomGram atom colSlot rowSlot)
        = ∑ colSlot, atomGram atom rowSlot colSlot ^ 2 := by
    intro rowSlot
    rw [hswap rowSlot, Finset.sum_congr rfl fun colSlot _ => hinner rowSlot colSlot]
    exact Finset.sum_congr rfl fun colSlot _ => by
      rw [atomGram_comm atom colSlot rowSlot]; ring
  rw [Finset.sum_congr rfl fun rowSlot _ => hrow rowSlot]
  exact atomGram_square_total hframe

end TraceLaws

/-! ## Layer 2 — the three flat moments -/

section FlatMoments

variable (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)

/-- **THE FLAT PAIR TOTAL.**  Over the thirty six ordered pairs the
shifted pair minors add to the square of the shifted trace minus the
rank. -/
theorem atomFlatPairTotal_eq
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ rowSlot, ∑ colSlot, atomPairMinor atom scale rowSlot colSlot)
      = (3 - ∑ slot, scale slot) ^ 2 - 3 := by
  classical
  have hcell : ∀ rowSlot colSlot : Fin 6,
      atomPairMinor atom scale rowSlot colSlot
        = atomShiftedDiag atom scale rowSlot * atomShiftedDiag atom scale colSlot
          - atomGram atom rowSlot colSlot ^ 2 := fun _ _ => rfl
  have hsplit : (∑ rowSlot, ∑ colSlot, atomPairMinor atom scale rowSlot colSlot)
      = (∑ rowSlot, ∑ colSlot, atomShiftedDiag atom scale rowSlot
            * atomShiftedDiag atom scale colSlot)
        - ∑ rowSlot, ∑ colSlot, atomGram atom rowSlot colSlot ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun rowSlot _ => by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun colSlot _ => hcell rowSlot colSlot
  have hproduct : (∑ rowSlot, ∑ colSlot, atomShiftedDiag atom scale rowSlot
        * atomShiftedDiag atom scale colSlot)
      = (∑ slot, atomShiftedDiag atom scale slot) ^ 2 := by
    rw [sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun rowSlot _ => (Finset.mul_sum _ _ _).symm
  rw [hsplit, hproduct, atomGram_square_total hframe,
    atomShiftedDiag_total hframe scale]
  norm_num

/-- **THE FIRST FLAT MOMENT.**  Over the ordered triples the shifted
traces add to `108` times the shifted trace of the whole gap form. -/
theorem atomFlatMomentOne_eq
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ first, ∑ second, ∑ third,
        (atomShiftedDiag atom scale first + atomShiftedDiag atom scale second
          + atomShiftedDiag atom scale third))
      = 108 * (3 - ∑ slot, scale slot) := by
  classical
  have hsplit : (∑ first, ∑ second, ∑ third,
        (atomShiftedDiag atom scale first + atomShiftedDiag atom scale second
          + atomShiftedDiag atom scale third))
      = (∑ first : Fin 6, ∑ _second : Fin 6, ∑ _third : Fin 6, atomShiftedDiag atom scale first)
        + (∑ _first : Fin 6, ∑ second : Fin 6, ∑ _third : Fin 6,
            atomShiftedDiag atom scale second)
        + ∑ _first : Fin 6, ∑ _second : Fin 6, ∑ third : Fin 6,
            atomShiftedDiag atom scale third := by
    simp only [Finset.sum_add_distrib]
  rw [hsplit, orderedTriple_first, orderedTriple_second, orderedTriple_third,
    atomShiftedDiag_total hframe scale]
  norm_num
  ring

/-- **THE SECOND FLAT MOMENT.**  Over the ordered triples the pair minor
totals add to `18` times the flat pair total. -/
theorem atomFlatMomentTwo_eq
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ first, ∑ second, ∑ third,
        (atomPairMinor atom scale first second + atomPairMinor atom scale first third
          + atomPairMinor atom scale second third))
      = 18 * ((3 - ∑ slot, scale slot) ^ 2 - 3) := by
  classical
  have hsplit : (∑ first, ∑ second, ∑ third,
        (atomPairMinor atom scale first second + atomPairMinor atom scale first third
          + atomPairMinor atom scale second third))
      = (∑ first : Fin 6, ∑ second : Fin 6, ∑ _third : Fin 6,
            atomPairMinor atom scale first second)
        + (∑ first : Fin 6, ∑ _second : Fin 6, ∑ third : Fin 6,
            atomPairMinor atom scale first third)
        + ∑ _first : Fin 6, ∑ second : Fin 6, ∑ third : Fin 6,
            atomPairMinor atom scale second third := by
    simp only [Finset.sum_add_distrib]
  rw [hsplit, orderedTriple_pairOneTwo, orderedTriple_pairOneThree,
    orderedTriple_pairTwoThree, atomFlatPairTotal_eq atom scale hframe]
  ring

/-- **THE THIRD FLAT MOMENT.**  Over the ordered triples the shifted
triple determinants add to a CUBIC IN THE MASS AND NOTHING ELSE.  The
three pieces are the cube of the shifted trace, twice the cube trace of
the Gram, and three copies of the shifted trace against the square trace
of the Gram. -/
theorem atomFlatMomentThree_eq
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ first, ∑ second, ∑ third, atomTripleDet atom scale first second third)
      = (3 - ∑ slot, scale slot) ^ 3 - 9 * (3 - ∑ slot, scale slot) + 6 := by
  classical
  set shift := fun slot => atomShiftedDiag atom scale slot with hshift
  set gram := fun rowSlot colSlot => atomGram atom rowSlot colSlot with hgram
  have hcell : ∀ first second third : Fin 6,
      atomTripleDet atom scale first second third
        = shift first * shift second * shift third
          + 2 * (gram first second * gram second third * gram third first)
          - shift first * gram second third ^ 2
          - shift second * gram first third ^ 2
          - shift third * gram first second ^ 2 := by
    intro first second third
    simp only [atomTripleDet, hshift, hgram, atomGram_comm atom third first]
    ring
  have hsplit : (∑ first, ∑ second, ∑ third, atomTripleDet atom scale first second third)
      = (∑ first, ∑ second, ∑ third, shift first * shift second * shift third)
        + (∑ first, ∑ second, ∑ third,
            2 * (gram first second * gram second third * gram third first))
        - (∑ first, ∑ second, ∑ third, shift first * gram second third ^ 2)
        - (∑ first, ∑ second, ∑ third, shift second * gram first third ^ 2)
        - ∑ first, ∑ second, ∑ third, shift third * gram first second ^ 2 := by
    rw [Finset.sum_congr rfl fun first _ => Finset.sum_congr rfl fun second _ =>
      Finset.sum_congr rfl fun third _ => hcell first second third]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hcube : (∑ first, ∑ second, ∑ third, shift first * shift second * shift third)
      = (∑ slot, shift slot) ^ 3 := by
    have hthree : ∀ first second : Fin 6,
        (∑ third, shift first * shift second * shift third)
          = shift first * shift second * ∑ slot, shift slot := fun _ _ =>
      (Finset.mul_sum _ _ _).symm
    have htwo : ∀ first : Fin 6,
        (∑ second, ∑ third, shift first * shift second * shift third)
          = shift first * (∑ slot, shift slot) * ∑ slot, shift slot := by
      intro first
      rw [Finset.sum_congr rfl fun second _ => hthree first second, ← Finset.sum_mul,
        ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun first _ => htwo first, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hcubeTrace : (∑ first, ∑ second, ∑ third,
      2 * (gram first second * gram second third * gram third first)) = 6 := by
    have hpull : ∀ first second : Fin 6,
        (∑ third, 2 * (gram first second * gram second third * gram third first))
          = 2 * ∑ third, gram first second * gram second third * gram third first :=
      fun _ _ => (Finset.mul_sum _ _ _).symm
    have hmid : ∀ first : Fin 6,
        (∑ second, ∑ third, 2 * (gram first second * gram second third * gram third first))
          = 2 * ∑ second, ∑ third,
              gram first second * gram second third * gram third first := by
      intro first
      rw [Finset.sum_congr rfl fun second _ => hpull first second, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun first _ => hmid first, ← Finset.mul_sum,
      atomGram_cube_total atom hframe]
    norm_num
  have hmixed : ∀ pick : Fin 6 → Fin 6 → Fin 6 → ℝ,
      (∀ first second third : Fin 6, pick first second third
        = shift first * gram second third ^ 2)
      → (∑ first, ∑ second, ∑ third, pick first second third)
        = (∑ slot, shift slot) * 3 := by
    intro pick hpick
    have hinner : ∀ first : Fin 6,
        (∑ second, ∑ third, pick first second third)
          = shift first * ∑ second, ∑ third, gram second third ^ 2 := by
      intro first
      rw [Finset.sum_congr rfl fun second _ => Finset.sum_congr rfl fun third _ =>
        hpick first second third]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun second _ => (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl fun first _ => hinner first, ← Finset.sum_mul,
      atomGram_square_total hframe]
    norm_num
  have hone := hmixed (fun first second third => shift first * gram second third ^ 2)
    (fun _ _ _ => rfl)
  have htwo : (∑ first, ∑ second, ∑ third, shift second * gram first third ^ 2)
      = (∑ slot, shift slot) * 3 := by
    have hswap : (∑ first, ∑ second, ∑ third, shift second * gram first third ^ 2)
        = ∑ second, ∑ first, ∑ third, shift second * gram first third ^ 2 := Finset.sum_comm
    rw [hswap]
    exact hmixed (fun first second third => shift first * gram second third ^ 2)
      (fun _ _ _ => rfl)
  have hthree : (∑ first, ∑ second, ∑ third, shift third * gram first second ^ 2)
      = (∑ slot, shift slot) * 3 := by
    have hinner : ∀ first : Fin 6,
        (∑ second, ∑ third, shift third * gram first second ^ 2)
          = ∑ third, ∑ second, shift third * gram first second ^ 2 :=
      fun _ => Finset.sum_comm
    have hswap : (∑ first, ∑ second, ∑ third, shift third * gram first second ^ 2)
        = ∑ first, ∑ third, ∑ second, shift third * gram first second ^ 2 :=
      Finset.sum_congr rfl fun first _ => hinner first
    have hswapTwo : (∑ first, ∑ third, ∑ second, shift third * gram first second ^ 2)
        = ∑ third, ∑ first, ∑ second, shift third * gram first second ^ 2 := Finset.sum_comm
    rw [hswap, hswapTwo]
    exact hmixed (fun first second third => shift first * gram second third ^ 2)
      (fun _ _ _ => rfl)
  rw [hsplit, hcube, hcubeTrace, hone, htwo, hthree, atomShiftedDiag_total hframe scale]
  norm_num
  ring

end FlatMoments

/-! ## Layer 3 — the universal characteristic average -/

section Universal

/-- **THE FLAT AVERAGE CHARACTERISTIC POLYNOMIAL IS UNIVERSAL.**  Over the
two hundred and sixteen ordered triples the characteristic polynomials of
the shifted Gram blocks add to a cubic that depends on the mass and on
nothing else.  Centered at one sixth of the shifted trace it is the
UNIVERSAL DEPRESSED CUBIC `s^3 - s/4 - 1/36`. -/
theorem atomFlatChar_eq (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (arg : ℝ) :
    (∑ first, ∑ second, ∑ third, atomTripleChar atom scale first second third arg)
      = 216 * ((arg - (3 - ∑ slot, scale slot) / 6) ^ 3
          - (arg - (3 - ∑ slot, scale slot) / 6) / 4 - 1 / 36) := by
  classical
  set mass := ∑ slot, scale slot with hmass
  have hsplit : (∑ first, ∑ second, ∑ third,
        atomTripleChar atom scale first second third arg)
      = (∑ _first : Fin 6, ∑ _second : Fin 6, ∑ _third : Fin 6, arg ^ 3)
        - (∑ first, ∑ second, ∑ third,
            (atomShiftedDiag atom scale first + atomShiftedDiag atom scale second
              + atomShiftedDiag atom scale third)) * arg ^ 2
        + (∑ first, ∑ second, ∑ third,
            (atomPairMinor atom scale first second + atomPairMinor atom scale first third
              + atomPairMinor atom scale second third)) * arg
        - ∑ first, ∑ second, ∑ third, atomTripleDet atom scale first second third := by
    simp only [atomTripleChar, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul]
  have hconst : (∑ _first : Fin 6, ∑ _second : Fin 6, ∑ _third : Fin 6, arg ^ 3)
      = 216 * arg ^ 3 := by
    simp
    ring
  rw [hsplit, hconst, atomFlatMomentOne_eq atom scale hframe,
    atomFlatMomentTwo_eq atom scale hframe, atomFlatMomentThree_eq atom scale hframe]
  ring

/-- **TWO DATA OF THE SAME MASS HAVE THE SAME FLAT SPECTRAL AVERAGE.**  The
geometry of the frame is invisible to the flat average, so no certificate
that reads only the flat average can separate one datum from another. -/
theorem atomFlatChar_eq_of_mass_eq (atomOne atomTwo : Fin 6 → (Fin 3 → ℝ))
    (scaleOne scaleTwo : Fin 6 → ℝ)
    (hframeOne : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atomOne slot ⬝ᵥ probe) * (atomOne slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hframeTwo : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atomTwo slot ⬝ᵥ probe) * (atomTwo slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hmass : (∑ slot, scaleOne slot) = ∑ slot, scaleTwo slot) (arg : ℝ) :
    (∑ first, ∑ second, ∑ third, atomTripleChar atomOne scaleOne first second third arg)
      = ∑ first, ∑ second, ∑ third,
          atomTripleChar atomTwo scaleTwo first second third arg := by
  rw [atomFlatChar_eq atomOne scaleOne hframeOne arg,
    atomFlatChar_eq atomTwo scaleTwo hframeTwo arg, hmass]

end Universal

/-! ## Layer 4 — the free pair pivot -/

section PairPivot

variable (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)

/-- The diagonal pair minor is the scale against the marginal. -/
theorem atomPairMinor_diagonal (slot : Fin 6) :
    atomPairMinor atom scale slot slot
      = scale slot ^ 2 - 2 * scale slot * atomGram atom slot slot := by
  simp only [atomPairMinor, atomShiftedDiag]
  ring

/-- **THE OFF DIAGONAL PAIR TOTAL.**  The flat pair total minus its
diagonal, in closed form. -/
theorem atomFlatOffPairTotal_eq
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ rowSlot, ∑ colSlot ∈ Finset.univ.erase rowSlot,
        atomPairMinor atom scale rowSlot colSlot)
      = (3 - ∑ slot, scale slot) ^ 2 - 3 - (∑ slot, scale slot ^ 2)
        + 2 * ∑ slot, scale slot * atomGram atom slot slot := by
  classical
  have herase : ∀ rowSlot : Fin 6,
      (∑ colSlot ∈ Finset.univ.erase rowSlot, atomPairMinor atom scale rowSlot colSlot)
        = (∑ colSlot, atomPairMinor atom scale rowSlot colSlot)
          - atomPairMinor atom scale rowSlot rowSlot := by
    intro rowSlot
    rw [eq_sub_iff_add_eq, Finset.sum_erase_add _ _ (Finset.mem_univ rowSlot)]
  rw [Finset.sum_congr rfl fun rowSlot _ => herase rowSlot, Finset.sum_sub_distrib,
    atomFlatPairTotal_eq atom scale hframe,
    Finset.sum_congr rfl fun slot _ => atomPairMinor_diagonal atom scale slot,
    Finset.sum_sub_distrib]
  have hcell : (∑ slot, 2 * scale slot * atomGram atom slot slot)
      = 2 * ∑ slot, scale slot * atomGram atom slot slot := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun slot _ => by ring
  rw [hcell]
  ring

/-- The scale weighted marginal total is strictly positive: the marginals
add to the rank, so one of them is positive. -/
theorem scaleMarginal_pos
    (hpos : ∀ slot, 0 < scale slot)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    0 < ∑ slot, scale slot * atomGram atom slot slot := by
  classical
  have htrace := atomGram_trace hframe
  have hterm : ∀ slot ∈ (Finset.univ : Finset (Fin 6)),
      0 ≤ scale slot * atomGram atom slot slot :=
    fun slot _ => mul_nonneg (hpos slot).le (atomGram_diag_nonneg atom slot)
  have hbig : ∃ slot, 0 < atomGram atom slot slot := by
    by_contra hall
    have hzero : ∀ slot ∈ (Finset.univ : Finset (Fin 6)), atomGram atom slot slot ≤ 0 :=
      fun slot _ => not_lt.mp (not_exists.mp hall slot)
    have := Finset.sum_le_sum hzero
    rw [htrace] at this
    norm_num at this
  obtain ⟨slot, hslot⟩ := hbig
  exact Finset.sum_pos' hterm ⟨slot, Finset.mem_univ slot, mul_pos (hpos slot) hslot⟩

/-- **THE OFF DIAGONAL PAIR TOTAL IS POSITIVE AT MASS AT MOST ONE.**  It
exceeds `6` times the mass deficit plus twice the scale weighted marginal
total. -/
theorem atomFlatOffPairTotal_pos
    (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) ≤ 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    0 < ∑ rowSlot, ∑ colSlot ∈ Finset.univ.erase rowSlot,
      atomPairMinor atom scale rowSlot colSlot := by
  classical
  have hclosed := atomFlatOffPairTotal_eq atom scale hframe
  have hmarginal := scaleMarginal_pos atom scale hpos hframe
  have hsquare : (∑ slot, scale slot ^ 2) ≤ (∑ slot, scale slot) ^ 2 := by
    have hexpand : (∑ slot, scale slot) ^ 2
        = ∑ rowSlot, ∑ colSlot, scale rowSlot * scale colSlot := by
      rw [sq, Finset.sum_mul]
      exact Finset.sum_congr rfl fun rowSlot _ => Finset.mul_sum _ _ _
    have hdiag : (∑ slot, scale slot ^ 2)
        = ∑ slot, scale slot * scale slot :=
      Finset.sum_congr rfl fun slot _ => sq (scale slot)
    rw [hexpand, hdiag]
    refine Finset.sum_le_sum fun rowSlot _ => ?_
    have hsingle : scale rowSlot * scale rowSlot
        ≤ ∑ colSlot, scale rowSlot * scale colSlot := by
      refine Finset.single_le_sum (f := fun colSlot => scale rowSlot * scale colSlot)
        (fun colSlot _ => mul_nonneg (hpos rowSlot).le (hpos colSlot).le)
        (Finset.mem_univ rowSlot)
    exact hsingle
  have hmasspos : 0 < ∑ slot, scale slot :=
    Finset.sum_pos (fun slot _ => hpos slot) ⟨0, Finset.mem_univ 0⟩
  rw [hclosed]
  nlinarith [hmarginal, hsquare, hmass, hmasspos]

/-- **THE FREE PAIR PIVOT.**  At mass at most one some pair of DISTINCT
slots carries a strictly positive shifted pair minor.  No hypothesis on
the geometry enters. -/
theorem exists_distinct_pair_pos_minor
    (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) ≤ 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ rowSlot colSlot : Fin 6, rowSlot ≠ colSlot
      ∧ 0 < atomPairMinor atom scale rowSlot colSlot := by
  classical
  have htotal := atomFlatOffPairTotal_pos atom scale hpos hmass hframe
  have houter : ∃ rowSlot ∈ (Finset.univ : Finset (Fin 6)),
      0 < ∑ colSlot ∈ Finset.univ.erase rowSlot, atomPairMinor atom scale rowSlot colSlot := by
    by_contra hall
    have hle : ∀ rowSlot ∈ (Finset.univ : Finset (Fin 6)),
        (∑ colSlot ∈ Finset.univ.erase rowSlot, atomPairMinor atom scale rowSlot colSlot)
          ≤ 0 := by
      intro rowSlot hrow
      by_contra hgt
      exact hall ⟨rowSlot, hrow, not_le.mp hgt⟩
    have := Finset.sum_le_sum hle
    simp only [Finset.sum_const, smul_zero] at this
    linarith
  obtain ⟨rowSlot, -, hrow⟩ := houter
  have hinner : ∃ colSlot ∈ Finset.univ.erase rowSlot,
      0 < atomPairMinor atom scale rowSlot colSlot := by
    by_contra hall
    have hle : ∀ colSlot ∈ Finset.univ.erase rowSlot,
        atomPairMinor atom scale rowSlot colSlot ≤ 0 := by
      intro colSlot hcol
      by_contra hgt
      exact hall ⟨colSlot, hcol, not_le.mp hgt⟩
    have := Finset.sum_le_sum hle
    simp only [Finset.sum_const, smul_zero] at this
    linarith
  obtain ⟨colSlot, hcol, hvalue⟩ := hinner
  exact ⟨rowSlot, colSlot, ((Finset.mem_erase.mp hcol).1).symm, hvalue⟩

end PairPivot

/-! ## Layer 5 — the mass threshold and the death of flat averaging -/

section Threshold

variable (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)

/-- **THE THIRD FLAT MOMENT IS POSITIVE BELOW MASS TWO FIFTHS.**  The
cubic `u^3 - 9 u + 6` is strictly increasing past the square root of
three, and at `u = 13/5` it already reads `22/125`. -/
theorem atomFlatMomentThree_pos_of_mass_le
    (hposMass : 0 ≤ ∑ slot, scale slot) (hmass : (∑ slot, scale slot) ≤ 2 / 5)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    0 < ∑ first, ∑ second, ∑ third, atomTripleDet atom scale first second third := by
  rw [atomFlatMomentThree_eq atom scale hframe]
  set mass := ∑ slot, scale slot with hmassDef
  have hlow : (13 : ℝ) / 5 ≤ 3 - mass := by linarith
  have hhigh : 3 - mass ≤ 3 := by linarith
  nlinarith [hlow, hhigh, sq_nonneg (3 - mass - 13 / 5), sq_nonneg (3 - mass)]

/-- **SOME ORDERED TRIPLE CARRIES A POSITIVE SHIFTED DETERMINANT BELOW MASS
TWO FIFTHS.** -/
theorem exists_orderedTriple_pos_det
    (hposMass : 0 ≤ ∑ slot, scale slot) (hmass : (∑ slot, scale slot) ≤ 2 / 5)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ first second third : Fin 6, 0 < atomTripleDet atom scale first second third := by
  classical
  have htotal := atomFlatMomentThree_pos_of_mass_le atom scale hposMass hmass hframe
  by_contra hall
  have hle : ∀ first second third : Fin 6,
      atomTripleDet atom scale first second third ≤ 0 := by
    intro first second third
    by_contra hgt
    exact hall ⟨first, second, third, not_le.mp hgt⟩
  have hsum : (∑ first, ∑ second, ∑ third, atomTripleDet atom scale first second third) ≤ 0 := by
    refine Finset.sum_nonpos fun first _ => Finset.sum_nonpos fun second _ =>
      Finset.sum_nonpos fun third _ => hle first second third
  linarith

/-- **THE THIRD FLAT MOMENT AT MASS ONE IS MINUS FOUR.** -/
theorem atomFlatMomentThree_at_mass_one
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ first, ∑ second, ∑ third, atomTripleDet atom scale first second third) = -4 := by
  rw [atomFlatMomentThree_eq atom scale hframe, hmass]
  norm_num

/-- **SOME ORDERED TRIPLE CARRIES A NEGATIVE SHIFTED DETERMINANT AT MASS
ONE.** -/
theorem exists_orderedTriple_neg_det
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ first second third : Fin 6, atomTripleDet atom scale first second third < 0 := by
  classical
  have htotal := atomFlatMomentThree_at_mass_one atom scale hmass hframe
  by_contra hall
  have hge : ∀ first second third : Fin 6,
      0 ≤ atomTripleDet atom scale first second third := by
    intro first second third
    by_contra hlt
    exact hall ⟨first, second, third, not_le.mp hlt⟩
  have hsum : (0 : ℝ)
      ≤ ∑ first, ∑ second, ∑ third, atomTripleDet atom scale first second third :=
    Finset.sum_nonneg fun first _ => Finset.sum_nonneg fun second _ =>
      Finset.sum_nonneg fun third _ => hge first second third
  rw [htotal] at hsum
  norm_num at hsum

/-- **FLAT DETERMINANT AVERAGING IS DEAD AT MASS ONE.**  The flat total of
the shifted triple determinants is a strictly negative universal
constant, so no argument that reads only that total can ever produce a
nonnegative determinant.  The campaign had this as a measurement, and it
is now a theorem. -/
theorem not_flatDeterminantAveraging :
    ¬ ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
        (∀ slot, 0 < scale slot) →
        (∑ slot, scale slot) = 1 →
        (∀ probe direction : Fin 3 → ℝ,
          (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
        0 ≤ ∑ first, ∑ second, ∑ third, atomTripleDet atom scale first second third := by
  intro hall
  have hstep := hall atomBoundaryAtom atomBoundaryScale atomBoundaryScale_pos
    atomBoundaryScale_sum atomBoundaryAtom_isTightFrame
  rw [atomFlatMomentThree_at_mass_one atomBoundaryAtom atomBoundaryScale
    atomBoundaryScale_sum atomBoundaryAtom_isTightFrame] at hstep
  norm_num at hstep

end Threshold

/-! ## Layer 6 — the isolated slot splits the cell down to rank two -/

section Split

/-- **BINET-CAUCHY FOR TWO SCALAR TRIPLE PRODUCTS.**  Two triple products
that share two of their three vectors multiply to the determinant of the
mixed Gram of the two triples. -/
theorem atomCross_triple_product (leftVec rightVec pivotVec baseVec : Fin 3 → ℝ) :
    (leftVec ⬝ᵥ atomCross pivotVec baseVec) * (rightVec ⬝ᵥ atomCross pivotVec baseVec)
      = (leftVec ⬝ᵥ rightVec)
          * ((pivotVec ⬝ᵥ pivotVec) * (baseVec ⬝ᵥ baseVec) - (pivotVec ⬝ᵥ baseVec) ^ 2)
        - (leftVec ⬝ᵥ pivotVec)
          * ((pivotVec ⬝ᵥ rightVec) * (baseVec ⬝ᵥ baseVec)
            - (pivotVec ⬝ᵥ baseVec) * (baseVec ⬝ᵥ rightVec))
        + (leftVec ⬝ᵥ baseVec)
          * ((pivotVec ⬝ᵥ rightVec) * (pivotVec ⬝ᵥ baseVec)
            - (pivotVec ⬝ᵥ pivotVec) * (baseVec ⬝ᵥ rightVec)) := by
  simp only [dotProduct, Fin.sum_univ_three, atomCross_zero, atomCross_one, atomCross_two]
  ring

/-- The LIFT of a plane coordinate pair back to the ambient space, along
the orthogonal frame carried by the pivot and the base. -/
noncomputable def planeLift (pivotVec baseVec : Fin 3 → ℝ) (pair : Fin 2 → ℝ) : Fin 3 → ℝ :=
  fun index => (Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹
    * (pair 0 * baseVec index + pair 1 * atomCross pivotVec baseVec index)

/-- The PLANE COORDINATES of an ambient vector against that frame. -/
noncomputable def planeCoord (pivotVec baseVec direction : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![(Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹ * (direction ⬝ᵥ baseVec),
    (Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹ * (direction ⬝ᵥ atomCross pivotVec baseVec)]

/-- The plane reading of a vector is the ambient reading against the
lift. -/
theorem planeCoord_dot_pair (pivotVec baseVec direction : Fin 3 → ℝ) (pair : Fin 2 → ℝ) :
    planeCoord pivotVec baseVec direction ⬝ᵥ pair
      = direction ⬝ᵥ planeLift pivotVec baseVec pair := by
  simp only [planeCoord, planeLift, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **THE LIFT IS AN ISOMETRY.**  The pivot is a unit vector, the base is
orthogonal to it, and the cross product of the two closes the frame. -/
theorem planeLift_dot (pivotVec baseVec : Fin 3 → ℝ) (pairOne pairTwo : Fin 2 → ℝ)
    (hunit : pivotVec ⬝ᵥ pivotVec = 1) (horth : pivotVec ⬝ᵥ baseVec = 0)
    (hbase : 0 < baseVec ⬝ᵥ baseVec) :
    planeLift pivotVec baseVec pairOne ⬝ᵥ planeLift pivotVec baseVec pairTwo
      = pairOne ⬝ᵥ pairTwo := by
  have hcross : atomCross pivotVec baseVec ⬝ᵥ atomCross pivotVec baseVec
      = baseVec ⬝ᵥ baseVec := by
    rw [atomCross_self_dot, hunit, horth]
    ring
  have hmixed : baseVec ⬝ᵥ atomCross pivotVec baseVec = 0 := by
    rw [dotProduct_comm]
    exact atomCross_dot_right pivotVec baseVec
  have hne : Real.sqrt (baseVec ⬝ᵥ baseVec) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hbase)
  have hkey : (Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹ * (Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹
      * (baseVec ⬝ᵥ baseVec) = 1 := by
    have hmul := Real.mul_self_sqrt hbase.le
    field_simp
    linarith [hmul]
  have hexpand : planeLift pivotVec baseVec pairOne ⬝ᵥ planeLift pivotVec baseVec pairTwo
      = (Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹ * (Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹
        * (pairOne 0 * pairTwo 0 * (baseVec ⬝ᵥ baseVec)
            + (pairOne 0 * pairTwo 1 + pairOne 1 * pairTwo 0)
              * (baseVec ⬝ᵥ atomCross pivotVec baseVec)
            + pairOne 1 * pairTwo 1
              * (atomCross pivotVec baseVec ⬝ᵥ atomCross pivotVec baseVec)) := by
    simp only [planeLift, dotProduct, Fin.sum_univ_three]
    ring
  have hpair : pairOne ⬝ᵥ pairTwo = pairOne 0 * pairTwo 0 + pairOne 1 * pairTwo 1 := by
    simp only [dotProduct, Fin.sum_univ_two]
  rw [hexpand, hmixed, hcross, hpair]
  linear_combination (pairOne 0 * pairTwo 0 + pairOne 1 * pairTwo 1) * hkey

/-- **THE PLANE COORDINATES PRESERVE THE DOT PRODUCT.**  On the orthogonal
complement of the pivot the coordinate map is an isometry, by
Binet-Cauchy. -/
theorem planeCoord_dot (pivotVec baseVec leftVec rightVec : Fin 3 → ℝ)
    (hunit : pivotVec ⬝ᵥ pivotVec = 1) (horth : pivotVec ⬝ᵥ baseVec = 0)
    (hbase : 0 < baseVec ⬝ᵥ baseVec)
    (hleft : pivotVec ⬝ᵥ leftVec = 0) (hright : pivotVec ⬝ᵥ rightVec = 0) :
    planeCoord pivotVec baseVec leftVec ⬝ᵥ planeCoord pivotVec baseVec rightVec
      = leftVec ⬝ᵥ rightVec := by
  have hbinet := atomCross_triple_product leftVec rightVec pivotVec baseVec
  have hleftSymm : leftVec ⬝ᵥ pivotVec = 0 := by rw [dotProduct_comm]; exact hleft
  rw [hunit, horth, hleftSymm, hright] at hbinet
  have hbaseright : baseVec ⬝ᵥ rightVec = rightVec ⬝ᵥ baseVec := dotProduct_comm _ _
  rw [hbaseright] at hbinet
  have hne : Real.sqrt (baseVec ⬝ᵥ baseVec) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hbase)
  have hkey : (Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹ * (Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹
      * (baseVec ⬝ᵥ baseVec) = 1 := by
    have hmul := Real.mul_self_sqrt hbase.le
    field_simp
    linarith [hmul]
  have hexpand : planeCoord pivotVec baseVec leftVec ⬝ᵥ planeCoord pivotVec baseVec rightVec
      = (Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹ * (Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹
        * ((leftVec ⬝ᵥ baseVec) * (rightVec ⬝ᵥ baseVec)
          + (leftVec ⬝ᵥ atomCross pivotVec baseVec)
            * (rightVec ⬝ᵥ atomCross pivotVec baseVec)) := by
    simp only [planeCoord, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  rw [hexpand, hbinet]
  linear_combination (leftVec ⬝ᵥ rightVec) * hkey

/-- **AN ISOLATED SLOT IS ORTHOGONAL TO EVERY OTHER SLOT.**  A marginal of
one saturates the row energy law. -/
theorem atomGram_off_isolated {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {pivot : Fin 6} (hone : atomGram atom pivot pivot = 1) {other : Fin 6}
    (hne : other ≠ pivot) : atomGram atom pivot other = 0 := by
  classical
  have hrow := atomGram_row_energy hframe pivot
  have hsplit : (∑ colSlot, atomGram atom pivot colSlot ^ 2)
      = atomGram atom pivot pivot ^ 2
        + ∑ colSlot ∈ Finset.univ.erase pivot, atomGram atom pivot colSlot ^ 2 :=
    (Finset.add_sum_erase _ (fun colSlot => atomGram atom pivot colSlot ^ 2)
      (Finset.mem_univ pivot)).symm
  rw [hsplit, hone] at hrow
  have hzero : (∑ colSlot ∈ Finset.univ.erase pivot, atomGram atom pivot colSlot ^ 2) = 0 := by
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun colSlot _ => sq_nonneg (atomGram atom pivot colSlot))).mp hzero
  have hmem : other ∈ Finset.univ.erase pivot :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ other⟩
  exact sq_eq_zero_iff.mp (hterm other hmem)

/-- A plane pair that dominates never carries a vanishing atom. -/
theorem planePair_atom_ne_zero {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (honePos : 0 < scaleOne) (htwoPos : 0 < scaleTwo)
    (hdom : PlanePairDominates atomOne atomTwo scaleOne scaleTwo) : atomOne ≠ 0 := by
  intro hzero
  have hkill : ∀ probe : Fin 2 → ℝ,
      scaleOne * scaleTwo * (probe ⬝ᵥ probe) ≤ scaleOne * (atomTwo ⬝ᵥ probe) ^ 2 := by
    intro probe
    have hstep := hdom probe
    have hone : atomOne ⬝ᵥ probe = 0 := by
      rw [hzero]
      simp
    rw [hone] at hstep
    simpa using hstep
  have hperp := hkill ![-(atomTwo 1), atomTwo 0]
  have hdotZero : atomTwo ⬝ᵥ ![-(atomTwo 1), atomTwo 0] = 0 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hnorm : (![-(atomTwo 1), atomTwo 0] : Fin 2 → ℝ) ⬝ᵥ ![-(atomTwo 1), atomTwo 0]
      = atomTwo 0 ^ 2 + atomTwo 1 ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hdotZero, hnorm] at hperp
  have hsq : atomTwo 0 ^ 2 + atomTwo 1 ^ 2 ≤ 0 := by
    by_contra hgt
    have hposSum : 0 < atomTwo 0 ^ 2 + atomTwo 1 ^ 2 := not_le.mp hgt
    have hprod := mul_pos (mul_pos honePos htwoPos) hposSum
    nlinarith [hperp, hprod]
  have hzeroTwo : atomTwo 0 = 0 ∧ atomTwo 1 = 0 := by
    constructor
    · exact sq_eq_zero_iff.mp
        (le_antisymm (by nlinarith [sq_nonneg (atomTwo 1), hsq]) (sq_nonneg _))
    · exact sq_eq_zero_iff.mp
        (le_antisymm (by nlinarith [sq_nonneg (atomTwo 0), hsq]) (sq_nonneg _))
  have hunit := hkill ![1, 0]
  have hdotUnit : atomTwo ⬝ᵥ (![1, 0] : Fin 2 → ℝ) = 0 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      hzeroTwo.1]
    ring
  have hnormUnit : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 1 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hdotUnit, hnormUnit] at hunit
  nlinarith [hunit, honePos, htwoPos]

/-- **THE ISOLATED SLOT SPLITS THE CELL DOWN TO RANK TWO.**  When one slot
carries a marginal of exactly one, its atom is a unit vector orthogonal to
every other atom.  The remaining five atoms are a tight frame of the plane
it leaves, their scale mass drops strictly below one, and the LANDED rank
two selection theorem supplies a dominating pair there.  That pair
together with the isolated slot is a dominating triple.

This is the first passage from the rank two lane into the rank three cell,
and it closes the isolated stratum of the residue outright. -/
theorem exists_weakCarrier_of_isolated_slot (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {pivot : Fin 6} (hone : atomGram atom pivot pivot = 1) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  have hunit : atom pivot ⬝ᵥ atom pivot = 1 := hone
  have hoff : ∀ other : Fin 6, other ≠ pivot → atom pivot ⬝ᵥ atom other = 0 :=
    fun other hne => atomGram_off_isolated hframe hone hne
  have hbaseExists : ∃ base : Fin 6, base ≠ pivot ∧ 0 < atom base ⬝ᵥ atom base := by
    by_contra hall
    have hzero : ∀ other : Fin 6, other ≠ pivot → atomGram atom other other ≤ 0 := by
      intro other hne
      by_contra hgt
      exact hall ⟨other, hne, not_le.mp hgt⟩
    have htrace := atomGram_trace hframe
    have hsplit : (∑ slot, atomGram atom slot slot)
        = atomGram atom pivot pivot
          + ∑ slot ∈ Finset.univ.erase pivot, atomGram atom slot slot :=
      (Finset.add_sum_erase _ (fun slot => atomGram atom slot slot)
        (Finset.mem_univ pivot)).symm
    have hrest : (∑ slot ∈ Finset.univ.erase pivot, atomGram atom slot slot) ≤ 0 :=
      Finset.sum_nonpos fun slot hslot => hzero slot (Finset.mem_erase.mp hslot).1
    rw [hsplit, hone] at htrace
    norm_num at htrace
    linarith
  obtain ⟨base, hbaseNe, hbasePos⟩ := hbaseExists
  have hbaseOrth : atom pivot ⬝ᵥ atom base = 0 := hoff base hbaseNe
  set planeAtom : Fin 6 → (Fin 2 → ℝ) :=
    fun slot => planeCoord (atom pivot) (atom base) (atom slot) with hplaneAtom
  have hplaneGram : ∀ rowSlot colSlot : Fin 6, rowSlot ≠ pivot → colSlot ≠ pivot →
      planeAtom rowSlot ⬝ᵥ planeAtom colSlot = atom rowSlot ⬝ᵥ atom colSlot :=
    fun rowSlot colSlot hrow hcol =>
      planeCoord_dot (atom pivot) (atom base) (atom rowSlot) (atom colSlot) hunit hbaseOrth
        hbasePos (hoff rowSlot hrow) (hoff colSlot hcol)
  have hplaneFrame : PlaneParseval planeAtom := by
    intro probe other
    have hcell : ∀ slot : Fin 6,
        (planeAtom slot ⬝ᵥ probe) * (planeAtom slot ⬝ᵥ other)
          = (atom slot ⬝ᵥ planeLift (atom pivot) (atom base) probe)
            * (atom slot ⬝ᵥ planeLift (atom pivot) (atom base) other) := by
      intro slot
      rw [hplaneAtom, planeCoord_dot_pair, planeCoord_dot_pair]
    rw [Finset.sum_congr rfl fun slot _ => hcell slot,
      hframe (planeLift (atom pivot) (atom base) probe)
        (planeLift (atom pivot) (atom base) other),
      planeLift_dot (atom pivot) (atom base) probe other hunit hbaseOrth hbasePos]
  obtain ⟨planeScale, hplanePivot, hplaneOther⟩ :
      ∃ weight : Fin 6 → ℝ, weight pivot = scale pivot / 2
        ∧ ∀ slot, slot ≠ pivot → weight slot = scale slot :=
    ⟨fun slot => if slot = pivot then scale pivot / 2 else scale slot, by simp,
      fun slot hslot => by simp [hslot]⟩
  have hplanePos : ∀ slot, 0 < planeScale slot := by
    intro slot
    by_cases heq : slot = pivot
    · rw [heq, hplanePivot]
      linarith [hpos pivot]
    · rw [hplaneOther slot heq]
      exact hpos slot
  have hplaneMass : (∑ slot, planeScale slot) < 1 := by
    have hsplit : (∑ slot, planeScale slot)
        = planeScale pivot + ∑ slot ∈ Finset.univ.erase pivot, planeScale slot :=
      (Finset.add_sum_erase _ planeScale (Finset.mem_univ pivot)).symm
    have hsplitScale : (∑ slot, scale slot)
        = scale pivot + ∑ slot ∈ Finset.univ.erase pivot, scale slot :=
      (Finset.add_sum_erase _ scale (Finset.mem_univ pivot)).symm
    have hrest : (∑ slot ∈ Finset.univ.erase pivot, planeScale slot)
        = ∑ slot ∈ Finset.univ.erase pivot, scale slot :=
      Finset.sum_congr rfl fun slot hslot =>
        hplaneOther slot (Finset.mem_erase.mp hslot).1
    rw [hsplitScale] at hmass
    rw [hsplit, hrest, hplanePivot]
    linarith [hpos pivot]
  obtain ⟨slotOne, slotTwo, hne, hdom⟩ :=
    exists_dominatingPlanePair (by norm_num : (3 : ℕ) ≤ 6) planeAtom planeScale hplaneFrame
      hplanePos hplaneMass
  have hpivotZero : planeAtom pivot = 0 := by
    funext index
    have hcrossZero : atom pivot ⬝ᵥ atomCross (atom pivot) (atom base) = 0 := by
      rw [dotProduct_comm]
      exact atomCross_dot_left (atom pivot) (atom base)
    fin_cases index <;>
      simp [hplaneAtom, planeCoord, hbaseOrth, hcrossZero]
  have honeNe : slotOne ≠ pivot := by
    intro heq
    exact planePair_atom_ne_zero (hplanePos slotOne) (hplanePos slotTwo) hdom
      (by rw [heq]; exact hpivotZero)
  have htwoNe : slotTwo ≠ pivot := by
    intro heq
    exact planePair_atom_ne_zero (hplanePos slotTwo) (hplanePos slotOne) hdom.symm
      (by rw [heq]; exact hpivotZero)
  have hscaleOne : planeScale slotOne = scale slotOne := hplaneOther slotOne honeNe
  have hscaleTwo : planeScale slotTwo = scale slotTwo := hplaneOther slotTwo htwoNe
  rw [hscaleOne, hscaleTwo] at hdom
  obtain ⟨htrace, hminor⟩ :=
    (planePairDominates_iff (hpos slotOne) (hpos slotTwo)).mp hdom
  rw [hplaneGram slotOne slotOne honeNe honeNe, hplaneGram slotTwo slotTwo htwoNe htwoNe]
    at htrace
  rw [hplaneGram slotOne slotTwo honeNe htwoNe, hplaneGram slotOne slotOne honeNe honeNe,
    hplaneGram slotTwo slotTwo htwoNe htwoNe] at hminor
  have hprodNonneg : 0 ≤ (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
      * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) :=
    le_trans (sq_nonneg (atom slotOne ⬝ᵥ atom slotTwo)) hminor
  have hshiftOne : 0 ≤ atom slotOne ⬝ᵥ atom slotOne - scale slotOne := by
    by_contra hlt
    have hneg : atom slotOne ⬝ᵥ atom slotOne - scale slotOne < 0 := not_le.mp hlt
    have hnegTwo : atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo ≤ 0 := by
      by_contra hgt
      have hposTwo : 0 < atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo := not_le.mp hgt
      nlinarith [hprodNonneg, mul_pos (neg_pos.mpr hneg) hposTwo]
    nlinarith [htrace, mul_pos (hpos slotTwo) (neg_pos.mpr hneg),
      mul_nonneg (hpos slotOne).le (neg_nonneg.mpr hnegTwo)]
  have hshiftTwo : 0 ≤ atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo := by
    by_contra hlt
    have hneg : atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo < 0 := not_le.mp hlt
    have hnegOne : atom slotOne ⬝ᵥ atom slotOne - scale slotOne ≤ 0 := by
      by_contra hgt
      have hposOne : 0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne := not_le.mp hgt
      nlinarith [hprodNonneg, mul_pos hposOne (neg_pos.mpr hneg)]
    nlinarith [htrace, mul_pos (hpos slotOne) (neg_pos.mpr hneg),
      mul_nonneg (hpos slotTwo).le (neg_nonneg.mpr hnegOne)]
  have hpivotLt : scale pivot < 1 := by
    have hsplit : (∑ slot, scale slot)
        = scale pivot + ∑ slot ∈ Finset.univ.erase pivot, scale slot :=
      (Finset.add_sum_erase _ scale (Finset.mem_univ pivot)).symm
    have hrestPos : 0 < ∑ slot ∈ Finset.univ.erase pivot, scale slot := by
      refine Finset.sum_pos (fun slot _ => hpos slot) ⟨slotOne, ?_⟩
      exact Finset.mem_erase.mpr ⟨honeNe, Finset.mem_univ slotOne⟩
    rw [hsplit] at hmass
    linarith
  refine exists_weakCarrier_of_values (Ne.symm honeNe) (Ne.symm htwoNe) hne ?_
  intro valueOne valueTwo valueThree
  have hgramPivot : atom pivot ⬝ᵥ atom pivot = 1 := hunit
  have hgramOne : atom pivot ⬝ᵥ atom slotOne = 0 := hoff slotOne honeNe
  have hgramTwo : atom pivot ⬝ᵥ atom slotTwo = 0 := hoff slotTwo htwoNe
  have hplaneForm : scale slotOne * valueTwo ^ 2 + scale slotTwo * valueThree ^ 2
      ≤ (atom slotOne ⬝ᵥ atom slotOne) * valueTwo ^ 2
        + (atom slotTwo ⬝ᵥ atom slotTwo) * valueThree ^ 2
        + 2 * (atom slotOne ⬝ᵥ atom slotTwo) * valueTwo * valueThree := by
    rcases eq_or_lt_of_le hshiftOne with hzero | hposOne
    · have hsqZero : (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 = 0 := by
        refine le_antisymm ?_ (sq_nonneg _)
        rw [← hzero] at hminor
        simpa using hminor
      have hcross : atom slotOne ⬝ᵥ atom slotTwo = 0 := sq_eq_zero_iff.mp hsqZero
      rw [hcross]
      nlinarith [hshiftTwo, hzero, sq_nonneg valueTwo, sq_nonneg valueThree]
    · nlinarith [hminor, hposOne, hshiftTwo,
        sq_nonneg ((atom slotOne ⬝ᵥ atom slotOne - scale slotOne) * valueTwo
          + (atom slotOne ⬝ᵥ atom slotTwo) * valueThree),
        mul_nonneg (sub_nonneg.mpr hminor) (sq_nonneg valueThree)]
  simp only [atomGram]
  rw [hgramPivot, hgramOne, hgramTwo]
  nlinarith [hplaneForm, hpivotLt, sq_nonneg valueOne,
    mul_le_mul_of_nonneg_right hpivotLt.le (sq_nonneg valueOne)]

end Split

end Gtz
