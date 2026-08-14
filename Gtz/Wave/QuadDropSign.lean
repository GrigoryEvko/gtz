import Gtz.Wave.QuadCoverSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The two term drop dichotomy is false, and the four term one repairs it

The `(6,3)` cell was factored into the four slot rung and the drop of one
slot.  The rung is a theorem.  The drop was reduced to the SIGN DICHOTOMY
`Gtz.AtomQuadDropSignClosed`: some pair with a positive dual block has four
erasure determinants whose first symmetric function is nonnegative, or whose
second symmetric function is nonpositive.

**That statement is FALSE.**  This module refutes it at an exact rational
tight frame with six atoms of entries in `0`, `1/2` and `-(1/2)`, at the
uniform scale one sixth, and it repairs the factorization.

## The witness

The six atoms are the six half sums of two of the three axes:

  `(1/2, 1/2, 0)`, `(1/2, -(1/2), 0)`, `(1/2, 0, 1/2)`,
  `(1/2, 0, -(1/2))`, `(0, 1/2, 1/2)`, `(0, 1/2, -(1/2))`.

They resolve the identity exactly, and the uniform scale one sixth has mass
one.  The gap form is five times the identity, so the dual Gram is the frame
Gram over five.  Every diagonal shift reads `1/15` and every dual pair block
is positive, so all fifteen pairs pass the two cheap conditions of the
criterion.  The twenty erasure determinants read only three values:

  `-(49/108000)` at four triples,
  `-(1/27000)` at twelve triples,
  `1/21600` at four triples.

At the three ORTHOGONAL pairs all four erasures are negative.  At the twelve
remaining pairs the four erasures are three negative values and one small
positive value, which is exactly the shape that defeats a two term sign
test: the first symmetric function stays negative because the positive
erasure is small, and the second symmetric function stays positive because
three of the four values are negative.  The margins are exact:

  first symmetric function `-(1/1350)` or `-(13/5400)`, both negative,
  second symmetric function `1/2430000` or `41/77760000`, both positive.

## The repair

Four reals are all negative exactly when the four symmetric functions
alternate in sign.  A two term test therefore cannot decide the sign
question, and the four term test can.  `Gtz.AtomQuadDropFourSignClosed`
adds the third and the fourth arms, `Gtz.atomVertexCoverClosed_of_dropFourSign`
carries the residue, and `Gtz.gtzWeighted_six_three_of_dropFourSign` carries
the cell.  `Gtz.quadFourSign_iff` shows that the four term test is EXACTLY
the sign question and no stronger, so the repair is tight and no fifth arm
exists.

At the witness the four term test fires at the twelve non orthogonal pairs
through the third and the fourth arms, and it fails at the three orthogonal
pairs.  The witness therefore separates the two term test from the four term
test, and it does not refute the cell: the triple of slots zero, two and
five is a nonnegative dual block, so the complementary triple covers.

## The pivot passage

The cell has a second face in the chart of one pivot slot.  Read a direction
as a multiple of the pivot atom plus a POLAR part, which is a probe that the
pivot atom reads as zero.  Against a polar probe the five other atoms resolve
the probe exactly, by the frame law alone, so the plane of the pivot carries a
free Parseval frame of five slots at scale total `1 - t_p`.  A triple through
the pivot covers exactly when, at every polar probe, the plane reading of the
pair beats the probe energy by the SCHUR MARGIN of the coupling.

`Gtz.atomPivotSchur_cover` is that passage.  It is pure algebra and it
consumes no frame law.  The isotropic relaxation, which bounds the coupling
square by the Cauchy-Schwarz product of the pivot weight and the plane
reading, is REFUTED at a margin of `-0.129`, so the DIRECTION of the coupling
is load bearing.

## The cycle law of the Gram

The realness of the field enters the drop through ONE quantity, the SIGNED
TRIANGLE PRODUCT `G_yz G_zw G_wy`.  Every other ingredient of an erasure
determinant is a principal minor, and a principal minor reads the same over
the real field and over the Hermitian field.  This module lands the exact
law that the triangle products obey:

  `sum over slots off the pair of (G_yz G_zw G_wy) = G_yw ^ 2 (1 - G_yy - G_ww)`.

Over the real field each term is the full product of three moduli with one
sign, so a positive total forces an EVEN triangle through the pair.  Over
the Hermitian field each term is a real part, and every real part can vanish
while the moduli stay large.  `Gtz.exists_pos_cycle_of_pair` is that
consequence.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.quadComplSum`, `Gtz.quadPairSum` — the complement sum of a pair and
  the doubled second symmetric function.
* `Gtz.quadFourSign_iff` — **THE FOUR TERM SIGN TEST IS EXACTLY THE SIGN
  QUESTION**, on four reals, in both directions.
* `Gtz.exists_nonneg_of_fourSigns` — the four term pigeonhole on a support
  of four slots or more.
* `Gtz.AtomQuadDropFourSignClosed`, `Gtz.atomVertexCoverClosed_of_dropFourSign`,
  `Gtz.gtzWeighted_six_three_of_dropFourSign`,
  `Gtz.atomQuadDropFourSignClosed_of_dropSign` — **THE REPAIRED
  FACTORIZATION**, and it is weaker than the refuted one.
* `Gtz.dropWitnessAtom`, `Gtz.dropWitnessScale`, `Gtz.dropWitnessScale_pos`,
  `Gtz.dropWitnessScale_sum`, `Gtz.dropWitnessAtom_isTightFrame`,
  `Gtz.dropWitnessGapCoef`, `Gtz.dropWitnessGapRow_zero` thru
  `Gtz.dropWitnessGapRow_two`, `Gtz.dropWitnessGapDet`,
  `Gtz.dropWitnessDualVec`, `Gtz.dropWitnessDualGram` — the witness and its
  dual Gram, in closed form.
* `Gtz.dropWitness_pair_fails` — **EVERY ORDERED PAIR FAILS BOTH ARMS.**
* `Gtz.not_atomQuadDropSignClosed`, `Gtz.not_atomQuadDropScalarClosed` —
  **THE REFUTATION**, for the sign criterion and for the scalar criterion
  above it.
* `Gtz.dropWitness_dualTripleDet_pos`, `Gtz.dropWitnessAtom_hasVertexCover` —
  the witness carries a covering triple, so it refutes the criterion and not
  the cell.
* `Gtz.atomGram_cycle_total`, `Gtz.atomGram_cycle_erase`,
  `Gtz.exists_pos_cycle_of_pair` — **THE CYCLE LAW**, the carrier of the
  field.
* `Gtz.atomPivotPlaneRead`, `Gtz.atomPivotCouple`, `Gtz.atomPivotWeight`,
  `Gtz.atomPivotPolar_parseval`, `Gtz.atomPivotSchur_cover` — **THE PIVOT
  PASSAGE**, in ambient coordinates.  A pivot and a pair whose plane reading
  beats the probe energy by the exact Schur margin give a covering triple, and
  the five atoms off the pivot resolve every polar probe for free.

## Vacuity

The refutation is an exact rational computation at one named configuration.
The repaired criterion is inhabited, because it is implied by the residue
through the sign question, and `Gtz.quadFourSign_iff` proves that the
implication is an equivalence on the four values.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the sign algebra of four reals -/

section SignAlgebra

/-- **THE COMPLEMENT SUM OF A PAIR.**  A sum over the four slots off a pair
is the total less the two slots of the pair. -/
theorem quadComplSum (weight : Fin 6 → ℝ) {slotOne slotTwo : Fin 6}
    (hne : slotOne ≠ slotTwo) :
    (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ, weight slot)
      = (∑ slot, weight slot) - weight slotOne - weight slotTwo := by
  classical
  have hstep := Finset.sum_add_sum_compl ({slotOne, slotTwo} : Finset (Fin 6)) weight
  rw [Finset.sum_pair hne] at hstep
  linarith

/-- **THE DOUBLED SECOND SYMMETRIC FUNCTION.**  The ordered double sum off
the diagonal is the square of the total less the total of the squares. -/
theorem quadPairSum {support : Finset (Fin 6)} (value : Fin 6 → ℝ) :
    (∑ slot ∈ support, ∑ other ∈ support.erase slot, value slot * value other)
      = (∑ slot ∈ support, value slot) ^ 2 - ∑ slot ∈ support, value slot ^ 2 := by
  classical
  have hcell : ∀ slot ∈ support,
      (∑ other ∈ support.erase slot, value slot * value other)
        = value slot * (∑ other ∈ support, value other) - value slot ^ 2 := by
    intro slot hslot
    have hsplit := Finset.add_sum_erase support value hslot
    rw [← Finset.mul_sum, ← hsplit]
    ring
  rw [Finset.sum_congr rfl hcell, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- **THE FOUR TERM SIGN TEST IS EXACTLY THE SIGN QUESTION.**  Four reals
carry a nonnegative member exactly when one of the four symmetric functions
breaks the alternation of a family of four negative numbers.  The forward
direction is the pigeonhole and the reverse direction is one evaluation of
the monic quartic with those four roots. -/
theorem quadFourSign_iff (first second third fourth : ℝ) :
    (0 ≤ first ∨ 0 ≤ second ∨ 0 ≤ third ∨ 0 ≤ fourth)
      ↔ (0 ≤ first + second + third + fourth
          ∨ first * second + first * third + first * fourth + second * third
              + second * fourth + third * fourth ≤ 0
          ∨ 0 ≤ first * second * third + first * second * fourth
              + first * third * fourth + second * third * fourth
          ∨ first * second * third * fourth ≤ 0) := by
  constructor
  · rintro hsome
    by_contra hcon
    obtain ⟨hone, hrestOne⟩ := not_or.mp hcon
    obtain ⟨htwo, hrestTwo⟩ := not_or.mp hrestOne
    obtain ⟨hthree, hfour⟩ := not_or.mp hrestTwo
    rw [not_le] at hone htwo hthree hfour
    have hkey : ∀ value : ℝ, 0 ≤ value →
        value = first ∨ value = second ∨ value = third ∨ value = fourth → False := by
      intro value hval hmem
      have hroot : (value - first) * (value - second) * (value - third)
          * (value - fourth) = 0 := by
        rcases hmem with h | h | h | h <;> rw [h] <;> ring
      have hexpand : (value - first) * (value - second) * (value - third)
          * (value - fourth)
          = value ^ 4 - (first + second + third + fourth) * value ^ 3
            + (first * second + first * third + first * fourth + second * third
                + second * fourth + third * fourth) * value ^ 2
            - (first * second * third + first * second * fourth
                + first * third * fourth + second * third * fourth) * value
            + first * second * third * fourth := by ring
      rw [hexpand] at hroot
      nlinarith [pow_nonneg hval 2, pow_nonneg hval 3, pow_nonneg hval 4, hval,
        mul_nonneg (le_of_lt (by linarith : (0:ℝ) < -(first + second + third + fourth)))
          (pow_nonneg hval 3),
        mul_nonneg (le_of_lt htwo) (pow_nonneg hval 2),
        mul_nonneg (le_of_lt (by linarith :
          (0:ℝ) < -(first * second * third + first * second * fourth
            + first * third * fourth + second * third * fourth))) hval]
    rcases hsome with h | h | h | h
    · exact hkey first h (Or.inl rfl)
    · exact hkey second h (Or.inr (Or.inl rfl))
    · exact hkey third h (Or.inr (Or.inr (Or.inl rfl)))
    · exact hkey fourth h (Or.inr (Or.inr (Or.inr rfl)))
  · rintro harm
    by_contra hcon
    obtain ⟨hone, hrestOne⟩ := not_or.mp hcon
    obtain ⟨htwo, hrestTwo⟩ := not_or.mp hrestOne
    obtain ⟨hthree, hfour⟩ := not_or.mp hrestTwo
    rw [not_le] at hone htwo hthree hfour
    rcases harm with h | h | h | h
    · linarith
    · nlinarith [mul_pos_of_neg_of_neg hone htwo, mul_pos_of_neg_of_neg hone hthree,
        mul_pos_of_neg_of_neg hone hfour, mul_pos_of_neg_of_neg htwo hthree,
        mul_pos_of_neg_of_neg htwo hfour, mul_pos_of_neg_of_neg hthree hfour]
    · nlinarith [mul_pos_of_neg_of_neg hone htwo, mul_pos_of_neg_of_neg hone hthree,
        mul_pos_of_neg_of_neg hone hfour, mul_pos_of_neg_of_neg htwo hthree,
        mul_pos_of_neg_of_neg htwo hfour, mul_pos_of_neg_of_neg hthree hfour,
        hone, htwo, hthree, hfour]
    · nlinarith [mul_pos_of_neg_of_neg hone htwo, mul_pos_of_neg_of_neg hthree hfour]

/-- **THE FOUR TERM PIGEONHOLE.**  On a support of four slots or more, a
nonnegative total, or a nonpositive doubled second symmetric function, or a
nonnegative sixfold third one, or a nonpositive twenty fourfold fourth one,
all forbid a family of strictly negative values. -/
theorem exists_nonneg_of_fourSigns {support : Finset (Fin 6)} (hcard : 4 ≤ support.card)
    (value : Fin 6 → ℝ)
    (hsign : 0 ≤ (∑ slot ∈ support, value slot)
      ∨ (∑ slot ∈ support, ∑ other ∈ support.erase slot, value slot * value other) ≤ 0
      ∨ 0 ≤ (∑ slot ∈ support, ∑ other ∈ support.erase slot,
              ∑ third ∈ (support.erase slot).erase other,
                value slot * value other * value third)
      ∨ (∑ slot ∈ support, ∑ other ∈ support.erase slot,
          ∑ third ∈ (support.erase slot).erase other,
            ∑ fourth ∈ ((support.erase slot).erase other).erase third,
              value slot * value other * value third * value fourth) ≤ 0) :
    ∃ slot ∈ support, 0 ≤ value slot := by
  classical
  by_contra hcon
  have hneg : ∀ slot ∈ support, value slot < 0 := by
    intro slot hslot
    exact not_le.mp fun hge => hcon ⟨slot, hslot, hge⟩
  have hnonempty : support.Nonempty := Finset.card_pos.mp (by omega)
  have hcardOne : ∀ slot ∈ support, 3 ≤ (support.erase slot).card := by
    intro slot hslot
    rw [Finset.card_erase_of_mem hslot]
    omega
  have hcardTwo : ∀ slot ∈ support, ∀ other ∈ support.erase slot,
      2 ≤ ((support.erase slot).erase other).card := by
    intro slot hslot other hother
    rw [Finset.card_erase_of_mem hother]
    have := hcardOne slot hslot
    omega
  have hcardThree : ∀ slot ∈ support, ∀ other ∈ support.erase slot,
      ∀ third ∈ (support.erase slot).erase other,
      1 ≤ (((support.erase slot).erase other).erase third).card := by
    intro slot hslot other hother third hthird
    rw [Finset.card_erase_of_mem hthird]
    have := hcardTwo slot hslot other hother
    omega
  rcases hsign with htotal | hsecond | hthird | hfourth
  · have hlt : (∑ slot ∈ support, value slot) < ∑ _slot ∈ support, (0 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty hnonempty fun slot hslot => hneg slot hslot
    rw [Finset.sum_const_zero] at hlt
    linarith
  · have hinner : ∀ slot ∈ support,
        0 < ∑ other ∈ support.erase slot, value slot * value other := by
      intro slot hslot
      have herase : (support.erase slot).Nonempty :=
        Finset.card_pos.mp (by have := hcardOne slot hslot; omega)
      have hlt : (∑ _other ∈ support.erase slot, (0 : ℝ))
          < ∑ other ∈ support.erase slot, value slot * value other :=
        Finset.sum_lt_sum_of_nonempty herase fun other hother =>
          mul_pos_of_neg_of_neg (hneg slot hslot)
            (hneg other (Finset.mem_of_mem_erase hother))
      rwa [Finset.sum_const_zero] at hlt
    have hlt : (∑ _slot ∈ support, (0 : ℝ))
        < ∑ slot ∈ support, ∑ other ∈ support.erase slot, value slot * value other :=
      Finset.sum_lt_sum_of_nonempty hnonempty fun slot hslot => hinner slot hslot
    rw [Finset.sum_const_zero] at hlt
    linarith
  · have hinner : ∀ slot ∈ support,
        (∑ other ∈ support.erase slot, ∑ third ∈ (support.erase slot).erase other,
          value slot * value other * value third) < 0 := by
      intro slot hslot
      have herase : (support.erase slot).Nonempty :=
        Finset.card_pos.mp (by have := hcardOne slot hslot; omega)
      have hcell : ∀ other ∈ support.erase slot,
          (∑ third ∈ (support.erase slot).erase other,
            value slot * value other * value third) < 0 := by
        intro other hother
        have hnext : (((support.erase slot).erase other)).Nonempty :=
          Finset.card_pos.mp (by have := hcardTwo slot hslot other hother; omega)
        have hlt : (∑ third ∈ (support.erase slot).erase other,
              value slot * value other * value third)
            < ∑ _third ∈ (support.erase slot).erase other, (0 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hnext fun third hthird =>
            mul_neg_of_pos_of_neg
              (mul_pos_of_neg_of_neg (hneg slot hslot)
                (hneg other (Finset.mem_of_mem_erase hother)))
              (hneg third (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hthird)))
        rwa [Finset.sum_const_zero] at hlt
      have hlt : (∑ other ∈ support.erase slot,
            ∑ third ∈ (support.erase slot).erase other,
              value slot * value other * value third)
          < ∑ _other ∈ support.erase slot, (0 : ℝ) :=
        Finset.sum_lt_sum_of_nonempty herase fun other hother => hcell other hother
      rwa [Finset.sum_const_zero] at hlt
    have hlt : (∑ slot ∈ support, ∑ other ∈ support.erase slot,
          ∑ third ∈ (support.erase slot).erase other,
            value slot * value other * value third)
        < ∑ _slot ∈ support, (0 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty hnonempty fun slot hslot => hinner slot hslot
    rw [Finset.sum_const_zero] at hlt
    linarith
  · have hinner : ∀ slot ∈ support,
        0 < ∑ other ∈ support.erase slot, ∑ third ∈ (support.erase slot).erase other,
          ∑ fourth ∈ ((support.erase slot).erase other).erase third,
            value slot * value other * value third * value fourth := by
      intro slot hslot
      have herase : (support.erase slot).Nonempty :=
        Finset.card_pos.mp (by have := hcardOne slot hslot; omega)
      have hcell : ∀ other ∈ support.erase slot,
          0 < ∑ third ∈ (support.erase slot).erase other,
            ∑ fourth ∈ ((support.erase slot).erase other).erase third,
              value slot * value other * value third * value fourth := by
        intro other hother
        have hnext : (((support.erase slot).erase other)).Nonempty :=
          Finset.card_pos.mp (by have := hcardTwo slot hslot other hother; omega)
        have hdeep : ∀ third ∈ (support.erase slot).erase other,
            0 < ∑ fourth ∈ ((support.erase slot).erase other).erase third,
              value slot * value other * value third * value fourth := by
          intro third hthird
          have hlast : ((((support.erase slot).erase other).erase third)).Nonempty :=
            Finset.card_pos.mp
              (by have := hcardThree slot hslot other hother third hthird; omega)
          have hlt : (∑ _fourth ∈ ((support.erase slot).erase other).erase third,
                (0 : ℝ))
              < ∑ fourth ∈ ((support.erase slot).erase other).erase third,
                value slot * value other * value third * value fourth :=
            Finset.sum_lt_sum_of_nonempty hlast fun fourth hfourth =>
              mul_pos_of_neg_of_neg
                (mul_neg_of_pos_of_neg
                  (mul_pos_of_neg_of_neg (hneg slot hslot)
                    (hneg other (Finset.mem_of_mem_erase hother)))
                  (hneg third (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hthird))))
                (hneg fourth (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
                  (Finset.mem_of_mem_erase hfourth))))
          rwa [Finset.sum_const_zero] at hlt
        have hlt : (∑ _third ∈ (support.erase slot).erase other, (0 : ℝ))
            < ∑ third ∈ (support.erase slot).erase other,
              ∑ fourth ∈ ((support.erase slot).erase other).erase third,
                value slot * value other * value third * value fourth :=
          Finset.sum_lt_sum_of_nonempty hnext fun third hthird => hdeep third hthird
        rwa [Finset.sum_const_zero] at hlt
      have hlt : (∑ _other ∈ support.erase slot, (0 : ℝ))
          < ∑ other ∈ support.erase slot, ∑ third ∈ (support.erase slot).erase other,
            ∑ fourth ∈ ((support.erase slot).erase other).erase third,
              value slot * value other * value third * value fourth :=
        Finset.sum_lt_sum_of_nonempty herase fun other hother => hcell other hother
      rwa [Finset.sum_const_zero] at hlt
    have hlt : (∑ _slot ∈ support, (0 : ℝ))
        < ∑ slot ∈ support, ∑ other ∈ support.erase slot,
          ∑ third ∈ (support.erase slot).erase other,
            ∑ fourth ∈ ((support.erase slot).erase other).erase third,
              value slot * value other * value third * value fourth :=
      Finset.sum_lt_sum_of_nonempty hnonempty fun slot hslot => hinner slot hslot
    rw [Finset.sum_const_zero] at hlt
    linarith

end SignAlgebra

/-! ## Layer 1 — the repaired factorization -/

section Repair

/-- **THE FOUR TERM DROP CRITERION.**  Some pair of slots carries a strictly
positive dual pair block, and the four erasure determinants of that pair
break the sign alternation of a family of four negative numbers at one of
the four symmetric functions.

The first two arms are the refuted criterion.  The third and the fourth arms
are the repair, and `Gtz.quadFourSign_iff` shows that no fifth arm exists. -/
def AtomQuadDropFourSignClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 0 < scale slotOne - atomDualGram atom scale slotOne slotOne
      ∧ 0 < (scale slotOne - atomDualGram atom scale slotOne slotOne)
            * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
          - atomDualGram atom scale slotOne slotTwo ^ 2
      ∧ (0 ≤ (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
            atomGapCoef scale slot * atomDualTripleDet atom scale slotOne slotTwo slot)
        ∨ (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
            ∑ other ∈ (({slotOne, slotTwo} : Finset (Fin 6))ᶜ).erase slot,
              (atomGapCoef scale slot * atomDualTripleDet atom scale slotOne slotTwo slot)
                * (atomGapCoef scale other
                  * atomDualTripleDet atom scale slotOne slotTwo other)) ≤ 0
        ∨ 0 ≤ (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
            ∑ other ∈ (({slotOne, slotTwo} : Finset (Fin 6))ᶜ).erase slot,
              ∑ third ∈ ((({slotOne, slotTwo} : Finset (Fin 6))ᶜ).erase slot).erase other,
                (atomGapCoef scale slot
                    * atomDualTripleDet atom scale slotOne slotTwo slot)
                  * (atomGapCoef scale other
                    * atomDualTripleDet atom scale slotOne slotTwo other)
                  * (atomGapCoef scale third
                    * atomDualTripleDet atom scale slotOne slotTwo third))
        ∨ (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
            ∑ other ∈ (({slotOne, slotTwo} : Finset (Fin 6))ᶜ).erase slot,
              ∑ third ∈ ((({slotOne, slotTwo} : Finset (Fin 6))ᶜ).erase slot).erase other,
                ∑ fourth ∈ (((({slotOne, slotTwo} : Finset (Fin 6))ᶜ).erase slot).erase
                    other).erase third,
                  (atomGapCoef scale slot
                      * atomDualTripleDet atom scale slotOne slotTwo slot)
                    * (atomGapCoef scale other
                      * atomDualTripleDet atom scale slotOne slotTwo other)
                    * (atomGapCoef scale third
                      * atomDualTripleDet atom scale slotOne slotTwo third)
                    * (atomGapCoef scale fourth
                      * atomDualTripleDet atom scale slotOne slotTwo fourth)) ≤ 0)

/-- **THE FOUR TERM CRITERION CLOSES THE RESIDUE.**  One erasure is
nonnegative, so the Schur square makes the dropped triple a nonnegative dual
block, so the remaining three slots cover. -/
theorem atomVertexCoverClosed_of_dropFourSign (hdrop : AtomQuadDropFourSignClosed) :
    AtomVertexCoverClosed := by
  classical
  intro atom scale hpos hmass hframe
  obtain ⟨slotOne, slotTwo, hne, hdiagOne, hminor, hsign⟩ := hdrop atom scale hpos hmass hframe
  have hcardCompl : (({slotOne, slotTwo} : Finset (Fin 6))ᶜ).card = 4 := by
    rw [Finset.card_compl, Finset.card_pair hne]
    simp
  obtain ⟨slotThree, hmem, hcell⟩ := exists_nonneg_of_fourSigns (support :=
      ({slotOne, slotTwo} : Finset (Fin 6))ᶜ) (by rw [hcardCompl])
    (fun slot => atomGapCoef scale slot * atomDualTripleDet atom scale slotOne slotTwo slot)
    hsign
  have hcoefThree := atomGapCoef_pos scale (hpos slotThree)
    (atomScale_lt_one scale hpos hmass slotThree)
  have hdet : 0 ≤ atomDualTripleDet atom scale slotOne slotTwo slotThree := by
    rcases eq_or_lt_of_le hcell with heq | hlt
    · nlinarith [hcoefThree]
    · nlinarith [hcoefThree]
  have hmemCompl := Finset.mem_compl.mp hmem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmemCompl
  have honeThree : slotOne ≠ slotThree := fun heq => hmemCompl.1 heq.symm
  have htwoThree : slotTwo ≠ slotThree := fun heq => hmemCompl.2 heq.symm
  refine ⟨({slotOne, slotTwo, slotThree} : Finset (Fin 6))ᶜ, ?_, fun direction => ?_⟩
  · rw [Finset.card_compl, Finset.card_insert_of_notMem (by simp [hne, honeThree]),
      Finset.card_pair htwoThree]
    simp
  · refine atomCover_of_dualTriple hpos hmass hframe hne honeThree htwoThree
      (fun valOne valTwo valThree => ?_) direction
    have hform := quadTripleForm_nonneg (diagOne :=
        scale slotOne - atomDualGram atom scale slotOne slotOne)
      (diagTwo := scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
      (diagThree := scale slotThree - atomDualGram atom scale slotThree slotThree)
      (offOneTwo := atomDualGram atom scale slotOne slotTwo)
      (offOneThree := atomDualGram atom scale slotOne slotThree)
      (offTwoThree := atomDualGram atom scale slotTwo slotThree)
      (first := valOne) (second := valTwo) (third := valThree) hdiagOne
      (by nlinarith [hminor]) (by simp only [atomDualTripleDet] at hdet; nlinarith [hdet])
    nlinarith [hform]

/-- **THE CELL FROM THE FOUR TERM DROP CRITERION.** -/
theorem gtzWeighted_six_three_of_dropFourSign (hdrop : AtomQuadDropFourSignClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomVertexCover (atomVertexCoverClosed_of_dropFourSign hdrop)

/-- **THE REPAIR IS A GENUINE WEAKENING.**  The two term criterion carries
the four term one, so the refutation of the two term criterion does not
touch the four term one. -/
theorem atomQuadDropFourSignClosed_of_dropSign (hdrop : AtomQuadDropSignClosed) :
    AtomQuadDropFourSignClosed := by
  intro atom scale hpos hmass hframe
  obtain ⟨slotOne, slotTwo, hne, hdiagOne, hminor, hsign⟩ := hdrop atom scale hpos hmass hframe
  refine ⟨slotOne, slotTwo, hne, hdiagOne, hminor, ?_⟩
  rcases hsign with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end Repair

/-! ## Layer 2 — the witness -/

section Witness

/-- **THE WITNESS.**  The six half sums of two of the three axes.  Three
pairs of them are orthogonal, and the twelve remaining pairs read a quarter
in absolute value. -/
noncomputable def dropWitnessAtom : Fin 6 → (Fin 3 → ℝ) :=
  ![![1 / 2, 1 / 2, 0], ![1 / 2, -(1 / 2), 0], ![1 / 2, 0, 1 / 2],
    ![1 / 2, 0, -(1 / 2)], ![0, 1 / 2, 1 / 2], ![0, 1 / 2, -(1 / 2)]]

/-- The uniform scale of mass one. -/
noncomputable def dropWitnessScale : Fin 6 → ℝ :=
  ![1 / 6, 1 / 6, 1 / 6, 1 / 6, 1 / 6, 1 / 6]

/-- The dual Gram of the witness, as a rational table.  It is the frame Gram
over five, because the gap form is five times the identity. -/
noncomputable def dropWitnessDual : Fin 6 → Fin 6 → ℝ :=
  ![![1 / 10, 0, 1 / 20, 1 / 20, 1 / 20, 1 / 20],
    ![0, 1 / 10, 1 / 20, 1 / 20, -(1 / 20), -(1 / 20)],
    ![1 / 20, 1 / 20, 1 / 10, 0, 1 / 20, -(1 / 20)],
    ![1 / 20, 1 / 20, 0, 1 / 10, -(1 / 20), 1 / 20],
    ![1 / 20, -(1 / 20), 1 / 20, -(1 / 20), 1 / 10, 0],
    ![1 / 20, -(1 / 20), -(1 / 20), 1 / 20, 0, 1 / 10]]

theorem dropWitnessAtom_zero : dropWitnessAtom 0 = ![1 / 2, 1 / 2, 0] := rfl

theorem dropWitnessAtom_one : dropWitnessAtom 1 = ![1 / 2, -(1 / 2), 0] := rfl

theorem dropWitnessAtom_two : dropWitnessAtom 2 = ![1 / 2, 0, 1 / 2] := rfl

theorem dropWitnessAtom_three : dropWitnessAtom 3 = ![1 / 2, 0, -(1 / 2)] := rfl

theorem dropWitnessAtom_four : dropWitnessAtom 4 = ![0, 1 / 2, 1 / 2] := rfl

theorem dropWitnessAtom_five : dropWitnessAtom 5 = ![0, 1 / 2, -(1 / 2)] := rfl

theorem dropWitnessScale_zero : dropWitnessScale 0 = 1 / 6 := rfl

theorem dropWitnessScale_one : dropWitnessScale 1 = 1 / 6 := rfl

theorem dropWitnessScale_two : dropWitnessScale 2 = 1 / 6 := rfl

theorem dropWitnessScale_three : dropWitnessScale 3 = 1 / 6 := rfl

theorem dropWitnessScale_four : dropWitnessScale 4 = 1 / 6 := rfl

theorem dropWitnessScale_five : dropWitnessScale 5 = 1 / 6 := rfl

theorem dropWitnessDual_zero :
    dropWitnessDual 0 = ![1 / 10, 0, 1 / 20, 1 / 20, 1 / 20, 1 / 20] := rfl

theorem dropWitnessDual_one :
    dropWitnessDual 1 = ![0, 1 / 10, 1 / 20, 1 / 20, -(1 / 20), -(1 / 20)] := rfl

theorem dropWitnessDual_two :
    dropWitnessDual 2 = ![1 / 20, 1 / 20, 1 / 10, 0, 1 / 20, -(1 / 20)] := rfl

theorem dropWitnessDual_three :
    dropWitnessDual 3 = ![1 / 20, 1 / 20, 0, 1 / 10, -(1 / 20), 1 / 20] := rfl

theorem dropWitnessDual_four :
    dropWitnessDual 4 = ![1 / 20, -(1 / 20), 1 / 20, -(1 / 20), 1 / 10, 0] := rfl

theorem dropWitnessDual_five :
    dropWitnessDual 5 = ![1 / 20, -(1 / 20), -(1 / 20), 1 / 20, 0, 1 / 10] := rfl

/-- The entries of a table of six, at the four indices that a double cons
does not reduce on its own. -/
theorem dropVecTwo (a b c d e f : ℝ) : ![a, b, c, d, e, f] 2 = c := rfl

theorem dropVecThree (a b c d e f : ℝ) : ![a, b, c, d, e, f] 3 = d := rfl

theorem dropVecFour (a b c d e f : ℝ) : ![a, b, c, d, e, f] 4 = e := rfl

theorem dropVecFive (a b c d e f : ℝ) : ![a, b, c, d, e, f] 5 = f := rfl

/-- The literal tables of the witness, gathered for the arithmetic tactics. -/
theorem dropWitnessScale_pos (slot : Fin 6) : 0 < dropWitnessScale slot := by
  fin_cases slot <;> norm_num [dropWitnessScale]

theorem dropWitnessScale_sum : (∑ slot, dropWitnessScale slot) = 1 := by
  simp [Fin.sum_univ_six, dropWitnessScale]
  norm_num

/-- **THE WITNESS IS A TIGHT FRAME.**  The six half sums of two axes resolve
the identity exactly. -/
theorem dropWitnessAtom_isTightFrame (probe direction : Fin 3 → ℝ) :
    (∑ slot, (dropWitnessAtom slot ⬝ᵥ probe) * (dropWitnessAtom slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  simp [Fin.sum_univ_six, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  ring

/-- Every gap coefficient of the witness reads five. -/
theorem dropWitnessGapCoef (slot : Fin 6) : atomGapCoef dropWitnessScale slot = 5 := by
  fin_cases slot <;> norm_num [atomGapCoef, dropWitnessScale]

theorem dropWitnessGapRow_zero :
    atomGapRow dropWitnessAtom dropWitnessScale 0 = ![5, 0, 0] := by
  funext colIndex
  simp only [atomGapRow, atomGapCoef, Fin.sum_univ_six, dropWitnessAtom_zero,
      dropWitnessAtom_one, dropWitnessAtom_two, dropWitnessAtom_three, dropWitnessAtom_four, dropWitnessAtom_five,
      dropWitnessScale_zero, dropWitnessScale_one, dropWitnessScale_two,
      dropWitnessScale_three, dropWitnessScale_four, dropWitnessScale_five]
  fin_cases colIndex <;> norm_num

theorem dropWitnessGapRow_one :
    atomGapRow dropWitnessAtom dropWitnessScale 1 = ![0, 5, 0] := by
  funext colIndex
  simp only [atomGapRow, atomGapCoef, Fin.sum_univ_six, dropWitnessAtom_zero,
      dropWitnessAtom_one, dropWitnessAtom_two, dropWitnessAtom_three, dropWitnessAtom_four, dropWitnessAtom_five,
      dropWitnessScale_zero, dropWitnessScale_one, dropWitnessScale_two,
      dropWitnessScale_three, dropWitnessScale_four, dropWitnessScale_five]
  fin_cases colIndex <;> norm_num

theorem dropWitnessGapRow_two :
    atomGapRow dropWitnessAtom dropWitnessScale 2 = ![0, 0, 5] := by
  funext colIndex
  simp only [atomGapRow, atomGapCoef, Fin.sum_univ_six, dropWitnessAtom_zero,
      dropWitnessAtom_one, dropWitnessAtom_two, dropWitnessAtom_three, dropWitnessAtom_four, dropWitnessAtom_five,
      dropWitnessScale_zero, dropWitnessScale_one, dropWitnessScale_two,
      dropWitnessScale_three, dropWitnessScale_four, dropWitnessScale_five,
      quadVecTwo]
  fin_cases colIndex <;> norm_num

/-- The determinant of the gap form of the witness. -/
theorem dropWitnessGapDet : atomGapDet dropWitnessAtom dropWitnessScale = 125 := by
  simp only [atomGapDet, symDet, symAdj_zero, dropWitnessGapRow_zero, dropWitnessGapRow_one,
    dropWitnessGapRow_two]
  norm_num [atomCross, dotProduct, Fin.sum_univ_three, quadVecTwo, quadConsTwo]

/-- **THE ADJUGATE OF THE GAP FORM OF THE WITNESS.**  The gap form is five
times the identity, so its adjugate is twenty five times the identity. -/
theorem dropWitnessSymAdj (index colIndex : Fin 3) :
    symAdj (atomGapRow dropWitnessAtom dropWitnessScale) index colIndex
      = if index = colIndex then 25 else 0 := by
  fin_cases index <;> fin_cases colIndex <;>
    simp [symAdj, atomCross, dropWitnessGapRow_zero, dropWitnessGapRow_one,
      dropWitnessGapRow_two] <;>
    norm_num

/-- **THE DUAL VECTOR OF THE WITNESS IS THE ATOM OVER FIVE.** -/
theorem dropWitnessDualVec (slot : Fin 6) (index : Fin 3) :
    atomDualVec dropWitnessAtom dropWitnessScale slot index
      = dropWitnessAtom slot index / 5 := by
  have hdet : symDet (atomGapRow dropWitnessAtom dropWitnessScale) = 125 := dropWitnessGapDet
  simp only [atomDualVec, symSolve, hdet, dotProduct, dropWitnessSymAdj, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- **THE DUAL GRAM OF THE WITNESS IS THE RATIONAL TABLE.** -/
theorem dropWitnessDualGram (rowSlot colSlot : Fin 6) :
    atomDualGram dropWitnessAtom dropWitnessScale rowSlot colSlot
      = dropWitnessDual rowSlot colSlot := by
  have hvec : atomDualVec dropWitnessAtom dropWitnessScale colSlot
      = fun index => dropWitnessAtom colSlot index / 5 := by
    funext index
    exact dropWitnessDualVec colSlot index
  simp only [atomDualGram, hvec, dotProduct, Fin.sum_univ_three]
  fin_cases rowSlot <;> fin_cases colSlot <;>
    simp [dropWitnessAtom, dropWitnessDual] <;>
    norm_num

end Witness

/-! ## Layer 3 — the refutation -/

section Refutation

/-- **EVERY ORDERED PAIR OF THE WITNESS FAILS BOTH ARMS.**  The first
symmetric function of the four erasures is strictly negative and the doubled
second one is strictly positive, at all thirty ordered pairs. -/
theorem dropWitness_pair_fails (slotOne slotTwo : Fin 6) (hne : slotOne ≠ slotTwo) :
    (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
        atomGapCoef dropWitnessScale slot
          * atomDualTripleDet dropWitnessAtom dropWitnessScale slotOne slotTwo slot) < 0
      ∧ 0 < ∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
          ∑ other ∈ (({slotOne, slotTwo} : Finset (Fin 6))ᶜ).erase slot,
            (atomGapCoef dropWitnessScale slot
                * atomDualTripleDet dropWitnessAtom dropWitnessScale slotOne slotTwo slot)
              * (atomGapCoef dropWitnessScale other
                * atomDualTripleDet dropWitnessAtom dropWitnessScale slotOne slotTwo other) := by
  classical
  rw [quadPairSum]
  rw [quadComplSum _ hne, quadComplSum _ hne]
  simp only [atomDualTripleDet, dropWitnessDualGram, dropWitnessGapCoef, Fin.sum_univ_six]
  fin_cases slotOne <;> fin_cases slotTwo <;>
    first
      | exact absurd rfl hne
      | (constructor <;> simp [dropWitnessScale, dropWitnessDual] <;> norm_num)

/-- **THE TWO TERM DROP DICHOTOMY IS FALSE.**  At the witness every pair of
slots carries a positive diagonal shift and a positive dual pair block, so
the two cheap conditions never exclude a pair, and the four erasure
determinants of every pair have a strictly negative total together with a
strictly positive doubled second symmetric function.  No pair satisfies the
criterion. -/
theorem not_atomQuadDropSignClosed : ¬ AtomQuadDropSignClosed := by
  intro hclosed
  obtain ⟨slotOne, slotTwo, hne, -, -, hsign⟩ :=
    hclosed dropWitnessAtom dropWitnessScale dropWitnessScale_pos dropWitnessScale_sum
      dropWitnessAtom_isTightFrame
  obtain ⟨hfirst, hsecond⟩ := dropWitness_pair_fails slotOne slotTwo hne
  rcases hsign with h | h
  · linarith
  · linarith

/-- **THE SCALAR DROP CRITERION IS FALSE.**  It carries the two term sign
criterion, which the witness refutes. -/
theorem not_atomQuadDropScalarClosed : ¬ AtomQuadDropScalarClosed := fun hscalar =>
  not_atomQuadDropSignClosed (atomQuadDropSignClosed_of_scalar hscalar)

end Refutation

/-! ## Layer 4 — the witness does not refute the cell -/

section Calibration

/-- The diagonal shift of the witness, at every slot. -/
theorem dropWitness_diag (slot : Fin 6) :
    dropWitnessScale slot - atomDualGram dropWitnessAtom dropWitnessScale slot slot
      = 1 / 15 := by
  rw [dropWitnessDualGram]
  fin_cases slot <;> simp [dropWitnessScale, dropWitnessDual] <;> norm_num

/-- The dual pair block of the two slots zero and two is strictly positive. -/
theorem dropWitness_minor_zeroTwo :
    0 < (dropWitnessScale 0 - atomDualGram dropWitnessAtom dropWitnessScale 0 0)
        * (dropWitnessScale 2 - atomDualGram dropWitnessAtom dropWitnessScale 2 2)
      - atomDualGram dropWitnessAtom dropWitnessScale 0 2 ^ 2 := by
  rw [dropWitness_diag, dropWitness_diag, dropWitnessDualGram]
  simp [dropWitnessDual]
  norm_num

/-- **ONE ERASURE OF THE WITNESS IS STRICTLY POSITIVE.**  The triple of slots
zero, two and five is a nonnegative dual block, so the complementary triple
covers.  The witness refutes the criterion and not the cell. -/
theorem dropWitness_dualTripleDet_pos :
    atomDualTripleDet dropWitnessAtom dropWitnessScale 0 2 5 = 1 / 21600 := by
  simp only [atomDualTripleDet, dropWitnessDualGram]
  simp [dropWitnessScale, dropWitnessDual]
  norm_num

/-- **THE WITNESS CARRIES A COVERING TRIPLE.**  The three slots one, three and
four dominate every direction at the uniform scale one sixth. -/
theorem dropWitnessAtom_hasVertexCover :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ direction : Fin 3 → ℝ,
          direction ⬝ᵥ direction
            ≤ ∑ slot ∈ car, (dropWitnessAtom slot ⬝ᵥ direction) ^ 2 / dropWitnessScale slot := by
  classical
  refine ⟨({0, 2, 5} : Finset (Fin 6))ᶜ, by decide, fun direction => ?_⟩
  have hdiagOne : 0 < dropWitnessScale 0
      - atomDualGram dropWitnessAtom dropWitnessScale 0 0 := by
    rw [dropWitness_diag]; norm_num
  have hminor := dropWitness_minor_zeroTwo
  have hdet : (0 : ℝ) ≤ atomDualTripleDet dropWitnessAtom dropWitnessScale 0 2 5 := by
    rw [dropWitness_dualTripleDet_pos]; norm_num
  refine atomCover_of_dualTriple dropWitnessScale_pos dropWitnessScale_sum
    dropWitnessAtom_isTightFrame (by decide : (0 : Fin 6) ≠ 2) (by decide : (0 : Fin 6) ≠ 5)
    (by decide : (2 : Fin 6) ≠ 5) (fun valOne valTwo valThree => ?_) direction
  have hform := quadTripleForm_nonneg (diagOne :=
      dropWitnessScale 0 - atomDualGram dropWitnessAtom dropWitnessScale 0 0)
    (diagTwo := dropWitnessScale 2 - atomDualGram dropWitnessAtom dropWitnessScale 2 2)
    (diagThree := dropWitnessScale 5 - atomDualGram dropWitnessAtom dropWitnessScale 5 5)
    (offOneTwo := atomDualGram dropWitnessAtom dropWitnessScale 0 2)
    (offOneThree := atomDualGram dropWitnessAtom dropWitnessScale 0 5)
    (offTwoThree := atomDualGram dropWitnessAtom dropWitnessScale 2 5)
    (first := valOne) (second := valTwo) (third := valThree) hdiagOne
    (by nlinarith [hminor]) (by simp only [atomDualTripleDet] at hdet; nlinarith [hdet])
  nlinarith [hform]

end Calibration

/-! ## Layer 5 — the cycle law of the Gram -/

section CycleLaw

variable {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}

/-- **THE TOTAL CYCLE LAW.**  The signed triangle products through a pair,
summed over all slots, read the square of the pair entry. -/
theorem atomGram_cycle_total
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot colSlot : Fin slotCount) :
    (∑ slot, atomGram atom rowSlot slot * atomGram atom slot colSlot
        * atomGram atom colSlot rowSlot)
      = atomGram atom rowSlot colSlot ^ 2 := by
  classical
  have hidem := atomGram_idempotent hframe rowSlot colSlot
  have hsplit : (∑ slot, atomGram atom rowSlot slot * atomGram atom slot colSlot
      * atomGram atom colSlot rowSlot)
      = (∑ slot, atomGram atom rowSlot slot * atomGram atom slot colSlot)
        * atomGram atom colSlot rowSlot := by
    rw [Finset.sum_mul]
  rw [hsplit, hidem, atomGram_comm atom colSlot rowSlot]
  ring

/-- **THE CYCLE LAW OFF THE PAIR.**  The signed triangle products through a
pair, summed over the slots off that pair, read the square of the pair entry
times the deficit of the two diagonal entries.

This is the one quantity of an erasure determinant that the Hermitian field
reads differently.  Over the real field each term is the full product of
three moduli with one sign.  Over the Hermitian field each term is a real
part, and a real part can vanish while the moduli stay large. -/
theorem atomGram_cycle_erase
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {rowSlot colSlot : Fin slotCount} (hne : rowSlot ≠ colSlot) :
    (∑ slot ∈ (Finset.univ.erase rowSlot).erase colSlot,
        atomGram atom rowSlot slot * atomGram atom slot colSlot
          * atomGram atom colSlot rowSlot)
      = atomGram atom rowSlot colSlot ^ 2
        * (1 - atomGram atom rowSlot rowSlot - atomGram atom colSlot colSlot) := by
  classical
  have hmemCol : colSlot ∈ Finset.univ.erase rowSlot :=
    Finset.mem_erase.mpr ⟨fun heq => hne heq.symm, Finset.mem_univ colSlot⟩
  have houter := Finset.add_sum_erase Finset.univ
    (fun slot => atomGram atom rowSlot slot * atomGram atom slot colSlot
      * atomGram atom colSlot rowSlot) (Finset.mem_univ rowSlot)
  have hinner := Finset.add_sum_erase (Finset.univ.erase rowSlot)
    (fun slot => atomGram atom rowSlot slot * atomGram atom slot colSlot
      * atomGram atom colSlot rowSlot) hmemCol
  have htotal := atomGram_cycle_total hframe rowSlot colSlot
  have hsym := atomGram_comm atom colSlot rowSlot
  have hrowCell : atomGram atom rowSlot rowSlot * atomGram atom rowSlot colSlot
      * atomGram atom colSlot rowSlot
      = atomGram atom rowSlot rowSlot * atomGram atom rowSlot colSlot ^ 2 := by
    rw [hsym]; ring
  have hcolCell : atomGram atom rowSlot colSlot * atomGram atom colSlot colSlot
      * atomGram atom colSlot rowSlot
      = atomGram atom colSlot colSlot * atomGram atom rowSlot colSlot ^ 2 := by
    rw [hsym]; ring
  rw [hrowCell] at houter
  rw [hcolCell] at hinner
  rw [htotal] at houter
  linarith

/-- **AN EVEN TRIANGLE THROUGH EVERY LIVE PAIR.**  If a pair entry is nonzero
and the two diagonal entries total less than one, some slot off the pair
carries a strictly positive signed triangle product.

Over the Hermitian field the same total holds for the real parts, and every
real part can vanish.  The strict positivity of ONE product is therefore a
real reading of the datum. -/
theorem exists_pos_cycle_of_pair
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {rowSlot colSlot : Fin slotCount} (hne : rowSlot ≠ colSlot)
    (hentry : atomGram atom rowSlot colSlot ≠ 0)
    (hdeficit : atomGram atom rowSlot rowSlot + atomGram atom colSlot colSlot < 1) :
    ∃ slot, slot ≠ rowSlot ∧ slot ≠ colSlot
      ∧ 0 < atomGram atom rowSlot slot * atomGram atom slot colSlot
          * atomGram atom colSlot rowSlot := by
  classical
  have hsum := atomGram_cycle_erase hframe hne
  have hsq : 0 < atomGram atom rowSlot colSlot ^ 2 := by positivity
  have hpos : 0 < ∑ slot ∈ (Finset.univ.erase rowSlot).erase colSlot,
      atomGram atom rowSlot slot * atomGram atom slot colSlot
        * atomGram atom colSlot rowSlot := by
    rw [hsum]
    exact mul_pos hsq (by linarith)
  have hzero : (∑ _slot ∈ (Finset.univ.erase rowSlot).erase colSlot, (0 : ℝ))
      < ∑ slot ∈ (Finset.univ.erase rowSlot).erase colSlot,
        atomGram atom rowSlot slot * atomGram atom slot colSlot
          * atomGram atom colSlot rowSlot := by
    rw [Finset.sum_const_zero]
    exact hpos
  obtain ⟨slot, hmem, hcell⟩ := Finset.exists_lt_of_sum_lt hzero
  refine ⟨slot, ?_, ?_, hcell⟩
  · exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hmem)).1
  · exact (Finset.mem_erase.mp hmem).1

end CycleLaw

/-! ## Layer 6 — the pivot passage from the plane to the cover -/

section PivotPassage

variable (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)

/-- The PLANE READING of a pair at a polar probe: the scaled squared readings
of the two slots off the pivot. -/
noncomputable def atomPivotPlaneRead (slotOne slotTwo : Fin 6) (probe : Fin 3 → ℝ) : ℝ :=
  (atom slotOne ⬝ᵥ probe) ^ 2 / scale slotOne
    + (atom slotTwo ⬝ᵥ probe) ^ 2 / scale slotTwo

/-- The COUPLING of a pair to the pivot at a polar probe.  This quantity is
the whole obstruction: its MODULUS is what a Cauchy-Schwarz bound reads, and
its DIRECTION is what the exact passage reads. -/
noncomputable def atomPivotCouple (pivot slotOne slotTwo : Fin 6) (probe : Fin 3 → ℝ) : ℝ :=
  atomGram atom pivot slotOne * (atom slotOne ⬝ᵥ probe) / scale slotOne
    + atomGram atom pivot slotTwo * (atom slotTwo ⬝ᵥ probe) / scale slotTwo

/-- The PIVOT WEIGHT of a pair: the scaled squared Gram entries to the pivot. -/
noncomputable def atomPivotWeight (pivot slotOne slotTwo : Fin 6) : ℝ :=
  atomGram atom pivot slotOne ^ 2 / scale slotOne
    + atomGram atom pivot slotTwo ^ 2 / scale slotTwo

variable {atom scale}

/-- **THE PLANE PARSEVAL LAW IS FREE.**  Against a probe orthogonal to the
pivot the five other atoms resolve the probe exactly, because the pivot reads
zero.  No projection and no plane coordinates are needed. -/
theorem atomPivotPolar_parseval
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {pivot : Fin 6} {probe : Fin 3 → ℝ} (hpolar : atom pivot ⬝ᵥ probe = 0) :
    (∑ slot ∈ Finset.univ.erase pivot, (atom slot ⬝ᵥ probe) ^ 2) = probe ⬝ᵥ probe := by
  classical
  have hall := hframe probe probe
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun slot => (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ probe)) (Finset.mem_univ pivot)
  simp only [hpolar, mul_zero, zero_add] at hsplit
  have hsq : ∀ slot : Fin 6, (atom slot ⬝ᵥ probe) ^ 2
      = (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ probe) := fun slot => sq _
  rw [Finset.sum_congr rfl fun slot _ => hsq slot, hsplit, hall]

/-- **THE PIVOT PASSAGE.**  A pivot whose diagonal beats its scale, together
with a pair whose plane reading beats the probe energy by the exact Schur
margin, gives a covering triple.

The passage is an EQUIVALENCE in substance: the triple covers exactly when
the displayed inequality holds at every polar probe.  The coupling enters
through its square, and the pivot budget `G_pp (G_pp - t_p)` pays for it.  The
passage is pure algebra and consumes no frame law.

The isotropic relaxation of this passage, which replaces the coupling square
by the Cauchy-Schwarz product of the pivot weight and the plane reading, is
REFUTED.  An adversarial descent drives its margin to `-0.129` while the cell
holds, so the DIRECTION of the coupling is load bearing and no modulus bound
closes the passage. -/
theorem atomPivotSchur_cover {pivot slotOne slotTwo : Fin 6}
    (hpivotPos : 0 < scale pivot) (honePos : 0 < scale slotOne) (htwoPos : 0 < scale slotTwo)
    (hgap : scale pivot < atomGram atom pivot pivot)
    (hschur : ∀ probe : Fin 3 → ℝ, atom pivot ⬝ᵥ probe = 0 →
      scale pivot * atomPivotCouple atom scale pivot slotOne slotTwo probe ^ 2
        ≤ (scale pivot * atomPivotWeight atom scale pivot slotOne slotTwo
            + atomGram atom pivot pivot
              * (atomGram atom pivot pivot - scale pivot))
          * (atomPivotPlaneRead atom scale slotOne slotTwo probe - probe ⬝ᵥ probe))
    (direction : Fin 3 → ℝ) :
    direction ⬝ᵥ direction
      ≤ (atom pivot ⬝ᵥ direction) ^ 2 / scale pivot
        + (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne
        + (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo := by
  classical
  have hdiagPos : 0 < atomGram atom pivot pivot := lt_trans hpivotPos hgap
  set lift : ℝ := (atom pivot ⬝ᵥ direction) / atomGram atom pivot pivot with hliftDef
  set probe : Fin 3 → ℝ := direction - lift • atom pivot with hprobeDef
  have hpolar : atom pivot ⬝ᵥ probe = 0 := by
    rw [hprobeDef, dotProduct_sub, dotProduct_smul, smul_eq_mul, hliftDef]
    have hgram : atom pivot ⬝ᵥ atom pivot = atomGram atom pivot pivot := rfl
    rw [hgram]
    field_simp
    ring
  have hread : ∀ slot : Fin 6,
      atom slot ⬝ᵥ direction = atom slot ⬝ᵥ probe + lift * atomGram atom pivot slot := by
    intro slot
    rw [hprobeDef, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have hgram : atom slot ⬝ᵥ atom pivot = atomGram atom pivot slot := by
      rw [atomGram, dotProduct_comm]
    rw [hgram]
    ring
  have henergy : direction ⬝ᵥ direction
      = probe ⬝ᵥ probe + lift ^ 2 * atomGram atom pivot pivot := by
    have hexpand : direction ⬝ᵥ direction
        = probe ⬝ᵥ probe + 2 * lift * (atom pivot ⬝ᵥ probe)
          + lift ^ 2 * (atom pivot ⬝ᵥ atom pivot) := by
      rw [hprobeDef]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, dotProduct_comm (atom pivot) direction]
      ring
    rw [hexpand, hpolar]
    have hgram : atom pivot ⬝ᵥ atom pivot = atomGram atom pivot pivot := rfl
    rw [hgram]
    ring
  have hpivotRead : atom pivot ⬝ᵥ direction = lift * atomGram atom pivot pivot := by
    rw [hread pivot, hpolar, zero_add]
  have hkey := hschur probe hpolar
  have hbudget : 0 < scale pivot * atomPivotWeight atom scale pivot slotOne slotTwo
      + atomGram atom pivot pivot * (atomGram atom pivot pivot - scale pivot) := by
    have hweight : 0 ≤ atomPivotWeight atom scale pivot slotOne slotTwo := by
      simp only [atomPivotWeight]
      positivity
    nlinarith [mul_pos hdiagPos (sub_pos.mpr hgap), mul_nonneg hpivotPos.le hweight]
  have hcell : ∀ slot : Fin 6, 0 < scale slot →
      (atom slot ⬝ᵥ direction) ^ 2 / scale slot
        = (atom slot ⬝ᵥ probe) ^ 2 / scale slot
          + 2 * lift * (atomGram atom pivot slot * (atom slot ⬝ᵥ probe) / scale slot)
          + lift ^ 2 * (atomGram atom pivot slot ^ 2 / scale slot) := by
    intro slot hslot
    rw [hread slot]
    field_simp
    ring
  rw [hcell slotOne honePos, hcell slotTwo htwoPos, henergy, hpivotRead]
  have hpivotSq : (lift * atomGram atom pivot pivot) ^ 2 / scale pivot
      = lift ^ 2 * atomGram atom pivot pivot ^ 2 / scale pivot := by ring
  rw [hpivotSq]
  have hsplit : lift ^ 2 * atomGram atom pivot pivot ^ 2 / scale pivot
      = lift ^ 2 * atomGram atom pivot pivot
        + lift ^ 2 * (atomGram atom pivot pivot
          * (atomGram atom pivot pivot - scale pivot)) / scale pivot := by
    field_simp
    ring
  rw [hsplit]
  have hgoal : probe ⬝ᵥ probe
      ≤ atomPivotPlaneRead atom scale slotOne slotTwo probe
        + 2 * lift * atomPivotCouple atom scale pivot slotOne slotTwo probe
        + lift ^ 2 * atomPivotWeight atom scale pivot slotOne slotTwo
        + lift ^ 2 * (atomGram atom pivot pivot
          * (atomGram atom pivot pivot - scale pivot)) / scale pivot := by
    have hscaled : lift ^ 2 * (atomGram atom pivot pivot
        * (atomGram atom pivot pivot - scale pivot)) / scale pivot * scale pivot
        = lift ^ 2 * (atomGram atom pivot pivot
          * (atomGram atom pivot pivot - scale pivot)) := by
      field_simp
    have hsquare : 0 ≤ (lift * (scale pivot * atomPivotWeight atom scale pivot slotOne slotTwo
          + atomGram atom pivot pivot * (atomGram atom pivot pivot - scale pivot))
        + scale pivot * atomPivotCouple atom scale pivot slotOne slotTwo probe) ^ 2 :=
      sq_nonneg _
    rw [← sub_nonneg]
    have hmul : 0 ≤ (atomPivotPlaneRead atom scale slotOne slotTwo probe
        + 2 * lift * atomPivotCouple atom scale pivot slotOne slotTwo probe
        + lift ^ 2 * atomPivotWeight atom scale pivot slotOne slotTwo
        + lift ^ 2 * (atomGram atom pivot pivot
          * (atomGram atom pivot pivot - scale pivot)) / scale pivot
        - probe ⬝ᵥ probe) * (scale pivot * (scale pivot
          * atomPivotWeight atom scale pivot slotOne slotTwo
          + atomGram atom pivot pivot
            * (atomGram atom pivot pivot - scale pivot))) := by
      have hexp : (atomPivotPlaneRead atom scale slotOne slotTwo probe
          + 2 * lift * atomPivotCouple atom scale pivot slotOne slotTwo probe
          + lift ^ 2 * atomPivotWeight atom scale pivot slotOne slotTwo
          + lift ^ 2 * (atomGram atom pivot pivot
            * (atomGram atom pivot pivot - scale pivot)) / scale pivot
          - probe ⬝ᵥ probe) * (scale pivot * (scale pivot
            * atomPivotWeight atom scale pivot slotOne slotTwo
            + atomGram atom pivot pivot
              * (atomGram atom pivot pivot - scale pivot)))
          = (lift * (scale pivot * atomPivotWeight atom scale pivot slotOne slotTwo
              + atomGram atom pivot pivot
                * (atomGram atom pivot pivot - scale pivot))
            + scale pivot * atomPivotCouple atom scale pivot slotOne slotTwo probe) ^ 2
            + ((scale pivot * atomPivotWeight atom scale pivot slotOne slotTwo
                + atomGram atom pivot pivot
                  * (atomGram atom pivot pivot - scale pivot))
              * (atomPivotPlaneRead atom scale slotOne slotTwo probe - probe ⬝ᵥ probe)
              - scale pivot
                * atomPivotCouple atom scale pivot slotOne slotTwo probe ^ 2)
              * scale pivot := by
        field_simp
        ring
      rw [hexp]
      have hslack : 0 ≤ (scale pivot * atomPivotWeight atom scale pivot slotOne slotTwo
          + atomGram atom pivot pivot
            * (atomGram atom pivot pivot - scale pivot))
        * (atomPivotPlaneRead atom scale slotOne slotTwo probe - probe ⬝ᵥ probe)
        - scale pivot * atomPivotCouple atom scale pivot slotOne slotTwo probe ^ 2 := by
        linarith [hkey]
      nlinarith [hsquare, mul_nonneg hslack hpivotPos.le]
    nlinarith [hmul, mul_pos hpivotPos hbudget]
  simp only [atomPivotPlaneRead, atomPivotCouple, atomPivotWeight] at hgoal
  linarith

end PivotPassage

end Gtz
