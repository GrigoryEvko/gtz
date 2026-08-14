import Gtz.Wave.WideSpectralAtomForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The parity strata of the wide spectral residue

The wide residue asks for a card-three carrier that dominates weakly.
This module closes two strata of it and measures EXACTLY what the sign
parity buys.

The tool is one identity.  On a probe supported by three slots the gap
between the blend energy and the scale energy is the ternary quadratic
form of the shifted diagonals and the Gram crosses.  Everything below is
a sufficient condition for that form to be nonnegative.

The FIRST stratum needs no sign.  When every cross has modulus at most a
bound and every shifted diagonal is at least TWICE that bound, the form
is diagonally dominant and EVERY triple dominates.

The SECOND stratum needs the sign.  When the Gram is equiangular of
modulus `cross`, the parity engine supplies a triple whose three crosses
are all `+cross` after one free sign flip, and then the form splits as a
nonnegative diagonal plus a nonnegative rank one.  The demand drops from
`2 * cross` to `cross` EXACTLY.

The factor two is the price of realness, and it is attained.  The real
icosahedral equiangular tight frame has `|a_y|² = 1/2`, uniform scales
`1/6`, shifted diagonal `1/3` and cross modulus `1/(2√5) = 0.2236`.  It
sits in the gap: `1/3 ≥ 0.2236` closes it through the parity, and
`1/3 < 0.4472` leaves it open to the sign-free stratum.  Its complex
counterpart, the two-trine, satisfies every hypothesis of the residue and
refutes its conclusion, and at the two-trine every triple product is
PURELY IMAGINARY — the real part of the parity term is annihilated.  That
is the measured separator of the two fields.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.wideTripleGap` — **THE TRIPLE GAP IDENTITY.**
* `Gtz.cross_ge_of_abs_le`, `Gtz.dominates_of_small_cross`,
  `Gtz.exists_dominating_triple_of_small_cross` — **THE SIGN-FREE
  STRATUM** at `2 * cross`.
* `Gtz.dominates_of_rankOne_cross`, `Gtz.dominates_of_equiangular_cross`
  — the rank-one and equiangular criteria.
* `Gtz.weakDominates_of_signFlip` — the sign gauge carries domination.
* `Gtz.wide_shiftedDiag_nonneg` — every shifted diagonal of a wide atom
  datum is nonnegative, because the free reading prices it.
* `Gtz.exists_dominating_triple_of_equiangular` — **THE EQUIANGULAR
  STRATUM**, at `cross` and not `2 * cross`.  This is the stratum of the
  icosahedral tight frame, the real analogue of the complex two-trine.
* `Gtz.atomTripleDet_parity_gain` — the determinant gain of a positive
  parity triple.

## Vacuity

Every statement is an unconditional matrix statement.  Nothing here is
quantified over a crux.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the triple gap identity -/

section TripleGap

/-- **THE TRIPLE GAP IDENTITY.**  On a probe supported by three slots the
gap between the blend energy and the scale energy is the ternary
quadratic form of the shifted diagonals and the Gram crosses. -/
theorem wideTripleGap {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) {slotOne slotTwo slotThree : Fin slotCount}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) {probe : Fin slotCount → ℝ}
    (hvanish : ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)),
      probe slot = 0) :
    atomBlend atom probe ⬝ᵥ atomBlend atom probe - ∑ slot, scale slot * probe slot ^ 2
      = atomShiftedDiag atom scale slotOne * probe slotOne ^ 2
        + atomShiftedDiag atom scale slotTwo * probe slotTwo ^ 2
        + atomShiftedDiag atom scale slotThree * probe slotThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * probe slotOne * probe slotTwo
        + 2 * atomGram atom slotOne slotThree * probe slotOne * probe slotThree
        + 2 * atomGram atom slotTwo slotThree * probe slotTwo * probe slotThree := by
  classical
  have hscaleSum : (∑ slot, scale slot * probe slot ^ 2)
      = scale slotOne * probe slotOne ^ 2 + scale slotTwo * probe slotTwo ^ 2
        + scale slotThree * probe slotThree ^ 2 :=
    sum_eq_triple_of_support honeTwo honeThree htwoThree
      fun slot hnot => by rw [hvanish slot hnot]; ring
  have hgramSum : atomBlend atom probe ⬝ᵥ atomBlend atom probe
      = (probe slotOne * probe slotOne * atomGram atom slotOne slotOne
          + probe slotOne * probe slotTwo * atomGram atom slotOne slotTwo
          + probe slotOne * probe slotThree * atomGram atom slotOne slotThree)
        + (probe slotTwo * probe slotOne * atomGram atom slotTwo slotOne
          + probe slotTwo * probe slotTwo * atomGram atom slotTwo slotTwo
          + probe slotTwo * probe slotThree * atomGram atom slotTwo slotThree)
        + (probe slotThree * probe slotOne * atomGram atom slotThree slotOne
          + probe slotThree * probe slotTwo * atomGram atom slotThree slotTwo
          + probe slotThree * probe slotThree * atomGram atom slotThree slotThree) := by
    rw [atomBlend_energy_eq_gram atom probe]
    have hinner : ∀ rowSlot : Fin slotCount,
        (∑ colSlot, probe rowSlot * probe colSlot * atomGram atom rowSlot colSlot)
          = probe rowSlot * probe slotOne * atomGram atom rowSlot slotOne
            + probe rowSlot * probe slotTwo * atomGram atom rowSlot slotTwo
            + probe rowSlot * probe slotThree * atomGram atom rowSlot slotThree :=
      fun rowSlot => sum_eq_triple_of_support honeTwo honeThree htwoThree
        fun colSlot hnot => by rw [hvanish colSlot hnot, mul_zero, zero_mul]
    rw [Finset.sum_congr rfl fun rowSlot _ => hinner rowSlot]
    refine sum_eq_triple_of_support honeTwo honeThree htwoThree ?_
    intro rowSlot hnot
    rw [hvanish rowSlot hnot]
    ring
  rw [hgramSum, hscaleSum]
  simp only [atomShiftedDiag]
  rw [atomGram_comm atom slotTwo slotOne, atomGram_comm atom slotThree slotOne,
    atomGram_comm atom slotThree slotTwo]
  ring

end TripleGap

/-! ## Layer 1 — the sign-free stratum -/

section SmallCross

/-- A cross term of bounded modulus never costs more than the bound
against the two squares. -/
theorem cross_ge_of_abs_le {cross bound valueOne valueTwo : ℝ}
    (hbound : |cross| ≤ bound) :
    -(bound * (valueOne ^ 2 + valueTwo ^ 2)) ≤ 2 * cross * valueOne * valueTwo := by
  have hnonneg : 0 ≤ bound := le_trans (abs_nonneg cross) hbound
  have hlow : -bound ≤ cross := neg_le_of_abs_le hbound
  have hhigh : cross ≤ bound := le_of_abs_le hbound
  rcases le_or_gt 0 (valueOne * valueTwo) with hsign | hsign
  · nlinarith [mul_nonneg hnonneg (sq_nonneg (valueOne - valueTwo)), hlow, hsign]
  · nlinarith [mul_nonneg hnonneg (sq_nonneg (valueOne + valueTwo)), hhigh, hsign]

/-- **THE SIGN-FREE CRITERION.**  A triple whose crosses have modulus at
most a bound and whose shifted diagonals are at least twice that bound
dominates weakly.  No sign, no parity, no selection. -/
theorem dominates_of_small_cross {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {slotOne slotTwo slotThree : Fin slotCount} {bound : ℝ}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hcrossOneTwo : |atomGram atom slotOne slotTwo| ≤ bound)
    (hcrossOneThree : |atomGram atom slotOne slotThree| ≤ bound)
    (hcrossTwoThree : |atomGram atom slotTwo slotThree| ≤ bound)
    (hdiagOne : 2 * bound ≤ atomShiftedDiag atom scale slotOne)
    (hdiagTwo : 2 * bound ≤ atomShiftedDiag atom scale slotTwo)
    (hdiagThree : 2 * bound ≤ atomShiftedDiag atom scale slotThree)
    {probe : Fin slotCount → ℝ}
    (hvanish : ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)),
      probe slot = 0) :
    (∑ slot, scale slot * probe slot ^ 2)
      ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  have hgap := wideTripleGap atom scale honeTwo honeThree htwoThree hvanish
  have hone := cross_ge_of_abs_le (valueOne := probe slotOne) (valueTwo := probe slotTwo)
    hcrossOneTwo
  have htwo := cross_ge_of_abs_le (valueOne := probe slotOne) (valueTwo := probe slotThree)
    hcrossOneThree
  have hthree := cross_ge_of_abs_le (valueOne := probe slotTwo) (valueTwo := probe slotThree)
    hcrossTwoThree
  nlinarith [hgap, hone, htwo, hthree, sq_nonneg (probe slotOne),
    sq_nonneg (probe slotTwo), sq_nonneg (probe slotThree), hdiagOne, hdiagTwo, hdiagThree]

end SmallCross

/-! ## Layer 2 — the rank-one cross and the equiangular criterion -/

section RankOneCross

/-- **THE RANK-ONE CROSS CRITERION.**  A triple whose three crosses
factor through one weight vector, and whose shifted diagonals dominate
the squared weights, dominates weakly: the gap splits as a nonnegative
diagonal plus a square. -/
theorem dominates_of_rankOne_cross {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount} {weightOne weightTwo weightThree : ℝ}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hcrossOneTwo : atomGram atom slotOne slotTwo = weightOne * weightTwo)
    (hcrossOneThree : atomGram atom slotOne slotThree = weightOne * weightThree)
    (hcrossTwoThree : atomGram atom slotTwo slotThree = weightTwo * weightThree)
    (hdiagOne : weightOne ^ 2 ≤ atomShiftedDiag atom scale slotOne)
    (hdiagTwo : weightTwo ^ 2 ≤ atomShiftedDiag atom scale slotTwo)
    (hdiagThree : weightThree ^ 2 ≤ atomShiftedDiag atom scale slotThree)
    {probe : Fin slotCount → ℝ}
    (hvanish : ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)),
      probe slot = 0) :
    (∑ slot, scale slot * probe slot ^ 2)
      ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  have hgap := wideTripleGap atom scale honeTwo honeThree htwoThree hvanish
  rw [hcrossOneTwo, hcrossOneThree, hcrossTwoThree] at hgap
  nlinarith [hgap, sq_nonneg (weightOne * probe slotOne + weightTwo * probe slotTwo
      + weightThree * probe slotThree),
    sq_nonneg (probe slotOne), sq_nonneg (probe slotTwo), sq_nonneg (probe slotThree),
    hdiagOne, hdiagTwo, hdiagThree]

/-- **THE EQUIANGULAR CRITERION.**  A triple whose three crosses are the
SAME nonnegative value and whose shifted diagonals are at least that
value dominates weakly.  The demand is `cross`, half of the sign-free
demand `2 * cross`. -/
theorem dominates_of_equiangular_cross {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount} {cross : ℝ}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) (hcrossNonneg : 0 ≤ cross)
    (hcrossOneTwo : atomGram atom slotOne slotTwo = cross)
    (hcrossOneThree : atomGram atom slotOne slotThree = cross)
    (hcrossTwoThree : atomGram atom slotTwo slotThree = cross)
    (hdiagOne : cross ≤ atomShiftedDiag atom scale slotOne)
    (hdiagTwo : cross ≤ atomShiftedDiag atom scale slotTwo)
    (hdiagThree : cross ≤ atomShiftedDiag atom scale slotThree)
    {probe : Fin slotCount → ℝ}
    (hvanish : ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)),
      probe slot = 0) :
    (∑ slot, scale slot * probe slot ^ 2)
      ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  have hroot : Real.sqrt cross * Real.sqrt cross = cross :=
    Real.mul_self_sqrt hcrossNonneg
  have hsquare : Real.sqrt cross ^ 2 = cross := by rw [pow_two]; exact hroot
  refine dominates_of_rankOne_cross (weightOne := Real.sqrt cross)
    (weightTwo := Real.sqrt cross) (weightThree := Real.sqrt cross)
    honeTwo honeThree htwoThree ?_ ?_ ?_ ?_ ?_ ?_ hvanish
  · rw [hcrossOneTwo, hroot]
  · rw [hcrossOneThree, hroot]
  · rw [hcrossTwoThree, hroot]
  · rw [hsquare]; exact hdiagOne
  · rw [hsquare]; exact hdiagTwo
  · rw [hsquare]; exact hdiagThree

/-- **THE PARITY GAIN OF THE DETERMINANT.**  A triple of nonnegative
parity carries the triple product term with a nonnegative sign, thus its
shifted determinant is at least the parity-free part.  This is the exact
arithmetic content of the sign. -/
theorem atomTripleDet_parity_gain {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount)
    (hparity : 0 ≤ atomGram atom slotOne slotTwo * atomGram atom slotOne slotThree
      * atomGram atom slotTwo slotThree) :
    atomShiftedDiag atom scale slotOne * atomShiftedDiag atom scale slotTwo
          * atomShiftedDiag atom scale slotThree
        - atomShiftedDiag atom scale slotOne * atomGram atom slotTwo slotThree ^ 2
        - atomShiftedDiag atom scale slotTwo * atomGram atom slotOne slotThree ^ 2
        - atomShiftedDiag atom scale slotThree * atomGram atom slotOne slotTwo ^ 2
      ≤ atomTripleDet atom scale slotOne slotTwo slotThree := by
  rw [atomTripleDet]
  linarith [hparity]

end RankOneCross

/-! ## Layer 3 — the sign gauge carries domination -/

section GaugeTransfer

/-- **THE SIGN GAUGE CARRIES DOMINATION.**  A carrier that dominates for
a flipped atom family dominates for the family itself. -/
theorem weakDominates_of_signFlip {sign : Fin 6 → ℝ}
    (hsign : ∀ slot, sign slot * sign slot = 1) {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} {car : Finset (Fin 6)}
    (hflip : ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
      (∑ slot, scale slot * probe slot ^ 2)
        ≤ atomBlend (wideSignFlip sign atom) probe
          ⬝ᵥ atomBlend (wideSignFlip sign atom) probe)
    (probe : Fin 6 → ℝ) (hvanish : ∀ slot ∉ car, probe slot = 0) :
    (∑ slot, scale slot * probe slot ^ 2)
      ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  have hstep := hflip (fun slot => sign slot * probe slot)
    fun slot hnot => by rw [hvanish slot hnot, mul_zero]
  rw [wideSignFlip_scale_energy hsign scale probe, wideSignFlip_blend] at hstep
  have hblend : atomBlend atom
        (fun slot => sign slot * (sign slot * probe slot)) = atomBlend atom probe := by
    funext index
    rw [atomBlend_apply, atomBlend_apply]
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [show sign slot * (sign slot * probe slot)
        = sign slot * sign slot * probe slot by ring, hsign slot, one_mul]
  rw [hblend] at hstep
  exact hstep

end GaugeTransfer

/-! ## Layer 4 — the two strata of the wide atom datum -/

section WideStrata

/-- **EVERY SHIFTED DIAGONAL OF A WIDE ATOM DATUM IS NONNEGATIVE.**  The
free reading prices it: the rank-two law puts the squared free reading
below the shifted diagonal. -/
theorem wide_shiftedDiag_nonneg {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    {free : Fin 3 → ℝ}
    (hrankTwo : ∀ slot, scale slot + (atom slot ⬝ᵥ free) ^ 2 ≤ atomGram atom slot slot)
    (slot : Fin 6) :
    (atom slot ⬝ᵥ free) ^ 2 ≤ atomShiftedDiag atom scale slot := by
  rw [atomShiftedDiag]
  linarith [hrankTwo slot]

/-- **THE SIGN-FREE STRATUM OF THE WIDE RESIDUE.**  When every cross has
modulus at most a bound and every shifted diagonal is at least twice that
bound, the very first triple dominates. -/
theorem exists_dominating_triple_of_small_cross {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} {bound : ℝ}
    (hcross : ∀ rowSlot colSlot : Fin 6, rowSlot ≠ colSlot →
      |atomGram atom rowSlot colSlot| ≤ bound)
    (hdiag : ∀ slot : Fin 6, 2 * bound ≤ atomShiftedDiag atom scale slot) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  refine ⟨{0, 1, 2}, card_triple_slots (by decide) (by decide) (by decide),
    fun probe hvanish => ?_⟩
  exact dominates_of_small_cross (by decide) (by decide) (by decide)
    (hcross 0 1 (by decide)) (hcross 0 2 (by decide)) (hcross 1 2 (by decide))
    (hdiag 0) (hdiag 1) (hdiag 2) hvanish

/-- **THE EQUIANGULAR STRATUM OF THE WIDE RESIDUE.**  When the Gram is
equiangular of modulus `cross` and every shifted diagonal is at least
`cross`, a dominating triple exists.

This is where the sign pays.  The parity engine supplies a triple whose
three crosses are all `+cross` after one free sign flip, the equiangular
criterion then closes it at `cross`, and the gauge carries the conclusion
back.  The sign-free stratum would demand `2 * cross`.

The stratum is not empty and it is not covered by the sign-free stratum:
the real icosahedral tight frame has `cross = 1/(2√5)` and shifted
diagonal `1/3` at uniform scales, thus `cross ≤ 1/3 < 2 * cross`. -/
theorem exists_dominating_triple_of_equiangular {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} {cross : ℝ}
    (hcross : ∀ rowSlot colSlot : Fin 6, rowSlot ≠ colSlot →
      |atomGram atom rowSlot colSlot| = cross)
    (hdiag : ∀ slot : Fin 6, cross ≤ atomShiftedDiag atom scale slot) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  have hcrossNonneg : 0 ≤ cross := by
    rw [← hcross 0 1 (by decide)]
    exact abs_nonneg _
  obtain ⟨sign, slotOne, slotTwo, hsign, honeNe, htwoNe, hpairNe, hgaugeOne, hgaugeTwo,
    hgaugeCross⟩ := exists_nonnegCross_triple atom 0
  have hflipAbs : ∀ rowSlot colSlot : Fin 6, rowSlot ≠ colSlot →
      |atomGram (wideSignFlip sign atom) rowSlot colSlot| = cross := by
    intro rowSlot colSlot hne
    rw [wideSignFlip_gram, abs_mul, abs_mul, hcross rowSlot colSlot hne]
    have habsOne : |sign rowSlot| = 1 := by
      have hsq : sign rowSlot ^ 2 = 1 := by rw [pow_two]; exact hsign rowSlot
      nlinarith [abs_nonneg (sign rowSlot), sq_abs (sign rowSlot), hsq]
    have habsTwo : |sign colSlot| = 1 := by
      have hsq : sign colSlot ^ 2 = 1 := by rw [pow_two]; exact hsign colSlot
      nlinarith [abs_nonneg (sign colSlot), sq_abs (sign colSlot), hsq]
    rw [habsOne, habsTwo, one_mul, one_mul]
  have hflipEq : ∀ rowSlot colSlot : Fin 6, rowSlot ≠ colSlot →
      0 ≤ atomGram (wideSignFlip sign atom) rowSlot colSlot →
      atomGram (wideSignFlip sign atom) rowSlot colSlot = cross := by
    intro rowSlot colSlot hne hnonneg
    rw [← hflipAbs rowSlot colSlot hne, abs_of_nonneg hnonneg]
  have hflipDiag : ∀ slot : Fin 6,
      cross ≤ atomShiftedDiag (wideSignFlip sign atom) scale slot := by
    intro slot
    rw [atomShiftedDiag, wideSignFlip_gram_diag hsign atom slot, ← atomShiftedDiag]
    exact hdiag slot
  refine ⟨{0, slotOne, slotTwo}, card_triple_slots (Ne.symm honeNe) (Ne.symm htwoNe) hpairNe,
    fun probe hvanish => ?_⟩
  refine weakDominates_of_signFlip hsign (fun flipProbe hflipVanish => ?_) probe hvanish
  exact dominates_of_equiangular_cross (Ne.symm honeNe) (Ne.symm htwoNe) hpairNe
    hcrossNonneg (hflipEq 0 slotOne (Ne.symm honeNe) hgaugeOne)
    (hflipEq 0 slotTwo (Ne.symm htwoNe) hgaugeTwo)
    (hflipEq slotOne slotTwo hpairNe hgaugeCross)
    (hflipDiag 0) (hflipDiag slotOne) (hflipDiag slotTwo) hflipVanish

end WideStrata

end Gtz
