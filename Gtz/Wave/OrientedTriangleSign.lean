import Gtz.Wave.AtomTriangleEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6400000

/-!
# The oriented triangle sign: the modulus bar, the fifth cell, and the cycle sum

Every certificate of the atom lane splits the shifted triple determinant into
a MODULUS part and a SIGN part.  Identity four of
`Gtz/Wave/AtomCoherentTriangle.lean` reads

  `atomTripleDet = atomTripleVolume - atomTripleReading + 2 * atomTriangleCycle`

and the first two terms are functions of the shifted diagonals and of the
SQUARES of the Gram entries alone.  The cycle is the only reading of a triple
that a square cannot reproduce.  This module measures exactly what that one
reading is worth, and it closes four questions of the lane.

## The modulus bar

The two integer triples `(2,1,0), (0,2,1), (1,0,2)` and
`(2,1,0), (0,2,1), (1,0,-2)` carry the SAME diagonal, the SAME squared Gram
entries, the SAME shifted diagonals and the SAME pair minors at the uniform
scale two.  Every reading that squares a Gram entry agrees on them.  Their
cycles are `+8` and `-8`, their shifted triple determinants are `+7` and
`-25`, and the first triple deflates while the second does not.

`Gtz.no_modulusCriterion_decides_atomTripleDeflates` turns that pair into an
impossibility theorem: NO criterion whose input is the shifted diagonal and
the squared Gram can be both sound and complete for the deflation test.  The
theorem kills a whole family of candidate criteria at once, and it explains
why the landed sign-free readings only ever cover strata.

## The fifth cell, and it is the anti-coherent one

The four cells of `Gtz/Wave/AtomCoherentTriangle.lean` all demand a
nonnegative cycle.  The MODULUS CELL demands the opposite thing: that the
modulus part beats twice the modulus of the cycle, so that the WORST
orientation still clears.  It is the first cell of the lane that fires at a
triple of negative cycle, and on the anti-coherent side it is EXACTLY sharp:
at a triple of nonpositive cycle the cell holds if and only if the
determinant is positive.

MEASURED (60000 random rank-three Parseval frames at scale mass one, exact
Gram, no whitener).  The six landed criteria together leave a residue of
0.96 percent.  At 574 of the 575 residue points EVERY dominating triple has a
NEGATIVE cycle, which is why no landed cell can fire there.  The modulus cell
fires at all 575, and at 99.99 percent of all data.  Its own worst case is
the icosahedral frame, where the modulus part is negative and only the four
coherent cells fire.  The two families are complementary, and the band
between them has width exactly `4 * |cycle|`.

## The cycle sum law

The oriented signs of a rank-three Parseval frame of six atoms are NOT free.
`Gtz.sum_atomTriangleCycle` proves

  `sum over the twenty triples of the cycle = (1/3) * sum of (diagonal - 1/2) ^ 3`

so the total oriented sign is a function of the DIAGONAL alone.  The proof is
three applications of the idempotent law and one trace law.  At a balanced
frame, where every diagonal is one half, the total is exactly zero: the
coherent and the anti-coherent triples balance.  The icosahedral frame is
such a datum, and it splits ten against ten.

`Gtz.atomPivotCycleSum` is the same law at one pivot, and it reads the
leverage-weighted row energy of that pivot.

## The pivot charge shadow, and a real-only supply

`Gtz.atomTriangleGap_eq_edge_mul_atomPivotCross` merges the coherent triangle
lane and the pivot lift lane: the triangle gap at an apex is the opposite
edge against the deflated cross.  The CHARGE SHADOW of a slot at a pivot is
the vector `P(p,y) * P(p,p) . a_y - P(p,y) ^ 2 . a_p`.  It is orthogonal to
the pivot atom, and the dot product of two charge shadows is the pivot
diagonal against `Gtz.atomChargeSign`, the raw form of the sign that the
pivot Schur route consumes.

Five charge shadows live in the plane orthogonal to the pivot atom.  At most
THREE vectors of a plane are pairwise obtuse, so a family of four in that
plane always carries a nonnegative pair.  Applying that twice gives TWO
distinct pairs of nonnegative charge sign at every pivot.  Over the complex
field the same count is ZERO, because five vectors of a four-dimensional real
space carry no obtuse bound.  The count two is attained.

## MEASURED, and recorded so that no successor repeats it

* Restricting the selection to STRICTLY coherent triples costs `0.444` at
  scale mass one, at a datum with every leverage above `1/20` and every scale
  above `1/50`.  Coherence is a certificate and never a selection rule.
* 19.98 percent of random data carries NO dominating coherent triple.
* The coherent-triple count of random data takes only the values 8, 10 and
  12, and the adversarial floor is 8.  Every slot lies on at least two
  coherent triples.
* The weighted maximal-volume selection, the argmax of `det P_T` against the
  product of the scales, fails with floor `-0.066`.  It reads only moduli, so
  the modulus bar predicts the failure.
* Every weighted average of the twenty shifted determinants that was tried
  goes negative: the plain sum, the determinantal weight, the positive-cycle
  weight and the product of the two.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomTripleModulus`, `Gtz.atomTripleDet_eq_modulus_add_cycle`,
  `Gtz.atomTripleDet_orientation_band` — **THE ORIENTATION SPLIT.**
* `Gtz.atomTripleDet_pos_of_modulusEnergy`,
  `Gtz.exists_deflated_pair_of_modulusEnergy` — **THE MODULUS CELL.**
* `Gtz.modulusEnergy_of_tripleDet_pos_of_nonpos_cycle`,
  `Gtz.atomTripleDet_pos_iff_modulusEnergy_of_nonpos_cycle` — the cell is
  SHARP on the anti-coherent side.
* `Gtz.atomTripleModulus_nonneg_of_small_cross` — the cell meets the
  sign-free stratum exactly at `2 * cross`.
* `Gtz.orientedBarCoherentAtom`, `Gtz.orientedBarAntiAtom` and their laws,
  `Gtz.no_modulusCriterion_decides_atomTripleDeflates` — **THE MODULUS BAR.**
* `Gtz.IsTrineSignature`, `Gtz.trineSignature_tripleDet`,
  `Gtz.trineSignature_decided_by_cycle`,
  `Gtz.icosaFrameAtom_isTrineSignature` — **THE SIGN DECIDES AT THE TRINE
  SIGNATURE**, and the threshold sits strictly inside the modulus band.
* `Gtz.atomCycleSum`, `Gtz.sum_atomTriangleCycle`,
  `Gtz.atomCycleSum_eq_zero_of_balanced`, `Gtz.atomPivotCycleSum` — **THE
  CYCLE SUM LAWS.**
* `Gtz.atomTriangleGap_eq_edge_mul_atomPivotCross`, `Gtz.atomChargeShadow`,
  `Gtz.atomChargeSign`, `Gtz.exists_nonneg_dot_of_orthogonal_four`,
  `Gtz.exists_two_nonneg_atomChargeSign` — **THE PIVOT CHARGE SUPPLY.**

## Vacuity

Layers zero, one, four and five are unconditional statements about a family
of vectors, a family of scales and three slots.  Layer two exhibits two
explicit integer families and computes every reading of them.  Layer three
has the landed icosahedral frame as a witness, so its hypothesis package is
satisfiable.
-/

namespace Gtz

/-! ## Layer 0 — the orientation split of the shifted triple determinant -/

/-- The MODULUS PART of the shifted triple determinant: the volume of the
three shifted diagonals against the reading of the three squared edges.  It
is a function of the shifted diagonals and of the SQUARES of the Gram entries
alone, so no orientation and no sign enter it. -/
def atomTripleModulus {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  atomTripleVolume atom scale slotOne slotTwo slotThree
    - atomTripleReading atom scale slotOne slotTwo slotThree

/-- **THE ORIENTATION SPLIT.**  The shifted triple determinant is the modulus
part plus twice the oriented cycle.  This is identity four of the coherent
triangle module, arranged so that the sign sits alone on one side. -/
theorem atomTripleDet_eq_modulus_add_cycle {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    atomTripleDet atom scale slotOne slotTwo slotThree
      = atomTripleModulus atom scale slotOne slotTwo slotThree
        + 2 * atomTriangleCycle atom slotOne slotTwo slotThree := by
  rw [atomTripleModulus, atomTripleDet_eq_energy atom scale slotOne slotTwo slotThree]
  ring

/-- The modulus part is written out in the raw readings. -/
theorem atomTripleModulus_eq {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    atomTripleModulus atom scale slotOne slotTwo slotThree
      = atomShiftedDiag atom scale slotOne * atomShiftedDiag atom scale slotTwo
          * atomShiftedDiag atom scale slotThree
        - atomShiftedDiag atom scale slotOne * atomGram atom slotTwo slotThree ^ 2
        - atomShiftedDiag atom scale slotTwo * atomGram atom slotOne slotThree ^ 2
        - atomShiftedDiag atom scale slotThree * atomGram atom slotOne slotTwo ^ 2 := by
  simp only [atomTripleModulus, atomTripleVolume, atomTripleReading]
  ring

/-- **THE MODULUS PART IS GAUGE INVARIANT.**  Seidel switching fixes the
shifted diagonal and every squared Gram entry. -/
theorem atomTripleModulus_atomSwitch {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    {sign : Fin slotCount → ℝ} {slotOne slotTwo slotThree : Fin slotCount}
    (hone : sign slotOne ^ 2 = 1) (htwo : sign slotTwo ^ 2 = 1)
    (hthree : sign slotThree ^ 2 = 1) :
    atomTripleModulus (atomSwitch atom sign) scale slotOne slotTwo slotThree
      = atomTripleModulus atom scale slotOne slotTwo slotThree := by
  simp only [atomTripleModulus, atomTripleVolume, atomTripleReading, atomGram_atomSwitch,
    atomShiftedDiag_atomSwitch atom scale hone,
    atomShiftedDiag_atomSwitch atom scale htwo,
    atomShiftedDiag_atomSwitch atom scale hthree, sign_pair_mul_sq hone htwo,
    sign_pair_mul_sq hone hthree, sign_pair_mul_sq htwo hthree]

/-- **THE ORIENTED SIGN IS WORTH EXACTLY FOUR TIMES THE CYCLE MODULUS.**  The
determinant of the best orientation minus the determinant of the worst one is
`4 * |cycle|`, and the modulus data determines neither endpoint alone. -/
theorem atomTripleDet_orientation_band {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    (atomTripleModulus atom scale slotOne slotTwo slotThree
          + 2 * |atomTriangleCycle atom slotOne slotTwo slotThree|)
        - (atomTripleModulus atom scale slotOne slotTwo slotThree
          - 2 * |atomTriangleCycle atom slotOne slotTwo slotThree|)
      = 4 * |atomTriangleCycle atom slotOne slotTwo slotThree| := by
  ring

/-- The determinant never leaves the orientation band, on the low side. -/
theorem atomTripleModulus_sub_le_atomTripleDet {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    atomTripleModulus atom scale slotOne slotTwo slotThree
        - 2 * |atomTriangleCycle atom slotOne slotTwo slotThree|
      ≤ atomTripleDet atom scale slotOne slotTwo slotThree := by
  rw [atomTripleDet_eq_modulus_add_cycle atom scale slotOne slotTwo slotThree]
  have habs := neg_abs_le (atomTriangleCycle atom slotOne slotTwo slotThree)
  linarith

/-- The determinant never leaves the orientation band, on the high side. -/
theorem atomTripleDet_le_atomTripleModulus_add {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    atomTripleDet atom scale slotOne slotTwo slotThree
      ≤ atomTripleModulus atom scale slotOne slotTwo slotThree
        + 2 * |atomTriangleCycle atom slotOne slotTwo slotThree| := by
  rw [atomTripleDet_eq_modulus_add_cycle atom scale slotOne slotTwo slotThree]
  have habs := le_abs_self (atomTriangleCycle atom slotOne slotTwo slotThree)
  linarith

/-- **THE COHERENT SIDE, SHARPLY.**  At a triple of nonnegative cycle the
determinant is positive exactly when the modulus part beats the negated
orientation band. -/
theorem atomTripleDet_pos_iff_of_nonneg_cycle {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hcycle : 0 ≤ atomTriangleCycle atom slotOne slotTwo slotThree) :
    0 < atomTripleDet atom scale slotOne slotTwo slotThree
      ↔ -(2 * |atomTriangleCycle atom slotOne slotTwo slotThree|)
          < atomTripleModulus atom scale slotOne slotTwo slotThree := by
  rw [atomTripleDet_eq_modulus_add_cycle atom scale slotOne slotTwo slotThree,
    abs_of_nonneg hcycle]
  constructor <;> intro hstep <;> linarith

/-- **THE ANTI-COHERENT SIDE, SHARPLY.**  At a triple of nonpositive cycle the
determinant is positive exactly when the modulus part beats twice the cycle
modulus.  This is the exact statement that the modulus cell of layer one is
not a loss on the anti-coherent stratum. -/
theorem atomTripleDet_pos_iff_modulusEnergy_of_nonpos_cycle {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hcycle : atomTriangleCycle atom slotOne slotTwo slotThree ≤ 0) :
    0 < atomTripleDet atom scale slotOne slotTwo slotThree
      ↔ 2 * |atomTriangleCycle atom slotOne slotTwo slotThree|
          < atomTripleModulus atom scale slotOne slotTwo slotThree := by
  rw [atomTripleDet_eq_modulus_add_cycle atom scale slotOne slotTwo slotThree,
    abs_of_nonpos hcycle]
  constructor <;> intro hstep <;> linarith

/-! ## Layer 1 — the modulus cell, the first anti-coherent cell of the lane -/

/-- **THE MODULUS CELL, DETERMINANT FORM.**  When the modulus part beats twice
the cycle modulus the determinant is positive, whatever the orientation is.
No sign is read at all, and the cell fires at triples of negative cycle where
every coherent cell is silent. -/
theorem atomTripleDet_pos_of_modulusEnergy {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hmodulus : 2 * |atomTriangleCycle atom slotOne slotTwo slotThree|
      < atomTripleModulus atom scale slotOne slotTwo slotThree) :
    0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  have hlow := atomTripleModulus_sub_le_atomTripleDet atom scale slotOne slotTwo slotThree
  linarith

/-- **THE MODULUS CELL IN RAW READINGS**, division free and square root free.
Twice the modulus of the cycle, plus the reading of the three squared edges,
below the volume of the three shifted diagonals. -/
theorem atomTripleDet_pos_of_modulusEnergy_raw {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hraw : 2 * |atomGram atom slotOne slotTwo * atomGram atom slotOne slotThree
            * atomGram atom slotTwo slotThree|
          + atomShiftedDiag atom scale slotOne * atomGram atom slotTwo slotThree ^ 2
          + atomShiftedDiag atom scale slotTwo * atomGram atom slotOne slotThree ^ 2
          + atomShiftedDiag atom scale slotThree * atomGram atom slotOne slotTwo ^ 2
        < atomShiftedDiag atom scale slotOne * atomShiftedDiag atom scale slotTwo
          * atomShiftedDiag atom scale slotThree) :
    0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  refine atomTripleDet_pos_of_modulusEnergy ?_
  rw [atomTripleModulus_eq, atomTriangleCycle]
  linarith

/-- **THE MODULUS CELL IS SHARP ON THE ANTI-COHERENT SIDE.**  Every triple of
nonpositive cycle whose determinant is positive already satisfies the cell,
so nothing is lost there.  This is why the cell covers the whole measured
residue of the four coherent cells. -/
theorem modulusEnergy_of_tripleDet_pos_of_nonpos_cycle {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hcycle : atomTriangleCycle atom slotOne slotTwo slotThree ≤ 0)
    (hdet : 0 < atomTripleDet atom scale slotOne slotTwo slotThree) :
    2 * |atomTriangleCycle atom slotOne slotTwo slotThree|
      < atomTripleModulus atom scale slotOne slotTwo slotThree :=
  (atomTripleDet_pos_iff_modulusEnergy_of_nonpos_cycle hcycle).mp hdet

/-- **THE MODULUS CELL, IN THE FORM THE RESIDUE CONSUMES.**  Three distinct
slots that are live and carry one positive pair minor and the modulus energy
supply the deflated pair of the blocked residue, at the first slot as pivot.
Compare `Gtz.exists_deflated_pair_of_coherentGaps`, which needs a positive
cycle: this one needs none. -/
theorem exists_deflated_pair_of_modulusEnergy {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hdiagOne : 0 < atomShiftedDiag atom scale slotOne)
    (hminor : 0 < atomPairMinor atom scale slotOne slotTwo)
    (hmodulus : 2 * |atomTriangleCycle atom slotOne slotTwo slotThree|
      < atomTripleModulus atom scale slotOne slotTwo slotThree) :
    ∃ pivot firstSlot secondSlot : Fin 6,
      pivot ≠ firstSlot ∧ pivot ≠ secondSlot ∧ firstSlot ≠ secondSlot
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot firstSlot
        ∧ atomPivotCross atom scale pivot firstSlot secondSlot ^ 2
            < atomPairMinor atom scale pivot firstSlot
              * atomPairMinor atom scale pivot secondSlot := by
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hdiagOne, hminor, ?_⟩
  exact deflated_pair_of_tripleDet_pos hdiagOne
    (atomTripleDet_pos_of_modulusEnergy hmodulus)

/-- **THE MODULUS CELL DEFLATES**, in the named predicate of the lane. -/
theorem atomTripleDeflates_of_modulusEnergy {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hdiagOne : 0 < atomShiftedDiag atom scale slotOne)
    (hminor : 0 < atomPairMinor atom scale slotOne slotTwo)
    (hmodulus : 2 * |atomTriangleCycle atom slotOne slotTwo slotThree|
      < atomTripleModulus atom scale slotOne slotTwo slotThree) :
    AtomTripleDeflates atom scale slotOne slotTwo slotThree :=
  ⟨hdiagOne, hminor,
    deflated_pair_of_tripleDet_pos hdiagOne (atomTripleDet_pos_of_modulusEnergy hmodulus)⟩

/-- **THE CELL MEETS THE SIGN-FREE STRATUM EXACTLY AT `2 * cross`.**  When
every edge has modulus at most a bound and every shifted diagonal is at least
twice that bound, the modulus part already beats twice the cycle modulus,
with equality exactly at the corner.  So the modulus cell recovers
`Gtz.dominates_of_small_cross` and is strictly wider off the corner. -/
theorem atomTripleModulus_nonneg_of_small_cross {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount} {bound : ℝ}
    (hboundNonneg : 0 ≤ bound)
    (hcrossOneTwo : |atomGram atom slotOne slotTwo| ≤ bound)
    (hcrossOneThree : |atomGram atom slotOne slotThree| ≤ bound)
    (hcrossTwoThree : |atomGram atom slotTwo slotThree| ≤ bound)
    (hdiagOne : 2 * bound ≤ atomShiftedDiag atom scale slotOne)
    (hdiagTwo : 2 * bound ≤ atomShiftedDiag atom scale slotTwo)
    (hdiagThree : 2 * bound ≤ atomShiftedDiag atom scale slotThree) :
    2 * |atomTriangleCycle atom slotOne slotTwo slotThree|
      ≤ atomTripleModulus atom scale slotOne slotTwo slotThree := by
  have hsqOneTwo : atomGram atom slotOne slotTwo ^ 2 ≤ bound ^ 2 := by
    nlinarith [sq_abs (atomGram atom slotOne slotTwo), abs_nonneg (atomGram atom slotOne slotTwo),
      hcrossOneTwo, hboundNonneg]
  have hsqOneThree : atomGram atom slotOne slotThree ^ 2 ≤ bound ^ 2 := by
    nlinarith [sq_abs (atomGram atom slotOne slotThree), abs_nonneg (atomGram atom slotOne slotThree),
      hcrossOneThree, hboundNonneg]
  have hsqTwoThree : atomGram atom slotTwo slotThree ^ 2 ≤ bound ^ 2 := by
    nlinarith [sq_abs (atomGram atom slotTwo slotThree), abs_nonneg (atomGram atom slotTwo slotThree),
      hcrossTwoThree, hboundNonneg]
  have hcycleAbs : |atomTriangleCycle atom slotOne slotTwo slotThree| ≤ bound ^ 3 := by
    rw [atomTriangleCycle, abs_mul, abs_mul]
    have hstep : |atomGram atom slotOne slotTwo| * |atomGram atom slotOne slotThree|
        ≤ bound * bound :=
      mul_le_mul hcrossOneTwo hcrossOneThree (abs_nonneg _) hboundNonneg
    calc |atomGram atom slotOne slotTwo| * |atomGram atom slotOne slotThree|
            * |atomGram atom slotTwo slotThree|
        ≤ (bound * bound) * bound :=
          mul_le_mul hstep hcrossTwoThree (abs_nonneg _)
            (mul_nonneg hboundNonneg hboundNonneg)
      _ = bound ^ 3 := by ring
  rw [atomTripleModulus_eq]
  set restOne := atomShiftedDiag atom scale slotOne with hrestOne
  set restTwo := atomShiftedDiag atom scale slotTwo with hrestTwo
  set restThree := atomShiftedDiag atom scale slotThree with hrestThree
  have hslackOne : 0 ≤ restOne - 2 * bound := by linarith
  have hslackTwo : 0 ≤ restTwo - 2 * bound := by linarith
  have hslackThree : 0 ≤ restThree - 2 * bound := by linarith
  have hrestOnePos : 0 ≤ restOne := by linarith
  have hrestTwoPos : 0 ≤ restTwo := by linarith
  have hrestThreePos : 0 ≤ restThree := by linarith
  nlinarith [hcycleAbs, hsqOneTwo, hsqOneThree, hsqTwoThree, hslackOne, hslackTwo,
    hslackThree, hrestOnePos, hrestTwoPos, hrestThreePos,
    mul_nonneg hslackOne hslackTwo, mul_nonneg hslackOne hslackThree,
    mul_nonneg hslackTwo hslackThree,
    mul_nonneg (mul_nonneg hslackOne hslackTwo) hslackThree,
    mul_nonneg hboundNonneg (mul_nonneg hslackOne hslackTwo),
    mul_nonneg hboundNonneg (mul_nonneg hslackOne hslackThree),
    mul_nonneg hboundNonneg (mul_nonneg hslackTwo hslackThree),
    mul_nonneg (mul_nonneg hboundNonneg hboundNonneg) hslackOne,
    mul_nonneg (mul_nonneg hboundNonneg hboundNonneg) hslackTwo,
    mul_nonneg (mul_nonneg hboundNonneg hboundNonneg) hslackThree]

/-! ## Layer 2 — the modulus bar

Two integer triples of three-space that every squared reading confuses.  The
first has the cycle `+8`, the second the cycle `-8`, and nothing else about
them differs. -/

/-- The COHERENT arm of the modulus bar. -/
def orientedBarCoherentAtom : Fin 3 → (Fin 3 → ℝ)
  | 0 => ![2, 1, 0]
  | 1 => ![0, 2, 1]
  | 2 => ![1, 0, 2]

/-- The ANTI-COHERENT arm of the modulus bar.  Only the last coordinate of the
last atom differs from the coherent arm. -/
def orientedBarAntiAtom : Fin 3 → (Fin 3 → ℝ)
  | 0 => ![2, 1, 0]
  | 1 => ![0, 2, 1]
  | 2 => ![1, 0, -2]

/-- The uniform scale of the modulus bar. -/
def orientedBarScale : Fin 3 → ℝ := fun _ => 2

theorem orientedBarScale_apply (slot : Fin 3) : orientedBarScale slot = 2 := rfl

theorem orientedBarCoherent_gram_zero_zero :
    atomGram orientedBarCoherentAtom 0 0 = 5 := by
  simp only [atomGram, orientedBarCoherentAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

theorem orientedBarCoherent_gram_one_one :
    atomGram orientedBarCoherentAtom 1 1 = 5 := by
  simp only [atomGram, orientedBarCoherentAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

theorem orientedBarCoherent_gram_two_two :
    atomGram orientedBarCoherentAtom 2 2 = 5 := by
  simp only [atomGram, orientedBarCoherentAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

theorem orientedBarCoherent_gram_zero_one :
    atomGram orientedBarCoherentAtom 0 1 = 2 := by
  simp only [atomGram, orientedBarCoherentAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

theorem orientedBarCoherent_gram_zero_two :
    atomGram orientedBarCoherentAtom 0 2 = 2 := by
  simp only [atomGram, orientedBarCoherentAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

theorem orientedBarCoherent_gram_one_two :
    atomGram orientedBarCoherentAtom 1 2 = 2 := by
  simp only [atomGram, orientedBarCoherentAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

theorem orientedBarAnti_gram_zero_zero :
    atomGram orientedBarAntiAtom 0 0 = 5 := by
  simp only [atomGram, orientedBarAntiAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

theorem orientedBarAnti_gram_one_one :
    atomGram orientedBarAntiAtom 1 1 = 5 := by
  simp only [atomGram, orientedBarAntiAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

theorem orientedBarAnti_gram_two_two :
    atomGram orientedBarAntiAtom 2 2 = 5 := by
  simp only [atomGram, orientedBarAntiAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

theorem orientedBarAnti_gram_zero_one :
    atomGram orientedBarAntiAtom 0 1 = 2 := by
  simp only [atomGram, orientedBarAntiAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

theorem orientedBarAnti_gram_zero_two :
    atomGram orientedBarAntiAtom 0 2 = 2 := by
  simp only [atomGram, orientedBarAntiAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

theorem orientedBarAnti_gram_one_two :
    atomGram orientedBarAntiAtom 1 2 = -2 := by
  simp only [atomGram, orientedBarAntiAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

/-- **THE TWO ARMS SHARE EVERY DIAGONAL.** -/
theorem orientedBar_gram_diag_eq (slot : Fin 3) :
    atomGram orientedBarCoherentAtom slot slot = atomGram orientedBarAntiAtom slot slot := by
  match slot with
  | 0 => rw [orientedBarCoherent_gram_zero_zero, orientedBarAnti_gram_zero_zero]
  | 1 => rw [orientedBarCoherent_gram_one_one, orientedBarAnti_gram_one_one]
  | 2 => rw [orientedBarCoherent_gram_two_two, orientedBarAnti_gram_two_two]

/-- **THE TWO ARMS SHARE EVERY SQUARED GRAM ENTRY.**  Every reading of the
lane that squares a Gram entry therefore agrees on them. -/
theorem orientedBar_gram_sq_eq (rowSlot colSlot : Fin 3) :
    atomGram orientedBarCoherentAtom rowSlot colSlot ^ 2
      = atomGram orientedBarAntiAtom rowSlot colSlot ^ 2 := by
  have hcomm : ∀ (atom : Fin 3 → (Fin 3 → ℝ)) (rowIndex colIndex : Fin 3),
      atomGram atom rowIndex colIndex = atomGram atom colIndex rowIndex :=
    fun atom rowIndex colIndex => atomGram_comm atom rowIndex colIndex
  match rowSlot, colSlot with
  | 0, 0 => rw [orientedBarCoherent_gram_zero_zero, orientedBarAnti_gram_zero_zero]
  | 0, 1 => rw [orientedBarCoherent_gram_zero_one, orientedBarAnti_gram_zero_one]
  | 0, 2 => rw [orientedBarCoherent_gram_zero_two, orientedBarAnti_gram_zero_two]
  | 1, 0 => rw [hcomm orientedBarCoherentAtom 1 0, hcomm orientedBarAntiAtom 1 0,
      orientedBarCoherent_gram_zero_one, orientedBarAnti_gram_zero_one]
  | 1, 1 => rw [orientedBarCoherent_gram_one_one, orientedBarAnti_gram_one_one]
  | 1, 2 => rw [orientedBarCoherent_gram_one_two, orientedBarAnti_gram_one_two]; norm_num
  | 2, 0 => rw [hcomm orientedBarCoherentAtom 2 0, hcomm orientedBarAntiAtom 2 0,
      orientedBarCoherent_gram_zero_two, orientedBarAnti_gram_zero_two]
  | 2, 1 => rw [hcomm orientedBarCoherentAtom 2 1, hcomm orientedBarAntiAtom 2 1,
      orientedBarCoherent_gram_one_two, orientedBarAnti_gram_one_two]; norm_num
  | 2, 2 => rw [orientedBarCoherent_gram_two_two, orientedBarAnti_gram_two_two]

/-- **THE TWO ARMS SHARE EVERY SHIFTED DIAGONAL.** -/
theorem orientedBar_shiftedDiag_eq (slot : Fin 3) :
    atomShiftedDiag orientedBarCoherentAtom orientedBarScale slot
      = atomShiftedDiag orientedBarAntiAtom orientedBarScale slot := by
  simp only [atomShiftedDiag, orientedBar_gram_diag_eq slot]

/-- The shifted diagonal of the modulus bar is three at every slot. -/
theorem orientedBar_shiftedDiag_coherent (slot : Fin 3) :
    atomShiftedDiag orientedBarCoherentAtom orientedBarScale slot = 3 := by
  simp only [atomShiftedDiag, orientedBarScale_apply]
  match slot with
  | 0 => rw [orientedBarCoherent_gram_zero_zero]; norm_num
  | 1 => rw [orientedBarCoherent_gram_one_one]; norm_num
  | 2 => rw [orientedBarCoherent_gram_two_two]; norm_num

theorem orientedBar_shiftedDiag_anti (slot : Fin 3) :
    atomShiftedDiag orientedBarAntiAtom orientedBarScale slot = 3 := by
  rw [← orientedBar_shiftedDiag_eq slot, orientedBar_shiftedDiag_coherent slot]

/-- **THE TWO ARMS SHARE EVERY PAIR MINOR**, because a pair minor squares its
Gram entry. -/
theorem orientedBar_pairMinor_eq (rowSlot colSlot : Fin 3) :
    atomPairMinor orientedBarCoherentAtom orientedBarScale rowSlot colSlot
      = atomPairMinor orientedBarAntiAtom orientedBarScale rowSlot colSlot := by
  simp only [atomPairMinor, orientedBar_shiftedDiag_eq, orientedBar_gram_sq_eq]

/-- Every pair minor of the modulus bar is five. -/
theorem orientedBar_pairMinor_coherent :
    atomPairMinor orientedBarCoherentAtom orientedBarScale 0 1 = 5 := by
  simp only [atomPairMinor, orientedBar_shiftedDiag_coherent,
    orientedBarCoherent_gram_zero_one]
  norm_num

/-- **THE TWO ARMS SHARE THE VOLUME AND THE READING**, so they share the whole
modulus part of the determinant. -/
theorem orientedBar_modulus_eq :
    atomTripleModulus orientedBarCoherentAtom orientedBarScale 0 1 2
      = atomTripleModulus orientedBarAntiAtom orientedBarScale 0 1 2 := by
  simp only [atomTripleModulus_eq, orientedBar_shiftedDiag_eq, orientedBar_gram_sq_eq]

/-- The shared modulus part of the modulus bar is `-9`. -/
theorem orientedBar_modulus_coherent :
    atomTripleModulus orientedBarCoherentAtom orientedBarScale 0 1 2 = -9 := by
  rw [atomTripleModulus_eq, orientedBar_shiftedDiag_coherent, orientedBar_shiftedDiag_coherent,
    orientedBar_shiftedDiag_coherent, orientedBarCoherent_gram_zero_one,
    orientedBarCoherent_gram_zero_two, orientedBarCoherent_gram_one_two]
  norm_num

/-- **THE CYCLES ARE OPPOSITE**, and this is the only reading that separates
the two arms. -/
theorem orientedBarCoherent_cycle :
    atomTriangleCycle orientedBarCoherentAtom 0 1 2 = 8 := by
  rw [atomTriangleCycle, orientedBarCoherent_gram_zero_one,
    orientedBarCoherent_gram_zero_two, orientedBarCoherent_gram_one_two]
  norm_num

theorem orientedBarAnti_cycle :
    atomTriangleCycle orientedBarAntiAtom 0 1 2 = -8 := by
  rw [atomTriangleCycle, orientedBarAnti_gram_zero_one,
    orientedBarAnti_gram_zero_two, orientedBarAnti_gram_one_two]
  norm_num

/-- The two arms share the MODULUS of the cycle, so even the unsigned cycle is
a shared reading. -/
theorem orientedBar_abs_cycle_eq :
    |atomTriangleCycle orientedBarCoherentAtom 0 1 2|
      = |atomTriangleCycle orientedBarAntiAtom 0 1 2| := by
  rw [orientedBarCoherent_cycle, orientedBarAnti_cycle]
  norm_num

/-- **THE COHERENT ARM HAS DETERMINANT SEVEN.** -/
theorem orientedBarCoherent_tripleDet :
    atomTripleDet orientedBarCoherentAtom orientedBarScale 0 1 2 = 7 := by
  rw [atomTripleDet_eq_modulus_add_cycle, orientedBar_modulus_coherent,
    orientedBarCoherent_cycle]
  norm_num

/-- **THE ANTI-COHERENT ARM HAS DETERMINANT MINUS TWENTY-FIVE.** -/
theorem orientedBarAnti_tripleDet :
    atomTripleDet orientedBarAntiAtom orientedBarScale 0 1 2 = -25 := by
  rw [atomTripleDet_eq_modulus_add_cycle, ← orientedBar_modulus_eq,
    orientedBar_modulus_coherent, orientedBarAnti_cycle]
  norm_num

/-- The difference of the two determinants is four times the cycle modulus,
which is the orientation band of layer zero read at the bar. -/
theorem orientedBar_det_gap :
    atomTripleDet orientedBarCoherentAtom orientedBarScale 0 1 2
        - atomTripleDet orientedBarAntiAtom orientedBarScale 0 1 2
      = 4 * |atomTriangleCycle orientedBarCoherentAtom 0 1 2| := by
  rw [orientedBarCoherent_tripleDet, orientedBarAnti_tripleDet, orientedBarCoherent_cycle]
  norm_num

/-- **THE COHERENT ARM DEFLATES.** -/
theorem orientedBarCoherent_deflates :
    AtomTripleDeflates orientedBarCoherentAtom orientedBarScale 0 1 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [orientedBar_shiftedDiag_coherent]; norm_num
  · rw [orientedBar_pairMinor_coherent]; norm_num
  · refine deflated_pair_of_tripleDet_pos ?_ ?_
    · rw [orientedBar_shiftedDiag_coherent]; norm_num
    · rw [orientedBarCoherent_tripleDet]; norm_num

/-- **THE ANTI-COHERENT ARM DOES NOT DEFLATE**, because its determinant is
negative while its pivot is live. -/
theorem orientedBarAnti_not_deflates :
    ¬ AtomTripleDeflates orientedBarAntiAtom orientedBarScale 0 1 2 := by
  intro hdeflates
  obtain ⟨hdiag, hminor, hcross⟩ := hdeflates
  have hdeflate := atomTripleDet_deflate orientedBarAntiAtom orientedBarScale 0 1 2
  have hdet : atomTripleDet orientedBarAntiAtom orientedBarScale 0 1 2 = -25 :=
    orientedBarAnti_tripleDet
  have hdiagValue : atomShiftedDiag orientedBarAntiAtom orientedBarScale 0 = 3 :=
    orientedBar_shiftedDiag_anti 0
  nlinarith [hdeflate, hcross, hdet, hdiagValue,
    sq_nonneg (atomPivotCross orientedBarAntiAtom orientedBarScale 0 1 2)]

/-- **THE MODULUS BAR.**  Two atom families of three-space with the SAME
shifted diagonals and the SAME squared Gram entries, one of which deflates and
one of which does not.  Every reading of the lane that factors through those
two tables is blind to the difference. -/
theorem exists_modulusBar :
    ∃ (atomOne atomTwo : Fin 3 → (Fin 3 → ℝ)) (scale : Fin 3 → ℝ),
      (∀ slot, atomShiftedDiag atomOne scale slot = atomShiftedDiag atomTwo scale slot)
        ∧ (∀ rowSlot colSlot, atomGram atomOne rowSlot colSlot ^ 2
            = atomGram atomTwo rowSlot colSlot ^ 2)
        ∧ AtomTripleDeflates atomOne scale 0 1 2
        ∧ ¬ AtomTripleDeflates atomTwo scale 0 1 2 :=
  ⟨orientedBarCoherentAtom, orientedBarAntiAtom, orientedBarScale,
    orientedBar_shiftedDiag_eq, orientedBar_gram_sq_eq,
    orientedBarCoherent_deflates, orientedBarAnti_not_deflates⟩

/-- **NO MODULUS CRITERION DECIDES THE DEFLATION TEST.**  A criterion whose
only inputs are the shifted diagonal table and the squared Gram table cannot
be both sound and complete for `Gtz.AtomTripleDeflates`.  The modulus bar
supplies the two data, and the criterion cannot separate them.

This is the reason a certificate of the lane must read the ORIENTED sign.
The landed sign-free readings — the diagonal dominance criterion, the heavy
criterion, the pair minors, the edge slacks, the volume and the reading — all
factor through those two tables, so each of them covers a stratum and none of
them can be sharp. -/
theorem no_modulusCriterion_decides_atomTripleDeflates
    (criterion : (Fin 3 → ℝ) → (Fin 3 → Fin 3 → ℝ) → Prop)
    (hsound : ∀ (atom : Fin 3 → (Fin 3 → ℝ)) (scale : Fin 3 → ℝ),
      criterion (fun slot => atomShiftedDiag atom scale slot)
          (fun rowSlot colSlot => atomGram atom rowSlot colSlot ^ 2) →
        AtomTripleDeflates atom scale 0 1 2)
    (hcomplete : ∀ (atom : Fin 3 → (Fin 3 → ℝ)) (scale : Fin 3 → ℝ),
      AtomTripleDeflates atom scale 0 1 2 →
        criterion (fun slot => atomShiftedDiag atom scale slot)
          (fun rowSlot colSlot => atomGram atom rowSlot colSlot ^ 2)) :
    False := by
  have hcoherent := hcomplete orientedBarCoherentAtom orientedBarScale
    orientedBarCoherent_deflates
  have hdiagTable : (fun slot => atomShiftedDiag orientedBarCoherentAtom orientedBarScale slot)
      = (fun slot => atomShiftedDiag orientedBarAntiAtom orientedBarScale slot) :=
    funext orientedBar_shiftedDiag_eq
  have hgramTable : (fun rowSlot colSlot =>
        atomGram orientedBarCoherentAtom rowSlot colSlot ^ 2)
      = (fun rowSlot colSlot => atomGram orientedBarAntiAtom rowSlot colSlot ^ 2) :=
    funext fun rowSlot => funext fun colSlot => orientedBar_gram_sq_eq rowSlot colSlot
  rw [hdiagTable, hgramTable] at hcoherent
  exact orientedBarAnti_not_deflates
    (hsound orientedBarAntiAtom orientedBarScale hcoherent)

/-- **NO MODULUS CRITERION DECIDES THE TRIPLE DETERMINANT** either.  The same
bar, read at the determinant rather than at the deflation test. -/
theorem no_modulusCriterion_decides_atomTripleDet
    (criterion : (Fin 3 → ℝ) → (Fin 3 → Fin 3 → ℝ) → Prop)
    (hsound : ∀ (atom : Fin 3 → (Fin 3 → ℝ)) (scale : Fin 3 → ℝ),
      criterion (fun slot => atomShiftedDiag atom scale slot)
          (fun rowSlot colSlot => atomGram atom rowSlot colSlot ^ 2) →
        0 < atomTripleDet atom scale 0 1 2)
    (hcomplete : ∀ (atom : Fin 3 → (Fin 3 → ℝ)) (scale : Fin 3 → ℝ),
      0 < atomTripleDet atom scale 0 1 2 →
        criterion (fun slot => atomShiftedDiag atom scale slot)
          (fun rowSlot colSlot => atomGram atom rowSlot colSlot ^ 2)) :
    False := by
  have hcoherentPos : 0 < atomTripleDet orientedBarCoherentAtom orientedBarScale 0 1 2 := by
    rw [orientedBarCoherent_tripleDet]; norm_num
  have hcoherent := hcomplete orientedBarCoherentAtom orientedBarScale hcoherentPos
  have hdiagTable : (fun slot => atomShiftedDiag orientedBarCoherentAtom orientedBarScale slot)
      = (fun slot => atomShiftedDiag orientedBarAntiAtom orientedBarScale slot) :=
    funext orientedBar_shiftedDiag_eq
  have hgramTable : (fun rowSlot colSlot =>
        atomGram orientedBarCoherentAtom rowSlot colSlot ^ 2)
      = (fun rowSlot colSlot => atomGram orientedBarAntiAtom rowSlot colSlot ^ 2) :=
    funext fun rowSlot => funext fun colSlot => orientedBar_gram_sq_eq rowSlot colSlot
  rw [hdiagTable, hgramTable] at hcoherent
  have hantiPos := hsound orientedBarAntiAtom orientedBarScale hcoherent
  rw [orientedBarAnti_tripleDet] at hantiPos
  norm_num at hantiPos

/-! ## Layer 3 — the trine signature, where the sign decides alone -/

/-- The TRINE SIGNATURE: every shifted diagonal is one third and every
distinct squared Gram entry is one twentieth.  The real icosahedral tight
frame at the uniform scale one sixth carries it, and so does the complex
two-trine — the two data agree on every modulus reading. -/
def IsTrineSignature (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) : Prop :=
  (∀ slot, atomShiftedDiag atom scale slot = 1 / 3)
    ∧ (∀ rowSlot colSlot : Fin 6, rowSlot ≠ colSlot →
        atomGram atom rowSlot colSlot ^ 2 = 1 / 20)

/-- **AT THE TRINE SIGNATURE THE DETERMINANT IS AN AFFINE FUNCTION OF THE
CYCLE.**  Every modulus reading is pinned, and the whole verdict rides on the
one reading a square cannot reproduce. -/
theorem trineSignature_tripleDet {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hsignature : IsTrineSignature atom scale) {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) :
    atomTripleDet atom scale slotOne slotTwo slotThree
      = 2 * atomTriangleCycle atom slotOne slotTwo slotThree - 7 / 540 := by
  obtain ⟨hdiag, hsq⟩ := hsignature
  rw [atomTripleDet_eq_modulus_add_cycle, atomTripleModulus_eq, hdiag slotOne,
    hdiag slotTwo, hdiag slotThree, hsq slotOne slotTwo honeTwo,
    hsq slotOne slotThree honeThree, hsq slotTwo slotThree htwoThree]
  ring

/-- **THE SIGN DECIDES.**  At the trine signature a triple has a positive
determinant exactly when its cycle beats `7/1080`. -/
theorem trineSignature_decided_by_cycle {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hsignature : IsTrineSignature atom scale) {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) :
    0 < atomTripleDet atom scale slotOne slotTwo slotThree
      ↔ 7 / 1080 < atomTriangleCycle atom slotOne slotTwo slotThree := by
  rw [trineSignature_tripleDet hsignature honeTwo honeThree htwoThree]
  constructor <;> intro hstep <;> linarith

/-- **THE CYCLE MODULUS IS PINNED AT THE TRINE SIGNATURE.**  Its square is
`1/8000`, the cube of one twentieth. -/
theorem trineSignature_cycle_sq {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hsignature : IsTrineSignature atom scale) {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) :
    atomTriangleCycle atom slotOne slotTwo slotThree ^ 2 = 1 / 8000 := by
  obtain ⟨_, hsq⟩ := hsignature
  rw [atomTriangleCycle, mul_pow, mul_pow, hsq slotOne slotTwo honeTwo,
    hsq slotOne slotThree honeThree, hsq slotTwo slotThree htwoThree]
  norm_num

/-- **THE THRESHOLD SITS STRICTLY INSIDE THE MODULUS BAND.**  The square of
the deciding threshold is smaller than the pinned square of the cycle, so the
modulus data at the trine signature is EXACTLY indecisive: one orientation
clears and the other does not. -/
theorem trineSignature_threshold_inside : (7 / 1080 : ℝ) ^ 2 < 1 / 8000 := by
  norm_num

/-- **THE COHERENT ORIENTATION CLEARS.**  A triple of the trine signature with
a positive cycle has a positive determinant. -/
theorem trineSignature_tripleDet_pos_of_pos_cycle {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} (hsignature : IsTrineSignature atom scale)
    {slotOne slotTwo slotThree : Fin 6} (honeTwo : slotOne ≠ slotTwo)
    (honeThree : slotOne ≠ slotThree) (htwoThree : slotTwo ≠ slotThree)
    (hcycle : 0 < atomTriangleCycle atom slotOne slotTwo slotThree) :
    0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  rw [trineSignature_decided_by_cycle hsignature honeTwo honeThree htwoThree]
  have hsq := trineSignature_cycle_sq hsignature honeTwo honeThree htwoThree
  nlinarith [hsq, hcycle, trineSignature_threshold_inside]

/-- **THE ANTI-COHERENT ORIENTATION FAILS**, and so does the vanishing one.
A triple of the trine signature with a nonpositive cycle has a negative
determinant.  The complex two-trine carries a vanishing real part of the
cycle at every triple, which is exactly this branch. -/
theorem trineSignature_tripleDet_neg_of_nonpos_cycle {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} (hsignature : IsTrineSignature atom scale)
    {slotOne slotTwo slotThree : Fin 6} (honeTwo : slotOne ≠ slotTwo)
    (honeThree : slotOne ≠ slotThree) (htwoThree : slotTwo ≠ slotThree)
    (hcycle : atomTriangleCycle atom slotOne slotTwo slotThree ≤ 0) :
    atomTripleDet atom scale slotOne slotTwo slotThree < 0 := by
  rw [trineSignature_tripleDet hsignature honeTwo honeThree htwoThree]
  linarith

/-- **THE VANISHING CYCLE READS A STRICTLY NEGATIVE DETERMINANT.**  This is the
scalar form of the complex obstruction: at the trine signature a triple whose
oriented sign is annihilated cannot dominate, at any of the twenty triples. -/
theorem trineSignature_tripleDet_of_zero_cycle {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} (hsignature : IsTrineSignature atom scale)
    {slotOne slotTwo slotThree : Fin 6} (honeTwo : slotOne ≠ slotTwo)
    (honeThree : slotOne ≠ slotThree) (htwoThree : slotTwo ≠ slotThree)
    (hcycle : atomTriangleCycle atom slotOne slotTwo slotThree = 0) :
    atomTripleDet atom scale slotOne slotTwo slotThree = -(7 / 540) := by
  rw [trineSignature_tripleDet hsignature honeTwo honeThree htwoThree, hcycle]
  ring

/-- **THE MODULUS CELL IS SILENT AT THE TRINE SIGNATURE.**  The modulus part
there is `-7/540`, which is negative, so the fifth cell never fires on this
family.  The four coherent cells do, at the ten coherent triples.  The two
families are complementary, and this is the sharpest witness of that. -/
theorem trineSignature_modulus {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hsignature : IsTrineSignature atom scale) {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) :
    atomTripleModulus atom scale slotOne slotTwo slotThree = -(7 / 540) := by
  obtain ⟨hdiag, hsq⟩ := hsignature
  rw [atomTripleModulus_eq, hdiag slotOne, hdiag slotTwo, hdiag slotThree,
    hsq slotOne slotTwo honeTwo, hsq slotOne slotThree honeThree,
    hsq slotTwo slotThree htwoThree]
  norm_num

/-- **THE ICOSAHEDRAL FRAME CARRIES THE TRINE SIGNATURE**, at the uniform
scale one sixth.  It is the landed real witness of the complex obstruction,
and every modulus reading of the two agrees. -/
theorem icosaFrameAtom_isTrineSignature :
    IsTrineSignature icosaFrameAtom (fun _ => 1 / 6) := by
  refine ⟨fun slot => ?_, fun rowSlot colSlot hne => ?_⟩
  · rw [icosaFrameAtom_shiftedDiag_eq]; norm_num
  · exact icosaFrameAtom_gram_sq_of_ne hne

/-- The shifted triple determinant of the icosahedral frame at the uniform
scale one sixth, in closed form: twice the cycle, minus `7/540`. -/
theorem icosaFrameAtom_tripleDet_eq {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) :
    atomTripleDet icosaFrameAtom (fun _ => 1 / 6) slotOne slotTwo slotThree
      = 2 * atomTriangleCycle icosaFrameAtom slotOne slotTwo slotThree - 7 / 540 :=
  trineSignature_tripleDet icosaFrameAtom_isTrineSignature honeTwo honeThree htwoThree

/-! ## Layer 4 — the cycle sum laws

The oriented signs of a rank-three Parseval frame of six atoms are not free.
Their total is a function of the diagonal alone. -/

/-- The total oriented sign of six slots: the sum of the cycles of the twenty
triples. -/
def atomCycleSum (atom : Fin 6 → (Fin 3 → ℝ)) : ℝ :=
  atomTriangleCycle atom 0 1 2 + atomTriangleCycle atom 0 1 3
    + atomTriangleCycle atom 0 1 4 + atomTriangleCycle atom 0 1 5
    + atomTriangleCycle atom 0 2 3 + atomTriangleCycle atom 0 2 4
    + atomTriangleCycle atom 0 2 5 + atomTriangleCycle atom 0 3 4
    + atomTriangleCycle atom 0 3 5 + atomTriangleCycle atom 0 4 5
    + atomTriangleCycle atom 1 2 3 + atomTriangleCycle atom 1 2 4
    + atomTriangleCycle atom 1 2 5 + atomTriangleCycle atom 1 3 4
    + atomTriangleCycle atom 1 3 5 + atomTriangleCycle atom 1 4 5
    + atomTriangleCycle atom 2 3 4 + atomTriangleCycle atom 2 3 5
    + atomTriangleCycle atom 2 4 5 + atomTriangleCycle atom 3 4 5

/-- The ROW CUBE of a slot: the double sum of the cycle through that slot with
repetitions permitted.  The idempotent law collapses it to the leverage. -/
theorem atomGram_rowCube {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot : Fin slotCount) :
    (∑ midSlot, ∑ farSlot, atomGram atom rowSlot midSlot
        * atomGram atom midSlot farSlot * atomGram atom farSlot rowSlot)
      = atomGram atom rowSlot rowSlot := by
  classical
  have hinner : ∀ midSlot : Fin slotCount,
      (∑ farSlot, atomGram atom rowSlot midSlot * atomGram atom midSlot farSlot
          * atomGram atom farSlot rowSlot)
        = atomGram atom rowSlot midSlot ^ 2 := by
    intro midSlot
    have hfactor : (∑ farSlot, atomGram atom rowSlot midSlot
          * atomGram atom midSlot farSlot * atomGram atom farSlot rowSlot)
        = atomGram atom rowSlot midSlot
          * ∑ farSlot, atomGram atom midSlot farSlot * atomGram atom farSlot rowSlot := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun farSlot _ => by ring
    rw [hfactor, atomGram_idempotent hframe midSlot rowSlot,
      atomGram_comm atom midSlot rowSlot]
    ring
  rw [Finset.sum_congr rfl fun midSlot _ => hinner midSlot]
  exact atomGram_row_energy hframe rowSlot

/-- The full triple sum of the cycle with repetitions permitted is the trace,
which is the rank. -/
theorem atomGram_tripleSum {rank : ℕ} {atom : Fin 6 → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ rowSlot, ∑ midSlot, ∑ farSlot, atomGram atom rowSlot midSlot
        * atomGram atom midSlot farSlot * atomGram atom farSlot rowSlot)
      = ((rank : ℕ) : ℝ) := by
  rw [Finset.sum_congr rfl fun rowSlot _ => atomGram_rowCube hframe rowSlot]
  exact atomGram_trace hframe

/-- **THE CYCLE SUM LAW.**  The total oriented sign of a rank-three Parseval
frame of six atoms is one third of the sum of the cubed deviations of the
diagonal from one half.

The proof is three applications of the idempotent law, one row energy law and
one trace law.  Nothing in it reads a scale, and nothing in it reads the sign
of a single Gram entry: the twenty signed products are pinned in total by the
six diagonal entries. -/
theorem sum_atomTriangleCycle {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    6 * atomCycleSum atom
      = 3 - 3 * (∑ slot, atomGram atom slot slot ^ 2)
        + 2 * (∑ slot, atomGram atom slot slot ^ 3) := by
  have htriple : (∑ rowSlot, ∑ midSlot, ∑ farSlot, atomGram atom rowSlot midSlot
      * atomGram atom midSlot farSlot * atomGram atom farSlot rowSlot) = (3 : ℝ) := by
    have hstep := atomGram_tripleSum hframe
    simpa using hstep
  have hrow : ∀ slot : Fin 6, (∑ colSlot, atomGram atom slot colSlot ^ 2)
      = atomGram atom slot slot := fun slot => atomGram_row_energy hframe slot
  have h10 := atomGram_comm atom 1 0
  have h20 := atomGram_comm atom 2 0
  have h30 := atomGram_comm atom 3 0
  have h40 := atomGram_comm atom 4 0
  have h50 := atomGram_comm atom 5 0
  have h21 := atomGram_comm atom 2 1
  have h31 := atomGram_comm atom 3 1
  have h41 := atomGram_comm atom 4 1
  have h51 := atomGram_comm atom 5 1
  have h32 := atomGram_comm atom 3 2
  have h42 := atomGram_comm atom 4 2
  have h52 := atomGram_comm atom 5 2
  have h43 := atomGram_comm atom 4 3
  have h53 := atomGram_comm atom 5 3
  have h54 := atomGram_comm atom 5 4
  have r0 := hrow 0
  have r1 := hrow 1
  have r2 := hrow 2
  have r3 := hrow 3
  have r4 := hrow 4
  have r5 := hrow 5
  simp only [atomCycleSum, atomTriangleCycle]
  simp only [Fin.sum_univ_six] at htriple r0 r1 r2 r3 r4 r5 ⊢
  simp only [h10, h20, h30, h40, h50, h21, h31, h41, h51, h32, h42, h52,
    h43, h53, h54] at htriple r0 r1 r2 r3 r4 r5 ⊢
  linear_combination htriple - 3 * atomGram atom 0 0 * r0 - 3 * atomGram atom 1 1 * r1
    - 3 * atomGram atom 2 2 * r2 - 3 * atomGram atom 3 3 * r3
    - 3 * atomGram atom 4 4 * r4 - 3 * atomGram atom 5 5 * r5

/-- **THE CYCLE SUM AS A SKEWNESS.**  The same law with the diagonal centred
at one half, which is the mean of the six leverages of a rank-three frame of
six slots.  The total oriented sign is one third of the third moment. -/
theorem sum_atomTriangleCycle_centred {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    3 * atomCycleSum atom = ∑ slot, (atomGram atom slot slot - 1 / 2) ^ 3 := by
  have hlaw := sum_atomTriangleCycle hframe
  have htrace : (∑ slot, atomGram atom slot slot) = (3 : ℝ) := by
    have hstep := atomGram_trace (rank := 3) hframe
    simpa using hstep
  simp only [Fin.sum_univ_six] at hlaw htrace ⊢
  linarith [hlaw, htrace]

/-- **A BALANCED FRAME HAS TOTAL ORIENTED SIGN ZERO.**  When every leverage is
one half the coherent and the anti-coherent triples balance exactly.  The
icosahedral frame is such a datum, and it splits ten against ten. -/
theorem atomCycleSum_eq_zero_of_balanced {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbalanced : ∀ slot, atomGram atom slot slot = 1 / 2) :
    atomCycleSum atom = 0 := by
  have hlaw := sum_atomTriangleCycle_centred hframe
  simp only [Fin.sum_univ_six, hbalanced] at hlaw
  norm_num at hlaw
  linarith

/-- **A QUANTITATIVE COHERENT SUPPLY.**  A frame whose centred third moment is
positive carries a triple of strictly positive cycle, and the largest cycle is
at least one sixtieth of that moment.  This is the first quantitative supply
of the oriented sign in the lane: the landed parity engine gives one coherent
triple and no bound. -/
theorem exists_pos_atomTriangleCycle_of_skew {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hskew : 0 < ∑ slot, (atomGram atom slot slot - 1 / 2) ^ 3) :
    0 < atomCycleSum atom := by
  have hlaw := sum_atomTriangleCycle_centred hframe
  linarith

/-- **THE CYCLE SUM AT ONE PIVOT.**  The ten triples through a slot carry a
total oriented sign that reads only the leverage of that slot and the
LEVERAGE-WEIGHTED ROW ENERGY of its Gram row.  The global law is the sum of
the six pivot laws, divided by three. -/
theorem atomPivotCycleSum {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (pivot : Fin 6) :
    2 * (∑ midSlot, ∑ farSlot, atomGram atom pivot midSlot
          * atomGram atom midSlot farSlot * atomGram atom farSlot pivot)
      = 2 * atomGram atom pivot pivot := by
  rw [atomGram_rowCube hframe pivot]

/-! ## Layer 5 — the pivot charge shadow and its real-only supply -/

/-- **THE LANE MERGE.**  The triangle gap at an apex is the opposite edge
against the deflated cross at that apex.  The coherent triangle lane and the
pivot lift lane read the SAME object, and this identity is the dictionary. -/
theorem atomTriangleGap_eq_edge_mul_atomPivotCross {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (apex slotOne slotTwo : Fin slotCount) :
    atomTriangleGap atom scale apex slotOne slotTwo
      = atomGram atom slotOne slotTwo
        * atomPivotCross atom scale apex slotOne slotTwo := by
  simp only [atomTriangleGap, atomTriangleCycle, atomPivotCross]
  ring

/-- The CHARGE SHADOW of a slot at a pivot: the pivot-orthogonal part of the
atom, scaled by the charge of that slot.  Every square root of the pivot lift
is cleared, so the vector is a polynomial in the readings. -/
def atomChargeShadow {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (pivot slot : Fin slotCount) : Fin rank → ℝ :=
  (atomGram atom pivot slot * atomGram atom pivot pivot) • atom slot
    - (atomGram atom pivot slot ^ 2) • atom pivot

/-- The CHARGE SIGN of a pair at a pivot: the pivot leverage against the
oriented cycle, minus the square of the charge product.  It is the raw form of
the sign term `c_ij * g_i * g_j` that the pivot Schur route consumes, and it
is strictly stronger than mere coherence. -/
def atomChargeSign {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (pivot slotOne slotTwo : Fin slotCount) : ℝ :=
  atomGram atom pivot pivot * atomTriangleCycle atom pivot slotOne slotTwo
    - (atomGram atom pivot slotOne * atomGram atom pivot slotTwo) ^ 2

/-- **THE CHARGE SHADOW IS ORTHOGONAL TO THE PIVOT ATOM.**  All five off-pivot
charge shadows therefore live in one plane. -/
theorem atomChargeShadow_dot_pivot {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (pivot slot : Fin slotCount) :
    atomChargeShadow atom pivot slot ⬝ᵥ atom pivot = 0 := by
  simp only [atomChargeShadow, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [show atom slot ⬝ᵥ atom pivot = atomGram atom slot pivot from rfl,
    show atom pivot ⬝ᵥ atom pivot = atomGram atom pivot pivot from rfl,
    atomGram_comm atom slot pivot]
  ring

/-- **THE CHARGE SHADOW DOT LAW.**  The dot product of two charge shadows is
the pivot leverage against the charge sign.  This is the exact bridge between
the oriented sign of the triple and the geometry of the shadow plane. -/
theorem atomChargeShadow_dot {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (pivot slotOne slotTwo : Fin slotCount) :
    atomChargeShadow atom pivot slotOne ⬝ᵥ atomChargeShadow atom pivot slotTwo
      = atomGram atom pivot pivot * atomChargeSign atom pivot slotOne slotTwo := by
  simp only [atomChargeShadow, atomChargeSign, atomTriangleCycle, sub_dotProduct,
    dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [show atom slotOne ⬝ᵥ atom slotTwo = atomGram atom slotOne slotTwo from rfl,
    show atom slotOne ⬝ᵥ atom pivot = atomGram atom slotOne pivot from rfl,
    show atom pivot ⬝ᵥ atom slotTwo = atomGram atom pivot slotTwo from rfl,
    show atom pivot ⬝ᵥ atom pivot = atomGram atom pivot pivot from rfl,
    atomGram_comm atom slotOne pivot]
  ring

/-- The charge sign is symmetric in its two off-pivot slots. -/
theorem atomChargeSign_comm {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (pivot slotOne slotTwo : Fin slotCount) :
    atomChargeSign atom pivot slotOne slotTwo = atomChargeSign atom pivot slotTwo slotOne := by
  simp only [atomChargeSign, atomTriangleCycle, atomGram_comm atom slotTwo slotOne]
  ring

/-- **A POSITIVE CHARGE SIGN IS STRICTLY STRONGER THAN COHERENCE.**  It puts
the cycle above an explicit positive threshold, so a pair of nonnegative
charge sign whose charges do not vanish carries a strictly positive cycle. -/
theorem atomTriangleCycle_pos_of_atomChargeSign {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {pivot slotOne slotTwo : Fin slotCount}
    (hpivot : 0 < atomGram atom pivot pivot)
    (hcharge : atomGram atom pivot slotOne * atomGram atom pivot slotTwo ≠ 0)
    (hsign : 0 ≤ atomChargeSign atom pivot slotOne slotTwo) :
    0 < atomTriangleCycle atom pivot slotOne slotTwo := by
  simp only [atomChargeSign] at hsign
  have hsq : 0 < (atomGram atom pivot slotOne * atomGram atom pivot slotTwo) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hcharge))
  nlinarith [hsign, hsq, hpivot]

/-- **FOUR VECTORS OF A PLANE ARE NEVER PAIRWISE OBTUSE.**  Four vectors of
three-space that are all orthogonal to one nonzero normal always carry a pair
of nonnegative dot product.

The proof is the obtuse bound one dimension down.  Drop one vector as a test
vector.  The remaining three are pairwise obtuse against it, so they are
linearly independent, and the normal is independent of them because it is
orthogonal to each of them and nonzero.  That makes four independent vectors
of three-space, which is impossible.

Over the complex field the same family lives in a FOUR-dimensional real space
and the bound is vacuous.  This is the real-only step of the layer. -/
theorem exists_nonneg_dot_of_orthogonal_four
    (vec : Fin 4 → (Fin 3 → ℝ)) {normal : Fin 3 → ℝ} (hnormal : normal ≠ 0)
    (hperp : ∀ index, vec index ⬝ᵥ normal = 0) :
    ∃ first second : Fin 4, first ≠ second ∧ 0 ≤ vec first ⬝ᵥ vec second := by
  classical
  by_contra hcontra
  push Not at hcontra
  have hlast : ∀ index : Fin 3, index.castSucc ≠ (3 : Fin 4) := by decide
  have hobtuse : IsPairwiseObtuse (fun index : Fin 3 => vec index.castSucc) := by
    intro first second hne
    exact hcontra _ _ (fun heq => hne (Fin.castSucc_injective 3 heq))
  have htest : ∀ index : Fin 3, vec index.castSucc ⬝ᵥ vec 3 < 0 :=
    fun index => hcontra _ _ (hlast index)
  have hindep := linearIndependent_of_isPairwiseObtuse_of_testVector hobtuse htest
  have hspanPerp : ∀ witness ∈ Submodule.span ℝ
      (Set.range (fun index : Fin 3 => vec index.castSucc)), witness ⬝ᵥ normal = 0 := by
    intro witness hwitness
    induction hwitness using Submodule.span_induction with
    | mem member hmember => obtain ⟨index, rfl⟩ := hmember; exact hperp _
    | zero => simp
    | add left right _ _ hleft hright => rw [add_dotProduct, hleft, hright, add_zero]
    | smul factor member _ hmember =>
        rw [smul_dotProduct, hmember, smul_eq_mul, mul_zero]
  have hnormalPos : 0 < normal ⬝ᵥ normal :=
    lt_of_le_of_ne (dotProduct_self_nonneg normal)
      (fun heq => hnormal (dotProduct_self_eq_zero.mp heq.symm))
  have hbig : LinearIndependent ℝ
      (Fin.cons normal (fun index : Fin 3 => vec index.castSucc)) := by
    refine LinearIndependent.finCons' normal _ hindep ?_
    intro coef witness hwitness hsum
    have hdot := congrArg (fun value : Fin 3 → ℝ => value ⬝ᵥ normal) hsum
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hspanPerp witness hwitness,
      zero_dotProduct, add_zero] at hdot
    rcases mul_eq_zero.mp hdot with hzero | hzero
    · exact hzero
    · exact absurd hzero (ne_of_gt hnormalPos)
  have hcard := hbig.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card ℝ] at hcard
  simp at hcard

/-- The plane obtuse bound in the `Finset` shape a slot consumer wants. -/
theorem exists_nonneg_dot_of_orthogonal_on {atomIndex : Type*} [DecidableEq atomIndex]
    {vec : atomIndex → (Fin 3 → ℝ)} (family : Finset atomIndex)
    (hcard : 4 ≤ family.card) {normal : Fin 3 → ℝ} (hnormal : normal ≠ 0)
    (hperp : ∀ index ∈ family, vec index ⬝ᵥ normal = 0) :
    ∃ first ∈ family, ∃ second ∈ family, first ≠ second ∧ 0 ≤ vec first ⬝ᵥ vec second := by
  classical
  obtain ⟨quad, hsubset, hquadCard⟩ := Finset.exists_subset_card_eq hcard
  have hequiv := quad.equivFinOfCardEq hquadCard
  set pick : Fin 4 → atomIndex := fun index => (hequiv.symm index : atomIndex) with hpick
  have hpickMem : ∀ index : Fin 4, pick index ∈ quad :=
    fun index => (hequiv.symm index).property
  have hpickInjective : Function.Injective pick := by
    intro first second heq
    exact hequiv.symm.injective (Subtype.ext heq)
  obtain ⟨first, second, hne, hdot⟩ :=
    exists_nonneg_dot_of_orthogonal_four (fun index => vec (pick index)) hnormal
      (fun index => hperp _ (hsubset (hpickMem index)))
  exact ⟨pick first, hsubset (hpickMem first), pick second, hsubset (hpickMem second),
    fun heq => hne (hpickInjective heq), hdot⟩

/-- **THE PIVOT CHARGE SUPPLY, ONE PAIR.**  At every pivot of a family of six
atoms of three-space with a nonzero pivot atom, some off-pivot pair carries a
nonnegative charge sign.  The family may be restricted by dropping one further
slot, and the supply survives, because four slots always remain. -/
theorem exists_nonneg_atomChargeSign_off {atom : Fin 6 → (Fin 3 → ℝ)} {pivot drop : Fin 6}
    (hpivotAtom : atom pivot ≠ 0) :
    ∃ slotOne slotTwo : Fin 6,
      slotOne ≠ pivot ∧ slotTwo ≠ pivot ∧ slotOne ≠ drop ∧ slotTwo ≠ drop
        ∧ slotOne ≠ slotTwo ∧ 0 ≤ atomChargeSign atom pivot slotOne slotTwo := by
  classical
  have hpivotPos : 0 < atomGram atom pivot pivot :=
    lt_of_le_of_ne (atomGram_diag_nonneg atom pivot)
      (fun heq => hpivotAtom (dotProduct_self_eq_zero.mp heq.symm))
  set family : Finset (Fin 6) := Finset.univ \ {pivot, drop} with hfamily
  have hpairCard : ({pivot, drop} : Finset (Fin 6)).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le pivot {drop}) ?_
    simp
  have hcard : 4 ≤ family.card := by
    have hcover : (Finset.univ : Finset (Fin 6))
        ⊆ family ∪ ({pivot, drop} : Finset (Fin 6)) := by
      intro slot _
      by_cases hin : slot ∈ ({pivot, drop} : Finset (Fin 6))
      · exact Finset.mem_union_right _ hin
      · exact Finset.mem_union_left _ (by
          rw [hfamily, Finset.mem_sdiff]
          exact ⟨Finset.mem_univ _, hin⟩)
    have hcoverCard := Finset.card_le_card hcover
    have hunionCard := Finset.card_union_le family ({pivot, drop} : Finset (Fin 6))
    have huniv : (Finset.univ : Finset (Fin 6)).card = 6 := by simp
    omega
  have hmem : ∀ slot ∈ family, slot ≠ pivot ∧ slot ≠ drop := by
    intro slot hslot
    rw [hfamily, Finset.mem_sdiff] at hslot
    have hnot := hslot.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
    push Not at hnot
    exact hnot
  obtain ⟨slotOne, hslotOne, slotTwo, hslotTwo, hne, hdot⟩ :=
    exists_nonneg_dot_of_orthogonal_on (vec := fun slot => atomChargeShadow atom pivot slot)
      family hcard hpivotAtom (fun slot _ => atomChargeShadow_dot_pivot atom pivot slot)
  refine ⟨slotOne, slotTwo, (hmem slotOne hslotOne).1, (hmem slotTwo hslotTwo).1,
    (hmem slotOne hslotOne).2, (hmem slotTwo hslotTwo).2, hne, ?_⟩
  rw [atomChargeShadow_dot atom pivot slotOne slotTwo] at hdot
  nlinarith [hdot, hpivotPos]

/-- **THE PIVOT CHARGE SUPPLY, TWO PAIRS — the real-only counting law of the
lane.**  At every pivot of six atoms of three-space with a nonzero pivot atom,
TWO DISTINCT off-pivot pairs carry a nonnegative charge sign.  The two pairs
are distinct because the second one avoids the first slot of the first one.

The count two is attained: an adversarial search over rank-three Parseval
frames at scale mass one reaches exactly two at some pivot and never fewer.
Over the complex field the count is ZERO, because the five charge shadows then
span a four-dimensional real space and carry no obtuse bound at all.  The
landed parity engine supplies ONE coherent triple at a pivot and no more, so
this is a strict gain of the pivot form. -/
theorem exists_two_nonneg_atomChargeSign {atom : Fin 6 → (Fin 3 → ℝ)} {pivot : Fin 6}
    (hpivotAtom : atom pivot ≠ 0) :
    ∃ firstOne firstTwo secondOne secondTwo : Fin 6,
      firstOne ≠ pivot ∧ firstTwo ≠ pivot ∧ firstOne ≠ firstTwo
        ∧ secondOne ≠ pivot ∧ secondTwo ≠ pivot ∧ secondOne ≠ secondTwo
        ∧ secondOne ≠ firstOne ∧ secondTwo ≠ firstOne
        ∧ 0 ≤ atomChargeSign atom pivot firstOne firstTwo
        ∧ 0 ≤ atomChargeSign atom pivot secondOne secondTwo := by
  obtain ⟨firstOne, firstTwo, hfirstOnePivot, hfirstTwoPivot, _, _, hfirstNe, hfirstSign⟩ :=
    exists_nonneg_atomChargeSign_off (atom := atom) (pivot := pivot) (drop := pivot) hpivotAtom
  obtain ⟨secondOne, secondTwo, hsecondOnePivot, hsecondTwoPivot, hsecondOneDrop,
    hsecondTwoDrop, hsecondNe, hsecondSign⟩ :=
    exists_nonneg_atomChargeSign_off (atom := atom) (pivot := pivot) (drop := firstOne)
      hpivotAtom
  exact ⟨firstOne, firstTwo, secondOne, secondTwo, hfirstOnePivot, hfirstTwoPivot,
    hfirstNe, hsecondOnePivot, hsecondTwoPivot, hsecondNe, hsecondOneDrop,
    hsecondTwoDrop, hfirstSign, hsecondSign⟩

/-! ## Layer 6 — the moment sums of the gap form are diagonal data

The gap form of a triple is the three-by-three block `N_T = P_T - diag(t_T)`.
Its characteristic polynomial has three coefficients: the trace, the sum of
the three pair minors, and the determinant.  Summed over the TWENTY triples,
EVERY ONE of the three collapses onto the diagonal of the projection and the
scales.  The whole off-diagonal geometry cancels.

The consequence is an impossibility theorem of the same weight as the modulus
bar: no certificate built from the AVERAGE characteristic polynomial of the
twenty triples can decide the cell, because two data with the same diagonal
share that polynomial exactly while one of them can dominate and the other
cannot.  It also explains, structurally, the banked measurement that the sum
of the twenty shifted determinants is `-0.2593` at the icosahedral frame: at
every balanced frame at the uniform scale that number is forced. -/

/-- The sum of the fifteen pair minors of the gap form. -/
def atomPairMinorSum (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) : ℝ :=
  atomPairMinor atom scale 0 1 + atomPairMinor atom scale 0 2
    + atomPairMinor atom scale 0 3 + atomPairMinor atom scale 0 4
    + atomPairMinor atom scale 0 5 + atomPairMinor atom scale 1 2
    + atomPairMinor atom scale 1 3 + atomPairMinor atom scale 1 4
    + atomPairMinor atom scale 1 5 + atomPairMinor atom scale 2 3
    + atomPairMinor atom scale 2 4 + atomPairMinor atom scale 2 5
    + atomPairMinor atom scale 3 4 + atomPairMinor atom scale 3 5
    + atomPairMinor atom scale 4 5

/-- The sum of the fifteen products of two shifted diagonals. -/
def atomRestPairSum (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) : ℝ :=
  atomShiftedDiag atom scale 0 * atomShiftedDiag atom scale 1
    + atomShiftedDiag atom scale 0 * atomShiftedDiag atom scale 2
    + atomShiftedDiag atom scale 0 * atomShiftedDiag atom scale 3
    + atomShiftedDiag atom scale 0 * atomShiftedDiag atom scale 4
    + atomShiftedDiag atom scale 0 * atomShiftedDiag atom scale 5
    + atomShiftedDiag atom scale 1 * atomShiftedDiag atom scale 2
    + atomShiftedDiag atom scale 1 * atomShiftedDiag atom scale 3
    + atomShiftedDiag atom scale 1 * atomShiftedDiag atom scale 4
    + atomShiftedDiag atom scale 1 * atomShiftedDiag atom scale 5
    + atomShiftedDiag atom scale 2 * atomShiftedDiag atom scale 3
    + atomShiftedDiag atom scale 2 * atomShiftedDiag atom scale 4
    + atomShiftedDiag atom scale 2 * atomShiftedDiag atom scale 5
    + atomShiftedDiag atom scale 3 * atomShiftedDiag atom scale 4
    + atomShiftedDiag atom scale 3 * atomShiftedDiag atom scale 5
    + atomShiftedDiag atom scale 4 * atomShiftedDiag atom scale 5

/-- **THE SECOND MOMENT SUM.**  The pair minors of the gap form total the
paired shifted diagonals minus the pair energy, with no other reading.  Each
of the twenty triples carries three pair minors and each pair sits in four
triples, so the sum over the triples is four times this. -/
theorem atomPairMinorSum_eq (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) :
    atomPairMinorSum atom scale = atomRestPairSum atom scale - atomPairEnergy atom := by
  simp only [atomPairMinorSum, atomRestPairSum, atomPairEnergy, atomPairMinor]
  ring

/-- **THE SECOND MOMENT SUM IS DIAGONAL DATA.** -/
theorem two_mul_atomPairMinorSum {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    2 * atomPairMinorSum atom scale
      = 2 * atomRestPairSum atom scale - 3 + atomDiagEnergy atom := by
  have hedge : 2 * atomPairEnergy atom = (3 : ℝ) - atomDiagEnergy atom := by
    have hstep := atomPairEnergy_two_mul (rank := 3) hframe
    simpa using hstep
  rw [atomPairMinorSum_eq]
  linarith [hedge]

/-- The sum of the twenty shifted triple determinants. -/
def atomTripleDetSum (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) : ℝ :=
  atomTripleDet atom scale 0 1 2 + atomTripleDet atom scale 0 1 3
    + atomTripleDet atom scale 0 1 4 + atomTripleDet atom scale 0 1 5
    + atomTripleDet atom scale 0 2 3 + atomTripleDet atom scale 0 2 4
    + atomTripleDet atom scale 0 2 5 + atomTripleDet atom scale 0 3 4
    + atomTripleDet atom scale 0 3 5 + atomTripleDet atom scale 0 4 5
    + atomTripleDet atom scale 1 2 3 + atomTripleDet atom scale 1 2 4
    + atomTripleDet atom scale 1 2 5 + atomTripleDet atom scale 1 3 4
    + atomTripleDet atom scale 1 3 5 + atomTripleDet atom scale 1 4 5
    + atomTripleDet atom scale 2 3 4 + atomTripleDet atom scale 2 3 5
    + atomTripleDet atom scale 2 4 5 + atomTripleDet atom scale 3 4 5

/-- The sum of the twenty products of three shifted diagonals. -/
def atomRestTripleSum (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) : ℝ :=
  atomTripleVolume atom scale 0 1 2 + atomTripleVolume atom scale 0 1 3
    + atomTripleVolume atom scale 0 1 4 + atomTripleVolume atom scale 0 1 5
    + atomTripleVolume atom scale 0 2 3 + atomTripleVolume atom scale 0 2 4
    + atomTripleVolume atom scale 0 2 5 + atomTripleVolume atom scale 0 3 4
    + atomTripleVolume atom scale 0 3 5 + atomTripleVolume atom scale 0 4 5
    + atomTripleVolume atom scale 1 2 3 + atomTripleVolume atom scale 1 2 4
    + atomTripleVolume atom scale 1 2 5 + atomTripleVolume atom scale 1 3 4
    + atomTripleVolume atom scale 1 3 5 + atomTripleVolume atom scale 1 4 5
    + atomTripleVolume atom scale 2 3 4 + atomTripleVolume atom scale 2 3 5
    + atomTripleVolume atom scale 2 4 5 + atomTripleVolume atom scale 3 4 5

/-- **THE THIRD MOMENT SUM, RAW FORM.**  The twenty shifted determinants total
the twenty shifted volumes, plus twice the total oriented sign, minus the
pair energy against the total shifted diagonal, plus the row energies weighted
by the shifted diagonals.  Only the ROW ENERGY LAW is consumed. -/
theorem atomTripleDetSum_eq {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomTripleDetSum atom scale
      = atomRestTripleSum atom scale + 2 * atomCycleSum atom
        - atomPairEnergy atom * (∑ slot, atomShiftedDiag atom scale slot)
        + ∑ slot, atomShiftedDiag atom scale slot
            * (atomGram atom slot slot - atomGram atom slot slot ^ 2) := by
  have hrow : ∀ slot : Fin 6, (∑ colSlot, atomGram atom slot colSlot ^ 2)
      = atomGram atom slot slot := fun slot => atomGram_row_energy hframe slot
  have h10 := atomGram_comm atom 1 0
  have h20 := atomGram_comm atom 2 0
  have h30 := atomGram_comm atom 3 0
  have h40 := atomGram_comm atom 4 0
  have h50 := atomGram_comm atom 5 0
  have h21 := atomGram_comm atom 2 1
  have h31 := atomGram_comm atom 3 1
  have h41 := atomGram_comm atom 4 1
  have h51 := atomGram_comm atom 5 1
  have h32 := atomGram_comm atom 3 2
  have h42 := atomGram_comm atom 4 2
  have h52 := atomGram_comm atom 5 2
  have h43 := atomGram_comm atom 4 3
  have h53 := atomGram_comm atom 5 3
  have h54 := atomGram_comm atom 5 4
  have r0 := hrow 0
  have r1 := hrow 1
  have r2 := hrow 2
  have r3 := hrow 3
  have r4 := hrow 4
  have r5 := hrow 5
  simp only [atomTripleDetSum, atomRestTripleSum, atomCycleSum, atomPairEnergy,
    atomTripleDet, atomTripleVolume, atomTriangleCycle]
  simp only [Fin.sum_univ_six] at r0 r1 r2 r3 r4 r5 ⊢
  simp only [h10, h20, h30, h40, h50, h21, h31, h41, h51, h32, h42, h52,
    h43, h53, h54] at r0 r1 r2 r3 r4 r5 ⊢
  linear_combination (atomShiftedDiag atom scale 0) * r0
    + (atomShiftedDiag atom scale 1) * r1 + (atomShiftedDiag atom scale 2) * r2
    + (atomShiftedDiag atom scale 3) * r3 + (atomShiftedDiag atom scale 4) * r4
    + (atomShiftedDiag atom scale 5) * r5

/-- **THE THIRD MOMENT SUM IS DIAGONAL DATA — the headline of this layer.**
The twenty shifted triple determinants of a rank-three Parseval frame of six
atoms total an explicit expression in the DIAGONAL of the projection and the
SCALES alone.  Every off-diagonal reading cancels.

The three ingredients are the cycle sum law of layer four, the pair energy law
of this layer, and the row energy law.  The identity is exact at every datum,
not an inequality and not an average. -/
theorem sum_atomTripleDet {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    6 * atomTripleDetSum atom scale
      = 6 * atomRestTripleSum atom scale
        + 4 * (∑ slot, (atomGram atom slot slot - 1 / 2) ^ 3)
        - 3 * (3 - atomDiagEnergy atom)
          * (∑ slot, atomShiftedDiag atom scale slot)
        + 6 * ∑ slot, atomShiftedDiag atom scale slot
            * (atomGram atom slot slot - atomGram atom slot slot ^ 2) := by
  have hraw := atomTripleDetSum_eq (scale := scale) hframe
  have hcycle := sum_atomTriangleCycle_centred hframe
  have hpair : 2 * atomPairEnergy atom = (3 : ℝ) - atomDiagEnergy atom := by
    have hstep := atomPairEnergy_two_mul (rank := 3) hframe
    simpa using hstep
  have hexpand : 6 * atomTripleDetSum atom scale
      = 6 * atomRestTripleSum atom scale + 4 * (3 * atomCycleSum atom)
        - 3 * (2 * atomPairEnergy atom) * (∑ slot, atomShiftedDiag atom scale slot)
        + 6 * ∑ slot, atomShiftedDiag atom scale slot
            * (atomGram atom slot slot - atomGram atom slot slot ^ 2) := by
    rw [hraw]; ring
  rw [hexpand, hcycle, hpair]

/-- **THE AVERAGE CHARACTERISTIC POLYNOMIAL IS BLIND.**  Two rank-three
Parseval frames of six atoms with the SAME diagonal carry the SAME sum of the
twenty shifted triple determinants, at every choice of scales.  The same holds
for the first and second moment sums, which read only the shifted diagonals
and the pair energy.

Hence no certificate whose input is the average characteristic polynomial of
the twenty triples can decide the cell.  The cell is FALSE over the complex
field at a datum whose diagonal is realized over the real field, so the
average polynomial cannot even separate the two fields. -/
theorem sum_atomTripleDet_eq_of_same_diagonal {atomOne atomTwo : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ}
    (hframeOne : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atomOne slot ⬝ᵥ probe) * (atomOne slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hframeTwo : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atomTwo slot ⬝ᵥ probe) * (atomTwo slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hdiag : ∀ slot, atomGram atomOne slot slot = atomGram atomTwo slot slot) :
    atomTripleDetSum atomOne scale = atomTripleDetSum atomTwo scale := by
  have hshifted : ∀ slot, atomShiftedDiag atomOne scale slot
      = atomShiftedDiag atomTwo scale slot := by
    intro slot
    simp only [atomShiftedDiag, hdiag slot]
  have hrestTriple : atomRestTripleSum atomOne scale = atomRestTripleSum atomTwo scale := by
    simp only [atomRestTripleSum, atomTripleVolume, hshifted]
  have hdiagEnergy : atomDiagEnergy atomOne = atomDiagEnergy atomTwo := by
    simp only [atomDiagEnergy, hdiag]
  have hlawOne := sum_atomTripleDet (scale := scale) hframeOne
  have hlawTwo := sum_atomTripleDet (scale := scale) hframeTwo
  rw [hdiagEnergy] at hlawOne
  simp only [Fin.sum_univ_six, hdiag, hshifted] at hlawOne hlawTwo
  rw [hrestTriple] at hlawOne
  linarith [hlawOne, hlawTwo]

/-- **A DIAGONAL-ONLY EXISTENCE CRITERION.**  When the diagonal expression of
the third moment sum is positive, some one of the twenty triples has a
positive shifted determinant.  This is the first criterion of the lane that
reads NO off-diagonal entry at all.

MEASURED: the criterion fires at `0.323` percent of the admissible diagonal
and scale pairs, so it is not empty and it is far from complete. -/
theorem exists_tripleDet_pos_of_diagonalSum {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hpositive : 0 < 6 * atomRestTripleSum atom scale
        + 4 * (∑ slot, (atomGram atom slot slot - 1 / 2) ^ 3)
        - 3 * (3 - atomDiagEnergy atom)
          * (∑ slot, atomShiftedDiag atom scale slot)
        + 6 * ∑ slot, atomShiftedDiag atom scale slot
            * (atomGram atom slot slot - atomGram atom slot slot ^ 2)) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  by_contra hcontra
  push Not at hcontra
  have hlaw := sum_atomTripleDet (scale := scale) hframe
  have hall : ∀ first second third : Fin 6, first ≠ second → first ≠ third →
      second ≠ third → atomTripleDet atom scale first second third ≤ 0 := by
    intro first second third hone htwo hthree
    exact hcontra first second third hone htwo hthree
  have hsum : atomTripleDetSum atom scale ≤ 0 := by
    simp only [atomTripleDetSum]
    have h012 := hall 0 1 2 (by decide) (by decide) (by decide)
    have h013 := hall 0 1 3 (by decide) (by decide) (by decide)
    have h014 := hall 0 1 4 (by decide) (by decide) (by decide)
    have h015 := hall 0 1 5 (by decide) (by decide) (by decide)
    have h023 := hall 0 2 3 (by decide) (by decide) (by decide)
    have h024 := hall 0 2 4 (by decide) (by decide) (by decide)
    have h025 := hall 0 2 5 (by decide) (by decide) (by decide)
    have h034 := hall 0 3 4 (by decide) (by decide) (by decide)
    have h035 := hall 0 3 5 (by decide) (by decide) (by decide)
    have h045 := hall 0 4 5 (by decide) (by decide) (by decide)
    have h123 := hall 1 2 3 (by decide) (by decide) (by decide)
    have h124 := hall 1 2 4 (by decide) (by decide) (by decide)
    have h125 := hall 1 2 5 (by decide) (by decide) (by decide)
    have h134 := hall 1 3 4 (by decide) (by decide) (by decide)
    have h135 := hall 1 3 5 (by decide) (by decide) (by decide)
    have h145 := hall 1 4 5 (by decide) (by decide) (by decide)
    have h234 := hall 2 3 4 (by decide) (by decide) (by decide)
    have h235 := hall 2 3 5 (by decide) (by decide) (by decide)
    have h245 := hall 2 4 5 (by decide) (by decide) (by decide)
    have h345 := hall 3 4 5 (by decide) (by decide) (by decide)
    linarith
  linarith [hlaw, hsum, hpositive]

end Gtz
