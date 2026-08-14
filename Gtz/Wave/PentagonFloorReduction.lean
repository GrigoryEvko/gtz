import Mathlib
import Gtz.Wave.PluckerSchurFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The pentagon floor: the tenth is six copies of a rank-two statement

`Gtz.AtomPluckerTenth` says that the level-two determinantal energy of a real
rank-three Parseval frame of six atoms stays at or below TEN times the
level-three energy.  `Gtz.atomPluckerTenth_of_balanced` proves it when all six
leverages are one half, and `Gtz.AtomPluckerTenthUnbalanced` was what remained.

This module removes the leverage split completely.  It shows that

  `6 * (10 * E3 - E2)  =  the total over the six five-slot families of one
  local reading`,

that the local reading has NO frame hypothesis and NO leverage in it, and that
it is a statement about FIVE vectors of rank three, which is a rank-two
statement in disguise.  The residue that closes the whole tenth is therefore

  `Gtz.AtomPentagonFloor`,

an unconstrained polynomial inequality in fifteen real numbers.

## The three coordinates

Write `p T` for `Gtz.atomBlockDet`, the determinant of the Gram block of a
triple.  It is the square of the volume of the three atoms
(`Gtz.atomBlockDet_eq_volume_sq`), so it is the squared Plucker coordinate.
The landed marginal law `Gtz.atomMarginal_01` and its fourteen siblings say

  `pair minor of {y,z}  =  the total of `p T` over the four triples that
  contain `{y,z}`,

so the whole tenth lives in the twenty numbers `p T` alone.  In those
coordinates

  `E2 = the total over the fifteen pairs of (the pair marginal) ^ 2`,
  `E3 = the total over the twenty triples of (p T) ^ 2`.

## The local reading

For a five-slot family `S` write `mass` for the total of the ten `p T` inside
`S`, `quad` for the total of their squares, and `star v` for the total of the
six `p T` inside `S` that contain the slot `v`.  The PENTAGON READING is

  `20 * quad + 3 * mass ^ 2 - 3 * (the total over the five slots of star ^ 2)`.

`Gtz.atomDropMargin_familySum` is the exact identity

  `6 * (10 * E3 - E2) = the total of the pentagon reading over the six
  five-slot families`.

It is a FREE polynomial identity in the twenty block determinants, once the
fifteen marginal laws replace the pair minors.  No leverage, no balance.

## Why five slots and not four

The same construction over the fifteen FOUR-slot families is also exact
(`Gtz.atomQuadMargin_familySum`), and it is finer.  But the four-slot reading is
NOT always positive.  `Gtz.atomQuadMargin_tetraFrame` gives the witness: four
vectors that point at the corners of a regular tetrahedron carry four equal
volumes, and the four-slot reading there is `-1/2`.  Those four vectors extend to
a real Parseval frame of six atoms with two zero atoms
(`Gtz.atomTetraFrame_isTightFrame`), so the refutation lives inside the cell.
The five-slot grouping repairs it: at the same frame the pentagon reading of the
family that keeps all four is `5/4` (`Gtz.atomDropMargin_tetraFrame`).

## Where the realness enters, exactly

Five vectors of rank three obey the Grassmann-Plucker relation

  `V 012 * V 034 - V 013 * V 024 + V 014 * V 023 = 0`

(`Gtz.atomVolumePlucker`), which is a `ring` identity.  Over the real field the
three terms are real, so the three PRODUCTS OF BLOCK DETERMINANTS

  `u = p 012 * p 034`, `w = p 013 * p 024`, `z = p 014 * p 023`

obey the EQUALITY

  `u ^ 2 + w ^ 2 + z ^ 2 = 2 * (u * w + w * z + z * u)`

(`Gtz.atomBlockDetRealLaw`).  Over the Hermitian field only `≤` survives, and
`Gtz.atomComplexTriple_defect` measures the deficit exactly: it is four times
the squared imaginary part of the cross product of the two outer terms.  This is
the real-only law that the whole programme spends, isolated in one line.

One immediate consequence is that a FLAT Plucker vector is impossible over the
real field: three equal positive products contradict the law
(`Gtz.atomBlockDetRealLaw_forbids_flat`).  A flat measure is exactly what makes
the twelve sharp, so the law is the reason the ten is reachable at all.

## What is proved here, and what is left

Proved without hypothesis:

* the two family identities, `Gtz.atomDropMargin_familySum` and
  `Gtz.atomQuadMargin_familySum`
* the real-only law and its complex defect
* the CAUCHY-SCHWARZ floor of the pentagon reading,
  `Gtz.atomPentagonReading_ge_neg_quad`, which recovers the landed twelve
  (`Gtz.atomPluckerEnergyTwo_le_twelve_of_pentagon`)
* the sharpness of the pentagon reading at the icosahedral readings,
  `Gtz.atomPentagonReading_pentagon`
* a new unconditional floor for the level-two energy,
  `Gtz.atomPluckerEnergyTwo_ge_spread`: `E2 ≥ 3/5 + the leverage spread`
* the tetrahedral refutation of the four-slot reading.

Left as ONE named residue: `Gtz.AtomPentagonFloor`.  It is strictly smaller than
`Gtz.AtomPluckerTenthUnbalanced`, because it closes the WHOLE tenth and not only
the unbalanced part, it reads five vectors and not six, it has no frame law in
it, and it has no case split.

## The measurement behind the residue

Adversarial descent on the scale-free pentagon reading over fifteen free
coordinates, at 300000 restarts by 6000 steps on 200 threads, reached
`-3.3e-15`.  The run stood behind a calibration gate that read the pentagon
reading at each of the six five-atom sub-configurations of the icosahedral frame
and got `4.4e-16` every time, which is the exact zero that
`Gtz.atomPentagonReading_pentagon` proves.  The argmin carried the normalised
readings `0.055279` five times and `0.144721` five times, which are
`(5 - sqrt 5) / 50` and `(5 + sqrt 5) / 50`, the exact readings of that theorem.
So the residue carries a failed refutation whose argmin is a proved equality
case.  Section 5 rule 1 of the standing audit still applies: a small positive
floor is evidence against a claim.  This floor is not small and not positive: it
is zero, and the zero is a theorem.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

Every statement below is proved.  `Gtz.AtomPentagonFloor` is a definition, and
the theorems that read it take it as a hypothesis.

## Vacuity

`Gtz.atomPentagonReading_single` shows that the pentagon reading is strictly
positive at a configuration with one independent triple, and
`Gtz.atomDropMargin_tetraFrame` computes it at a frame of the cell, so
`Gtz.AtomPentagonFloor` is not vacuous.  `Gtz.atomPluckerEnergyTwo_le_twelve_of_pentagon`
spends the whole decomposition unconditionally.
-/

namespace Gtz

/-! ## Layer 0 — the real-only law, and where the Hermitian field breaks it -/

/-- **THE SQUARED THREE-TERM LAW OVER THE REAL FIELD.**  Three real numbers with
`x - y + z = 0` have squares that obey

  `u ^ 2 + w ^ 2 + z ^ 2 = 2 * (u * w + w * z + z * u)`.

Equivalently `(u + w + z) ^ 2 = 2 * (u ^ 2 + w ^ 2 + z ^ 2)`.  This is the whole
real-only content of the campaign, in one line. -/
theorem atomSignedTriple_realLaw {left mid right : ℝ} (hrel : left - mid + right = 0) :
    (left ^ 2) ^ 2 + (mid ^ 2) ^ 2 + (right ^ 2) ^ 2
      = 2 * (left ^ 2 * mid ^ 2 + mid ^ 2 * right ^ 2 + right ^ 2 * left ^ 2) := by
  have hmid : mid = left + right := by linarith
  subst hmid
  ring

/-- **THE HERMITIAN DEFECT.**  Over the complex field the same three-term
relation leaves an exact deficit: four times the squared imaginary part of the
product of the first term with the conjugate of the third.

Over the real field that imaginary part is zero and the law becomes the equality
of `Gtz.atomSignedTriple_realLaw`.  This single term is the whole distance
between the real cell and the Hermitian cell. -/
theorem atomComplexTriple_defect (left mid right : ℂ) (hrel : left - mid + right = 0) :
    2 * (Complex.normSq left * Complex.normSq mid
        + Complex.normSq mid * Complex.normSq right
        + Complex.normSq right * Complex.normSq left)
      - ((Complex.normSq left) ^ 2 + (Complex.normSq mid) ^ 2 + (Complex.normSq right) ^ 2)
      = 4 * (left.im * right.re - left.re * right.im) ^ 2 := by
  have hmid : mid = left + right := by
    have h := congrArg Complex.re hrel
    have h' := congrArg Complex.im hrel
    simp only [Complex.sub_re, Complex.add_re, Complex.zero_re, Complex.sub_im,
      Complex.add_im, Complex.zero_im] at h h'
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im] <;> linarith
  subst hmid
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

/-- **THE HERMITIAN FIELD KEEPS ONLY THE INEQUALITY.**  The equality of the real
field becomes a one-sided bound over the complex field. -/
theorem atomComplexTriple_le (left mid right : ℂ) (hrel : left - mid + right = 0) :
    (Complex.normSq left) ^ 2 + (Complex.normSq mid) ^ 2 + (Complex.normSq right) ^ 2
      ≤ 2 * (Complex.normSq left * Complex.normSq mid
        + Complex.normSq mid * Complex.normSq right
        + Complex.normSq right * Complex.normSq left) := by
  have hdef := atomComplexTriple_defect left mid right hrel
  nlinarith [sq_nonneg (left.im * right.re - left.re * right.im)]

/-- **THE GRASSMANN-PLUCKER RELATION OF FIVE VECTORS OF RANK THREE.**  It needs
no hypothesis: it is a polynomial identity in the fifteen coordinates. -/
theorem atomVolumePlucker (vecZero vecOne vecTwo vecThree vecFour : Fin 3 → ℝ) :
    atomVolume vecZero vecOne vecTwo * atomVolume vecZero vecThree vecFour
      - atomVolume vecZero vecOne vecThree * atomVolume vecZero vecTwo vecFour
      + atomVolume vecZero vecOne vecFour * atomVolume vecZero vecTwo vecThree = 0 := by
  simp only [atomVolume, atomWedge, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE REAL-ONLY LAW IN BLOCK-DETERMINANT COORDINATES.**  The three products
of block determinants that the Grassmann-Plucker relation pairs obey the squared
three-term law.  This is the form a successor lane consumes: it reads only the
twenty numbers `Gtz.atomBlockDet` and it holds for EVERY six-atom family, with
no frame law. -/
theorem atomBlockDetRealLaw (atom : Fin 6 → (Fin 3 → ℝ))
    (slotZero slotOne slotTwo slotThree slotFour : Fin 6) :
    (atomBlockDet atom slotZero slotOne slotTwo
        * atomBlockDet atom slotZero slotThree slotFour) ^ 2
      + (atomBlockDet atom slotZero slotOne slotThree
        * atomBlockDet atom slotZero slotTwo slotFour) ^ 2
      + (atomBlockDet atom slotZero slotOne slotFour
        * atomBlockDet atom slotZero slotTwo slotThree) ^ 2
      = 2 * ((atomBlockDet atom slotZero slotOne slotTwo
            * atomBlockDet atom slotZero slotThree slotFour)
          * (atomBlockDet atom slotZero slotOne slotThree
            * atomBlockDet atom slotZero slotTwo slotFour)
        + (atomBlockDet atom slotZero slotOne slotThree
            * atomBlockDet atom slotZero slotTwo slotFour)
          * (atomBlockDet atom slotZero slotOne slotFour
            * atomBlockDet atom slotZero slotTwo slotThree)
        + (atomBlockDet atom slotZero slotOne slotFour
            * atomBlockDet atom slotZero slotTwo slotThree)
          * (atomBlockDet atom slotZero slotOne slotTwo
            * atomBlockDet atom slotZero slotThree slotFour)) := by
  have hrel := atomVolumePlucker (atom slotZero) (atom slotOne) (atom slotTwo)
    (atom slotThree) (atom slotFour)
  have hlaw := atomSignedTriple_realLaw
    (left := atomVolume (atom slotZero) (atom slotOne) (atom slotTwo)
      * atomVolume (atom slotZero) (atom slotThree) (atom slotFour))
    (mid := atomVolume (atom slotZero) (atom slotOne) (atom slotThree)
      * atomVolume (atom slotZero) (atom slotTwo) (atom slotFour))
    (right := atomVolume (atom slotZero) (atom slotOne) (atom slotFour)
      * atomVolume (atom slotZero) (atom slotTwo) (atom slotThree)) hrel
  simp only [atomBlockDet_eq_volume_sq]
  linear_combination hlaw

/-- **THE REAL FIELD FORBIDS A FLAT PLUCKER VECTOR.**  Three equal products
force the common value to be zero.  A flat determinantal measure is exactly the
equality case of the landed twelve, so this is the reason the ten is
reachable. -/
theorem atomBlockDetRealLaw_forbids_flat {first second third : ℝ}
    (hlaw : first ^ 2 + second ^ 2 + third ^ 2
      = 2 * (first * second + second * third + third * first))
    (hone : first = second) (htwo : second = third) : first = 0 := by
  subst hone; subst htwo
  nlinarith [hlaw]

/-! ## Layer 1 — the pentagon reading of ten determinantal readings -/

/-- The PENTAGON READING of the ten readings of a five-slot family.  The ten
arguments are indexed by the ten triples of five slots, in increasing order.

It is `20 * quad + 3 * mass ^ 2 - 3 * (the total of the five squared stars)`,
where `mass` is the total of the ten readings, `quad` is the total of their
squares, and `star v` is the total of the six readings whose triple contains the
slot `v`. -/
def atomPentagonReading (readOneTwoThree readOneTwoFour readOneTwoFive readOneThreeFour
    readOneThreeFive readOneFourFive readTwoThreeFour readTwoThreeFive readTwoFourFive
    readThreeFourFive : ℝ) : ℝ :=
  20 * (readOneTwoThree ^ 2 + readOneTwoFour ^ 2 + readOneTwoFive ^ 2 + readOneThreeFour ^ 2
      + readOneThreeFive ^ 2 + readOneFourFive ^ 2 + readTwoThreeFour ^ 2
      + readTwoThreeFive ^ 2 + readTwoFourFive ^ 2 + readThreeFourFive ^ 2)
    + 3 * (readOneTwoThree + readOneTwoFour + readOneTwoFive + readOneThreeFour
      + readOneThreeFive + readOneFourFive + readTwoThreeFour + readTwoThreeFive
      + readTwoFourFive + readThreeFourFive) ^ 2
    - 3 * ((readOneTwoThree + readOneTwoFour + readOneTwoFive + readOneThreeFour
          + readOneThreeFive + readOneFourFive) ^ 2
      + (readOneTwoThree + readOneTwoFour + readOneTwoFive + readTwoThreeFour
          + readTwoThreeFive + readTwoFourFive) ^ 2
      + (readOneTwoThree + readOneThreeFour + readOneThreeFive + readTwoThreeFour
          + readTwoThreeFive + readThreeFourFive) ^ 2
      + (readOneTwoFour + readOneThreeFour + readOneFourFive + readTwoThreeFour
          + readTwoFourFive + readThreeFourFive) ^ 2
      + (readOneTwoFive + readOneThreeFive + readOneFourFive + readTwoThreeFive
          + readTwoFourFive + readThreeFourFive) ^ 2)

/-- **THE PENTAGON READING IS SHARP.**  At the icosahedral readings the reading
is exactly zero.  The five large readings are `5 + sqrt 5` and the five small
ones are `5 - sqrt 5`, and they sit in the pentagon pattern: a triple carries the
large reading exactly when the two slots it omits are neighbours on the
five-cycle `1-2-3-4-5-1`.

Adversarial descent over fifteen free coordinates put its argmin on exactly
these readings, normalised to `(5 + sqrt 5) / 50` and `(5 - sqrt 5) / 50`.  The
five-atom sub-configurations of the icosahedral frame realise them. -/
theorem atomPentagonReading_pentagon (root : ℝ) (hroot : root ^ 2 = 5) :
    atomPentagonReading (5 + root) (5 - root) (5 + root) (5 - root) (5 - root)
      (5 + root) (5 + root) (5 - root) (5 - root) (5 + root) = 0 := by
  simp only [atomPentagonReading]
  linear_combination (200 : ℝ) * hroot

/-- **THE PENTAGON READING SEES ONE INDEPENDENT TRIPLE.**  A family with a
single non-zero reading carries the reading `14 * r ^ 2`, so the floor is not
vacuous and it is not an equality in general. -/
theorem atomPentagonReading_single (reading : ℝ) :
    atomPentagonReading reading 0 0 0 0 0 0 0 0 0 = 14 * reading ^ 2 := by
  simp only [atomPentagonReading]; ring

/-- **THE CAUCHY-SCHWARZ FLOOR OF THE PENTAGON READING.**  The reading never
falls below minus four times the total of the squares.

The proof is the exact identity `the total of the squared stars = mass ^ 2 + the
total of the squared co-stars`, where the CO-STAR of a slot is the total of the
four readings whose triple misses that slot, together with five Cauchy-Schwarz
steps on four terms.  Summed over the six five-slot families this floor gives
back exactly the landed twelve, so the whole distance from twelve to ten is the
distance from this floor to zero. -/
theorem atomPentagonReading_ge_neg_quad (readOneTwoThree readOneTwoFour readOneTwoFive
    readOneThreeFour readOneThreeFive readOneFourFive readTwoThreeFour readTwoThreeFive
    readTwoFourFive readThreeFourFive : ℝ) :
    -4 * (readOneTwoThree ^ 2 + readOneTwoFour ^ 2 + readOneTwoFive ^ 2 + readOneThreeFour ^ 2
        + readOneThreeFive ^ 2 + readOneFourFive ^ 2 + readTwoThreeFour ^ 2
        + readTwoThreeFive ^ 2 + readTwoFourFive ^ 2 + readThreeFourFive ^ 2)
      ≤ atomPentagonReading readOneTwoThree readOneTwoFour readOneTwoFive readOneThreeFour
          readOneThreeFive readOneFourFive readTwoThreeFour readTwoThreeFive readTwoFourFive
          readThreeFourFive := by
  have hcs : ∀ partOne partTwo partThree partFour : ℝ,
      (partOne + partTwo + partThree + partFour) ^ 2
        ≤ 4 * (partOne ^ 2 + partTwo ^ 2 + partThree ^ 2 + partFour ^ 2) := by
    intro partOne partTwo partThree partFour
    nlinarith [sq_nonneg (partOne - partTwo), sq_nonneg (partOne - partThree),
      sq_nonneg (partOne - partFour), sq_nonneg (partTwo - partThree),
      sq_nonneg (partTwo - partFour), sq_nonneg (partThree - partFour)]
  have costarOne := hcs readTwoThreeFour readTwoThreeFive readTwoFourFive readThreeFourFive
  have costarTwo := hcs readOneThreeFour readOneThreeFive readOneFourFive readThreeFourFive
  have costarThree := hcs readOneTwoFour readOneTwoFive readOneFourFive readTwoFourFive
  have costarFour := hcs readOneTwoThree readOneTwoFive readOneThreeFive readTwoThreeFive
  have costarFive := hcs readOneTwoThree readOneTwoFour readOneThreeFour readTwoThreeFour
  simp only [atomPentagonReading]
  nlinarith [costarOne, costarTwo, costarThree, costarFour, costarFive]

/-! ## Layer 2 — the drop margin of a six-atom family -/

variable {atom : Fin 6 → (Fin 3 → ℝ)}

/-- The DROP MARGIN of a five-slot family of a six-atom family: the pentagon
reading of the ten block determinants inside that family. -/
noncomputable def atomDropMargin (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree slotFour slotFive : Fin 6) : ℝ :=
  atomPentagonReading (atomBlockDet atom slotOne slotTwo slotThree)
    (atomBlockDet atom slotOne slotTwo slotFour) (atomBlockDet atom slotOne slotTwo slotFive)
    (atomBlockDet atom slotOne slotThree slotFour) (atomBlockDet atom slotOne slotThree slotFive)
    (atomBlockDet atom slotOne slotFour slotFive) (atomBlockDet atom slotTwo slotThree slotFour)
    (atomBlockDet atom slotTwo slotThree slotFive) (atomBlockDet atom slotTwo slotFour slotFive)
    (atomBlockDet atom slotThree slotFour slotFive)

/-- **THE FAMILY IDENTITY.**  Six times the gap of the tenth is exactly the total
of the six drop margins.

This is the centre of the module.  It is a FREE polynomial identity in the
twenty block determinants: the only inputs are the fifteen marginal laws, which
replace each pair minor by the total of the four block determinants that contain
its pair.  There is no leverage in it and no balance. -/
theorem atomDropMargin_familySum
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    6 * (10 * atomPluckerEnergyThree atom - atomPluckerEnergyTwo atom)
      = atomDropMargin atom 1 2 3 4 5 + atomDropMargin atom 0 2 3 4 5
        + atomDropMargin atom 0 1 3 4 5 + atomDropMargin atom 0 1 2 4 5
        + atomDropMargin atom 0 1 2 3 5 + atomDropMargin atom 0 1 2 3 4 := by
  have h01 := atomMarginal_01 hframe
  have h02 := atomMarginal_02 hframe
  have h03 := atomMarginal_03 hframe
  have h04 := atomMarginal_04 hframe
  have h05 := atomMarginal_05 hframe
  have h12 := atomMarginal_12 hframe
  have h13 := atomMarginal_13 hframe
  have h14 := atomMarginal_14 hframe
  have h15 := atomMarginal_15 hframe
  have h23 := atomMarginal_23 hframe
  have h24 := atomMarginal_24 hframe
  have h25 := atomMarginal_25 hframe
  have h34 := atomMarginal_34 hframe
  have h35 := atomMarginal_35 hframe
  have h45 := atomMarginal_45 hframe
  simp only [atomPluckerEnergyThree, atomPluckerEnergyTwo, atomTripleFamilySum,
    atomPairFamilySum, atomDropMargin, atomPentagonReading]
  linear_combination (6 * (atomBlockPairMinor atom 0 1
      + (atomBlockDet atom 0 1 2 + atomBlockDet atom 0 1 3 + atomBlockDet atom 0 1 4
        + atomBlockDet atom 0 1 5))) * h01
    + (6 * (atomBlockPairMinor atom 0 2
      + (atomBlockDet atom 0 1 2 + atomBlockDet atom 0 2 3 + atomBlockDet atom 0 2 4
        + atomBlockDet atom 0 2 5))) * h02
    + (6 * (atomBlockPairMinor atom 0 3
      + (atomBlockDet atom 0 1 3 + atomBlockDet atom 0 2 3 + atomBlockDet atom 0 3 4
        + atomBlockDet atom 0 3 5))) * h03
    + (6 * (atomBlockPairMinor atom 0 4
      + (atomBlockDet atom 0 1 4 + atomBlockDet atom 0 2 4 + atomBlockDet atom 0 3 4
        + atomBlockDet atom 0 4 5))) * h04
    + (6 * (atomBlockPairMinor atom 0 5
      + (atomBlockDet atom 0 1 5 + atomBlockDet atom 0 2 5 + atomBlockDet atom 0 3 5
        + atomBlockDet atom 0 4 5))) * h05
    + (6 * (atomBlockPairMinor atom 1 2
      + (atomBlockDet atom 0 1 2 + atomBlockDet atom 1 2 3 + atomBlockDet atom 1 2 4
        + atomBlockDet atom 1 2 5))) * h12
    + (6 * (atomBlockPairMinor atom 1 3
      + (atomBlockDet atom 0 1 3 + atomBlockDet atom 1 2 3 + atomBlockDet atom 1 3 4
        + atomBlockDet atom 1 3 5))) * h13
    + (6 * (atomBlockPairMinor atom 1 4
      + (atomBlockDet atom 0 1 4 + atomBlockDet atom 1 2 4 + atomBlockDet atom 1 3 4
        + atomBlockDet atom 1 4 5))) * h14
    + (6 * (atomBlockPairMinor atom 1 5
      + (atomBlockDet atom 0 1 5 + atomBlockDet atom 1 2 5 + atomBlockDet atom 1 3 5
        + atomBlockDet atom 1 4 5))) * h15
    + (6 * (atomBlockPairMinor atom 2 3
      + (atomBlockDet atom 0 2 3 + atomBlockDet atom 1 2 3 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 2 3 5))) * h23
    + (6 * (atomBlockPairMinor atom 2 4
      + (atomBlockDet atom 0 2 4 + atomBlockDet atom 1 2 4 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 2 4 5))) * h24
    + (6 * (atomBlockPairMinor atom 2 5
      + (atomBlockDet atom 0 2 5 + atomBlockDet atom 1 2 5 + atomBlockDet atom 2 3 5
        + atomBlockDet atom 2 4 5))) * h25
    + (6 * (atomBlockPairMinor atom 3 4
      + (atomBlockDet atom 0 3 4 + atomBlockDet atom 1 3 4 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 3 4 5))) * h34
    + (6 * (atomBlockPairMinor atom 3 5
      + (atomBlockDet atom 0 3 5 + atomBlockDet atom 1 3 5 + atomBlockDet atom 2 3 5
        + atomBlockDet atom 3 4 5))) * h35
    + (6 * (atomBlockPairMinor atom 4 5
      + (atomBlockDet atom 0 4 5 + atomBlockDet atom 1 4 5 + atomBlockDet atom 2 4 5
        + atomBlockDet atom 3 4 5))) * h45

/-! ## Layer 3 — the residue: a floor on five vectors of rank three -/

/-- The PENTAGON MARGIN of five vectors of rank three: the pentagon reading of
the ten squared volumes.  It is homogeneous of degree eight, so the floor
`0 ≤ atomPentagonMargin` is a statement about a point of the Grassmannian of
three-planes in the five-slot space, which is six-dimensional. -/
noncomputable def atomPentagonMargin (vecOne vecTwo vecThree vecFour vecFive : Fin 3 → ℝ) : ℝ :=
  atomPentagonReading (atomVolume vecOne vecTwo vecThree ^ 2)
    (atomVolume vecOne vecTwo vecFour ^ 2) (atomVolume vecOne vecTwo vecFive ^ 2)
    (atomVolume vecOne vecThree vecFour ^ 2) (atomVolume vecOne vecThree vecFive ^ 2)
    (atomVolume vecOne vecFour vecFive ^ 2) (atomVolume vecTwo vecThree vecFour ^ 2)
    (atomVolume vecTwo vecThree vecFive ^ 2) (atomVolume vecTwo vecFour vecFive ^ 2)
    (atomVolume vecThree vecFour vecFive ^ 2)

/-- The drop margin of a six-atom family is the pentagon margin of the five
atoms that stay. -/
theorem atomDropMargin_eq_pentagonMargin (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree slotFour slotFive : Fin 6) :
    atomDropMargin atom slotOne slotTwo slotThree slotFour slotFive
      = atomPentagonMargin (atom slotOne) (atom slotTwo) (atom slotThree) (atom slotFour)
          (atom slotFive) := by
  simp only [atomDropMargin, atomPentagonMargin, atomBlockDet_eq_volume_sq]

/-- **THE PENTAGON FLOOR.**  The one residue that closes the whole tenth.

It reads FIVE vectors of rank three and nothing else.  There is no frame law in
it, no leverage, and no case split.  It is a polynomial inequality in fifteen
free real numbers, homogeneous of degree eight.

It is sharp: `Gtz.atomPentagonReading_pentagon` gives the equality case, and the
five-atom sub-configurations of the icosahedral frame realise it.  Adversarial
descent at 300000 restarts by 6000 steps reached `-3.3e-15` and put its argmin on
exactly those readings. -/
def AtomPentagonFloor : Prop :=
  ∀ vecOne vecTwo vecThree vecFour vecFive : Fin 3 → ℝ,
    0 ≤ atomPentagonMargin vecOne vecTwo vecThree vecFour vecFive

/-- **THE PENTAGON FLOOR CLOSES THE TENTH.**  Six copies of the residue, one for
each atom that the family drops, give `E2 ≤ 10 * E3` for EVERY real rank-three
Parseval frame of six atoms.  The balanced case of
`Gtz.atomPluckerTenth_of_balanced` is not used, and no leverage is read. -/
theorem atomPluckerTenth_of_pentagonFloor (hfloor : AtomPentagonFloor) : AtomPluckerTenth := by
  intro atom hframe
  have hsum := atomDropMargin_familySum hframe
  have hdrop : ∀ slotOne slotTwo slotThree slotFour slotFive : Fin 6,
      0 ≤ atomDropMargin atom slotOne slotTwo slotThree slotFour slotFive := by
    intro slotOne slotTwo slotThree slotFour slotFive
    rw [atomDropMargin_eq_pentagonMargin]
    exact hfloor _ _ _ _ _
  have h0 := hdrop 1 2 3 4 5
  have h1 := hdrop 0 2 3 4 5
  have h2 := hdrop 0 1 3 4 5
  have h3 := hdrop 0 1 2 4 5
  have h4 := hdrop 0 1 2 3 5
  have h5 := hdrop 0 1 2 3 4
  linarith

/-- The pentagon floor also closes the leverage residue that
`Gtz.Wave.PluckerSchurFloor` left, because it closes the whole tenth. -/
theorem atomPluckerTenthUnbalanced_of_pentagonFloor (hfloor : AtomPentagonFloor) :
    AtomPluckerTenthUnbalanced :=
  fun atom hframe _ => atomPluckerTenth_of_pentagonFloor hfloor atom hframe

/-- **THE PENTAGON FLOOR SPENDS AT ONE TENTH.**  It gives the spectral supply at
one tenth, which is the best constant the determinantal-energy route can ever
carry, and twenty percent past the landed `Gtz.atomSpectralSupply_twelfth`. -/
theorem atomSpectralSupply_tenth_of_pentagonFloor (hfloor : AtomPentagonFloor) :
    AtomSpectralSupply (1 / 10) :=
  atomSpectralSupply_tenth_of_pluckerTenth (atomPluckerTenth_of_pentagonFloor hfloor)

/-! ## Layer 4 — the twelve, recovered from the same decomposition -/

/-- **THE TWELVE COMES BACK FROM THE PENTAGON FLOOR OF CAUCHY-SCHWARZ.**  The
Cauchy-Schwarz floor of the pentagon reading, summed over the six five-slot
families, is exactly the landed `Gtz.atomPluckerEnergyTwo_le_twelve`.

So the whole distance from twelve to ten is the distance from
`Gtz.atomPentagonReading_ge_neg_quad` to `Gtz.AtomPentagonFloor`, and that
distance is one rank-two statement. -/
theorem atomPluckerEnergyTwo_le_twelve_of_pentagon
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomPluckerEnergyTwo atom ≤ 12 * atomPluckerEnergyThree atom := by
  have hsum := atomDropMargin_familySum hframe
  have hb0 := atomPentagonReading_ge_neg_quad (atomBlockDet atom 1 2 3)
    (atomBlockDet atom 1 2 4) (atomBlockDet atom 1 2 5) (atomBlockDet atom 1 3 4)
    (atomBlockDet atom 1 3 5) (atomBlockDet atom 1 4 5) (atomBlockDet atom 2 3 4)
    (atomBlockDet atom 2 3 5) (atomBlockDet atom 2 4 5) (atomBlockDet atom 3 4 5)
  have hb1 := atomPentagonReading_ge_neg_quad (atomBlockDet atom 0 2 3)
    (atomBlockDet atom 0 2 4) (atomBlockDet atom 0 2 5) (atomBlockDet atom 0 3 4)
    (atomBlockDet atom 0 3 5) (atomBlockDet atom 0 4 5) (atomBlockDet atom 2 3 4)
    (atomBlockDet atom 2 3 5) (atomBlockDet atom 2 4 5) (atomBlockDet atom 3 4 5)
  have hb2 := atomPentagonReading_ge_neg_quad (atomBlockDet atom 0 1 3)
    (atomBlockDet atom 0 1 4) (atomBlockDet atom 0 1 5) (atomBlockDet atom 0 3 4)
    (atomBlockDet atom 0 3 5) (atomBlockDet atom 0 4 5) (atomBlockDet atom 1 3 4)
    (atomBlockDet atom 1 3 5) (atomBlockDet atom 1 4 5) (atomBlockDet atom 3 4 5)
  have hb3 := atomPentagonReading_ge_neg_quad (atomBlockDet atom 0 1 2)
    (atomBlockDet atom 0 1 4) (atomBlockDet atom 0 1 5) (atomBlockDet atom 0 2 4)
    (atomBlockDet atom 0 2 5) (atomBlockDet atom 0 4 5) (atomBlockDet atom 1 2 4)
    (atomBlockDet atom 1 2 5) (atomBlockDet atom 1 4 5) (atomBlockDet atom 2 4 5)
  have hb4 := atomPentagonReading_ge_neg_quad (atomBlockDet atom 0 1 2)
    (atomBlockDet atom 0 1 3) (atomBlockDet atom 0 1 5) (atomBlockDet atom 0 2 3)
    (atomBlockDet atom 0 2 5) (atomBlockDet atom 0 3 5) (atomBlockDet atom 1 2 3)
    (atomBlockDet atom 1 2 5) (atomBlockDet atom 1 3 5) (atomBlockDet atom 2 3 5)
  have hb5 := atomPentagonReading_ge_neg_quad (atomBlockDet atom 0 1 2)
    (atomBlockDet atom 0 1 3) (atomBlockDet atom 0 1 4) (atomBlockDet atom 0 2 3)
    (atomBlockDet atom 0 2 4) (atomBlockDet atom 0 3 4) (atomBlockDet atom 1 2 3)
    (atomBlockDet atom 1 2 4) (atomBlockDet atom 1 3 4) (atomBlockDet atom 2 3 4)
  simp only [atomDropMargin] at hsum
  simp only [atomPluckerEnergyThree, atomTripleFamilySum] at hsum ⊢
  linarith

/-! ## Layer 5 — the four-slot grouping, and why it is too fine -/

/-- The FOUR-SLOT READING of the four readings of a four-slot family. -/
def atomQuadReading (readOneTwoThree readOneTwoFour readOneThreeFour readTwoThreeFour : ℝ) : ℝ :=
  10 * (readOneTwoThree ^ 2 + readOneTwoFour ^ 2 + readOneThreeFour ^ 2 + readTwoThreeFour ^ 2)
    - 3 * (readOneTwoThree + readOneTwoFour + readOneThreeFour + readTwoThreeFour) ^ 2

/-- The QUAD MARGIN of a four-slot family of a six-atom family. -/
noncomputable def atomQuadMargin (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree slotFour : Fin 6) : ℝ :=
  atomQuadReading (atomBlockDet atom slotOne slotTwo slotThree)
    (atomBlockDet atom slotOne slotTwo slotFour) (atomBlockDet atom slotOne slotThree slotFour)
    (atomBlockDet atom slotTwo slotThree slotFour)

/-- **THE FINER FAMILY IDENTITY.**  Three times the gap of the tenth is the total
of the fifteen quad margins.  It is exact, and it is finer than the five-slot
identity, because every five-slot family carries five four-slot families and
every four-slot family sits in two five-slot families.

But the quad margin is NOT always positive.  Refer to
`Gtz.atomQuadMargin_tetraFrame`. -/
theorem atomQuadMargin_familySum
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    3 * (10 * atomPluckerEnergyThree atom - atomPluckerEnergyTwo atom)
      = atomQuadMargin atom 0 1 2 3 + atomQuadMargin atom 0 1 2 4 + atomQuadMargin atom 0 1 2 5
        + atomQuadMargin atom 0 1 3 4 + atomQuadMargin atom 0 1 3 5 + atomQuadMargin atom 0 1 4 5
        + atomQuadMargin atom 0 2 3 4 + atomQuadMargin atom 0 2 3 5 + atomQuadMargin atom 0 2 4 5
        + atomQuadMargin atom 0 3 4 5 + atomQuadMargin atom 1 2 3 4 + atomQuadMargin atom 1 2 3 5
        + atomQuadMargin atom 1 2 4 5 + atomQuadMargin atom 1 3 4 5
        + atomQuadMargin atom 2 3 4 5 := by
  have h01 := atomMarginal_01 hframe
  have h02 := atomMarginal_02 hframe
  have h03 := atomMarginal_03 hframe
  have h04 := atomMarginal_04 hframe
  have h05 := atomMarginal_05 hframe
  have h12 := atomMarginal_12 hframe
  have h13 := atomMarginal_13 hframe
  have h14 := atomMarginal_14 hframe
  have h15 := atomMarginal_15 hframe
  have h23 := atomMarginal_23 hframe
  have h24 := atomMarginal_24 hframe
  have h25 := atomMarginal_25 hframe
  have h34 := atomMarginal_34 hframe
  have h35 := atomMarginal_35 hframe
  have h45 := atomMarginal_45 hframe
  simp only [atomPluckerEnergyThree, atomPluckerEnergyTwo, atomTripleFamilySum,
    atomPairFamilySum, atomQuadMargin, atomQuadReading]
  linear_combination (3 * (atomBlockPairMinor atom 0 1
      + (atomBlockDet atom 0 1 2 + atomBlockDet atom 0 1 3 + atomBlockDet atom 0 1 4
        + atomBlockDet atom 0 1 5))) * h01
    + (3 * (atomBlockPairMinor atom 0 2
      + (atomBlockDet atom 0 1 2 + atomBlockDet atom 0 2 3 + atomBlockDet atom 0 2 4
        + atomBlockDet atom 0 2 5))) * h02
    + (3 * (atomBlockPairMinor atom 0 3
      + (atomBlockDet atom 0 1 3 + atomBlockDet atom 0 2 3 + atomBlockDet atom 0 3 4
        + atomBlockDet atom 0 3 5))) * h03
    + (3 * (atomBlockPairMinor atom 0 4
      + (atomBlockDet atom 0 1 4 + atomBlockDet atom 0 2 4 + atomBlockDet atom 0 3 4
        + atomBlockDet atom 0 4 5))) * h04
    + (3 * (atomBlockPairMinor atom 0 5
      + (atomBlockDet atom 0 1 5 + atomBlockDet atom 0 2 5 + atomBlockDet atom 0 3 5
        + atomBlockDet atom 0 4 5))) * h05
    + (3 * (atomBlockPairMinor atom 1 2
      + (atomBlockDet atom 0 1 2 + atomBlockDet atom 1 2 3 + atomBlockDet atom 1 2 4
        + atomBlockDet atom 1 2 5))) * h12
    + (3 * (atomBlockPairMinor atom 1 3
      + (atomBlockDet atom 0 1 3 + atomBlockDet atom 1 2 3 + atomBlockDet atom 1 3 4
        + atomBlockDet atom 1 3 5))) * h13
    + (3 * (atomBlockPairMinor atom 1 4
      + (atomBlockDet atom 0 1 4 + atomBlockDet atom 1 2 4 + atomBlockDet atom 1 3 4
        + atomBlockDet atom 1 4 5))) * h14
    + (3 * (atomBlockPairMinor atom 1 5
      + (atomBlockDet atom 0 1 5 + atomBlockDet atom 1 2 5 + atomBlockDet atom 1 3 5
        + atomBlockDet atom 1 4 5))) * h15
    + (3 * (atomBlockPairMinor atom 2 3
      + (atomBlockDet atom 0 2 3 + atomBlockDet atom 1 2 3 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 2 3 5))) * h23
    + (3 * (atomBlockPairMinor atom 2 4
      + (atomBlockDet atom 0 2 4 + atomBlockDet atom 1 2 4 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 2 4 5))) * h24
    + (3 * (atomBlockPairMinor atom 2 5
      + (atomBlockDet atom 0 2 5 + atomBlockDet atom 1 2 5 + atomBlockDet atom 2 3 5
        + atomBlockDet atom 2 4 5))) * h25
    + (3 * (atomBlockPairMinor atom 3 4
      + (atomBlockDet atom 0 3 4 + atomBlockDet atom 1 3 4 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 3 4 5))) * h34
    + (3 * (atomBlockPairMinor atom 3 5
      + (atomBlockDet atom 0 3 5 + atomBlockDet atom 1 3 5 + atomBlockDet atom 2 3 5
        + atomBlockDet atom 3 4 5))) * h35
    + (3 * (atomBlockPairMinor atom 4 5
      + (atomBlockDet atom 0 4 5 + atomBlockDet atom 1 4 5 + atomBlockDet atom 2 4 5
        + atomBlockDet atom 3 4 5))) * h45

/-- **THE TETRAHEDRAL FRAME.**  Four atoms at the corners of a regular
tetrahedron, each of squared length three quarters, together with two zero
atoms.  It is a real rank-three Parseval frame of six atoms, so it lives inside
the deciding cell. -/
noncomputable def atomTetraFrame : Fin 6 → (Fin 3 → ℝ) :=
  ![![1 / 2, 1 / 2, 1 / 2], ![1 / 2, -(1 / 2), -(1 / 2)], ![-(1 / 2), 1 / 2, -(1 / 2)],
    ![-(1 / 2), -(1 / 2), 1 / 2], ![0, 0, 0], ![0, 0, 0]]

theorem atomTetraFrame_isTightFrame (probe direction : Fin 3 → ℝ) :
    (∑ slot, (atomTetraFrame slot ⬝ᵥ probe) * (atomTetraFrame slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  simp [Fin.sum_univ_six, atomTetraFrame, dotProduct, Fin.sum_univ_three]
  ring

/-- The Gram of the tetrahedral frame.  The four live atoms carry the leverage
three quarters and the inner product minus one quarter, and every entry that
touches a zero atom is zero. -/
theorem atomTetraFrame_gram_diag : atomGram atomTetraFrame 0 0 = 3 / 4
    ∧ atomGram atomTetraFrame 1 1 = 3 / 4 ∧ atomGram atomTetraFrame 2 2 = 3 / 4
    ∧ atomGram atomTetraFrame 3 3 = 3 / 4 ∧ atomGram atomTetraFrame 4 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [atomGram, atomTetraFrame, dotProduct, Fin.sum_univ_three] <;> norm_num

theorem atomTetraFrame_gram_live : atomGram atomTetraFrame 0 1 = -(1 / 4)
    ∧ atomGram atomTetraFrame 0 2 = -(1 / 4) ∧ atomGram atomTetraFrame 0 3 = -(1 / 4)
    ∧ atomGram atomTetraFrame 1 2 = -(1 / 4) ∧ atomGram atomTetraFrame 1 3 = -(1 / 4)
    ∧ atomGram atomTetraFrame 2 3 = -(1 / 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [atomGram, atomTetraFrame, dotProduct, Fin.sum_univ_three] <;> norm_num

theorem atomTetraFrame_gram_dead : atomGram atomTetraFrame 0 4 = 0
    ∧ atomGram atomTetraFrame 1 4 = 0 ∧ atomGram atomTetraFrame 2 4 = 0
    ∧ atomGram atomTetraFrame 3 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [atomGram, atomTetraFrame, dotProduct, Fin.sum_univ_three]

/-- The ten block determinants of the five-slot family `0 1 2 3 4` of the
tetrahedral frame.  The four triples inside the tetrahedron read one quarter and
every triple that meets a zero atom reads zero. -/
theorem atomTetraFrame_blockDet :
    atomBlockDet atomTetraFrame 0 1 2 = 1 / 4 ∧ atomBlockDet atomTetraFrame 0 1 3 = 1 / 4
      ∧ atomBlockDet atomTetraFrame 0 1 4 = 0 ∧ atomBlockDet atomTetraFrame 0 2 3 = 1 / 4
      ∧ atomBlockDet atomTetraFrame 0 2 4 = 0 ∧ atomBlockDet atomTetraFrame 0 3 4 = 0
      ∧ atomBlockDet atomTetraFrame 1 2 3 = 1 / 4 ∧ atomBlockDet atomTetraFrame 1 2 4 = 0
      ∧ atomBlockDet atomTetraFrame 1 3 4 = 0 ∧ atomBlockDet atomTetraFrame 2 3 4 = 0 := by
  obtain ⟨g00, g11, g22, g33, g44⟩ := atomTetraFrame_gram_diag
  obtain ⟨g01, g02, g03, g12, g13, g23⟩ := atomTetraFrame_gram_live
  obtain ⟨g04, g14, g24, g34⟩ := atomTetraFrame_gram_dead
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [atomBlockDet, g00, g11, g22, g33, g44, g01, g02, g03, g12, g13, g23,
      g04, g14, g24, g34] <;> norm_num

/-- **THE FOUR-SLOT READING IS REFUTED AT A FRAME OF THE CELL.**  The four atoms
of `Gtz.atomTetraFrame` carry four equal block determinants, and the four-slot
reading there is `-1/2`.

So the four-slot grouping of `Gtz.atomQuadMargin_familySum` cannot be closed term
by term, and a successor lane must not try.  In scale-free readings the same
witness reads `atomQuadReading 16 16 16 16 = -2048`. -/
theorem atomQuadMargin_tetraFrame : atomQuadMargin atomTetraFrame 0 1 2 3 = -(1 / 2) := by
  obtain ⟨d012, d013, -, d023, -, -, d123, -, -, -⟩ := atomTetraFrame_blockDet
  simp only [atomQuadMargin, atomQuadReading, d012, d013, d023, d123]
  norm_num

theorem atomQuadReading_flat_refuted : atomQuadReading 16 16 16 16 = -2048 := by
  simp only [atomQuadReading]; norm_num

/-- **THE FIVE-SLOT GROUPING REPAIRS IT.**  At the same tetrahedral frame the
pentagon reading of the family `0 1 2 3 4` is `5/4`, which is positive.  The one
negative four-slot reading is paid for by the four positive ones inside the same
five-slot family. -/
theorem atomDropMargin_tetraFrame : atomDropMargin atomTetraFrame 0 1 2 3 4 = 5 / 4 := by
  obtain ⟨d012, d013, d014, d023, d024, d034, d123, d124, d134, d234⟩ := atomTetraFrame_blockDet
  simp only [atomDropMargin, atomPentagonReading, d012, d013, d014, d023, d024, d034,
    d123, d124, d134, d234]
  norm_num

/-! ## Layer 6 — a new unconditional floor for the level-two energy -/

/-- The LEVERAGE SPREAD of a six-atom family: the total of the squared distances
of the six leverages from one half.  It is zero exactly on `Gtz.AtomBalanced`. -/
noncomputable def atomLeverageSpread (atom : Fin 6 → (Fin 3 → ℝ)) : ℝ :=
  (atomGram atom 0 0 - 1 / 2) ^ 2 + (atomGram atom 1 1 - 1 / 2) ^ 2
    + (atomGram atom 2 2 - 1 / 2) ^ 2 + (atomGram atom 3 3 - 1 / 2) ^ 2
    + (atomGram atom 4 4 - 1 / 2) ^ 2 + (atomGram atom 5 5 - 1 / 2) ^ 2

/-- The BALANCE GAP of the level-two energy: the total over the fifteen pairs of
the squared distance of the pair minor from the value that the two leverages
alone predict. -/
noncomputable def atomPairBalanceGap (atom : Fin 6 → (Fin 3 → ℝ)) : ℝ :=
  atomPairFamilySum fun rowSlot colSlot =>
    (atomBlockPairMinor atom rowSlot colSlot - 1 / 5
      - (atomGram atom rowSlot rowSlot + atomGram atom colSlot colSlot - 1) / 2) ^ 2

/-- **THE ROW LAW OF THE PAIR MINORS.**  The pair minors of one slot total twice
its leverage.  The diagonal pair minor is zero, so the total over all six slots
and the total over the five other slots agree. -/
theorem atomBlockPairMinor_row
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot : Fin 6) :
    (∑ colSlot, atomBlockPairMinor atom rowSlot colSlot)
      = 2 * atomGram atom rowSlot rowSlot := by
  have hrow := atomGram_row_energy hframe rowSlot
  have htrace := atomGram_trace (atom := atom) hframe
  have hsplit : (∑ colSlot, atomBlockPairMinor atom rowSlot colSlot)
      = atomGram atom rowSlot rowSlot * (∑ colSlot, atomGram atom colSlot colSlot)
        - ∑ colSlot, atomGram atom rowSlot colSlot ^ 2 := by
    simp only [atomBlockPairMinor, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
  rw [hsplit, hrow, htrace]
  norm_num
  ring

/-- **THE BALANCE IDENTITY OF THE LEVEL-TWO ENERGY, ABSTRACTLY.**  Fifteen pair
readings and six leverage readings that obey the six row laws and the trace law
satisfy an exact identity: the level-two energy is three fifths, plus the
leverage spread, plus a total of fifteen squares. -/
theorem atomPairSpread_identity
    (pairZeroOne pairZeroTwo pairZeroThree pairZeroFour pairZeroFive pairOneTwo pairOneThree
      pairOneFour pairOneFive pairTwoThree pairTwoFour pairTwoFive pairThreeFour pairThreeFive
      pairFourFive : ℝ)
    (levZero levOne levTwo levThree levFour levFive : ℝ)
    (hrowZero : pairZeroOne + pairZeroTwo + pairZeroThree + pairZeroFour + pairZeroFive
      = 2 * levZero)
    (hrowOne : pairZeroOne + pairOneTwo + pairOneThree + pairOneFour + pairOneFive = 2 * levOne)
    (hrowTwo : pairZeroTwo + pairOneTwo + pairTwoThree + pairTwoFour + pairTwoFive = 2 * levTwo)
    (hrowThree : pairZeroThree + pairOneThree + pairTwoThree + pairThreeFour + pairThreeFive
      = 2 * levThree)
    (hrowFour : pairZeroFour + pairOneFour + pairTwoFour + pairThreeFour + pairFourFive
      = 2 * levFour)
    (hrowFive : pairZeroFive + pairOneFive + pairTwoFive + pairThreeFive + pairFourFive
      = 2 * levFive)
    (htrace : levZero + levOne + levTwo + levThree + levFour + levFive = 3) :
    (pairZeroOne ^ 2 + pairZeroTwo ^ 2 + pairZeroThree ^ 2 + pairZeroFour ^ 2 + pairZeroFive ^ 2
        + pairOneTwo ^ 2 + pairOneThree ^ 2 + pairOneFour ^ 2 + pairOneFive ^ 2
        + pairTwoThree ^ 2 + pairTwoFour ^ 2 + pairTwoFive ^ 2 + pairThreeFour ^ 2
        + pairThreeFive ^ 2 + pairFourFive ^ 2)
      - 3 / 5
      - ((levZero - 1 / 2) ^ 2 + (levOne - 1 / 2) ^ 2 + (levTwo - 1 / 2) ^ 2
        + (levThree - 1 / 2) ^ 2 + (levFour - 1 / 2) ^ 2 + (levFive - 1 / 2) ^ 2)
      = (pairZeroOne - 1 / 5 - (levZero + levOne - 1) / 2) ^ 2
        + (pairZeroTwo - 1 / 5 - (levZero + levTwo - 1) / 2) ^ 2
        + (pairZeroThree - 1 / 5 - (levZero + levThree - 1) / 2) ^ 2
        + (pairZeroFour - 1 / 5 - (levZero + levFour - 1) / 2) ^ 2
        + (pairZeroFive - 1 / 5 - (levZero + levFive - 1) / 2) ^ 2
        + (pairOneTwo - 1 / 5 - (levOne + levTwo - 1) / 2) ^ 2
        + (pairOneThree - 1 / 5 - (levOne + levThree - 1) / 2) ^ 2
        + (pairOneFour - 1 / 5 - (levOne + levFour - 1) / 2) ^ 2
        + (pairOneFive - 1 / 5 - (levOne + levFive - 1) / 2) ^ 2
        + (pairTwoThree - 1 / 5 - (levTwo + levThree - 1) / 2) ^ 2
        + (pairTwoFour - 1 / 5 - (levTwo + levFour - 1) / 2) ^ 2
        + (pairTwoFive - 1 / 5 - (levTwo + levFive - 1) / 2) ^ 2
        + (pairThreeFour - 1 / 5 - (levThree + levFour - 1) / 2) ^ 2
        + (pairThreeFive - 1 / 5 - (levThree + levFive - 1) / 2) ^ 2
        + (pairFourFive - 1 / 5 - (levFour + levFive - 1) / 2) ^ 2 := by
  linear_combination (levZero - 3 / 10) * hrowZero + (levOne - 3 / 10) * hrowOne
    + (levTwo - 3 / 10) * hrowTwo + (levThree - 3 / 10) * hrowThree
    + (levFour - 3 / 10) * hrowFour + (levFive - 3 / 10) * hrowFive
    - (1 / 4) * (levZero + levOne + levTwo + levThree + levFour + levFive - 23 / 5) * htrace

/-- **THE LEVEL-TWO ENERGY NEVER FALLS BELOW THREE FIFTHS PLUS THE SPREAD.**
This is an exact identity, and it is new: the level-two energy of a real
rank-three Parseval frame of six atoms is three fifths plus the leverage spread
plus a total of fifteen squares.

Three fifths is what fifteen equal pair minors give, and the icosahedral frame is
where it is attained. -/
theorem atomPluckerEnergyTwo_spread_identity
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomPluckerEnergyTwo atom - 3 / 5 - atomLeverageSpread atom = atomPairBalanceGap atom := by
  have hcomm : ∀ rowSlot colSlot : Fin 6,
      atomBlockPairMinor atom colSlot rowSlot = atomBlockPairMinor atom rowSlot colSlot := by
    intro rowSlot colSlot
    simp only [atomBlockPairMinor, atomGram_comm atom colSlot rowSlot]
    ring
  have hdiag : ∀ slot : Fin 6, atomBlockPairMinor atom slot slot = 0 := by
    intro slot; simp only [atomBlockPairMinor]; ring
  have hrow : ∀ rowSlot : Fin 6,
      (∑ colSlot, atomBlockPairMinor atom rowSlot colSlot) = 2 * atomGram atom rowSlot rowSlot :=
    atomBlockPairMinor_row hframe
  have hr0 := hrow 0
  have hr1 := hrow 1
  have hr2 := hrow 2
  have hr3 := hrow 3
  have hr4 := hrow 4
  have hr5 := hrow 5
  simp only [Fin.sum_univ_six, hdiag, hcomm 0 1, hcomm 0 2, hcomm 0 3, hcomm 0 4, hcomm 0 5,
    hcomm 1 2, hcomm 1 3, hcomm 1 4, hcomm 1 5, hcomm 2 3, hcomm 2 4, hcomm 2 5,
    hcomm 3 4, hcomm 3 5, hcomm 4 5] at hr0 hr1 hr2 hr3 hr4 hr5
  have htrace := atomGram_trace (atom := atom) hframe
  simp only [Fin.sum_univ_six] at htrace
  simp only [atomPluckerEnergyTwo, atomPairBalanceGap, atomPairFamilySum, atomLeverageSpread]
  exact atomPairSpread_identity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by push_cast at htrace; linarith)

/-- **THE LEVEL-TWO FLOOR.**  A corollary of the identity. -/
theorem atomPluckerEnergyTwo_ge_spread
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    3 / 5 + atomLeverageSpread atom ≤ atomPluckerEnergyTwo atom := by
  have hid := atomPluckerEnergyTwo_spread_identity hframe
  have hnn : 0 ≤ atomPairBalanceGap atom := by
    simp only [atomPairBalanceGap, atomPairFamilySum]
    positivity
  linarith

/-- **WHAT THE PENTAGON FLOOR WOULD BUY AT LEVEL THREE.**  The level-two floor
and the tenth together pin the level-three energy from below, and the constant
`3/50` is exactly the icosahedral reading. -/
theorem atomPluckerEnergyThree_ge_of_pentagonFloor (hfloor : AtomPentagonFloor)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    3 / 50 + atomLeverageSpread atom / 10 ≤ atomPluckerEnergyThree atom := by
  have htenth := atomPluckerTenth_of_pentagonFloor hfloor atom hframe
  have hfloor2 := atomPluckerEnergyTwo_ge_spread hframe
  linarith

end Gtz
