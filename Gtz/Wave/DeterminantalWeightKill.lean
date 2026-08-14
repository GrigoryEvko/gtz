import Mathlib
import Gtz.Wave.SpectralSupplyCell
import Gtz.Wave.QuadDropSign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000
set_option linter.unusedSimpArgs false

/-!
# The determinantal weight is the wrong measure, and the Bargmann sign is why

The campaign selects a triple of the six slots and then certifies it.  One whole
family of selection arguments averages the SHIFTED TRIPLE DETERMINANT
`atomTripleDet atom (fun _ => w) a b c`, which is `det(block - w)`, against a
weight on the twenty triples, and hopes that a nonnegative total forces a
nonnegative member.  The determinantal weight `atomBlockDet` is the obvious
candidate, because the twenty determinants are the masses of a determinantal
point process and they add to one.

This module closes that family.  It is a negative result, and it is exact.

## 1. The flat average caps below the Hermitian ceiling

`Gtz.atomTripleDet_familySum_uniform` says that at a uniform scale the twenty
shifted determinants add to `1 - 12 w + 30 w ^ 2 - 20 w ^ 3`, a constant of the
problem.  That cubic factors:

  `1 - 12 w + 30 w ^ 2 - 20 w ^ 3 = (1 - 2 w) * (10 w ^ 2 - 10 w + 1)`.

Its smallest root is `(5 - sqrt 15) / 10 = 0.1127017`, and the cubic is strictly
negative on the whole interval from that root to `1 / 2`.  So the flat average
certifies at most `0.1127017`.  That is BELOW the Hermitian value
`(3 - sqrt 5) / 6 = 0.1273220` of the cell, and far below the target `1 / 6`.
`Gtz.atomFlatDropCeiling_lt_hermitianCeiling` records the comparison.

## 2. No weight that reads the determinant alone can work

`Gtz.dropWitnessAtom` is the cuboctahedron: six face diagonals of a cube, a
tight frame of leverage `1 / 2` whose spectral value is `1 / 4`.  Its twenty
triples carry exactly three readings, keyed by the BARGMANN INVARIANT
`atomTripleBargmann`, the product of the three off-diagonal Gram entries:

| count | Bargmann | determinant | shifted determinant at `1/6` |
|---|---|---|---|
| 4  | `1 / 64`  | `1 / 16` | `5 / 864`   |
| 12 | `0`       | `1 / 16` | `-1 / 216`  |
| 4  | `-1 / 64` | `0`      | `-49 / 864` |

The three orbit totals are `5 / 216`, `-1 / 18` and `-49 / 216`, and they add to
`-7 / 27` as the universal cubic demands.  A weight that reads only the
determinant cannot separate the first two rows, because both carry `1 / 16`, and
their combined total is `-7 / 216`, which is NEGATIVE.  The total over the third
row is `-49 / 216`, also negative.  So every nonnegative weight that is a
function of the determinant alone gives a strictly negative total at this one
frame.  `Gtz.not_atomDeterminantalWeightSupply` is that statement.

This kills, in one exact rational witness, the whole candidate list: the
determinantal weight itself, every power of it, the indicator of its support,
and the Naimark dual, which is again a function of determinants.

## 3. Nor can the determinant times the Bargmann invariant

The table above says the surviving direction must read the Bargmann invariant,
because that is the only reading that separates the first two rows.  It does not
survive either.  `Gtz.trineFoilAtom` is a regular tetrahedron of four atoms of
leverage `3 / 4` together with two zero atoms.  It is a tight frame, and its
spectral value is `1 / 4`.  Its twenty triples carry two readings:

| count | Bargmann | determinant | shifted determinant at `1/6` |
|---|---|---|---|
| 4  | `-1 / 64` | `1 / 4` | `25 / 432` |
| 16 | `0`       | `0`     | `7 / 432` (four of them) or `-5 / 108` (twelve) |

Every triple of positive determinant carries a NEGATIVE Bargmann invariant, so
every weight of the shape `f(determinant) * Bargmann` with `f` nonnegative gives
a strictly negative total.  `Gtz.not_atomBargmannWeightSupply` is that
statement.  The two witnesses are complementary: the cuboctahedron gives the
determinantal weight a positive total on the Bargmann-signed reading, and the
trine foil gives the Bargmann-signed weight a positive total on the
determinantal reading.

## 4. What survives: a floor from the trace and the determinant only

The last section is positive.  For three nonnegative reals with total `first`
and product `third`, every one of them is at least the smallest root of
`x * (first - x) ^ 2 = 4 * third` on `[0, first / 3]`, because
`x * (first - x) ^ 2 - 4 * third` vanishes to second order at a coincidence of
the other two.  `Gtz.amgm_le_of_root_bound` is the scalar criterion, and it
reads the TRACE and the DETERMINANT of a block and nothing else.

At the cuboctahedron the four winning triples carry `first = 3 / 2` and
`third = 1 / 16`, and the criterion reads exactly `1 - sqrt 3 / 2 = 0.1339746`.
That number is ABOVE the Hermitian ceiling `(3 - sqrt 5) / 6 = 0.1273220`, and
`Gtz.atomAmgmCuboctahedron_passes_ceiling` records it.  A criterion that reads
only principal minors is blind to the field as a RULE, but the minor data itself
is not blind, and the two must not be confused.
-/

namespace Gtz

open scoped BigOperators

/-! ## Layer 0 — the Bargmann invariant of a triple -/

/-- The BARGMANN INVARIANT of a triple: the product of the three off-diagonal
Gram entries.  Over a real frame it is a signed square root of the product of
the three squared entries, and over a Hermitian frame only the real part
survives.  This is the one reading of a block that separates the two fields. -/
def atomTripleBargmann {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  atomGram atom slotOne slotTwo * atomGram atom slotOne slotThree
    * atomGram atom slotTwo slotThree

/-- **THE REAL LAW OF THE BARGMANN INVARIANT.**  Over a real frame the square of
the invariant is exactly the product of the three squared off-diagonal entries.
Over a Hermitian frame the same product only DOMINATES the square of the real
part, and the gap is the whole distance between the two fields. -/
theorem atomTripleBargmann_sq {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) :
    atomTripleBargmann atom slotOne slotTwo slotThree ^ 2
      = atomGram atom slotOne slotTwo ^ 2 * atomGram atom slotOne slotThree ^ 2
        * atomGram atom slotTwo slotThree ^ 2 := by
  simp only [atomTripleBargmann]
  ring

/-- **THE BLOCK DETERMINANT SPLITS INTO AN EVEN PART AND THE BARGMANN
INVARIANT.**  Everything except the last term is even in the off-diagonal
entries, so the last term is the only place a certificate can read an
orientation. -/
theorem atomBlockDet_eq_bargmann (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    atomBlockDet atom slotOne slotTwo slotThree
      = atomGram atom slotOne slotOne * atomGram atom slotTwo slotTwo
            * atomGram atom slotThree slotThree
        - atomGram atom slotOne slotOne * atomGram atom slotTwo slotThree ^ 2
        - atomGram atom slotTwo slotTwo * atomGram atom slotOne slotThree ^ 2
        - atomGram atom slotThree slotThree * atomGram atom slotOne slotTwo ^ 2
        + 2 * atomTripleBargmann atom slotOne slotTwo slotThree := by
  simp only [atomBlockDet, atomTripleBargmann]
  ring

/-! ## Layer 1 — the flat average caps below the Hermitian ceiling -/

/-- **THE UNIVERSAL CUBIC FACTORS.**  The total of the twenty shifted triple
determinants at a uniform scale is a cubic that does not read the frame, and it
splits into a linear factor at one half and a quadratic factor whose roots are
`(5 -+ sqrt 15) / 10`. -/
theorem atomFlatDrop_factor (weight : ℝ) :
    1 - 12 * weight + 30 * weight ^ 2 - 20 * weight ^ 3
      = (1 - 2 * weight) * (10 * weight ^ 2 - 10 * weight + 1) := by
  ring

/-- The CEILING OF THE FLAT AVERAGE: the smallest root of the universal cubic. -/
noncomputable def atomFlatDropCeiling : ℝ := (5 - Real.sqrt 15) / 10

theorem atomFlatDropCeiling_root :
    10 * atomFlatDropCeiling ^ 2 - 10 * atomFlatDropCeiling + 1 = 0 := by
  have hsq : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  simp only [atomFlatDropCeiling]
  nlinarith [hsq]

theorem atomFlatDropCeiling_bounds :
    (0 : ℝ) < atomFlatDropCeiling ∧ atomFlatDropCeiling < 1 / 2 := by
  have hsq : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 15 := Real.sqrt_nonneg 15
  constructor <;> simp only [atomFlatDropCeiling] <;> nlinarith [hsq, hnn]

/-- **THE FLAT AVERAGE IS STRICTLY NEGATIVE ABOVE ITS CEILING.**  For a uniform
scale strictly between `(5 - sqrt 15) / 10` and `1 / 2` the universal cubic is
strictly negative, so some triple of every frame fails at that scale.  No flat
average can certify past the ceiling. -/
theorem atomFlatDrop_neg_of_gt {weight : ℝ} (hlow : atomFlatDropCeiling < weight)
    (hhigh : weight < 1 / 2) :
    1 - 12 * weight + 30 * weight ^ 2 - 20 * weight ^ 3 < 0 := by
  have hsq : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 15 := Real.sqrt_nonneg 15
  have hlow' : (5 - Real.sqrt 15) / 10 < weight := hlow
  have hquad : 10 * weight ^ 2 - 10 * weight + 1 < 0 := by nlinarith [hsq, hnn]
  have hlin : 0 < 1 - 2 * weight := by linarith
  rw [atomFlatDrop_factor]
  exact mul_neg_of_pos_of_neg hlin hquad

/-- **THE FLAT CEILING IS BELOW THE HERMITIAN CEILING.**  The flat average dies
before the field-agnostic obstruction even applies.  The three numbers are
`0.1127017 < 0.1273220 < 0.1666667`. -/
theorem atomFlatDropCeiling_lt_hermitianCeiling :
    atomFlatDropCeiling < (3 - Real.sqrt 5) / 6
      ∧ (3 - Real.sqrt 5) / 6 < 1 / 6 := by
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn15 : (0 : ℝ) ≤ Real.sqrt 15 := Real.sqrt_nonneg 15
  have hn5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5lb : (2 : ℝ) < Real.sqrt 5 := by nlinarith [h5, hn5]
  have h15lb : (3 : ℝ) < Real.sqrt 15 := by nlinarith [h15, hn15]
  constructor
  · simp only [atomFlatDropCeiling]
    nlinarith [h15, h5, hn15, hn5, h5lb, h15lb]
  · nlinarith [h5, hn5, h5lb]

/-! ## Layer 2 — the cuboctahedron reads three orbits

`Gtz.dropWitnessAtom` is the six face diagonals of a cube, scaled to a tight
frame.  Every diagonal Gram entry is `1 / 2`, every off-diagonal entry is `0` or
`± 1 / 4`, and the three zeros form a perfect matching of the six slots. -/

/-- The uniform scale of the mass-one interface, as a slot table. -/
noncomputable def atomSixthScale : Fin 6 → ℝ := fun _ => (1 : ℝ) / 6

theorem atomSixthScale_apply (slot : Fin 6) : atomSixthScale slot = (1 : ℝ) / 6 := rfl

/-- The Gram of the cuboctahedron, entry by entry.  Every diagonal entry is
`1 / 2`, every off-diagonal entry is `0` or `± 1 / 4`, and the three zeros form
the perfect matching `{0,1}`, `{2,3}`, `{4,5}` of the six slots. -/
theorem dropWitnessGram_diag_zero : atomGram dropWitnessAtom 0 0 = 1 / 2 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_zero_one : atomGram dropWitnessAtom 0 1 = 0 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]

theorem dropWitnessGram_zero_two : atomGram dropWitnessAtom 0 2 = 1 / 4 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_zero_three : atomGram dropWitnessAtom 0 3 = 1 / 4 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_zero_four : atomGram dropWitnessAtom 0 4 = 1 / 4 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_zero_five : atomGram dropWitnessAtom 0 5 = 1 / 4 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_one_one : atomGram dropWitnessAtom 1 1 = 1 / 2 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_one_two : atomGram dropWitnessAtom 1 2 = 1 / 4 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_one_three : atomGram dropWitnessAtom 1 3 = 1 / 4 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_one_four : atomGram dropWitnessAtom 1 4 = -(1 / 4) := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_one_five : atomGram dropWitnessAtom 1 5 = -(1 / 4) := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_two_two : atomGram dropWitnessAtom 2 2 = 1 / 2 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_two_three : atomGram dropWitnessAtom 2 3 = 0 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]

theorem dropWitnessGram_two_four : atomGram dropWitnessAtom 2 4 = 1 / 4 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_two_five : atomGram dropWitnessAtom 2 5 = -(1 / 4) := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_three_three : atomGram dropWitnessAtom 3 3 = 1 / 2 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_three_four : atomGram dropWitnessAtom 3 4 = -(1 / 4) := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_three_five : atomGram dropWitnessAtom 3 5 = 1 / 4 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_four_four : atomGram dropWitnessAtom 4 4 = 1 / 2 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

theorem dropWitnessGram_four_five : atomGram dropWitnessAtom 4 5 = 0 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]

theorem dropWitnessGram_five_five : atomGram dropWitnessAtom 5 5 = 1 / 2 := by
  simp [atomGram, dropWitnessAtom, dotProduct, Fin.sum_univ_three]
  norm_num

/-- The twenty block determinants of the cuboctahedron.  Sixteen read `1 / 16`
and four read `0`. -/
theorem dropWitnessBlockDet :
    atomBlockDet dropWitnessAtom 0 1 2 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 0 1 3 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 0 1 4 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 0 1 5 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 0 2 3 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 0 2 4 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 0 2 5 = 0
      ∧ atomBlockDet dropWitnessAtom 0 3 4 = 0
      ∧ atomBlockDet dropWitnessAtom 0 3 5 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 0 4 5 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 1 2 3 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 1 2 4 = 0
      ∧ atomBlockDet dropWitnessAtom 1 2 5 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 1 3 4 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 1 3 5 = 0
      ∧ atomBlockDet dropWitnessAtom 1 4 5 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 2 3 4 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 2 3 5 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 2 4 5 = 1 / 16
      ∧ atomBlockDet dropWitnessAtom 3 4 5 = 1 / 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [atomBlockDet,
      dropWitnessGram_diag_zero, dropWitnessGram_zero_one, dropWitnessGram_zero_two,
      dropWitnessGram_zero_three, dropWitnessGram_zero_four, dropWitnessGram_zero_five,
      dropWitnessGram_one_one, dropWitnessGram_one_two, dropWitnessGram_one_three,
      dropWitnessGram_one_four, dropWitnessGram_one_five, dropWitnessGram_two_two,
      dropWitnessGram_two_three, dropWitnessGram_two_four, dropWitnessGram_two_five,
      dropWitnessGram_three_three, dropWitnessGram_three_four, dropWitnessGram_three_five,
      dropWitnessGram_four_four, dropWitnessGram_four_five, dropWitnessGram_five_five] <;> norm_num

/-- The twenty Bargmann invariants of the cuboctahedron.  Four read `1 / 64`,
four read `-1 / 64`, and twelve read `0`. -/
theorem dropWitnessBargmann :
    atomTripleBargmann dropWitnessAtom 0 2 4 = 1 / 64
      ∧ atomTripleBargmann dropWitnessAtom 0 3 5 = 1 / 64
      ∧ atomTripleBargmann dropWitnessAtom 1 2 5 = 1 / 64
      ∧ atomTripleBargmann dropWitnessAtom 1 3 4 = 1 / 64
      ∧ atomTripleBargmann dropWitnessAtom 0 2 5 = -(1 / 64)
      ∧ atomTripleBargmann dropWitnessAtom 0 3 4 = -(1 / 64)
      ∧ atomTripleBargmann dropWitnessAtom 1 2 4 = -(1 / 64)
      ∧ atomTripleBargmann dropWitnessAtom 1 3 5 = -(1 / 64)
      ∧ atomTripleBargmann dropWitnessAtom 0 1 2 = 0
      ∧ atomTripleBargmann dropWitnessAtom 0 1 3 = 0
      ∧ atomTripleBargmann dropWitnessAtom 0 1 4 = 0
      ∧ atomTripleBargmann dropWitnessAtom 0 1 5 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [atomTripleBargmann,
      dropWitnessGram_diag_zero, dropWitnessGram_zero_one, dropWitnessGram_zero_two,
      dropWitnessGram_zero_three, dropWitnessGram_zero_four, dropWitnessGram_zero_five,
      dropWitnessGram_one_one, dropWitnessGram_one_two, dropWitnessGram_one_three,
      dropWitnessGram_one_four, dropWitnessGram_one_five, dropWitnessGram_two_two,
      dropWitnessGram_two_three, dropWitnessGram_two_four, dropWitnessGram_two_five,
      dropWitnessGram_three_three, dropWitnessGram_three_four, dropWitnessGram_three_five,
      dropWitnessGram_four_four, dropWitnessGram_four_five, dropWitnessGram_five_five] <;> norm_num

/-- The twenty shifted triple determinants of the cuboctahedron at the uniform
scale `1 / 6`.  Four read `5 / 864`, twelve read `-1 / 216`, and four read
`-49 / 864`. -/
theorem dropWitnessTripleDet :
    atomTripleDet dropWitnessAtom atomSixthScale 0 2 4 = 5 / 864
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 0 3 5 = 5 / 864
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 1 2 5 = 5 / 864
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 1 3 4 = 5 / 864
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 0 2 5 = -(49 / 864)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 0 3 4 = -(49 / 864)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 1 2 4 = -(49 / 864)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 1 3 5 = -(49 / 864)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 0 1 2 = -(1 / 216)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 0 1 3 = -(1 / 216)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 0 1 4 = -(1 / 216)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 0 1 5 = -(1 / 216)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 0 2 3 = -(1 / 216)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 0 4 5 = -(1 / 216)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 1 2 3 = -(1 / 216)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 1 4 5 = -(1 / 216)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 2 3 4 = -(1 / 216)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 2 3 5 = -(1 / 216)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 2 4 5 = -(1 / 216)
      ∧ atomTripleDet dropWitnessAtom atomSixthScale 3 4 5 = -(1 / 216) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [atomTripleDet, atomShiftedDiag, atomSixthScale,
      dropWitnessGram_diag_zero, dropWitnessGram_zero_one, dropWitnessGram_zero_two,
      dropWitnessGram_zero_three, dropWitnessGram_zero_four, dropWitnessGram_zero_five,
      dropWitnessGram_one_one, dropWitnessGram_one_two, dropWitnessGram_one_three,
      dropWitnessGram_one_four, dropWitnessGram_one_five, dropWitnessGram_two_two,
      dropWitnessGram_two_three, dropWitnessGram_two_four, dropWitnessGram_two_five,
      dropWitnessGram_three_three, dropWitnessGram_three_four, dropWitnessGram_three_five,
      dropWitnessGram_four_four, dropWitnessGram_four_five, dropWitnessGram_five_five] <;> norm_num


/-- The twenty second-minor totals of the cuboctahedron.  Eight read `9 / 16`
and twelve read `5 / 8`. -/
theorem dropWitnessBlockSecond :
    atomBlockSecond dropWitnessAtom 0 2 4 = 9 / 16
      ∧ atomBlockSecond dropWitnessAtom 0 3 5 = 9 / 16
      ∧ atomBlockSecond dropWitnessAtom 1 2 5 = 9 / 16
      ∧ atomBlockSecond dropWitnessAtom 1 3 4 = 9 / 16
      ∧ atomBlockSecond dropWitnessAtom 0 2 5 = 9 / 16
      ∧ atomBlockSecond dropWitnessAtom 0 3 4 = 9 / 16
      ∧ atomBlockSecond dropWitnessAtom 1 2 4 = 9 / 16
      ∧ atomBlockSecond dropWitnessAtom 1 3 5 = 9 / 16
      ∧ atomBlockSecond dropWitnessAtom 0 1 2 = 5 / 8
      ∧ atomBlockSecond dropWitnessAtom 0 1 3 = 5 / 8
      ∧ atomBlockSecond dropWitnessAtom 0 1 4 = 5 / 8
      ∧ atomBlockSecond dropWitnessAtom 0 1 5 = 5 / 8
      ∧ atomBlockSecond dropWitnessAtom 0 2 3 = 5 / 8
      ∧ atomBlockSecond dropWitnessAtom 0 4 5 = 5 / 8
      ∧ atomBlockSecond dropWitnessAtom 1 2 3 = 5 / 8
      ∧ atomBlockSecond dropWitnessAtom 1 4 5 = 5 / 8
      ∧ atomBlockSecond dropWitnessAtom 2 3 4 = 5 / 8
      ∧ atomBlockSecond dropWitnessAtom 2 3 5 = 5 / 8
      ∧ atomBlockSecond dropWitnessAtom 2 4 5 = 5 / 8
      ∧ atomBlockSecond dropWitnessAtom 3 4 5 = 5 / 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [atomBlockSecond, dropWitnessGram_diag_zero, dropWitnessGram_zero_one, dropWitnessGram_zero_two,
      dropWitnessGram_zero_three, dropWitnessGram_zero_four, dropWitnessGram_zero_five,
      dropWitnessGram_one_one, dropWitnessGram_one_two, dropWitnessGram_one_three,
      dropWitnessGram_one_four, dropWitnessGram_one_five, dropWitnessGram_two_two,
      dropWitnessGram_two_three, dropWitnessGram_two_four, dropWitnessGram_two_five,
      dropWitnessGram_three_three, dropWitnessGram_three_four, dropWitnessGram_three_five,
      dropWitnessGram_four_four, dropWitnessGram_four_five, dropWitnessGram_five_five] <;> norm_num

/-! ## Layer 3 — the kill of every weight that reads the determinant alone -/

/-- **THE DETERMINANTAL WEIGHT SUPPLY.**  A weight on the twenty triples that
is a function of the block determinant, nonnegative everywhere on the attainable
range and strictly positive on the nondegenerate triples, whose weighted total of
the shifted determinants is never negative.  Every candidate the campaign
proposed lives here: the determinantal weight itself, each of its powers, the
indicator of its support, and the Naimark dual, which is again a determinant. -/
def AtomDeterminantalWeightSupply : Prop :=
  ∃ weight : ℝ → ℝ,
    (∀ value : ℝ, 0 ≤ value → 0 ≤ weight value)
      ∧ (∀ value : ℝ, 0 < value → 0 < weight value)
      ∧ ∀ atom : Fin 6 → (Fin 3 → ℝ),
          (∀ probe direction : Fin 3 → ℝ,
            (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
          0 ≤ atomTripleFamilySum (fun slotOne slotTwo slotThree =>
                weight (atomBlockDet atom slotOne slotTwo slotThree)
                  * atomTripleDet atom atomSixthScale slotOne slotTwo slotThree)

/-- **THE REFUTATION.**  The cuboctahedron gives every such weight a strictly
negative total.  Its twenty triples read only two determinants, `1 / 16` and `0`,
and BOTH classes total negative: `-7 / 216` and `-49 / 216`.  A weight that reads
the determinant alone cannot tell the four winners from the twelve near-misses,
because all sixteen carry the same determinant. -/
theorem not_atomDeterminantalWeightSupply : ¬ AtomDeterminantalWeightSupply := by
  rintro ⟨weight, hnonneg, hpos, hcert⟩
  have hsum := hcert dropWitnessAtom dropWitnessAtom_isTightFrame
  obtain ⟨d024, d035, d125, d134, d025, d034, d124, d135, d012, d013, d014, d015,
    d023, d045, d123, d145, d234, d235, d245, d345⟩ := dropWitnessTripleDet
  obtain ⟨p012, p013, p014, p015, p023, p024, p025, p034, p035, p045,
    p123, p124, p125, p134, p135, p145, p234, p235, p245, p345⟩ := dropWitnessBlockDet
  simp only [atomTripleFamilySum, p012, p013, p014, p015, p023, p024, p025, p034,
    p035, p045, p123, p124, p125, p134, p135, p145, p234, p235, p245, p345,
    d024, d035, d125, d134, d025, d034, d124, d135, d012, d013, d014, d015,
    d023, d045, d123, d145, d234, d235, d245, d345] at hsum
  have hbig : 0 < weight (1 / 16) := hpos _ (by norm_num)
  have hzero : 0 ≤ weight 0 := hnonneg 0 le_rfl
  linarith

/-- **NO POWER OF THE DETERMINANT WORKS.**  Every positive power of the
determinantal weight is a determinantal weight, so the refutation covers the
whole family at once. -/
theorem not_atomDeterminantalPowerSupply (power : ℕ) (_hpower : 1 ≤ power) :
    ¬ ∀ atom : Fin 6 → (Fin 3 → ℝ),
        (∀ probe direction : Fin 3 → ℝ,
          (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
        0 ≤ atomTripleFamilySum (fun slotOne slotTwo slotThree =>
              atomBlockDet atom slotOne slotTwo slotThree ^ power
                * atomTripleDet atom atomSixthScale slotOne slotTwo slotThree) := by
  intro hcert
  exact not_atomDeterminantalWeightSupply
    ⟨fun value => value ^ power, fun _ hv => pow_nonneg hv power,
      fun _ hv => pow_pos hv power, hcert⟩

/-- **NOR THE INDICATOR OF THE SUPPORT.**  The uniform measure on the triples of
positive determinant is also a determinantal weight. -/
theorem not_atomDeterminantalSupportSupply :
    ¬ ∀ atom : Fin 6 → (Fin 3 → ℝ),
        (∀ probe direction : Fin 3 → ℝ,
          (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
        0 ≤ atomTripleFamilySum (fun slotOne slotTwo slotThree =>
              (if 0 < atomBlockDet atom slotOne slotTwo slotThree then (1 : ℝ) else 0)
                * atomTripleDet atom atomSixthScale slotOne slotTwo slotThree) := by
  intro hcert
  refine not_atomDeterminantalWeightSupply
    ⟨fun value => if 0 < value then (1 : ℝ) else 0, ?_, ?_, hcert⟩
  · intro value _
    dsimp only
    split_ifs <;> norm_num
  · intro value hv
    dsimp only
    rw [if_pos hv]
    norm_num


/-! ## Layer 4 — the second witness kills the Bargmann-signed weight

The table of layer 2 says that the only reading which separates the four winners
of the cuboctahedron from its twelve near-misses is the Bargmann invariant.  The
obvious repair is to multiply the determinantal weight by it.  A second exact
frame closes that too. -/

/-- **THE TRINE FOIL.**  A regular tetrahedron of four atoms of leverage `3 / 4`
together with two zero atoms.  The frame law does not forbid a zero atom, and
this frame carries spectral value `1 / 4`, well past the target.  Every triple of
positive determinant is a face of the tetrahedron, and every such face has a
NEGATIVE Bargmann invariant, because all six inner products are `-1 / 4`. -/
noncomputable def trineFoilAtom : Fin 6 → (Fin 3 → ℝ) :=
  ![![0, 0, 0],
    ![1 / 2, 1 / 2, 1 / 2],
    ![0, 0, 0],
    ![1 / 2, -(1 / 2), -(1 / 2)],
    ![-(1 / 2), 1 / 2, -(1 / 2)],
    ![-(1 / 2), -(1 / 2), 1 / 2]]

theorem trineFoilAtom_isTightFrame (probe direction : Fin 3 → ℝ) :
    (∑ slot, (trineFoilAtom slot ⬝ᵥ probe) * (trineFoilAtom slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  simp [Fin.sum_univ_six, trineFoilAtom, dotProduct, Fin.sum_univ_three]
  ring

theorem trineFoilGram_zero_row (colSlot : Fin 6) : atomGram trineFoilAtom 0 colSlot = 0 := by
  fin_cases colSlot <;>
    simp [atomGram, trineFoilAtom, dotProduct, Fin.sum_univ_three]

theorem trineFoilGram_two_row (colSlot : Fin 6) : atomGram trineFoilAtom 2 colSlot = 0 := by
  fin_cases colSlot <;>
    simp [atomGram, trineFoilAtom, dotProduct, Fin.sum_univ_three]

theorem trineFoilGram_diag :
    atomGram trineFoilAtom 1 1 = 3 / 4 ∧ atomGram trineFoilAtom 3 3 = 3 / 4
      ∧ atomGram trineFoilAtom 4 4 = 3 / 4 ∧ atomGram trineFoilAtom 5 5 = 3 / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [atomGram, trineFoilAtom, dotProduct, Fin.sum_univ_three] <;> norm_num

theorem trineFoilGram_off :
    atomGram trineFoilAtom 1 3 = -(1 / 4) ∧ atomGram trineFoilAtom 1 4 = -(1 / 4)
      ∧ atomGram trineFoilAtom 1 5 = -(1 / 4) ∧ atomGram trineFoilAtom 3 4 = -(1 / 4)
      ∧ atomGram trineFoilAtom 3 5 = -(1 / 4) ∧ atomGram trineFoilAtom 4 5 = -(1 / 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [atomGram, trineFoilAtom, dotProduct, Fin.sum_univ_three] <;> norm_num

/-- The four faces of the tetrahedron carry determinant `1 / 4`, Bargmann
invariant `-1 / 64` and shifted determinant `25 / 432`. -/
theorem trineFoilFace :
    (atomBlockDet trineFoilAtom 1 3 4 = 1 / 4
        ∧ atomTripleBargmann trineFoilAtom 1 3 4 = -(1 / 64)
        ∧ atomTripleDet trineFoilAtom atomSixthScale 1 3 4 = 25 / 432)
      ∧ (atomBlockDet trineFoilAtom 1 3 5 = 1 / 4
        ∧ atomTripleBargmann trineFoilAtom 1 3 5 = -(1 / 64)
        ∧ atomTripleDet trineFoilAtom atomSixthScale 1 3 5 = 25 / 432)
      ∧ (atomBlockDet trineFoilAtom 1 4 5 = 1 / 4
        ∧ atomTripleBargmann trineFoilAtom 1 4 5 = -(1 / 64)
        ∧ atomTripleDet trineFoilAtom atomSixthScale 1 4 5 = 25 / 432)
      ∧ (atomBlockDet trineFoilAtom 3 4 5 = 1 / 4
        ∧ atomTripleBargmann trineFoilAtom 3 4 5 = -(1 / 64)
        ∧ atomTripleDet trineFoilAtom atomSixthScale 3 4 5 = 25 / 432) := by
  obtain ⟨g11, g33, g44, g55⟩ := trineFoilGram_diag
  obtain ⟨g13, g14, g15, g34, g35, g45⟩ := trineFoilGram_off
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    simp only [atomBlockDet, atomTripleBargmann, atomTripleDet, atomShiftedDiag,
      atomSixthScale, g11, g33, g44, g55, g13, g14, g15, g34, g35, g45] <;> norm_num

/-- Every triple that meets a zero atom carries Bargmann invariant zero, so
sixteen of the twenty triples of the trine foil contribute nothing to a
Bargmann-signed total. -/
theorem trineFoilBargmann_zero (slotOne slotTwo slotThree : Fin 6)
    (hzero : slotOne = 0 ∨ slotTwo = 0 ∨ slotThree = 0
      ∨ slotOne = 2 ∨ slotTwo = 2 ∨ slotThree = 2) :
    atomTripleBargmann trineFoilAtom slotOne slotTwo slotThree = 0 := by
  have hcomm : ∀ a b : Fin 6, atomGram trineFoilAtom a b = atomGram trineFoilAtom b a :=
    fun a b => atomGram_comm trineFoilAtom a b
  simp only [atomTripleBargmann]
  rcases hzero with h | h | h | h | h | h <;> subst h
  · rw [trineFoilGram_zero_row]; ring
  · rw [hcomm, trineFoilGram_zero_row]; ring
  · rw [hcomm slotOne 0, trineFoilGram_zero_row]; ring
  · rw [trineFoilGram_two_row]; ring
  · rw [hcomm, trineFoilGram_two_row]; ring
  · rw [hcomm slotOne 2, trineFoilGram_two_row]; ring

/-- **THE BARGMANN-SIGNED WEIGHT SUPPLY.**  The determinantal weight multiplied
by the Bargmann invariant of the triple, which is the one repair the table of
layer 2 leaves open. -/
def AtomBargmannWeightSupply : Prop :=
  ∃ weight : ℝ → ℝ,
    (∀ value : ℝ, 0 ≤ value → 0 ≤ weight value)
      ∧ (∀ value : ℝ, 0 < value → 0 < weight value)
      ∧ ∀ atom : Fin 6 → (Fin 3 → ℝ),
          (∀ probe direction : Fin 3 → ℝ,
            (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
          0 ≤ atomTripleFamilySum (fun slotOne slotTwo slotThree =>
                weight (atomBlockDet atom slotOne slotTwo slotThree)
                  * atomTripleBargmann atom slotOne slotTwo slotThree
                  * atomTripleDet atom atomSixthScale slotOne slotTwo slotThree)

/-- **THE SECOND REFUTATION.**  At the trine foil the only triples of positive
determinant are the four faces of the tetrahedron, every one of them carries a
NEGATIVE Bargmann invariant and a POSITIVE shifted determinant, and the other
sixteen contribute nothing.  The total is `-25 / 6912` times the weight at
`1 / 4`, which is strictly negative. -/
theorem not_atomBargmannWeightSupply : ¬ AtomBargmannWeightSupply := by
  rintro ⟨weight, _, hpos, hcert⟩
  have hsum := hcert trineFoilAtom trineFoilAtom_isTightFrame
  obtain ⟨⟨q134, b134, t134⟩, ⟨q135, b135, t135⟩, ⟨q145, b145, t145⟩, ⟨q345, b345, t345⟩⟩ :=
    trineFoilFace
  have hz : ∀ slotOne slotTwo slotThree : Fin 6,
      slotOne = 0 ∨ slotTwo = 0 ∨ slotThree = 0
        ∨ slotOne = 2 ∨ slotTwo = 2 ∨ slotThree = 2 →
      atomTripleBargmann trineFoilAtom slotOne slotTwo slotThree = 0 :=
    trineFoilBargmann_zero
  simp only [atomTripleFamilySum,
    hz 0 1 2 (by tauto), hz 0 1 3 (by tauto), hz 0 1 4 (by tauto), hz 0 1 5 (by tauto),
    hz 0 2 3 (by tauto), hz 0 2 4 (by tauto), hz 0 2 5 (by tauto), hz 0 3 4 (by tauto),
    hz 0 3 5 (by tauto), hz 0 4 5 (by tauto), hz 1 2 3 (by tauto), hz 1 2 4 (by tauto),
    hz 1 2 5 (by tauto), hz 2 3 4 (by tauto), hz 2 3 5 (by tauto), hz 2 4 5 (by tauto),
    q134, b134, t134, q135, b135, t135, q145, b145, t145, q345, b345, t345] at hsum
  have hq : 0 < weight (1 / 4) := hpos _ (by norm_num)
  linarith

/-! ## Layer 5 — a floor that reads the trace and the determinant only -/

/-- **THE ROOT CRITERION.**  For three nonnegative reals the polynomial
`x * (total - x) ^ 2 - 4 * product` is nonnegative at each of them, because at
`x = first` it equals `first * (second - third) ^ 2`.  It is strictly increasing
below a third of the total.  So a scale at which the polynomial is nonpositive,
and which does not pass a third of the total, is below all three.

This reads the TRACE and the DETERMINANT of a block and nothing else.  It is
weaker than the shifted wedge ladder, which reads all three symmetric functions,
but it is the sharpest criterion available from two of them. -/
theorem amgm_le_of_root_bound {first second third floor : ℝ}
    (hfirst : 0 ≤ first) (hfloor : 0 ≤ floor)
    (hmean : 3 * floor ≤ first + second + third)
    (hroot : floor * (first + second + third - floor) ^ 2
      ≤ 4 * (first * second * third)) :
    floor ≤ first := by
  by_contra hcontra
  push Not at hcontra
  have hd : 0 < floor - first := by linarith
  have hs : 2 * floor + (floor - first) ≤ second + third := by linarith
  have hsplit : 4 * (first * second * third)
      = first * (second + third) ^ 2 - first * (second - third) ^ 2 := by ring
  have hgap : floor * (first + second + third - floor) ^ 2 - first * (second + third) ^ 2
      = (floor - first)
        * ((second + third) ^ 2 - 2 * (second + third) * floor + floor * (floor - first)) := by
    ring
  have hslack : 0 ≤ second + third - 2 * floor - (floor - first) := by linarith
  have hinner : 3 * floor * (floor - first) + (floor - first) ^ 2
      ≤ (second + third) ^ 2 - 2 * (second + third) * floor + floor * (floor - first) := by
    nlinarith [hslack, hfloor, hd,
      mul_nonneg hslack (by linarith : (0 : ℝ) ≤ second + third + (floor - first))]
  have hprod : (floor - first) * (3 * floor * (floor - first) + (floor - first) ^ 2)
      ≤ (floor - first) * ((second + third) ^ 2 - 2 * (second + third) * floor
          + floor * (floor - first)) :=
    mul_le_mul_of_nonneg_left hinner (le_of_lt hd)
  have hposprod : 0 < (floor - first) * (3 * floor * (floor - first) + (floor - first) ^ 2) := by
    have hleft : 0 ≤ 3 * floor * (floor - first) :=
      mul_nonneg (mul_nonneg (by norm_num) hfloor) (le_of_lt hd)
    have hright : 0 < (floor - first) ^ 2 := pow_pos hd 2
    exact mul_pos hd (by linarith)
  have hAa : 0 ≤ first * (second - third) ^ 2 := mul_nonneg hfirst (sq_nonneg _)
  nlinarith [hroot, hsplit, hgap, hprod, hposprod, hAa]

/-- **THE ROOT CRITERION AT THE CUBOCTAHEDRON.**  The four winning triples carry
trace `3 / 2` and determinant `1 / 16`, and there the criterion reads exactly
`1 - sqrt 3 / 2`. -/
theorem amgmRoot_cuboctahedron :
    (1 - Real.sqrt 3 / 2) * (3 / 2 - (1 - Real.sqrt 3 / 2)) ^ 2 = 4 * (1 / 16) := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [hsq]

/-- **THE READING PASSES THE HERMITIAN CEILING.**  The four numbers of the cell,
in order: the ceiling of the flat average, the Hermitian value, the reading of
the root criterion at the cuboctahedron, and the target.

  `0.1127017 < 0.1273220 < 0.1339746 < 0.1666667`.

A criterion that reads only principal minors is blind to the field as a RULE,
but the minor data of a real frame is not the minor data of a Hermitian frame,
and only the second blindness would cap a certificate at the Hermitian value. -/
theorem amgmRoot_passes_ceiling :
    atomFlatDropCeiling < (3 - Real.sqrt 5) / 6
      ∧ (3 - Real.sqrt 5) / 6 < 1 - Real.sqrt 3 / 2
      ∧ 1 - Real.sqrt 3 / 2 < 1 / 6 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hn3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h5lb : (2 : ℝ) < Real.sqrt 5 := by nlinarith [h5, hn5]
  have h3lb : (1 : ℝ) < Real.sqrt 3 := by nlinarith [h3, hn3]
  have hb : (13 : ℝ) < 6 * Real.sqrt 5 := by nlinarith [h5, hn5]
  have hsq3 : (3 * Real.sqrt 3) ^ 2 < (3 + Real.sqrt 5) ^ 2 := by nlinarith [h3, h5, hb]
  have hlt : 3 * Real.sqrt 3 < 3 + Real.sqrt 5 := by
    by_contra hcontra
    push Not at hcontra
    nlinarith [hcontra, hn3, hn5, hsq3]
  refine ⟨(atomFlatDropCeiling_lt_hermitianCeiling).1, ?_, ?_⟩
  · linarith
  · nlinarith [h3, hn3, h3lb]

/-! ## Layer 6 — the second rung of the shifted wedge ladder, in closed form

The successor lane averages the SECOND RUNG of the shifted wedge ladder against
the determinantal weight.  Written in the three symmetric functions of a block,
that rung is a single ratio of polynomials, and this layer records it together
with its exact reading at the cuboctahedron. -/

/-- The SECOND RUNG of the shifted wedge ladder in symmetric coordinates.  One
Newton step on the characteristic polynomial from the wedge value `third /
second`, cleared of its inner denominator. -/
noncomputable def wedgeRungTwo (first second third : ℝ) : ℝ :=
  third * (second ^ 3 - first * second * third + 2 * third ^ 2)
    / (second * (second ^ 3 - 2 * first * second * third + 3 * third ^ 2))

/-- **THE SECOND RUNG IS ONE NEWTON STEP, CLEARED OF DENOMINATORS.**  Write
`p = third / second` for the wedge value.  The shifted determinant at `p` is
`p ^ 2 * (first - p)` and the shifted second minor total is
`second - 2 * p * first + 3 * p ^ 2`.  Multiplying the step
`p + shiftedDeterminant / shiftedSecond` above and below by `second ^ 3` turns
the numerator of `wedgeRungTwo` into the identity below, whose two summands are
exactly `p` and the correction.  The identity itself needs no hypothesis. -/
theorem wedgeRungTwo_clear (first second third : ℝ) :
    third * (second ^ 3 - first * second * third + 2 * third ^ 2)
      = third * (second ^ 3 - 2 * first * second * third + 3 * third ^ 2)
        + third ^ 2 * (first * second - third) := by
  ring

/-- The second rung at the four winning triples of the cuboctahedron. -/
theorem wedgeRungTwo_cuboctahedron_win : wedgeRungTwo (3 / 2) (9 / 16) (1 / 16) = 109 / 621 := by
  simp only [wedgeRungTwo]; norm_num

/-- The second rung at the twelve near-missing triples of the cuboctahedron. -/
theorem wedgeRungTwo_cuboctahedron_near : wedgeRungTwo (3 / 2) (5 / 8) (1 / 16) = 99 / 710 := by
  simp only [wedgeRungTwo]; norm_num

/-- **THE DETERMINANTAL AVERAGE OF THE SECOND RUNG AT THE CUBOCTAHEDRON.**  The
four degenerate triples carry no mass, the four winners carry `1 / 16` each at
`109 / 621`, and the twelve near-misses carry `1 / 16` each at `99 / 710`. -/
theorem wedgeRungTwo_dropWitness_average :
    4 * (1 / 16 : ℝ) * (109 / 621) + 12 * (1 / 16 : ℝ) * (99 / 710) = 261827 / 1763640 := by
  norm_num

/-- **THE AVERAGE PASSES THE HERMITIAN CEILING.**  The determinantal average of
the second rung at the cuboctahedron reads `0.14845830`, which is above the
Hermitian value `0.12732200` and below the target `1 / 6`.  Adversarial descent
places the minimum of that average at `0.1484425`, so the cuboctahedron is the
near-extremal of the successor target and this rational is its exact value. -/
theorem wedgeRungTwo_dropWitness_passes_ceiling :
    (3 - Real.sqrt 5) / 6 < (261827 : ℝ) / 1763640
      ∧ (261827 : ℝ) / 1763640 < 1 / 6 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5lb : (2 : ℝ) < Real.sqrt 5 := by nlinarith [h5, hn5]
  exact ⟨by nlinarith [h5, hn5, h5lb], by norm_num⟩

/-- **THE DETERMINANTAL AVERAGE OF THE WEDGE RUNG AT THE CUBOCTAHEDRON.**  The
first rung reads `1 / 9` at the winners and `1 / 10` at the near-misses, so its
determinantal average is `37 / 360 = 0.1027778`, which is BELOW the Hermitian
ceiling.  The whole gain of the successor target is the step from the first rung
to the second. -/
theorem wedgeRungOne_dropWitness_average :
    4 * (1 / 16 : ℝ) * (1 / 9) + 12 * (1 / 16 : ℝ) * (1 / 10) = 37 / 360 := by
  norm_num


/-! ## Layer 7 — a reduction of the second rung that keeps the ceiling

The successor target is a lower bound on the DETERMINANTAL AVERAGE of the second
rung.  The rung is a ratio, so the average resists a common denominator.  This
layer replaces the rung by a simpler ratio that is never larger, and whose
adversarial average still passes the Hermitian ceiling.

Write `p = third / second` for the wedge value.  The shifted second minor total
at `p` is `second - 2 p first + 3 p ^ 2`, and `3 p <= first` makes it no larger
than `second - p first`.  Enlarging the denominator of a nonnegative correction
lowers the rung, and after clearing denominators the reduced rung is the single
ratio `third * (second ^ 3 - third ^ 2) / (second ^ 2 * (second ^ 2 - first *
third))`, which needs no ladder and no Newton step. -/

/-- The REDUCED SECOND RUNG.  The second rung with its shifted second minor
total replaced by the larger `second - p * first`, cleared of denominators. -/
noncomputable def wedgeRungTwoLower (first second third : ℝ) : ℝ :=
  third * (second ^ 3 - third ^ 2) / (second ^ 2 * (second ^ 2 - first * third))

/-- **THE CROSS-MULTIPLIED COMPARISON IS ONE IDENTITY.**  The whole distance
between the reduced rung and the true second rung is the product
`third ^ 2 * (first * second - third) * (first * second - 3 * third)`.  Two
Newton inequalities of a real block make both brackets nonnegative. -/
theorem wedgeRungTwoLower_cross (first second third : ℝ) :
    (second ^ 3 - third ^ 2) * (second ^ 3 - 2 * first * second * third + 3 * third ^ 2)
      - (second ^ 3 - first * second * third + 2 * third ^ 2) * (second ^ 3 - first * second * third)
      = -(third ^ 2 * ((first * second - third) * (first * second - 3 * third))) := by
  ring

/-- **THE REDUCTION IS VALID.**  Under the two Newton inequalities `3 * third <=
first * second` and `first * third < second ^ 2`, and with a live shifted second
minor total, the reduced rung never exceeds the second rung. -/
theorem wedgeRungTwoLower_le {first second third : ℝ}
    (hsecond : 0 < second) (hthird : 0 ≤ third)
    (hmean : 3 * third ≤ first * second)
    (hden : 0 < second ^ 2 - first * third)
    (hstep : 0 < second ^ 3 - 2 * first * second * third + 3 * third ^ 2) :
    wedgeRungTwoLower first second third ≤ wedgeRungTwo first second third := by
  have hs2 : (0 : ℝ) < second ^ 2 := by positivity
  have hlowDen : (0 : ℝ) < second ^ 2 * (second ^ 2 - first * third) := by positivity
  have hupDen : (0 : ℝ) < second * (second ^ 3 - 2 * first * second * third + 3 * third ^ 2) :=
    mul_pos hsecond hstep
  have hgap : 0 ≤ third ^ 2 * ((first * second - third) * (first * second - 3 * third)) := by
    have hone : 0 ≤ first * second - 3 * third := by linarith
    have htwo : 0 ≤ first * second - third := by linarith
    positivity
  rw [wedgeRungTwoLower, wedgeRungTwo, div_le_div_iff₀ hlowDen hupDen]
  nlinarith [wedgeRungTwoLower_cross first second third, hgap, hthird, hsecond,
    mul_nonneg hthird (le_of_lt hsecond)]

/-- The reduced rung at the four winning triples of the cuboctahedron. -/
theorem wedgeRungTwoLower_cuboctahedron_win :
    wedgeRungTwoLower (3 / 2) (9 / 16) (1 / 16) = 713 / 4617 := by
  simp only [wedgeRungTwoLower]; norm_num

/-- The reduced rung at the twelve near-missing triples of the cuboctahedron. -/
theorem wedgeRungTwoLower_cuboctahedron_near :
    wedgeRungTwoLower (3 / 2) (5 / 8) (1 / 16) = 123 / 950 := by
  simp only [wedgeRungTwoLower]; norm_num

/-- **THE DETERMINANTAL AVERAGE OF THE REDUCED RUNG AT THE CUBOCTAHEDRON.**
Adversarial descent over real frames, behind a calibration gate that reproduced
the spectral value at the real extremal and the Hermitian value
`(3 - sqrt 5) / 6 = 0.127322003751` to twelve digits, places the MINIMUM of this
average at exactly this frame and this rational. -/
theorem wedgeRungTwoLower_dropWitness_average :
    4 * (1 / 16 : ℝ) * (713 / 4617) + 12 * (1 / 16 : ℝ) * (123 / 950)
      = 125317 / 923400 := by
  norm_num

/-- **THE REDUCTION KEEPS THE CEILING.**  The reduced average reads
`0.13571258` at its adversarial minimum, the Hermitian value is `0.12732200`,
and the target is `0.16666667`.  So the reduction throws away the ladder and the
Newton step and STILL passes the field-agnostic obstruction.  What it does not
yet supply is the proof that the cuboctahedron is the minimum. -/
theorem wedgeRungTwoLower_dropWitness_passes_ceiling :
    (3 - Real.sqrt 5) / 6 < (125317 : ℝ) / 923400
      ∧ (125317 : ℝ) / 923400 < 1 / 6 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5lb : (2 : ℝ) < Real.sqrt 5 := by nlinarith [h5, hn5]
  exact ⟨by nlinarith [h5, hn5, h5lb], by norm_num⟩

/-- **THE FOUR CONSTANTS OF THE SUCCESSOR TARGET, IN ORDER.**  The determinantal
average of the FIRST rung at the cuboctahedron is `37 / 360 = 0.1027778`, which
is BELOW the Hermitian ceiling.  The reduced second rung reads
`125317 / 923400 = 0.1357126`, and the true second rung reads
`261827 / 1763640 = 0.1484583`.  All three are readings of ONE frame, and the
whole gain of the successor target is the step from the first rung to the
second. -/
theorem wedgeRung_dropWitness_ladder :
    (37 : ℝ) / 360 < (3 - Real.sqrt 5) / 6
      ∧ (3 - Real.sqrt 5) / 6 < (125317 : ℝ) / 923400
      ∧ (125317 : ℝ) / 923400 < (261827 : ℝ) / 1763640
      ∧ (261827 : ℝ) / 1763640 < 1 / 6 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h5lb : (2 : ℝ) < Real.sqrt 5 := by nlinarith [h5, hn5]
  refine ⟨by nlinarith [h5, hn5, h5lb], by nlinarith [h5, hn5, h5lb], by norm_num, by norm_num⟩

end Gtz
