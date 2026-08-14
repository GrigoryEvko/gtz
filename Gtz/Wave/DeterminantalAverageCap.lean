import Mathlib
import Gtz.Wave.DeterminantalWeightKill
import Gtz.Wave.PluckerSchurFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The determinantal average of the reduced rung, and the cap on the moment programme

The campaign selects a triple of the six slots with the DETERMINANTAL MEASURE.
The twenty triple determinants total one (`Gtz.atomBlockDet_familySum`), so the
largest per-triple floor is at least the determinantal average of the floors.
With the reduced second rung `Gtz.wedgeRungTwoLower` as the floor, that average
is the target

  `sum over the twenty triples of p T * wedgeRungTwoLower (e1 T) (e2 T) (e3 T)`,

and the campaign wants a lower bound above the field-agnostic ceiling
`(3 - sqrt 5) / 6 = 0.127322003750`.

This module does four things.  Two are negative and two are positive.

## 1.  The extremal of the reduced rung is the cuboctahedron, not the icosahedron

`Gtz.wedgeAverageTerm` names one summand of the average, and
`Gtz.wedgeAverageTerm_eq` gives it in closed form:

  `p * wedgeRungTwoLower e1 e2 e3 = e3 ^ 2 * (e2 ^ 3 - e3 ^ 2)
                                     / (e2 ^ 2 * (e2 ^ 2 - e1 * e3))`.

At the ICOSAHEDRAL frame every triple carries `e1 = 3/2` and `e2 = 3/5`, and the
twenty determinants split ten and ten at `(5 +- sqrt 5) / 100`.
`Gtz.wedgeAverage_icosahedral` computes the average there EXACTLY, and the square
root cancels:

  `1637 / 12015 = 0.136246358718`.

The cuboctahedron reads `125317 / 923400 = 0.135712583929`
(`Gtz.wedgeRungTwoLower_dropWitness_average`), which is SMALLER.  So the
icosahedron is not the extremal of the reduced rung
(`Gtz.wedgeAverage_icosahedral_ladder`).

That contrast is the point.  `Gtz.pluckerAverage_icosahedral` shows that the
FIRST rung averages to exactly `1 / 10` at the same frame, which IS its extremal.
The extremal MOVES along the ladder: the first rung binds at the icosahedron, the
reduced second rung binds at the cuboctahedron, and adversarial descent puts the
full second rung at an unbalanced frame near the cuboctahedron.  A proof strategy
that assumes one binding frame for the whole ladder is built on sand.

## 2.  The moment programme cannot reach the ceiling

A frame forces UNIVERSAL READINGS on the twenty triples:

  `sum of e1 = 30`, `sum of e2 = 12`, `sum of e3 = 1`,

and each of the six slots carries the marginal laws
`sum over the ten triples that contain the slot of e3 = 1/2` and the same total
for `e2` equal to `6` at balanced leverages.  Layer 5 proves the three global
totals for every frame (`Gtz.atomFrameMomentTotals`), so the class is not empty.

The natural mechanized certificate reads ONLY those numbers, together with the
per-triple fact that the block spectrum lies in `[0,1] ^ 3`.  A tangent plane
`Phi >= alpha * e3 + beta * e2 + gamma` then gives the bound `alpha + 12 * beta +
20 * gamma` in one step.

`Gtz.not_atomMomentCap` closes that whole programme.  Twenty EQUAL triples, each
with the spectrum `(1/2, (1 - sqrt (3/5)) / 2, (1 + sqrt (3/5)) / 2)`, carry

  `e1 = 3/2`, `e2 = 3/5`, `e3 = 1/20`,

obey every one of the readings above, and average to `427 / 4104 = 0.104045`,
which is BELOW the ceiling.  A constant witness satisfies all six slot marginals
at once, so the refutation covers the marginal laws too.

## 3.  The energy floor is the missing ingredient, and it is not enough either

The witness of section 2 has `sum of e3 ^ 2 = 1 / 20 = 0.05`.  Layer 6 proves
that a real balanced frame obeys

  `3 / 50 <= sum over the twenty triples of p T ^ 2`   (`Gtz.atomPluckerEnergyThree_floor`),

which is `0.06`.  So the witness is NOT a frame, and the energy floor is exactly
what separates it from one.  The floor is new here and it is sharp at the
icosahedron.  Its proof is two steps: the fifteen pair minors total
`e2` of the Gram, which is `3` (`Gtz.atomPairMinor_familySum`), so
Cauchy-Schwarz over fifteen slots gives `3 / 5 <= E2`
(`Gtz.atomPluckerEnergyTwo_floor`), and `Gtz.atomPluckerTenth_of_balanced` gives
`E2 <= 10 * E3`.

`Gtz.not_atomMomentCap_withEnergy` shows that ADDING the energy floor still does
not reach the ceiling.  Ten triples carry `(3/2, 129/200, 29/400)` and ten carry
`(3/2, 111/200, 11/400)`, the ten and ten split slot-balanced five and five, so
every marginal law holds.  The energy total is `481 / 8000 = 0.060125`, which
passes the floor, and the average is `0.123836`, still below the ceiling.

So the moment programme is capped strictly below `(3 - sqrt 5) / 6`, with or
without the energy floor.  A certificate must consume a reading of the frame that
is NOT a moment of the twenty triples.  The heat matrix of
`Gtz.Wave.PluckerSchurFloor` is such a reading, and it is the only one the
campaign has.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

Every statement below is proved.  `Gtz.atomPluckerEnergyThree_floor` needs
`Gtz.AtomBalanced`, which the icosahedral frame and `Gtz.dropWitnessAtom` both
carry.

## Vacuity

`Gtz.atomPluckerEnergyThree_floor` is not vacuous:
`Gtz.atomPluckerEnergyThree_dropWitness` reads `1 / 16` at the standing red-team
frame, which passes the floor with room.  `Gtz.AtomMomentFeasible` is not
vacuous: `Gtz.atomMomentFeasible_uniform` and
`Gtz.atomMomentFeasible_split` exhibit two members.
-/

namespace Gtz

/-! ## Layer 0 — one summand of the determinantal average -/

/-- ONE SUMMAND of the determinantal average of the reduced second rung: the
triple determinant times the rung it carries. -/
noncomputable def wedgeAverageTerm (first second third : ℝ) : ℝ :=
  third * wedgeRungTwoLower first second third

/-- **THE SUMMAND IN CLOSED FORM.**  The determinant cancels one factor of the
numerator of the rung, so the summand is a single ratio whose numerator is
quadratic in the determinant. -/
theorem wedgeAverageTerm_eq (first second third : ℝ) :
    wedgeAverageTerm first second third
      = third ^ 2 * (second ^ 3 - third ^ 2)
        / (second ^ 2 * (second ^ 2 - first * third)) := by
  simp only [wedgeAverageTerm, wedgeRungTwoLower, ← mul_div_assoc]
  ring_nf

/-- The summand of the UNIFORM witness of layer 3. -/
theorem wedgeAverageTerm_uniform : wedgeAverageTerm (3 / 2) (3 / 5) (1 / 20) = 427 / 82080 := by
  simp only [wedgeAverageTerm, wedgeRungTwoLower]; norm_num

/-- The summand of the HEAVY class of the split witness of layer 4. -/
theorem wedgeAverageTerm_heavy :
    wedgeAverageTerm (3 / 2) (129 / 200) (29 / 400) = 1770001399 / 163627624800 := by
  simp only [wedgeAverageTerm, wedgeRungTwoLower]; norm_num

/-- The summand of the LIGHT class of the split witness of layer 4. -/
theorem wedgeAverageTerm_light :
    wedgeAverageTerm (3 / 2) (111 / 200) (11 / 400) = 164751301 / 105181912800 := by
  simp only [wedgeAverageTerm, wedgeRungTwoLower]; norm_num

/-! ## Layer 1 — the spectrum of a block lies in the unit box -/

/-- A triple of symmetric functions is a BLOCK SPECTRUM when it comes from three
readings in `[0,1]`.  The Gram block of a triple of a Parseval frame is a
principal block of a projection, so its three eigenvalues lie in `[0,1]` and its
symmetric functions are a block spectrum. -/
def AtomBlockSpectrum (first second third : ℝ) : Prop :=
  ∃ rootOne rootTwo rootThree : ℝ,
    0 ≤ rootOne ∧ rootOne ≤ 1 ∧ 0 ≤ rootTwo ∧ rootTwo ≤ 1
      ∧ 0 ≤ rootThree ∧ rootThree ≤ 1
      ∧ first = rootOne + rootTwo + rootThree
      ∧ second = rootOne * rootTwo + rootOne * rootThree + rootTwo * rootThree
      ∧ third = rootOne * rootTwo * rootThree

/-- **THE HALF FAMILY.**  For every product between `0` and `1/4` the readings
`(3/2, 1/2 + product, product / 2)` are a block spectrum.  The witness is
`(1/2, (1 - r) / 2, (1 + r) / 2)` with `r` the square root of `1 - 4 * product`,
which is the spectrum whose two free readings add to one.

Every witness of layers 3 and 4 comes from this one family. -/
theorem atomBlockSpectrum_half {product second third : ℝ}
    (hlow : 0 ≤ product) (hhigh : product ≤ 1 / 4)
    (hsecond : second = 1 / 2 + product) (hthird : third = product / 2) :
    AtomBlockSpectrum (3 / 2) second third := by
  have hnn : (0 : ℝ) ≤ 1 - 4 * product := by linarith
  have hsq : Real.sqrt (1 - 4 * product) ^ 2 = 1 - 4 * product := Real.sq_sqrt hnn
  have hrootnn : (0 : ℝ) ≤ Real.sqrt (1 - 4 * product) := Real.sqrt_nonneg _
  have hrootle : Real.sqrt (1 - 4 * product) ≤ 1 := by nlinarith [hsq, hrootnn, hlow]
  refine ⟨1 / 2, (1 - Real.sqrt (1 - 4 * product)) / 2,
    (1 + Real.sqrt (1 - 4 * product)) / 2, by norm_num, by norm_num, by linarith,
    by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
  · rw [hsecond]; nlinarith [hsq]
  · rw [hthird]; nlinarith [hsq]

/-- The block spectrum of the UNIFORM witness. -/
theorem atomBlockSpectrum_uniform : AtomBlockSpectrum (3 / 2) (3 / 5) (1 / 20) :=
  atomBlockSpectrum_half (product := 1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The block spectrum of the HEAVY class. -/
theorem atomBlockSpectrum_heavy : AtomBlockSpectrum (3 / 2) (129 / 200) (29 / 400) :=
  atomBlockSpectrum_half (product := 29 / 200) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The block spectrum of the LIGHT class. -/
theorem atomBlockSpectrum_light : AtomBlockSpectrum (3 / 2) (111 / 200) (11 / 400) :=
  atomBlockSpectrum_half (product := 11 / 200) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-! ## Layer 2 — the six slot marginals and the moment class -/

/-- The total of a triple reading over the TEN triples that contain slot `0`. -/
def atomSlotMarginalZero (value : Fin 6 → Fin 6 → Fin 6 → ℝ) : ℝ :=
  value 0 1 2 + value 0 1 3 + value 0 1 4 + value 0 1 5 + value 0 2 3
    + value 0 2 4 + value 0 2 5 + value 0 3 4 + value 0 3 5 + value 0 4 5

/-- The total of a triple reading over the TEN triples that contain slot `1`. -/
def atomSlotMarginalOne (value : Fin 6 → Fin 6 → Fin 6 → ℝ) : ℝ :=
  value 0 1 2 + value 0 1 3 + value 0 1 4 + value 0 1 5 + value 1 2 3
    + value 1 2 4 + value 1 2 5 + value 1 3 4 + value 1 3 5 + value 1 4 5

/-- The total of a triple reading over the TEN triples that contain slot `2`. -/
def atomSlotMarginalTwo (value : Fin 6 → Fin 6 → Fin 6 → ℝ) : ℝ :=
  value 0 1 2 + value 0 2 3 + value 0 2 4 + value 0 2 5 + value 1 2 3
    + value 1 2 4 + value 1 2 5 + value 2 3 4 + value 2 3 5 + value 2 4 5

/-- The total of a triple reading over the TEN triples that contain slot `3`. -/
def atomSlotMarginalThree (value : Fin 6 → Fin 6 → Fin 6 → ℝ) : ℝ :=
  value 0 1 3 + value 0 2 3 + value 0 3 4 + value 0 3 5 + value 1 2 3
    + value 1 3 4 + value 1 3 5 + value 2 3 4 + value 2 3 5 + value 3 4 5

/-- The total of a triple reading over the TEN triples that contain slot `4`. -/
def atomSlotMarginalFour (value : Fin 6 → Fin 6 → Fin 6 → ℝ) : ℝ :=
  value 0 1 4 + value 0 2 4 + value 0 3 4 + value 0 4 5 + value 1 2 4
    + value 1 3 4 + value 1 4 5 + value 2 3 4 + value 2 4 5 + value 3 4 5

/-- The total of a triple reading over the TEN triples that contain slot `5`. -/
def atomSlotMarginalFive (value : Fin 6 → Fin 6 → Fin 6 → ℝ) : ℝ :=
  value 0 1 5 + value 0 2 5 + value 0 3 5 + value 0 4 5 + value 1 2 5
    + value 1 3 5 + value 1 4 5 + value 2 3 5 + value 2 4 5 + value 3 4 5

/-- **THE MOMENT CLASS.**  Every reading of the twenty triples that a real
balanced Parseval frame of six atoms forces, and that a certificate can read
without looking at the frame again:

- each triple carries a block spectrum in the unit box,
- the three global totals are `30`, `12` and `1`,
- each of the six slots carries the determinantal marginal `1/2` and the second
  minor marginal `6`.

A certificate that reads only these numbers is exactly a certificate that is
valid for every member of this class. -/
def AtomMomentFeasible (first second third : Fin 6 → Fin 6 → Fin 6 → ℝ) : Prop :=
  (∀ slotOne slotTwo slotThree : Fin 6,
      AtomBlockSpectrum (first slotOne slotTwo slotThree) (second slotOne slotTwo slotThree)
        (third slotOne slotTwo slotThree))
    ∧ atomTripleFamilySum first = 30
    ∧ atomTripleFamilySum second = 12
    ∧ atomTripleFamilySum third = 1
    ∧ atomSlotMarginalZero third = 1 / 2 ∧ atomSlotMarginalOne third = 1 / 2
    ∧ atomSlotMarginalTwo third = 1 / 2 ∧ atomSlotMarginalThree third = 1 / 2
    ∧ atomSlotMarginalFour third = 1 / 2 ∧ atomSlotMarginalFive third = 1 / 2
    ∧ atomSlotMarginalZero second = 6 ∧ atomSlotMarginalOne second = 6
    ∧ atomSlotMarginalTwo second = 6 ∧ atomSlotMarginalThree second = 6
    ∧ atomSlotMarginalFour second = 6 ∧ atomSlotMarginalFive second = 6

/-- The DETERMINANTAL AVERAGE of the reduced second rung, read off moment data. -/
noncomputable def atomMomentAverage
    (first second third : Fin 6 → Fin 6 → Fin 6 → ℝ) : ℝ :=
  atomTripleFamilySum fun slotOne slotTwo slotThree =>
    wedgeAverageTerm (first slotOne slotTwo slotThree) (second slotOne slotTwo slotThree)
      (third slotOne slotTwo slotThree)

/-! ## Layer 3 — the uniform witness caps the moment programme -/

/-- The uniform witness reads `3/2` at every triple. -/
noncomputable def atomUniformFirst : Fin 6 → Fin 6 → Fin 6 → ℝ := fun _ _ _ => 3 / 2

/-- The uniform witness reads `3/5` at every triple. -/
noncomputable def atomUniformSecond : Fin 6 → Fin 6 → Fin 6 → ℝ := fun _ _ _ => 3 / 5

/-- The uniform witness reads `1/20` at every triple. -/
noncomputable def atomUniformThird : Fin 6 → Fin 6 → Fin 6 → ℝ := fun _ _ _ => 1 / 20

/-- **THE UNIFORM WITNESS IS IN THE MOMENT CLASS.**  Twenty equal triples satisfy
every slot marginal at once, because each slot carries exactly ten of them. -/
theorem atomMomentFeasible_uniform :
    AtomMomentFeasible atomUniformFirst atomUniformSecond atomUniformThird := by
  refine ⟨fun _ _ _ => atomBlockSpectrum_uniform, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [atomTripleFamilySum, atomSlotMarginalZero, atomSlotMarginalOne,
      atomSlotMarginalTwo, atomSlotMarginalThree, atomSlotMarginalFour, atomSlotMarginalFive,
      atomUniformFirst, atomUniformSecond, atomUniformThird] <;> norm_num

/-- The determinantal average of the uniform witness, exactly. -/
theorem atomMomentAverage_uniform :
    atomMomentAverage atomUniformFirst atomUniformSecond atomUniformThird = 427 / 4104 := by
  simp only [atomMomentAverage, atomTripleFamilySum, atomUniformFirst, atomUniformSecond,
    atomUniformThird, wedgeAverageTerm_uniform]
  norm_num

/-- **ONE EIGHTH IS BELOW THE FIELD-AGNOSTIC CEILING.**  The comparison every
refutation of this module ends with. -/
theorem atomEighth_lt_hermitianCeiling : (1 : ℝ) / 8 < (3 - Real.sqrt 5) / 6 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [hsq, hnn]

/-- **THE MOMENT PROGRAMME IS CAPPED.**  No lower bound at the field-agnostic
ceiling follows from the moment class alone.

The witness is twenty EQUAL triples of spectrum
`(1/2, (1 - sqrt (3/5)) / 2, (1 + sqrt (3/5)) / 2)`.  It obeys the three global
totals, all twelve slot marginals and the unit box, and its determinantal average
is `427 / 4104 = 0.1040448`, which is below `(3 - sqrt 5) / 6 = 0.1273220`.

A tangent-plane certificate `Phi >= alpha * e3 + beta * e2 + gamma` is a member of
the killed family, because its bound `alpha + 12 * beta + 20 * gamma` is a
function of the moment data only. -/
theorem not_atomMomentCap :
    ¬ ∀ first second third : Fin 6 → Fin 6 → Fin 6 → ℝ,
        AtomMomentFeasible first second third →
        (3 - Real.sqrt 5) / 6 ≤ atomMomentAverage first second third := by
  intro hclaim
  have hbound := hclaim atomUniformFirst atomUniformSecond atomUniformThird
    atomMomentFeasible_uniform
  rw [atomMomentAverage_uniform] at hbound
  have heighth := atomEighth_lt_hermitianCeiling
  norm_num at hbound
  linarith

/-- **THE UNIFORM WITNESS MISSES THE ENERGY FLOOR, AND ONLY THAT.**  Its
determinantal energy is `1/20 = 0.05`, and layer 6 shows that a real balanced
frame carries at least `3/50 = 0.06`.  So the energy floor is exactly the reading
that separates the witness from a frame. -/
theorem atomMomentEnergy_uniform :
    atomTripleFamilySum
        (fun slotOne slotTwo slotThree => atomUniformThird slotOne slotTwo slotThree ^ 2)
      = 1 / 20 := by
  simp only [atomTripleFamilySum, atomUniformThird]; norm_num

/-! ## Layer 4 — the split witness survives the energy floor

The ten triples

  `012, 013, 024, 035, 045, 125, 134, 145, 234, 235`

meet each of the six slots exactly five times, so a reading that is constant on
that class and constant on its complement obeys every slot marginal as soon as it
obeys the two global totals. -/

/-- The MARK of the slot-balanced ten-and-ten split: one on the ten triples of
the class, zero elsewhere. -/
noncomputable def atomSplitMark (slotOne slotTwo slotThree : Fin 6) : ℝ :=
  if (slotOne, slotTwo, slotThree) = ((0 : Fin 6), (1 : Fin 6), (2 : Fin 6)) then 1 else
  if (slotOne, slotTwo, slotThree) = ((0 : Fin 6), (1 : Fin 6), (3 : Fin 6)) then 1 else
  if (slotOne, slotTwo, slotThree) = ((0 : Fin 6), (2 : Fin 6), (4 : Fin 6)) then 1 else
  if (slotOne, slotTwo, slotThree) = ((0 : Fin 6), (3 : Fin 6), (5 : Fin 6)) then 1 else
  if (slotOne, slotTwo, slotThree) = ((0 : Fin 6), (4 : Fin 6), (5 : Fin 6)) then 1 else
  if (slotOne, slotTwo, slotThree) = ((1 : Fin 6), (2 : Fin 6), (5 : Fin 6)) then 1 else
  if (slotOne, slotTwo, slotThree) = ((1 : Fin 6), (3 : Fin 6), (4 : Fin 6)) then 1 else
  if (slotOne, slotTwo, slotThree) = ((1 : Fin 6), (4 : Fin 6), (5 : Fin 6)) then 1 else
  if (slotOne, slotTwo, slotThree) = ((2 : Fin 6), (3 : Fin 6), (4 : Fin 6)) then 1 else
  if (slotOne, slotTwo, slotThree) = ((2 : Fin 6), (3 : Fin 6), (5 : Fin 6)) then 1 else 0

/-- The mark reads only `0` or `1`. -/
theorem atomSplitMark_cases (slotOne slotTwo slotThree : Fin 6) :
    atomSplitMark slotOne slotTwo slotThree = 0
      ∨ atomSplitMark slotOne slotTwo slotThree = 1 := by
  unfold atomSplitMark; split_ifs <;> simp

/-- The split witness reads `3/2` at every triple. -/
noncomputable def atomSplitFirst : Fin 6 → Fin 6 → Fin 6 → ℝ := fun _ _ _ => 3 / 2

/-- The split witness reads `129/200` on the class and `111/200` off it. -/
noncomputable def atomSplitSecond : Fin 6 → Fin 6 → Fin 6 → ℝ :=
  fun slotOne slotTwo slotThree =>
    111 / 200 + atomSplitMark slotOne slotTwo slotThree * (9 / 100)

/-- The split witness reads `29/400` on the class and `11/400` off it. -/
noncomputable def atomSplitThird : Fin 6 → Fin 6 → Fin 6 → ℝ :=
  fun slotOne slotTwo slotThree =>
    11 / 400 + atomSplitMark slotOne slotTwo slotThree * (9 / 200)

/-- **THE SPLIT WITNESS IS IN THE MOMENT CLASS.**  The ten marks total ten over
the twenty triples and five over the ten triples of each slot, which is exactly
what the three global totals and the twelve marginals ask for. -/
theorem atomMomentFeasible_split :
    AtomMomentFeasible atomSplitFirst atomSplitSecond atomSplitThird := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro slotOne slotTwo slotThree
    rcases atomSplitMark_cases slotOne slotTwo slotThree with hmark | hmark <;>
      simp only [atomSplitFirst, atomSplitSecond, atomSplitThird, hmark] <;> norm_num
    · exact atomBlockSpectrum_light
    · exact atomBlockSpectrum_heavy
  all_goals
    simp only [atomTripleFamilySum, atomSlotMarginalZero, atomSlotMarginalOne,
      atomSlotMarginalTwo, atomSlotMarginalThree, atomSlotMarginalFour, atomSlotMarginalFive,
      atomSplitFirst, atomSplitSecond, atomSplitThird, atomSplitMark]
  all_goals norm_num [Fin.ext_iff]

/-- The determinantal energy of the split witness is `481 / 8000 = 0.060125`,
which PASSES the floor `3 / 50 = 0.06` of layer 6. -/
theorem atomMomentEnergy_split :
    atomTripleFamilySum
        (fun slotOne slotTwo slotThree => atomSplitThird slotOne slotTwo slotThree ^ 2)
      = 481 / 8000 := by
  simp only [atomTripleFamilySum, atomSplitThird, atomSplitMark]
  norm_num [Fin.ext_iff]

/-- The determinantal average of the split witness stays below one eighth. -/
theorem atomMomentAverage_split :
    atomMomentAverage atomSplitFirst atomSplitSecond atomSplitThird < 1 / 8 := by
  have hshape : atomMomentAverage atomSplitFirst atomSplitSecond atomSplitThird
      = 10 * wedgeAverageTerm (3 / 2) (129 / 200) (29 / 400)
        + 10 * wedgeAverageTerm (3 / 2) (111 / 200) (11 / 400) := by
    simp only [atomMomentAverage, atomTripleFamilySum, atomSplitFirst, atomSplitSecond,
      atomSplitThird, atomSplitMark]
    norm_num [Fin.ext_iff]
    ring
  rw [hshape, wedgeAverageTerm_heavy, wedgeAverageTerm_light]
  norm_num

/-- **THE MOMENT PROGRAMME IS CAPPED EVEN WITH THE ENERGY FLOOR.**  Adding the
proved floor `3 / 50 <= sum of p ^ 2` to the moment class does NOT lift the cap
past the field-agnostic ceiling.

The witness carries ten triples of spectrum with `e2 = 129/200`, `e3 = 29/400`
and ten with `e2 = 111/200`, `e3 = 11/400`, split five and five at every slot.
Its energy is `481 / 8000`, which passes `3 / 50 = 480 / 8000`, and its average is
`0.1238360`, still below `(3 - sqrt 5) / 6 = 0.1273220`.

So a certificate must consume a reading of the frame that is NOT a moment of the
twenty triples and NOT the level-three energy. -/
theorem not_atomMomentCap_withEnergy :
    ¬ ∀ first second third : Fin 6 → Fin 6 → Fin 6 → ℝ,
        AtomMomentFeasible first second third →
        3 / 50 ≤ atomTripleFamilySum
          (fun slotOne slotTwo slotThree => third slotOne slotTwo slotThree ^ 2) →
        (3 - Real.sqrt 5) / 6 ≤ atomMomentAverage first second third := by
  intro hclaim
  have hbound := hclaim atomSplitFirst atomSplitSecond atomSplitThird
    atomMomentFeasible_split (by rw [atomMomentEnergy_split]; norm_num)
  have hsplit := atomMomentAverage_split
  have heighth := atomEighth_lt_hermitianCeiling
  linarith

/-! ## Layer 5 — the frame really does carry the three global totals

`Gtz.atomBlockTrace_familySum` and `Gtz.atomBlockSecond_familySum` are landed in
`Gtz.Wave.SpectralSupplyCell`.  This layer adds the pair-minor total that the
energy floor of layer 6 consumes, and collects the three totals in one place. -/

variable {atom : Fin 6 → (Fin 3 → ℝ)}

/-- **THE FIFTEEN PAIR MINORS TOTAL THREE.**  They are the second elementary
reading of the Gram, and a rank-three projection carries `e2 = 3`.  The proof
reads the trace law and the idempotence law of the Gram, and nothing else. -/
theorem atomPairMinor_familySum
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomPairFamilySum (fun rowSlot colSlot => atomBlockPairMinor atom rowSlot colSlot) = 3 := by
  have htrace := atomGram_trace hframe
  have hpower := atomGramPowerTwo_eq hframe
  simp only [Fin.sum_univ_six] at htrace
  simp only [atomGramPowerTwo, Fin.sum_univ_six] at hpower
  simp only [atomGram_comm atom 1 0, atomGram_comm atom 2 0, atomGram_comm atom 3 0,
    atomGram_comm atom 4 0, atomGram_comm atom 5 0, atomGram_comm atom 2 1,
    atomGram_comm atom 3 1, atomGram_comm atom 4 1, atomGram_comm atom 5 1,
    atomGram_comm atom 3 2, atomGram_comm atom 4 2, atomGram_comm atom 5 2,
    atomGram_comm atom 4 3, atomGram_comm atom 5 3, atomGram_comm atom 5 4] at hpower
  have hsquare : (atomGram atom 0 0 + atomGram atom 1 1 + atomGram atom 2 2
      + atomGram atom 3 3 + atomGram atom 4 4 + atomGram atom 5 5) ^ 2 = 9 := by
    rw [htrace]; norm_num
  simp only [atomPairFamilySum, atomBlockPairMinor]
  linear_combination (1 / 2 : ℝ) * hsquare - (1 / 2 : ℝ) * hpower

/-- **THE SECOND MINOR TOTAL IS FOUR TIMES THE PAIR-MINOR TOTAL.**  Each of the
fifteen pairs lies in four of the twenty triples.  Together with
`Gtz.atomPairMinor_familySum` this is a second route to the landed
`Gtz.atomBlockSecond_familySum`, and it is the route that keeps the pair minors
visible. -/
theorem atomBlockSecond_eq_four_pairMinor (atom : Fin 6 → (Fin 3 → ℝ)) :
    atomTripleFamilySum (atomBlockSecond atom)
      = 4 * atomPairFamilySum (fun rowSlot colSlot => atomBlockPairMinor atom rowSlot colSlot) := by
  simp only [atomTripleFamilySum, atomBlockSecond_eq_pairMinor_sum, atomPairFamilySum]
  ring

/-- **THE FRAME CARRIES THE THREE GLOBAL TOTALS OF THE MOMENT CLASS.**  So the
class of layer 2 is a genuine relaxation of the frame problem, and the caps of
layers 3 and 4 apply to it. -/
theorem atomFrameMomentTotals
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomTripleFamilySum (atomBlockTrace atom) = 30
      ∧ atomTripleFamilySum (atomBlockSecond atom) = 12
      ∧ atomTripleFamilySum (atomBlockDet atom) = 1 :=
  ⟨atomBlockTrace_familySum hframe, atomBlockSecond_familySum hframe,
    atomBlockDet_familySum hframe⟩

/-! ## Layer 6 — the level-three energy floor, sharp at the icosahedron -/

/-- The fifteen pair readings, listed as one vector. -/
noncomputable def atomPairVector (value : Fin 6 → Fin 6 → ℝ) : Fin 15 → ℝ :=
  ![value 0 1, value 0 2, value 0 3, value 0 4, value 0 5,
    value 1 2, value 1 3, value 1 4, value 1 5,
    value 2 3, value 2 4, value 2 5, value 3 4, value 3 5, value 4 5]

/-- **CAUCHY-SCHWARZ OVER THE FIFTEEN PAIRS.**  The square of the total is at most
fifteen times the total of the squares. -/
theorem atomPairFamilySum_sq_le (value : Fin 6 → Fin 6 → ℝ) :
    atomPairFamilySum value ^ 2 ≤ 15 * atomPairFamilySum (fun rowSlot colSlot =>
      value rowSlot colSlot ^ 2) := by
  have hone : atomPairFamilySum value = ∑ index, atomPairVector value index := by
    simp [atomPairFamilySum, atomPairVector, Fin.sum_univ_succ]; ring
  have htwo : atomPairFamilySum (fun rowSlot colSlot => value rowSlot colSlot ^ 2)
      = ∑ index, atomPairVector value index ^ 2 := by
    simp [atomPairFamilySum, atomPairVector, Fin.sum_univ_succ]; ring
  rw [hone, htwo]
  simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 15)))
    (f := atomPairVector value)

/-- **THE LEVEL-TWO ENERGY FLOOR.**  The fifteen pair minors total three, so their
squares total at least `9 / 15 = 3 / 5`.  Equality asks for fifteen equal minors,
which is exactly the icosahedral frame. -/
theorem atomPluckerEnergyTwo_floor
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    3 / 5 ≤ atomPluckerEnergyTwo atom := by
  have hsum := atomPairMinor_familySum hframe
  have hcs := atomPairFamilySum_sq_le (fun rowSlot colSlot => atomBlockPairMinor atom rowSlot colSlot)
  rw [hsum] at hcs
  simp only [atomPluckerEnergyTwo]
  linarith

/-- **THE LEVEL-THREE ENERGY FLOOR.**  A real balanced Parseval frame of six atoms
carries

  `3 / 50 <= sum over the twenty triples of (triple determinant) ^ 2`.

Two steps close it.  Cauchy-Schwarz over the fifteen pair minors, which total
three, gives `3 / 5 <= E2`.  The real-only tenth
`Gtz.atomPluckerTenth_of_balanced` gives `E2 <= 10 * E3`.

The bound is SHARP at the icosahedral frame, whose fifteen pair minors are all
`1 / 5` and whose twenty triple determinants are `(5 +- sqrt 5) / 100`, ten of
each.  Both steps are equalities there. -/
theorem atomPluckerEnergyThree_floor
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom) :
    3 / 50 ≤ atomPluckerEnergyThree atom := by
  have hlow := atomPluckerEnergyTwo_floor hframe
  have htenth := atomPluckerTenth_of_balanced hframe hbal
  linarith

/-- **THE FLOOR IS NOT VACUOUS.**  The standing red-team frame of the campaign
reads `1 / 16 = 0.0625`, which passes the floor `3 / 50 = 0.06` with room. -/
theorem atomPluckerEnergyThree_dropWitness :
    atomPluckerEnergyThree dropWitnessAtom = 1 / 16 := by
  obtain ⟨p012, p013, p014, p015, p023, p024, p025, p034, p035, p045,
    p123, p124, p125, p134, p135, p145, p234, p235, p245, p345⟩ := dropWitnessBlockDet
  simp only [atomPluckerEnergyThree, atomTripleFamilySum, p012, p013, p014, p015, p023,
    p024, p025, p034, p035, p045, p123, p124, p125, p134, p135, p145, p234, p235, p245, p345]
  norm_num

/-- The floor holds at the red-team frame, with room. -/
theorem atomPluckerEnergyThree_floor_dropWitness :
    3 / 50 ≤ atomPluckerEnergyThree dropWitnessAtom := by
  rw [atomPluckerEnergyThree_dropWitness]; norm_num

/-! ## Layer 7 — the icosahedral reading of the reduced rung -/

/-- **THE CONJUGATE PAIR IDENTITY.**  Ten triples at `e2 = 3/5` and determinant
`high`, together with ten at the same second minor total and determinant
`1/10 - high`, average to a value that depends only on the PRODUCT of the two
determinants.  At the icosahedral product `1 / 500` the average is a rational
number, and the square root of the frame cancels.

The whole proof is one `linear_combination` against the product law. -/
theorem wedgeAverage_conjugatePair {high : ℝ} (hlow : 0 ≤ high) (hhigh : high ≤ 1 / 10)
    (hprod : high * (1 / 10 - high) = 1 / 500) :
    wedgeAverageTerm (3 / 2) (3 / 5) high
        + wedgeAverageTerm (3 / 2) (3 / 5) (1 / 10 - high)
      = 1637 / 120150 := by
  have dOne : (0 : ℝ) < (3 / 5 : ℝ) ^ 2 * ((3 / 5 : ℝ) ^ 2 - (3 / 2) * high) := by nlinarith
  have dTwo : (0 : ℝ) < (3 / 5 : ℝ) ^ 2 * ((3 / 5 : ℝ) ^ 2 - (3 / 2) * (1 / 10 - high)) := by
    nlinarith
  rw [wedgeAverageTerm_eq, wedgeAverageTerm_eq, div_add_div _ _ (ne_of_gt dOne) (ne_of_gt dTwo),
    div_eq_iff (ne_of_gt (mul_pos dOne dTwo))]
  linear_combination
    (1053 / 2500 * high ^ 2 - 1053 / 25000 * high - 1856277 / 27812500) * hprod

/-- **THE ICOSAHEDRAL AVERAGE OF THE REDUCED RUNG.**  At the icosahedral frame
every triple carries `e1 = 3/2` and `e2 = 3/5`, and the twenty determinants split
ten and ten at `(5 +- sqrt 5) / 100`.  The determinantal average of the reduced
second rung is then EXACTLY

  `1637 / 12015 = 0.1362463587`,

and it is rational, because the two conjugate readings cancel the square root. -/
theorem wedgeAverage_icosahedral :
    10 * wedgeAverageTerm (3 / 2) (3 / 5) ((5 + Real.sqrt 5) / 100)
        + 10 * wedgeAverageTerm (3 / 2) (3 / 5) ((5 - Real.sqrt 5) / 100)
      = 1637 / 12015 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hlt : Real.sqrt 5 < 3 := by nlinarith [hsq, hnn]
  have hpair := wedgeAverage_conjugatePair (high := (5 + Real.sqrt 5) / 100)
    (by linarith) (by linarith) (by linear_combination (-1 / 10000 : ℝ) * hsq)
  have hconj : (1 : ℝ) / 10 - (5 + Real.sqrt 5) / 100 = (5 - Real.sqrt 5) / 100 := by ring
  rw [hconj] at hpair
  linarith

/-- **THE ICOSAHEDRAL AVERAGE OF THE FIRST RUNG.**  The same frame averages the
LANDED wedge step `e3 / e2` to exactly `1 / 10`, which is the adversarial minimum
of that average.  So the icosahedron IS the extremal of the first rung. -/
theorem pluckerAverage_icosahedral :
    10 * (((5 + Real.sqrt 5) / 100) ^ 2 / (3 / 5))
        + 10 * (((5 - Real.sqrt 5) / 100) ^ 2 / (3 / 5))
      = 1 / 10 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 300 : ℝ) * hsq

/-- **THE EXTREMAL MOVES ALONG THE LADDER.**  The four readings of the reduced
second rung, in order:

  `(3 - sqrt 5) / 6 = 0.1273220` — the field-agnostic ceiling,
  `125317 / 923400 = 0.1357126` — the CUBOCTAHEDRON,
  `1637 / 12015    = 0.1362464` — the ICOSAHEDRON,
  `1 / 6           = 0.1666667` — the truth over the real field.

The cuboctahedron reads STRICTLY LESS than the icosahedron, so the icosahedron is
not the extremal of the reduced rung.  But the icosahedron IS the extremal of the
first rung, where it reads exactly `1 / 10`
(`Gtz.pluckerAverage_icosahedral`).  The binding frame therefore MOVES when the
ladder is climbed, and a proof strategy that pins one frame for the whole ladder
cannot be correct. -/
theorem wedgeAverage_icosahedral_ladder :
    (3 - Real.sqrt 5) / 6 < (125317 : ℝ) / 923400
      ∧ (125317 : ℝ) / 923400 < 1637 / 12015
      ∧ (1637 : ℝ) / 12015 < 1 / 6 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hgt : (2 : ℝ) < Real.sqrt 5 := by nlinarith [hsq, hnn]
  exact ⟨by nlinarith [hsq, hnn, hgt], by norm_num, by norm_num⟩

/-- **THE FIRST RUNG IS BELOW THE CEILING AND THE SECOND IS ABOVE IT.**  The whole
gain of the successor target is the one step from `e3 / e2` to the reduced second
rung, and both readings are at the SAME frame in
`Gtz.wedgeRung_dropWitness_ladder`.  Here they are at the ICOSAHEDRON, where the
first rung is sharp. -/
theorem wedgeAverage_icosahedral_gain :
    (1 : ℝ) / 10 < (3 - Real.sqrt 5) / 6 ∧ (3 - Real.sqrt 5) / 6 < 1637 / 12015 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hgt : (2 : ℝ) < Real.sqrt 5 := by nlinarith [hsq, hnn]
  constructor <;> nlinarith [hsq, hnn, hgt]

/-! ## Layer 8 — how much the reduced rung can gain over the landed wedge step

The landed wedge step reads `e3 / e2`.  The reduced second rung never reads less,
and it never reads more than three halves of it.  Both bounds are one algebraic
step, and the second one CAPS the whole route: the determinantal average of the
reduced rung is at most three halves of the determinantal average of the wedge
step, whose adversarial value is exactly `1 / 10`. -/

/-- **THE GAIN IS NOT NEGATIVE.**  The reduced second rung never reads less than
the landed wedge step.  The gap is

  `e3 ^ 2 * (e1 * e2 - e3) / (e2 ^ 2 * (e2 ^ 2 - e1 * e3))`,

and `Gtz.atomBlockDet_mul_le_atomBlockSecond_mul` is the step the rung improves.
The hypothesis `3 * e3 <= e1 * e2` is the same Newton reading that
`Gtz.wedgeRungTwoLower_le` already spends. -/
theorem wedgeRungTwoLower_ge_wedge {first second third : ℝ}
    (hsecond : 0 < second) (hthird : 0 ≤ third)
    (hmean : 3 * third ≤ first * second)
    (hden : 0 < second ^ 2 - first * third) :
    third / second ≤ wedgeRungTwoLower first second third := by
  have hs2 : (0 : ℝ) < second ^ 2 := by positivity
  have hlowDen : (0 : ℝ) < second ^ 2 * (second ^ 2 - first * third) := by positivity
  rw [wedgeRungTwoLower, div_le_div_iff₀ hsecond hlowDen]
  have hgap : 0 ≤ third ^ 2 * (first * second - third) := by
    have : 0 ≤ first * second - third := by linarith
    positivity
  nlinarith [hgap, hthird, hsecond, hs2]

/-- **THE GAIN IS AT MOST ONE HALF.**  The reduced second rung never reads more
than three halves of the landed wedge step.  The gap is

  `(e3 / 2) * (e2 ^ 3 - 3 * e1 * e2 * e3 + 2 * e3 ^ 2)
     / (e2 ^ 2 * (e2 ^ 2 - e1 * e3))`,

and the bracket is not negative because Newton gives `3 * e1 * e3 <= e2 ^ 2`, so
`3 * e1 * e2 * e3 <= e2 ^ 3`.  The bound is attained when the three eigenvalues
of the block agree, where the rung reads `13 / 9` of the wedge step and the
factor `3 / 2` is the limit of the family. -/
theorem wedgeRungTwoLower_le_three_halves {first second third : ℝ}
    (hsecond : 0 < second) (hthird : 0 ≤ third)
    (hnewton : 3 * (first * third) ≤ second ^ 2)
    (hden : 0 < second ^ 2 - first * third) :
    wedgeRungTwoLower first second third ≤ 3 / 2 * (third / second) := by
  have hs2 : (0 : ℝ) < second ^ 2 := by positivity
  have hlowDen : (0 : ℝ) < second ^ 2 * (second ^ 2 - first * third) := by positivity
  have hcube : 3 * (first * second * third) ≤ second ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hnewton (le_of_lt hsecond)]
  have hbracket : (0 : ℝ)
      ≤ 1 / 2 * (second ^ 3 - 3 * (first * second * third)) + third ^ 2 := by
    nlinarith [hcube, sq_nonneg third]
  rw [wedgeRungTwoLower, mul_div_assoc', div_le_div_iff₀ hlowDen hsecond]
  nlinarith [mul_nonneg (mul_nonneg hthird (le_of_lt hsecond)) hbracket]

/-- **THE SANDWICH.**  Under the two Newton readings the reduced second rung sits
between the landed wedge step and three halves of it. -/
theorem wedgeRungTwoLower_sandwich {first second third : ℝ}
    (hsecond : 0 < second) (hthird : 0 ≤ third)
    (hmean : 3 * third ≤ first * second)
    (hnewton : 3 * (first * third) ≤ second ^ 2)
    (hden : 0 < second ^ 2 - first * third) :
    third / second ≤ wedgeRungTwoLower first second third
      ∧ wedgeRungTwoLower first second third ≤ 3 / 2 * (third / second) :=
  ⟨wedgeRungTwoLower_ge_wedge hsecond hthird hmean hden,
    wedgeRungTwoLower_le_three_halves hsecond hthird hnewton hden⟩

/-- The sandwich at the four WINNING triples of the cuboctahedron.  The wedge step
reads `1 / 9`, the rung reads `713 / 4617`, and three halves of the wedge step is
`1 / 6`.  The gain is thirty-nine percent of the fifty percent that is available. -/
theorem wedgeRungTwoLower_sandwich_cuboctahedron_win :
    (1 : ℝ) / 16 / (9 / 16) ≤ wedgeRungTwoLower (3 / 2) (9 / 16) (1 / 16)
      ∧ wedgeRungTwoLower (3 / 2) (9 / 16) (1 / 16) ≤ 3 / 2 * ((1 : ℝ) / 16 / (9 / 16)) := by
  rw [wedgeRungTwoLower_cuboctahedron_win]; constructor <;> norm_num

/-- The sandwich at the twelve NEAR-MISSING triples of the cuboctahedron.  The
wedge step reads `1 / 10` and the rung reads `123 / 950`. -/
theorem wedgeRungTwoLower_sandwich_cuboctahedron_near :
    (1 : ℝ) / 16 / (5 / 8) ≤ wedgeRungTwoLower (3 / 2) (5 / 8) (1 / 16)
      ∧ wedgeRungTwoLower (3 / 2) (5 / 8) (1 / 16) ≤ 3 / 2 * ((1 : ℝ) / 16 / (5 / 8)) := by
  rw [wedgeRungTwoLower_cuboctahedron_near]; constructor <;> norm_num

/-- **THE ROUTE HAS A CEILING OF ITS OWN.**  The determinantal average of the
reduced rung is at most three halves of the determinantal average of the landed
wedge step, term by term.  The wedge average has the adversarial value `1 / 10`,
attained at the icosahedron (`Gtz.pluckerAverage_icosahedral`), so this route can
never certify more than `3 / 20 = 0.15`.

The target `(3 - sqrt 5) / 6 = 0.1273220` is inside that window, and the measured
adversarial value of the reduced average is `125317 / 923400 = 0.1357126`.  So
the window is `0.1273220 < 0.1357126 < 0.15`, and it is narrow. -/
theorem wedgeAverage_route_window :
    (3 - Real.sqrt 5) / 6 < (125317 : ℝ) / 923400
      ∧ (125317 : ℝ) / 923400 < 3 / 20
      ∧ (3 : ℝ) / 20 = 3 / 2 * (1 / 10) := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hgt : (2 : ℝ) < Real.sqrt 5 := by nlinarith [hsq, hnn]
  exact ⟨by nlinarith [hsq, hnn, hgt], by norm_num, by norm_num⟩

end Gtz
