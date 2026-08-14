import Gtz.Wave.DeterminantalAverageCap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The spread law is not the missing ingredient

The campaign selects a triple of the six slots with the DETERMINANTAL MEASURE.
The twenty triple determinants total one, so the largest per-triple floor is at
least the determinantal average of the floors, and a certificate wants that
average above the field-agnostic ceiling `(3 - sqrt 5) / 6 = 0.127322003750`.

`Gtz.not_atomMomentCap` closed the programme that reads only the three global
totals, the twelve slot marginals and the per-triple spectral box.  The witness
that closed it carries TWENTY EQUAL determinants, and
`Gtz.not_uniform_dppTripleWeight` says no real frame does that.  So the natural
next move is to add the real-only spread law and ask whether the cap lifts.

**IT DOES NOT.**  This module proves it, and in the strongest shape available:
not for one chosen floor, but for EVERY per-triple floor at once.

## The class

`Gtz.AtomSpreadFeasible` is the moment class, tightened four ways.

* The second reading is TIED to the determinants by the landed pair-minor law
  `Gtz.atomBlockPairMinor_eq_blockDet_sum`: the pair minor of two slots is the
  total of the four triple determinants through that pair.  So the second
  reading is a linear function of the twenty determinants and is no longer free.
  The split witness of `Gtz.not_atomMomentCap_withEnergy` DIES here.  All fifteen
  of its pair minors read `1/5`, which forces the second reading `3/5` at every
  triple, and `(3/2, 3/5, 29/400)` is not a real spectrum.
* Every slot carries the doubled marginal `1`, which is `Gtz.dppTripleMarginal_eq`
  at a balanced frame.
* Every triple of DISTINCT slots reads a block spectrum in the unit box.
* The determinants obey the doubled spread law `Gtz.dppPlucker_spread_double`:
  through one pivot and four slots, `2 * (the smallest) <= (the largest)`.

`Gtz.atomSpreadFeasible_blockDet` proves that every balanced real Parseval frame
is a member, with the spectral box as the one standing hypothesis.

## The sharp objective

A per-triple floor is any reading that is at most every eigenvalue of the block.
`Gtz.AtomTripleEigenFloor` says that, and `Gtz.atomEigenFloor_le_bar` turns one
sign change of the characteristic polynomial into an upper bound for it.  Capping
the determinantal average of an ARBITRARY member of that family caps every
certificate of this shape at once, so no comparison of candidate rungs is needed.

## The witness, and it is exact

Read the label `slot y -> y + 1` in binary.  Slot `0` reads `001` and slot `5`
reads `110`, and no slot reads `000` or `111`.  Each binary digit cuts the six
slots into two triples, and the three cuts together SEPARATE EVERY PAIR of
slots, because no two slots share all three digits.  The six triples on those
three cuts,

  `{0,1,2}` `{3,4,5}`,  `{0,3,4}` `{1,2,5}`,  `{1,3,5}` `{0,2,4}`,

carry the weight `1/34`, and the other fourteen carry `2/34`.

Separation is the whole reason the spread law survives.  The six determinants
through a pivot and four slots are the six cuts that separate the pivot from the
omitted slot, so at least one light cut is among them, and the heavy value is
exactly twice the light one.  The spread law therefore holds with EQUALITY at all
thirty pivot families (`Gtz.atomSpreadFeasible_witness`).

`Gtz.atomSpreadWitness_floorCap` reads the cap: EVERY per-triple floor averages
to at most `2107 / 17000 = 0.123941176471`, below `(3 - sqrt 5) / 6`.  The true
reading of the witness is `0.123237642703`, and the bound spends `63/1000` and
`137/1000` for the two smallest eigenvalues `0.062762683902` and
`0.136196562446`.

## What the witness fails, and that is the point

`Gtz.atomSpreadWitness_energyFails` reads `E3 = 31/578 = 0.053633`, below the
landed floor `3/50 = 0.06`.  `Gtz.atomSpreadWitness_tenthFails` reads
`E2 = 351/578 = 0.607266` against `10 * E3 = 310/578 = 0.536332`, so the tenth
fails too.  **The spread law is not the missing ingredient.  The level-three
energy floor is.**

## The measured ladder, for the successor

The determinantal average of the SMALLEST EIGENVALUE, minimised over the exact
class of this module, was measured.  With no real-only law it reads
`(5 - sqrt 15) / 10 = 0.112701665379`, attained at the flat point, and the solver
reproduces that constant to fifteen digits.  Adding the spread law moves it to
`0.1204`.  Adding the level-three energy floor INSTEAD moves it to `0.1399`, and
adding the tenth as well moves it to `0.1465`, both past the ceiling.  Those
three are search minima and are NOT theorems.  The refutation here is a theorem,
because a feasible point below a bar is a proof and a search minimum above a bar
is not.
-/

namespace Gtz

/-! ## Layer 0 — the block determinant IS the Plücker weight -/

/-- **THE BRIDGE.**  The determinant of the Gram block of a triple and the
determinantal weight of the interlacing module are the same polynomial in the
Gram entries.  One `ring` closes it, and it lets the landed spread law speak
about `Gtz.atomBlockDet`. -/
theorem atomBlockDet_eq_dppTripleWeight (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    atomBlockDet atom slotOne slotTwo slotThree
      = dppTripleWeight atom slotOne slotTwo slotThree := by
  simp only [atomBlockDet, dppTripleWeight]
  ring

/-- The block determinant does not read the order of the first two slots. -/
theorem atomBlockDet_swap_left (atom : Fin 6 → (Fin 3 → ℝ)) (a b c : Fin 6) :
    atomBlockDet atom a b c = atomBlockDet atom b a c := by
  simp only [atomBlockDet, atomGram_comm atom b a]
  ring

/-- The block determinant does not read the order of the last two slots. -/
theorem atomBlockDet_swap_right (atom : Fin 6 → (Fin 3 → ℝ)) (a b c : Fin 6) :
    atomBlockDet atom a b c = atomBlockDet atom a c b := by
  simp only [atomBlockDet, atomGram_comm atom c b]
  ring

theorem atomBlockDet_self_left (atom : Fin 6 → (Fin 3 → ℝ)) (a b : Fin 6) :
    atomBlockDet atom a a b = 0 := by
  simp only [atomBlockDet]
  ring

/-! ## Layer 1 — the spread law, as a property of a weight table -/

/-- **THE SPREAD LAW AS A CLASS CONDITION.**  Fix a pivot slot and four other
slots.  Whatever bars bracket the six weights through that pivot, twice the lower
bar is at most the upper bar.  With the bars taken to be the smallest and the
largest of the six, this says `2 * min <= max`.

This is verbatim the conclusion of the landed `Gtz.dppPlucker_spread_double`, so
`Gtz.atomWeightSpread_blockDet` is a two line proof and the class below is a
genuine relaxation of the real frame problem. -/
def AtomWeightSpread (weight : Fin 6 → Fin 6 → Fin 6 → ℝ) : Prop :=
  ∀ pivot slotOne slotTwo slotThree slotFour : Fin 6, ∀ low high : ℝ, 0 ≤ low →
    low ≤ weight pivot slotOne slotTwo → low ≤ weight pivot slotOne slotThree →
    low ≤ weight pivot slotOne slotFour → low ≤ weight pivot slotTwo slotThree →
    low ≤ weight pivot slotTwo slotFour → low ≤ weight pivot slotThree slotFour →
    weight pivot slotOne slotTwo ≤ high → weight pivot slotOne slotThree ≤ high →
    weight pivot slotOne slotFour ≤ high → weight pivot slotTwo slotThree ≤ high →
    weight pivot slotTwo slotFour ≤ high → weight pivot slotThree slotFour ≤ high →
    2 * low ≤ high

/-- **EVERY REAL FRAME OBEYS THE SPREAD LAW.**  Straight from the landed doubled
spread law through the bridge of layer 0. -/
theorem atomWeightSpread_blockDet (atom : Fin 6 → (Fin 3 → ℝ)) :
    AtomWeightSpread (atomBlockDet atom) := by
  intro pivot slotOne slotTwo slotThree slotFour low high hlow
    h12 h13 h14 h23 h24 h34 g12 g13 g14 g23 g24 g34
  simp only [atomBlockDet_eq_dppTripleWeight] at h12 h13 h14 h23 h24 h34 g12 g13 g14 g23 g24 g34
  exact dppPlucker_spread_double atom pivot slotOne slotTwo slotThree slotFour low high hlow
    h12 h13 h14 h23 h24 h34 g12 g13 g14 g23 g24 g34

/-! ## Layer 2 — the tightened moment class -/

/-- **THE SPREAD MOMENT CLASS.**  Everything a certificate may read about a
balanced real Parseval frame of six atoms, once the second reading is tied to the
determinants. -/
def AtomSpreadFeasible (weight second : Fin 6 → Fin 6 → Fin 6 → ℝ) : Prop :=
  (∀ a b c : Fin 6, 0 ≤ weight a b c)
    ∧ (∀ a b c : Fin 6, weight a b c = weight b a c)
    ∧ (∀ a b c : Fin 6, weight a b c = weight a c b)
    ∧ (∀ a b : Fin 6, weight a a b = 0)
    ∧ (∀ a b c : Fin 6, second a b c
        = (∑ v, weight a b v) + (∑ v, weight a c v) + (∑ v, weight b c v))
    ∧ (∀ a : Fin 6, (∑ b, ∑ c, weight a b c) = 1)
    ∧ atomTripleFamilySum weight = 1
    ∧ (∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
        AtomBlockSpectrum (3 / 2) (second a b c) (weight a b c))
    ∧ AtomWeightSpread weight

/-- **THE CLASS IS A GENUINE RELAXATION.**  Every balanced real Parseval frame of
six atoms delivers a member, with the spectral box as the one standing
hypothesis.  The box is the statement that the Gram block of three slots of a
Parseval frame is a principal block of an orthogonal projection, so its three
eigenvalues lie in `[0,1]`. -/
theorem atomSpreadFeasible_blockDet {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : AtomBalanced atom)
    (hbox : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
      AtomBlockSpectrum (3 / 2) (atomBlockSecond atom a b c) (atomBlockDet atom a b c)) :
    AtomSpreadFeasible (atomBlockDet atom) (atomBlockSecond atom) := by
  refine ⟨atomBlockDet_nonneg atom, atomBlockDet_swap_left atom, atomBlockDet_swap_right atom,
    atomBlockDet_self_left atom, ?_, ?_, atomBlockDet_familySum hframe, hbox,
    atomWeightSpread_blockDet atom⟩
  · intro a b c
    rw [atomBlockSecond_eq_pairMinor_sum, ← atomBlockPairMinor_eq_blockDet_sum hframe a b,
      ← atomBlockPairMinor_eq_blockDet_sum hframe a c,
      ← atomBlockPairMinor_eq_blockDet_sum hframe b c]
  · intro a
    have hmarg := dppTripleMarginal_eq hframe a
    simp only [← atomBlockDet_eq_dppTripleWeight] at hmarg
    rw [hmarg, hbal a]
    norm_num

/-! ## Layer 3 — a per-triple floor, and how to cap it -/

/-- **A PER-TRIPLE FLOOR.**  A reading that is at most EVERY eigenvalue of the
block of every triple.  The characteristic polynomial of the block of a balanced
frame is `x ^ 3 - (3/2) * x ^ 2 + second * x - weight`, so this says exactly
`floor <= lambda_min`.

Every floor the campaign owns is of this shape: `Gtz.wedgeRungTwoLower`, the
wedge step `e3 / e2`, the full second rung of `Gtz.atomBlendFloor_shift`, and the
smallest eigenvalue itself.  Capping this family caps all of them at once. -/
def AtomTripleEigenFloor (weight second floorReading : Fin 6 → Fin 6 → Fin 6 → ℝ) : Prop :=
  ∀ a b c : Fin 6, ∀ root : ℝ,
    root ^ 3 - (3 / 2) * root ^ 2 + second a b c * root - weight a b c = 0 →
    floorReading a b c ≤ root

/-- **ONE SIGN CHANGE CAPS THE FLOOR.**  If the characteristic polynomial is not
negative at a bar, it has a root at or below that bar, so every per-triple floor
is at or below the bar.  The polynomial is negative at zero because the
determinant is not negative, and the intermediate value theorem does the rest.
No eigenvalue is ever computed. -/
theorem atomEigenFloor_le_bar {weight second floorReading : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hfloor : AtomTripleEigenFloor weight second floorReading)
    (a b c : Fin 6) {bar : ℝ} (hbar : 0 ≤ bar) (hweight : 0 ≤ weight a b c)
    (hsign : 0 ≤ bar ^ 3 - (3 / 2) * bar ^ 2 + second a b c * bar - weight a b c) :
    floorReading a b c ≤ bar := by
  have hcont : ContinuousOn
      (fun x : ℝ => x ^ 3 - (3 / 2) * x ^ 2 + second a b c * x - weight a b c)
      (Set.Icc 0 bar) := by fun_prop
  have hmem : (0 : ℝ) ∈ Set.Icc
      ((fun x : ℝ => x ^ 3 - (3 / 2) * x ^ 2 + second a b c * x - weight a b c) 0)
      ((fun x : ℝ => x ^ 3 - (3 / 2) * x ^ 2 + second a b c * x - weight a b c) bar) := by
    constructor <;> simp <;> linarith
  obtain ⟨root, hroot, hval⟩ := intermediate_value_Icc hbar hcont hmem
  exact le_trans (hfloor a b c root hval) hroot.2

/-! ## Layer 4 — the witness -/

/-- The binary label of a slot, as a bit. -/
def atomSpreadBit : Fin 6 → ℕ := ![1, 2, 4, 8, 16, 32]

/-- The set of three slots, as one number. -/
def atomSpreadMask (a b c : Fin 6) : ℕ := atomSpreadBit a + atomSpreadBit b + atomSpreadBit c

/-- The witness weight, in units of `1/34`.  Zero on a repeated slot, one on the
six light triples, two elsewhere.  The six light triples are the two sides of each
of the three coordinate cuts of the labelling `slot y -> y + 1` read in binary:

  `{0,1,2}` and `{3,4,5}`, `{0,3,4}` and `{1,2,5}`, `{1,3,5}` and `{0,2,4}`. -/
def atomSpreadNum (a b c : Fin 6) : ℕ :=
  if a = b ∨ a = c ∨ b = c then 0
  else if atomSpreadMask a b c = 7 ∨ atomSpreadMask a b c = 21 ∨ atomSpreadMask a b c = 25
      ∨ atomSpreadMask a b c = 38 ∨ atomSpreadMask a b c = 42 ∨ atomSpreadMask a b c = 56
    then 1 else 2

/-- The witness weight. -/
noncomputable def atomSpreadWeight (a b c : Fin 6) : ℝ := (atomSpreadNum a b c : ℝ) / 34

/-- The witness second reading, defined AS the pair-minor law asks, so that the
class condition holds by definition at every index triple, repeated slots
included. -/
noncomputable def atomSpreadSecond (a b c : Fin 6) : ℝ :=
  (∑ v, atomSpreadWeight a b v) + (∑ v, atomSpreadWeight a c v) + (∑ v, atomSpreadWeight b c v)

theorem atomSpreadNum_le_two (a b c : Fin 6) : atomSpreadNum a b c ≤ 2 := by
  unfold atomSpreadNum; split_ifs <;> omega

theorem atomSpreadWeight_nonneg (a b c : Fin 6) : 0 ≤ atomSpreadWeight a b c := by
  unfold atomSpreadWeight; positivity

theorem atomSpreadWeight_of_num_zero {a b c : Fin 6} (h : atomSpreadNum a b c = 0) :
    atomSpreadWeight a b c = 0 := by simp [atomSpreadWeight, h]

theorem atomSpreadWeight_of_num_one {a b c : Fin 6} (h : atomSpreadNum a b c = 1) :
    atomSpreadWeight a b c = 1 / 34 := by simp [atomSpreadWeight, h]

theorem atomSpreadWeight_of_num_two {a b c : Fin 6} (h : atomSpreadNum a b c = 2) :
    atomSpreadWeight a b c = 1 / 17 := by
  simp only [atomSpreadWeight, h]; norm_num

/-! ### The finite facts, each a kernel computation on the labels -/

/-- The witness table is symmetric in the first two slots. -/
theorem atomSpreadNum_swap_left (a b c : Fin 6) : atomSpreadNum a b c = atomSpreadNum b a c := by
  revert a b c; decide

/-- The witness table is symmetric in the last two slots. -/
theorem atomSpreadNum_swap_right (a b c : Fin 6) : atomSpreadNum a b c = atomSpreadNum a c b := by
  revert a b c; decide

/-- The witness table vanishes on a repeated slot. -/
theorem atomSpreadNum_self_left (a b : Fin 6) : atomSpreadNum a a b = 0 := by
  revert a b; decide

/-- **THE PAIR-MINOR TOTAL AT A LIGHT TRIPLE.**  The three pair minors of a light
triple total `19/34`. -/
theorem atomSpreadNum_pairSum_one (a b c : Fin 6) (h : atomSpreadNum a b c = 1) :
    (∑ v, atomSpreadNum a b v) + (∑ v, atomSpreadNum a c v)
      + (∑ v, atomSpreadNum b c v) = 19 := by
  revert h; revert a b c; decide

/-- **THE PAIR-MINOR TOTAL AT A HEAVY TRIPLE.**  The three pair minors of a heavy
triple total `21/34`. -/
theorem atomSpreadNum_pairSum_two (a b c : Fin 6) (h : atomSpreadNum a b c = 2) :
    (∑ v, atomSpreadNum a b v) + (∑ v, atomSpreadNum a c v)
      + (∑ v, atomSpreadNum b c v) = 21 := by
  revert h; revert a b c; decide

/-- **EVERY SLOT CARRIES THE DOUBLED MARGINAL `34`.**  In real units this is the
marginal `1`, which is `Gtz.dppTripleMarginal_eq` at a balanced frame. -/
theorem atomSpreadNum_marginal (a : Fin 6) : (∑ b, ∑ c, atomSpreadNum a b c) = 34 := by
  revert a; decide

/-- **THE SPREAD PATTERN.**  Through any pivot and any four slots, EITHER one of
the six weights sits on a repeated slot and is zero, OR a light weight and a heavy
weight both occur.  The second case is the reason the three light cuts had to
separate every pair of slots. -/
theorem atomSpreadNum_core (pivot s1 s2 s3 s4 : Fin 6) :
    (atomSpreadNum pivot s1 s2 = 0 ∨ atomSpreadNum pivot s1 s3 = 0
        ∨ atomSpreadNum pivot s1 s4 = 0 ∨ atomSpreadNum pivot s2 s3 = 0
        ∨ atomSpreadNum pivot s2 s4 = 0 ∨ atomSpreadNum pivot s3 s4 = 0)
      ∨ ((atomSpreadNum pivot s1 s2 = 1 ∨ atomSpreadNum pivot s1 s3 = 1
            ∨ atomSpreadNum pivot s1 s4 = 1 ∨ atomSpreadNum pivot s2 s3 = 1
            ∨ atomSpreadNum pivot s2 s4 = 1 ∨ atomSpreadNum pivot s3 s4 = 1)
          ∧ (atomSpreadNum pivot s1 s2 = 2 ∨ atomSpreadNum pivot s1 s3 = 2
            ∨ atomSpreadNum pivot s1 s4 = 2 ∨ atomSpreadNum pivot s2 s3 = 2
            ∨ atomSpreadNum pivot s2 s4 = 2 ∨ atomSpreadNum pivot s3 s4 = 2)) := by
  revert pivot s1 s2 s3 s4; decide

/-- The twenty sorted triples: six light readings and fourteen heavy ones. -/
theorem atomSpreadNum_sorted :
    atomSpreadNum 0 1 2 = 1 ∧ atomSpreadNum 0 1 3 = 2 ∧ atomSpreadNum 0 1 4 = 2
      ∧ atomSpreadNum 0 1 5 = 2 ∧ atomSpreadNum 0 2 3 = 2 ∧ atomSpreadNum 0 2 4 = 1
      ∧ atomSpreadNum 0 2 5 = 2 ∧ atomSpreadNum 0 3 4 = 1 ∧ atomSpreadNum 0 3 5 = 2
      ∧ atomSpreadNum 0 4 5 = 2 ∧ atomSpreadNum 1 2 3 = 2 ∧ atomSpreadNum 1 2 4 = 2
      ∧ atomSpreadNum 1 2 5 = 1 ∧ atomSpreadNum 1 3 4 = 2 ∧ atomSpreadNum 1 3 5 = 1
      ∧ atomSpreadNum 1 4 5 = 2 ∧ atomSpreadNum 2 3 4 = 2 ∧ atomSpreadNum 2 3 5 = 2
      ∧ atomSpreadNum 2 4 5 = 2 ∧ atomSpreadNum 3 4 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### The witness is in the class -/

theorem atomSpreadWeight_sum (a b : Fin 6) :
    (∑ v, atomSpreadWeight a b v) = ((∑ v, atomSpreadNum a b v : ℕ) : ℝ) / 34 := by
  simp only [atomSpreadWeight, ← Finset.sum_div]
  push_cast
  ring

theorem atomSpreadSecond_of_num_one {a b c : Fin 6} (h : atomSpreadNum a b c = 1) :
    atomSpreadSecond a b c = 19 / 34 := by
  have hp := atomSpreadNum_pairSum_one a b c h
  simp only [atomSpreadSecond, atomSpreadWeight_sum, ← add_div]
  rw [show ((∑ v, atomSpreadNum a b v : ℕ) : ℝ) + ((∑ v, atomSpreadNum a c v : ℕ) : ℝ)
      + ((∑ v, atomSpreadNum b c v : ℕ) : ℝ)
    = (((∑ v, atomSpreadNum a b v) + (∑ v, atomSpreadNum a c v)
        + (∑ v, atomSpreadNum b c v) : ℕ) : ℝ) from by push_cast; ring, hp]
  norm_num

theorem atomSpreadSecond_of_num_two {a b c : Fin 6} (h : atomSpreadNum a b c = 2) :
    atomSpreadSecond a b c = 21 / 34 := by
  have hp := atomSpreadNum_pairSum_two a b c h
  simp only [atomSpreadSecond, atomSpreadWeight_sum, ← add_div]
  rw [show ((∑ v, atomSpreadNum a b v : ℕ) : ℝ) + ((∑ v, atomSpreadNum a c v : ℕ) : ℝ)
      + ((∑ v, atomSpreadNum b c v : ℕ) : ℝ)
    = (((∑ v, atomSpreadNum a b v) + (∑ v, atomSpreadNum a c v)
        + (∑ v, atomSpreadNum b c v) : ℕ) : ℝ) from by push_cast; ring, hp]
  norm_num

theorem atomSpreadNum_ne_zero {a b c : Fin 6} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    atomSpreadNum a b c ≠ 0 := by
  unfold atomSpreadNum
  rw [if_neg (by tauto)]
  split_ifs <;> omega

theorem atomSpreadWeight_familySum : atomTripleFamilySum atomSpreadWeight = 1 := by
  obtain ⟨n012, n013, n014, n015, n023, n024, n025, n034, n035, n045,
    n123, n124, n125, n134, n135, n145, n234, n235, n245, n345⟩ := atomSpreadNum_sorted
  simp only [atomTripleFamilySum, atomSpreadWeight, n012, n013, n014, n015, n023, n024, n025,
    n034, n035, n045, n123, n124, n125, n134, n135, n145, n234, n235, n245, n345]
  norm_num

/-- **THE WITNESS IS A MEMBER OF THE SPREAD MOMENT CLASS.** -/
theorem atomSpreadFeasible_witness : AtomSpreadFeasible atomSpreadWeight atomSpreadSecond := by
  refine ⟨atomSpreadWeight_nonneg, ?_, ?_, ?_, fun a b c => rfl, ?_,
    atomSpreadWeight_familySum, ?_, ?_⟩
  · intro a b c; simp only [atomSpreadWeight, atomSpreadNum_swap_left a b c]
  · intro a b c; simp only [atomSpreadWeight, atomSpreadNum_swap_right a b c]
  · intro a b; simp [atomSpreadWeight, atomSpreadNum_self_left a b]
  · intro a
    simp only [atomSpreadWeight, ← Finset.sum_div]
    rw [show (∑ b, ∑ c, ((atomSpreadNum a b c : ℝ))) = ((∑ b, ∑ c, atomSpreadNum a b c : ℕ) : ℝ)
      from by push_cast; ring, atomSpreadNum_marginal a]
    norm_num
  · intro a b c hab hac hbc
    have hzero := atomSpreadNum_ne_zero hab hac hbc
    have hcase : atomSpreadNum a b c = 1 ∨ atomSpreadNum a b c = 2 := by
      have := atomSpreadNum_le_two a b c; omega
    rcases hcase with hone | htwo
    · rw [atomSpreadWeight_of_num_one hone, atomSpreadSecond_of_num_one hone]
      exact atomBlockSpectrum_half (product := 1 / 17) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · rw [atomSpreadWeight_of_num_two htwo, atomSpreadSecond_of_num_two htwo]
      exact atomBlockSpectrum_half (product := 2 / 17) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
  · intro pivot s1 s2 s3 s4 low high hlow h12 h13 h14 h23 h24 h34 g12 g13 g14 g23 g24 g34
    have hhigh : 0 ≤ high := le_trans hlow (le_trans h12 g12)
    rcases atomSpreadNum_core pivot s1 s2 s3 s4 with hz | ⟨hone, htwo⟩
    · rcases hz with h | h | h | h | h | h <;> linarith [atomSpreadWeight_of_num_zero h]
    · rcases hone with h | h | h | h | h | h <;> rcases htwo with k | k | k | k | k | k <;>
        linarith [atomSpreadWeight_of_num_one h, atomSpreadWeight_of_num_two k]

/-! ## Layer 5 — the cap, for every per-triple floor at once -/

/-- The characteristic polynomial of a LIGHT triple is not negative at `63/1000`,
so the smallest eigenvalue of a light block is at most `63/1000`.  The true
reading is `0.062762683902`. -/
theorem atomSpreadSign_light :
    (0 : ℝ) ≤ (63 / 1000) ^ 3 - (3 / 2) * (63 / 1000) ^ 2 + (19 / 34) * (63 / 1000) - 1 / 34 := by
  norm_num

/-- The characteristic polynomial of a HEAVY triple is not negative at `137/1000`,
so the smallest eigenvalue of a heavy block is at most `137/1000`.  The true
reading is `0.136196562446`. -/
theorem atomSpreadSign_heavy :
    (0 : ℝ) ≤ (137 / 1000) ^ 3 - (3 / 2) * (137 / 1000) ^ 2 + (21 / 34) * (137 / 1000) - 1 / 17 := by
  norm_num

theorem atomSpreadTerm_light {floorReading : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hfloor : AtomTripleEigenFloor atomSpreadWeight atomSpreadSecond floorReading)
    {a b c : Fin 6} (h : atomSpreadNum a b c = 1) :
    atomSpreadWeight a b c * floorReading a b c ≤ (1 / 34) * (63 / 1000) := by
  have hbar := atomEigenFloor_le_bar hfloor a b c (bar := 63 / 1000) (by norm_num)
    (atomSpreadWeight_nonneg a b c)
    (by rw [atomSpreadSecond_of_num_one h, atomSpreadWeight_of_num_one h]
        exact atomSpreadSign_light)
  rw [atomSpreadWeight_of_num_one h]
  exact mul_le_mul_of_nonneg_left hbar (by norm_num)

theorem atomSpreadTerm_heavy {floorReading : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hfloor : AtomTripleEigenFloor atomSpreadWeight atomSpreadSecond floorReading)
    {a b c : Fin 6} (h : atomSpreadNum a b c = 2) :
    atomSpreadWeight a b c * floorReading a b c ≤ (1 / 17) * (137 / 1000) := by
  have hbar := atomEigenFloor_le_bar hfloor a b c (bar := 137 / 1000) (by norm_num)
    (atomSpreadWeight_nonneg a b c)
    (by rw [atomSpreadSecond_of_num_two h, atomSpreadWeight_of_num_two h]
        exact atomSpreadSign_heavy)
  rw [atomSpreadWeight_of_num_two h]
  exact mul_le_mul_of_nonneg_left hbar (by norm_num)

/-- **THE CAP OF THE WITNESS, FOR EVERY PER-TRIPLE FLOOR.**  Whatever reading is
at most every eigenvalue of every block, its determinantal average at the witness
is at most `2107 / 17000 = 0.123941176471`.

Six light triples spend `(1/34) * (63/1000)` and fourteen heavy triples spend
`(1/17) * (137/1000)`.  The true reading of the witness is `0.123237642703`, so
the two rational bars cost only `0.0007` of slack. -/
theorem atomSpreadWitness_floorCap (floorReading : Fin 6 → Fin 6 → Fin 6 → ℝ)
    (hfloor : AtomTripleEigenFloor atomSpreadWeight atomSpreadSecond floorReading) :
    atomTripleFamilySum (fun a b c => atomSpreadWeight a b c * floorReading a b c)
      ≤ 2107 / 17000 := by
  obtain ⟨n012, n013, n014, n015, n023, n024, n025, n034, n035, n045,
    n123, n124, n125, n134, n135, n145, n234, n235, n245, n345⟩ := atomSpreadNum_sorted
  simp only [atomTripleFamilySum]
  linarith [atomSpreadTerm_light hfloor n012, atomSpreadTerm_heavy hfloor n013,
    atomSpreadTerm_heavy hfloor n014, atomSpreadTerm_heavy hfloor n015,
    atomSpreadTerm_heavy hfloor n023, atomSpreadTerm_light hfloor n024,
    atomSpreadTerm_heavy hfloor n025, atomSpreadTerm_light hfloor n034,
    atomSpreadTerm_heavy hfloor n035, atomSpreadTerm_heavy hfloor n045,
    atomSpreadTerm_heavy hfloor n123, atomSpreadTerm_heavy hfloor n124,
    atomSpreadTerm_light hfloor n125, atomSpreadTerm_heavy hfloor n134,
    atomSpreadTerm_light hfloor n135, atomSpreadTerm_heavy hfloor n145,
    atomSpreadTerm_heavy hfloor n234, atomSpreadTerm_heavy hfloor n235,
    atomSpreadTerm_heavy hfloor n245, atomSpreadTerm_light hfloor n345]

/-- The cap is below the field-agnostic ceiling, with room. -/
theorem atomSpreadCap_lt_hermitianCeiling : (2107 : ℝ) / 17000 < (3 - Real.sqrt 5) / 6 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [hsq, hnn]

/-- **THE SPREAD LAW DOES NOT LIFT THE CAP.**  No per-triple floor whatever, read
off the second reading and the determinant of a block and valid as a lower bound
for every eigenvalue of that block, has determinantal average at the field-agnostic
ceiling on the whole spread moment class.

The witness is the three-cut weight table of layer 4.  It obeys the pair-minor
law, the six doubled slot marginals, the total, the unit box at every triple of
distinct slots, and the doubled spread law WITH EQUALITY at all thirty pivot
families.  Every valid floor averages to at most `2107 / 17000 = 0.1239412`
there, and the ceiling is `(3 - sqrt 5) / 6 = 0.1273220`. -/
theorem not_atomSpreadCap :
    ¬ ∃ rung : ℝ → ℝ → ℝ,
        (∀ second weight root : ℝ,
            root ^ 3 - (3 / 2) * root ^ 2 + second * root - weight = 0 → rung second weight ≤ root)
          ∧ ∀ weight second : Fin 6 → Fin 6 → Fin 6 → ℝ, AtomSpreadFeasible weight second →
              (3 - Real.sqrt 5) / 6
                ≤ atomTripleFamilySum
                    (fun a b c => weight a b c * rung (second a b c) (weight a b c)) := by
  rintro ⟨rung, hvalid, hclaim⟩
  have hfloor : AtomTripleEigenFloor atomSpreadWeight atomSpreadSecond
      (fun a b c => rung (atomSpreadSecond a b c) (atomSpreadWeight a b c)) :=
    fun a b c root hroot => hvalid _ _ root hroot
  have hcap := atomSpreadWitness_floorCap _ hfloor
  have hbound := hclaim atomSpreadWeight atomSpreadSecond atomSpreadFeasible_witness
  have hlt := atomSpreadCap_lt_hermitianCeiling
  linarith

/-! ## Layer 6 — what the witness fails, and that is the whole message -/

/-- The fifteen pair minors of the witness, in units of `1/34`.  Six read `6`,
six read `7` and three read `8`, and they total `102 / 34 = 3` as a rank-three
projection asks. -/
theorem atomSpreadNum_pairs :
    (∑ v, atomSpreadNum 0 1 v) = 7 ∧ (∑ v, atomSpreadNum 0 2 v) = 6
      ∧ (∑ v, atomSpreadNum 0 3 v) = 7 ∧ (∑ v, atomSpreadNum 0 4 v) = 6
      ∧ (∑ v, atomSpreadNum 0 5 v) = 8 ∧ (∑ v, atomSpreadNum 1 2 v) = 6
      ∧ (∑ v, atomSpreadNum 1 3 v) = 7 ∧ (∑ v, atomSpreadNum 1 4 v) = 8
      ∧ (∑ v, atomSpreadNum 1 5 v) = 6 ∧ (∑ v, atomSpreadNum 2 3 v) = 8
      ∧ (∑ v, atomSpreadNum 2 4 v) = 7 ∧ (∑ v, atomSpreadNum 2 5 v) = 7
      ∧ (∑ v, atomSpreadNum 3 4 v) = 6 ∧ (∑ v, atomSpreadNum 3 5 v) = 6
      ∧ (∑ v, atomSpreadNum 4 5 v) = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **THE WITNESS MISSES THE LEVEL-THREE ENERGY FLOOR.**  Its determinantal energy
is `31/578 = 0.0536332`, and the landed floor for a real balanced frame is
`3/50 = 0.06` (`Gtz.atomPluckerEnergyThree_floor`).  So the energy floor, and NOT
the spread law, is what separates this witness from a frame. -/
theorem atomSpreadWitness_energyFails :
    atomTripleFamilySum (fun a b c => atomSpreadWeight a b c ^ 2) = 31 / 578
      ∧ (31 : ℝ) / 578 < 3 / 50 := by
  obtain ⟨n012, n013, n014, n015, n023, n024, n025, n034, n035, n045,
    n123, n124, n125, n134, n135, n145, n234, n235, n245, n345⟩ := atomSpreadNum_sorted
  constructor
  · simp only [atomTripleFamilySum, atomSpreadWeight, n012, n013, n014, n015, n023, n024, n025,
      n034, n035, n045, n123, n124, n125, n134, n135, n145, n234, n235, n245, n345]
    norm_num
  · norm_num

/-- **THE WITNESS MISSES THE TENTH.**  Its level-two energy is `351/578 = 0.607266`
and ten times its level-three energy is `310/578 = 0.536332`, so the real-only
tenth `E2 <= 10 * E3` fails as well. -/
theorem atomSpreadWitness_tenthFails :
    atomPairFamilySum (fun y z => (∑ v, atomSpreadWeight y z v) ^ 2) = 351 / 578
      ∧ (10 : ℝ) * (31 / 578) < 351 / 578 := by
  obtain ⟨m01, m02, m03, m04, m05, m12, m13, m14, m15, m23, m24, m25, m34, m35, m45⟩ :=
    atomSpreadNum_pairs
  constructor
  · simp only [atomPairFamilySum, atomSpreadWeight_sum, m01, m02, m03, m04, m05, m12, m13, m14,
      m15, m23, m24, m25, m34, m35, m45]
    norm_num
  · norm_num

/-! ## Layer 7 — the reduced rung reads even less -/

/-- The reduced second rung of `Gtz.Wave.DeterminantalWeightKill` averages to
`0.111294179594` at the witness, well below one eighth and therefore well below
the ceiling.  The gap between this and the sharp reading `0.123237642703` is the
price of the rung, not of the class. -/
theorem atomSpreadWitness_reducedRung :
    atomTripleFamilySum (fun a b c =>
        wedgeAverageTerm (3 / 2) (atomSpreadSecond a b c) (atomSpreadWeight a b c)) < 1 / 8 := by
  obtain ⟨n012, n013, n014, n015, n023, n024, n025, n034, n035, n045,
    n123, n124, n125, n134, n135, n145, n234, n235, n245, n345⟩ := atomSpreadNum_sorted
  have hl : ∀ a b c : Fin 6, atomSpreadNum a b c = 1 →
      wedgeAverageTerm (3 / 2) (atomSpreadSecond a b c) (atomSpreadWeight a b c)
        = wedgeAverageTerm (3 / 2) (19 / 34) (1 / 34) := by
    intro a b c h
    rw [atomSpreadSecond_of_num_one h, atomSpreadWeight_of_num_one h]
  have hh : ∀ a b c : Fin 6, atomSpreadNum a b c = 2 →
      wedgeAverageTerm (3 / 2) (atomSpreadSecond a b c) (atomSpreadWeight a b c)
        = wedgeAverageTerm (3 / 2) (21 / 34) (1 / 17) := by
    intro a b c h
    rw [atomSpreadSecond_of_num_two h, atomSpreadWeight_of_num_two h]
  simp only [atomTripleFamilySum, hl _ _ _ n012, hh _ _ _ n013, hh _ _ _ n014, hh _ _ _ n015,
    hh _ _ _ n023, hl _ _ _ n024, hh _ _ _ n025, hl _ _ _ n034, hh _ _ _ n035, hh _ _ _ n045,
    hh _ _ _ n123, hh _ _ _ n124, hl _ _ _ n125, hh _ _ _ n134, hl _ _ _ n135, hh _ _ _ n145,
    hh _ _ _ n234, hh _ _ _ n235, hh _ _ _ n245, hl _ _ _ n345]
  simp only [wedgeAverageTerm, wedgeRungTwoLower]
  norm_num

/-- **THE LADDER OF THIS MODULE, IN ORDER.**  The reduced rung at the witness, the
sharp bound at the witness, the field-agnostic ceiling, and the truth over the
real field. -/
theorem atomSpreadWitness_ladder :
    (2107 : ℝ) / 17000 < (3 - Real.sqrt 5) / 6 ∧ (3 - Real.sqrt 5) / 6 < 1 / 6 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  refine ⟨atomSpreadCap_lt_hermitianCeiling, ?_⟩
  nlinarith [hsq, hnn]

/-! ## Layer 8 — the complementary second reading -/

/-- **THE SECOND READING IS ONE HALF PLUS TWO COMPLEMENTARY DETERMINANTS.**  In
the spread moment class the pair-minor law, the six doubled slot marginals and the
total force

  `second T = 1/2 + weight T + weight (the complement of T)`.

The derivation is four lines of linear algebra.  Write `A` for the total of the
nine weights that meet `T` in exactly two slots.  The pair-minor law gives
`second T = 3 * weight T + A`.  The three marginals of the slots of `T` add to
`3 * weight T + 2 * A + B = 3/2`, where `B` is the total of the nine weights that
meet `T` in exactly one slot, and the grand total gives
`weight T + A + B + weight Tᶜ = 1`.  Subtracting the second from the first leaves
`2 * weight T + A = 1/2 + weight Tᶜ`, which is the claim.

Two consequences are worth naming.  The second reading of a triple EQUALS the
second reading of its complement.  And on the complement-symmetric slice
`weight T = weight Tᶜ` the readings collapse to the one-parameter family
`(3/2, 1/2 + 2 q, q)`, whose discriminant is `(1 - 8 q) ^ 3 / 16` and whose block
spectrum is the half family of `Gtz.atomBlockSpectrum_half`.  That collapse turns
the twenty-variable relaxation into a ten-variable one, indexed by the ten
splittings of the six slots into two triples, and it is what makes the search of
this module cheap.

The ten equations below check the identity at the witness. -/
theorem atomSpreadSecond_complement :
    atomSpreadSecond 0 1 2 = 1 / 2 + atomSpreadWeight 0 1 2 + atomSpreadWeight 3 4 5
      ∧ atomSpreadSecond 0 1 3 = 1 / 2 + atomSpreadWeight 0 1 3 + atomSpreadWeight 2 4 5
      ∧ atomSpreadSecond 0 1 4 = 1 / 2 + atomSpreadWeight 0 1 4 + atomSpreadWeight 2 3 5
      ∧ atomSpreadSecond 0 1 5 = 1 / 2 + atomSpreadWeight 0 1 5 + atomSpreadWeight 2 3 4
      ∧ atomSpreadSecond 0 2 3 = 1 / 2 + atomSpreadWeight 0 2 3 + atomSpreadWeight 1 4 5
      ∧ atomSpreadSecond 0 2 4 = 1 / 2 + atomSpreadWeight 0 2 4 + atomSpreadWeight 1 3 5
      ∧ atomSpreadSecond 0 2 5 = 1 / 2 + atomSpreadWeight 0 2 5 + atomSpreadWeight 1 3 4
      ∧ atomSpreadSecond 0 3 4 = 1 / 2 + atomSpreadWeight 0 3 4 + atomSpreadWeight 1 2 5
      ∧ atomSpreadSecond 0 3 5 = 1 / 2 + atomSpreadWeight 0 3 5 + atomSpreadWeight 1 2 4
      ∧ atomSpreadSecond 0 4 5 = 1 / 2 + atomSpreadWeight 0 4 5 + atomSpreadWeight 1 2 3 := by
  obtain ⟨n012, n013, n014, n015, n023, n024, n025, n034, n035, n045,
    n123, n124, n125, n134, n135, n145, n234, n235, n245, n345⟩ := atomSpreadNum_sorted
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [atomSpreadSecond_of_num_one n012, atomSpreadWeight_of_num_one n012,
      atomSpreadWeight_of_num_one n345]; norm_num
  · rw [atomSpreadSecond_of_num_two n013, atomSpreadWeight_of_num_two n013,
      atomSpreadWeight_of_num_two n245]; norm_num
  · rw [atomSpreadSecond_of_num_two n014, atomSpreadWeight_of_num_two n014,
      atomSpreadWeight_of_num_two n235]; norm_num
  · rw [atomSpreadSecond_of_num_two n015, atomSpreadWeight_of_num_two n015,
      atomSpreadWeight_of_num_two n234]; norm_num
  · rw [atomSpreadSecond_of_num_two n023, atomSpreadWeight_of_num_two n023,
      atomSpreadWeight_of_num_two n145]; norm_num
  · rw [atomSpreadSecond_of_num_one n024, atomSpreadWeight_of_num_one n024,
      atomSpreadWeight_of_num_one n135]; norm_num
  · rw [atomSpreadSecond_of_num_two n025, atomSpreadWeight_of_num_two n025,
      atomSpreadWeight_of_num_two n134]; norm_num
  · rw [atomSpreadSecond_of_num_one n034, atomSpreadWeight_of_num_one n034,
      atomSpreadWeight_of_num_one n125]; norm_num
  · rw [atomSpreadSecond_of_num_two n035, atomSpreadWeight_of_num_two n035,
      atomSpreadWeight_of_num_two n124]; norm_num
  · rw [atomSpreadSecond_of_num_two n045, atomSpreadWeight_of_num_two n045,
      atomSpreadWeight_of_num_two n123]; norm_num

/-- **THE FLAT POINT IS EXCLUDED, AND THE SPREAD LAW IS WHAT EXCLUDES IT.**  A
weight table that reads the same value at every triple of distinct slots and obeys
the spread law reads ZERO there, so it cannot carry the total one.  This is the
class-level form of `Gtz.not_uniform_dppTripleWeight`, and it is the whole reason
this module exists. -/
theorem atomSpreadFeasible_not_uniform {weight second : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (h : AtomSpreadFeasible weight second) (value : ℝ)
    (huniform : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → weight a b c = value) : False := by
  obtain ⟨hnn, -, -, -, -, -, htot, -, hspread⟩ := h
  have hval : 0 ≤ value := by
    rw [← huniform 0 1 2 (by decide) (by decide) (by decide)]; exact hnn 0 1 2
  have hstep := hspread 0 1 2 3 4 value value hval
    (le_of_eq (huniform 0 1 2 (by decide) (by decide) (by decide)).symm)
    (le_of_eq (huniform 0 1 3 (by decide) (by decide) (by decide)).symm)
    (le_of_eq (huniform 0 1 4 (by decide) (by decide) (by decide)).symm)
    (le_of_eq (huniform 0 2 3 (by decide) (by decide) (by decide)).symm)
    (le_of_eq (huniform 0 2 4 (by decide) (by decide) (by decide)).symm)
    (le_of_eq (huniform 0 3 4 (by decide) (by decide) (by decide)).symm)
    (le_of_eq (huniform 0 1 2 (by decide) (by decide) (by decide)))
    (le_of_eq (huniform 0 1 3 (by decide) (by decide) (by decide)))
    (le_of_eq (huniform 0 1 4 (by decide) (by decide) (by decide)))
    (le_of_eq (huniform 0 2 3 (by decide) (by decide) (by decide)))
    (le_of_eq (huniform 0 2 4 (by decide) (by decide) (by decide)))
    (le_of_eq (huniform 0 3 4 (by decide) (by decide) (by decide)))
  have hzero : value = 0 := by linarith
  simp only [atomTripleFamilySum] at htot
  rw [huniform 0 1 2 (by decide) (by decide) (by decide),
    huniform 0 1 3 (by decide) (by decide) (by decide),
    huniform 0 1 4 (by decide) (by decide) (by decide),
    huniform 0 1 5 (by decide) (by decide) (by decide),
    huniform 0 2 3 (by decide) (by decide) (by decide),
    huniform 0 2 4 (by decide) (by decide) (by decide),
    huniform 0 2 5 (by decide) (by decide) (by decide),
    huniform 0 3 4 (by decide) (by decide) (by decide),
    huniform 0 3 5 (by decide) (by decide) (by decide),
    huniform 0 4 5 (by decide) (by decide) (by decide),
    huniform 1 2 3 (by decide) (by decide) (by decide),
    huniform 1 2 4 (by decide) (by decide) (by decide),
    huniform 1 2 5 (by decide) (by decide) (by decide),
    huniform 1 3 4 (by decide) (by decide) (by decide),
    huniform 1 3 5 (by decide) (by decide) (by decide),
    huniform 1 4 5 (by decide) (by decide) (by decide),
    huniform 2 3 4 (by decide) (by decide) (by decide),
    huniform 2 3 5 (by decide) (by decide) (by decide),
    huniform 2 4 5 (by decide) (by decide) (by decide),
    huniform 3 4 5 (by decide) (by decide) (by decide), hzero] at htot
  norm_num at htot

/-! ## Layer 9 — the four constants of the determinantal-average route -/

/-- **THE CONSTANT LADDER OF THE ROUTE, IN ORDER.**  Four exact numbers bound the
determinantal average of the SMALLEST EIGENVALUE, which is the sharpest objective
the route can carry, because every per-triple floor is at most that eigenvalue.

  `(5 - sqrt 15) / 10 = 0.112701665379`  the flat point, and the cap of the
      moment class with NO real-only law.  It is also the flat-average ceiling
      `Gtz.atomFlatDrop_factor` and the measured quaternionic constant, three
      readings of one number.
  `(3 - sqrt 5) / 6   = 0.127322003750`  the field-agnostic ceiling, the bar.
  `(2 - sqrt 2) / 4   = 0.146446609407`  the reading of the point that the
      REAL-ONLY TENTH `Gtz.atomPluckerTenth` drives the class to: two of the ten
      splittings of the six slots carry no determinant and the other eight carry
      `1/16`, every block then reads `(3/2, 5/8, 1/16)`, and its smallest
      eigenvalue is `(2 - sqrt 2) / 4`.  The tenth is exactly tight there, at
      `E2 = 10 * E3 = 5/8`.
  `1 / 6              = 0.166666666667`  the truth over the real field.

The witness of this module reads `2107 / 17000 = 0.123941176471` and sits BELOW
the bar, which is the refutation.  Every point that survives the tenth that the
search of this module found sits above the bar.  So the tenth carries the realness
that the spread law does not.

Two measurements name the remaining room, and they are measurements and not
theorems.  Minimised over the class of this module the sharp average reads
`0.1204` with the spread law and `0.1464` with the tenth.  Minimised over GENUINE
balanced real Parseval frames it reads `0.1652156`, which is BELOW `1/6`.  So even
a perfect per-triple floor cannot certify the truth through a determinantal
average: the route has a ceiling of its own, near `0.16522`, and it is one percent
short.  The frame that reads it carries eight determinants at exactly `1/16` and
twelve others in four classes. -/
theorem atomSpreadConstantLadder :
    (5 - Real.sqrt 15) / 10 < (3 - Real.sqrt 5) / 6
      ∧ (3 - Real.sqrt 5) / 6 < (2 - Real.sqrt 2) / 4
      ∧ (2 - Real.sqrt 2) / 4 < 1 / 6 := by
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have n15 : (0 : ℝ) ≤ Real.sqrt 15 := Real.sqrt_nonneg 15
  have n5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have n2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  refine ⟨by nlinarith [h15, h5, n15, n5], by nlinarith [h5, h2, n5, n2],
    by nlinarith [h2, n2]⟩

/-- **THE READING OF THE TENTH EXTREMAL, EXACTLY.**  A block with the readings
`(3/2, 5/8, 1/16)` has the spectrum `(1/2, (2 - sqrt 2)/4, (2 + sqrt 2)/4)`, so its
smallest eigenvalue is `(2 - sqrt 2)/4`.  Sixteen such blocks carrying the whole
determinantal mass average to that same number. -/
theorem atomTenthExtremal_spectrum :
    AtomBlockSpectrum (3 / 2) (5 / 8) (1 / 16)
      ∧ ((2 - Real.sqrt 2) / 4) ^ 3 - (3 / 2) * ((2 - Real.sqrt 2) / 4) ^ 2
          + (5 / 8) * ((2 - Real.sqrt 2) / 4) - 1 / 16 = 0 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨atomBlockSpectrum_half (product := 1 / 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num), ?_⟩
  nlinarith [h2]

/-- The block of a triple that carries NO determinant, in the same extremal, reads
`(3/2, 1/2, 0)` and has the spectrum `(0, 1/2, 1)`. -/
theorem atomTenthExtremal_flatSpectrum : AtomBlockSpectrum (3 / 2) (1 / 2) 0 :=
  atomBlockSpectrum_half (product := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Layer 10 — why the split witness of the moment programme dies here -/

/-- **THE DISCRIMINANT OF A BLOCK SPECTRUM IS NOT NEGATIVE.**  It is the square of
the product of the three eigenvalue gaps, so a triple of readings whose
discriminant is negative is not a real spectrum at all. -/
theorem atomBlockSpectrum_disc_nonneg {first second third : ℝ}
    (h : AtomBlockSpectrum first second third) :
    0 ≤ 18 * first * second * third - 4 * first ^ 3 * third + first ^ 2 * second ^ 2
      - 4 * second ^ 3 - 27 * third ^ 2 := by
  obtain ⟨r1, r2, r3, -, -, -, -, -, -, h1, h2, h3⟩ := h
  subst h1; subst h2; subst h3
  nlinarith [sq_nonneg ((r1 - r2) * (r1 - r3) * (r2 - r3))]

/-- **THE SPLIT WITNESS OF `Gtz.not_atomMomentCap_withEnergy` IS NOT IN THIS
CLASS.**  Its ten heavy triples read the determinant `29/400`.  All fifteen of its
pair minors read `1/5`, because every pair carries exactly two heavy triples and
two light ones among the four triples through it.  The pair-minor law then forces
the second reading `3 * (1/5) = 3/5` at EVERY triple, in place of the `129/200`
that the witness declares.

The forced reading `(3/2, 3/5, 29/400)` has discriminant `-27/160000`, so it is
not a real spectrum.  The witness that capped the moment programme with the
energy floor therefore does not survive the pair-minor law, and the class of this
module is strictly smaller than the class of
`Gtz.AtomMomentFeasible` intersected with the energy floor. -/
theorem not_atomBlockSpectrum_splitHeavy : ¬ AtomBlockSpectrum (3 / 2) (3 / 5) (29 / 400) := by
  intro h
  have hd := atomBlockSpectrum_disc_nonneg h
  have hv : 18 * (3 / 2 : ℝ) * (3 / 5) * (29 / 400) - 4 * (3 / 2) ^ 3 * (29 / 400)
      + (3 / 2) ^ 2 * (3 / 5) ^ 2 - 4 * (3 / 5) ^ 3 - 27 * (29 / 400) ^ 2
      = -(27 / 160000) := by norm_num
  rw [hv] at hd
  norm_num at hd

/-- **BOTH CLASSES OF THE SPLIT WITNESS DIE, AND BY THE SAME MARGIN.**  With the
second reading forced to `3/5`, the discriminant of `(3/2, 3/5, e)` is the
downward parabola `27 * e * (1/10 - e) - 27 * e ^ 2 ... ` whose two roots are
`(5 +- sqrt 5) / 100`, the icosahedral pair, and whose axis is `e = 1/20`, the flat
point.  The two readings `29/400` and `11/400` sit symmetrically about `1/20` at a
distance `9/400`, which is MORE than the icosahedral half-width `sqrt 5 / 100`, so
both fall outside the two roots and both read `-27/160000`. -/
theorem atomSplitHeavy_disc :
    18 * (3 / 2 : ℝ) * (3 / 5) * (29 / 400) - 4 * (3 / 2) ^ 3 * (29 / 400)
        + (3 / 2) ^ 2 * (3 / 5) ^ 2 - 4 * (3 / 5) ^ 3 - 27 * (29 / 400) ^ 2
      = -(27 / 160000)
      ∧ 18 * (3 / 2 : ℝ) * (3 / 5) * (11 / 400) - 4 * (3 / 2) ^ 3 * (11 / 400)
        + (3 / 2) ^ 2 * (3 / 5) ^ 2 - 4 * (3 / 5) ^ 3 - 27 * (11 / 400) ^ 2
      = -(27 / 160000) := by
  constructor <;> norm_num

/-- Neither reading of the split witness is a real spectrum once the pair-minor
law has forced the second reading to `3/5`. -/
theorem not_atomBlockSpectrum_splitLight : ¬ AtomBlockSpectrum (3 / 2) (3 / 5) (11 / 400) := by
  intro h
  have hd := atomBlockSpectrum_disc_nonneg h
  rw [atomSplitHeavy_disc.2] at hd
  norm_num at hd

end Gtz
