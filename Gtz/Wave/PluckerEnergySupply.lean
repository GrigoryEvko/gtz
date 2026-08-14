import Gtz.Wave.SpectralSupplyCell

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The determinantal energy of a rank-three Parseval frame of six atoms

This module reads the atom cell through the DETERMINANTAL MEASURE that the
twenty triples carry, and not through the flat average of the twenty. The flat
average is a constant of the whole problem, so it cannot select. The
determinantal average selects, and it lands three things.

## 1. The two-slot marginal law

`Gtz.atomBlockPairMinor_eq_blockDet_sum`: for every pair of slots the PAIR MINOR is
the total of the six triple determinants that carry the pair,

  `s y * s z - g y z ^ 2 = ∑ v, atomBlockDet atom y z v`.

Two of the six terms are zero, so the pair minor is the total of the four
triples that contain the pair. The proof is the frame law read against ONE
vector, the wedge of the two slots, and the two zero terms are the two
orthogonality laws of that wedge. This is the second marginal of the
determinantal measure, and the campaign did not have it.

## 2. The determinantal moment law

With the pair minors and the triple determinants as the two levels of the
measure, define

  `E2 = ∑ over the fifteen pairs of (pair minor) ^ 2`
  `E3 = ∑ over the twenty triples of (triple determinant) ^ 2`.

`Gtz.atomBlockDet_mul_second_familySum` says that the determinantal average of
the SECOND MINOR TOTAL is `E2`, and the determinantal average of the triple
determinant is `E3`:

  `∑ T, p T * second T = E2`   and   `∑ T, p T * det T = E3`.

So the pair `(E2, E3)` is the second and third coefficient of the
determinant-weighted characteristic polynomial of the twenty blocks. Both are
explicit polynomials in the Gram.

## 3. The energy bound, and the exact residue

`Gtz.atomSpectralSupply_of_energyBound`: whenever `E2 ≤ ratio * E3` the frame
carries a triple whose block never shortens a probe below `1 / ratio`. The
proof selects the triple by the determinantal average and certifies it by the
landed wedge inequality.

`Gtz.atomPluckerEnergyTwo_le_twelve` proves `E2 ≤ 12 * E3` for EVERY frame, by
one Cauchy-Schwarz step for each of the fifteen pairs. So
`Gtz.atomSpectralSupply_twelfth` gives

  **every rank-three Parseval frame of six atoms carries a triple with a
  spectral floor of one twelfth.**

The previous record of the campaign is `Gtz.atomSpectralSupply_of_lt_twelfth`,
which needs the floor STRICTLY below one twelfth, and its concrete form
`Gtz.exists_atomLightCarrier_thirteen` at one thirteenth. The bound here is at
one twelfth, and the mechanism is different: the flat average of the twenty
blocks cannot pass twelve, because the second minor total of the twenty is `12`
and their determinant total is `1`, and both are universal.

`Gtz.atomPluckerFlatnessGap_eq_spread` says exactly what the twelve costs:

  `12 * E3 - E2 = ∑ over the fifteen pairs of ∑ over the six pairs of triples
      that carry it of (difference of the two triple determinants) ^ 2`.

**The distance from the record to the truth is EXACTLY the non-flatness of the
Plücker weight vector.** The unifying hypothesis of the campaign is no longer a
hypothesis about a mechanism. It is this identity.

`Gtz.AtomPluckerTenth` names the residue: `E2 ≤ 10 * E3`. It is REAL-ONLY. The
adversarial value of `E2 / E3` over the real frames is exactly `10`, attained at
the icosahedral frame, and over the Hermitian field it is `78 / 7`, which is
larger. `Gtz.atomSpectralSupply_tenth_of_pluckerTenth` spends the residue for a
floor of one tenth.

## What this module does NOT reach

The truth is one sixth. The step that loses is the wedge inequality, which
reads `lambda_min >= det / second`. At the real extremal the winning triple has
the spectrum `(1/6, 16/21, 1)`, so its `det / second` is `16 / 133`, well below
one sixth. No bound built on the wedge inequality can be sharp. The successor
lane must replace the wedge step, and not the energy step.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

Every statement below is proved. `Gtz.AtomPluckerTenth` is a definition, and
every theorem that reads it takes it as a hypothesis.

## Vacuity

`Gtz.atomSpectralSupply_twelfth` is unconditional and its hypothesis is the
frame law alone, so it is not vacuous.
-/

namespace Gtz

variable {atom : Fin 6 → (Fin 3 → ℝ)}

/-! ## Layer 0 — the pair minor as a level of the determinantal measure -/

/-- The PAIR MINOR of two slots: the two-by-two principal minor of the Gram.
It is the second marginal of the determinantal measure, and it is the squared
energy of the wedge of the two atoms. -/
def atomBlockPairMinor (atom : Fin 6 → (Fin 3 → ℝ)) (rowSlot colSlot : Fin 6) : ℝ :=
  atomGram atom rowSlot rowSlot * atomGram atom colSlot colSlot
    - atomGram atom rowSlot colSlot ^ 2

theorem atomBlockPairMinor_eq_wedge_energy (atom : Fin 6 → (Fin 3 → ℝ))
    (rowSlot colSlot : Fin 6) :
    atomBlockPairMinor atom rowSlot colSlot
      = atomWedge (atom rowSlot) (atom colSlot)
        ⬝ᵥ atomWedge (atom rowSlot) (atom colSlot) :=
  atomPairGram_eq_wedge_energy atom rowSlot colSlot

theorem atomBlockPairMinor_nonneg (atom : Fin 6 → (Fin 3 → ℝ)) (rowSlot colSlot : Fin 6) :
    0 ≤ atomBlockPairMinor atom rowSlot colSlot :=
  atomPairGram_nonneg atom rowSlot colSlot

/-- **THE SECOND MINOR TOTAL IS THE TOTAL OF THREE PAIR MINORS.** -/
theorem atomBlockSecond_eq_pairMinor_sum (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    atomBlockSecond atom slotOne slotTwo slotThree
      = atomBlockPairMinor atom slotOne slotTwo + atomBlockPairMinor atom slotOne slotThree
        + atomBlockPairMinor atom slotTwo slotThree := by
  simp only [atomBlockSecond, atomBlockPairMinor]

/-- The triple determinant read as the squared volume against the wedge of the
first two slots. -/
theorem atomBlockDet_eq_wedge_reading (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    atomBlockDet atom slotOne slotTwo slotThree
      = (atom slotThree ⬝ᵥ atomWedge (atom slotOne) (atom slotTwo)) ^ 2 := by
  rw [atomBlockDet_eq_volume_sq]
  simp only [atomVolume, dotProduct, Fin.sum_univ_three, atomWedge,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- The triple determinant does not read the order of its three slots: the
rotation. -/
theorem atomBlockDet_rot (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6) :
    atomBlockDet atom slotOne slotTwo slotThree = atomBlockDet atom slotThree slotOne slotTwo := by
  simp only [atomBlockDet, atomGram, dotProduct, Fin.sum_univ_three]
  ring

/-- The triple determinant does not read the order of its three slots: the last
two change places. -/
theorem atomBlockDet_swapLast (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    atomBlockDet atom slotOne slotTwo slotThree = atomBlockDet atom slotOne slotThree slotTwo := by
  simp only [atomBlockDet, atomGram, dotProduct, Fin.sum_univ_three]
  ring

/-- A triple determinant with a repeated outer slot is zero. -/
theorem atomBlockDet_dup_outer (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo : Fin 6) :
    atomBlockDet atom slotOne slotTwo slotOne = 0 := by
  simp only [atomBlockDet, atomGram, dotProduct, Fin.sum_univ_three]
  ring

/-- A triple determinant with a repeated inner slot is zero. -/
theorem atomBlockDet_dup_inner (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo : Fin 6) :
    atomBlockDet atom slotOne slotTwo slotTwo = 0 := by
  simp only [atomBlockDet, atomGram, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE TWO-SLOT MARGINAL LAW.**  The pair minor of two slots is the total of
the six triple determinants that carry the pair in the first two places.  Two
of the six terms are zero, so it is the total of the four triples that contain
the pair.

The proof reads the frame law against ONE vector, the wedge of the two slots,
and the wedge energy law turns the answer into the pair minor.  This is the
second marginal of the determinantal measure of the twenty triples. -/
theorem atomBlockPairMinor_eq_blockDet_sum
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot colSlot : Fin 6) :
    (∑ v, atomBlockDet atom rowSlot colSlot v) = atomBlockPairMinor atom rowSlot colSlot := by
  have hcell : ∀ v : Fin 6, atomBlockDet atom rowSlot colSlot v
      = (atom v ⬝ᵥ atomWedge (atom rowSlot) (atom colSlot))
        * (atom v ⬝ᵥ atomWedge (atom rowSlot) (atom colSlot)) := by
    intro v
    rw [atomBlockDet_eq_wedge_reading, sq]
  rw [Finset.sum_congr rfl fun v _ => hcell v,
    hframe (atomWedge (atom rowSlot) (atom colSlot))
      (atomWedge (atom rowSlot) (atom colSlot)),
    atomBlockPairMinor_eq_wedge_energy]

/-! ## Layer 1 — the fifteen marginals in canonical order -/

/-- The total of a reading over the FIFTEEN distinct pairs of six slots. -/
def atomPairFamilySum (value : Fin 6 → Fin 6 → ℝ) : ℝ :=
  value 0 1 + value 0 2 + value 0 3 + value 0 4 + value 0 5
    + value 1 2 + value 1 3 + value 1 4 + value 1 5
    + value 2 3 + value 2 4 + value 2 5
    + value 3 4 + value 3 5 + value 4 5

theorem atomMarginal_01
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 1 2 + atomBlockDet atom 0 1 3 + atomBlockDet atom 0 1 4
        + atomBlockDet atom 0 1 5
      = atomBlockPairMinor atom 0 1 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 0 1
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  linarith

theorem atomMarginal_02
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 1 2 + atomBlockDet atom 0 2 3 + atomBlockDet atom 0 2 4
        + atomBlockDet atom 0 2 5
      = atomBlockPairMinor atom 0 2 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 0 2
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_swapLast atom 0 2 1] at h
  linarith

theorem atomMarginal_03
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 1 3 + atomBlockDet atom 0 2 3 + atomBlockDet atom 0 3 4
        + atomBlockDet atom 0 3 5
      = atomBlockPairMinor atom 0 3 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 0 3
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_swapLast atom 0 3 1, atomBlockDet_swapLast atom 0 3 2] at h
  linarith

theorem atomMarginal_04
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 1 4 + atomBlockDet atom 0 2 4 + atomBlockDet atom 0 3 4
        + atomBlockDet atom 0 4 5
      = atomBlockPairMinor atom 0 4 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 0 4
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_swapLast atom 0 4 1, atomBlockDet_swapLast atom 0 4 2,
    atomBlockDet_swapLast atom 0 4 3] at h
  linarith

theorem atomMarginal_05
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 1 5 + atomBlockDet atom 0 2 5 + atomBlockDet atom 0 3 5
        + atomBlockDet atom 0 4 5
      = atomBlockPairMinor atom 0 5 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 0 5
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_swapLast atom 0 5 1, atomBlockDet_swapLast atom 0 5 2,
    atomBlockDet_swapLast atom 0 5 3, atomBlockDet_swapLast atom 0 5 4] at h
  linarith

theorem atomMarginal_12
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 1 2 + atomBlockDet atom 1 2 3 + atomBlockDet atom 1 2 4
        + atomBlockDet atom 1 2 5
      = atomBlockPairMinor atom 1 2 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 1 2
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_rot atom 1 2 0] at h
  linarith

theorem atomMarginal_13
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 1 3 + atomBlockDet atom 1 2 3 + atomBlockDet atom 1 3 4
        + atomBlockDet atom 1 3 5
      = atomBlockPairMinor atom 1 3 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 1 3
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_rot atom 1 3 0, atomBlockDet_swapLast atom 1 3 2] at h
  linarith

theorem atomMarginal_14
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 1 4 + atomBlockDet atom 1 2 4 + atomBlockDet atom 1 3 4
        + atomBlockDet atom 1 4 5
      = atomBlockPairMinor atom 1 4 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 1 4
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_rot atom 1 4 0, atomBlockDet_swapLast atom 1 4 2,
    atomBlockDet_swapLast atom 1 4 3] at h
  linarith

theorem atomMarginal_15
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 1 5 + atomBlockDet atom 1 2 5 + atomBlockDet atom 1 3 5
        + atomBlockDet atom 1 4 5
      = atomBlockPairMinor atom 1 5 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 1 5
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_rot atom 1 5 0, atomBlockDet_swapLast atom 1 5 2,
    atomBlockDet_swapLast atom 1 5 3, atomBlockDet_swapLast atom 1 5 4] at h
  linarith

theorem atomMarginal_23
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 2 3 + atomBlockDet atom 1 2 3 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 2 3 5
      = atomBlockPairMinor atom 2 3 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 2 3
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_rot atom 2 3 0, atomBlockDet_rot atom 2 3 1] at h
  linarith

theorem atomMarginal_24
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 2 4 + atomBlockDet atom 1 2 4 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 2 4 5
      = atomBlockPairMinor atom 2 4 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 2 4
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_rot atom 2 4 0, atomBlockDet_rot atom 2 4 1,
    atomBlockDet_swapLast atom 2 4 3] at h
  linarith

theorem atomMarginal_25
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 2 5 + atomBlockDet atom 1 2 5 + atomBlockDet atom 2 3 5
        + atomBlockDet atom 2 4 5
      = atomBlockPairMinor atom 2 5 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 2 5
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_rot atom 2 5 0, atomBlockDet_rot atom 2 5 1,
    atomBlockDet_swapLast atom 2 5 3, atomBlockDet_swapLast atom 2 5 4] at h
  linarith

theorem atomMarginal_34
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 3 4 + atomBlockDet atom 1 3 4 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 3 4 5
      = atomBlockPairMinor atom 3 4 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 3 4
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_rot atom 3 4 0, atomBlockDet_rot atom 3 4 1,
    atomBlockDet_rot atom 3 4 2] at h
  linarith

theorem atomMarginal_35
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 3 5 + atomBlockDet atom 1 3 5 + atomBlockDet atom 2 3 5
        + atomBlockDet atom 3 4 5
      = atomBlockPairMinor atom 3 5 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 3 5
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_rot atom 3 5 0, atomBlockDet_rot atom 3 5 1,
    atomBlockDet_rot atom 3 5 2, atomBlockDet_swapLast atom 3 5 4] at h
  linarith

theorem atomMarginal_45
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomBlockDet atom 0 4 5 + atomBlockDet atom 1 4 5 + atomBlockDet atom 2 4 5
        + atomBlockDet atom 3 4 5
      = atomBlockPairMinor atom 4 5 := by
  have h := atomBlockPairMinor_eq_blockDet_sum hframe 4 5
  simp only [Fin.sum_univ_six, atomBlockDet_dup_outer, atomBlockDet_dup_inner] at h
  rw [atomBlockDet_rot atom 4 5 0, atomBlockDet_rot atom 4 5 1,
    atomBlockDet_rot atom 4 5 2, atomBlockDet_rot atom 4 5 3] at h
  linarith

/-! ## Layer 2 — the two determinantal energies -/

/-- The DETERMINANTAL ENERGY OF LEVEL TWO: the total of the squared pair minors
over the fifteen pairs.  It is the determinantal average of the second minor
total of the twenty blocks. -/
def atomPluckerEnergyTwo (atom : Fin 6 → (Fin 3 → ℝ)) : ℝ :=
  atomPairFamilySum fun rowSlot colSlot => atomBlockPairMinor atom rowSlot colSlot ^ 2

/-- The DETERMINANTAL ENERGY OF LEVEL THREE: the total of the squared triple
determinants over the twenty triples.  It is the determinantal average of the
triple determinant. -/
def atomPluckerEnergyThree (atom : Fin 6 → (Fin 3 → ℝ)) : ℝ :=
  atomTripleFamilySum fun slotOne slotTwo slotThree =>
    atomBlockDet atom slotOne slotTwo slotThree ^ 2

theorem atomPluckerEnergyThree_nonneg (atom : Fin 6 → (Fin 3 → ℝ)) :
    0 ≤ atomPluckerEnergyThree atom := by
  simp only [atomPluckerEnergyThree, atomTripleFamilySum]
  positivity

theorem atomPluckerEnergyTwo_nonneg (atom : Fin 6 → (Fin 3 → ℝ)) :
    0 ≤ atomPluckerEnergyTwo atom := by
  simp only [atomPluckerEnergyTwo, atomPairFamilySum]
  positivity

/-- **THE DETERMINANTAL MOMENT LAW.**  The determinantal average of the second
minor total of the twenty blocks is the level-two energy.  The flat average of
the same reading is the universal constant `12`, which cannot separate one
frame from another.  The determinantal average is a polynomial in the Gram that
does separate them. -/
theorem atomBlockDet_mul_second_familySum
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomTripleFamilySum (fun slotOne slotTwo slotThree =>
        atomBlockDet atom slotOne slotTwo slotThree
          * atomBlockSecond atom slotOne slotTwo slotThree)
      = atomPluckerEnergyTwo atom := by
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
  simp only [atomTripleFamilySum, atomPluckerEnergyTwo, atomPairFamilySum,
    atomBlockSecond_eq_pairMinor_sum]
  linear_combination (atomBlockPairMinor atom 0 1) * h01 + (atomBlockPairMinor atom 0 2) * h02
    + (atomBlockPairMinor atom 0 3) * h03 + (atomBlockPairMinor atom 0 4) * h04
    + (atomBlockPairMinor atom 0 5) * h05 + (atomBlockPairMinor atom 1 2) * h12
    + (atomBlockPairMinor atom 1 3) * h13 + (atomBlockPairMinor atom 1 4) * h14
    + (atomBlockPairMinor atom 1 5) * h15 + (atomBlockPairMinor atom 2 3) * h23
    + (atomBlockPairMinor atom 2 4) * h24 + (atomBlockPairMinor atom 2 5) * h25
    + (atomBlockPairMinor atom 3 4) * h34 + (atomBlockPairMinor atom 3 5) * h35
    + (atomBlockPairMinor atom 4 5) * h45

/-! ## Layer 3 — the flatness identity and the energy bound -/

/-- The SPREAD TERM of four readings: the total of their six squared
differences. -/
def atomFourFlatnessTerm (valueOne valueTwo valueThree valueFour : ℝ) : ℝ :=
  (valueOne - valueTwo) ^ 2 + (valueOne - valueThree) ^ 2 + (valueOne - valueFour) ^ 2
    + (valueTwo - valueThree) ^ 2 + (valueTwo - valueFour) ^ 2
    + (valueThree - valueFour) ^ 2

/-- **THE FOUR-SLOT FLATNESS IDENTITY.**  Four times the total of the squares
against the square of the total is exactly the spread term. -/
theorem atomFourFlatness (valueOne valueTwo valueThree valueFour : ℝ) :
    4 * (valueOne ^ 2 + valueTwo ^ 2 + valueThree ^ 2 + valueFour ^ 2)
        - (valueOne + valueTwo + valueThree + valueFour) ^ 2
      = atomFourFlatnessTerm valueOne valueTwo valueThree valueFour := by
  simp only [atomFourFlatnessTerm]
  ring

/-- The four-slot Cauchy-Schwarz step, in the form the pair marginal feeds. -/
theorem atomFourCauchy (valueOne valueTwo valueThree valueFour : ℝ) :
    (valueOne + valueTwo + valueThree + valueFour) ^ 2
      ≤ 4 * (valueOne ^ 2 + valueTwo ^ 2 + valueThree ^ 2 + valueFour ^ 2) := by
  nlinarith [sq_nonneg (valueOne - valueTwo), sq_nonneg (valueOne - valueThree),
    sq_nonneg (valueOne - valueFour), sq_nonneg (valueTwo - valueThree),
    sq_nonneg (valueTwo - valueFour), sq_nonneg (valueThree - valueFour)]

/-- The SPREAD of the determinantal measure: the total, over the fifteen pairs,
of the six squared differences of the four triple determinants that carry the
pair.  It is zero exactly when the twenty triple determinants are all equal. -/
def atomPluckerSpread (atom : Fin 6 → (Fin 3 → ℝ)) : ℝ :=
  atomFourFlatnessTerm (atomBlockDet atom 0 1 2) (atomBlockDet atom 0 1 3)
      (atomBlockDet atom 0 1 4) (atomBlockDet atom 0 1 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 1 2) (atomBlockDet atom 0 2 3)
      (atomBlockDet atom 0 2 4) (atomBlockDet atom 0 2 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 1 3) (atomBlockDet atom 0 2 3)
      (atomBlockDet atom 0 3 4) (atomBlockDet atom 0 3 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 1 4) (atomBlockDet atom 0 2 4)
      (atomBlockDet atom 0 3 4) (atomBlockDet atom 0 4 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 1 5) (atomBlockDet atom 0 2 5)
      (atomBlockDet atom 0 3 5) (atomBlockDet atom 0 4 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 1 2) (atomBlockDet atom 1 2 3)
      (atomBlockDet atom 1 2 4) (atomBlockDet atom 1 2 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 1 3) (atomBlockDet atom 1 2 3)
      (atomBlockDet atom 1 3 4) (atomBlockDet atom 1 3 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 1 4) (atomBlockDet atom 1 2 4)
      (atomBlockDet atom 1 3 4) (atomBlockDet atom 1 4 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 1 5) (atomBlockDet atom 1 2 5)
      (atomBlockDet atom 1 3 5) (atomBlockDet atom 1 4 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 2 3) (atomBlockDet atom 1 2 3)
      (atomBlockDet atom 2 3 4) (atomBlockDet atom 2 3 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 2 4) (atomBlockDet atom 1 2 4)
      (atomBlockDet atom 2 3 4) (atomBlockDet atom 2 4 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 2 5) (atomBlockDet atom 1 2 5)
      (atomBlockDet atom 2 3 5) (atomBlockDet atom 2 4 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 3 4) (atomBlockDet atom 1 3 4)
      (atomBlockDet atom 2 3 4) (atomBlockDet atom 3 4 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 3 5) (atomBlockDet atom 1 3 5)
      (atomBlockDet atom 2 3 5) (atomBlockDet atom 3 4 5)
    + atomFourFlatnessTerm (atomBlockDet atom 0 4 5) (atomBlockDet atom 1 4 5)
      (atomBlockDet atom 2 4 5) (atomBlockDet atom 3 4 5)

theorem atomPluckerSpread_nonneg (atom : Fin 6 → (Fin 3 → ℝ)) :
    0 ≤ atomPluckerSpread atom := by
  simp only [atomPluckerSpread, atomFourFlatnessTerm]
  positivity

/-- **THE FLATNESS IDENTITY.**  The distance between twelve times the level-three
energy and the level-two energy is EXACTLY the spread of the determinantal
measure.  The unifying hypothesis of the campaign, that the theorem holds
because a real Plücker vector cannot be flat, is this identity: the twelve is
what a FLAT measure costs, and every departure from flatness is paid back in
full. -/
theorem atomPluckerFlatnessGap_eq_spread
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    12 * atomPluckerEnergyThree atom - atomPluckerEnergyTwo atom
      = atomPluckerSpread atom := by
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
    atomPairFamilySum, atomPluckerSpread, atomFourFlatnessTerm]
  linear_combination (atomBlockPairMinor atom 0 1
      + (atomBlockDet atom 0 1 2 + atomBlockDet atom 0 1 3 + atomBlockDet atom 0 1 4
        + atomBlockDet atom 0 1 5)) * h01
    + (atomBlockPairMinor atom 0 2
      + (atomBlockDet atom 0 1 2 + atomBlockDet atom 0 2 3 + atomBlockDet atom 0 2 4
        + atomBlockDet atom 0 2 5)) * h02
    + (atomBlockPairMinor atom 0 3
      + (atomBlockDet atom 0 1 3 + atomBlockDet atom 0 2 3 + atomBlockDet atom 0 3 4
        + atomBlockDet atom 0 3 5)) * h03
    + (atomBlockPairMinor atom 0 4
      + (atomBlockDet atom 0 1 4 + atomBlockDet atom 0 2 4 + atomBlockDet atom 0 3 4
        + atomBlockDet atom 0 4 5)) * h04
    + (atomBlockPairMinor atom 0 5
      + (atomBlockDet atom 0 1 5 + atomBlockDet atom 0 2 5 + atomBlockDet atom 0 3 5
        + atomBlockDet atom 0 4 5)) * h05
    + (atomBlockPairMinor atom 1 2
      + (atomBlockDet atom 0 1 2 + atomBlockDet atom 1 2 3 + atomBlockDet atom 1 2 4
        + atomBlockDet atom 1 2 5)) * h12
    + (atomBlockPairMinor atom 1 3
      + (atomBlockDet atom 0 1 3 + atomBlockDet atom 1 2 3 + atomBlockDet atom 1 3 4
        + atomBlockDet atom 1 3 5)) * h13
    + (atomBlockPairMinor atom 1 4
      + (atomBlockDet atom 0 1 4 + atomBlockDet atom 1 2 4 + atomBlockDet atom 1 3 4
        + atomBlockDet atom 1 4 5)) * h14
    + (atomBlockPairMinor atom 1 5
      + (atomBlockDet atom 0 1 5 + atomBlockDet atom 1 2 5 + atomBlockDet atom 1 3 5
        + atomBlockDet atom 1 4 5)) * h15
    + (atomBlockPairMinor atom 2 3
      + (atomBlockDet atom 0 2 3 + atomBlockDet atom 1 2 3 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 2 3 5)) * h23
    + (atomBlockPairMinor atom 2 4
      + (atomBlockDet atom 0 2 4 + atomBlockDet atom 1 2 4 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 2 4 5)) * h24
    + (atomBlockPairMinor atom 2 5
      + (atomBlockDet atom 0 2 5 + atomBlockDet atom 1 2 5 + atomBlockDet atom 2 3 5
        + atomBlockDet atom 2 4 5)) * h25
    + (atomBlockPairMinor atom 3 4
      + (atomBlockDet atom 0 3 4 + atomBlockDet atom 1 3 4 + atomBlockDet atom 2 3 4
        + atomBlockDet atom 3 4 5)) * h34
    + (atomBlockPairMinor atom 3 5
      + (atomBlockDet atom 0 3 5 + atomBlockDet atom 1 3 5 + atomBlockDet atom 2 3 5
        + atomBlockDet atom 3 4 5)) * h35
    + (atomBlockPairMinor atom 4 5
      + (atomBlockDet atom 0 4 5 + atomBlockDet atom 1 4 5 + atomBlockDet atom 2 4 5
        + atomBlockDet atom 3 4 5)) * h45

/-- **THE UNCONDITIONAL ENERGY BOUND.**  The level-two energy never passes
twelve times the level-three energy.  The proof is the flatness identity and
the fact that a total of squares is never negative. -/
theorem atomPluckerEnergyTwo_le_twelve
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomPluckerEnergyTwo atom ≤ 12 * atomPluckerEnergyThree atom := by
  have hgap := atomPluckerFlatnessGap_eq_spread hframe
  have hspread := atomPluckerSpread_nonneg atom
  linarith

/-! ## Layer 4 — the energy bound gives a spectral floor -/

/-- The blend floor of a triple whose second minor total stays at or below a
multiple of its determinant.  This is the non-strict form of the landed
`Gtz.atomSupplyTriple_blend_floor`. -/
theorem atomSupplyTriple_blend_floor_le (atom : Fin 6 → (Fin 3 → ℝ))
    {slotOne slotTwo slotThree : Fin 6} {ratio : ℝ}
    (hdet : 0 < atomBlockDet atom slotOne slotTwo slotThree)
    (hsecond : atomBlockSecond atom slotOne slotTwo slotThree
      ≤ ratio * atomBlockDet atom slotOne slotTwo slotThree)
    (weightOne weightTwo weightThree : ℝ) :
    weightOne ^ 2 + weightTwo ^ 2 + weightThree ^ 2
      ≤ ratio * (atomSlotBlend atom slotOne slotTwo slotThree
          weightOne weightTwo weightThree
        ⬝ᵥ atomSlotBlend atom slotOne slotTwo slotThree
          weightOne weightTwo weightThree) := by
  have hwedge := atomBlockDet_mul_le_atomBlockSecond_mul atom slotOne slotTwo slotThree
    weightOne weightTwo weightThree
  have hblendNonneg : 0 ≤ atomSlotBlend atom slotOne slotTwo slotThree
      weightOne weightTwo weightThree
      ⬝ᵥ atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree :=
    atomDot_self_nonneg _
  nlinarith [hwedge, hdet, hsecond, hblendNonneg, sq_nonneg weightOne, sq_nonneg weightTwo,
    sq_nonneg weightThree]

/-- A determinant that carries a strict step against its second minor total is
zero. -/
theorem atomDet_eq_zero_of_step {det second ratio : ℝ} (hdet : 0 ≤ det)
    (heq : ratio * det ^ 2 = det * second) (hstep : 0 < det → ratio * det < second) :
    det = 0 := by
  rcases hdet.lt_or_eq with hpos | hzero
  · exfalso
    have hlt := hstep hpos
    nlinarith [heq, hlt, hpos]
  · exact hzero.symm

/-- **THE ENERGY SELECTION.**  An energy bound at a ratio supplies a triple
whose determinant is positive and whose second minor total stays at or below
that multiple of it.  Where the moment law of the campaign averages the twenty
blocks FLATLY and cannot pass twelve, this averages them against the
determinantal measure. -/
theorem exists_atomEnergyTriple
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {ratio : ℝ}
    (hbound : atomPluckerEnergyTwo atom ≤ ratio * atomPluckerEnergyThree atom) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 < atomBlockDet atom slotOne slotTwo slotThree
        ∧ atomBlockSecond atom slotOne slotTwo slotThree
            ≤ ratio * atomBlockDet atom slotOne slotTwo slotThree := by
  by_contra hcontra
  push Not at hcontra
  have hmoment := atomBlockDet_mul_second_familySum hframe
  have hmass := atomBlockDet_familySum hframe
  have hstep : ∀ slotOne slotTwo slotThree : Fin 6, slotOne ≠ slotTwo → slotOne ≠ slotThree →
      slotTwo ≠ slotThree →
      ratio * atomBlockDet atom slotOne slotTwo slotThree ^ 2
        ≤ atomBlockDet atom slotOne slotTwo slotThree
          * atomBlockSecond atom slotOne slotTwo slotThree := by
    intro slotOne slotTwo slotThree hone htwo hthree
    rcases (atomBlockDet_nonneg atom slotOne slotTwo slotThree).lt_or_eq with hpos | hzero
    · have := hcontra slotOne slotTwo slotThree hone htwo hthree hpos
      nlinarith [this, hpos]
    · rw [← hzero]
      simp
  have s012 := hstep 0 1 2 (by decide) (by decide) (by decide)
  have s013 := hstep 0 1 3 (by decide) (by decide) (by decide)
  have s014 := hstep 0 1 4 (by decide) (by decide) (by decide)
  have s015 := hstep 0 1 5 (by decide) (by decide) (by decide)
  have s023 := hstep 0 2 3 (by decide) (by decide) (by decide)
  have s024 := hstep 0 2 4 (by decide) (by decide) (by decide)
  have s025 := hstep 0 2 5 (by decide) (by decide) (by decide)
  have s034 := hstep 0 3 4 (by decide) (by decide) (by decide)
  have s035 := hstep 0 3 5 (by decide) (by decide) (by decide)
  have s045 := hstep 0 4 5 (by decide) (by decide) (by decide)
  have s123 := hstep 1 2 3 (by decide) (by decide) (by decide)
  have s124 := hstep 1 2 4 (by decide) (by decide) (by decide)
  have s125 := hstep 1 2 5 (by decide) (by decide) (by decide)
  have s134 := hstep 1 3 4 (by decide) (by decide) (by decide)
  have s135 := hstep 1 3 5 (by decide) (by decide) (by decide)
  have s145 := hstep 1 4 5 (by decide) (by decide) (by decide)
  have s234 := hstep 2 3 4 (by decide) (by decide) (by decide)
  have s235 := hstep 2 3 5 (by decide) (by decide) (by decide)
  have s245 := hstep 2 4 5 (by decide) (by decide) (by decide)
  have s345 := hstep 3 4 5 (by decide) (by decide) (by decide)
  simp only [atomTripleFamilySum] at hmoment hmass
  simp only [atomPluckerEnergyThree, atomTripleFamilySum] at hbound
  rw [← hmoment] at hbound
  have e012 : ratio * atomBlockDet atom 0 1 2 ^ 2
      = atomBlockDet atom 0 1 2 * atomBlockSecond atom 0 1 2 := by linarith
  have e013 : ratio * atomBlockDet atom 0 1 3 ^ 2
      = atomBlockDet atom 0 1 3 * atomBlockSecond atom 0 1 3 := by linarith
  have e014 : ratio * atomBlockDet atom 0 1 4 ^ 2
      = atomBlockDet atom 0 1 4 * atomBlockSecond atom 0 1 4 := by linarith
  have e015 : ratio * atomBlockDet atom 0 1 5 ^ 2
      = atomBlockDet atom 0 1 5 * atomBlockSecond atom 0 1 5 := by linarith
  have e023 : ratio * atomBlockDet atom 0 2 3 ^ 2
      = atomBlockDet atom 0 2 3 * atomBlockSecond atom 0 2 3 := by linarith
  have e024 : ratio * atomBlockDet atom 0 2 4 ^ 2
      = atomBlockDet atom 0 2 4 * atomBlockSecond atom 0 2 4 := by linarith
  have e025 : ratio * atomBlockDet atom 0 2 5 ^ 2
      = atomBlockDet atom 0 2 5 * atomBlockSecond atom 0 2 5 := by linarith
  have e034 : ratio * atomBlockDet atom 0 3 4 ^ 2
      = atomBlockDet atom 0 3 4 * atomBlockSecond atom 0 3 4 := by linarith
  have e035 : ratio * atomBlockDet atom 0 3 5 ^ 2
      = atomBlockDet atom 0 3 5 * atomBlockSecond atom 0 3 5 := by linarith
  have e045 : ratio * atomBlockDet atom 0 4 5 ^ 2
      = atomBlockDet atom 0 4 5 * atomBlockSecond atom 0 4 5 := by linarith
  have e123 : ratio * atomBlockDet atom 1 2 3 ^ 2
      = atomBlockDet atom 1 2 3 * atomBlockSecond atom 1 2 3 := by linarith
  have e124 : ratio * atomBlockDet atom 1 2 4 ^ 2
      = atomBlockDet atom 1 2 4 * atomBlockSecond atom 1 2 4 := by linarith
  have e125 : ratio * atomBlockDet atom 1 2 5 ^ 2
      = atomBlockDet atom 1 2 5 * atomBlockSecond atom 1 2 5 := by linarith
  have e134 : ratio * atomBlockDet atom 1 3 4 ^ 2
      = atomBlockDet atom 1 3 4 * atomBlockSecond atom 1 3 4 := by linarith
  have e135 : ratio * atomBlockDet atom 1 3 5 ^ 2
      = atomBlockDet atom 1 3 5 * atomBlockSecond atom 1 3 5 := by linarith
  have e145 : ratio * atomBlockDet atom 1 4 5 ^ 2
      = atomBlockDet atom 1 4 5 * atomBlockSecond atom 1 4 5 := by linarith
  have e234 : ratio * atomBlockDet atom 2 3 4 ^ 2
      = atomBlockDet atom 2 3 4 * atomBlockSecond atom 2 3 4 := by linarith
  have e235 : ratio * atomBlockDet atom 2 3 5 ^ 2
      = atomBlockDet atom 2 3 5 * atomBlockSecond atom 2 3 5 := by linarith
  have e245 : ratio * atomBlockDet atom 2 4 5 ^ 2
      = atomBlockDet atom 2 4 5 * atomBlockSecond atom 2 4 5 := by linarith
  have e345 : ratio * atomBlockDet atom 3 4 5 ^ 2
      = atomBlockDet atom 3 4 5 * atomBlockSecond atom 3 4 5 := by linarith
  have z012 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 0 1 2) e012
    (hcontra 0 1 2 (by decide) (by decide) (by decide))
  have z013 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 0 1 3) e013
    (hcontra 0 1 3 (by decide) (by decide) (by decide))
  have z014 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 0 1 4) e014
    (hcontra 0 1 4 (by decide) (by decide) (by decide))
  have z015 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 0 1 5) e015
    (hcontra 0 1 5 (by decide) (by decide) (by decide))
  have z023 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 0 2 3) e023
    (hcontra 0 2 3 (by decide) (by decide) (by decide))
  have z024 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 0 2 4) e024
    (hcontra 0 2 4 (by decide) (by decide) (by decide))
  have z025 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 0 2 5) e025
    (hcontra 0 2 5 (by decide) (by decide) (by decide))
  have z034 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 0 3 4) e034
    (hcontra 0 3 4 (by decide) (by decide) (by decide))
  have z035 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 0 3 5) e035
    (hcontra 0 3 5 (by decide) (by decide) (by decide))
  have z045 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 0 4 5) e045
    (hcontra 0 4 5 (by decide) (by decide) (by decide))
  have z123 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 1 2 3) e123
    (hcontra 1 2 3 (by decide) (by decide) (by decide))
  have z124 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 1 2 4) e124
    (hcontra 1 2 4 (by decide) (by decide) (by decide))
  have z125 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 1 2 5) e125
    (hcontra 1 2 5 (by decide) (by decide) (by decide))
  have z134 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 1 3 4) e134
    (hcontra 1 3 4 (by decide) (by decide) (by decide))
  have z135 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 1 3 5) e135
    (hcontra 1 3 5 (by decide) (by decide) (by decide))
  have z145 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 1 4 5) e145
    (hcontra 1 4 5 (by decide) (by decide) (by decide))
  have z234 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 2 3 4) e234
    (hcontra 2 3 4 (by decide) (by decide) (by decide))
  have z235 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 2 3 5) e235
    (hcontra 2 3 5 (by decide) (by decide) (by decide))
  have z245 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 2 4 5) e245
    (hcontra 2 4 5 (by decide) (by decide) (by decide))
  have z345 := atomDet_eq_zero_of_step (atomBlockDet_nonneg atom 3 4 5) e345
    (hcontra 3 4 5 (by decide) (by decide) (by decide))
  rw [z012, z013, z014, z015, z023, z024, z025, z034, z035, z045, z123, z124, z125,
    z134, z135, z145, z234, z235, z245, z345] at hmass
  norm_num at hmass

/-- **THE ENERGY BRIDGE.**  An energy bound at a positive ratio gives the
spectral supply at the reciprocal floor.  Every statement of this module feeds
the cell through this one theorem. -/
theorem atomSpectralSupply_of_energyBound {ratio : ℝ} (hratio : 0 < ratio)
    (hbound : ∀ atom : Fin 6 → (Fin 3 → ℝ),
      (∀ probe direction : Fin 3 → ℝ,
        (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
      atomPluckerEnergyTwo atom ≤ ratio * atomPluckerEnergyThree atom) :
    AtomSpectralSupply (1 / ratio) := by
  intro atom hframe
  obtain ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, hdet, hsecond⟩ :=
    exists_atomEnergyTriple hframe (hbound atom hframe)
  refine ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, ?_⟩
  intro weightOne weightTwo weightThree
  have hstep := atomSupplyTriple_blend_floor_le atom hdet hsecond
    weightOne weightTwo weightThree
  rw [div_mul_eq_mul_div, div_le_iff₀ hratio]
  nlinarith [hstep, hratio]

/-- **THE TWELFTH.**  Every rank-three Parseval frame of six atoms carries a
triple whose block never shortens a probe below one twelfth.  The hypothesis is
the frame law and nothing else.

The previous record needs the floor STRICTLY below one twelfth, and its
concrete form is one thirteenth.  The reason the flat average cannot pass
twelve is that the second minor total of the twenty blocks is `12` and the
determinant total is `1`, and both are universal.  The determinantal average
reaches the boundary, and `Gtz.atomPluckerFlatnessGap_eq_spread` says what is
left: the spread of the twenty triple determinants. -/
theorem atomSpectralSupply_twelfth : AtomSpectralSupply (1 / 12) :=
  atomSpectralSupply_of_energyBound (by norm_num)
    fun _ hframe => atomPluckerEnergyTwo_le_twelve hframe

/-! ## Layer 5 — the residue, named -/

/-- **THE RESIDUE.**  The level-two energy of every REAL rank-three Parseval
frame of six atoms stays at or below TEN times the level-three energy.

This is real-only.  The adversarial value of the ratio over the real frames is
exactly `10`, and it is attained at the icosahedral frame, whose fifteen pair
minors are all `1/5` and whose twenty triple determinants split ten and ten at
`(1 ± 1/√5)/20`.  Over the Hermitian field the adversarial value is `78/7`,
which is larger, so no field-agnostic argument can prove this statement.

`Gtz.atomPluckerFlatnessGap_eq_spread` turns it into a sharp lower bound on the
spread: the residue holds exactly when the spread of the determinantal measure
is at least twice the level-three energy. -/
def AtomPluckerTenth : Prop :=
  ∀ atom : Fin 6 → (Fin 3 → ℝ),
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    atomPluckerEnergyTwo atom ≤ 10 * atomPluckerEnergyThree atom

/-- **THE RESIDUE IS EXACTLY A SPREAD FLOOR.**  The energy statement at ten and
the statement that the spread is at least twice the level-three energy are the
same statement. -/
theorem atomPluckerTenth_iff_spread
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomPluckerEnergyTwo atom ≤ 10 * atomPluckerEnergyThree atom
      ↔ 2 * atomPluckerEnergyThree atom ≤ atomPluckerSpread atom := by
  have hgap := atomPluckerFlatnessGap_eq_spread hframe
  constructor <;> intro h <;> linarith

/-- **THE RESIDUE SPENDS AT ONE TENTH.**  The named real-only residue gives the
spectral supply at one tenth, which is thirty percent past the record. -/
theorem atomSpectralSupply_tenth_of_pluckerTenth (hresidue : AtomPluckerTenth) :
    AtomSpectralSupply (1 / 10) :=
  atomSpectralSupply_of_energyBound (by norm_num) hresidue

/-- **THE RESIDUE CLOSES EVERY SCALE BELOW ONE TENTH.**  The concrete form the
cell consumes. -/
theorem exists_atomCarrier_of_pluckerTenth (hresidue : AtomPluckerTenth)
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hlight : ∀ slot, scale slot ≤ 1 / 10) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  obtain ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, hfloor⟩ :=
    atomSpectralSupply_tenth_of_pluckerTenth hresidue atom hframe
  exact exists_atomCarrier_of_blendFloor atom scale hone htwo hthree hfloor hlight

/-- **THE UNCONDITIONAL CARRIER AT ONE TWELFTH.**  The concrete form of the
record. -/
theorem exists_atomCarrier_twelfth (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hlight : ∀ slot, scale slot ≤ 1 / 12) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  obtain ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, hfloor⟩ :=
    atomSpectralSupply_twelfth atom hframe
  exact exists_atomCarrier_of_blendFloor atom scale hone htwo hthree hfloor hlight

end Gtz
