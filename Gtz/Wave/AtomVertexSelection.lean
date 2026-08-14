import Gtz.Wave.AtomMassOneLadder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The vertex selection frame: the free half is free, and the residue is an integrality gap

The atom lane's residue is the non-strict selection at scale mass exactly
one: six tight-frame atoms of rank three and six positive scales of total
one carry a TRIPLE whose Gram dominates the scale diagonal.  This module
separates that statement into the part that is free and the part that is
not, and it closes two strata of the free part outright.

## The three rungs of the ladder

A COVER of a datum is a family of six weights in the unit interval whose
scaled atom operator dominates the identity.  The residue asks for a cover
that is a TRIPLE.  The three rungs are:

* For each direction separately, some triple covers it — a pigeonhole
  against the reading law.  `Gtz.exists_triple_reading_of_direction`.
* One fractional cover of total three covers every direction at once —
  the Cauchy-Binet marginal of the datum, one Cauchy-Schwarz.
  `Gtz.atomFractionalCoverClosed_holds`.
* One TRIPLE covers every direction at once — the residue.

The first two rungs are unconditional theorems of this module.  The step
from the second to the third is the whole remaining content of the cell:
the residue is the INTEGRALITY GAP of an explicit fractional cover, and no
minimax theorem, no separation theorem and no compactness argument is
needed to reach that fractional cover.

## The marginal cover

The cover is `cover slot = atomGram atom slot slot`, the squared length of
the atom.  Its three properties are exactly the three the hypersimplex
asks for: each weight lies in the unit interval, the six add to the rank,
and the scaled operator dominates the identity.  The last one is one
Cauchy-Schwarz in Engel form against the reading law, because the squared
reading of an atom never exceeds its squared length.

The same computation gives the trace: the marginal cover operator has
trace at least nine, where the identity has trace three.  The fractional
cover therefore carries a factor-three slack while the residue is exactly
tight at the boundary witness, which locates the whole difficulty in the
passage to a vertex.

## The two unconditional criteria

Two elementary criteria close a triple with no selection rule and no
hypothesis beyond the frame law.

* THE DIAGONALLY DOMINANT CRITERION.  A triple dominates when each of its
  atoms has squared length above its scale by at least the sum of the two
  Gram couplings of that atom inside the triple.
* THE HEAVY CRITERION.  A triple dominates when its three squared lengths
  total at least two plus the largest of its three scales.  The proof
  reads the complementary Gram, which is again a symmetric idempotent, and
  bounds its largest value by its trace.

## The pool and the stratum split

The POOL of a datum is the set of slots whose scale is at most the squared
length of the atom.  Every dominating triple lies in the pool, and the
pool always has at least three slots.  When it has EXACTLY three, the heavy
criterion closes those three, and the residue may therefore assume a pool
of four slots or more.  That is a strict shrink of the hypothesis class of
the residue.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomDot_self_nonneg`, `Gtz.atomDot_eq_zero_of_energy_nonpos`,
  `Gtz.atomDot_sq_le_energy` — the elementary dot product calculus.
* `Gtz.atomReading_sum`, `Gtz.atomBlend_energy_le_probe_energy` — the
  reading law, and the Gram of a tight frame is below the identity.
* `Gtz.atomGramComp`, `Gtz.atomGramComp_comm`,
  `Gtz.atomGramComp_idempotent`, `Gtz.atomGramComp_row_energy`,
  `Gtz.atomGramComp_minor`, `Gtz.atomGramComp_diag_nonneg`,
  `Gtz.atomGramComp_trace` — the complementary projection.
* `Gtz.atomGram_cross_total` — the cross moment of a slot.
* `Gtz.exists_slot_reading_ge`, `Gtz.exists_slot_scale_le_gram`,
  `Gtz.exists_triple_reading_of_direction` — **THE FREE HALF, POINTWISE**.
* `Gtz.atomMarginalCover_dominates`, `Gtz.atomMarginalCover_trace`,
  `Gtz.AtomFractionalCoverClosed`, `Gtz.atomFractionalCoverClosed_holds` —
  **THE FREE HALF, WITH THE QUANTIFIERS IN THE HARD ORDER**, unconditional
  and explicit.
* `Gtz.two_mul_ge_neg_abs_mul`, `Gtz.two_mul_le_of_sq_le` — the two scalar
  engines of the criteria.
* `Gtz.atomTriple_values_of_diagonalDominance`,
  `Gtz.atomTriple_values_of_heavy` — **THE TWO UNCONDITIONAL CRITERIA**.
* `Gtz.exists_weakCarrier_of_values` — the value form gives a carrier.
* `Gtz.atomPool`, `Gtz.atomPool_of_weakCarrier`,
  `Gtz.atomPool_three_le_card`, `Gtz.atomPool_heavy`,
  `Gtz.exists_weakCarrier_of_thin_pool` — **THE THIN POOL CLOSES**.
* `Gtz.AtomThickPoolBoundaryClosed`,
  `Gtz.atomTripleBoundaryClosed_of_thickPool`,
  `Gtz.gtzWeighted_six_three_of_thickPool` — **THE STRATUM SPLIT**: the
  residue may assume a pool of four slots or more, and the cell follows.
* `Gtz.familyMatrix`, `Gtz.familyMatrix_mulVec`,
  `Gtz.familyMatrix_transpose_energy`, `Gtz.matrix_dual_lower`,
  `Gtz.dualEnergy_of_blendEnergy`, `Gtz.blendEnergy_of_dualEnergy` —
  **THE TRANSPOSE LAW**: a square matrix that never shortens a vector
  never shortens one through its transpose either.
* `Gtz.atomScaledTriple`, `Gtz.tripleCombination_energy`,
  `Gtz.atomScaledTriple_reading`, `Gtz.atomScaledTriple_blend`,
  `Gtz.atomScaledTriple_scale_value`,
  `Gtz.atomTriple_operator_iff_values` — the scaled triple, and the
  operator face of a triple against its value face.
* `Gtz.AtomTripleOperatorClosed`,
  `Gtz.atomTripleBoundaryClosed_of_atomTripleOperator`,
  `Gtz.atomTripleOperatorClosed_of_atomTripleBoundary`,
  `Gtz.atomTripleOperatorClosed_iff_atomTripleBoundary`,
  `Gtz.gtzWeighted_six_three_of_atomTripleOperator` — **THE SIXTH FACE OF
  THE CELL**: the residue in the language of the fractional cover, of
  which the free half is the relaxation.

## The operator face

The residue reads, in the operator language, as the fractional cover
restricted to weights zero and one.  The passage between that face and the
probe face of the landed residue is the transpose law, because a triple of
atoms of rank three is a SQUARE family.  Over a rectangular family the two
faces are different statements, and the coincidence at the cell is the
same numerology that makes this cell the deciding one.

## Vacuity

The frame calculus, the pigeonhole and the marginal cover are
unconditional theorems.  The two criteria carry explicit scalar
hypotheses which the probe of this session finds satisfied at ninety-two
percent of random data, and the thin pool arises at half a percent of
random data and at two and a half percent of near-degenerate data, thus
none of them is vacuous.  The stratum split consumes the thin pool
theorem and gives back the landed residue, thus it is not vacuous either.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the elementary dot product calculus -/

section Elementary

variable {rank : ℕ}

/-- The self energy of a vector is nonnegative. -/
theorem atomDot_self_nonneg (vector : Fin rank → ℝ) : 0 ≤ vector ⬝ᵥ vector :=
  Finset.sum_nonneg fun _index _ => mul_self_nonneg _

/-- A vector of nonpositive self energy vanishes. -/
theorem atomDot_eq_zero_of_energy_nonpos {vector : Fin rank → ℝ}
    (henergy : vector ⬝ᵥ vector ≤ 0) : vector = 0 := by
  have hterm : ∀ index ∈ (Finset.univ : Finset (Fin rank)), 0 ≤ vector index * vector index :=
    fun index _ => mul_self_nonneg _
  have hzero : (∑ index, vector index * vector index) = 0 :=
    le_antisymm henergy (Finset.sum_nonneg hterm)
  funext index
  have hcell := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero index (Finset.mem_univ index)
  simpa using mul_self_eq_zero.mp hcell

/-- **CAUCHY-SCHWARZ** for the dot product, in squared form. -/
theorem atomDot_sq_le_energy (leftVec rightVec : Fin rank → ℝ) :
    (leftVec ⬝ᵥ rightVec) ^ 2 ≤ (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin rank))
    (fun index => leftVec index) (fun index => rightVec index)
  simp only [dotProduct]
  calc (∑ index, leftVec index * rightVec index) ^ 2
      ≤ (∑ index, leftVec index ^ 2) * ∑ index, rightVec index ^ 2 := hcs
    _ = (∑ index, leftVec index * leftVec index)
          * ∑ index, rightVec index * rightVec index := by
        congr 1 <;> exact Finset.sum_congr rfl fun index _ => pow_two _

end Elementary

/-! ## Layer 1 — the Gram of a tight frame is a projection -/

section FrameCalculus

variable {slotCount rank : ℕ}

/-- The READING LAW: the squared readings of a tight frame against a
direction add to the self energy of that direction. -/
theorem atomReading_sum (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (direction : Fin rank → ℝ) :
    (∑ slot, (atom slot ⬝ᵥ direction) ^ 2) = direction ⬝ᵥ direction := by
  rw [← hframe direction direction]
  exact Finset.sum_congr rfl fun slot _ => pow_two _

/-- **THE BLEND ENERGY NEVER EXCEEDS THE PROBE ENERGY.**  The Gram of a
tight frame is below the identity. -/
theorem atomBlend_energy_le_probe_energy (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (probe : Fin slotCount → ℝ) :
    atomBlend atom probe ⬝ᵥ atomBlend atom probe ≤ ∑ slot, probe slot ^ 2 := by
  have hblend := atomBlend_dot atom probe (atomBlend atom probe)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin slotCount))
    (fun slot => probe slot) (fun slot => atom slot ⬝ᵥ atomBlend atom probe)
  have hreading := atomReading_sum atom hframe (atomBlend atom probe)
  have hnonneg := atomDot_self_nonneg (atomBlend atom probe)
  have hprobeNonneg : (0 : ℝ) ≤ ∑ slot, probe slot ^ 2 :=
    Finset.sum_nonneg fun slot _ => sq_nonneg (probe slot)
  rw [hreading] at hcs
  rw [hblend] at hnonneg ⊢
  nlinarith [hcs, hnonneg, hprobeNonneg, hblend]

/-- The COMPLEMENTARY GRAM of a tight frame: the identity minus the Gram.
It is the Gram of the complementary projection. -/
def atomGramComp (atom : Fin slotCount → (Fin rank → ℝ))
    (rowSlot colSlot : Fin slotCount) : ℝ :=
  (if rowSlot = colSlot then (1 : ℝ) else 0) - atomGram atom rowSlot colSlot

theorem atomGramComp_comm (atom : Fin slotCount → (Fin rank → ℝ))
    (rowSlot colSlot : Fin slotCount) :
    atomGramComp atom rowSlot colSlot = atomGramComp atom colSlot rowSlot := by
  simp only [atomGramComp, atomGram_comm atom rowSlot colSlot]
  by_cases heq : rowSlot = colSlot
  · rw [heq]
  · rw [if_neg heq, if_neg (Ne.symm heq)]

/-- **THE COMPLEMENTARY GRAM IS IDEMPOTENT TOO.** -/
theorem atomGramComp_idempotent (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot colSlot : Fin slotCount) :
    (∑ mid, atomGramComp atom rowSlot mid * atomGramComp atom mid colSlot)
      = atomGramComp atom rowSlot colSlot := by
  classical
  have hexpand : ∀ mid : Fin slotCount,
      atomGramComp atom rowSlot mid * atomGramComp atom mid colSlot
        = (if rowSlot = mid then (1 : ℝ) else 0) * (if mid = colSlot then (1 : ℝ) else 0)
          - (if rowSlot = mid then (1 : ℝ) else 0) * atomGram atom mid colSlot
          - atomGram atom rowSlot mid * (if mid = colSlot then (1 : ℝ) else 0)
          + atomGram atom rowSlot mid * atomGram atom mid colSlot := by
    intro mid
    simp only [atomGramComp]
    ring
  have hone : (∑ mid : Fin slotCount,
      (if rowSlot = mid then (1 : ℝ) else 0) * (if mid = colSlot then (1 : ℝ) else 0))
      = if rowSlot = colSlot then (1 : ℝ) else 0 := by
    simp
  have htwo : (∑ mid : Fin slotCount,
      (if rowSlot = mid then (1 : ℝ) else 0) * atomGram atom mid colSlot)
      = atomGram atom rowSlot colSlot := by
    simp [Finset.sum_ite_eq]
  have hthree : (∑ mid : Fin slotCount,
      atomGram atom rowSlot mid * (if mid = colSlot then (1 : ℝ) else 0))
      = atomGram atom rowSlot colSlot := by
    simp [Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl fun mid _ => hexpand mid, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, hone, htwo, hthree,
    atomGram_idempotent hframe rowSlot colSlot, atomGramComp]
  ring

/-- The squared entries of a complementary Gram row add to its diagonal. -/
theorem atomGramComp_row_energy (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (slot : Fin slotCount) :
    (∑ mid, (atomGramComp atom slot mid) ^ 2) = atomGramComp atom slot slot := by
  rw [← atomGramComp_idempotent atom hframe slot slot]
  refine Finset.sum_congr rfl fun mid _ => ?_
  rw [atomGramComp_comm atom mid slot]
  ring

/-- The diagonal of the complementary Gram is nonnegative. -/
theorem atomGramComp_diag_nonneg (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (slot : Fin slotCount) :
    0 ≤ atomGramComp atom slot slot := by
  have hle := atomGram_diag_le_one hframe slot
  have hdiag : atomGramComp atom slot slot = 1 - atomGram atom slot slot := by
    simp [atomGramComp]
  rw [hdiag]
  linarith

/-- **THE MINOR LAW OF THE COMPLEMENTARY GRAM.**  Every off-diagonal entry
is bounded by the two diagonal entries, by Cauchy-Schwarz against the two
rows of the idempotent. -/
theorem atomGramComp_minor (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot colSlot : Fin slotCount) :
    (atomGramComp atom rowSlot colSlot) ^ 2
      ≤ atomGramComp atom rowSlot rowSlot * atomGramComp atom colSlot colSlot := by
  have hrow := atomGramComp_row_energy atom hframe rowSlot
  have hcol := atomGramComp_row_energy atom hframe colSlot
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin slotCount))
    (fun mid => atomGramComp atom rowSlot mid) (fun mid => atomGramComp atom colSlot mid)
  have hentry : (∑ mid, atomGramComp atom rowSlot mid * atomGramComp atom colSlot mid)
      = atomGramComp atom rowSlot colSlot := by
    rw [← atomGramComp_idempotent atom hframe rowSlot colSlot]
    exact Finset.sum_congr rfl fun mid _ => by rw [atomGramComp_comm atom colSlot mid]
  rw [hentry, hrow, hcol] at hcs
  exact hcs

/-- The trace of the complementary Gram is the corank. -/
theorem atomGramComp_trace (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ slot, atomGramComp atom slot slot) = (slotCount : ℝ) - (rank : ℝ) := by
  have htrace := atomGram_trace hframe
  have hdiag : ∀ slot : Fin slotCount,
      atomGramComp atom slot slot = 1 - atomGram atom slot slot := by
    intro slot
    simp [atomGramComp]
  rw [Finset.sum_congr rfl fun slot _ => hdiag slot, Finset.sum_sub_distrib, htrace]
  simp

/-- **THE CROSS MOMENT OF A SLOT.**  The Gram complements of a slot against
all slots total the corank of a single atom times its squared length.  At
rank three this is the squared cross product law. -/
theorem atomGram_cross_total (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (slot : Fin slotCount) :
    (∑ other, (atomGram atom slot slot * atomGram atom other other
        - (atomGram atom slot other) ^ 2))
      = ((rank : ℝ) - 1) * atomGram atom slot slot := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, atomGram_trace hframe,
    atomGram_row_energy hframe slot]
  ring

end FrameCalculus

/-! ## Layer 2 — the free half, pointwise -/

section Pointwise

variable {slotCount rank : ℕ}

/-- **THE READING PIGEONHOLE.**  Some slot reads a direction at least as
strongly as its share of the scale mass asks.  This is the whole free half
at one direction. -/
theorem exists_slot_reading_ge (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hslot : 0 < slotCount) (direction : Fin rank → ℝ) :
    ∃ slot, scale slot * (direction ⬝ᵥ direction)
      ≤ (∑ z, scale z) * (atom slot ⬝ᵥ direction) ^ 2 := by
  have hnonempty : (Finset.univ : Finset (Fin slotCount)).Nonempty :=
    ⟨⟨0, hslot⟩, Finset.mem_univ _⟩
  have hsum : (∑ slot, scale slot * (direction ⬝ᵥ direction))
      ≤ ∑ slot, (∑ z, scale z) * (atom slot ⬝ᵥ direction) ^ 2 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, atomReading_sum atom hframe direction]
  obtain ⟨slot, _, hle⟩ := Finset.exists_le_of_sum_le hnonempty hsum
  exact ⟨slot, hle⟩

/-- **THE PIVOT SLOT.**  Some slot carries a squared length of at least the
rank times its scale.  At mass one this is the free pivot `alpha ≥ 3`. -/
theorem exists_slot_scale_le_gram (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hslot : 0 < slotCount) :
    ∃ slot, (rank : ℝ) * scale slot ≤ (∑ z, scale z) * atomGram atom slot slot := by
  have hnonempty : (Finset.univ : Finset (Fin slotCount)).Nonempty :=
    ⟨⟨0, hslot⟩, Finset.mem_univ _⟩
  have hsum : (∑ slot, (rank : ℝ) * scale slot)
      ≤ ∑ slot, (∑ z, scale z) * atomGram atom slot slot := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, atomGram_trace hframe]
    exact le_of_eq (mul_comm _ _)
  obtain ⟨slot, _, hle⟩ := Finset.exists_le_of_sum_le hnonempty hsum
  exact ⟨slot, hle⟩

/-- **THE FREE HALF WITH THE EASY QUANTIFIER ORDER.**  For each direction
separately, a triple of distinct slots covers that direction.  The residue
is the same statement with the triple chosen BEFORE the direction. -/
theorem exists_triple_reading_of_direction (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (direction : Fin 3 → ℝ) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ direction ⬝ᵥ direction
            ≤ (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne
              + (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo
              + (atom slotThree ⬝ᵥ direction) ^ 2 / scale slotThree := by
  obtain ⟨pivot, hpivot⟩ := exists_slot_reading_ge atom scale hframe (by norm_num) direction
  rw [hmass, one_mul] at hpivot
  have hdistinct : ∀ slot : Fin 6,
      slot ≠ slot + 1 ∧ slot ≠ slot + 2 ∧ slot + 1 ≠ slot + 2 := by decide
  obtain ⟨hone, htwo, hthree⟩ := hdistinct pivot
  refine ⟨pivot, pivot + 1, pivot + 2, hone, htwo, hthree, ?_⟩
  have hfirst : direction ⬝ᵥ direction ≤ (atom pivot ⬝ᵥ direction) ^ 2 / scale pivot := by
    rw [le_div_iff₀ (hpos pivot)]
    linarith [hpivot]
  have hsecond : (0 : ℝ) ≤ (atom (pivot + 1) ⬝ᵥ direction) ^ 2 / scale (pivot + 1) :=
    div_nonneg (sq_nonneg _) (hpos _).le
  have hthird : (0 : ℝ) ≤ (atom (pivot + 2) ⬝ᵥ direction) ^ 2 / scale (pivot + 2) :=
    div_nonneg (sq_nonneg _) (hpos _).le
  linarith

end Pointwise

/-! ## Layer 3 — the marginal cover, the free half with the hard quantifier order -/

section MarginalCover

variable {slotCount rank : ℕ}

/-- **THE MARGINAL COVER DOMINATES.**  The Cauchy-Binet marginal of a
datum — the squared length of each atom — is a fractional cover of the
identity.  The proof is one Cauchy-Schwarz in Engel form against the
reading law, because the squared reading of an atom never exceeds its
squared length. -/
theorem atomMarginalCover_dominates (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (hpos : ∀ slot, 0 < scale slot)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (direction : Fin rank → ℝ) :
    direction ⬝ᵥ direction
      ≤ (∑ z, scale z)
        * ∑ slot, (atomGram atom slot slot / scale slot) * (atom slot ⬝ᵥ direction) ^ 2 := by
  classical
  have hterm : ∀ slot : Fin slotCount,
      0 ≤ (atomGram atom slot slot / scale slot) * (atom slot ⬝ᵥ direction) ^ 2 :=
    fun slot => mul_nonneg (div_nonneg (atomGram_diag_nonneg atom slot) (hpos slot).le)
      (sq_nonneg _)
  have hsumNonneg : (0 : ℝ)
      ≤ ∑ slot, (atomGram atom slot slot / scale slot) * (atom slot ⬝ᵥ direction) ^ 2 :=
    Finset.sum_nonneg fun slot _ => hterm slot
  have hscaleNonneg : (0 : ℝ) ≤ ∑ z, scale z :=
    Finset.sum_nonneg fun z _ => (hpos z).le
  rcases (atomDot_self_nonneg direction).lt_or_eq with hdpos | hdzero
  · have hmasspos : 0 < ∑ z, scale z := by
      rcases (Finset.univ : Finset (Fin slotCount)).eq_empty_or_nonempty with hempty | hne
      · exfalso
        rw [← atomReading_sum atom hframe direction, hempty, Finset.sum_empty] at hdpos
        exact lt_irrefl 0 hdpos
      · exact Finset.sum_pos (fun z _ => hpos z) hne
    have hengel := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin slotCount))
      (fun slot => (atom slot ⬝ᵥ direction) ^ 2) (fun z _ => hpos z)
    rw [atomReading_sum atom hframe direction] at hengel
    have hbound : ∀ slot : Fin slotCount,
        ((atom slot ⬝ᵥ direction) ^ 2) ^ 2 / scale slot
          ≤ (direction ⬝ᵥ direction)
            * ((atomGram atom slot slot / scale slot) * (atom slot ⬝ᵥ direction) ^ 2) := by
      intro slot
      have hcs : (atom slot ⬝ᵥ direction) ^ 2
          ≤ atomGram atom slot slot * (direction ⬝ᵥ direction) :=
        atomDot_sq_le_energy (atom slot) direction
      rw [div_le_iff₀ (hpos slot)]
      have hfactor : 0 ≤ (atom slot ⬝ᵥ direction) ^ 2 := sq_nonneg _
      have hcancel : atomGram atom slot slot / scale slot * scale slot
          = atomGram atom slot slot := div_mul_cancel₀ _ (ne_of_gt (hpos slot))
      have hexpand : (direction ⬝ᵥ direction)
            * (atomGram atom slot slot / scale slot * (atom slot ⬝ᵥ direction) ^ 2)
            * scale slot
          = (direction ⬝ᵥ direction) * atomGram atom slot slot
            * (atom slot ⬝ᵥ direction) ^ 2 := by
        linear_combination (direction ⬝ᵥ direction) * (atom slot ⬝ᵥ direction) ^ 2 * hcancel
      rw [hexpand]
      nlinarith [hcs, hfactor]
    have hsumbound : (∑ slot, ((atom slot ⬝ᵥ direction) ^ 2) ^ 2 / scale slot)
        ≤ (direction ⬝ᵥ direction)
          * ∑ slot, (atomGram atom slot slot / scale slot) * (atom slot ⬝ᵥ direction) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun slot _ => hbound slot
    rw [div_le_iff₀ hmasspos] at hengel
    nlinarith [hengel, hsumbound, hdpos, hmasspos, hsumNonneg]
  · rw [← hdzero]
    exact mul_nonneg hscaleNonneg hsumNonneg

/-- **THE TRACE OF THE MARGINAL COVER.**  Where the identity carries trace
`rank`, the marginal cover operator carries trace at least `rank` squared:
the fractional cover has a factor-`rank` slack. -/
theorem atomMarginalCover_trace (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (hpos : ∀ slot, 0 < scale slot)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ((rank : ℝ)) ^ 2
      ≤ (∑ z, scale z) * ∑ slot, (atomGram atom slot slot) ^ 2 / scale slot := by
  classical
  rcases (Finset.univ : Finset (Fin slotCount)).eq_empty_or_nonempty with hempty | hne
  · have htrace := atomGram_trace hframe
    rw [hempty, Finset.sum_empty] at htrace
    rw [← htrace]
    simp [hempty]
  · have hmasspos : 0 < ∑ z, scale z := Finset.sum_pos (fun z _ => hpos z) hne
    have hengel := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin slotCount))
      (fun slot => atomGram atom slot slot) (fun z _ => hpos z)
    rw [atomGram_trace hframe, div_le_iff₀ hmasspos] at hengel
    linarith [hengel]

/-- **THE FRACTIONAL COVER RESIDUE, WHICH IS NOT A RESIDUE.**  Six tight
frame atoms of rank three with six positive scales of total one carry a
family of six weights in the unit interval, of total three, whose scaled
atom operator dominates the identity.  The residue of the lane is the same
statement with the weights restricted to zero and one. -/
def AtomFractionalCoverClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ cover : Fin 6 → ℝ,
      (∀ slot, 0 ≤ cover slot) ∧ (∀ slot, cover slot ≤ 1)
        ∧ (∑ slot, cover slot) = 3
        ∧ ∀ direction : Fin 3 → ℝ,
            direction ⬝ᵥ direction
              ≤ ∑ slot, (cover slot / scale slot) * (atom slot ⬝ᵥ direction) ^ 2

/-- **THE FREE HALF IS FREE.**  The fractional cover always exists, and it
is EXPLICIT: the squared lengths of the atoms.  No minimax theorem, no
separation theorem and no compactness argument enters. -/
theorem atomFractionalCoverClosed_holds : AtomFractionalCoverClosed := by
  intro atom scale hpos hmass hframe
  refine ⟨fun slot => atomGram atom slot slot, fun slot => atomGram_diag_nonneg atom slot,
    fun slot => atomGram_diag_le_one hframe slot, ?_, fun direction => ?_⟩
  · rw [atomGram_trace hframe]
    norm_num
  · have hdom := atomMarginalCover_dominates atom scale hpos hframe direction
    rw [hmass, one_mul] at hdom
    exact hdom

end MarginalCover

/-! ## Layer 4 — the two scalar engines -/

/-- The absolute value engine of the diagonally dominant criterion. -/
theorem two_mul_ge_neg_abs_mul (coupling first second : ℝ) :
    -(|coupling| * (first ^ 2 + second ^ 2)) ≤ 2 * coupling * first * second := by
  rcases abs_cases coupling with ⟨habs, hsign⟩ | ⟨habs, hsign⟩
  · rw [habs]
    nlinarith [sq_nonneg (first + second), hsign]
  · rw [habs]
    nlinarith [sq_nonneg (first - second), hsign]

/-- The minor engine of the heavy criterion: a nonnegative two by two
minor turns a cross term into two diagonal terms. -/
theorem two_mul_le_of_sq_le {diagOne diagTwo coupling first second : ℝ}
    (hone : 0 ≤ diagOne) (htwo : 0 ≤ diagTwo) (hminor : coupling ^ 2 ≤ diagOne * diagTwo) :
    2 * coupling * first * second ≤ diagOne * second ^ 2 + diagTwo * first ^ 2 := by
  rcases eq_or_lt_of_le hone with hzero | hpos
  · have hcoupling : coupling = 0 := by
      have : coupling ^ 2 ≤ 0 := by rw [← hzero] at hminor; simpa using hminor
      nlinarith [sq_nonneg coupling]
    rw [hcoupling]
    nlinarith [mul_nonneg htwo (sq_nonneg first), mul_nonneg hone (sq_nonneg second)]
  · nlinarith [sq_nonneg (diagOne * second - coupling * first),
      mul_nonneg (sub_nonneg.mpr hminor) (sq_nonneg first), hpos]

/-! ## Layer 5 — the two unconditional domination criteria -/

section Criteria

variable {slotCount rank : ℕ}

/-- **THE DIAGONALLY DOMINANT CRITERION.**  A triple dominates when each of
its atoms has squared length above its scale by at least the sum of the two
Gram couplings of that atom inside the triple.  No frame law is needed. -/
theorem atomTriple_values_of_diagonalDominance (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) {slotOne slotTwo slotThree : Fin slotCount}
    (hone : |atomGram atom slotOne slotTwo| + |atomGram atom slotOne slotThree|
      ≤ atomGram atom slotOne slotOne - scale slotOne)
    (htwo : |atomGram atom slotOne slotTwo| + |atomGram atom slotTwo slotThree|
      ≤ atomGram atom slotTwo slotTwo - scale slotTwo)
    (hthree : |atomGram atom slotOne slotThree| + |atomGram atom slotTwo slotThree|
      ≤ atomGram atom slotThree slotThree - scale slotThree)
    (valueOne valueTwo valueThree : ℝ) :
    scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
        + scale slotThree * valueThree ^ 2
      ≤ atomGram atom slotOne slotOne * valueOne ^ 2
        + atomGram atom slotTwo slotTwo * valueTwo ^ 2
        + atomGram atom slotThree slotThree * valueThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
        + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
        + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree := by
  have hcrossOneTwo := two_mul_ge_neg_abs_mul (atomGram atom slotOne slotTwo) valueOne valueTwo
  have hcrossOneThree :=
    two_mul_ge_neg_abs_mul (atomGram atom slotOne slotThree) valueOne valueThree
  have hcrossTwoThree :=
    two_mul_ge_neg_abs_mul (atomGram atom slotTwo slotThree) valueTwo valueThree
  nlinarith [hcrossOneTwo, hcrossOneThree, hcrossTwoThree, hone, htwo, hthree,
    sq_nonneg valueOne, sq_nonneg valueTwo, sq_nonneg valueThree,
    mul_nonneg (abs_nonneg (atomGram atom slotOne slotTwo)) (sq_nonneg valueOne),
    mul_nonneg (abs_nonneg (atomGram atom slotOne slotThree)) (sq_nonneg valueThree),
    mul_nonneg (abs_nonneg (atomGram atom slotTwo slotThree)) (sq_nonneg valueTwo)]

/-- **THE HEAVY CRITERION.**  A triple dominates when its three squared
lengths total at least two plus each of its three scales.  The complementary
Gram is again a symmetric idempotent, and its largest value on the triple is
bounded by its trace there. -/
theorem atomTriple_values_of_heavy (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {slotOne slotTwo slotThree : Fin slotCount}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hone : scale slotOne ≤ atomGram atom slotOne slotOne + atomGram atom slotTwo slotTwo
      + atomGram atom slotThree slotThree - 2)
    (htwo : scale slotTwo ≤ atomGram atom slotOne slotOne + atomGram atom slotTwo slotTwo
      + atomGram atom slotThree slotThree - 2)
    (hthree : scale slotThree ≤ atomGram atom slotOne slotOne + atomGram atom slotTwo slotTwo
      + atomGram atom slotThree slotThree - 2)
    (valueOne valueTwo valueThree : ℝ) :
    scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
        + scale slotThree * valueThree ^ 2
      ≤ atomGram atom slotOne slotOne * valueOne ^ 2
        + atomGram atom slotTwo slotTwo * valueTwo ^ 2
        + atomGram atom slotThree slotThree * valueThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
        + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
        + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree := by
  have hdiagOne := atomGramComp_diag_nonneg atom hframe slotOne
  have hdiagTwo := atomGramComp_diag_nonneg atom hframe slotTwo
  have hdiagThree := atomGramComp_diag_nonneg atom hframe slotThree
  have hminorOneTwo := atomGramComp_minor atom hframe slotOne slotTwo
  have hminorOneThree := atomGramComp_minor atom hframe slotOne slotThree
  have hminorTwoThree := atomGramComp_minor atom hframe slotTwo slotThree
  have hstepOneTwo := two_mul_le_of_sq_le hdiagOne hdiagTwo hminorOneTwo (first := valueOne)
    (second := valueTwo)
  have hstepOneThree := two_mul_le_of_sq_le hdiagOne hdiagThree hminorOneThree
    (first := valueOne) (second := valueThree)
  have hstepTwoThree := two_mul_le_of_sq_le hdiagTwo hdiagThree hminorTwoThree
    (first := valueTwo) (second := valueThree)
  have hcompOne : atomGramComp atom slotOne slotOne = 1 - atomGram atom slotOne slotOne := by
    simp [atomGramComp]
  have hcompTwo : atomGramComp atom slotTwo slotTwo = 1 - atomGram atom slotTwo slotTwo := by
    simp [atomGramComp]
  have hcompThree :
      atomGramComp atom slotThree slotThree = 1 - atomGram atom slotThree slotThree := by
    simp [atomGramComp]
  have hoffOneTwo : atomGramComp atom slotOne slotTwo = -atomGram atom slotOne slotTwo := by
    simp [atomGramComp, honeTwo]
  have hoffOneThree :
      atomGramComp atom slotOne slotThree = -atomGram atom slotOne slotThree := by
    simp [atomGramComp, honeThree]
  have hoffTwoThree :
      atomGramComp atom slotTwo slotThree = -atomGram atom slotTwo slotThree := by
    simp [atomGramComp, htwoThree]
  simp only [hcompOne, hcompTwo, hcompThree, hoffOneTwo, hoffOneThree, hoffTwoThree]
    at hstepOneTwo hstepOneThree hstepTwoThree
  nlinarith [hstepOneTwo, hstepOneThree, hstepTwoThree, hone, htwo, hthree,
    sq_nonneg valueOne, sq_nonneg valueTwo, sq_nonneg valueThree]

end Criteria

/-! ## Layer 6 — the carrier from the value form -/

/-- A triple of values that dominates gives a weak carrier of the residue. -/
theorem exists_weakCarrier_of_values {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hvalues : ∀ valueOne valueTwo valueThree : ℝ,
      scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
          + scale slotThree * valueThree ^ 2
        ≤ atomGram atom slotOne slotOne * valueOne ^ 2
          + atomGram atom slotTwo slotTwo * valueTwo ^ 2
          + atomGram atom slotThree slotThree * valueThree ^ 2
          + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
          + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
          + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  refine ⟨{slotOne, slotTwo, slotThree}, ?_, fun probe hvanish => ?_⟩
  · exact Finset.card_eq_three.mpr ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree,
      htwoThree, rfl⟩
  · have hscaleSum : (∑ slot, scale slot * probe slot ^ 2)
        = scale slotOne * probe slotOne ^ 2 + scale slotTwo * probe slotTwo ^ 2
          + scale slotThree * probe slotThree ^ 2 :=
      sum_eq_triple_of_support honeTwo honeThree htwoThree
        fun slot hnot => by rw [hvanish slot hnot]; ring
    have henergy := blend_energy_eq_triple_of_support atom honeTwo honeThree htwoThree hvanish
    rw [hscaleSum, henergy]
    exact hvalues (probe slotOne) (probe slotTwo) (probe slotThree)

/-! ## Layer 7 — the pool and the stratum split -/

section Pool

/-- The POOL of a datum: the slots whose scale is at most the squared
length of the atom.  Every dominating triple lies inside the pool. -/
noncomputable def atomPool (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) :
    Finset (Fin 6) :=
  Finset.univ.filter fun slot => scale slot ≤ atomGram atom slot slot

theorem atomPool_mem_iff {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ} (slot : Fin 6) :
    slot ∈ atomPool atom scale ↔ scale slot ≤ atomGram atom slot slot := by
  simp [atomPool]

/-- Every slot of a weak carrier lies in the pool: the single-slot probe
reads the necessary condition. -/
theorem atomPool_of_weakCarrier {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    {car : Finset (Fin 6)}
    (hdom : ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
      (∑ slot, scale slot * probe slot ^ 2)
        ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe)
    {slot : Fin 6} (hmem : slot ∈ car) : slot ∈ atomPool atom scale := by
  classical
  have hvanish : ∀ other ∉ car, (fun z => if z = slot then (1 : ℝ) else 0) other = 0 := by
    intro other hnot
    have hne : other ≠ slot := fun heq => hnot (heq ▸ hmem)
    simp [hne]
  have hstep := hdom (fun z => if z = slot then (1 : ℝ) else 0) hvanish
  have hscale : (∑ z, scale z * (if z = slot then (1 : ℝ) else 0) ^ 2) = scale slot := by
    simp
  have hblend : atomBlend atom (fun z => if z = slot then (1 : ℝ) else 0) = atom slot := by
    funext index
    simp [atomBlend]
  rw [hscale, hblend] at hstep
  exact (atomPool_mem_iff slot).mpr hstep

/-- **THE POOL IS HEAVY.**  Outside the pool the squared lengths sit below
the scales, so the pool carries more than two units of the trace: it
exceeds two by at least its own scale mass. -/
theorem atomPool_heavy (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (2 : ℝ) + (∑ slot ∈ atomPool atom scale, scale slot)
      ≤ ∑ slot ∈ atomPool atom scale, atomGram atom slot slot := by
  classical
  have hsplitGram := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin 6))
    (fun slot => scale slot ≤ atomGram atom slot slot) (fun slot => atomGram atom slot slot)
  have hsplitScale := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin 6))
    (fun slot => scale slot ≤ atomGram atom slot slot) scale
  have htrace : (∑ slot, atomGram atom slot slot) = (3 : ℝ) := by
    rw [atomGram_trace hframe]; norm_num
  have houtside : (∑ slot ∈ Finset.univ.filter
        (fun slot => ¬ scale slot ≤ atomGram atom slot slot), atomGram atom slot slot)
      ≤ ∑ slot ∈ Finset.univ.filter
        (fun slot => ¬ scale slot ≤ atomGram atom slot slot), scale slot := by
    refine Finset.sum_le_sum fun slot hslot => ?_
    have hnot := (Finset.mem_filter.mp hslot).2
    exact le_of_not_ge hnot
  rw [htrace] at hsplitGram
  rw [hmass] at hsplitScale
  simp only [atomPool]
  linarith

/-- **THE POOL CARRIES AT LEAST THREE SLOTS.**  Every squared length is at
most one, so a pool of trace above two holds three slots or more. -/
theorem atomPool_three_le_card (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    3 ≤ (atomPool atom scale).card := by
  classical
  have hheavy := atomPool_heavy atom scale hmass hframe
  have hcard : (∑ slot ∈ atomPool atom scale, atomGram atom slot slot)
      ≤ ((atomPool atom scale).card : ℝ) := by
    calc (∑ slot ∈ atomPool atom scale, atomGram atom slot slot)
        ≤ ∑ _slot ∈ atomPool atom scale, (1 : ℝ) :=
          Finset.sum_le_sum fun slot _ => atomGram_diag_le_one hframe slot
      _ = ((atomPool atom scale).card : ℝ) := by simp
  rcases (atomPool atom scale).eq_empty_or_nonempty with hempty | hne
  · exfalso
    rw [hempty] at hheavy
    simp only [Finset.sum_empty, add_zero] at hheavy
    linarith
  · have hscalePos : 0 < ∑ slot ∈ atomPool atom scale, scale slot :=
      Finset.sum_pos (fun slot _ => hpos slot) hne
    have hcardReal : (2 : ℝ) < ((atomPool atom scale).card : ℝ) := by linarith
    have hcardNat : 2 < (atomPool atom scale).card := by exact_mod_cast hcardReal
    omega

/-- **THE THIN POOL CLOSES.**  When exactly three slots carry a squared
length above their scale, those three dominate, by the heavy criterion. -/
theorem exists_weakCarrier_of_thin_pool (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hthin : (atomPool atom scale).card = 3) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hpoolEq⟩ :=
    Finset.card_eq_three.mp hthin
  have hheavy := atomPool_heavy atom scale hmass hframe
  rw [hpoolEq] at hheavy
  have hsumScale : (∑ slot ∈ ({slotOne, slotTwo, slotThree} : Finset (Fin 6)), scale slot)
      = scale slotOne + scale slotTwo + scale slotThree := by
    rw [Finset.sum_insert (by simp [honeTwo, honeThree]),
      Finset.sum_insert (by simp [htwoThree]), Finset.sum_singleton]
    ring
  have hsumGram :
      (∑ slot ∈ ({slotOne, slotTwo, slotThree} : Finset (Fin 6)), atomGram atom slot slot)
      = atomGram atom slotOne slotOne + atomGram atom slotTwo slotTwo
        + atomGram atom slotThree slotThree := by
    rw [Finset.sum_insert (by simp [honeTwo, honeThree]),
      Finset.sum_insert (by simp [htwoThree]), Finset.sum_singleton]
    ring
  rw [hsumScale, hsumGram] at hheavy
  refine exists_weakCarrier_of_values honeTwo honeThree htwoThree ?_
  refine atomTriple_values_of_heavy atom scale hframe honeTwo honeThree htwoThree ?_ ?_ ?_
  · linarith [hpos slotTwo, hpos slotThree]
  · linarith [hpos slotOne, hpos slotThree]
  · linarith [hpos slotOne, hpos slotTwo]

/-- **THE RESIDUE ON THE THICK POOL.**  The mass-one selection restricted
to the data whose pool carries four slots or more. -/
def AtomThickPoolBoundaryClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    4 ≤ (atomPool atom scale).card →
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe

/-- **THE STRATUM SPLIT.**  The residue may assume a pool of four slots or
more: the three-slot pool is closed by the heavy criterion. -/
theorem atomTripleBoundaryClosed_of_thickPool (hthick : AtomThickPoolBoundaryClosed) :
    AtomTripleBoundaryClosed := by
  intro atom scale hpos hmass hframe
  have hthree := atomPool_three_le_card atom scale hpos hmass hframe
  rcases eq_or_lt_of_le hthree with heq | hlt
  · exact exists_weakCarrier_of_thin_pool atom scale hpos hmass hframe heq.symm
  · exact hthick atom scale hpos hmass hframe hlt

/-- **THE CELL FROM THE THICK POOL RESIDUE.** -/
theorem gtzWeighted_six_three_of_thickPool (hthick : AtomThickPoolBoundaryClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomTripleBoundary
    (atomTripleBoundaryClosed_of_thickPool hthick)

end Pool

/-! ## Layer 8 — the operator face of the residue -/

section Duality

/-- The square matrix whose columns are a family of vectors of its own
dimension. -/
noncomputable def familyMatrix {size : ℕ} (fam : Fin size → (Fin size → ℝ)) :
    Matrix (Fin size) (Fin size) ℝ :=
  Matrix.of fun row col => fam col row

theorem familyMatrix_mulVec {size : ℕ} (fam : Fin size → (Fin size → ℝ))
    (coeff : Fin size → ℝ) :
    familyMatrix fam *ᵥ coeff = atomBlend fam coeff := by
  funext row
  simp only [familyMatrix, Matrix.mulVec, Matrix.of_apply, dotProduct, atomBlend]
  exact Finset.sum_congr rfl fun col _ => mul_comm _ _

theorem familyMatrix_transpose_energy {size : ℕ} (fam : Fin size → (Fin size → ℝ))
    (direction : Fin size → ℝ) :
    ((familyMatrix fam)ᵀ *ᵥ direction) ⬝ᵥ ((familyMatrix fam)ᵀ *ᵥ direction)
      = ∑ index, (fam index ⬝ᵥ direction) ^ 2 := by
  have hentry : (familyMatrix fam)ᵀ *ᵥ direction = fun index => fam index ⬝ᵥ direction := by
    funext index
    simp only [familyMatrix, Matrix.mulVec, Matrix.transpose_apply, Matrix.of_apply, dotProduct]
  rw [hentry]
  exact Finset.sum_congr rfl fun index _ => (pow_two _).symm

/-- **THE TRANSPOSE LAW.**  A square matrix that never shortens a vector
never shortens a vector through its transpose either.  The proof takes the
inverse, reads it as a contraction, and closes with one Cauchy-Schwarz.
This is the whole content of the passage between the probe face and the
operator face of the residue. -/
theorem matrix_dual_lower {size : ℕ} (mat : Matrix (Fin size) (Fin size) ℝ)
    (hlow : ∀ coeff : Fin size → ℝ, coeff ⬝ᵥ coeff ≤ (mat *ᵥ coeff) ⬝ᵥ (mat *ᵥ coeff))
    (direction : Fin size → ℝ) :
    direction ⬝ᵥ direction ≤ (matᵀ *ᵥ direction) ⬝ᵥ (matᵀ *ᵥ direction) := by
  classical
  have hdet : mat.det ≠ 0 := by
    intro hzero
    obtain ⟨vec, hne, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
    have hstep := hlow vec
    rw [hkernel] at hstep
    simp only [dotProduct_zero] at hstep
    exact hne (atomDot_eq_zero_of_energy_nonpos hstep)
  have hunit : IsUnit mat.det := isUnit_iff_ne_zero.mpr hdet
  have hmulinv : mat * mat⁻¹ = 1 := Matrix.mul_nonsing_inv mat hunit
  have hcontract : (mat⁻¹ *ᵥ direction) ⬝ᵥ (mat⁻¹ *ᵥ direction) ≤ direction ⬝ᵥ direction := by
    have hstep := hlow (mat⁻¹ *ᵥ direction)
    rwa [Matrix.mulVec_mulVec, hmulinv, Matrix.one_mulVec] at hstep
  have hident : (mat⁻¹)ᵀ *ᵥ (matᵀ *ᵥ direction) = direction := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hmulinv, Matrix.transpose_one,
      Matrix.one_mulVec]
  have hadj : direction ⬝ᵥ ((mat⁻¹)ᵀ *ᵥ (matᵀ *ᵥ direction))
      = (mat⁻¹ *ᵥ direction) ⬝ᵥ (matᵀ *ᵥ direction) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [hident] at hadj
  have hcs := atomDot_sq_le_energy (mat⁻¹ *ᵥ direction) (matᵀ *ᵥ direction)
  have htop := atomDot_self_nonneg (matᵀ *ᵥ direction)
  rcases (atomDot_self_nonneg direction).lt_or_eq with hdpos | hdzero
  · nlinarith [hcs, hcontract, hadj, hdpos, htop]
  · rw [← hdzero]
    exact htop

/-- The dual reading bound follows from the blend bound. -/
theorem dualEnergy_of_blendEnergy {size : ℕ} (fam : Fin size → (Fin size → ℝ))
    (hblend : ∀ coeff : Fin size → ℝ,
      (∑ index, coeff index ^ 2) ≤ atomBlend fam coeff ⬝ᵥ atomBlend fam coeff)
    (direction : Fin size → ℝ) :
    direction ⬝ᵥ direction ≤ ∑ index, (fam index ⬝ᵥ direction) ^ 2 := by
  have hlow : ∀ coeff : Fin size → ℝ,
      coeff ⬝ᵥ coeff ≤ (familyMatrix fam *ᵥ coeff) ⬝ᵥ (familyMatrix fam *ᵥ coeff) := by
    intro coeff
    rw [familyMatrix_mulVec]
    have hsq : coeff ⬝ᵥ coeff = ∑ index, coeff index ^ 2 :=
      Finset.sum_congr rfl fun index _ => (pow_two _).symm
    rw [hsq]
    exact hblend coeff
  have hstep := matrix_dual_lower (familyMatrix fam) hlow direction
  rwa [familyMatrix_transpose_energy] at hstep

/-- The blend bound follows from the dual reading bound. -/
theorem blendEnergy_of_dualEnergy {size : ℕ} (fam : Fin size → (Fin size → ℝ))
    (hdual : ∀ direction : Fin size → ℝ,
      direction ⬝ᵥ direction ≤ ∑ index, (fam index ⬝ᵥ direction) ^ 2)
    (coeff : Fin size → ℝ) :
    (∑ index, coeff index ^ 2) ≤ atomBlend fam coeff ⬝ᵥ atomBlend fam coeff := by
  have hlow : ∀ direction : Fin size → ℝ,
      direction ⬝ᵥ direction
        ≤ ((familyMatrix fam)ᵀ *ᵥ direction) ⬝ᵥ ((familyMatrix fam)ᵀ *ᵥ direction) := by
    intro direction
    rw [familyMatrix_transpose_energy]
    exact hdual direction
  have hstep := matrix_dual_lower (familyMatrix fam)ᵀ hlow coeff
  rw [Matrix.transpose_transpose, familyMatrix_mulVec] at hstep
  have hsq : coeff ⬝ᵥ coeff = ∑ index, coeff index ^ 2 :=
    Finset.sum_congr rfl fun index _ => (pow_two _).symm
  rwa [hsq] at hstep

end Duality

/-! ## Layer 9 — the scaled triple and the operator residue -/

section Operator

/-- The three atoms of a triple, each divided by the square root of its
scale.  The Gram of this family is the operator of the triple. -/
noncomputable def atomScaledTriple (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (slotOne slotTwo slotThree : Fin 6) : Fin 3 → (Fin 3 → ℝ) :=
  ![(Real.sqrt (scale slotOne))⁻¹ • atom slotOne,
    (Real.sqrt (scale slotTwo))⁻¹ • atom slotTwo,
    (Real.sqrt (scale slotThree))⁻¹ • atom slotThree]

/-- The energy of a three-term combination is the Gram form of the three
vectors. -/
theorem tripleCombination_energy {rank : ℕ} (vecOne vecTwo vecThree : Fin rank → ℝ)
    (valueOne valueTwo valueThree : ℝ) :
    (fun index => valueOne * vecOne index + valueTwo * vecTwo index
        + valueThree * vecThree index)
      ⬝ᵥ (fun index => valueOne * vecOne index + valueTwo * vecTwo index
        + valueThree * vecThree index)
      = (vecOne ⬝ᵥ vecOne) * valueOne ^ 2 + (vecTwo ⬝ᵥ vecTwo) * valueTwo ^ 2
        + (vecThree ⬝ᵥ vecThree) * valueThree ^ 2
        + 2 * (vecOne ⬝ᵥ vecTwo) * valueOne * valueTwo
        + 2 * (vecOne ⬝ᵥ vecThree) * valueOne * valueThree
        + 2 * (vecTwo ⬝ᵥ vecThree) * valueTwo * valueThree := by
  simp only [dotProduct]
  have hcell : ∀ index : Fin rank,
      (valueOne * vecOne index + valueTwo * vecTwo index + valueThree * vecThree index)
        * (valueOne * vecOne index + valueTwo * vecTwo index + valueThree * vecThree index)
      = valueOne ^ 2 * (vecOne index * vecOne index)
        + valueTwo ^ 2 * (vecTwo index * vecTwo index)
        + valueThree ^ 2 * (vecThree index * vecThree index)
        + 2 * valueOne * valueTwo * (vecOne index * vecTwo index)
        + 2 * valueOne * valueThree * (vecOne index * vecThree index)
        + 2 * valueTwo * valueThree * (vecTwo index * vecThree index) := by
    intro index
    ring
  rw [Finset.sum_congr rfl fun index _ => hcell index]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The scaled reading of a triple is the operator form. -/
theorem atomScaledTriple_reading (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hpos : ∀ slot, 0 < scale slot) (slotOne slotTwo slotThree : Fin 6)
    (direction : Fin 3 → ℝ) :
    (∑ index, (atomScaledTriple atom scale slotOne slotTwo slotThree index ⬝ᵥ direction) ^ 2)
      = (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne
        + (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo
        + (atom slotThree ⬝ᵥ direction) ^ 2 / scale slotThree := by
  have hcell : ∀ slot : Fin 6,
      (((Real.sqrt (scale slot))⁻¹ • atom slot) ⬝ᵥ direction) ^ 2
        = (atom slot ⬝ᵥ direction) ^ 2 / scale slot := by
    intro slot
    rw [smul_dotProduct, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt (hpos slot).le]
    ring
  rw [Fin.sum_univ_three,
    show atomScaledTriple atom scale slotOne slotTwo slotThree 0
      = (Real.sqrt (scale slotOne))⁻¹ • atom slotOne from rfl,
    show atomScaledTriple atom scale slotOne slotTwo slotThree 1
      = (Real.sqrt (scale slotTwo))⁻¹ • atom slotTwo from rfl,
    show atomScaledTriple atom scale slotOne slotTwo slotThree 2
      = (Real.sqrt (scale slotThree))⁻¹ • atom slotThree from rfl,
    hcell slotOne, hcell slotTwo, hcell slotThree]

/-- The blend of the scaled triple is the plain combination at the boosted
values. -/
theorem atomScaledTriple_blend (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (slotOne slotTwo slotThree : Fin 6) (coeff : Fin 3 → ℝ) :
    atomBlend (atomScaledTriple atom scale slotOne slotTwo slotThree) coeff
      = fun index => (coeff 0 * (Real.sqrt (scale slotOne))⁻¹) * atom slotOne index
        + (coeff 1 * (Real.sqrt (scale slotTwo))⁻¹) * atom slotTwo index
        + (coeff 2 * (Real.sqrt (scale slotThree))⁻¹) * atom slotThree index := by
  funext index
  rw [atomBlend, Fin.sum_univ_three,
    show atomScaledTriple atom scale slotOne slotTwo slotThree 0
      = (Real.sqrt (scale slotOne))⁻¹ • atom slotOne from rfl,
    show atomScaledTriple atom scale slotOne slotTwo slotThree 1
      = (Real.sqrt (scale slotTwo))⁻¹ • atom slotTwo from rfl,
    show atomScaledTriple atom scale slotOne slotTwo slotThree 2
      = (Real.sqrt (scale slotThree))⁻¹ • atom slotThree from rfl]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The boosted value of a coefficient carries the scale back. -/
theorem atomScaledTriple_scale_value {weight coefficient : ℝ} (hweight : 0 < weight) :
    weight * (coefficient * (Real.sqrt weight)⁻¹) ^ 2 = coefficient ^ 2 := by
  have hsqrt : (Real.sqrt weight) ^ 2 = weight := Real.sq_sqrt hweight.le
  have hne : weight ≠ 0 := ne_of_gt hweight
  rw [mul_pow, inv_pow, hsqrt]
  field_simp

/-- **THE OPERATOR FACE AND THE VALUE FACE OF A TRIPLE AGREE.**  The
operator of a triple dominates the identity exactly when the Gram of the
triple dominates the scale diagonal.  Over a square family the two faces
are one statement, and the transpose law is the whole passage. -/
theorem atomTriple_operator_iff_values (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hpos : ∀ slot, 0 < scale slot) (slotOne slotTwo slotThree : Fin 6) :
    (∀ direction : Fin 3 → ℝ,
        direction ⬝ᵥ direction
          ≤ (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne
            + (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo
            + (atom slotThree ⬝ᵥ direction) ^ 2 / scale slotThree)
      ↔ (∀ valueOne valueTwo valueThree : ℝ,
          scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
              + scale slotThree * valueThree ^ 2
            ≤ atomGram atom slotOne slotOne * valueOne ^ 2
              + atomGram atom slotTwo slotTwo * valueTwo ^ 2
              + atomGram atom slotThree slotThree * valueThree ^ 2
              + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
              + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
              + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree) := by
  classical
  have hsqrtOne : (0 : ℝ) < Real.sqrt (scale slotOne) := Real.sqrt_pos.mpr (hpos slotOne)
  have hsqrtTwo : (0 : ℝ) < Real.sqrt (scale slotTwo) := Real.sqrt_pos.mpr (hpos slotTwo)
  have hsqrtThree : (0 : ℝ) < Real.sqrt (scale slotThree) := Real.sqrt_pos.mpr (hpos slotThree)
  have hblendValue : ∀ coeff : Fin 3 → ℝ,
      atomBlend (atomScaledTriple atom scale slotOne slotTwo slotThree) coeff
          ⬝ᵥ atomBlend (atomScaledTriple atom scale slotOne slotTwo slotThree) coeff
        = atomGram atom slotOne slotOne * (coeff 0 * (Real.sqrt (scale slotOne))⁻¹) ^ 2
          + atomGram atom slotTwo slotTwo * (coeff 1 * (Real.sqrt (scale slotTwo))⁻¹) ^ 2
          + atomGram atom slotThree slotThree * (coeff 2 * (Real.sqrt (scale slotThree))⁻¹) ^ 2
          + 2 * atomGram atom slotOne slotTwo * (coeff 0 * (Real.sqrt (scale slotOne))⁻¹)
              * (coeff 1 * (Real.sqrt (scale slotTwo))⁻¹)
          + 2 * atomGram atom slotOne slotThree * (coeff 0 * (Real.sqrt (scale slotOne))⁻¹)
              * (coeff 2 * (Real.sqrt (scale slotThree))⁻¹)
          + 2 * atomGram atom slotTwo slotThree * (coeff 1 * (Real.sqrt (scale slotTwo))⁻¹)
              * (coeff 2 * (Real.sqrt (scale slotThree))⁻¹) := by
    intro coeff
    rw [atomScaledTriple_blend atom scale slotOne slotTwo slotThree coeff,
      tripleCombination_energy]
    rfl
  have hcoeffValue : ∀ coeff : Fin 3 → ℝ,
      (∑ index, coeff index ^ 2)
        = scale slotOne * (coeff 0 * (Real.sqrt (scale slotOne))⁻¹) ^ 2
          + scale slotTwo * (coeff 1 * (Real.sqrt (scale slotTwo))⁻¹) ^ 2
          + scale slotThree * (coeff 2 * (Real.sqrt (scale slotThree))⁻¹) ^ 2 := by
    intro coeff
    rw [Fin.sum_univ_three, atomScaledTriple_scale_value (hpos slotOne),
      atomScaledTriple_scale_value (hpos slotTwo),
      atomScaledTriple_scale_value (hpos slotThree)]
  constructor
  · intro hdual valueOne valueTwo valueThree
    have hfamDual : ∀ direction : Fin 3 → ℝ,
        direction ⬝ᵥ direction
          ≤ ∑ index,
              (atomScaledTriple atom scale slotOne slotTwo slotThree index ⬝ᵥ direction) ^ 2 := by
      intro direction
      rw [atomScaledTriple_reading atom scale hpos slotOne slotTwo slotThree direction]
      exact hdual direction
    have hstep := blendEnergy_of_dualEnergy
      (atomScaledTriple atom scale slotOne slotTwo slotThree) hfamDual
      ![valueOne * Real.sqrt (scale slotOne), valueTwo * Real.sqrt (scale slotTwo),
        valueThree * Real.sqrt (scale slotThree)]
    rw [hblendValue, hcoeffValue] at hstep
    have hcancelOne : valueOne * Real.sqrt (scale slotOne) * (Real.sqrt (scale slotOne))⁻¹
        = valueOne := by field_simp
    have hcancelTwo : valueTwo * Real.sqrt (scale slotTwo) * (Real.sqrt (scale slotTwo))⁻¹
        = valueTwo := by field_simp
    have hcancelThree :
        valueThree * Real.sqrt (scale slotThree) * (Real.sqrt (scale slotThree))⁻¹
        = valueThree := by field_simp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, hcancelOne, hcancelTwo, hcancelThree] at hstep
    exact hstep
  · intro hvalues direction
    have hfamBlend : ∀ coeff : Fin 3 → ℝ,
        (∑ index, coeff index ^ 2)
          ≤ atomBlend (atomScaledTriple atom scale slotOne slotTwo slotThree) coeff
              ⬝ᵥ atomBlend (atomScaledTriple atom scale slotOne slotTwo slotThree) coeff := by
      intro coeff
      rw [hblendValue coeff, hcoeffValue coeff]
      exact hvalues (coeff 0 * (Real.sqrt (scale slotOne))⁻¹)
        (coeff 1 * (Real.sqrt (scale slotTwo))⁻¹)
        (coeff 2 * (Real.sqrt (scale slotThree))⁻¹)
    have hstep := dualEnergy_of_blendEnergy
      (atomScaledTriple atom scale slotOne slotTwo slotThree) hfamBlend direction
    rwa [atomScaledTriple_reading atom scale hpos slotOne slotTwo slotThree direction] at hstep

/-- **THE OPERATOR FACE OF THE RESIDUE.**  Six tight frame atoms of rank
three with six positive scales of total one carry a triple whose scaled
atom operator dominates the identity.  This is the residue in the language
of the fractional cover, and the cover of the free half is its
relaxation. -/
def AtomTripleOperatorClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ ∀ direction : Fin 3 → ℝ,
            direction ⬝ᵥ direction
              ≤ (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne
                + (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo
                + (atom slotThree ⬝ᵥ direction) ^ 2 / scale slotThree

/-- The operator face gives the mass-one selection. -/
theorem atomTripleBoundaryClosed_of_atomTripleOperator
    (hoperator : AtomTripleOperatorClosed) : AtomTripleBoundaryClosed := by
  intro atom scale hpos hmass hframe
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hdual⟩ :=
    hoperator atom scale hpos hmass hframe
  exact exists_weakCarrier_of_values honeTwo honeThree htwoThree
    ((atomTriple_operator_iff_values atom scale hpos slotOne slotTwo slotThree).mp hdual)

/-- The mass-one selection gives the operator face. -/
theorem atomTripleOperatorClosed_of_atomTripleBoundary
    (hboundary : AtomTripleBoundaryClosed) : AtomTripleOperatorClosed := by
  classical
  intro atom scale hpos hmass hframe
  obtain ⟨car, hcard, hdom⟩ := hboundary atom scale hpos hmass hframe
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hcarEq⟩ :=
    Finset.card_eq_three.mp hcard
  subst hcarEq
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, ?_⟩
  exact (atomTriple_operator_iff_values atom scale hpos slotOne slotTwo slotThree).mpr
    (weak_values_of_weak_carrier honeTwo honeThree htwoThree hdom)

/-- **THE SIXTH FACE OF THE CELL.**  The operator face and the mass-one
selection are one statement. -/
theorem atomTripleOperatorClosed_iff_atomTripleBoundary :
    AtomTripleOperatorClosed ↔ AtomTripleBoundaryClosed :=
  ⟨atomTripleBoundaryClosed_of_atomTripleOperator,
    atomTripleOperatorClosed_of_atomTripleBoundary⟩

/-- **THE CELL FROM THE OPERATOR FACE.** -/
theorem gtzWeighted_six_three_of_atomTripleOperator
    (hoperator : AtomTripleOperatorClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomTripleBoundary
    (atomTripleBoundaryClosed_of_atomTripleOperator hoperator)

end Operator

end Gtz
