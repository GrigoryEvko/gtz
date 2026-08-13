import Gtz.Wave.AtomEnergyCeiling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The atom Gram and the dominating pair — the selection layer of the third rung

The design geometry layer reduced the whole rank-six wall to one
inequality about six vectors in three dimensions: the ATOM TRIPLE
CEILING.  That inequality carries a quantifier over a continuum, thus no
finite certificate reads it directly.  This module removes the continuum
and supplies the first unconditional selection theorem of the campaign.

The layer starts from the GRAM of the atom family.  The frame law says
that the six atom vectors are the rows of an isometry, thus their Gram
matrix is a symmetric idempotent of trace three.  Two exact laws follow,
and they are the whole arithmetic of this module: the ROW ENERGY LAW,
which prices the square sum of one Gram row by its own diagonal entry,
and the TRACE LAW, which prices the diagonal total by the rank.  No
design and no chart value enter.

The blend identity of the previous layer becomes a plain double sum
against the Gram.  Thus a carrier dominates exactly when a small
symmetric block is positive definite, and positive definiteness of a
block of dimension two or three is a POLYNOMIAL condition through the
nested minors.  Two closed-form square decompositions supply that
condition with no eigenvalue, no spectral theorem and no analysis.

The last layer is the selection theorem.  Take the shifted Gram, that
is, the Gram minus the diagonal of the scales.  Sum its pair minors over
a region of slots.  The row energy law and the trace law price that
total from below, and the failure of every pair inside the region prices
the same total from above by the square of the negative part of the
shifted diagonal.  The two prices collide as soon as the diagonal mass
of the region is more than one plus twice its scale mass.  At the full
slot set of a rank-three frame the diagonal mass is three and the scale
mass is less than one, thus the collision is unconditional: **every
rank-three atom frame with scales of total less than one carries a
DOMINATING PAIR.**  The pair is the first two links of a Sylvester
chain, thus the atom triple ceiling now needs one link only, and that
link is the determinant of one three by three block.

The last layer prices that link.  The determinant of a three-slot block
factors as the shifted diagonal of the third slot against the pair
minor, minus the SCHUR LEAK of that slot.  The leak of a pair sums over
all slots to one exact expression in five Gram entries, again by the row
energy law and the idempotence law.  Thus a dominating pair extends as
soon as the shifted diagonal mass of a region beats the leak of that
region, and the residue of the third rung is one scalar margin.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.probeUnit`, `Gtz.dotProduct_probeUnit`, `Gtz.probeUnit_energy` —
  the probe basis.
* `Gtz.atomGram` — the Gram of an atom family.
* `Gtz.atomGram_comm`, `Gtz.atomGram_diag_nonneg`,
  `Gtz.atomGram_sq_le_diag_mul` — the unconditional Gram laws.
* `Gtz.atomBlend_energy_eq_gram` — **THE BLEND IS A GRAM FORM.**
* `Gtz.atomGram_row_energy` — **THE ROW ENERGY LAW.**
* `Gtz.atomGram_trace` — **THE TRACE LAW.**
* `Gtz.atomGram_idempotent` — **THE IDEMPOTENCE LAW.**
* `Gtz.atomGram_diag_le_one`, `Gtz.atomGram_square_total`,
  `Gtz.atomGram_region_square_le` — the readings of the frame laws.
* `Gtz.quadratic_pos_of_pair_minors` — **THE PAIR CERTIFICATE.**
* `Gtz.quadratic_pos_of_triple_minors` — **THE TRIPLE CERTIFICATE.**
* `Gtz.atomShiftedDiag`, `Gtz.atomPairMinor`, `Gtz.atomTripleDet`,
  `Gtz.atomNegDefect` — the shifted Gram calculus, with
  `Gtz.negDefect_nonneg`, `Gtz.negDefect_eq_zero`,
  `Gtz.negDefect_eq_neg`, `Gtz.negDefect_le_scale`.
* `Gtz.pairMinor_region_total` — the exact pair-minor total of a region.
* `Gtz.pairMinor_le_negDefect_mul` — the pointwise price of a failure.
* `Gtz.exists_dominating_pair_on` — **THE DOMINATING PAIR THEOREM** at a
  region.
* `Gtz.exists_dominating_pair` — its unconditional form at a rank-three
  frame.
* `Gtz.atomShiftedDiag_total`, `Gtz.atomShiftedDiag_lt_one` — the
  shifted diagonal budget.
* `Gtz.exists_dominating_pair_off_slot` — **THE DOMINATING PAIR OFF ONE
  SLOT**, the shape an extension argument consumes.
* `Gtz.atomRead`, `Gtz.atomBlend_atomRead`, `Gtz.atomRead_ne_zero`,
  `Gtz.shifted_form_pos_on_reads` — **THE POSITIVE READ SPACE**: the
  shifted Gram is positive definite on a space of dimension three, and
  the residue is exactly the passage from that space to a COORDINATE
  space of dimension three.
* `Gtz.sum_over_pair_slots`, `Gtz.sum_over_triple_slots`,
  `Gtz.sum_eq_pair_of_support`, `Gtz.sum_eq_triple_of_support`,
  `Gtz.card_triple_slots` — the support calculus of a small carrier.
* `Gtz.dominates_of_pair_minors`, `Gtz.dominates_of_triple_minors` —
  **THE CARRIER DISCHARGE**: a nested minor chain dominates every
  nonzero vector of its carrier.
* `Gtz.AtomTripleSylvesterClosed` — **THE POLYNOMIAL RESIDUE.**
* `Gtz.atomTripleCeilingClosed_of_sylvester` — the residue closes the
  atom triple ceiling.
* `Gtz.atomTripleSylvester_pair_free` — the first two links of the chain
  are free at every datum.
* `Gtz.exists_dominating_pair_carrier` — the dominating pair as a
  carrier of card two.
* `Gtz.RankSixFrame.exists_dominating_pair` — the dominating pair at a
  rank-six frame of a `(6,3)` crux.
* `Gtz.rankSixOuterKilled_of_sylvester`,
  `Gtz.rankSixSupportTwoClosed_of_sylvester`,
  `Gtz.rankSixOuterCircuitClosed_of_sylvester`,
  `Gtz.rankSixOuterRegularClosed_of_sylvester`,
  `Gtz.rankSixOuterThinClosed_of_sylvester`,
  `Gtz.gtzWeighted_six_three_of_sylvester_of_interior`,
  `Gtz.rankFiveSupportTwoClosed_of_sylvester_of_interior`,
  `Gtz.rankFourSupportTwoClosed_of_sylvester_of_interior` — the rung
  from the polynomial residue.
* `Gtz.atomSchurLeak`, `Gtz.atomTripleDet_schur` — **THE SCHUR
  FACTORIZATION** of a three-slot determinant.
* `Gtz.atomSchurLeak_total`, `Gtz.atomTripleDet_total` — the exact
  averaged price of an extension of one pair.
* `Gtz.exists_extending_slot`,
  `Gtz.exists_sylvester_chain_of_extension` — **THE EXTENSION
  CRITERION**: a region whose shifted diagonal mass beats its own Schur
  leak against a dominating pair supplies a dominating triple.
* `Gtz.atom_full_frame_dominates` — **THE FULL FRAME DOMINATES**, thus
  the residue of the third rung is one ROUNDING law and not an
  existence law.
* `Gtz.AtomFrameDropClosed`, `Gtz.atom_univ_dominates` — the
  frame-constrained drop and the start of its descent.

## Vacuity

Every law of layers zero thru four is an unconditional statement about a
family of vectors.  The crux statements are vacuous if
`Gtz.GtzWeighted 6 3` holds, because no crux exists then.
-/

namespace Gtz

/-! ## Layer 0 — the probe basis and the atom Gram -/

/-- The standard unit vector of the probe space. -/
def probeUnit {rank : ℕ} (index : Fin rank) : Fin rank → ℝ :=
  fun other => if other = index then 1 else 0

theorem dotProduct_probeUnit {rank : ℕ} (value : Fin rank → ℝ) (index : Fin rank) :
    value ⬝ᵥ probeUnit index = value index := by
  classical
  rw [dotProduct, Finset.sum_eq_single index
    (fun other _ hne => by simp only [probeUnit, if_neg hne, mul_zero])
    (fun hnot => absurd (Finset.mem_univ _) hnot)]
  simp [probeUnit]

theorem probeUnit_energy {rank : ℕ} (index : Fin rank) :
    probeUnit index ⬝ᵥ probeUnit index = 1 := by
  rw [dotProduct_probeUnit]
  simp [probeUnit]

/-- The GRAM of an atom family: the dot product of two atom vectors.
The frame law makes it a symmetric idempotent of trace `rank`, thus the
whole design geometry moves into one symmetric matrix of slot size. -/
def atomGram {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (rowSlot colSlot : Fin slotCount) : ℝ :=
  atom rowSlot ⬝ᵥ atom colSlot

theorem atomGram_comm {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (rowSlot colSlot : Fin slotCount) :
    atomGram atom rowSlot colSlot = atomGram atom colSlot rowSlot :=
  dotProduct_comm _ _

theorem atomGram_diag_nonneg {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (slot : Fin slotCount) : 0 ≤ atomGram atom slot slot := by
  simp only [atomGram, dotProduct]
  exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- The Cauchy-Schwarz law of the Gram: an off-diagonal entry is capped
by the two diagonal entries that carry it. -/
theorem atomGram_sq_le_diag_mul {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (rowSlot colSlot : Fin slotCount) :
    atomGram atom rowSlot colSlot ^ 2
      ≤ atomGram atom rowSlot rowSlot * atomGram atom colSlot colSlot := by
  classical
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin rank))
    (fun index => atom rowSlot index) (fun index => atom colSlot index)
  simp only [atomGram, dotProduct]
  refine hcauchy.trans (le_of_eq ?_)
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => sq _

/-- **THE BLEND IS A GRAM FORM.**  The blend energy of an ambient vector
is the double sum of the Gram against that vector.  Thus the whole
design geometry of a carrier is one small symmetric block. -/
theorem atomBlend_energy_eq_gram {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (probe : Fin slotCount → ℝ) :
    atomBlend atom probe ⬝ᵥ atomBlend atom probe
      = ∑ rowSlot, ∑ colSlot,
          probe rowSlot * probe colSlot * atomGram atom rowSlot colSlot := by
  classical
  rw [atomBlend_dot]
  refine Finset.sum_congr rfl fun rowSlot _ => ?_
  rw [dotProduct_comm, atomBlend_dot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun colSlot _ => ?_
  simp only [atomGram]
  rw [dotProduct_comm (atom colSlot) (atom rowSlot)]
  ring

/-! ## Layer 1 — the two frame laws -/

variable {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}

/-- **THE ROW ENERGY LAW.**  The square sum of one Gram row is the
diagonal entry of that row.  This is idempotence of the Gram read one
row at a time, and it needs the frame law only. -/
theorem atomGram_row_energy
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot : Fin slotCount) :
    (∑ colSlot, atomGram atom rowSlot colSlot ^ 2) = atomGram atom rowSlot rowSlot := by
  classical
  have hcell : ∀ colSlot : Fin slotCount,
      atomGram atom rowSlot colSlot ^ 2
        = (atom colSlot ⬝ᵥ atom rowSlot) * (atom colSlot ⬝ᵥ atom rowSlot) := by
    intro colSlot
    simp only [atomGram]
    rw [dotProduct_comm (atom rowSlot) (atom colSlot), sq]
  rw [Finset.sum_congr rfl fun colSlot _ => hcell colSlot, hframe (atom rowSlot) (atom rowSlot)]
  rfl

/-- **THE TRACE LAW.**  The diagonal total of the Gram is the rank. -/
theorem atomGram_trace
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ slot, atomGram atom slot slot) = (rank : ℝ) := by
  classical
  have hswap : (∑ slot, atomGram atom slot slot)
      = ∑ index : Fin rank, ∑ slot : Fin slotCount,
          (atom slot ⬝ᵥ probeUnit index) * (atom slot ⬝ᵥ probeUnit index) := by
    have hcell : ∀ slot : Fin slotCount, atomGram atom slot slot
        = ∑ index : Fin rank,
            (atom slot ⬝ᵥ probeUnit index) * (atom slot ⬝ᵥ probeUnit index) := by
      intro slot
      simp only [dotProduct_probeUnit]
      simp only [atomGram, dotProduct]
    rw [Finset.sum_congr rfl fun slot _ => hcell slot, Finset.sum_comm]
  rw [hswap, Finset.sum_congr rfl fun index _ =>
    (hframe (probeUnit index) (probeUnit index)).trans (probeUnit_energy index),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **THE IDEMPOTENCE LAW.**  The Gram of a frame is a symmetric
idempotent: with the trace law it is a projection of rank `rank`, thus
the whole design geometry is one orthogonal projection of slot size. -/
theorem atomGram_idempotent
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot colSlot : Fin slotCount) :
    (∑ midSlot, atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot)
      = atomGram atom rowSlot colSlot := by
  classical
  have hcell : ∀ midSlot : Fin slotCount,
      atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot
        = (atom midSlot ⬝ᵥ atom rowSlot) * (atom midSlot ⬝ᵥ atom colSlot) := by
    intro midSlot
    simp only [atomGram]
    rw [dotProduct_comm (atom rowSlot) (atom midSlot)]
  rw [Finset.sum_congr rfl fun midSlot _ => hcell midSlot,
    hframe (atom rowSlot) (atom colSlot)]
  rfl

/-- Every diagonal entry of the Gram of a frame is at most one. -/
theorem atomGram_diag_le_one
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (slot : Fin slotCount) : atomGram atom slot slot ≤ 1 := by
  classical
  have hsingle : atomGram atom slot slot ^ 2
      ≤ ∑ colSlot, atomGram atom slot colSlot ^ 2 :=
    Finset.single_le_sum (f := fun colSlot => atomGram atom slot colSlot ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ slot)
  rw [atomGram_row_energy hframe slot] at hsingle
  nlinarith [hsingle, atomGram_diag_nonneg atom slot]

/-- The full square total of the Gram of a frame is the rank. -/
theorem atomGram_square_total
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ rowSlot, ∑ colSlot, atomGram atom rowSlot colSlot ^ 2) = (rank : ℝ) := by
  rw [Finset.sum_congr rfl fun rowSlot _ => atomGram_row_energy hframe rowSlot,
    atomGram_trace hframe]

/-- The square total of the Gram on a region is capped by the diagonal
mass of that region. -/
theorem atomGram_region_square_le
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (region : Finset (Fin slotCount)) :
    (∑ rowSlot ∈ region, ∑ colSlot ∈ region, atomGram atom rowSlot colSlot ^ 2)
      ≤ ∑ rowSlot ∈ region, atomGram atom rowSlot rowSlot := by
  classical
  refine Finset.sum_le_sum fun rowSlot _ => ?_
  rw [← atomGram_row_energy hframe rowSlot]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ region)
    fun _ _ _ => sq_nonneg _

/-! ## Layer 2 — the nested minor certificates -/

/-- **THE PAIR CERTIFICATE.**  A symmetric block of dimension two with a
positive first diagonal entry and a positive determinant is positive on
every nonzero vector.  The proof is one square decomposition. -/
theorem quadratic_pos_of_pair_minors {diagOne diagTwo cross valueOne valueTwo : ℝ}
    (hdiag : 0 < diagOne) (hminor : 0 < diagOne * diagTwo - cross ^ 2)
    (hne : valueOne ≠ 0 ∨ valueTwo ≠ 0) :
    0 < diagOne * valueOne ^ 2 + 2 * cross * valueOne * valueTwo
      + diagTwo * valueTwo ^ 2 := by
  have hsplit : diagOne * (diagOne * valueOne ^ 2 + 2 * cross * valueOne * valueTwo
      + diagTwo * valueTwo ^ 2)
      = (diagOne * valueOne + cross * valueTwo) ^ 2
        + (diagOne * diagTwo - cross ^ 2) * valueTwo ^ 2 := by ring
  have hpos : 0 < (diagOne * valueOne + cross * valueTwo) ^ 2
      + (diagOne * diagTwo - cross ^ 2) * valueTwo ^ 2 := by
    rcases eq_or_ne valueTwo 0 with hzero | hnz
    · have hone : valueOne ≠ 0 := by
        rcases hne with h | h
        · exact h
        · exact absurd hzero h
      rw [hzero]
      have : (0 : ℝ) < (diagOne * valueOne) ^ 2 :=
        pow_pos (abs_pos.mpr (mul_ne_zero (ne_of_gt hdiag) hone)) 2
          |>.trans_le (le_of_eq (by rw [sq_abs]))
      nlinarith [this]
    · have hsq : (0 : ℝ) < valueTwo ^ 2 :=
        pow_pos (abs_pos.mpr hnz) 2 |>.trans_le (le_of_eq (by rw [sq_abs]))
      nlinarith [sq_nonneg (diagOne * valueOne + cross * valueTwo), mul_pos hminor hsq]
  nlinarith [hsplit, hpos, hdiag]

/-- **THE TRIPLE CERTIFICATE.**  A symmetric block of dimension three
whose nested minors are positive is positive on every nonzero vector.
The proof is the closed-form square decomposition of the block, thus it
needs no eigenvalue and no spectral theorem. -/
theorem quadratic_pos_of_triple_minors
    {diagOne diagTwo diagThree crossOneTwo crossOneThree crossTwoThree
      valueOne valueTwo valueThree : ℝ}
    (hdiag : 0 < diagOne)
    (hminor : 0 < diagOne * diagTwo - crossOneTwo ^ 2)
    (hdet : 0 < diagOne * diagTwo * diagThree
      + 2 * crossOneTwo * crossOneThree * crossTwoThree
      - diagOne * crossTwoThree ^ 2 - diagTwo * crossOneThree ^ 2
      - diagThree * crossOneTwo ^ 2)
    (hne : ¬(valueOne = 0 ∧ valueTwo = 0 ∧ valueThree = 0)) :
    0 < diagOne * valueOne ^ 2 + diagTwo * valueTwo ^ 2 + diagThree * valueThree ^ 2
      + 2 * crossOneTwo * valueOne * valueTwo
      + 2 * crossOneThree * valueOne * valueThree
      + 2 * crossTwoThree * valueTwo * valueThree := by
  set minorTwo := diagOne * diagTwo - crossOneTwo ^ 2 with hminorTwo
  set determinant := diagOne * diagTwo * diagThree
    + 2 * crossOneTwo * crossOneThree * crossTwoThree
    - diagOne * crossTwoThree ^ 2 - diagTwo * crossOneThree ^ 2
    - diagThree * crossOneTwo ^ 2 with hdeterminant
  set form := diagOne * valueOne ^ 2 + diagTwo * valueTwo ^ 2 + diagThree * valueThree ^ 2
    + 2 * crossOneTwo * valueOne * valueTwo
    + 2 * crossOneThree * valueOne * valueThree
    + 2 * crossTwoThree * valueTwo * valueThree with hform
  have hsplit : diagOne * minorTwo * form
      = minorTwo * (diagOne * valueOne + crossOneTwo * valueTwo
          + crossOneThree * valueThree) ^ 2
        + (minorTwo * valueTwo
            + (diagOne * crossTwoThree - crossOneTwo * crossOneThree) * valueThree) ^ 2
        + diagOne * determinant * valueThree ^ 2 := by
    rw [hminorTwo, hdeterminant, hform]; ring
  have hpos : 0 < minorTwo * (diagOne * valueOne + crossOneTwo * valueTwo
      + crossOneThree * valueThree) ^ 2
      + (minorTwo * valueTwo
          + (diagOne * crossTwoThree - crossOneTwo * crossOneThree) * valueThree) ^ 2
      + diagOne * determinant * valueThree ^ 2 := by
    rcases eq_or_ne valueThree 0 with hthree | hthree
    · rcases eq_or_ne valueTwo 0 with htwo | htwo
      · have hone : valueOne ≠ 0 := by
          intro hzero
          exact hne ⟨hzero, htwo, hthree⟩
        rw [hthree, htwo]
        have hsq : (0 : ℝ) < (diagOne * valueOne + crossOneTwo * 0 + crossOneThree * 0) ^ 2 := by
          have hnz : diagOne * valueOne + crossOneTwo * 0 + crossOneThree * 0 ≠ 0 := by
            rw [mul_zero, mul_zero, add_zero, add_zero]
            exact mul_ne_zero (ne_of_gt hdiag) hone
          exact pow_pos (abs_pos.mpr hnz) 2 |>.trans_le (le_of_eq (by rw [sq_abs]))
        nlinarith [hsq, hminor, sq_nonneg (minorTwo * 0
          + (diagOne * crossTwoThree - crossOneTwo * crossOneThree) * 0)]
      · rw [hthree]
        have hsq : (0 : ℝ) < (minorTwo * valueTwo
            + (diagOne * crossTwoThree - crossOneTwo * crossOneThree) * 0) ^ 2 := by
          have hnz : minorTwo * valueTwo
              + (diagOne * crossTwoThree - crossOneTwo * crossOneThree) * 0 ≠ 0 := by
            rw [mul_zero, add_zero]
            exact mul_ne_zero (ne_of_gt hminor) htwo
          exact pow_pos (abs_pos.mpr hnz) 2 |>.trans_le (le_of_eq (by rw [sq_abs]))
        nlinarith [hsq, hminor, sq_nonneg (diagOne * valueOne + crossOneTwo * valueTwo
          + crossOneThree * 0)]
    · have hsq : (0 : ℝ) < valueThree ^ 2 :=
        pow_pos (abs_pos.mpr hthree) 2 |>.trans_le (le_of_eq (by rw [sq_abs]))
      have hlast : 0 < diagOne * determinant * valueThree ^ 2 :=
        mul_pos (mul_pos hdiag hdet) hsq
      nlinarith [hlast, hminor,
        sq_nonneg (diagOne * valueOne + crossOneTwo * valueTwo + crossOneThree * valueThree),
        sq_nonneg (minorTwo * valueTwo
          + (diagOne * crossTwoThree - crossOneTwo * crossOneThree) * valueThree),
        mul_nonneg hminor.le (sq_nonneg (diagOne * valueOne + crossOneTwo * valueTwo
          + crossOneThree * valueThree))]
  nlinarith [hsplit, hpos, mul_pos hdiag hminor]

/-! ## Layer 3 — the shifted Gram calculus -/

/-- The SHIFTED DIAGONAL of the Gram at a slot: the diagonal entry of
the Gram minus the scale of that slot. -/
def atomShiftedDiag {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slot : Fin slotCount) : ℝ :=
  atomGram atom slot slot - scale slot

/-- The PAIR MINOR of the shifted Gram at two slots. -/
def atomPairMinor {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (rowSlot colSlot : Fin slotCount) : ℝ :=
  atomShiftedDiag atom scale rowSlot * atomShiftedDiag atom scale colSlot
    - atomGram atom rowSlot colSlot ^ 2

/-- The DETERMINANT of the shifted Gram block of three slots. -/
def atomTripleDet {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  atomShiftedDiag atom scale slotOne * atomShiftedDiag atom scale slotTwo
      * atomShiftedDiag atom scale slotThree
    + 2 * atomGram atom slotOne slotTwo * atomGram atom slotOne slotThree
        * atomGram atom slotTwo slotThree
    - atomShiftedDiag atom scale slotOne * atomGram atom slotTwo slotThree ^ 2
    - atomShiftedDiag atom scale slotTwo * atomGram atom slotOne slotThree ^ 2
    - atomShiftedDiag atom scale slotThree * atomGram atom slotOne slotTwo ^ 2

/-- The NEGATIVE DEFECT of a slot: the part of the scale that the
diagonal entry of the Gram does not carry. -/
def atomNegDefect {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slot : Fin slotCount) : ℝ :=
  max 0 (-atomShiftedDiag atom scale slot)

theorem negDefect_nonneg {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slot : Fin slotCount) :
    0 ≤ atomNegDefect atom scale slot := le_max_left _ _

theorem negDefect_eq_zero {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {slot : Fin slotCount}
    (hpos : 0 < atomShiftedDiag atom scale slot) : atomNegDefect atom scale slot = 0 :=
  max_eq_left (by linarith)

theorem negDefect_eq_neg {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {slot : Fin slotCount}
    (hnonpos : atomShiftedDiag atom scale slot ≤ 0) :
    atomNegDefect atom scale slot = -atomShiftedDiag atom scale slot :=
  max_eq_right (by linarith)

/-- The negative defect of a slot never exceeds the scale of that slot,
because the diagonal entry of the Gram is nonnegative. -/
theorem negDefect_le_scale {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    {scale : Fin slotCount → ℝ} {slot : Fin slotCount} (hscale : 0 ≤ scale slot) :
    atomNegDefect atom scale slot ≤ scale slot := by
  rcases le_or_gt (atomShiftedDiag atom scale slot) 0 with hnonpos | hpos
  · rw [negDefect_eq_neg hnonpos]
    simp only [atomShiftedDiag]
    linarith [atomGram_diag_nonneg atom slot]
  · rw [negDefect_eq_zero hpos]
    exact hscale

/-- The exact pair-minor total of a region: the square of the shifted
diagonal mass minus the square total of the Gram on that region. -/
theorem pairMinor_region_total {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (region : Finset (Fin slotCount)) :
    (∑ rowSlot ∈ region, ∑ colSlot ∈ region, atomPairMinor atom scale rowSlot colSlot)
      = (∑ slot ∈ region, atomShiftedDiag atom scale slot) ^ 2
        - ∑ rowSlot ∈ region, ∑ colSlot ∈ region, atomGram atom rowSlot colSlot ^ 2 := by
  classical
  have hrow : ∀ rowSlot : Fin slotCount,
      (∑ colSlot ∈ region, atomPairMinor atom scale rowSlot colSlot)
        = atomShiftedDiag atom scale rowSlot * (∑ colSlot ∈ region, atomShiftedDiag atom scale colSlot)
          - ∑ colSlot ∈ region, atomGram atom rowSlot colSlot ^ 2 := by
    intro rowSlot
    simp only [atomPairMinor]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun rowSlot _ => hrow rowSlot, Finset.sum_sub_distrib,
    ← Finset.sum_mul, sq]

/-- **THE POINTWISE PRICE OF A FAILURE.**  If no pair of the region
dominates, then every pair minor of the region is capped by the product
of the two negative defects.  The diagonal case needs no hypothesis. -/
theorem pairMinor_le_negDefect_mul {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    (hscale : ∀ slot, 0 < scale slot) {region : Finset (Fin slotCount)}
    (hnone : ∀ rowSlot ∈ region, ∀ colSlot ∈ region, rowSlot ≠ colSlot →
      0 < atomShiftedDiag atom scale rowSlot → 0 < atomShiftedDiag atom scale colSlot →
      atomPairMinor atom scale rowSlot colSlot ≤ 0)
    {rowSlot colSlot : Fin slotCount} (hrow : rowSlot ∈ region) (hcol : colSlot ∈ region) :
    atomPairMinor atom scale rowSlot colSlot
      ≤ atomNegDefect atom scale rowSlot * atomNegDefect atom scale colSlot := by
  rcases eq_or_ne rowSlot colSlot with hsame | hdiff
  · subst hsame
    rcases le_or_gt (atomShiftedDiag atom scale rowSlot) 0 with hnonpos | hpos
    · rw [negDefect_eq_neg hnonpos]
      simp only [atomPairMinor]
      nlinarith [sq_nonneg (atomGram atom rowSlot rowSlot)]
    · rw [negDefect_eq_zero hpos, mul_zero]
      have hlt : atomShiftedDiag atom scale rowSlot < atomGram atom rowSlot rowSlot := by
        simp only [atomShiftedDiag]
        linarith [hscale rowSlot]
      simp only [atomPairMinor]
      nlinarith [hpos, hlt]
  · rcases le_or_gt (atomShiftedDiag atom scale rowSlot) 0 with hrowNonpos | hrowPos
    · rcases le_or_gt (atomShiftedDiag atom scale colSlot) 0 with hcolNonpos | hcolPos
      · rw [negDefect_eq_neg hrowNonpos, negDefect_eq_neg hcolNonpos]
        simp only [atomPairMinor]
        nlinarith [sq_nonneg (atomGram atom rowSlot colSlot)]
      · rw [negDefect_eq_zero hcolPos, mul_zero]
        simp only [atomPairMinor]
        nlinarith [sq_nonneg (atomGram atom rowSlot colSlot),
          mul_nonpos_of_nonpos_of_nonneg hrowNonpos hcolPos.le]
    · rcases le_or_gt (atomShiftedDiag atom scale colSlot) 0 with hcolNonpos | hcolPos
      · rw [negDefect_eq_zero hrowPos, zero_mul]
        simp only [atomPairMinor]
        nlinarith [sq_nonneg (atomGram atom rowSlot colSlot),
          mul_nonpos_of_nonneg_of_nonpos hrowPos.le hcolNonpos]
      · rw [negDefect_eq_zero hrowPos, zero_mul]
        exact hnone rowSlot hrow colSlot hcol hdiff hrowPos hcolPos

/-! ## Layer 4 — the dominating pair theorem -/

/-- **THE DOMINATING PAIR THEOREM AT A REGION.**  If the diagonal mass
of a region of slots is more than one plus twice its scale mass, then
two slots of the region carry a positive definite block of the shifted
Gram.  The proof prices the pair-minor total of the region from below by
the row energy law and the trace law, and from above by the square of
the negative defect mass, and the two prices collide. -/
theorem exists_dominating_pair_on {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} (hscale : ∀ slot, 0 < scale slot)
    {region : Finset (Fin slotCount)}
    (hmass : 1 + 2 * (∑ slot ∈ region, scale slot)
      < ∑ slot ∈ region, atomGram atom slot slot) :
    ∃ rowSlot ∈ region, ∃ colSlot ∈ region, rowSlot ≠ colSlot
      ∧ 0 < atomShiftedDiag atom scale rowSlot
      ∧ 0 < atomShiftedDiag atom scale colSlot
      ∧ 0 < atomPairMinor atom scale rowSlot colSlot := by
  classical
  by_contra hcontra
  have hnone : ∀ rowSlot ∈ region, ∀ colSlot ∈ region, rowSlot ≠ colSlot →
      0 < atomShiftedDiag atom scale rowSlot → 0 < atomShiftedDiag atom scale colSlot →
      atomPairMinor atom scale rowSlot colSlot ≤ 0 := by
    intro rowSlot hrow colSlot hcol hdiff hrowPos hcolPos
    by_contra hlt
    exact hcontra ⟨rowSlot, hrow, colSlot, hcol, hdiff, hrowPos, hcolPos, not_le.mp hlt⟩
  set mass := ∑ slot ∈ region, atomGram atom slot slot with hmassDef
  set scaleMass := ∑ slot ∈ region, scale slot with hscaleMassDef
  set defectMass := ∑ slot ∈ region, atomNegDefect atom scale slot with hdefectMassDef
  have hshift : (∑ slot ∈ region, atomShiftedDiag atom scale slot) = mass - scaleMass := by
    simp only [atomShiftedDiag, hmassDef, hscaleMassDef]
    rw [Finset.sum_sub_distrib]
  have hdefectNonneg : 0 ≤ defectMass :=
    Finset.sum_nonneg fun slot _ => negDefect_nonneg atom scale slot
  have hdefectLe : defectMass ≤ scaleMass :=
    Finset.sum_le_sum fun slot _ => negDefect_le_scale atom (hscale slot).le
  have hscaleNonneg : 0 ≤ scaleMass :=
    Finset.sum_nonneg fun slot _ => (hscale slot).le
  have hupper : (∑ rowSlot ∈ region, ∑ colSlot ∈ region, atomPairMinor atom scale rowSlot colSlot)
      ≤ defectMass ^ 2 := by
    have hterm : (∑ rowSlot ∈ region, ∑ colSlot ∈ region, atomPairMinor atom scale rowSlot colSlot)
        ≤ ∑ rowSlot ∈ region, ∑ colSlot ∈ region,
            atomNegDefect atom scale rowSlot * atomNegDefect atom scale colSlot :=
      Finset.sum_le_sum fun rowSlot hrow => Finset.sum_le_sum fun colSlot hcol =>
        pairMinor_le_negDefect_mul hscale hnone hrow hcol
    rw [sq, hdefectMassDef, Finset.sum_mul_sum]
    exact hterm
  have hlower : (mass - scaleMass) ^ 2 - mass
      ≤ ∑ rowSlot ∈ region, ∑ colSlot ∈ region, atomPairMinor atom scale rowSlot colSlot := by
    rw [pairMinor_region_total atom scale region, hshift]
    have := atomGram_region_square_le hframe (atom := atom) region
    rw [← hmassDef] at this
    linarith [this]
  have hkey : (mass - scaleMass) ^ 2 - mass ≤ scaleMass ^ 2 := by
    have hsq : defectMass ^ 2 ≤ scaleMass ^ 2 := by nlinarith [hdefectNonneg, hdefectLe]
    linarith [hlower, hupper, hsq]
  nlinarith [hkey, hmass, hscaleNonneg]

/-- **THE DOMINATING PAIR THEOREM.**  A rank-three atom frame whose
scales are positive and total less than one carries two slots on which
the shifted Gram is positive definite.  The statement is unconditional:
no chart, no crux, no stationarity and no combinatorics enter. -/
theorem exists_dominating_pair {slotCount : ℕ} {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ rowSlot colSlot : Fin slotCount, rowSlot ≠ colSlot
      ∧ 0 < atomShiftedDiag atom scale rowSlot
      ∧ 0 < atomShiftedDiag atom scale colSlot
      ∧ 0 < atomPairMinor atom scale rowSlot colSlot := by
  classical
  have htrace : (∑ slot, atomGram atom slot slot) = (3 : ℝ) := by
    rw [atomGram_trace hframe]; norm_num
  have hmass : 1 + 2 * (∑ slot ∈ (Finset.univ : Finset (Fin slotCount)), scale slot)
      < ∑ slot ∈ (Finset.univ : Finset (Fin slotCount)), atomGram atom slot slot := by
    rw [htrace]
    linarith [hsmall]
  obtain ⟨rowSlot, _, colSlot, _, hdiff, hrowPos, hcolPos, hminor⟩ :=
    exists_dominating_pair_on hframe hscale hmass
  exact ⟨rowSlot, colSlot, hdiff, hrowPos, hcolPos, hminor⟩

/-- The shifted diagonal mass of a frame is the rank minus the scale
mass.  At rank three with scales of total less than one it is more than
two, thus at least three slots carry a positive shifted diagonal. -/
theorem atomShiftedDiag_total {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) :
    (∑ slot, atomShiftedDiag atom scale slot) = (rank : ℝ) - ∑ slot, scale slot := by
  simp only [atomShiftedDiag]
  rw [Finset.sum_sub_distrib, atomGram_trace hframe]

/-- Every shifted diagonal entry of a frame is less than one. -/
theorem atomShiftedDiag_lt_one {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} (hscale : ∀ slot, 0 < scale slot) (slot : Fin slotCount) :
    atomShiftedDiag atom scale slot < 1 := by
  simp only [atomShiftedDiag]
  linarith [atomGram_diag_le_one hframe slot, hscale slot]

/-- **THE DOMINATING PAIR OFF ONE SLOT.**  A rank-three frame whose
scales total less than one carries a dominating pair that misses any
prescribed light slot.  This is the region form of the selection theorem
at the complement of one slot, and it is the shape an extension argument
consumes. -/
theorem exists_dominating_pair_off_slot {slotCount : ℕ} {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (excluded : Fin slotCount)
    (hlight : atomGram atom excluded excluded + 2 * (∑ slot, scale slot)
      < 2 + 2 * scale excluded) :
    ∃ rowSlot ≠ excluded, ∃ colSlot ≠ excluded, rowSlot ≠ colSlot
      ∧ 0 < atomShiftedDiag atom scale rowSlot
      ∧ 0 < atomShiftedDiag atom scale colSlot
      ∧ 0 < atomPairMinor atom scale rowSlot colSlot := by
  classical
  have hdiagSplit : (∑ slot ∈ ({excluded} : Finset (Fin slotCount))ᶜ,
        atomGram atom slot slot) + atomGram atom excluded excluded = (3 : ℝ) := by
    rw [← Finset.sum_singleton (f := fun slot => atomGram atom slot slot) excluded,
      Finset.sum_compl_add_sum]
    rw [atomGram_trace hframe]; norm_num
  have hscaleSplit : (∑ slot ∈ ({excluded} : Finset (Fin slotCount))ᶜ, scale slot)
      + scale excluded = ∑ slot, scale slot := by
    rw [← Finset.sum_singleton (f := scale) excluded, Finset.sum_compl_add_sum]
  have hmass : 1 + 2 * (∑ slot ∈ ({excluded} : Finset (Fin slotCount))ᶜ, scale slot)
      < ∑ slot ∈ ({excluded} : Finset (Fin slotCount))ᶜ, atomGram atom slot slot := by
    linarith [hdiagSplit, hscaleSplit, hlight]
  obtain ⟨rowSlot, hrowMem, colSlot, hcolMem, hdiff, hrowPos, hcolPos, hminor⟩ :=
    exists_dominating_pair_on hframe hscale hmass
  refine ⟨rowSlot, ?_, colSlot, ?_, hdiff, hrowPos, hcolPos, hminor⟩
  · simpa using hrowMem
  · simpa using hcolMem

/-! ## Layer 5 — the positive read space -/

/-- The READ of an ambient direction at the slots: the coordinate of the
direction against each atom vector. -/
def atomRead {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (probe : Fin rank → ℝ) : Fin slotCount → ℝ :=
  fun slot => atom slot ⬝ᵥ probe

/-- The blend of a read is the direction itself.  This is the frame law
read as a reconstruction law. -/
theorem atomBlend_atomRead {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (probe : Fin rank → ℝ) : atomBlend atom (atomRead atom probe) = probe := by
  funext index
  rw [← dotProduct_probeUnit (atomBlend atom (atomRead atom probe)) index, atomBlend_dot]
  simp only [atomRead]
  rw [hframe probe (probeUnit index), dotProduct_probeUnit]

/-- The read of a nonzero direction is a nonzero slot vector. -/
theorem atomRead_ne_zero {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {probe : Fin rank → ℝ} (hne : probe ≠ 0) : atomRead atom probe ≠ 0 := by
  intro hzero
  refine hne ?_
  rw [← atomBlend_atomRead hframe probe, hzero]
  funext index
  simp only [atomBlend, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- **THE POSITIVE READ SPACE.**  The shifted Gram form is strictly
positive at the read of every nonzero direction.  Thus the shifted Gram
of a rank-three frame with scales of total less than one is positive
definite on a space of dimension three, and the atom triple ceiling asks
only whether one COORDINATE space of dimension three carries the same
positivity.  This is the exact statement of the residue gap. -/
theorem shifted_form_pos_on_reads {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) {probe : Fin rank → ℝ} (hne : probe ≠ 0) :
    (∑ slot, scale slot * atomRead atom probe slot ^ 2)
      < atomBlend atom (atomRead atom probe) ⬝ᵥ atomBlend atom (atomRead atom probe) := by
  classical
  have henergy : (∑ slot, atomRead atom probe slot ^ 2) = probe ⬝ᵥ probe := by
    simp only [atomRead, sq]
    exact hframe probe probe
  have hnormPos : 0 < probe ⬝ᵥ probe := by
    obtain ⟨index, hlive⟩ : ∃ index, probe index ≠ 0 := by
      by_contra hnone
      exact hne (funext fun index => not_not.mp fun hlt => hnone ⟨index, hlt⟩)
    rw [dotProduct]
    exact Finset.sum_pos' (fun _ _ => mul_self_nonneg _)
      ⟨index, Finset.mem_univ _, mul_self_pos.mpr hlive⟩
  have hcap : ∀ slot : Fin slotCount, scale slot ≤ ∑ other, scale other :=
    fun slot => Finset.single_le_sum (f := scale) (fun other _ => (hscale other).le)
      (Finset.mem_univ slot)
  have hbound : (∑ slot, scale slot * atomRead atom probe slot ^ 2)
      ≤ (∑ slot, scale slot) * (probe ⬝ᵥ probe) := by
    rw [← henergy, Finset.mul_sum]
    exact Finset.sum_le_sum fun slot _ =>
      mul_le_mul_of_nonneg_right (hcap slot) (sq_nonneg _)
  rw [atomBlend_atomRead hframe probe]
  nlinarith [hbound, hsmall, hnormPos]

/-! ## Layer 6 — the support calculus and the carrier discharge -/

/-- The sum of a slot function over an explicit two-slot carrier. -/
theorem sum_over_pair_slots {slotCount : ℕ} {slotOne slotTwo : Fin slotCount}
    (hne : slotOne ≠ slotTwo) (value : Fin slotCount → ℝ) :
    (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin slotCount)), value slot)
      = value slotOne + value slotTwo := Finset.sum_pair hne

/-- The sum of a slot function over an explicit three-slot carrier. -/
theorem sum_over_triple_slots {slotCount : ℕ} {slotOne slotTwo slotThree : Fin slotCount}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) (value : Fin slotCount → ℝ) :
    (∑ slot ∈ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)), value slot)
      = value slotOne + value slotTwo + value slotThree := by
  classical
  rw [Finset.sum_insert (by simp [honeTwo, honeThree]), sum_over_pair_slots htwoThree]
  ring

/-- A slot function supported on a two-slot carrier sums to its two
values. -/
theorem sum_eq_pair_of_support {slotCount : ℕ} {slotOne slotTwo : Fin slotCount}
    (hne : slotOne ≠ slotTwo) {value : Fin slotCount → ℝ}
    (hvanish : ∀ slot ∉ ({slotOne, slotTwo} : Finset (Fin slotCount)), value slot = 0) :
    (∑ slot, value slot) = value slotOne + value slotTwo := by
  classical
  rw [← sum_over_pair_slots hne value]
  exact (Finset.sum_subset (Finset.subset_univ _) fun slot _ hnot => hvanish slot hnot).symm

/-- A slot function supported on a three-slot carrier sums to its three
values. -/
theorem sum_eq_triple_of_support {slotCount : ℕ} {slotOne slotTwo slotThree : Fin slotCount}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) {value : Fin slotCount → ℝ}
    (hvanish : ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)),
      value slot = 0) :
    (∑ slot, value slot) = value slotOne + value slotTwo + value slotThree := by
  classical
  rw [← sum_over_triple_slots honeTwo honeThree htwoThree value]
  exact (Finset.sum_subset (Finset.subset_univ _) fun slot _ hnot => hvanish slot hnot).symm

/-- **THE PAIR CARRIER DISCHARGE.**  A dominating pair dominates every
nonzero vector of its own carrier. -/
theorem dominates_of_pair_minors {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo : Fin slotCount} (hne : slotOne ≠ slotTwo)
    (hdiag : 0 < atomShiftedDiag atom scale slotOne)
    (hminor : 0 < atomPairMinor atom scale slotOne slotTwo)
    {probe : Fin slotCount → ℝ}
    (hvanish : ∀ slot ∉ ({slotOne, slotTwo} : Finset (Fin slotCount)), probe slot = 0)
    (hprobe : probe ≠ 0) :
    (∑ slot, scale slot * probe slot ^ 2)
      < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  have hscaleSum : (∑ slot, scale slot * probe slot ^ 2)
      = scale slotOne * probe slotOne ^ 2 + scale slotTwo * probe slotTwo ^ 2 :=
    sum_eq_pair_of_support hne fun slot hnot => by rw [hvanish slot hnot]; ring
  have hgramSum : atomBlend atom probe ⬝ᵥ atomBlend atom probe
      = (probe slotOne * probe slotOne * atomGram atom slotOne slotOne
          + probe slotOne * probe slotTwo * atomGram atom slotOne slotTwo)
        + (probe slotTwo * probe slotOne * atomGram atom slotTwo slotOne
          + probe slotTwo * probe slotTwo * atomGram atom slotTwo slotTwo) := by
    rw [atomBlend_energy_eq_gram atom probe]
    have hinner : ∀ rowSlot : Fin slotCount,
        (∑ colSlot, probe rowSlot * probe colSlot * atomGram atom rowSlot colSlot)
          = probe rowSlot * probe slotOne * atomGram atom rowSlot slotOne
            + probe rowSlot * probe slotTwo * atomGram atom rowSlot slotTwo :=
      fun rowSlot => sum_eq_pair_of_support hne
        fun colSlot hnot => by rw [hvanish colSlot hnot, mul_zero, zero_mul]
    rw [Finset.sum_congr rfl fun rowSlot _ => hinner rowSlot]
    refine sum_eq_pair_of_support hne ?_
    intro rowSlot hnot
    rw [hvanish rowSlot hnot]
    ring
  have hlive : probe slotOne ≠ 0 ∨ probe slotTwo ≠ 0 := by
    by_contra hnone
    have hone : probe slotOne = 0 := not_not.mp fun hlt => hnone (Or.inl hlt)
    have htwo : probe slotTwo = 0 := not_not.mp fun hlt => hnone (Or.inr hlt)
    refine hprobe (funext fun slot => ?_)
    by_cases hmem : slot ∈ ({slotOne, slotTwo} : Finset (Fin slotCount))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hsel | hsel
      · rw [hsel, hone]; rfl
      · rw [hsel, htwo]; rfl
    · rw [hvanish slot hmem]; rfl
  have hpos := quadratic_pos_of_pair_minors (valueOne := probe slotOne)
    (valueTwo := probe slotTwo) hdiag hminor hlive
  have hidentity : (probe slotOne * probe slotOne * atomGram atom slotOne slotOne
        + probe slotOne * probe slotTwo * atomGram atom slotOne slotTwo)
      + (probe slotTwo * probe slotOne * atomGram atom slotTwo slotOne
        + probe slotTwo * probe slotTwo * atomGram atom slotTwo slotTwo)
      - (scale slotOne * probe slotOne ^ 2 + scale slotTwo * probe slotTwo ^ 2)
      = atomShiftedDiag atom scale slotOne * probe slotOne ^ 2
        + 2 * atomGram atom slotOne slotTwo * probe slotOne * probe slotTwo
        + atomShiftedDiag atom scale slotTwo * probe slotTwo ^ 2 := by
    simp only [atomShiftedDiag]
    rw [atomGram_comm atom slotTwo slotOne]
    ring
  rw [hgramSum, hscaleSum]
  linarith [hpos, hidentity]

/-- **THE TRIPLE CARRIER DISCHARGE.**  A positive nested minor chain on
three slots dominates every nonzero vector of that carrier.  This is the
passage from the polynomial residue to the quadratic residue, and it
carries no analysis. -/
theorem dominates_of_triple_minors {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hdiag : 0 < atomShiftedDiag atom scale slotOne)
    (hminor : 0 < atomPairMinor atom scale slotOne slotTwo)
    (hdet : 0 < atomTripleDet atom scale slotOne slotTwo slotThree)
    {probe : Fin slotCount → ℝ}
    (hvanish : ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)),
      probe slot = 0)
    (hprobe : probe ≠ 0) :
    (∑ slot, scale slot * probe slot ^ 2)
      < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
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
  have hlive : ¬(probe slotOne = 0 ∧ probe slotTwo = 0 ∧ probe slotThree = 0) := by
    rintro ⟨hone, htwo, hthree⟩
    refine hprobe (funext fun slot => ?_)
    by_cases hmem : slot ∈ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hsel | hsel | hsel
      · rw [hsel, hone]; rfl
      · rw [hsel, htwo]; rfl
      · rw [hsel, hthree]; rfl
    · rw [hvanish slot hmem]; rfl
  have hpos := quadratic_pos_of_triple_minors (valueOne := probe slotOne)
    (valueTwo := probe slotTwo) (valueThree := probe slotThree)
    (diagOne := atomShiftedDiag atom scale slotOne)
    (diagTwo := atomShiftedDiag atom scale slotTwo)
    (diagThree := atomShiftedDiag atom scale slotThree)
    (crossOneTwo := atomGram atom slotOne slotTwo)
    (crossOneThree := atomGram atom slotOne slotThree)
    (crossTwoThree := atomGram atom slotTwo slotThree)
    hdiag hminor hdet hlive
  have hidentity : ((probe slotOne * probe slotOne * atomGram atom slotOne slotOne
          + probe slotOne * probe slotTwo * atomGram atom slotOne slotTwo
          + probe slotOne * probe slotThree * atomGram atom slotOne slotThree)
        + (probe slotTwo * probe slotOne * atomGram atom slotTwo slotOne
          + probe slotTwo * probe slotTwo * atomGram atom slotTwo slotTwo
          + probe slotTwo * probe slotThree * atomGram atom slotTwo slotThree)
        + (probe slotThree * probe slotOne * atomGram atom slotThree slotOne
          + probe slotThree * probe slotTwo * atomGram atom slotThree slotTwo
          + probe slotThree * probe slotThree * atomGram atom slotThree slotThree))
      - (scale slotOne * probe slotOne ^ 2 + scale slotTwo * probe slotTwo ^ 2
        + scale slotThree * probe slotThree ^ 2)
      = atomShiftedDiag atom scale slotOne * probe slotOne ^ 2
        + atomShiftedDiag atom scale slotTwo * probe slotTwo ^ 2
        + atomShiftedDiag atom scale slotThree * probe slotThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * probe slotOne * probe slotTwo
        + 2 * atomGram atom slotOne slotThree * probe slotOne * probe slotThree
        + 2 * atomGram atom slotTwo slotThree * probe slotTwo * probe slotThree := by
    simp only [atomShiftedDiag]
    rw [atomGram_comm atom slotTwo slotOne, atomGram_comm atom slotThree slotOne,
      atomGram_comm atom slotThree slotTwo]
    ring
  rw [hgramSum, hscaleSum]
  linarith [hpos, hidentity]

/-! ## Layer 7 — the polynomial residue -/

/-- The carrier of three distinct slots has card three. -/
theorem card_triple_slots {slotCount : ℕ} {slotOne slotTwo slotThree : Fin slotCount}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) :
    ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)).card = 3 := by
  classical
  rw [Finset.card_insert_of_notMem (by simp [honeTwo, honeThree]),
    Finset.card_insert_of_notMem (by simp [htwoThree]), Finset.card_singleton]

/-- **THE POLYNOMIAL RESIDUE.**  Six vectors in three dimensions that
form a tight frame, together with six positive scales of total less than
one, carry three slots whose shifted Gram block has a positive nested
minor chain.

The statement has no quantifier over a continuum.  It is three
polynomial inequalities in the twenty-one Gram entries and the six
scales, thus a numeric certificate reads it directly.  The dominating
pair theorem supplies its first two links at every datum, thus the
residue is the DETERMINANT link only. -/
def AtomTripleSylvesterClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 < atomShiftedDiag atom scale slotOne
        ∧ 0 < atomPairMinor atom scale slotOne slotTwo
        ∧ 0 < atomTripleDet atom scale slotOne slotTwo slotThree

/-- **THE POLYNOMIAL RESIDUE CLOSES THE ATOM TRIPLE CEILING.** -/
theorem atomTripleCeilingClosed_of_sylvester
    (hresidue : AtomTripleSylvesterClosed) : AtomTripleCeilingClosed := by
  classical
  intro atom scale hpos hsmall hframe
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hdiag, hminor, hdet⟩ :=
    hresidue atom scale hpos hsmall hframe
  refine ⟨{slotOne, slotTwo, slotThree}, card_triple_slots honeTwo honeThree htwoThree,
    fun probe hvanish hne => ?_⟩
  exact dominates_of_triple_minors honeTwo honeThree htwoThree hdiag hminor hdet hvanish hne

/-- **THE FIRST TWO LINKS OF THE CHAIN ARE FREE.**  At every datum of the
residue the dominating pair theorem supplies a positive diagonal entry
and a positive pair minor, thus the residue asks for the determinant
link only. -/
theorem atomTripleSylvester_pair_free (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hpos : ∀ slot, 0 < scale slot) (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 0 < atomShiftedDiag atom scale slotOne
      ∧ 0 < atomShiftedDiag atom scale slotTwo
      ∧ 0 < atomPairMinor atom scale slotOne slotTwo :=
  exists_dominating_pair hframe hpos hsmall

/-- **THE DOMINATING PAIR CARRIER.**  The dominating pair of a
rank-three frame carries a two-slot subset on which the shifted form is
strictly positive at every nonzero vector. -/
theorem exists_dominating_pair_carrier {slotCount : ℕ} {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ car : Finset (Fin slotCount), car.card = 2
      ∧ ∀ probe : Fin slotCount → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  obtain ⟨slotOne, slotTwo, hne, hdiag, _, hminor⟩ := exists_dominating_pair hframe hscale hsmall
  refine ⟨{slotOne, slotTwo}, ?_, fun probe hvanish hprobe => ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  · exact dominates_of_pair_minors hne hdiag hminor hvanish hprobe

/-! ## Layer 8 — the crux readings and the rung -/

/-- **THE DOMINATING PAIR AT A RANK-SIX FRAME.**  Every rank-six frame of
a `(6,3)` crux carries two atoms whose shifted Gram block is positive
definite.  Interiority is a theorem at rank six, thus the reading is
unconditional. -/
theorem RankSixFrame.exists_dominating_pair {crux : SixThreeCrux} (frame : RankSixFrame crux) :
    ∃ (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo : Fin 6), slotOne ≠ slotTwo
      ∧ (∀ probe direction : Fin 3 → ℝ,
          (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
      ∧ 0 < atomShiftedDiag atom (fun slot =>
          chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight slot) slotOne
      ∧ 0 < atomShiftedDiag atom (fun slot =>
          chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight slot) slotTwo
      ∧ 0 < atomPairMinor atom (fun slot =>
          chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight slot) slotOne slotTwo := by
  classical
  obtain ⟨atom, hframe, _⟩ := crux.exists_atom_system
  have hsmall : (∑ slot : Fin 6, (chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight slot)) < 1 := by
    rw [frame.shifted_weight_sum]
    linarith [crux.hasNegativeChartValue]
  obtain ⟨slotOne, slotTwo, hne, hdiagOne, hdiagTwo, hminor⟩ :=
    _root_.Gtz.exists_dominating_pair hframe frame.shifted_weight_pos hsmall
  exact ⟨atom, slotOne, slotTwo, hne, hframe, hdiagOne, hdiagTwo, hminor⟩

/-- The rank-six direct kill from the polynomial residue. -/
theorem rankSixOuterKilled_of_sylvester
    (hresidue : AtomTripleSylvesterClosed) : RankSixOuterKilled :=
  rankSixOuterKilled_of_atomTripleCeiling (atomTripleCeilingClosed_of_sylvester hresidue)

/-- **THE RANK-SIX DISCHARGE FROM THE POLYNOMIAL RESIDUE.** -/
theorem rankSixSupportTwoClosed_of_sylvester
    (hresidue : AtomTripleSylvesterClosed) : RankSixSupportTwoClosed :=
  rankSixSupportTwoClosed_of_atomTripleCeiling (atomTripleCeilingClosed_of_sylvester hresidue)

/-- The circuit residue of the outer-zero lattice from the polynomial
residue. -/
theorem rankSixOuterCircuitClosed_of_sylvester
    (hresidue : AtomTripleSylvesterClosed) : RankSixOuterCircuitClosed :=
  rankSixOuterCircuitClosed_of_atomTripleCeiling (atomTripleCeilingClosed_of_sylvester hresidue)

/-- The regular residue of the outer-zero lattice from the polynomial
residue. -/
theorem rankSixOuterRegularClosed_of_sylvester
    (hresidue : AtomTripleSylvesterClosed) : RankSixOuterRegularClosed :=
  rankSixOuterRegularClosed_of_atomTripleCeiling (atomTripleCeilingClosed_of_sylvester hresidue)

/-- The thin residue of the outer-zero lattice from the polynomial
residue. -/
theorem rankSixOuterThinClosed_of_sylvester
    (hresidue : AtomTripleSylvesterClosed) : RankSixOuterThinClosed :=
  rankSixOuterThinClosed_of_atomTripleCeiling (atomTripleCeilingClosed_of_sylvester hresidue)

/-- **THE WHOLE `(6,3)` STATEMENT FROM THE POLYNOMIAL RESIDUE AND
INTERIORITY.** -/
theorem gtzWeighted_six_three_of_sylvester_of_interior
    (hresidue : AtomTripleSylvesterClosed)
    (hinterior : ∀ crux : SixThreeCrux, ∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomTripleCeiling_of_interior
    (atomTripleCeilingClosed_of_sylvester hresidue) hinterior

/-- The rank-five support-two closure from the polynomial residue and
interiority. -/
theorem rankFiveSupportTwoClosed_of_sylvester_of_interior
    (hresidue : AtomTripleSylvesterClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (atomIndex : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFiveSupportTwoClosed :=
  rankFiveSupportTwoClosed_of_atomTripleCeiling_of_interior
    (atomTripleCeilingClosed_of_sylvester hresidue) hinterior

/-- The rank-four support-two closure from the polynomial residue and
interiority. -/
theorem rankFourSupportTwoClosed_of_sylvester_of_interior
    (hresidue : AtomTripleSylvesterClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (atomIndex : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_atomTripleCeiling_of_interior
    (atomTripleCeilingClosed_of_sylvester hresidue) hinterior

/-! ## Layer 9 — the extension calculus -/

/-- The SCHUR LEAK of a third slot against a pair: the part of the pair
minor that the cross entries of the third slot spend. -/
def atomSchurLeak {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  atomShiftedDiag atom scale slotOne * atomGram atom slotTwo slotThree ^ 2
    - 2 * atomGram atom slotOne slotTwo * atomGram atom slotOne slotThree
        * atomGram atom slotTwo slotThree
    + atomShiftedDiag atom scale slotTwo * atomGram atom slotOne slotThree ^ 2

/-- **THE SCHUR FACTORIZATION.**  The determinant of a three-slot block
is the shifted diagonal of the third slot against the pair minor, minus
the Schur leak of that slot.  Thus a dominating pair extends exactly
when one slot pays more than it leaks. -/
theorem atomTripleDet_schur {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slotOne slotTwo slotThree : Fin slotCount) :
    atomTripleDet atom scale slotOne slotTwo slotThree
      = atomShiftedDiag atom scale slotThree * atomPairMinor atom scale slotOne slotTwo
        - atomSchurLeak atom scale slotOne slotTwo slotThree := by
  simp only [atomTripleDet, atomPairMinor, atomSchurLeak]
  ring

/-- **THE SCHUR LEAK TOTAL.**  The Schur leak of a pair sums over all
slots to one exact expression in the two diagonal entries, the two
shifted diagonal entries and the cross entry of that pair.  The proof is
the row energy law at each slot of the pair and the idempotence law at
the pair. -/
theorem atomSchurLeak_total {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (slotOne slotTwo : Fin slotCount) :
    (∑ slotThree, atomSchurLeak atom scale slotOne slotTwo slotThree)
      = atomShiftedDiag atom scale slotOne * atomGram atom slotTwo slotTwo
        - 2 * atomGram atom slotOne slotTwo ^ 2
        + atomShiftedDiag atom scale slotTwo * atomGram atom slotOne slotOne := by
  classical
  have hcross : (∑ slotThree, atomGram atom slotOne slotThree * atomGram atom slotTwo slotThree)
      = atomGram atom slotOne slotTwo := by
    rw [← atomGram_idempotent hframe slotOne slotTwo]
    exact Finset.sum_congr rfl fun slotThree _ => by
      rw [atomGram_comm atom slotTwo slotThree]
  have hsplit : ∀ slotThree : Fin slotCount,
      atomSchurLeak atom scale slotOne slotTwo slotThree
        = atomShiftedDiag atom scale slotOne * atomGram atom slotTwo slotThree ^ 2
          - 2 * atomGram atom slotOne slotTwo
              * (atomGram atom slotOne slotThree * atomGram atom slotTwo slotThree)
          + atomShiftedDiag atom scale slotTwo * atomGram atom slotOne slotThree ^ 2 := by
    intro slotThree
    simp only [atomSchurLeak]
    ring
  rw [Finset.sum_congr rfl fun slotThree _ => hsplit slotThree, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    hcross, atomGram_row_energy hframe slotTwo, atomGram_row_energy hframe slotOne]
  ring

/-- **THE DETERMINANT TOTAL OF A PAIR.**  The three-slot determinants of
one pair sum over all slots to the shifted diagonal mass against the
pair minor, minus the Schur leak total.  This is the exact averaged
price of an extension. -/
theorem atomTripleDet_total {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (slotOne slotTwo : Fin slotCount) :
    (∑ slotThree, atomTripleDet atom scale slotOne slotTwo slotThree)
      = ((rank : ℝ) - ∑ slot, scale slot) * atomPairMinor atom scale slotOne slotTwo
        - (atomShiftedDiag atom scale slotOne * atomGram atom slotTwo slotTwo
          - 2 * atomGram atom slotOne slotTwo ^ 2
          + atomShiftedDiag atom scale slotTwo * atomGram atom slotOne slotOne) := by
  classical
  rw [Finset.sum_congr rfl fun slotThree _ =>
      atomTripleDet_schur atom scale slotOne slotTwo slotThree,
    Finset.sum_sub_distrib, ← Finset.sum_mul, atomShiftedDiag_total hframe scale,
    atomSchurLeak_total hframe scale slotOne slotTwo]

/-- **THE EXTENSION CRITERION.**  If the shifted diagonal mass of a
region beats the Schur leak of that region against a pair, then one slot
of the region extends the pair to a positive determinant. -/
theorem exists_extending_slot {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {slotOne slotTwo : Fin slotCount}
    {region : Finset (Fin slotCount)}
    (hmargin : (∑ slotThree ∈ region, atomSchurLeak atom scale slotOne slotTwo slotThree)
      < (∑ slotThree ∈ region, atomShiftedDiag atom scale slotThree)
        * atomPairMinor atom scale slotOne slotTwo) :
    ∃ slotThree ∈ region, 0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  classical
  by_contra hcontra
  have hnone : ∀ slotThree ∈ region,
      atomShiftedDiag atom scale slotThree * atomPairMinor atom scale slotOne slotTwo
        ≤ atomSchurLeak atom scale slotOne slotTwo slotThree := by
    intro slotThree hmem
    have hle : atomTripleDet atom scale slotOne slotTwo slotThree ≤ 0 := by
      by_contra hlt
      exact hcontra ⟨slotThree, hmem, not_le.mp hlt⟩
    rw [atomTripleDet_schur atom scale slotOne slotTwo slotThree] at hle
    linarith [hle]
  have hsum : (∑ slotThree ∈ region, atomShiftedDiag atom scale slotThree)
      * atomPairMinor atom scale slotOne slotTwo
      ≤ ∑ slotThree ∈ region, atomSchurLeak atom scale slotOne slotTwo slotThree := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hnone
  exact absurd hsum (not_le.mpr hmargin)

/-- **THE SYLVESTER CHAIN FROM AN EXTENSION MARGIN.**  A dominating pair
together with a region that misses the pair and beats its Schur leak
supplies the whole nested minor chain, thus a dominating triple. -/
theorem exists_sylvester_chain_of_extension {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo : Fin slotCount} {region : Finset (Fin slotCount)}
    (hscale : 0 < scale slotOne) (hdiag : 0 < atomShiftedDiag atom scale slotOne)
    (hminor : 0 < atomPairMinor atom scale slotOne slotTwo)
    (honeOff : slotOne ∉ region) (htwoOff : slotTwo ∉ region)
    (hmargin : (∑ slotThree ∈ region, atomSchurLeak atom scale slotOne slotTwo slotThree)
      < (∑ slotThree ∈ region, atomShiftedDiag atom scale slotThree)
        * atomPairMinor atom scale slotOne slotTwo) :
    ∃ slotThree : Fin slotCount, slotOne ≠ slotTwo ∧ slotOne ≠ slotThree
      ∧ slotTwo ≠ slotThree
      ∧ 0 < atomShiftedDiag atom scale slotOne
      ∧ 0 < atomPairMinor atom scale slotOne slotTwo
      ∧ 0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  classical
  obtain ⟨slotThree, hmem, hdet⟩ := exists_extending_slot hmargin
  have honeTwo : slotOne ≠ slotTwo := by
    intro hsame
    rw [← hsame] at hminor
    simp only [atomPairMinor, atomShiftedDiag] at hminor
    simp only [atomShiftedDiag] at hdiag
    nlinarith [hminor, hdiag, hscale, atomGram_diag_nonneg atom slotOne]
  exact ⟨slotThree, honeTwo, fun hsame => honeOff (hsame ▸ hmem),
    fun hsame => htwoOff (hsame ▸ hmem), hdiag, hminor, hdet⟩

/-! ## Layer 10 — the descent start -/

/-- **THE FULL FRAME DOMINATES.**  Read the reciprocal scales against the
atom energies of any direction.  The whole slot set beats the ambient
square norm at every nonzero direction, and the only inputs are the
frame law and a scale total below one.

This is the START of a descent.  The atom triple ceiling asks for a
carrier of card `rank`, and the full slot set already dominates, thus
the residue of the third rung is one ROUNDING law: shrink a dominating
slot set to card `rank` and keep the domination.  The same rounding law
is the open drop condition of the hinge arm, whose refutation of the
bare shrink route (three atoms in two dimensions, a positive total and
no positive pair) has scale total `7/4`, thus it does NOT refute the
frame-constrained law that this layer starts. -/
theorem atom_full_frame_dominates {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) (coeff : Fin slotCount → ℝ)
    (hcoeff : ∀ slot, coeff slot * scale slot = 1)
    {direction : Fin rank → ℝ} (hne : direction ≠ 0) :
    direction ⬝ᵥ direction < ∑ slot, coeff slot * (atom slot ⬝ᵥ direction) ^ 2 := by
  classical
  have henergy : (∑ slot, (atom slot ⬝ᵥ direction) ^ 2) = direction ⬝ᵥ direction := by
    simp only [sq]
    exact hframe direction direction
  have hnormPos : 0 < direction ⬝ᵥ direction := by
    obtain ⟨index, hlive⟩ : ∃ index, direction index ≠ 0 := by
      by_contra hnone
      exact hne (funext fun index => not_not.mp fun hlt => hnone ⟨index, hlt⟩)
    rw [dotProduct]
    exact Finset.sum_pos' (fun _ _ => mul_self_nonneg _)
      ⟨index, Finset.mem_univ _, mul_self_pos.mpr hlive⟩
  have hnonempty : (Finset.univ : Finset (Fin slotCount)).Nonempty := by
    rcases (Finset.univ : Finset (Fin slotCount)).eq_empty_or_nonempty with hempty | hsome
    · exfalso
      rw [← henergy, hempty, Finset.sum_empty] at hnormPos
      exact absurd hnormPos (lt_irrefl 0)
    · exact hsome
  have htotalPos : 0 < ∑ slot, scale slot :=
    Finset.sum_pos (fun slot _ => hscale slot) hnonempty
  have hcap : ∀ slot : Fin slotCount, scale slot ≤ ∑ other, scale other :=
    fun slot => Finset.single_le_sum (f := scale) (fun other _ => (hscale other).le)
      (Finset.mem_univ slot)
  have hcoeffPos : ∀ slot : Fin slotCount, 0 < coeff slot := by
    intro slot
    by_contra hnot
    have hle : coeff slot ≤ 0 := not_lt.mp hnot
    nlinarith [hcoeff slot, hscale slot, hle]
  have hone : ∀ slot : Fin slotCount, 1 ≤ coeff slot * ∑ other, scale other := by
    intro slot
    have := mul_le_mul_of_nonneg_left (hcap slot) (hcoeffPos slot).le
    rw [hcoeff slot] at this
    exact this
  have hbound : (∑ slot, (atom slot ⬝ᵥ direction) ^ 2)
      ≤ (∑ other, scale other) * ∑ slot, coeff slot * (atom slot ⬝ᵥ direction) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun slot _ => ?_
    have hstep := mul_le_mul_of_nonneg_right (hone slot) (sq_nonneg (atom slot ⬝ᵥ direction))
    calc (atom slot ⬝ᵥ direction) ^ 2
        = 1 * (atom slot ⬝ᵥ direction) ^ 2 := by ring
      _ ≤ (coeff slot * ∑ other, scale other) * (atom slot ⬝ᵥ direction) ^ 2 := hstep
      _ = (∑ other, scale other) * (coeff slot * (atom slot ⬝ᵥ direction) ^ 2) := by ring
  rw [henergy] at hbound
  nlinarith [hbound, hsmall, hnormPos, htotalPos]

/-- **THE FRAME-CONSTRAINED DROP.**  The rounding law that the descent
needs: a dominating slot set of card more than three, at a frame with
scales of total less than one, has a slot that the domination can spare.
This is the design-constrained form of the hinge arm drop condition, and
the two programs share it. -/
def AtomFrameDropClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) (coeff : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ slot, coeff slot * scale slot = 1) →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∀ region : Finset (Fin 6), 3 < region.card →
      (∀ direction : Fin 3 → ℝ, direction ≠ 0 →
        direction ⬝ᵥ direction < ∑ slot ∈ region, coeff slot * (atom slot ⬝ᵥ direction) ^ 2) →
      ∃ dropped ∈ region, ∀ direction : Fin 3 → ℝ, direction ≠ 0 →
        direction ⬝ᵥ direction
          < ∑ slot ∈ region.erase dropped, coeff slot * (atom slot ⬝ᵥ direction) ^ 2

/-- The full slot set of a rank-three frame starts the descent: it is a
dominating region of card six. -/
theorem atom_univ_dominates {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin 6 → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) (coeff : Fin 6 → ℝ)
    (hcoeff : ∀ slot, coeff slot * scale slot = 1) :
    ∀ direction : Fin 3 → ℝ, direction ≠ 0 →
      direction ⬝ᵥ direction
        < ∑ slot ∈ (Finset.univ : Finset (Fin 6)), coeff slot * (atom slot ⬝ᵥ direction) ^ 2 :=
  fun _direction hne => atom_full_frame_dominates hframe hscale hsmall coeff hcoeff hne

end Gtz
