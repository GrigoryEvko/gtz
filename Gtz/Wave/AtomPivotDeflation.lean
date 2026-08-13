import Gtz.Wave.AtomGramSelection
import Gtz.Wave.DenseCeilingCollapse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The pivot deflation and the pair extension total — the third rung becomes a pair search

The dense collapse layer removed the last side hypothesis from the atom
triple ceiling: that ceiling ALONE closes the `(6,3)` cell.  The selection
layer removed the continuum from the ceiling and reduced it to a Sylvester
chain whose first two links are free at every datum.  One link is open,
and it is the DETERMINANT of one three-slot block.

This module prices that link exactly, and it lowers its rank.

The first law is the DEFLATION.  The determinant of a three-slot block,
scaled by the shifted diagonal of one slot of the block, is the difference
of two squares: the product of the two pair minors that the slot carries,
minus the square of one cross expression.  Thus a slot with a positive
shifted diagonal turns the ceiling into a PAIR test in the deflated Gram,
and the search over twenty triples becomes a search over fifteen pairs
after one pivot.  The deflated pair test is the plane pair test of the
dense collapse layer, with the pivot energy in place of the plane.

The second law is the PAIR EXTENSION TOTAL.  The three-slot determinants
of one fixed pair, summed over every OTHER slot, have a closed form: the
rank minus two minus the scale mass, against the pair minor, minus three
explicit correction terms in the two diagonal entries, the cross entry and
the two scales of the pair.  The row energy law and the idempotence law
carry the whole proof.  Two readings follow.  At a pair of vanishing
scales the total is the scale gap against the pair minor, thus **a
dominating pair of vanishing scales always extends to a dominating
triple**.  At a general pair the total is a margin that a certificate
reads directly, and it is TIGHT: at the regular tetrahedron with four
equal atoms and four equal scales the margin is zero exactly at scale mass
one.

The third law is the LIGHT PIVOT.  Some slot pays at most the scale share
of the rank: the shifted diagonal of that slot beats its own scale by the
factor `(rank - mass) / mass`.  Thus a pivot with a positive shifted
diagonal always exists, and it is quantitatively light.

The last law is a REFUTATION.  The frame-constrained drop — the shared
residue of this program and of the mass-gap descent — is FALSE.  Four
atoms of a tight frame with rational entries dominate the probe space,
and no single atom of the four can be dropped.  The descent from a
dominating region of card four to a dominating triple does not exist, thus
no successor must look for it.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomPivotCross` — the deflated cross entry of a pivot.
* `Gtz.atomTripleDet_deflate` — **THE DEFLATION**: the Dodgson identity of
  the shifted Gram block.
* `Gtz.atomTripleDet_pos_of_deflated_pair` — the deflated pair test
  supplies the determinant link.
* `Gtz.exists_sylvester_chain_of_deflated_pair` — the whole Sylvester
  chain from one pivot and one deflated pair.
* `Gtz.atomTripleDet_pair_region_total` — **THE PAIR EXTENSION TOTAL.**
* `Gtz.atomTripleDet_pair_region_total_three` — its rank-three reading.
* `Gtz.exists_extending_slot_of_margin` — a positive total supplies an
  extending slot.
* `Gtz.exists_sylvester_chain_of_pair_margin` — **THE MARGIN CRITERION.**
* `Gtz.exists_sylvester_chain_of_light_pair` — **THE ZERO-SCALE PAIR
  EXTENDS**, with no margin hypothesis at all.
* `Gtz.pairMinor_eq_gram_triple_total` — the pair minor of a frame is the
  total of the unshifted three-slot determinants of that pair.
* `Gtz.exists_light_pivot` — **THE LIGHT PIVOT.**
* `Gtz.exists_pivot_shiftedDiag_pos` — a pivot of positive shifted
  diagonal always exists.
* `Gtz.AtomPivotPairClosed` — **THE PIVOT PAIR RESIDUE**, the third rung
  as a pair search.
* `Gtz.atomTripleSylvesterClosed_of_pivotPair`,
  `Gtz.atomTripleCeilingClosed_of_pivotPair`,
  `Gtz.gtzWeighted_six_three_of_pivotPair`,
  `Gtz.gtzWeightedAll_three_of_pivotPair` — **THE CELL FROM THE PIVOT
  PAIR RESIDUE**, with no side hypothesis.
* `Gtz.rankFiveDenseClosed_of_pivotPair`,
  `Gtz.rankSixDenseClosed_of_pivotPair`,
  `Gtz.rankSixSupportTwoClosed_of_pivotPair`,
  `Gtz.rankFiveSupportTwoClosed_of_pivotPair`,
  `Gtz.rankFourSupportTwoClosed_of_pivotPair` — the dense branches and the
  support-two closures from the same residue.
* `Gtz.dropAtom`, `Gtz.dropScale`, `Gtz.dropCoeff`, `Gtz.dropRegion` —
  the refuting datum, with `Gtz.dropAtom_frame`, `Gtz.dropScale_sum`,
  `Gtz.dropRegion_dominates`.
* `Gtz.not_atomFrameDropClosed` — **THE FRAME DROP IS FALSE.**
* `Gtz.atomGramMinor`, `Gtz.atomGramVolume` — the squared area of a pair
  and the squared volume of a triple, with
  `Gtz.atomGramMinor_eq_pairMinor`, `Gtz.atomGramVolume_eq_tripleDet`,
  `Gtz.atomGramMinor_nonneg` and the three degeneracy laws
  `Gtz.atomGramVolume_repeat_left`, `Gtz.atomGramVolume_repeat_outer`,
  `Gtz.atomGramVolume_repeat_right`.
* `Gtz.atomGramMinor_eq_volume_total` — **THE PAIR VOLUME LAW**: the
  volumes of one pair total the area of that pair.
* `Gtz.pairMinor_mul_form_ge_det_mul_sq` — **THE COORDINATE
  CAUCHY-SCHWARZ** of a symmetric block of dimension three.
* `Gtz.atomBlend_energy_triple` — the blend energy of a three-slot
  carrier.
* `Gtz.dominates_of_trace_certificate` — **THE TRACE CERTIFICATE**, the
  first domination criterion that is LINEAR in the scales.
* `Gtz.atomGramMinor_pos_of_pairMinor_pos` — a dominating pair has a
  positive Gram minor.
* `Gtz.exists_maximal_volume_triple` — **THE MAXIMAL VOLUME TRIPLE**
  exists and is nondegenerate.
* `Gtz.atomGramMinor_le_four_mul_volume` — every area is capped by four
  maximal volumes.
* `Gtz.exists_dominating_triple_of_scale_lt_quarter` — **THE QUARTER
  THRESHOLD**: the atom triple ceiling holds at every scale mass below one
  quarter.

## Vacuity

Every law of layers zero thru three is an unconditional statement about a
family of vectors and a family of scales.  The refutation is a statement
about one explicit rational datum, thus it is vacuous under no hypothesis.
-/

namespace Gtz

/-! ## Layer 0 — the deflation of a triple determinant -/

/-- The DEFLATED CROSS ENTRY of two slots against a pivot: the cross entry
of the pair, scaled by the shifted diagonal of the pivot, minus the
product of the two cross entries that the pivot carries. -/
def atomPivotCross {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot slotOne slotTwo : Fin slotCount) : ℝ :=
  atomShiftedDiag atom scale pivot * atomGram atom slotOne slotTwo
    - atomGram atom pivot slotOne * atomGram atom pivot slotTwo

/-- **THE DEFLATION.**  The three-slot determinant, scaled by the shifted
diagonal of its first slot, is the product of the two pair minors of that
slot against the difference of one square.  This is the Dodgson identity
of the shifted Gram block, and it turns the determinant link of the third
rung into a PAIR test in the deflated Gram. -/
theorem atomTripleDet_deflate {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot slotOne slotTwo : Fin slotCount) :
    atomShiftedDiag atom scale pivot * atomTripleDet atom scale pivot slotOne slotTwo
      = atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo
        - atomPivotCross atom scale pivot slotOne slotTwo ^ 2 := by
  simp only [atomTripleDet, atomPairMinor, atomPivotCross]
  ring

/-- **THE DEFLATED PAIR TEST SUPPLIES THE DETERMINANT LINK.**  A pivot of
positive shifted diagonal, two slots whose pivot minors have a positive
product and whose deflated cross entry is small, give a positive
three-slot determinant. -/
theorem atomTripleDet_pos_of_deflated_pair {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {pivot slotOne slotTwo : Fin slotCount}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hdeflate : atomPivotCross atom scale pivot slotOne slotTwo ^ 2
      < atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo) :
    0 < atomTripleDet atom scale pivot slotOne slotTwo := by
  have hscaled : 0 < atomShiftedDiag atom scale pivot
      * atomTripleDet atom scale pivot slotOne slotTwo := by
    rw [atomTripleDet_deflate atom scale pivot slotOne slotTwo]
    linarith [hdeflate]
  by_contra hnot
  nlinarith [hscaled, hpivot, not_lt.mp hnot]

/-- **THE SYLVESTER CHAIN FROM ONE PIVOT AND ONE DEFLATED PAIR.**  The
whole nested minor chain of the third rung comes from a pivot of positive
shifted diagonal, one positive pivot minor and one deflated pair test. -/
theorem exists_sylvester_chain_of_deflated_pair {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {pivot slotOne slotTwo : Fin slotCount}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hminor : 0 < atomPairMinor atom scale pivot slotOne)
    (hdeflate : atomPivotCross atom scale pivot slotOne slotTwo ^ 2
      < atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo) :
    0 < atomShiftedDiag atom scale pivot
      ∧ 0 < atomPairMinor atom scale pivot slotOne
      ∧ 0 < atomTripleDet atom scale pivot slotOne slotTwo :=
  ⟨hpivot, hminor, atomTripleDet_pos_of_deflated_pair hpivot hdeflate⟩

/-! ## Layer 1 — the pair extension total -/

/-- The CORRECTION of a pair: the exact price that the two scales of the
pair charge against the extension of that pair. -/
def atomPairCorrection {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slotOne slotTwo : Fin slotCount) : ℝ :=
  atomShiftedDiag atom scale slotOne * scale slotTwo
      * (1 - atomGram atom slotTwo slotTwo - atomShiftedDiag atom scale slotTwo)
    + atomShiftedDiag atom scale slotTwo * scale slotOne
      * (1 - atomGram atom slotOne slotOne - atomShiftedDiag atom scale slotOne)
    + 2 * atomGram atom slotOne slotTwo ^ 2 * (scale slotOne + scale slotTwo)

/-- **THE PAIR EXTENSION TOTAL.**  The three-slot determinants of one pair,
summed over every slot OUTSIDE the pair, have a closed form: the rank
minus two minus the scale mass, against the pair minor, minus the
correction of the pair.

The row energy law and the idempotence law carry the whole proof, thus the
identity holds at every rank and at every slot count.  The identity is
TIGHT: at the regular tetrahedron with four equal atoms of diagonal three
quarters and four equal scales the total is zero exactly at scale mass
one. -/
theorem atomTripleDet_pair_region_total {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) {slotOne slotTwo : Fin slotCount} (hne : slotOne ≠ slotTwo) :
    (∑ slotThree ∈ ((Finset.univ.erase slotOne).erase slotTwo),
        atomTripleDet atom scale slotOne slotTwo slotThree)
      = ((rank : ℝ) - 2 - ∑ slot, scale slot) * atomPairMinor atom scale slotOne slotTwo
        - atomPairCorrection atom scale slotOne slotTwo := by
  classical
  have hmem : slotTwo ∈ (Finset.univ : Finset (Fin slotCount)).erase slotOne :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  rw [Finset.sum_erase_eq_sub hmem, Finset.sum_erase_eq_sub (Finset.mem_univ slotOne),
    atomTripleDet_total hframe scale slotOne slotTwo]
  simp only [atomTripleDet, atomPairMinor, atomPairCorrection, atomShiftedDiag]
  rw [atomGram_comm atom slotTwo slotOne]
  ring

/-- The rank-three reading of the pair extension total: the scale gap
against the pair minor, minus the correction. -/
theorem atomTripleDet_pair_region_total_three {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) {slotOne slotTwo : Fin slotCount} (hne : slotOne ≠ slotTwo) :
    (∑ slotThree ∈ ((Finset.univ.erase slotOne).erase slotTwo),
        atomTripleDet atom scale slotOne slotTwo slotThree)
      = (1 - ∑ slot, scale slot) * atomPairMinor atom scale slotOne slotTwo
        - atomPairCorrection atom scale slotOne slotTwo := by
  rw [atomTripleDet_pair_region_total hframe scale hne]
  norm_num

/-- **THE PAIR MINOR IS A DETERMINANT TOTAL.**  At vanishing scales the
extension total of a pair of a rank-three frame is exactly the Gram minor
of that pair.  This is the determinantal law of a projection read at one
pair: the squared volumes of the triples that contain the pair total the
squared area of the pair. -/
theorem pairMinor_eq_gram_triple_total {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {slotOne slotTwo : Fin slotCount} (hne : slotOne ≠ slotTwo) :
    (∑ slotThree ∈ ((Finset.univ.erase slotOne).erase slotTwo),
        atomTripleDet atom (fun _ => 0) slotOne slotTwo slotThree)
      = atomGram atom slotOne slotOne * atomGram atom slotTwo slotTwo
        - atomGram atom slotOne slotTwo ^ 2 := by
  rw [atomTripleDet_pair_region_total_three hframe (fun _ => 0) hne]
  simp only [atomPairCorrection, atomPairMinor, atomShiftedDiag, Finset.sum_const_zero]
  ring

/-! ## Layer 2 — the margin criteria -/

/-- A positive extension total supplies a slot outside the pair whose
three-slot determinant is positive. -/
theorem exists_extending_slot_of_margin {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) {slotOne slotTwo : Fin slotCount} (hne : slotOne ≠ slotTwo)
    (hmargin : atomPairCorrection atom scale slotOne slotTwo
      < ((rank : ℝ) - 2 - ∑ slot, scale slot) * atomPairMinor atom scale slotOne slotTwo) :
    ∃ slotThree, slotThree ≠ slotOne ∧ slotThree ≠ slotTwo
      ∧ 0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  classical
  by_contra hcontra
  have hnone : ∀ slotThree ∈ ((Finset.univ.erase slotOne).erase slotTwo),
      atomTripleDet atom scale slotOne slotTwo slotThree ≤ 0 := by
    intro slotThree hmem
    have hone : slotThree ≠ slotOne :=
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hmem)).1
    have htwo : slotThree ≠ slotTwo := (Finset.mem_erase.mp hmem).1
    by_contra hlt
    exact hcontra ⟨slotThree, hone, htwo, not_le.mp hlt⟩
  have hsum := Finset.sum_nonpos hnone
  rw [atomTripleDet_pair_region_total hframe scale hne] at hsum
  linarith [hsum, hmargin]

/-- **THE MARGIN CRITERION.**  A dominating pair whose extension total is
positive supplies the whole Sylvester chain, thus a dominating triple.
The margin is one polynomial inequality in five Gram entries and two
scales, and it is exact: no estimate enters its proof. -/
theorem exists_sylvester_chain_of_pair_margin {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) {slotOne slotTwo : Fin slotCount} (hne : slotOne ≠ slotTwo)
    (hdiag : 0 < atomShiftedDiag atom scale slotOne)
    (hminor : 0 < atomPairMinor atom scale slotOne slotTwo)
    (hmargin : atomPairCorrection atom scale slotOne slotTwo
      < ((rank : ℝ) - 2 - ∑ slot, scale slot) * atomPairMinor atom scale slotOne slotTwo) :
    ∃ slotThree, slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
      ∧ 0 < atomShiftedDiag atom scale slotOne
      ∧ 0 < atomPairMinor atom scale slotOne slotTwo
      ∧ 0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  obtain ⟨slotThree, hone, htwo, hdet⟩ :=
    exists_extending_slot_of_margin hframe scale hne hmargin
  exact ⟨slotThree, hne, fun heq => hone heq.symm, fun heq => htwo heq.symm, hdiag, hminor, hdet⟩

/-- **THE ZERO-SCALE PAIR EXTENDS.**  A dominating pair whose two scales
vanish always extends to a dominating triple, with no margin hypothesis:
the correction of such a pair is zero and the scale mass of a rank-three
frame is less than one.

This is the boundary reading of the pair extension total, and it is the
first unconditional extension law of the campaign. -/
theorem exists_sylvester_chain_of_light_pair {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} (hsmall : (∑ slot, scale slot) < 1)
    {slotOne slotTwo : Fin slotCount} (hne : slotOne ≠ slotTwo)
    (hzeroOne : scale slotOne = 0) (hzeroTwo : scale slotTwo = 0)
    (hdiag : 0 < atomShiftedDiag atom scale slotOne)
    (hminor : 0 < atomPairMinor atom scale slotOne slotTwo) :
    ∃ slotThree, slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
      ∧ 0 < atomShiftedDiag atom scale slotOne
      ∧ 0 < atomPairMinor atom scale slotOne slotTwo
      ∧ 0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  refine exists_sylvester_chain_of_pair_margin hframe scale hne hdiag hminor ?_
  have hcorrection : atomPairCorrection atom scale slotOne slotTwo = 0 := by
    simp only [atomPairCorrection, hzeroOne, hzeroTwo]
    ring
  have hrank : ((3 : ℕ) : ℝ) - 2 - ∑ slot, scale slot = 1 - ∑ slot, scale slot := by norm_num
  rw [hcorrection, hrank]
  exact mul_pos (by linarith [hsmall]) hminor

/-! ## Layer 3 — the light pivot -/

/-- **THE LIGHT PIVOT.**  Some slot of a frame with positive scales of
total less than the rank pays at most the scale share of the rank: its
scale, against the rank minus the scale mass, is capped by the scale mass
against its own shifted diagonal.  Such a slot has a POSITIVE shifted
diagonal, thus it is a pivot.

The proof is the shifted diagonal budget and one pigeonhole: if every slot
failed the cap, the scale mass would exceed itself. -/
theorem exists_light_pivot {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hnonempty : (Finset.univ : Finset (Fin slotCount)).Nonempty)
    (hsmall : (∑ slot, scale slot) < (rank : ℝ)) :
    ∃ pivot, scale pivot * ((rank : ℝ) - ∑ slot, scale slot)
        ≤ (∑ slot, scale slot) * atomShiftedDiag atom scale pivot
      ∧ 0 < atomShiftedDiag atom scale pivot := by
  classical
  have hmassPos : 0 < ∑ slot, scale slot :=
    Finset.sum_pos (fun slot _ => hscale slot) hnonempty
  have hgapPos : 0 < (rank : ℝ) - ∑ slot, scale slot := by linarith [hsmall]
  obtain ⟨pivot, hcap⟩ : ∃ pivot, scale pivot * ((rank : ℝ) - ∑ slot, scale slot)
      ≤ (∑ slot, scale slot) * atomShiftedDiag atom scale pivot := by
    by_contra hcontra
    have hstrict : ∀ slot : Fin slotCount,
        (∑ other, scale other) * atomShiftedDiag atom scale slot
          < scale slot * ((rank : ℝ) - ∑ other, scale other) := by
      intro slot
      by_contra hle
      exact hcontra ⟨slot, not_lt.mp hle⟩
    have htotal : (∑ other, scale other) * (∑ slot, atomShiftedDiag atom scale slot)
        < (∑ slot, scale slot) * ((rank : ℝ) - ∑ other, scale other) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_lt_sum_of_nonempty hnonempty fun slot _ => hstrict slot
    rw [atomShiftedDiag_total hframe scale] at htotal
    exact absurd htotal (by linarith)
  refine ⟨pivot, hcap, ?_⟩
  by_contra hnot
  have hle : atomShiftedDiag atom scale pivot ≤ 0 := not_lt.mp hnot
  nlinarith [hcap, hscale pivot, hgapPos, hmassPos, hle]

/-- A pivot of positive shifted diagonal always exists at a rank-three
frame with positive scales of total less than one. -/
theorem exists_pivot_shiftedDiag_pos {slotCount : ℕ} {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hnonempty : (Finset.univ : Finset (Fin slotCount)).Nonempty)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ pivot, 0 < atomShiftedDiag atom scale pivot := by
  obtain ⟨pivot, _, hpos⟩ :=
    exists_light_pivot hframe hscale hnonempty (by push_cast; linarith [hsmall])
  exact ⟨pivot, hpos⟩

/-! ## Layer 4 — the pivot pair residue and the rung -/

/-- **THE PIVOT PAIR RESIDUE.**  Six vectors in three dimensions that form
a tight frame, together with six positive scales of total less than one,
carry a PIVOT and a PAIR: the pivot has a positive shifted diagonal, the
first pivot minor is positive, and the deflated cross entry of the pair is
smaller than the product of the two pivot minors.

The search is a PAIR search after one pivot, thus fifteen tests rather
than twenty, and each test is one polynomial inequality in the atom Gram
and the scales.  The deflation identity turns this residue into the
determinant link of the third rung, and the dense collapse layer turns
that link into the whole `(6,3)` cell. -/
def AtomPivotPairClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ pivot slotOne slotTwo : Fin 6,
      pivot ≠ slotOne ∧ pivot ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot slotOne
        ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
            < atomPairMinor atom scale pivot slotOne
              * atomPairMinor atom scale pivot slotTwo

/-- **THE PIVOT PAIR RESIDUE CLOSES THE POLYNOMIAL RESIDUE.** -/
theorem atomTripleSylvesterClosed_of_pivotPair
    (hresidue : AtomPivotPairClosed) : AtomTripleSylvesterClosed := by
  intro atom scale hpos hsmall hframe
  obtain ⟨pivot, slotOne, slotTwo, hpivotOne, hpivotTwo, hne, hdiag, hminor, hdeflate⟩ :=
    hresidue atom scale hpos hsmall hframe
  exact ⟨pivot, slotOne, slotTwo, hpivotOne, hpivotTwo, hne, hdiag, hminor,
    atomTripleDet_pos_of_deflated_pair hdiag hdeflate⟩

/-- The atom triple ceiling from the pivot pair residue. -/
theorem atomTripleCeilingClosed_of_pivotPair
    (hresidue : AtomPivotPairClosed) : AtomTripleCeilingClosed :=
  atomTripleCeilingClosed_of_sylvester (atomTripleSylvesterClosed_of_pivotPair hresidue)

/-- **THE `(6,3)` CELL FROM THE PIVOT PAIR RESIDUE.**  No interiority, no
frame, no rank and no stationarity: one pair search closes the cell. -/
theorem gtzWeighted_six_three_of_pivotPair
    (hresidue : AtomPivotPairClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomTripleCeiling (atomTripleCeilingClosed_of_pivotPair hresidue)

/-- **THE RANK-THREE PAYOFF FROM THE PIVOT PAIR RESIDUE.** -/
theorem gtzWeightedAll_three_of_pivotPair
    (hresidue : AtomPivotPairClosed) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_atomTripleCeiling (atomTripleCeilingClosed_of_pivotPair hresidue)

/-- The crux type is empty under the pivot pair residue. -/
theorem isEmpty_sixThreeCrux_of_pivotPair
    (hresidue : AtomPivotPairClosed) : IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_atomTripleCeiling (atomTripleCeilingClosed_of_pivotPair hresidue)

/-- The rank-five dense branch from the pivot pair residue. -/
theorem rankFiveDenseClosed_of_pivotPair
    (hresidue : AtomPivotPairClosed) : RankFiveDenseClosed :=
  rankFiveDenseClosed_of_atomTripleCeiling (atomTripleCeilingClosed_of_pivotPair hresidue)

/-- The rank-six dense branch from the pivot pair residue. -/
theorem rankSixDenseClosed_of_pivotPair
    (hresidue : AtomPivotPairClosed) : RankSixDenseClosed :=
  rankSixDenseClosed_of_atomTripleCeiling (atomTripleCeilingClosed_of_pivotPair hresidue)

/-- The rank-six support-two closure from the pivot pair residue. -/
theorem rankSixSupportTwoClosed_of_pivotPair
    (hresidue : AtomPivotPairClosed) : RankSixSupportTwoClosed :=
  rankSixSupportTwoClosed_of_atomTripleCeiling (atomTripleCeilingClosed_of_pivotPair hresidue)

/-- The rank-five support-two closure from the pivot pair residue. -/
theorem rankFiveSupportTwoClosed_of_pivotPair
    (hresidue : AtomPivotPairClosed) : RankFiveSupportTwoClosed :=
  rankFiveSupportTwoClosed_of_atomTripleCeiling (atomTripleCeilingClosed_of_pivotPair hresidue)

/-- The rank-four support-two closure from the pivot pair residue. -/
theorem rankFourSupportTwoClosed_of_pivotPair
    (hresidue : AtomPivotPairClosed) : RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_atomTripleCeiling (atomTripleCeilingClosed_of_pivotPair hresidue)

/-! ## Layer 5 — the refutation of the frame drop -/

/-- The refuting atom family: four atoms of a square pattern with a small
third coordinate, and two atoms on the third axis.  Every entry is
rational. -/
noncomputable def dropAtom : Fin 6 → (Fin 3 → ℝ) :=
  ![![1/2, 1/2, 3/10], ![1/2, -1/2, 3/10], ![1/2, 1/2, -3/10], ![1/2, -1/2, -3/10],
    ![0, 0, 12/25], ![0, 0, 16/25]]

/-- The refuting scales: one fifth on the four square atoms and one
twentieth on the two axis atoms. -/
noncomputable def dropScale : Fin 6 → ℝ := ![1/5, 1/5, 1/5, 1/5, 1/20, 1/20]

/-- The reciprocals of the refuting scales. -/
noncomputable def dropCoeff : Fin 6 → ℝ := ![5, 5, 5, 5, 20, 20]

/-- The refuting region: the four square atoms. -/
def dropRegion : Finset (Fin 6) := {0, 1, 2, 3}

/-- The sum of a slot function over the refuting region. -/
theorem dropRegion_sum (value : Fin 6 → ℝ) :
    (∑ slot ∈ dropRegion, value slot) = value 0 + value 1 + value 2 + value 3 := by
  simp only [dropRegion]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- The refuting region has card four. -/
theorem dropRegion_card : dropRegion.card = 4 := by decide

/-- The refuting atoms form a tight frame of the probe space. -/
theorem dropAtom_frame : ∀ probe direction : Fin 3 → ℝ,
    (∑ slot, (dropAtom slot ⬝ᵥ probe) * (dropAtom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction := by
  intro probe direction
  simp [dropAtom, dotProduct, Fin.sum_univ_six, Fin.sum_univ_three]
  ring

/-- The refuting scales are positive. -/
theorem dropScale_pos : ∀ slot, 0 < dropScale slot := by
  intro slot
  fin_cases slot <;> norm_num [dropScale]

/-- The refuting scales total nine tenths. -/
theorem dropScale_sum : (∑ slot, dropScale slot) = 9 / 10 := by
  simp [dropScale, Fin.sum_univ_six]
  norm_num

/-- The refuting coefficients are the reciprocals of the refuting scales. -/
theorem dropCoeff_spec : ∀ slot, dropCoeff slot * dropScale slot = 1 := by
  intro slot
  fin_cases slot <;> norm_num [dropCoeff, dropScale]

/-- **THE REFUTING REGION DOMINATES.**  The four square atoms, against
their reciprocal scales, beat the probe energy at every nonzero
direction. -/
theorem dropRegion_dominates : ∀ direction : Fin 3 → ℝ, direction ≠ 0 →
    direction ⬝ᵥ direction
      < ∑ slot ∈ dropRegion, dropCoeff slot * (dropAtom slot ⬝ᵥ direction) ^ 2 := by
  intro direction hne
  have hnormPos : 0 < direction ⬝ᵥ direction := by
    obtain ⟨index, hindex⟩ : ∃ index, direction index ≠ 0 := by
      by_contra hnone
      exact hne (funext fun index => not_not.mp fun hlt => hnone ⟨index, hlt⟩)
    rw [dotProduct]
    exact Finset.sum_pos' (fun _ _ => mul_self_nonneg _)
      ⟨index, Finset.mem_univ _, mul_self_pos.mpr hindex⟩
  simp only [dotProduct, Fin.sum_univ_three] at hnormPos
  rw [dropRegion_sum]
  simp [dropAtom, dropCoeff, dotProduct, Fin.sum_univ_three]
  nlinarith [hnormPos, sq_nonneg (direction 0), sq_nonneg (direction 1),
    sq_nonneg (direction 2)]

/-- **THE FRAME DROP IS FALSE.**  The frame-constrained drop — the rounding
law that the descent of the third rung and the mass-gap descent of the
hinge arm both need — does NOT hold.

The refuting datum is explicit and rational: four atoms of a tight frame
dominate the probe space against their reciprocal scales, the scale mass
is nine tenths, and every one of the four single-atom drops loses a
direction.  The four witnesses are the four sign patterns of one integer
vector.

Thus the descent from a dominating region of card four to a dominating
triple does not exist at all, and no shrink route to the third rung can
proceed one atom at a time. -/
theorem not_atomFrameDropClosed : ¬ AtomFrameDropClosed := by
  intro hdrop
  obtain ⟨dropped, hmem, hkeep⟩ := hdrop dropAtom dropScale dropCoeff dropScale_pos
    (by rw [dropScale_sum]; norm_num) dropCoeff_spec dropAtom_frame dropRegion
    (by rw [dropRegion_card]; norm_num) dropRegion_dominates
  have hexpand : ∀ slot : Fin 6, slot ∈ dropRegion → ∀ direction : Fin 3 → ℝ,
      (∑ other ∈ dropRegion.erase slot,
          dropCoeff other * (dropAtom other ⬝ᵥ direction) ^ 2)
        = (∑ other ∈ dropRegion, dropCoeff other * (dropAtom other ⬝ᵥ direction) ^ 2)
          - dropCoeff slot * (dropAtom slot ⬝ᵥ direction) ^ 2 := by
    intro slot hslot direction
    exact Finset.sum_erase_eq_sub hslot
  simp only [dropRegion, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · have hbad := hkeep ![3, 3, 7] (by intro hzero; simpa using congrFun hzero 0)
    rw [hexpand 0 (by decide) ![3, 3, 7], dropRegion_sum] at hbad
    simp [dropAtom, dropCoeff, dotProduct, Fin.sum_univ_three] at hbad
    norm_num at hbad
  · have hbad := hkeep ![3, -3, 7] (by intro hzero; simpa using congrFun hzero 0)
    rw [hexpand 1 (by decide) ![3, -3, 7], dropRegion_sum] at hbad
    simp [dropAtom, dropCoeff, dotProduct, Fin.sum_univ_three] at hbad
    norm_num at hbad
  · have hbad := hkeep ![3, 3, -7] (by intro hzero; simpa using congrFun hzero 0)
    rw [hexpand 2 (by decide) ![3, 3, -7], dropRegion_sum] at hbad
    simp [dropAtom, dropCoeff, dotProduct, Fin.sum_univ_three] at hbad
    norm_num at hbad
  · have hbad := hkeep ![3, -3, -7] (by intro hzero; simpa using congrFun hzero 0)
    rw [hexpand 3 (by decide) ![3, -3, -7], dropRegion_sum] at hbad
    simp [dropAtom, dropCoeff, dotProduct, Fin.sum_univ_three] at hbad
    norm_num at hbad

/-! ## Layer 6 — the Gram volume and the coordinate Cauchy-Schwarz -/

/-- The GRAM MINOR of two slots: the squared area of the parallelogram
that the two atoms span. -/
def atomGramMinor {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (rowSlot colSlot : Fin slotCount) : ℝ :=
  atomGram atom rowSlot rowSlot * atomGram atom colSlot colSlot
    - atomGram atom rowSlot colSlot ^ 2

/-- The GRAM VOLUME of three slots: the squared volume of the
parallelepiped that the three atoms span. -/
def atomGramVolume {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  atomGram atom slotOne slotOne * atomGram atom slotTwo slotTwo
      * atomGram atom slotThree slotThree
    + 2 * atomGram atom slotOne slotTwo * atomGram atom slotOne slotThree
        * atomGram atom slotTwo slotThree
    - atomGram atom slotOne slotOne * atomGram atom slotTwo slotThree ^ 2
    - atomGram atom slotTwo slotTwo * atomGram atom slotOne slotThree ^ 2
    - atomGram atom slotThree slotThree * atomGram atom slotOne slotTwo ^ 2

/-- The Gram minor is the shifted pair minor at vanishing scales. -/
theorem atomGramMinor_eq_pairMinor {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (rowSlot colSlot : Fin slotCount) :
    atomGramMinor atom rowSlot colSlot = atomPairMinor atom (fun _ => 0) rowSlot colSlot := by
  simp only [atomGramMinor, atomPairMinor, atomShiftedDiag, sub_zero]

/-- The Gram volume is the shifted triple determinant at vanishing
scales. -/
theorem atomGramVolume_eq_tripleDet {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) :
    atomGramVolume atom slotOne slotTwo slotThree
      = atomTripleDet atom (fun _ => 0) slotOne slotTwo slotThree := by
  simp only [atomGramVolume, atomTripleDet, atomShiftedDiag, sub_zero]

/-- Every Gram minor is nonnegative: this is the Cauchy-Schwarz law of the
Gram. -/
theorem atomGramMinor_nonneg {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (rowSlot colSlot : Fin slotCount) : 0 ≤ atomGramMinor atom rowSlot colSlot := by
  simp only [atomGramMinor]
  linarith [atomGram_sq_le_diag_mul atom rowSlot colSlot]

/-- **THE PAIR VOLUME LAW.**  The Gram volumes of one pair, summed over
every slot outside the pair, total the Gram minor of that pair.  This is
the determinantal law of a projection read at one pair, and it needs the
frame law only. -/
theorem atomGramMinor_eq_volume_total {slotCount : ℕ} {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {slotOne slotTwo : Fin slotCount} (hne : slotOne ≠ slotTwo) :
    (∑ slotThree ∈ ((Finset.univ.erase slotOne).erase slotTwo),
        atomGramVolume atom slotOne slotTwo slotThree)
      = atomGramMinor atom slotOne slotTwo := by
  rw [atomGramMinor, ← pairMinor_eq_gram_triple_total hframe hne]
  exact Finset.sum_congr rfl fun slotThree _ => atomGramVolume_eq_tripleDet atom _ _ _

/-- **THE COORDINATE CAUCHY-SCHWARZ.**  In a symmetric block of dimension
three with a positive first diagonal entry and a nonnegative first pair
minor, the pair minor against the quadratic form dominates the
determinant against the square of the third coordinate.

The proof is the closed-form square decomposition of the block, thus it
carries no analysis and no eigenvalue. -/
theorem pairMinor_mul_form_ge_det_mul_sq
    {diagOne diagTwo diagThree crossOneTwo crossOneThree crossTwoThree
      valueOne valueTwo valueThree : ℝ}
    (hdiag : 0 < diagOne) (hminor : 0 ≤ diagOne * diagTwo - crossOneTwo ^ 2) :
    (diagOne * diagTwo * diagThree
        + 2 * crossOneTwo * crossOneThree * crossTwoThree
        - diagOne * crossTwoThree ^ 2 - diagTwo * crossOneThree ^ 2
        - diagThree * crossOneTwo ^ 2) * valueThree ^ 2
      ≤ (diagOne * diagTwo - crossOneTwo ^ 2)
        * (diagOne * valueOne ^ 2 + diagTwo * valueTwo ^ 2 + diagThree * valueThree ^ 2
          + 2 * crossOneTwo * valueOne * valueTwo
          + 2 * crossOneThree * valueOne * valueThree
          + 2 * crossTwoThree * valueTwo * valueThree) := by
  have hsplit : diagOne * ((diagOne * diagTwo - crossOneTwo ^ 2)
        * (diagOne * valueOne ^ 2 + diagTwo * valueTwo ^ 2 + diagThree * valueThree ^ 2
          + 2 * crossOneTwo * valueOne * valueTwo
          + 2 * crossOneThree * valueOne * valueThree
          + 2 * crossTwoThree * valueTwo * valueThree)
        - (diagOne * diagTwo * diagThree
          + 2 * crossOneTwo * crossOneThree * crossTwoThree
          - diagOne * crossTwoThree ^ 2 - diagTwo * crossOneThree ^ 2
          - diagThree * crossOneTwo ^ 2) * valueThree ^ 2)
      = (diagOne * diagTwo - crossOneTwo ^ 2)
          * (diagOne * valueOne + crossOneTwo * valueTwo + crossOneThree * valueThree) ^ 2
        + ((diagOne * diagTwo - crossOneTwo ^ 2) * valueTwo
          + (diagOne * crossTwoThree - crossOneTwo * crossOneThree) * valueThree) ^ 2 := by
    ring
  nlinarith [hsplit, hminor, sq_nonneg (diagOne * valueOne + crossOneTwo * valueTwo
      + crossOneThree * valueThree),
    sq_nonneg ((diagOne * diagTwo - crossOneTwo ^ 2) * valueTwo
      + (diagOne * crossTwoThree - crossOneTwo * crossOneThree) * valueThree),
    mul_nonneg hminor (sq_nonneg (diagOne * valueOne + crossOneTwo * valueTwo
      + crossOneThree * valueThree))]

/-- The blend energy of a probe supported on a three-slot carrier is the
quadratic form of the Gram block of that carrier. -/
theorem atomBlend_energy_triple {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    {slotOne slotTwo slotThree : Fin slotCount}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) {probe : Fin slotCount → ℝ}
    (hvanish : ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)),
      probe slot = 0) :
    atomBlend atom probe ⬝ᵥ atomBlend atom probe
      = atomGram atom slotOne slotOne * probe slotOne ^ 2
        + atomGram atom slotTwo slotTwo * probe slotTwo ^ 2
        + atomGram atom slotThree slotThree * probe slotThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * probe slotOne * probe slotTwo
        + 2 * atomGram atom slotOne slotThree * probe slotOne * probe slotThree
        + 2 * atomGram atom slotTwo slotThree * probe slotTwo * probe slotThree := by
  classical
  rw [atomBlend_energy_eq_gram atom probe]
  have hinner : ∀ rowSlot : Fin slotCount,
      (∑ colSlot, probe rowSlot * probe colSlot * atomGram atom rowSlot colSlot)
        = probe rowSlot * probe slotOne * atomGram atom rowSlot slotOne
          + probe rowSlot * probe slotTwo * atomGram atom rowSlot slotTwo
          + probe rowSlot * probe slotThree * atomGram atom rowSlot slotThree :=
    fun rowSlot => sum_eq_triple_of_support honeTwo honeThree htwoThree
      fun colSlot hnot => by rw [hvanish colSlot hnot, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun rowSlot _ => hinner rowSlot,
    sum_eq_triple_of_support honeTwo honeThree htwoThree
      (fun rowSlot hnot => by rw [hvanish rowSlot hnot]; ring)]
  rw [atomGram_comm atom slotTwo slotOne, atomGram_comm atom slotThree slotOne,
    atomGram_comm atom slotThree slotTwo]
  ring

/-- **THE TRACE CERTIFICATE.**  A carrier of three slots whose Gram volume
beats the scale mass of its own Gram minors dominates every nonzero probe
of that carrier.

The certificate is LINEAR in the scales, thus an averaging argument reads
it, and it needs no eigenvalue: three instances of the coordinate
Cauchy-Schwarz carry the whole proof. -/
theorem dominates_of_trace_certificate {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    (hscale : ∀ slot, 0 ≤ scale slot)
    {slotOne slotTwo slotThree : Fin slotCount}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hvolume : 0 < atomGramVolume atom slotOne slotTwo slotThree)
    (hcert : scale slotOne * atomGramMinor atom slotTwo slotThree
        + scale slotTwo * atomGramMinor atom slotOne slotThree
        + scale slotThree * atomGramMinor atom slotOne slotTwo
      < atomGramVolume atom slotOne slotTwo slotThree)
    {probe : Fin slotCount → ℝ}
    (hvanish : ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount)),
      probe slot = 0)
    (hprobe : probe ≠ 0) :
    (∑ slot, scale slot * probe slot ^ 2)
      < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  have hposOne : 0 < atomGram atom slotOne slotOne := by
    rcases lt_or_eq_of_le (atomGram_diag_nonneg atom slotOne) with hlt | heq
    · exact hlt
    · exfalso
      have hcauchyTwo := atomGram_sq_le_diag_mul atom slotOne slotTwo
      have hcauchyThree := atomGram_sq_le_diag_mul atom slotOne slotThree
      rw [← heq] at hcauchyTwo hcauchyThree
      have hcrossTwo : atomGram atom slotOne slotTwo = 0 :=
        sq_eq_zero_iff.mp (le_antisymm (by nlinarith [hcauchyTwo]) (sq_nonneg _))
      have hcrossThree : atomGram atom slotOne slotThree = 0 :=
        sq_eq_zero_iff.mp (le_antisymm (by nlinarith [hcauchyThree]) (sq_nonneg _))
      have hzero : atomGramVolume atom slotOne slotTwo slotThree = 0 := by
        simp only [atomGramVolume, hcrossTwo, hcrossThree, ← heq]
        ring
      rw [hzero] at hvolume
      exact absurd hvolume (lt_irrefl 0)
  have hposThree : 0 < atomGram atom slotThree slotThree := by
    rcases lt_or_eq_of_le (atomGram_diag_nonneg atom slotThree) with hlt | heq
    · exact hlt
    · exfalso
      have hcauchyOne := atomGram_sq_le_diag_mul atom slotOne slotThree
      have hcauchyTwo := atomGram_sq_le_diag_mul atom slotTwo slotThree
      rw [← heq, mul_zero] at hcauchyOne hcauchyTwo
      have hcrossOne : atomGram atom slotOne slotThree = 0 :=
        sq_eq_zero_iff.mp (le_antisymm (by nlinarith [hcauchyOne]) (sq_nonneg _))
      have hcrossTwo : atomGram atom slotTwo slotThree = 0 :=
        sq_eq_zero_iff.mp (le_antisymm (by nlinarith [hcauchyTwo]) (sq_nonneg _))
      have hzero : atomGramVolume atom slotOne slotTwo slotThree = 0 := by
        simp only [atomGramVolume, hcrossOne, hcrossTwo, ← heq]
        ring
      rw [hzero] at hvolume
      exact absurd hvolume (lt_irrefl 0)
  set diagOne := atomGram atom slotOne slotOne with hdiagOne
  set diagTwo := atomGram atom slotTwo slotTwo with hdiagTwo
  set diagThree := atomGram atom slotThree slotThree with hdiagThree
  set crossOneTwo := atomGram atom slotOne slotTwo with hcrossOneTwo
  set crossOneThree := atomGram atom slotOne slotThree with hcrossOneThree
  set crossTwoThree := atomGram atom slotTwo slotThree with hcrossTwoThree
  have hminorOneTwo : 0 ≤ diagOne * diagTwo - crossOneTwo ^ 2 :=
    atomGramMinor_nonneg atom slotOne slotTwo
  have hminorOneThree : 0 ≤ diagOne * diagThree - crossOneThree ^ 2 :=
    atomGramMinor_nonneg atom slotOne slotThree
  have hminorTwoThree : 0 ≤ diagTwo * diagThree - crossTwoThree ^ 2 :=
    atomGramMinor_nonneg atom slotTwo slotThree
  have hvol : 0 < diagOne * diagTwo * diagThree
      + 2 * crossOneTwo * crossOneThree * crossTwoThree
      - diagOne * crossTwoThree ^ 2 - diagTwo * crossOneThree ^ 2
      - diagThree * crossOneTwo ^ 2 := hvolume
  have hdodgson : diagOne * (diagOne * diagTwo * diagThree
        + 2 * crossOneTwo * crossOneThree * crossTwoThree
        - diagOne * crossTwoThree ^ 2 - diagTwo * crossOneThree ^ 2
        - diagThree * crossOneTwo ^ 2)
      = (diagOne * diagTwo - crossOneTwo ^ 2) * (diagOne * diagThree - crossOneThree ^ 2)
        - (diagOne * crossTwoThree - crossOneTwo * crossOneThree) ^ 2 := by ring
  have hminorPos : 0 < diagOne * diagTwo - crossOneTwo ^ 2 := by
    nlinarith [hdodgson, mul_pos hposOne hvol, hminorOneTwo, hminorOneThree,
      sq_nonneg (diagOne * crossTwoThree - crossOneTwo * crossOneThree)]
  set valueOne := probe slotOne with hvalueOne
  set valueTwo := probe slotTwo with hvalueTwo
  set valueThree := probe slotThree with hvalueThree
  set form := diagOne * valueOne ^ 2 + diagTwo * valueTwo ^ 2 + diagThree * valueThree ^ 2
    + 2 * crossOneTwo * valueOne * valueTwo
    + 2 * crossOneThree * valueOne * valueThree
    + 2 * crossTwoThree * valueTwo * valueThree with hform
  have henergy : atomBlend atom probe ⬝ᵥ atomBlend atom probe = form :=
    atomBlend_energy_triple atom honeTwo honeThree htwoThree hvanish
  have hlive : ¬(valueOne = 0 ∧ valueTwo = 0 ∧ valueThree = 0) := by
    rintro ⟨hone, htwo, hthree⟩
    refine hprobe (funext fun slot => ?_)
    by_cases hmem : slot ∈ ({slotOne, slotTwo, slotThree} : Finset (Fin slotCount))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hsel | hsel | hsel
      · rw [hsel, ← hvalueOne, hone]; rfl
      · rw [hsel, ← hvalueTwo, htwo]; rfl
      · rw [hsel, ← hvalueThree, hthree]; rfl
    · rw [hvanish slot hmem]; rfl
  have hformPos : 0 < form := by
    have := quadratic_pos_of_triple_minors (diagOne := diagOne) (diagTwo := diagTwo)
      (diagThree := diagThree) (crossOneTwo := crossOneTwo) (crossOneThree := crossOneThree)
      (crossTwoThree := crossTwoThree) (valueOne := valueOne) (valueTwo := valueTwo)
      (valueThree := valueThree) hposOne hminorPos hvol hlive
    exact this
  have hthreeBound := pairMinor_mul_form_ge_det_mul_sq (diagOne := diagOne) (diagTwo := diagTwo)
    (diagThree := diagThree) (crossOneTwo := crossOneTwo) (crossOneThree := crossOneThree)
    (crossTwoThree := crossTwoThree) (valueOne := valueOne) (valueTwo := valueTwo)
    (valueThree := valueThree) hposOne hminorPos.le
  have htwoBound := pairMinor_mul_form_ge_det_mul_sq (diagOne := diagOne) (diagTwo := diagThree)
    (diagThree := diagTwo) (crossOneTwo := crossOneThree) (crossOneThree := crossOneTwo)
    (crossTwoThree := crossTwoThree) (valueOne := valueOne) (valueTwo := valueThree)
    (valueThree := valueTwo) hposOne hminorOneThree
  have honeBound := pairMinor_mul_form_ge_det_mul_sq (diagOne := diagThree) (diagTwo := diagTwo)
    (diagThree := diagOne) (crossOneTwo := crossTwoThree) (crossOneThree := crossOneThree)
    (crossTwoThree := crossOneTwo) (valueOne := valueThree) (valueTwo := valueTwo)
    (valueThree := valueOne) hposThree
    (by linarith [hminorTwoThree, mul_comm diagTwo diagThree])
  have hscaleSum : (∑ slot, scale slot * probe slot ^ 2)
      = scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
        + scale slotThree * valueThree ^ 2 :=
    sum_eq_triple_of_support honeTwo honeThree htwoThree
      fun slot hnot => by rw [hvanish slot hnot]; ring
  have hcertExpand : scale slotOne * (diagTwo * diagThree - crossTwoThree ^ 2)
      + scale slotTwo * (diagOne * diagThree - crossOneThree ^ 2)
      + scale slotThree * (diagOne * diagTwo - crossOneTwo ^ 2)
      < diagOne * diagTwo * diagThree
        + 2 * crossOneTwo * crossOneThree * crossTwoThree
        - diagOne * crossTwoThree ^ 2 - diagTwo * crossOneThree ^ 2
        - diagThree * crossOneTwo ^ 2 := hcert
  rw [hscaleSum, henergy]
  nlinarith [hthreeBound, htwoBound, honeBound, hcertExpand, hformPos, hvol,
    mul_nonneg (hscale slotOne) (sq_nonneg valueOne),
    mul_nonneg (hscale slotTwo) (sq_nonneg valueTwo),
    mul_nonneg (hscale slotThree) (sq_nonneg valueThree),
    mul_le_mul_of_nonneg_left hthreeBound (hscale slotThree),
    mul_le_mul_of_nonneg_left htwoBound (hscale slotTwo),
    mul_le_mul_of_nonneg_left honeBound (hscale slotOne)]

/-! ## Layer 7 — the maximal volume triple and the quarter threshold -/

/-- A repeated first pair kills the Gram volume. -/
theorem atomGramVolume_repeat_left {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (slotOne slotTwo : Fin slotCount) : atomGramVolume atom slotOne slotOne slotTwo = 0 := by
  simp only [atomGramVolume]
  ring

/-- A repeated outer pair kills the Gram volume. -/
theorem atomGramVolume_repeat_outer {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (slotOne slotTwo : Fin slotCount) : atomGramVolume atom slotOne slotTwo slotOne = 0 := by
  simp only [atomGramVolume]
  rw [atomGram_comm atom slotTwo slotOne]
  ring

/-- A repeated last pair kills the Gram volume. -/
theorem atomGramVolume_repeat_right {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (slotOne slotTwo : Fin slotCount) : atomGramVolume atom slotOne slotTwo slotTwo = 0 := by
  simp only [atomGramVolume]
  ring

/-- The Gram minor of a dominating pair is positive: the shifted minor is
positive and the shifted diagonal entries never exceed the diagonal
entries of the Gram. -/
theorem atomGramMinor_pos_of_pairMinor_pos {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    (hscale : ∀ slot, 0 ≤ scale slot) {slotOne slotTwo : Fin slotCount}
    (hdiagOne : 0 < atomShiftedDiag atom scale slotOne)
    (hdiagTwo : 0 < atomShiftedDiag atom scale slotTwo)
    (hminor : 0 < atomPairMinor atom scale slotOne slotTwo) :
    0 < atomGramMinor atom slotOne slotTwo := by
  have hcapOne : atomShiftedDiag atom scale slotOne ≤ atomGram atom slotOne slotOne := by
    simp only [atomShiftedDiag]
    linarith [hscale slotOne]
  have hcapTwo : atomShiftedDiag atom scale slotTwo ≤ atomGram atom slotTwo slotTwo := by
    simp only [atomShiftedDiag]
    linarith [hscale slotTwo]
  simp only [atomGramMinor]
  simp only [atomPairMinor] at hminor
  nlinarith [hminor, hdiagOne, hdiagTwo, hcapOne, hcapTwo]

/-- **THE MAXIMAL VOLUME TRIPLE.**  A rank-three frame with positive
scales of total less than one carries three distinct slots of maximal
Gram volume, and that volume is positive.

The dominating pair theorem supplies a pair of positive Gram minor, the
pair volume law turns that minor into a positive volume at one slot, and
a repeated slot kills the volume, thus the maximizer is a genuine
triple. -/
theorem exists_maximal_volume_triple {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin 6 → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 < atomGramVolume atom slotOne slotTwo slotThree
        ∧ ∀ probeOne probeTwo probeThree : Fin 6,
            atomGramVolume atom probeOne probeTwo probeThree
              ≤ atomGramVolume atom slotOne slotTwo slotThree := by
  classical
  obtain ⟨pairOne, pairTwo, hpairNe, hpairDiagOne, hpairDiagTwo, hpairMinor⟩ :=
    exists_dominating_pair hframe hscale hsmall
  have hgramPos : 0 < atomGramMinor atom pairOne pairTwo :=
    atomGramMinor_pos_of_pairMinor_pos (fun slot => (hscale slot).le)
      hpairDiagOne hpairDiagTwo hpairMinor
  obtain ⟨extra, -, hextraPos⟩ : ∃ extra ∈ ((Finset.univ.erase pairOne).erase pairTwo),
      0 < atomGramVolume atom pairOne pairTwo extra := by
    by_contra hcontra
    have hcontra' : ∀ extra ∈ ((Finset.univ.erase pairOne).erase pairTwo),
        atomGramVolume atom pairOne pairTwo extra ≤ 0 := by
      intro extra hextra
      by_contra hpos
      exact hcontra ⟨extra, hextra, not_le.mp hpos⟩
    have hnonpos := Finset.sum_nonpos hcontra' 
    rw [atomGramMinor_eq_volume_total hframe hpairNe] at hnonpos
    linarith [hgramPos, hnonpos]
  obtain ⟨best, -, hbest⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin 6 × Fin 6 × Fin 6))
    (fun triple => atomGramVolume atom triple.1 triple.2.1 triple.2.2)
    ⟨(pairOne, pairTwo, extra), Finset.mem_univ _⟩
  have hmax : ∀ probeOne probeTwo probeThree : Fin 6,
      atomGramVolume atom probeOne probeTwo probeThree
        ≤ atomGramVolume atom best.1 best.2.1 best.2.2 :=
    fun probeOne probeTwo probeThree =>
      hbest (probeOne, probeTwo, probeThree) (Finset.mem_univ _)
  have hbestPos : 0 < atomGramVolume atom best.1 best.2.1 best.2.2 :=
    lt_of_lt_of_le hextraPos (hmax pairOne pairTwo extra)
  refine ⟨best.1, best.2.1, best.2.2, ?_, ?_, ?_, hbestPos, hmax⟩
  · intro hsame
    rw [← hsame, atomGramVolume_repeat_left atom best.1 best.2.2] at hbestPos
    exact absurd hbestPos (lt_irrefl 0)
  · intro hsame
    rw [← hsame, atomGramVolume_repeat_outer atom best.1 best.2.1] at hbestPos
    exact absurd hbestPos (lt_irrefl 0)
  · intro hsame
    rw [← hsame, atomGramVolume_repeat_right atom best.1 best.2.1] at hbestPos
    exact absurd hbestPos (lt_irrefl 0)

/-- Every Gram minor of a six-slot rank-three frame is capped by four
maximal volumes: the pair volume law spreads the minor over the four
slots outside the pair. -/
theorem atomGramMinor_le_four_mul_volume {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {bestOne bestTwo bestThree : Fin 6}
    (hmax : ∀ probeOne probeTwo probeThree : Fin 6,
      atomGramVolume atom probeOne probeTwo probeThree
        ≤ atomGramVolume atom bestOne bestTwo bestThree)
    {slotOne slotTwo : Fin 6} (hne : slotOne ≠ slotTwo) :
    atomGramMinor atom slotOne slotTwo
      ≤ 4 * atomGramVolume atom bestOne bestTwo bestThree := by
  classical
  have hcard : ((Finset.univ.erase slotOne).erase slotTwo).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ slotOne)]
    simp
  rw [← atomGramMinor_eq_volume_total hframe hne]
  calc (∑ slotThree ∈ ((Finset.univ.erase slotOne).erase slotTwo),
          atomGramVolume atom slotOne slotTwo slotThree)
      ≤ ∑ _slotThree ∈ ((Finset.univ.erase slotOne).erase slotTwo),
          atomGramVolume atom bestOne bestTwo bestThree :=
        Finset.sum_le_sum fun slotThree _ => hmax slotOne slotTwo slotThree
    _ = 4 * atomGramVolume atom bestOne bestTwo bestThree := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        norm_num

/-- **THE QUARTER THRESHOLD.**  A rank-three frame on six slots whose
positive scales total less than one quarter carries a dominating triple.

The triple is the one of MAXIMAL Gram volume, and the certificate is the
trace certificate: every Gram minor of the frame is capped by four
maximal volumes, thus the scale mass of the minors is capped by four
times the scale mass against the maximal volume.  No eigenvalue, no
compactness and no search enter the proof. -/
theorem exists_dominating_triple_of_scale_lt_quarter {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin 6 → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1 / 4) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) → probe ≠ 0 →
          (∑ slot, scale slot * probe slot ^ 2)
            < atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hvolume, hmax⟩ :=
    exists_maximal_volume_triple hframe hscale (by linarith [hsmall])
  have hcapOneTwo := atomGramMinor_le_four_mul_volume hframe hmax honeTwo
  have hcapOneThree := atomGramMinor_le_four_mul_volume hframe hmax honeThree
  have hcapTwoThree := atomGramMinor_le_four_mul_volume hframe hmax htwoThree
  have htripleMass : scale slotOne + scale slotTwo + scale slotThree ≤ ∑ slot, scale slot := by
    rw [← sum_over_triple_slots honeTwo honeThree htwoThree scale]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun slot _ _ => (hscale slot).le
  have hcert : scale slotOne * atomGramMinor atom slotTwo slotThree
      + scale slotTwo * atomGramMinor atom slotOne slotThree
      + scale slotThree * atomGramMinor atom slotOne slotTwo
      < atomGramVolume atom slotOne slotTwo slotThree := by
    have hone := mul_le_mul_of_nonneg_left hcapTwoThree (hscale slotOne).le
    have htwo := mul_le_mul_of_nonneg_left hcapOneThree (hscale slotTwo).le
    have hthree := mul_le_mul_of_nonneg_left hcapOneTwo (hscale slotThree).le
    nlinarith [hone, htwo, hthree, hvolume, htripleMass, hsmall,
      (hscale slotOne).le, (hscale slotTwo).le, (hscale slotThree).le]
  refine ⟨{slotOne, slotTwo, slotThree}, card_triple_slots honeTwo honeThree htwoThree,
    fun probe hvanish hne => ?_⟩
  exact dominates_of_trace_certificate (fun slot => (hscale slot).le) honeTwo honeThree htwoThree
    hvolume hcert hvanish hne

end Gtz
