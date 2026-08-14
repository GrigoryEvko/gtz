import Gtz.Wave.AtomIntegralityGap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6400000

/-!
# The signature geometry of the gap form, and two new domination criteria

The residue of the atom lane reads, in matrix language, as follows.  Six
tight frame atoms of rank three give a rank three orthogonal projection
`P` on the slot space, six positive scales of total one give a diagonal
`D`, and the GAP FORM is `N = P - D`.  The residue asks for a coordinate
three subspace on which `N` is nonnegative.

This module develops the signature geometry of that form.  It is the
cross product calculus of rank three, the inertia of the gap form, two
new unconditional domination criteria that read the ADJUGATE of the
triple Gram, and the calibration of both against the landed boundary
witness.

## The inertia of the gap form

The gap form is positive definite on the range of the projection with an
explicit margin, and negative definite on its kernel.  Both are three
dimensional, so the inertia is exactly three and three and the form is
nonsingular.  The two statements are three lines each: on a reading the
blend returns the direction and the reading law caps the scale term, and
on the kernel the blend energy vanishes outright.

## The adjugate reading of a triple

Let `a`, `b`, `c` be the three atoms of a triple and let `D` be the
determinant of the three of them.  The three CROSS PRODUCTS `b x c`,
`c x a` and `a x b` read a combination `w = p a + q b + r c` as `D p`,
`D q` and `D r`.  So the gap form of the triple, multiplied by the
determinant of the triple Gram, becomes

  `det(Gram) * (energy of w - scale form of (p, q, r))`
    `= det(Gram) * (w . w) - (scale a) (c1 . w)^2 - ... `

and the whole question is whether the three cross products, weighted by
the scales, stay below the determinant of the Gram.  That is a bound on
the largest value of a sum of three rank one forms, and every bound on
such a sum gives a domination criterion.

## The two criteria

* THE CROSS TRACE CRITERION.  The trace bound.  A triple dominates when
  the scale weighted sum of its three two by two Gram minors is at most
  the determinant of its three by three Gram.  One Cauchy-Schwarz per
  term.
* THE ADJUGATE DOMINANCE CRITERION.  The diagonal dominance bound on the
  same sum, read through the Gram of the three cross products.  The
  passage from the coefficient face to the direction face is one
  Cauchy-Schwarz and needs no matrix inverse.

Both are unconditional, division free and square root free, and both are
new to the lane.  Neither is complete: the landed boundary witness
refutes both at all twenty triples, as it must, because it carries twelve
tied triples and no strict one.

## The four slot rung, and where the difficulty sits

The residue asks for a covering set of THREE slots.  The set of covers is
closed upward, so a covering triple grows to a covering QUADRUPLE, and
the four slot statement is a genuine weakening of the residue.  It is a
weakening with room: at the sharp extremal every quadruple that carries
four distinct directions covers, and the operator gap there has
determinant three or twenty seven, while the triple statement is tied at
zero.  So the whole difficulty of the cell sits in the LAST slot.

This module compiles that factoring.  `AtomQuadCoverClosed` is the rung,
`AtomQuadDropClosed` is the drop of one slot, and the two together close
the residue and the cell.  The factored form `AtomQuadDropSomeClosed` is
proved EQUIVALENT to the residue, so nothing is lost in the passage and
the reader is not misled: the rung alone is strictly weaker, the drop
alone is strictly stronger, and only the pair is the cell.

Two laws of the drop are unconditional.  A dropped slot costs only its
own reading, so the remaining slots still cover every direction that the
dropped atom does not read.  And in every plane of directions some
nonzero combination survives the drop, which is the inertia statement of
the drop: the erased operator falls short in at most one direction.

## The necessary laws of a dominating triple

Every pair inside a dominating triple carries a nonnegative shifted two
by two minor, which is the Sylvester law of the gap form read on a
coordinate plane.  A consequence explains the sharp extremal: a pair with
a vanishing Gram minor never lies inside a dominating triple, and that is
exactly why eight of the twenty triples of the doubled tetrahedron fail
outright while the other twelve are tied.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomCross`, `Gtz.atomCross_dot`, `Gtz.atomCross_self_dot`,
  `Gtz.atomCross_dot_left`, `Gtz.atomCross_dot_right`, `Gtz.atomDet3`,
  `Gtz.atomDet3_cycle_left`, `Gtz.atomDet3_cycle_right` — the cross
  product calculus of rank three, with the Binet and Lagrange
  identities.
* `Gtz.gramPairDet`, `Gtz.gramTripleDet`, `Gtz.gramPairDet_eq_cross`,
  `Gtz.gramPairDet_eq_crossEnergy`, `Gtz.gramTripleDet_eq_det_sq`,
  `Gtz.gramTripleDet_nonneg` — the two Gram minors of a triple, read as
  cross products.
* `Gtz.atomBlend_reading`, `Gtz.atomGap_reading_ge`,
  `Gtz.atomGap_reading_pos`, `Gtz.atomGap_kernel_neg`,
  `Gtz.atomGap_kernel_lt` — **THE INERTIA THREE AND THREE OF THE GAP
  FORM**, with the margin `1 - cap`.
* `Gtz.atomTripleBlend`, `Gtz.atomCross_reads_combination_one`,
  `Gtz.atomCross_reads_combination_two`,
  `Gtz.atomCross_reads_combination_three`, `Gtz.atomTripleBlend_energy`,
  `Gtz.atomTripleBlend_gram` — the cross reading of a three term
  combination.
* `Gtz.two_mul_le_abs_mul`, `Gtz.tripleValues_of_crossTrace`,
  `Gtz.atomTriple_values_of_crossTrace`,
  `Gtz.exists_weakCarrier_of_crossTrace` — **THE CROSS TRACE CRITERION**.
* `Gtz.crossGram_energy_le`, `Gtz.crossGram_reading_le`,
  `Gtz.tripleValues_of_adjugateDominance`, `Gtz.gramAdjOneTwo`,
  `Gtz.gramAdjOneThree`, `Gtz.gramAdjTwoThree`,
  `Gtz.gramAdjOneTwo_eq_cross`, `Gtz.gramAdjOneThree_eq_cross`,
  `Gtz.gramAdjTwoThree_eq_cross`,
  `Gtz.atomTriple_values_of_adjugateDominance` — **THE ADJUGATE
  DOMINANCE CRITERION**, with the matrix free transpose passage.
* `Gtz.gramPairDet_row_total`, `Gtz.gramPairDet_total` — the two level
  determinantal identities, free from the landed cross moment.
* `Gtz.dot_combination`, `Gtz.AtomQuadCoverClosed`,
  `Gtz.atomQuadCoverClosed_of_atomVertexCover`,
  `Gtz.quadCover_of_lightPair`, `Gtz.lightPair_of_marginal`,
  `Gtz.exists_quadCover_of_lightMarginalPair` — **THE FOUR SLOT RUNG**,
  with an unconditional criterion that reads two marginals and one
  scale.
* `Gtz.atomCover_erase_of_orthogonal`,
  `Gtz.exists_covered_combination_of_erase` — **THE TWO LAWS OF THE
  DROP**.
* `Gtz.AtomQuadDropClosed`, `Gtz.AtomQuadDropSomeClosed`,
  `Gtz.atomVertexCoverClosed_of_quadDropSome`,
  `Gtz.atomQuadDropSomeClosed_of_atomVertexCover`,
  `Gtz.atomQuadDropSomeClosed_iff_atomVertexCover`,
  `Gtz.atomVertexCoverClosed_of_quad_and_drop`,
  `Gtz.gtzWeighted_six_three_of_quad_and_drop` — **THE FACTORING OF THE
  CELL INTO THE RUNG AND THE DROP**, with the converse compiled.
* `Gtz.atomPair_minor_of_values`, `Gtz.not_values_of_parallel_pair` —
  the Sylvester law of a dominating triple, and the parallel pair kill.
* `Gtz.AtomTripleCrossTrace`, `Gtz.AtomTripleAdjugateDominance`,
  `Gtz.not_atomTripleCrossTrace_boundaryWitness`,
  `Gtz.not_atomTripleAdjugateDominance_boundaryWitness`,
  `Gtz.AtomTripleCrossTraceClosed`,
  `Gtz.AtomTripleAdjugateDominanceClosed`,
  `Gtz.atomTripleBoundaryClosed_of_crossTraceClosed`,
  `Gtz.atomTripleBoundaryClosed_of_adjugateDominanceClosed`,
  `Gtz.not_atomTripleCrossTraceClosed`,
  `Gtz.not_atomTripleAdjugateDominanceClosed` — **NEITHER CRITERION IS
  COMPLETE**: each selection form closes the residue, and each is
  refuted at the landed sharp extremal at all twenty triples.

## Vacuity

The cross product calculus, the inertia laws, the two laws of the drop
and the two determinantal identities are unconditional theorems.  The two
criteria carry explicit scalar hypotheses which an exact integer census
of one million two hundred thousand rational data finds satisfied at
ninety five percent and at one hundred percent of the data, thus neither
is vacuous.  The rung criterion and the parallel pair kill are also
inhabited, the second at the eight repeating triples of the landed
witness.  The four refutations are exact rational computations at one
named configuration, thus they are not vacuous either.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the cross product calculus of rank three -/

section Cross

/-- The CROSS PRODUCT of two vectors of rank three. -/
def atomCross (left right : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![left 1 * right 2 - left 2 * right 1,
    left 2 * right 0 - left 0 * right 2,
    left 0 * right 1 - left 1 * right 0]

@[simp] theorem atomCross_zero (left right : Fin 3 → ℝ) :
    atomCross left right 0 = left 1 * right 2 - left 2 * right 1 := rfl

@[simp] theorem atomCross_one (left right : Fin 3 → ℝ) :
    atomCross left right 1 = left 2 * right 0 - left 0 * right 2 := rfl

@[simp] theorem atomCross_two (left right : Fin 3 → ℝ) :
    atomCross left right 2 = left 0 * right 1 - left 1 * right 0 := rfl

/-- **THE BINET IDENTITY.**  The dot product of two cross products is the
two by two determinant of the four dot products. -/
theorem atomCross_dot (leftOne rightOne leftTwo rightTwo : Fin 3 → ℝ) :
    atomCross leftOne rightOne ⬝ᵥ atomCross leftTwo rightTwo
      = (leftOne ⬝ᵥ leftTwo) * (rightOne ⬝ᵥ rightTwo)
        - (leftOne ⬝ᵥ rightTwo) * (rightOne ⬝ᵥ leftTwo) := by
  simp only [dotProduct, Fin.sum_univ_three, atomCross_zero, atomCross_one, atomCross_two]
  ring

/-- **THE LAGRANGE IDENTITY.**  The squared length of a cross product is
the two by two Gram minor of the pair. -/
theorem atomCross_self_dot (left right : Fin 3 → ℝ) :
    atomCross left right ⬝ᵥ atomCross left right
      = (left ⬝ᵥ left) * (right ⬝ᵥ right) - (left ⬝ᵥ right) ^ 2 := by
  rw [atomCross_dot]
  rw [dotProduct_comm right left]
  ring

theorem atomCross_dot_left (left right : Fin 3 → ℝ) :
    atomCross left right ⬝ᵥ left = 0 := by
  simp only [dotProduct, Fin.sum_univ_three, atomCross_zero, atomCross_one, atomCross_two]
  ring

theorem atomCross_dot_right (left right : Fin 3 → ℝ) :
    atomCross left right ⬝ᵥ right = 0 := by
  simp only [dotProduct, Fin.sum_univ_three, atomCross_zero, atomCross_one, atomCross_two]
  ring

/-- The DETERMINANT of three vectors of rank three. -/
def atomDet3 (first second third : Fin 3 → ℝ) : ℝ := atomCross first second ⬝ᵥ third

theorem atomDet3_cycle_left (first second third : Fin 3 → ℝ) :
    atomCross second third ⬝ᵥ first = atomDet3 first second third := by
  simp only [atomDet3, dotProduct, Fin.sum_univ_three, atomCross_zero, atomCross_one,
    atomCross_two]
  ring

theorem atomDet3_cycle_right (first second third : Fin 3 → ℝ) :
    atomCross third first ⬝ᵥ second = atomDet3 first second third := by
  simp only [atomDet3, dotProduct, Fin.sum_univ_three, atomCross_zero, atomCross_one,
    atomCross_two]
  ring

end Cross

/-! ## Layer 1 — the two Gram minors of a triple -/

section GramMinor

variable {slotCount : ℕ}

/-- The two by two Gram minor of a pair of slots. -/
def gramPairDet (gram : Fin slotCount → Fin slotCount → ℝ) (slotOne slotTwo : Fin slotCount) : ℝ :=
  gram slotOne slotOne * gram slotTwo slotTwo - gram slotOne slotTwo * gram slotTwo slotOne

/-- The three by three Gram determinant of a triple of slots. -/
def gramTripleDet (gram : Fin slotCount → Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  gram slotOne slotOne
      * (gram slotTwo slotTwo * gram slotThree slotThree
        - gram slotTwo slotThree * gram slotThree slotTwo)
    - gram slotOne slotTwo
      * (gram slotTwo slotOne * gram slotThree slotThree
        - gram slotTwo slotThree * gram slotThree slotOne)
    + gram slotOne slotThree
      * (gram slotTwo slotOne * gram slotThree slotTwo
        - gram slotTwo slotTwo * gram slotThree slotOne)

/-- The two by two Gram minor is the squared length of the cross
product. -/
theorem gramPairDet_eq_cross {rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (slotOne slotTwo : Fin slotCount) :
    gramPairDet (atomGram atom) slotOne slotTwo
      = (atom slotOne ⬝ᵥ atom slotOne) * (atom slotTwo ⬝ᵥ atom slotTwo)
        - (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := by
  simp only [gramPairDet, atomGram, dotProduct_comm (atom slotTwo) (atom slotOne)]
  ring

/-- At rank three the two by two Gram minor is the squared length of the
cross product of the two atoms. -/
theorem gramPairDet_eq_crossEnergy (atom : Fin slotCount → (Fin 3 → ℝ))
    (slotOne slotTwo : Fin slotCount) :
    gramPairDet (atomGram atom) slotOne slotTwo
      = atomCross (atom slotOne) (atom slotTwo) ⬝ᵥ atomCross (atom slotOne) (atom slotTwo) := by
  rw [gramPairDet_eq_cross atom slotOne slotTwo, atomCross_self_dot]

/-- **THE GRAM DETERMINANT IS THE SQUARED DETERMINANT.**  At rank three
the three by three Gram determinant of a triple is the square of the
determinant of the three atoms. -/
theorem gramTripleDet_eq_det_sq (atom : Fin slotCount → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) :
    gramTripleDet (atomGram atom) slotOne slotTwo slotThree
      = (atomDet3 (atom slotOne) (atom slotTwo) (atom slotThree)) ^ 2 := by
  simp only [gramTripleDet, atomGram, atomDet3, dotProduct, Fin.sum_univ_three,
    atomCross_zero, atomCross_one, atomCross_two]
  ring

/-- The Gram determinant of a triple is nonnegative. -/
theorem gramTripleDet_nonneg (atom : Fin slotCount → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) :
    0 ≤ gramTripleDet (atomGram atom) slotOne slotTwo slotThree := by
  rw [gramTripleDet_eq_det_sq]
  exact sq_nonneg _

end GramMinor

/-! ## Layer 2 — the inertia of the gap form -/

section Inertia

variable {slotCount rank : ℕ}

/-- **THE BLEND OF A READING IS THE DIRECTION.**  A tight frame
reconstructs every direction from its own readings. -/
theorem atomBlend_reading (atom : Fin slotCount → (Fin rank → ℝ))
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (direction : Fin rank → ℝ) :
    atomBlend atom (fun slot => atom slot ⬝ᵥ direction) = direction := by
  classical
  funext index
  have hunit := hframe (fun position => if position = index then (1 : ℝ) else 0) direction
  have hleft : ∀ slot : Fin slotCount,
      (atom slot ⬝ᵥ fun position => if position = index then (1 : ℝ) else 0) = atom slot index := by
    intro slot
    simp [dotProduct]
  have hright :
      (fun position => if position = index then (1 : ℝ) else 0) ⬝ᵥ direction = direction index := by
    simp [dotProduct]
  rw [Finset.sum_congr rfl fun slot _ => by rw [hleft slot], hright] at hunit
  rw [atomBlend_apply]
  rw [← hunit]
  exact Finset.sum_congr rfl fun slot _ => mul_comm _ _

/-- **THE GAP FORM IS POSITIVE DEFINITE ON THE RANGE.**  On the reading of
a direction the blend energy is the energy of that direction, and the
reading law caps the scale term by the largest scale.  The margin is one
minus that cap. -/
theorem atomGap_reading_ge (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {cap : ℝ} (hcap : ∀ slot, scale slot ≤ cap) (direction : Fin rank → ℝ) :
    (1 - cap) * (direction ⬝ᵥ direction)
      ≤ (atomBlend atom (fun slot => atom slot ⬝ᵥ direction)
            ⬝ᵥ atomBlend atom (fun slot => atom slot ⬝ᵥ direction))
        - ∑ slot, scale slot * (atom slot ⬝ᵥ direction) ^ 2 := by
  have hblend := atomBlend_reading atom hframe direction
  have hreading := atomReading_sum atom hframe direction
  have hbound : (∑ slot, scale slot * (atom slot ⬝ᵥ direction) ^ 2)
      ≤ cap * (direction ⬝ᵥ direction) := by
    rw [← hreading, Finset.mul_sum]
    exact Finset.sum_le_sum fun slot _ =>
      mul_le_mul_of_nonneg_right (hcap slot) (sq_nonneg _)
  rw [hblend]
  linarith

/-- **THE GAP FORM IS NEGATIVE SEMIDEFINITE ON THE KERNEL.**  A probe that
the blend annihilates carries no blend energy at all, so the gap form
reads minus the scale energy. -/
theorem atomGap_kernel_neg (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    {probe : Fin slotCount → ℝ} (hkernel : atomBlend atom probe = 0) :
    (atomBlend atom probe ⬝ᵥ atomBlend atom probe) - ∑ slot, scale slot * probe slot ^ 2
      = -∑ slot, scale slot * probe slot ^ 2 := by
  rw [hkernel]
  simp

/-- **THE GAP FORM IS NEGATIVE DEFINITE ON THE KERNEL.**  A nonzero probe
in the kernel of the blend gives a strictly negative gap. -/
theorem atomGap_kernel_lt (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (hpos : ∀ slot, 0 < scale slot) {probe : Fin slotCount → ℝ}
    (hkernel : atomBlend atom probe = 0) (hne : probe ≠ 0) :
    (atomBlend atom probe ⬝ᵥ atomBlend atom probe) - ∑ slot, scale slot * probe slot ^ 2 < 0 := by
  classical
  rw [atomGap_kernel_neg atom scale hkernel]
  have hslot : ∃ slot, probe slot ≠ 0 := by
    by_contra hall
    exact hne (funext fun slot => not_not.mp (not_exists.mp hall slot))
  obtain ⟨slot, hslotne⟩ := hslot
  have hterm : ∀ other ∈ (Finset.univ : Finset (Fin slotCount)),
      0 ≤ scale other * probe other ^ 2 :=
    fun other _ => mul_nonneg (hpos other).le (sq_nonneg _)
  have hsqpos : 0 < probe slot ^ 2 := by positivity
  have hstrict : 0 < scale slot * probe slot ^ 2 := mul_pos (hpos slot) hsqpos
  have hsum : 0 < ∑ other, scale other * probe other ^ 2 :=
    Finset.sum_pos' hterm ⟨slot, Finset.mem_univ slot, hstrict⟩
  linarith

end Inertia

/-! ## Layer 3 — the cross reading of a triple -/

section CrossReading

variable {slotCount : ℕ}

/-- The three term combination of three atoms. -/
def atomTripleBlend (first second third : Fin 3 → ℝ) (valueOne valueTwo valueThree : ℝ) :
    Fin 3 → ℝ :=
  fun index => valueOne * first index + valueTwo * second index + valueThree * third index

/-- The first cross product reads the combination as the determinant
times the first value. -/
theorem atomCross_reads_combination_one (first second third : Fin 3 → ℝ)
    (valueOne valueTwo valueThree : ℝ) :
    atomCross second third ⬝ᵥ atomTripleBlend first second third valueOne valueTwo valueThree
      = atomDet3 first second third * valueOne := by
  simp only [atomTripleBlend, atomDet3, dotProduct, Fin.sum_univ_three, atomCross_zero,
    atomCross_one, atomCross_two]
  ring

/-- The second cross product reads the combination as the determinant
times the second value. -/
theorem atomCross_reads_combination_two (first second third : Fin 3 → ℝ)
    (valueOne valueTwo valueThree : ℝ) :
    atomCross third first ⬝ᵥ atomTripleBlend first second third valueOne valueTwo valueThree
      = atomDet3 first second third * valueTwo := by
  simp only [atomTripleBlend, atomDet3, dotProduct, Fin.sum_univ_three, atomCross_zero,
    atomCross_one, atomCross_two]
  ring

/-- The third cross product reads the combination as the determinant
times the third value. -/
theorem atomCross_reads_combination_three (first second third : Fin 3 → ℝ)
    (valueOne valueTwo valueThree : ℝ) :
    atomCross first second ⬝ᵥ atomTripleBlend first second third valueOne valueTwo valueThree
      = atomDet3 first second third * valueThree := by
  simp only [atomTripleBlend, atomDet3, dotProduct, Fin.sum_univ_three, atomCross_zero,
    atomCross_one, atomCross_two]
  ring

/-- The energy of the three term combination is the Gram form. -/
theorem atomTripleBlend_energy (first second third : Fin 3 → ℝ)
    (valueOne valueTwo valueThree : ℝ) :
    atomTripleBlend first second third valueOne valueTwo valueThree
        ⬝ᵥ atomTripleBlend first second third valueOne valueTwo valueThree
      = (first ⬝ᵥ first) * valueOne ^ 2 + (second ⬝ᵥ second) * valueTwo ^ 2
        + (third ⬝ᵥ third) * valueThree ^ 2
        + 2 * (first ⬝ᵥ second) * valueOne * valueTwo
        + 2 * (first ⬝ᵥ third) * valueOne * valueThree
        + 2 * (second ⬝ᵥ third) * valueTwo * valueThree :=
  tripleCombination_energy first second third valueOne valueTwo valueThree

end CrossReading

/-! ## Layer 4 — the two scalar engines of the criteria -/

/-- The upper absolute value engine. -/
theorem two_mul_le_abs_mul (coupling first second : ℝ) :
    2 * coupling * first * second ≤ |coupling| * (first ^ 2 + second ^ 2) := by
  rcases abs_cases coupling with ⟨habs, _hsign⟩ | ⟨habs, _hsign⟩
  · rw [habs]
    nlinarith [sq_nonneg (first - second)]
  · rw [habs]
    nlinarith [sq_nonneg (first + second)]

/-! ## Layer 5 — the cross trace criterion -/

section CrossTrace

variable {slotCount : ℕ}

/-- **THE CROSS TRACE CRITERION, IN VECTOR FORM.**  When the three cross
products of a triple, weighted by the scales, carry a total squared
length below the Gram determinant, the triple dominates. -/
theorem tripleValues_of_crossTrace {first second third : Fin 3 → ℝ}
    {scaleOne scaleTwo scaleThree : ℝ}
    (honePos : 0 < scaleOne) (htwoPos : 0 < scaleTwo) (hthreePos : 0 < scaleThree)
    (hdet : 0 < (atomDet3 first second third) ^ 2)
    (hcrit : scaleOne * (atomCross second third ⬝ᵥ atomCross second third)
        + scaleTwo * (atomCross third first ⬝ᵥ atomCross third first)
        + scaleThree * (atomCross first second ⬝ᵥ atomCross first second)
      ≤ (atomDet3 first second third) ^ 2)
    (valueOne valueTwo valueThree : ℝ) :
    scaleOne * valueOne ^ 2 + scaleTwo * valueTwo ^ 2 + scaleThree * valueThree ^ 2
      ≤ atomTripleBlend first second third valueOne valueTwo valueThree
          ⬝ᵥ atomTripleBlend first second third valueOne valueTwo valueThree := by
  set blend := atomTripleBlend first second third valueOne valueTwo valueThree with hblendDef
  set det := atomDet3 first second third with hdetDef
  have hone := atomCross_reads_combination_one first second third valueOne valueTwo valueThree
  have htwo := atomCross_reads_combination_two first second third valueOne valueTwo valueThree
  have hthree := atomCross_reads_combination_three first second third valueOne valueTwo valueThree
  have hcsOne := atomDot_sq_le_energy (atomCross second third) blend
  have hcsTwo := atomDot_sq_le_energy (atomCross third first) blend
  have hcsThree := atomDot_sq_le_energy (atomCross first second) blend
  rw [hone] at hcsOne
  rw [htwo] at hcsTwo
  rw [hthree] at hcsThree
  have hblendNonneg := atomDot_self_nonneg blend
  have hkeyOne : scaleOne * (det * valueOne) ^ 2
      ≤ scaleOne * ((atomCross second third ⬝ᵥ atomCross second third) * (blend ⬝ᵥ blend)) :=
    mul_le_mul_of_nonneg_left hcsOne honePos.le
  have hkeyTwo : scaleTwo * (det * valueTwo) ^ 2
      ≤ scaleTwo * ((atomCross third first ⬝ᵥ atomCross third first) * (blend ⬝ᵥ blend)) :=
    mul_le_mul_of_nonneg_left hcsTwo htwoPos.le
  have hkeyThree : scaleThree * (det * valueThree) ^ 2
      ≤ scaleThree * ((atomCross first second ⬝ᵥ atomCross first second) * (blend ⬝ᵥ blend)) :=
    mul_le_mul_of_nonneg_left hcsThree hthreePos.le
  have hslack : (scaleOne * (atomCross second third ⬝ᵥ atomCross second third)
        + scaleTwo * (atomCross third first ⬝ᵥ atomCross third first)
        + scaleThree * (atomCross first second ⬝ᵥ atomCross first second)) * (blend ⬝ᵥ blend)
      ≤ det ^ 2 * (blend ⬝ᵥ blend) :=
    mul_le_mul_of_nonneg_right hcrit hblendNonneg
  rw [show (det * valueOne) ^ 2 = det ^ 2 * valueOne ^ 2 from by ring] at hkeyOne
  rw [show (det * valueTwo) ^ 2 = det ^ 2 * valueTwo ^ 2 from by ring] at hkeyTwo
  rw [show (det * valueThree) ^ 2 = det ^ 2 * valueThree ^ 2 from by ring] at hkeyThree
  have hcollect : scaleOne * ((atomCross second third ⬝ᵥ atomCross second third) * (blend ⬝ᵥ blend))
        + scaleTwo * ((atomCross third first ⬝ᵥ atomCross third first) * (blend ⬝ᵥ blend))
        + scaleThree * ((atomCross first second ⬝ᵥ atomCross first second) * (blend ⬝ᵥ blend))
      = (scaleOne * (atomCross second third ⬝ᵥ atomCross second third)
          + scaleTwo * (atomCross third first ⬝ᵥ atomCross third first)
          + scaleThree * (atomCross first second ⬝ᵥ atomCross first second))
        * (blend ⬝ᵥ blend) := by ring
  have hfactor : det ^ 2 * (scaleOne * valueOne ^ 2 + scaleTwo * valueTwo ^ 2
        + scaleThree * valueThree ^ 2)
      ≤ det ^ 2 * (blend ⬝ᵥ blend) := by
    have hstep : det ^ 2 * scaleOne * valueOne ^ 2 + det ^ 2 * scaleTwo * valueTwo ^ 2
        + det ^ 2 * scaleThree * valueThree ^ 2 ≤ det ^ 2 * (blend ⬝ᵥ blend) := by
      linarith [hkeyOne, hkeyTwo, hkeyThree, hslack, hcollect]
    linarith [hstep]
  exact le_of_mul_le_mul_left hfactor hdet

end CrossTrace

/-! ## Layer 6 — the adjugate dominance criterion -/

section AdjugateDominance

/-- **THE COEFFICIENT FACE OF THE ADJUGATE BOUND.**  Diagonal dominance of
the scale weighted Gram of the three cross products bounds the energy of
every scale weighted combination of them. -/
theorem crossGram_energy_le {crossOne crossTwo crossThree : Fin 3 → ℝ}
    {scaleOne scaleTwo scaleThree bound : ℝ}
    (honePos : 0 < scaleOne) (htwoPos : 0 < scaleTwo) (hthreePos : 0 < scaleThree)
    (hone : scaleOne * (crossOne ⬝ᵥ crossOne) + scaleTwo * |crossOne ⬝ᵥ crossTwo|
      + scaleThree * |crossOne ⬝ᵥ crossThree| ≤ bound)
    (htwo : scaleTwo * (crossTwo ⬝ᵥ crossTwo) + scaleOne * |crossOne ⬝ᵥ crossTwo|
      + scaleThree * |crossTwo ⬝ᵥ crossThree| ≤ bound)
    (hthree : scaleThree * (crossThree ⬝ᵥ crossThree) + scaleOne * |crossOne ⬝ᵥ crossThree|
      + scaleTwo * |crossTwo ⬝ᵥ crossThree| ≤ bound)
    (weightOne weightTwo weightThree : ℝ) :
    (fun index => scaleOne * weightOne * crossOne index + scaleTwo * weightTwo * crossTwo index
        + scaleThree * weightThree * crossThree index)
      ⬝ᵥ (fun index => scaleOne * weightOne * crossOne index + scaleTwo * weightTwo * crossTwo index
        + scaleThree * weightThree * crossThree index)
      ≤ bound * (scaleOne * weightOne ^ 2 + scaleTwo * weightTwo ^ 2
          + scaleThree * weightThree ^ 2) := by
  have hexpand := tripleCombination_energy crossOne crossTwo crossThree
    (scaleOne * weightOne) (scaleTwo * weightTwo) (scaleThree * weightThree)
  have hcrossOneTwo := two_mul_le_abs_mul (crossOne ⬝ᵥ crossTwo) weightOne weightTwo
  have hcrossOneThree := two_mul_le_abs_mul (crossOne ⬝ᵥ crossThree) weightOne weightThree
  have hcrossTwoThree := two_mul_le_abs_mul (crossTwo ⬝ᵥ crossThree) weightTwo weightThree
  have hprodOneTwo : 0 < scaleOne * scaleTwo := mul_pos honePos htwoPos
  have hprodOneThree : 0 < scaleOne * scaleThree := mul_pos honePos hthreePos
  have hprodTwoThree : 0 < scaleTwo * scaleThree := mul_pos htwoPos hthreePos
  have hboundOne : scaleOne * weightOne ^ 2
        * (scaleOne * (crossOne ⬝ᵥ crossOne) + scaleTwo * |crossOne ⬝ᵥ crossTwo|
          + scaleThree * |crossOne ⬝ᵥ crossThree|)
      ≤ scaleOne * weightOne ^ 2 * bound :=
    mul_le_mul_of_nonneg_left hone (mul_nonneg honePos.le (sq_nonneg _))
  have hboundTwo : scaleTwo * weightTwo ^ 2
        * (scaleTwo * (crossTwo ⬝ᵥ crossTwo) + scaleOne * |crossOne ⬝ᵥ crossTwo|
          + scaleThree * |crossTwo ⬝ᵥ crossThree|)
      ≤ scaleTwo * weightTwo ^ 2 * bound :=
    mul_le_mul_of_nonneg_left htwo (mul_nonneg htwoPos.le (sq_nonneg _))
  have hboundThree : scaleThree * weightThree ^ 2
        * (scaleThree * (crossThree ⬝ᵥ crossThree) + scaleOne * |crossOne ⬝ᵥ crossThree|
          + scaleTwo * |crossTwo ⬝ᵥ crossThree|)
      ≤ scaleThree * weightThree ^ 2 * bound :=
    mul_le_mul_of_nonneg_left hthree (mul_nonneg hthreePos.le (sq_nonneg _))
  rw [hexpand]
  nlinarith [hboundOne, hboundTwo, hboundThree, hcrossOneTwo, hcrossOneThree, hcrossTwoThree,
    hprodOneTwo, hprodOneThree, hprodTwoThree, honePos, htwoPos, hthreePos,
    mul_nonneg hprodOneTwo.le (abs_nonneg (crossOne ⬝ᵥ crossTwo)),
    mul_nonneg hprodOneThree.le (abs_nonneg (crossOne ⬝ᵥ crossThree)),
    mul_nonneg hprodTwoThree.le (abs_nonneg (crossTwo ⬝ᵥ crossThree))]

/-- **THE TRANSPOSE PASSAGE, WITHOUT MATRICES.**  A bound on the energy of
every scale weighted combination of three vectors gives the same bound on
the scale weighted sum of their squared readings.  One Cauchy-Schwarz. -/
theorem crossGram_reading_le {crossOne crossTwo crossThree : Fin 3 → ℝ}
    {scaleOne scaleTwo scaleThree bound : ℝ}
    (honePos : 0 < scaleOne) (htwoPos : 0 < scaleTwo) (hthreePos : 0 < scaleThree)
    (hbound : 0 ≤ bound)
    (hcoeff : ∀ weightOne weightTwo weightThree : ℝ,
      (fun index => scaleOne * weightOne * crossOne index + scaleTwo * weightTwo * crossTwo index
          + scaleThree * weightThree * crossThree index)
        ⬝ᵥ (fun index => scaleOne * weightOne * crossOne index
          + scaleTwo * weightTwo * crossTwo index + scaleThree * weightThree * crossThree index)
        ≤ bound * (scaleOne * weightOne ^ 2 + scaleTwo * weightTwo ^ 2
            + scaleThree * weightThree ^ 2))
    (probe : Fin 3 → ℝ) :
    scaleOne * (crossOne ⬝ᵥ probe) ^ 2 + scaleTwo * (crossTwo ⬝ᵥ probe) ^ 2
        + scaleThree * (crossThree ⬝ᵥ probe) ^ 2
      ≤ bound * (probe ⬝ᵥ probe) := by
  set weightOne := crossOne ⬝ᵥ probe with hweightOne
  set weightTwo := crossTwo ⬝ᵥ probe with hweightTwo
  set weightThree := crossThree ⬝ᵥ probe with hweightThree
  set carrier : Fin 3 → ℝ := fun index =>
    scaleOne * weightOne * crossOne index + scaleTwo * weightTwo * crossTwo index
      + scaleThree * weightThree * crossThree index with hcarrier
  set total := scaleOne * weightOne ^ 2 + scaleTwo * weightTwo ^ 2
    + scaleThree * weightThree ^ 2 with htotal
  have hpairing : carrier ⬝ᵥ probe = total := by
    simp only [hcarrier, htotal, hweightOne, hweightTwo, hweightThree, dotProduct,
      Fin.sum_univ_three]
    ring
  have henergy := hcoeff weightOne weightTwo weightThree
  have hcs := atomDot_sq_le_energy carrier probe
  rw [hpairing] at hcs
  have hpartOne : 0 ≤ scaleOne * weightOne ^ 2 := mul_nonneg honePos.le (sq_nonneg _)
  have hpartTwo : 0 ≤ scaleTwo * weightTwo ^ 2 := mul_nonneg htwoPos.le (sq_nonneg _)
  have hpartThree : 0 ≤ scaleThree * weightThree ^ 2 := mul_nonneg hthreePos.le (sq_nonneg _)
  have htotalNonneg : 0 ≤ total := by rw [htotal]; linarith
  have hprobeNonneg := atomDot_self_nonneg probe
  rcases htotalNonneg.lt_or_eq with hpos | hzero
  · nlinarith [hcs, henergy, hpos, hprobeNonneg]
  · rw [← hzero]
    exact mul_nonneg hbound hprobeNonneg

/-- **THE ADJUGATE DOMINANCE CRITERION, IN VECTOR FORM.**  When the Gram
of the three cross products is diagonally dominant against the Gram
determinant, the triple dominates. -/
theorem tripleValues_of_adjugateDominance {first second third : Fin 3 → ℝ}
    {scaleOne scaleTwo scaleThree : ℝ}
    (honePos : 0 < scaleOne) (htwoPos : 0 < scaleTwo) (hthreePos : 0 < scaleThree)
    (hdet : 0 < (atomDet3 first second third) ^ 2)
    (hone : scaleOne * (atomCross second third ⬝ᵥ atomCross second third)
        + scaleTwo * |atomCross second third ⬝ᵥ atomCross third first|
        + scaleThree * |atomCross second third ⬝ᵥ atomCross first second|
      ≤ (atomDet3 first second third) ^ 2)
    (htwo : scaleTwo * (atomCross third first ⬝ᵥ atomCross third first)
        + scaleOne * |atomCross second third ⬝ᵥ atomCross third first|
        + scaleThree * |atomCross third first ⬝ᵥ atomCross first second|
      ≤ (atomDet3 first second third) ^ 2)
    (hthree : scaleThree * (atomCross first second ⬝ᵥ atomCross first second)
        + scaleOne * |atomCross second third ⬝ᵥ atomCross first second|
        + scaleTwo * |atomCross third first ⬝ᵥ atomCross first second|
      ≤ (atomDet3 first second third) ^ 2)
    (valueOne valueTwo valueThree : ℝ) :
    scaleOne * valueOne ^ 2 + scaleTwo * valueTwo ^ 2 + scaleThree * valueThree ^ 2
      ≤ atomTripleBlend first second third valueOne valueTwo valueThree
          ⬝ᵥ atomTripleBlend first second third valueOne valueTwo valueThree := by
  set blend := atomTripleBlend first second third valueOne valueTwo valueThree with hblendDef
  set det := atomDet3 first second third with hdetDef
  have hcoeff := fun weightOne weightTwo weightThree =>
    crossGram_energy_le (crossOne := atomCross second third) (crossTwo := atomCross third first)
      (crossThree := atomCross first second) honePos htwoPos hthreePos hone htwo hthree
      weightOne weightTwo weightThree
  have hreading := crossGram_reading_le honePos htwoPos hthreePos (sq_nonneg det) hcoeff blend
  have hone' := atomCross_reads_combination_one first second third valueOne valueTwo valueThree
  have htwo' := atomCross_reads_combination_two first second third valueOne valueTwo valueThree
  have hthree' := atomCross_reads_combination_three first second third valueOne valueTwo valueThree
  rw [← hdetDef] at hone' htwo' hthree'
  rw [hone', htwo', hthree'] at hreading
  rw [show (det * valueOne) ^ 2 = det ^ 2 * valueOne ^ 2 from by ring,
    show (det * valueTwo) ^ 2 = det ^ 2 * valueTwo ^ 2 from by ring,
    show (det * valueThree) ^ 2 = det ^ 2 * valueThree ^ 2 from by ring] at hreading
  have hfactor : det ^ 2 * (scaleOne * valueOne ^ 2 + scaleTwo * valueTwo ^ 2
        + scaleThree * valueThree ^ 2)
      ≤ det ^ 2 * (blend ⬝ᵥ blend) := by linarith [hreading]
  exact le_of_mul_le_mul_left hfactor hdet

end AdjugateDominance

/-! ## Layer 7 — the two criteria in the Gram language -/

section GramCriteria

variable {slotCount : ℕ}

/-- The first off diagonal entry of the adjugate of a triple Gram. -/
def gramAdjOneTwo (gram : Fin slotCount → Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  gram slotTwo slotThree * gram slotThree slotOne - gram slotTwo slotOne * gram slotThree slotThree

/-- The second off diagonal entry of the adjugate of a triple Gram. -/
def gramAdjOneThree (gram : Fin slotCount → Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  gram slotTwo slotOne * gram slotThree slotTwo - gram slotTwo slotTwo * gram slotThree slotOne

/-- The third off diagonal entry of the adjugate of a triple Gram. -/
def gramAdjTwoThree (gram : Fin slotCount → Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  gram slotThree slotOne * gram slotOne slotTwo - gram slotThree slotTwo * gram slotOne slotOne

theorem gramAdjOneTwo_eq_cross (atom : Fin slotCount → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) :
    gramAdjOneTwo (atomGram atom) slotOne slotTwo slotThree
      = atomCross (atom slotTwo) (atom slotThree)
          ⬝ᵥ atomCross (atom slotThree) (atom slotOne) := by
  simp only [gramAdjOneTwo, atomGram, dotProduct, Fin.sum_univ_three, atomCross_zero,
    atomCross_one, atomCross_two]
  ring

theorem gramAdjOneThree_eq_cross (atom : Fin slotCount → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) :
    gramAdjOneThree (atomGram atom) slotOne slotTwo slotThree
      = atomCross (atom slotTwo) (atom slotThree)
          ⬝ᵥ atomCross (atom slotOne) (atom slotTwo) := by
  simp only [gramAdjOneThree, atomGram, dotProduct, Fin.sum_univ_three, atomCross_zero,
    atomCross_one, atomCross_two]
  ring

theorem gramAdjTwoThree_eq_cross (atom : Fin slotCount → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) :
    gramAdjTwoThree (atomGram atom) slotOne slotTwo slotThree
      = atomCross (atom slotThree) (atom slotOne)
          ⬝ᵥ atomCross (atom slotOne) (atom slotTwo) := by
  simp only [gramAdjTwoThree, atomGram, dotProduct, Fin.sum_univ_three, atomCross_zero,
    atomCross_one, atomCross_two]
  ring

/-- The blend of a triple of atoms reads its energy as the Gram form. -/
theorem atomTripleBlend_gram (atom : Fin slotCount → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) (valueOne valueTwo valueThree : ℝ) :
    atomTripleBlend (atom slotOne) (atom slotTwo) (atom slotThree) valueOne valueTwo valueThree
        ⬝ᵥ atomTripleBlend (atom slotOne) (atom slotTwo) (atom slotThree)
          valueOne valueTwo valueThree
      = atomGram atom slotOne slotOne * valueOne ^ 2
        + atomGram atom slotTwo slotTwo * valueTwo ^ 2
        + atomGram atom slotThree slotThree * valueThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
        + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
        + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree :=
  atomTripleBlend_energy (atom slotOne) (atom slotTwo) (atom slotThree)
    valueOne valueTwo valueThree

/-- **THE CROSS TRACE CRITERION.**  A triple with a nonzero Gram
determinant dominates when the scale weighted sum of its three two by two
Gram minors stays below that determinant.  The proof is one
Cauchy-Schwarz per cross product. -/
theorem atomTriple_values_of_crossTrace (atom : Fin slotCount → (Fin 3 → ℝ))
    (scale : Fin slotCount → ℝ) {slotOne slotTwo slotThree : Fin slotCount}
    (honePos : 0 < scale slotOne) (htwoPos : 0 < scale slotTwo)
    (hthreePos : 0 < scale slotThree)
    (hdet : 0 < gramTripleDet (atomGram atom) slotOne slotTwo slotThree)
    (hcrit : scale slotOne * gramPairDet (atomGram atom) slotTwo slotThree
        + scale slotTwo * gramPairDet (atomGram atom) slotThree slotOne
        + scale slotThree * gramPairDet (atomGram atom) slotOne slotTwo
      ≤ gramTripleDet (atomGram atom) slotOne slotTwo slotThree)
    (valueOne valueTwo valueThree : ℝ) :
    scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
        + scale slotThree * valueThree ^ 2
      ≤ atomGram atom slotOne slotOne * valueOne ^ 2
        + atomGram atom slotTwo slotTwo * valueTwo ^ 2
        + atomGram atom slotThree slotThree * valueThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
        + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
        + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree := by
  rw [gramTripleDet_eq_det_sq atom slotOne slotTwo slotThree] at hdet hcrit
  rw [gramPairDet_eq_crossEnergy atom slotTwo slotThree,
    gramPairDet_eq_crossEnergy atom slotThree slotOne,
    gramPairDet_eq_crossEnergy atom slotOne slotTwo] at hcrit
  rw [← atomTripleBlend_gram atom slotOne slotTwo slotThree valueOne valueTwo valueThree]
  exact tripleValues_of_crossTrace honePos htwoPos hthreePos hdet hcrit
    valueOne valueTwo valueThree

/-- **THE ADJUGATE DOMINANCE CRITERION.**  A triple with a nonzero Gram
determinant dominates when the scale weighted adjugate of its Gram is
diagonally dominant against that determinant. -/
theorem atomTriple_values_of_adjugateDominance (atom : Fin slotCount → (Fin 3 → ℝ))
    (scale : Fin slotCount → ℝ) {slotOne slotTwo slotThree : Fin slotCount}
    (honePos : 0 < scale slotOne) (htwoPos : 0 < scale slotTwo)
    (hthreePos : 0 < scale slotThree)
    (hdet : 0 < gramTripleDet (atomGram atom) slotOne slotTwo slotThree)
    (hone : scale slotOne * gramPairDet (atomGram atom) slotTwo slotThree
        + scale slotTwo * |gramAdjOneTwo (atomGram atom) slotOne slotTwo slotThree|
        + scale slotThree * |gramAdjOneThree (atomGram atom) slotOne slotTwo slotThree|
      ≤ gramTripleDet (atomGram atom) slotOne slotTwo slotThree)
    (htwo : scale slotTwo * gramPairDet (atomGram atom) slotThree slotOne
        + scale slotOne * |gramAdjOneTwo (atomGram atom) slotOne slotTwo slotThree|
        + scale slotThree * |gramAdjTwoThree (atomGram atom) slotOne slotTwo slotThree|
      ≤ gramTripleDet (atomGram atom) slotOne slotTwo slotThree)
    (hthree : scale slotThree * gramPairDet (atomGram atom) slotOne slotTwo
        + scale slotOne * |gramAdjOneThree (atomGram atom) slotOne slotTwo slotThree|
        + scale slotTwo * |gramAdjTwoThree (atomGram atom) slotOne slotTwo slotThree|
      ≤ gramTripleDet (atomGram atom) slotOne slotTwo slotThree)
    (valueOne valueTwo valueThree : ℝ) :
    scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
        + scale slotThree * valueThree ^ 2
      ≤ atomGram atom slotOne slotOne * valueOne ^ 2
        + atomGram atom slotTwo slotTwo * valueTwo ^ 2
        + atomGram atom slotThree slotThree * valueThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
        + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
        + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree := by
  rw [gramTripleDet_eq_det_sq atom slotOne slotTwo slotThree] at hdet hone htwo hthree
  rw [gramPairDet_eq_crossEnergy atom slotTwo slotThree,
    gramAdjOneTwo_eq_cross atom slotOne slotTwo slotThree,
    gramAdjOneThree_eq_cross atom slotOne slotTwo slotThree] at hone
  rw [gramPairDet_eq_crossEnergy atom slotThree slotOne,
    gramAdjOneTwo_eq_cross atom slotOne slotTwo slotThree,
    gramAdjTwoThree_eq_cross atom slotOne slotTwo slotThree] at htwo
  rw [gramPairDet_eq_crossEnergy atom slotOne slotTwo,
    gramAdjOneThree_eq_cross atom slotOne slotTwo slotThree,
    gramAdjTwoThree_eq_cross atom slotOne slotTwo slotThree] at hthree
  rw [← atomTripleBlend_gram atom slotOne slotTwo slotThree valueOne valueTwo valueThree]
  exact tripleValues_of_adjugateDominance honePos htwoPos hthreePos hdet hone htwo hthree
    valueOne valueTwo valueThree

/-- The cross trace criterion delivers a weak carrier of the residue. -/
theorem exists_weakCarrier_of_crossTrace {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (honePos : 0 < scale slotOne) (htwoPos : 0 < scale slotTwo)
    (hthreePos : 0 < scale slotThree)
    (hdet : 0 < gramTripleDet (atomGram atom) slotOne slotTwo slotThree)
    (hcrit : scale slotOne * gramPairDet (atomGram atom) slotTwo slotThree
        + scale slotTwo * gramPairDet (atomGram atom) slotThree slotOne
        + scale slotThree * gramPairDet (atomGram atom) slotOne slotTwo
      ≤ gramTripleDet (atomGram atom) slotOne slotTwo slotThree) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe :=
  exists_weakCarrier_of_values honeTwo honeThree htwoThree
    (atomTriple_values_of_crossTrace atom scale honePos htwoPos hthreePos hdet hcrit)

end GramCriteria

/-! ## Layer 8 — the two level determinantal identities -/

section Determinantal

variable {slotCount : ℕ}

/-- **THE ROW TOTAL OF THE TWO BY TWO MINORS.**  At rank three the two by
two Gram minors of one slot against all slots add to twice the squared
length of that atom. -/
theorem gramPairDet_row_total (atom : Fin slotCount → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (slot : Fin slotCount) :
    (∑ other, gramPairDet (atomGram atom) slot other) = 2 * atomGram atom slot slot := by
  have hcross := atomGram_cross_total atom hframe slot
  have hcell : ∀ other : Fin slotCount,
      gramPairDet (atomGram atom) slot other
        = atomGram atom slot slot * atomGram atom other other
          - (atomGram atom slot other) ^ 2 := by
    intro other
    simp only [gramPairDet, atomGram_comm atom other slot]
    ring
  rw [Finset.sum_congr rfl fun other _ => hcell other, hcross]
  norm_num

/-- **THE TOTAL OF THE TWO BY TWO MINORS.**  At rank three and six slots
the fifteen unordered two by two Gram minors add to three. -/
theorem gramPairDet_total (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ slot, ∑ other, gramPairDet (atomGram atom) slot other) = 6 := by
  rw [Finset.sum_congr rfl fun slot _ => gramPairDet_row_total atom hframe slot,
    ← Finset.mul_sum, atomGram_trace hframe]
  norm_num

end Determinantal

/-! ## Layer 9 — the four slot rung and the drop of one slot -/

section Quad

/-- The dot product of a vector against a combination of two directions. -/
theorem dot_combination (probe dirOne dirTwo : Fin 3 → ℝ) (alpha beta : ℝ) :
    probe ⬝ᵥ (fun index => alpha * dirOne index + beta * dirTwo index)
      = alpha * (probe ⬝ᵥ dirOne) + beta * (probe ⬝ᵥ dirTwo) := by
  simp only [dotProduct, Fin.sum_univ_three]
  ring

/-- **THE FOUR SLOT COVER, THE LADDER RUNG BELOW THE RESIDUE.**  Six tight
frame atoms of rank three with six positive scales of total one carry a
set of FOUR slots whose scaled atom operator dominates the identity.  The
residue asks for three. -/
def AtomQuadCoverClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ car : Finset (Fin 6), car.card = 4
      ∧ ∀ direction : Fin 3 → ℝ,
          direction ⬝ᵥ direction
            ≤ ∑ slot ∈ car, (atom slot ⬝ᵥ direction) ^ 2 / scale slot

/-- **THE RESIDUE IMPLIES THE RUNG.**  A covering triple grows to a
covering quadruple, so the rung is a genuine weakening. -/
theorem atomQuadCoverClosed_of_atomVertexCover (hvertex : AtomVertexCoverClosed) :
    AtomQuadCoverClosed := by
  classical
  intro atom scale hpos hmass hframe
  obtain ⟨car, hcard, hdom⟩ := hvertex atom scale hpos hmass hframe
  obtain ⟨big, hsub, -, hbigcard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ car)
      (by rw [hcard]; norm_num : car.card ≤ 4) (by simp)
  exact ⟨big, hbigcard, fun direction =>
    atomCover_mono_subset atom scale hpos hsub direction (hdom direction)⟩

/-- **THE LIGHT PAIR CRITERION FOR THE RUNG.**  When a pair of slots reads
every direction below the complement of the largest remaining scale, the
four remaining slots cover.  Three lines: the reading law splits, the
largest scale bounds every denominator, and the two cancel. -/
theorem quadCover_of_lightPair (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hpos : ∀ slot, 0 < scale slot)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {slotOne slotTwo : Fin 6} (hne : slotOne ≠ slotTwo) {cap : ℝ} (hcapPos : 0 < cap)
    (hbound : ∀ slot, slot ∉ ({slotOne, slotTwo} : Finset (Fin 6)) → scale slot ≤ cap)
    (hlight : ∀ direction : Fin 3 → ℝ,
      (atom slotOne ⬝ᵥ direction) ^ 2 + (atom slotTwo ⬝ᵥ direction) ^ 2
        ≤ (1 - cap) * (direction ⬝ᵥ direction))
    (direction : Fin 3 → ℝ) :
    direction ⬝ᵥ direction
      ≤ ∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
          (atom slot ⬝ᵥ direction) ^ 2 / scale slot := by
  classical
  have hsplit := Finset.sum_add_sum_compl ({slotOne, slotTwo} : Finset (Fin 6))
    (fun slot => (atom slot ⬝ᵥ direction) ^ 2)
  have hpair : (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6)),
      (atom slot ⬝ᵥ direction) ^ 2)
      = (atom slotOne ⬝ᵥ direction) ^ 2 + (atom slotTwo ⬝ᵥ direction) ^ 2 :=
    Finset.sum_pair hne
  have hreading := atomReading_sum atom hframe direction
  rw [hpair, hreading] at hsplit
  have hlow := hlight direction
  have hrest : cap * (direction ⬝ᵥ direction)
      ≤ ∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ, (atom slot ⬝ᵥ direction) ^ 2 := by
    linarith
  have hterm : ∀ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
      (atom slot ⬝ᵥ direction) ^ 2 / cap ≤ (atom slot ⬝ᵥ direction) ^ 2 / scale slot := by
    intro slot hslot
    exact div_le_div_of_nonneg_left (sq_nonneg _) (hpos slot)
      (hbound slot (Finset.mem_compl.mp hslot))
  have hsum : (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
        (atom slot ⬝ᵥ direction) ^ 2) / cap
      ≤ ∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
        (atom slot ⬝ᵥ direction) ^ 2 / scale slot := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum hterm
  have hdiv : direction ⬝ᵥ direction
      ≤ (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
          (atom slot ⬝ᵥ direction) ^ 2) / cap := by
    rw [le_div_iff₀ hcapPos]
    linarith
  linarith

/-- The scalar form of the light pair hypothesis: two atoms whose squared
lengths total below the complement of the cap are a light pair. -/
theorem lightPair_of_marginal (atom : Fin 6 → (Fin 3 → ℝ)) {slotOne slotTwo : Fin 6} {cap : ℝ}
    (hmarginal : atomGram atom slotOne slotOne + atomGram atom slotTwo slotTwo ≤ 1 - cap)
    (direction : Fin 3 → ℝ) :
    (atom slotOne ⬝ᵥ direction) ^ 2 + (atom slotTwo ⬝ᵥ direction) ^ 2
      ≤ (1 - cap) * (direction ⬝ᵥ direction) := by
  have hone := atomDot_sq_le_energy (atom slotOne) direction
  have htwo := atomDot_sq_le_energy (atom slotTwo) direction
  have henergy := atomDot_self_nonneg direction
  have hgramOne : atomGram atom slotOne slotOne = atom slotOne ⬝ᵥ atom slotOne := rfl
  have hgramTwo : atomGram atom slotTwo slotTwo = atom slotTwo ⬝ᵥ atom slotTwo := rfl
  rw [hgramOne, hgramTwo] at hmarginal
  nlinarith [hone, htwo, henergy, hmarginal]

/-- **THE DROPPED SLOT COSTS ONLY ITS OWN READING.**  If a set of slots
covers, then after one slot is erased the rest still cover every
direction that the erased atom does not read.  The deficiency of a drop
lives inside one plane. -/
theorem atomCover_erase_of_orthogonal (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    {car : Finset (Fin 6)} {pivot : Fin 6} (hpivot : pivot ∈ car)
    (hcover : ∀ direction : Fin 3 → ℝ,
      direction ⬝ᵥ direction ≤ ∑ slot ∈ car, (atom slot ⬝ᵥ direction) ^ 2 / scale slot)
    {direction : Fin 3 → ℝ} (horth : atom pivot ⬝ᵥ direction = 0) :
    direction ⬝ᵥ direction
      ≤ ∑ slot ∈ car.erase pivot, (atom slot ⬝ᵥ direction) ^ 2 / scale slot := by
  classical
  have hsplit := Finset.add_sum_erase car
    (fun slot => (atom slot ⬝ᵥ direction) ^ 2 / scale slot) hpivot
  have hzero : (atom pivot ⬝ᵥ direction) ^ 2 / scale pivot = 0 := by
    rw [horth]
    simp
  rw [hzero, zero_add] at hsplit
  rw [hsplit]
  exact hcover direction

/-- **THE DEFICIENCY OF A DROP IS AT MOST ONE DIMENSIONAL.**  Given a
covering set and a dropped slot, every plane of directions carries a
nonzero combination that the remaining slots still cover.  This is the
inertia statement of the drop: the erased operator falls short of the
identity in at most one direction. -/
theorem exists_covered_combination_of_erase (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    {car : Finset (Fin 6)} {pivot : Fin 6} (hpivot : pivot ∈ car)
    (hcover : ∀ direction : Fin 3 → ℝ,
      direction ⬝ᵥ direction ≤ ∑ slot ∈ car, (atom slot ⬝ᵥ direction) ^ 2 / scale slot)
    (dirOne dirTwo : Fin 3 → ℝ) :
    ∃ alpha beta : ℝ, (alpha ≠ 0 ∨ beta ≠ 0)
      ∧ (fun index => alpha * dirOne index + beta * dirTwo index)
            ⬝ᵥ (fun index => alpha * dirOne index + beta * dirTwo index)
          ≤ ∑ slot ∈ car.erase pivot,
              (atom slot ⬝ᵥ (fun index => alpha * dirOne index + beta * dirTwo index)) ^ 2
                / scale slot := by
  classical
  by_cases hfirst : atom pivot ⬝ᵥ dirOne = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    refine atomCover_erase_of_orthogonal atom scale hpivot hcover ?_
    rw [dot_combination, hfirst]
    ring
  · refine ⟨atom pivot ⬝ᵥ dirTwo, -(atom pivot ⬝ᵥ dirOne), Or.inr (neg_ne_zero.mpr hfirst), ?_⟩
    refine atomCover_erase_of_orthogonal atom scale hpivot hcover ?_
    rw [dot_combination]
    ring

/-- **THE DROP OF ONE SLOT.**  Every covering set of four slots carries a
slot whose removal leaves a covering triple. -/
def AtomQuadDropClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    ∀ car : Finset (Fin 6), car.card = 4 →
    (∀ direction : Fin 3 → ℝ,
      direction ⬝ᵥ direction ≤ ∑ slot ∈ car, (atom slot ⬝ᵥ direction) ^ 2 / scale slot) →
    ∃ pivot ∈ car, ∀ direction : Fin 3 → ℝ,
      direction ⬝ᵥ direction
        ≤ ∑ slot ∈ car.erase pivot, (atom slot ⬝ᵥ direction) ^ 2 / scale slot

/-- **THE FACTORED RESIDUE.**  Some covering set of four slots carries a
slot whose removal leaves a covering triple. -/
def AtomQuadDropSomeClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ car : Finset (Fin 6), car.card = 4
      ∧ (∀ direction : Fin 3 → ℝ,
          direction ⬝ᵥ direction ≤ ∑ slot ∈ car, (atom slot ⬝ᵥ direction) ^ 2 / scale slot)
      ∧ ∃ pivot ∈ car, ∀ direction : Fin 3 → ℝ,
          direction ⬝ᵥ direction
            ≤ ∑ slot ∈ car.erase pivot, (atom slot ⬝ᵥ direction) ^ 2 / scale slot

/-- The factored residue gives the integral cover. -/
theorem atomVertexCoverClosed_of_quadDropSome (hdrop : AtomQuadDropSomeClosed) :
    AtomVertexCoverClosed := by
  classical
  intro atom scale hpos hmass hframe
  obtain ⟨car, hcard, -, pivot, hpivot, herase⟩ := hdrop atom scale hpos hmass hframe
  refine ⟨car.erase pivot, ?_, herase⟩
  rw [Finset.card_erase_of_mem hpivot, hcard]

/-- The integral cover gives the factored residue. -/
theorem atomQuadDropSomeClosed_of_atomVertexCover (hvertex : AtomVertexCoverClosed) :
    AtomQuadDropSomeClosed := by
  classical
  intro atom scale hpos hmass hframe
  obtain ⟨car, hcard, hdom⟩ := hvertex atom scale hpos hmass hframe
  obtain ⟨big, hsub, -, hbigcard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ car)
      (by rw [hcard]; norm_num : car.card ≤ 4) (by simp)
  have hbigcover : ∀ direction : Fin 3 → ℝ,
      direction ⬝ᵥ direction ≤ ∑ slot ∈ big, (atom slot ⬝ᵥ direction) ^ 2 / scale slot :=
    fun direction => atomCover_mono_subset atom scale hpos hsub direction (hdom direction)
  have hssub : car ⊂ big := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro heq
    rw [heq, hbigcard] at hcard
    norm_num at hcard
  obtain ⟨pivot, hpivotBig, hpivotNot⟩ := Finset.exists_of_ssubset hssub
  refine ⟨big, hbigcard, hbigcover, pivot, hpivotBig, fun direction => ?_⟩
  refine atomCover_mono_subset atom scale hpos ?_ direction (hdom direction)
  intro slot hslot
  exact Finset.mem_erase.mpr ⟨fun heq => hpivotNot (heq ▸ hslot), hsub hslot⟩

/-- **THE RESIDUE FACTORS THROUGH THE FOUR SLOT RUNG.**  The integral
cover and the factored residue are one statement, so nothing is lost in
the passage.  The gain is that the rung carries a margin at the sharp
extremal while the residue does not. -/
theorem atomQuadDropSomeClosed_iff_atomVertexCover :
    AtomQuadDropSomeClosed ↔ AtomVertexCoverClosed :=
  ⟨atomVertexCoverClosed_of_quadDropSome, atomQuadDropSomeClosed_of_atomVertexCover⟩

/-- **THE RUNG AND THE DROP TOGETHER CLOSE THE RESIDUE.** -/
theorem atomVertexCoverClosed_of_quad_and_drop (hquad : AtomQuadCoverClosed)
    (hdrop : AtomQuadDropClosed) : AtomVertexCoverClosed := by
  refine atomVertexCoverClosed_of_quadDropSome ?_
  intro atom scale hpos hmass hframe
  obtain ⟨car, hcard, hcover⟩ := hquad atom scale hpos hmass hframe
  obtain ⟨pivot, hpivot, herase⟩ := hdrop atom scale hpos car hcard hcover
  exact ⟨car, hcard, hcover, pivot, hpivot, herase⟩

/-- **THE CELL FROM THE RUNG AND THE DROP.** -/
theorem gtzWeighted_six_three_of_quad_and_drop (hquad : AtomQuadCoverClosed)
    (hdrop : AtomQuadDropClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomVertexCover (atomVertexCoverClosed_of_quad_and_drop hquad hdrop)

end Quad

/-! ## Layer 10 — the calibration against the sharp extremal -/

section Calibration

/-- The hypothesis of the cross trace criterion at one triple. -/
def AtomTripleCrossTrace (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (slotOne slotTwo slotThree : Fin 6) : Prop :=
  0 < gramTripleDet (atomGram atom) slotOne slotTwo slotThree
    ∧ scale slotOne * gramPairDet (atomGram atom) slotTwo slotThree
        + scale slotTwo * gramPairDet (atomGram atom) slotThree slotOne
        + scale slotThree * gramPairDet (atomGram atom) slotOne slotTwo
      ≤ gramTripleDet (atomGram atom) slotOne slotTwo slotThree

/-- The hypothesis of the adjugate dominance criterion at one triple. -/
def AtomTripleAdjugateDominance (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (slotOne slotTwo slotThree : Fin 6) : Prop :=
  0 < gramTripleDet (atomGram atom) slotOne slotTwo slotThree
    ∧ scale slotOne * gramPairDet (atomGram atom) slotTwo slotThree
        + scale slotTwo * |gramAdjOneTwo (atomGram atom) slotOne slotTwo slotThree|
        + scale slotThree * |gramAdjOneThree (atomGram atom) slotOne slotTwo slotThree|
      ≤ gramTripleDet (atomGram atom) slotOne slotTwo slotThree
    ∧ scale slotTwo * gramPairDet (atomGram atom) slotThree slotOne
        + scale slotOne * |gramAdjOneTwo (atomGram atom) slotOne slotTwo slotThree|
        + scale slotThree * |gramAdjTwoThree (atomGram atom) slotOne slotTwo slotThree|
      ≤ gramTripleDet (atomGram atom) slotOne slotTwo slotThree
    ∧ scale slotThree * gramPairDet (atomGram atom) slotOne slotTwo
        + scale slotOne * |gramAdjOneThree (atomGram atom) slotOne slotTwo slotThree|
        + scale slotTwo * |gramAdjTwoThree (atomGram atom) slotOne slotTwo slotThree|
      ≤ gramTripleDet (atomGram atom) slotOne slotTwo slotThree

/-- **THE CROSS TRACE CRITERION FAILS AT EVERY TRIPLE OF THE SHARP
EXTREMAL.**  The doubled tetrahedron carries twelve tied triples and no
strict one, so no criterion that leaves slack can read it.  Eight triples
repeat a direction and carry a vanishing Gram determinant, and the
remaining twelve carry a scale weighted minor total of exactly three
halves of that determinant. -/
theorem not_atomTripleCrossTrace_boundaryWitness {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) :
    ¬ AtomTripleCrossTrace atomBoundaryAtom atomBoundaryScale slotOne slotTwo slotThree := by
  simp only [AtomTripleCrossTrace, gramTripleDet, gramPairDet, atomBoundaryAtom_gram]
  fin_cases slotOne <;> fin_cases slotTwo <;> fin_cases slotThree <;>
    first
      | exact absurd rfl honeTwo
      | exact absurd rfl honeThree
      | exact absurd rfl htwoThree
      | norm_num [atomBoundaryGram, atomBoundaryScale]

/-- **THE ADJUGATE DOMINANCE CRITERION FAILS AT EVERY TRIPLE OF THE SHARP
EXTREMAL.** -/
theorem not_atomTripleAdjugateDominance_boundaryWitness {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) :
    ¬ AtomTripleAdjugateDominance atomBoundaryAtom atomBoundaryScale
        slotOne slotTwo slotThree := by
  simp only [AtomTripleAdjugateDominance, gramTripleDet, gramPairDet, gramAdjOneTwo,
    gramAdjOneThree, gramAdjTwoThree, atomBoundaryAtom_gram]
  fin_cases slotOne <;> fin_cases slotTwo <;> fin_cases slotThree <;>
    first
      | exact absurd rfl honeTwo
      | exact absurd rfl honeThree
      | exact absurd rfl htwoThree
      | norm_num [atomBoundaryGram, atomBoundaryScale]

/-- The selection form of the cross trace criterion. -/
def AtomTripleCrossTraceClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ AtomTripleCrossTrace atom scale slotOne slotTwo slotThree

/-- The selection form of the adjugate dominance criterion. -/
def AtomTripleAdjugateDominanceClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ AtomTripleAdjugateDominance atom scale slotOne slotTwo slotThree

/-- The cross trace selection closes the residue, thus it is a statement
STRICTLY STRONGER than the cell. -/
theorem atomTripleBoundaryClosed_of_crossTraceClosed
    (hclosed : AtomTripleCrossTraceClosed) : AtomTripleBoundaryClosed := by
  intro atom scale hpos hmass hframe
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hdet, hcrit⟩ :=
    hclosed atom scale hpos hmass hframe
  exact exists_weakCarrier_of_crossTrace honeTwo honeThree htwoThree (hpos slotOne)
    (hpos slotTwo) (hpos slotThree) hdet hcrit

/-- The adjugate dominance selection closes the residue too. -/
theorem atomTripleBoundaryClosed_of_adjugateDominanceClosed
    (hclosed : AtomTripleAdjugateDominanceClosed) : AtomTripleBoundaryClosed := by
  intro atom scale hpos hmass hframe
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hdet, hone, htwo,
    hthree⟩ := hclosed atom scale hpos hmass hframe
  exact exists_weakCarrier_of_values honeTwo honeThree htwoThree
    (atomTriple_values_of_adjugateDominance atom scale (hpos slotOne) (hpos slotTwo)
      (hpos slotThree) hdet hone htwo hthree)

/-- **THE CROSS TRACE SELECTION IS FALSE.**  The sharp extremal refutes
it at all twenty triples, so no proof of the cell can run through it. -/
theorem not_atomTripleCrossTraceClosed : ¬ AtomTripleCrossTraceClosed := by
  intro hclosed
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hcrit⟩ :=
    hclosed atomBoundaryAtom atomBoundaryScale atomBoundaryScale_pos atomBoundaryScale_sum
      atomBoundaryAtom_isTightFrame
  exact not_atomTripleCrossTrace_boundaryWitness honeTwo honeThree htwoThree hcrit

/-- **THE ADJUGATE DOMINANCE SELECTION IS FALSE.** -/
theorem not_atomTripleAdjugateDominanceClosed : ¬ AtomTripleAdjugateDominanceClosed := by
  intro hclosed
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hcrit⟩ :=
    hclosed atomBoundaryAtom atomBoundaryScale atomBoundaryScale_pos atomBoundaryScale_sum
      atomBoundaryAtom_isTightFrame
  exact not_atomTripleAdjugateDominance_boundaryWitness honeTwo honeThree htwoThree hcrit

end Calibration

/-! ## Layer 11 — the necessary laws of a dominating triple -/

section Necessary

variable {slotCount : ℕ}

/-- **THE GAP FORM IS STRICTLY POSITIVE ON A NONZERO READING.**  With the
largest scale strictly below one the margin is strictly positive, so the
gap form is positive definite on the range of the projection. -/
theorem atomGap_reading_pos {rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {cap : ℝ} (hcap : ∀ slot, scale slot ≤ cap) (hcapLt : cap < 1)
    {direction : Fin rank → ℝ} (hne : direction ≠ 0) :
    0 < (atomBlend atom (fun slot => atom slot ⬝ᵥ direction)
            ⬝ᵥ atomBlend atom (fun slot => atom slot ⬝ᵥ direction))
        - ∑ slot, scale slot * (atom slot ⬝ᵥ direction) ^ 2 := by
  have hmargin := atomGap_reading_ge atom scale hframe hcap direction
  have henergy : 0 < direction ⬝ᵥ direction := by
    rcases (atomDot_self_nonneg direction).lt_or_eq with hpos | hzero
    · exact hpos
    · exact absurd (atomDot_eq_zero_of_energy_nonpos (le_of_eq hzero.symm)) hne
  nlinarith [hmargin, henergy, hcapLt]

/-- **THE PAIR MINOR OF A DOMINATING TRIPLE.**  Every pair inside a
dominating triple carries a nonnegative shifted minor.  This is the two by
two Sylvester law of the gap form, read on a coordinate plane. -/
theorem atomPair_minor_of_values (atom : Fin slotCount → (Fin 3 → ℝ))
    (scale : Fin slotCount → ℝ) {slotOne slotTwo slotThree : Fin slotCount}
    (hvalues : ∀ valueOne valueTwo valueThree : ℝ,
      scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
          + scale slotThree * valueThree ^ 2
        ≤ atomGram atom slotOne slotOne * valueOne ^ 2
          + atomGram atom slotTwo slotTwo * valueTwo ^ 2
          + atomGram atom slotThree slotThree * valueThree ^ 2
          + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
          + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
          + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree) :
    (atomGram atom slotOne slotTwo) ^ 2
      ≤ (atomGram atom slotOne slotOne - scale slotOne)
        * (atomGram atom slotTwo slotTwo - scale slotTwo) := by
  have hdiagOne := hvalues 1 0 0
  have hdiagTwo := hvalues 0 1 0
  have hshiftOne : 0 ≤ atomGram atom slotOne slotOne - scale slotOne := by nlinarith [hdiagOne]
  have hshiftTwo : 0 ≤ atomGram atom slotTwo slotTwo - scale slotTwo := by nlinarith [hdiagTwo]
  have hprobeOne := hvalues (-(atomGram atom slotOne slotTwo))
    (atomGram atom slotOne slotOne - scale slotOne) 0
  have hprobeTwo := hvalues (atomGram atom slotTwo slotTwo - scale slotTwo)
    (-(atomGram atom slotOne slotTwo)) 0
  have hprobeThree := hvalues (atomGram atom slotOne slotTwo) (-1) 0
  rcases hshiftOne.lt_or_eq with hpos | hzero
  · nlinarith [hprobeOne, hpos, hshiftTwo]
  · nlinarith [hprobeTwo, hprobeThree, hzero, hshiftTwo,
      sq_nonneg (atomGram atom slotOne slotTwo),
      mul_nonneg hshiftTwo (sq_nonneg (atomGram atom slotOne slotTwo))]

/-- **A PARALLEL PAIR NEVER DOMINATES.**  When two slots carry a vanishing
two by two Gram minor, no triple that holds both of them dominates.  This
is why eight of the twenty triples of the sharp extremal fail outright. -/
theorem not_values_of_parallel_pair (atom : Fin slotCount → (Fin 3 → ℝ))
    (scale : Fin slotCount → ℝ) {slotOne slotTwo slotThree : Fin slotCount}
    (honePos : 0 < scale slotOne) (htwoPos : 0 < scale slotTwo)
    (hparallel : gramPairDet (atomGram atom) slotOne slotTwo = 0) :
    ¬ (∀ valueOne valueTwo valueThree : ℝ,
      scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
          + scale slotThree * valueThree ^ 2
        ≤ atomGram atom slotOne slotOne * valueOne ^ 2
          + atomGram atom slotTwo slotTwo * valueTwo ^ 2
          + atomGram atom slotThree slotThree * valueThree ^ 2
          + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
          + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
          + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree) := by
  intro hvalues
  have hminor := atomPair_minor_of_values atom scale hvalues
  have hdiagOne := hvalues 1 0 0
  have hdiagTwo := hvalues 0 1 0
  have hshiftOne : scale slotOne ≤ atomGram atom slotOne slotOne := by nlinarith [hdiagOne]
  have hshiftTwo : scale slotTwo ≤ atomGram atom slotTwo slotTwo := by nlinarith [hdiagTwo]
  have hpar : (atomGram atom slotOne slotTwo) ^ 2
      = atomGram atom slotOne slotOne * atomGram atom slotTwo slotTwo := by
    simp only [gramPairDet, atomGram_comm atom slotTwo slotOne] at hparallel
    nlinarith [hparallel]
  nlinarith [hminor, hpar, hshiftOne, hshiftTwo, honePos, htwoPos]

end Necessary

/-! ## Layer 12 — the scalar form of the rung criterion -/

section RungScalar

/-- **THE SCALAR RUNG CRITERION.**  When two slots carry squared lengths
totalling at most the complement of the largest remaining scale, the four
remaining slots cover.  Everything is a marginal and a scale. -/
theorem exists_quadCover_of_lightMarginalPair (atom : Fin 6 → (Fin 3 → ℝ))
    (scale : Fin 6 → ℝ) (hpos : ∀ slot, 0 < scale slot)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {slotOne slotTwo : Fin 6} (hne : slotOne ≠ slotTwo) {cap : ℝ} (hcapPos : 0 < cap)
    (hbound : ∀ slot, slot ∉ ({slotOne, slotTwo} : Finset (Fin 6)) → scale slot ≤ cap)
    (hmarginal : atomGram atom slotOne slotOne + atomGram atom slotTwo slotTwo ≤ 1 - cap) :
    ∃ car : Finset (Fin 6), car.card = 4
      ∧ ∀ direction : Fin 3 → ℝ,
          direction ⬝ᵥ direction
            ≤ ∑ slot ∈ car, (atom slot ⬝ᵥ direction) ^ 2 / scale slot := by
  classical
  refine ⟨({slotOne, slotTwo} : Finset (Fin 6))ᶜ, ?_, ?_⟩
  · rw [Finset.card_compl, Finset.card_pair hne]
    simp
  · exact quadCover_of_lightPair atom scale hpos hframe hne hcapPos hbound
      (lightPair_of_marginal atom hmarginal)

end RungScalar

end Gtz
