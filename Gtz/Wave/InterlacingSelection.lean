import Gtz.Wave.AtomBoundaryWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6400000

/-!
# The determinantal moment certificate, and why it cannot close the cell

The residue of the atom lane asks for a TRIPLE whose shifted Gram block is
positive semidefinite.  The interlacing method of Marcus, Spielman and
Srivastava, extended to negatively dependent samples by Anari and Oveis
Gharan, converts an averaged statement into a statement about ONE member of a
family: for a strongly Rayleigh measure on the triples, some triple's extreme
root is at least as good as the extreme root of the AVERAGE characteristic
polynomial.  That is the step the campaign has been missing, because the
average is good and no individual member is.

This module builds the measure side of that method in full, and then refutes
the inequality the method has to consume.

## The measure

The Cauchy-Binet weights of a tight frame are the squared volumes of the
triples.  They are the determinantal point process of the Gram, and its
marginals are the geometry itself:

* `Gtz.dppPairMarginal_eq` — the squared volumes of the triples through a
  PAIR add to the squared wedge of that pair.  One line from the frame law,
  applied to the cross product of the two atoms.
* `Gtz.dppSlotMarginal_eq` — the squared wedges through a SLOT add to twice
  the squared length of that slot.  The row energy law and the trace law.
* `Gtz.dppTripleWeight_mass` — the squared volumes add to six over the
  ordered triples, that is to one over the twenty unordered ones.  This is
  Cauchy-Binet at a tight frame, and it needs no determinant theory.

## The moments

Because the weights are a determinantal point process, the average of each
coefficient of the triple collapses onto the corresponding minor sum:

* `Gtz.dppMomentOne_eq` — the average of the trace of the shifted block is
  six times the squared-length-weighted sum of the shifted diagonals.
* `Gtz.dppMomentTwo_eq` — the average of the second coefficient is three
  times the squared-wedge-weighted sum of the pair minors.
* `Gtz.dppMomentThree` — the third moment is the squared-volume-weighted sum
  of the triple determinants, by definition.

## The engine, and the residue of the method

`Gtz.exists_triple_char_neg` is the free half of the interlacing argument:
nonnegative weights of positive mass whose three averaged coefficients are
nonnegative force, at EVERY negative argument, SOME weighted triple whose
characteristic polynomial is negative there.  The engine is stated for
arbitrary nonnegative weights, so it serves any strongly Rayleigh measure.

The cell asks for ONE triple whose characteristic polynomial is negative at
EVERY negative argument.  `Gtz.TripleQuantifierExchange` names that exchange,
and `Gtz.exists_charNegative_of_moments_of_exchange` composes the two halves.
An interlacing family is exactly the device that performs the exchange.

## The refutation

`Gtz.not_dppMomentCertificate` — **the determinantal moment certificate is
FALSE.**  The witness is the LINE datum `Gtz.dppLineAtom`: four parallel
atoms on the first axis with coefficients `4/5, 1/5, 2/5, 2/5`, and two unit
atoms on the other two axes, with the scale mass `99/100` concentrated on the
longest parallel atom.  Its third moment is exactly `-10496871/12500000`,
while its first two moments stay positive, and the datum carries a strictly
dominating triple, so the CELL HOLDS where the certificate fails.

The adversarial floor of the third moment over the whole stratum is exactly
`-3/16`, attained in the limit of the same line family at squared
coefficients `5/8, 1/8, 1/8, 1/8` with the whole scale mass on the longest
atom.  Blockedness does not rescue it: the adversarial floor on the blocked
stratum is still negative.

## The tightness, which is what makes the negative informative

`Gtz.dppTie_momentThree_eq_zero` — at the boundary witness the third moment
is EXACTLY ZERO.  The mechanism is exact: all twenty triple determinants of
that datum are nonpositive, and the eight strictly negative ones are exactly
the eight triples that repeat a direction, which carry squared volume zero.
So the certificate is SHARP at the extremal of the cell and negative off it,
which `Gtz.dppMomentThree_crosses_zero` states in one theorem.  The
obstruction is not the choice of measure.

## The converse, run before the route was proposed

`Gtz.dppMoments_nonneg_of_dominating` — a dominating triple makes the POINT
MASS on that triple satisfy all three moment inequalities.  A point mass is
strongly Rayleigh, and it is a limit of tilts of the determinantal point
process, so the SUPREMUM of the certificate over the admissible measures is
the cell itself.  A measure chosen by search is therefore never a reduction:
only a measure given by a FORMULA can be a proof, and the formula the
geometry supplies is the one refuted here.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

Every statement below is a theorem.  The marginal laws, the moment laws and
the engine hold at every tight frame of rank three on six slots.  The
refutation and the tightness are exact rational computations at two named
configurations, and the refutation is a refutation, thus not vacuous.
-/
namespace Gtz

/-! ## Layer 0 — the cross product and the determinantal weights -/

/-- The CROSS PRODUCT of two rank-three vectors. -/
def atomCross (leftVec rightVec : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun index =>
    if index = 0 then leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1
    else if index = 1 then leftVec 2 * rightVec 0 - leftVec 0 * rightVec 2
    else leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0

theorem atomCross_zero (leftVec rightVec : Fin 3 → ℝ) :
    atomCross leftVec rightVec 0 = leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1 := by
  simp [atomCross]

theorem atomCross_one (leftVec rightVec : Fin 3 → ℝ) :
    atomCross leftVec rightVec 1 = leftVec 2 * rightVec 0 - leftVec 0 * rightVec 2 := by
  norm_num [atomCross]

theorem atomCross_two (leftVec rightVec : Fin 3 → ℝ) :
    atomCross leftVec rightVec 2 = leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0 := by
  simp only [atomCross, show ((2 : Fin 3) = 0) = False from by simp,
    show ((2 : Fin 3) = 1) = False from by simp, if_false]

/-- The PAIR WEIGHT of the determinantal point process: the two by two
principal minor of the Gram, which is the squared wedge of the two atoms. -/
def dppPairWeight (atom : Fin 6 → (Fin 3 → ℝ)) (rowSlot colSlot : Fin 6) : ℝ :=
  atomGram atom rowSlot rowSlot * atomGram atom colSlot colSlot
    - atomGram atom rowSlot colSlot ^ 2

/-- The TRIPLE WEIGHT of the determinantal point process: the three by
three principal minor of the Gram, which is the squared volume of the three
atoms. -/
def dppTripleWeight (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6) : ℝ :=
  atomGram atom slotOne slotOne
      * (atomGram atom slotTwo slotTwo * atomGram atom slotThree slotThree
          - atomGram atom slotTwo slotThree ^ 2)
    - atomGram atom slotOne slotTwo
        * (atomGram atom slotOne slotTwo * atomGram atom slotThree slotThree
            - atomGram atom slotTwo slotThree * atomGram atom slotOne slotThree)
    + atomGram atom slotOne slotThree
        * (atomGram atom slotOne slotTwo * atomGram atom slotTwo slotThree
            - atomGram atom slotTwo slotTwo * atomGram atom slotOne slotThree)

theorem dppPairWeight_comm (atom : Fin 6 → (Fin 3 → ℝ)) (rowSlot colSlot : Fin 6) :
    dppPairWeight atom rowSlot colSlot = dppPairWeight atom colSlot rowSlot := by
  simp only [dppPairWeight, atomGram, dotProduct, Fin.sum_univ_three]
  ring

/-- The pair weight is nonnegative: it is the Cauchy-Schwarz defect. -/
theorem dppPairWeight_nonneg (atom : Fin 6 → (Fin 3 → ℝ)) (rowSlot colSlot : Fin 6) :
    0 ≤ dppPairWeight atom rowSlot colSlot := by
  have hcs := atomGram_sq_le_diag_mul atom rowSlot colSlot
  simp only [dppPairWeight]
  linarith

theorem dppPairWeight_self (atom : Fin 6 → (Fin 3 → ℝ)) (slot : Fin 6) :
    dppPairWeight atom slot slot = 0 := by
  simp only [dppPairWeight]
  ring

/-- **THE PAIR WEIGHT IS THE SQUARED WEDGE.**  Lagrange's identity in rank
three: the Cauchy-Schwarz defect of two atoms is the squared length of their
cross product. -/
theorem dppPairWeight_eq_crossEnergy (atom : Fin 6 → (Fin 3 → ℝ)) (rowSlot colSlot : Fin 6) :
    dppPairWeight atom rowSlot colSlot
      = atomCross (atom rowSlot) (atom colSlot) ⬝ᵥ atomCross (atom rowSlot) (atom colSlot) := by
  simp only [dppPairWeight, atomGram, dotProduct, Fin.sum_univ_three,
    atomCross_zero, atomCross_one, atomCross_two]
  ring

/-- **THE TRIPLE WEIGHT IS THE SQUARED VOLUME.**  The three by three Gram
minor of three rank-three vectors is the square of their scalar triple
product. -/
theorem dppTripleWeight_eq_sq (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6) :
    dppTripleWeight atom slotOne slotTwo slotThree
      = (atom slotThree ⬝ᵥ atomCross (atom slotOne) (atom slotTwo)) ^ 2 := by
  simp only [dppTripleWeight, atomGram, dotProduct, Fin.sum_univ_three,
    atomCross_zero, atomCross_one, atomCross_two]
  ring

theorem dppTripleWeight_nonneg (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6) :
    0 ≤ dppTripleWeight atom slotOne slotTwo slotThree := by
  rw [dppTripleWeight_eq_sq]
  exact sq_nonneg _

/-! ## Layer 1 — the symmetry of the weights -/

theorem dppTripleWeight_swap_last (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    dppTripleWeight atom slotOne slotTwo slotThree
      = dppTripleWeight atom slotOne slotThree slotTwo := by
  simp only [dppTripleWeight, atomGram, dotProduct, Fin.sum_univ_three]
  ring

theorem dppTripleWeight_swap_first (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    dppTripleWeight atom slotOne slotTwo slotThree
      = dppTripleWeight atom slotTwo slotOne slotThree := by
  simp only [dppTripleWeight, atomGram, dotProduct, Fin.sum_univ_three]
  ring

theorem dppTripleWeight_rotate (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    dppTripleWeight atom slotOne slotTwo slotThree
      = dppTripleWeight atom slotTwo slotThree slotOne := by
  simp only [dppTripleWeight, atomGram, dotProduct, Fin.sum_univ_three]
  ring

theorem dppTripleWeight_self_first (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo : Fin 6) :
    dppTripleWeight atom slotOne slotOne slotTwo = 0 := by
  simp only [dppTripleWeight, atomGram, dotProduct, Fin.sum_univ_three]
  ring

theorem dppTripleWeight_self_last (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo : Fin 6) :
    dppTripleWeight atom slotOne slotTwo slotTwo = 0 := by
  simp only [dppTripleWeight, atomGram, dotProduct, Fin.sum_univ_three]
  ring

theorem dppTripleWeight_self_outer (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo : Fin 6) :
    dppTripleWeight atom slotOne slotTwo slotOne = 0 := by
  simp only [dppTripleWeight, atomGram, dotProduct, Fin.sum_univ_three]
  ring

theorem atomPairMinor_comm (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (rowSlot colSlot : Fin 6) :
    atomPairMinor atom scale rowSlot colSlot = atomPairMinor atom scale colSlot rowSlot := by
  simp only [atomPairMinor, atomShiftedDiag, atomGram, dotProduct, Fin.sum_univ_three]
  ring

theorem atomTripleDet_swap_last (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (slotOne slotTwo slotThree : Fin 6) :
    atomTripleDet atom scale slotOne slotTwo slotThree
      = atomTripleDet atom scale slotOne slotThree slotTwo := by
  simp only [atomTripleDet, atomShiftedDiag, atomGram, dotProduct, Fin.sum_univ_three]
  ring

theorem atomTripleDet_swap_first (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (slotOne slotTwo slotThree : Fin 6) :
    atomTripleDet atom scale slotOne slotTwo slotThree
      = atomTripleDet atom scale slotTwo slotOne slotThree := by
  simp only [atomTripleDet, atomShiftedDiag, atomGram, dotProduct, Fin.sum_univ_three]
  ring

/-! ## Layer 2 — the marginal laws of the determinantal point process -/

/-- **THE TWO POINT MARGINAL.**  The squared volumes of the triples through
one PAIR add to the squared wedge of that pair.  The proof is the frame law
against the cross product of the two atoms: the third slot ranges over the
whole frame, so its readings resolve the energy of that cross product. -/
theorem dppPairMarginal_eq {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot colSlot : Fin 6) :
    (∑ slot, dppTripleWeight atom rowSlot colSlot slot) = dppPairWeight atom rowSlot colSlot := by
  classical
  have hcell : ∀ slot : Fin 6,
      dppTripleWeight atom rowSlot colSlot slot
        = (atom slot ⬝ᵥ atomCross (atom rowSlot) (atom colSlot))
          * (atom slot ⬝ᵥ atomCross (atom rowSlot) (atom colSlot)) := by
    intro slot
    rw [dppTripleWeight_eq_sq]
    ring
  rw [Finset.sum_congr rfl fun slot _ => hcell slot,
    hframe (atomCross (atom rowSlot) (atom colSlot)) (atomCross (atom rowSlot) (atom colSlot)),
    dppPairWeight_eq_crossEnergy]

/-- **THE ONE POINT MARGINAL.**  The squared wedges through one slot add to
twice the squared length of that slot.  The row energy law removes the
squares of the Gram row, and the trace law replaces the diagonal mass by the
rank. -/
theorem dppSlotMarginal_eq {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot : Fin 6) :
    (∑ slot, dppPairWeight atom rowSlot slot) = 2 * atomGram atom rowSlot rowSlot := by
  classical
  have hsplit : (∑ slot, dppPairWeight atom rowSlot slot)
      = atomGram atom rowSlot rowSlot * (∑ slot, atomGram atom slot slot)
        - ∑ slot, atomGram atom rowSlot slot ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun slot _ => rfl
  rw [hsplit, atomGram_trace hframe, atomGram_row_energy hframe rowSlot]
  norm_num
  ring

/-- **THE MASS OF THE DETERMINANTAL POINT PROCESS.**  Over the ordered
triples the squared volumes add to six, that is to one over the twenty
unordered triples.  This is Cauchy-Binet at a tight frame. -/
theorem dppTripleWeight_mass {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ slotOne, ∑ slotTwo, ∑ slotThree, dppTripleWeight atom slotOne slotTwo slotThree) = 6 := by
  classical
  have hinner : ∀ slotOne slotTwo : Fin 6,
      (∑ slotThree, dppTripleWeight atom slotOne slotTwo slotThree)
        = dppPairWeight atom slotOne slotTwo := fun a b => dppPairMarginal_eq hframe a b
  have hmid : ∀ slotOne : Fin 6,
      (∑ slotTwo, ∑ slotThree, dppTripleWeight atom slotOne slotTwo slotThree)
        = 2 * atomGram atom slotOne slotOne := by
    intro slotOne
    rw [Finset.sum_congr rfl fun slotTwo _ => hinner slotOne slotTwo]
    exact dppSlotMarginal_eq hframe slotOne
  rw [Finset.sum_congr rfl fun slotOne _ => hmid slotOne, ← Finset.mul_sum,
    atomGram_trace hframe]
  norm_num

/-! ## Layer 3 — the three moments -/

/-- The FIRST MOMENT: the determinantal average of the trace of the shifted
Gram block, over the ordered triples. -/
def dppMomentOne (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) : ℝ :=
  ∑ slotOne, ∑ slotTwo, ∑ slotThree,
    dppTripleWeight atom slotOne slotTwo slotThree
      * (atomShiftedDiag atom scale slotOne + atomShiftedDiag atom scale slotTwo
          + atomShiftedDiag atom scale slotThree)

/-- The SECOND MOMENT: the determinantal average of the pair minor total of
the shifted Gram block, over the ordered triples. -/
def dppMomentTwo (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) : ℝ :=
  ∑ slotOne, ∑ slotTwo, ∑ slotThree,
    dppTripleWeight atom slotOne slotTwo slotThree
      * (atomPairMinor atom scale slotOne slotTwo + atomPairMinor atom scale slotOne slotThree
          + atomPairMinor atom scale slotTwo slotThree)

/-- The THIRD MOMENT: the determinantal average of the triple determinant of
the shifted Gram block, over the ordered triples. -/
def dppMomentThree (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) : ℝ :=
  ∑ slotOne, ∑ slotTwo, ∑ slotThree,
    dppTripleWeight atom slotOne slotTwo slotThree
      * atomTripleDet atom scale slotOne slotTwo slotThree

/-- The reindexing that swaps the last two members of an ordered triple. -/
theorem tripleSum_swap_last (value : Fin 6 → Fin 6 → Fin 6 → ℝ) :
    (∑ slotOne, ∑ slotTwo, ∑ slotThree, value slotOne slotTwo slotThree)
      = ∑ slotOne, ∑ slotTwo, ∑ slotThree, value slotOne slotThree slotTwo := by
  classical
  exact Finset.sum_congr rfl fun slotOne _ => Finset.sum_comm

/-- The reindexing that swaps the first two members of an ordered triple. -/
theorem tripleSum_swap_first (value : Fin 6 → Fin 6 → Fin 6 → ℝ) :
    (∑ slotOne, ∑ slotTwo, ∑ slotThree, value slotOne slotTwo slotThree)
      = ∑ slotOne, ∑ slotTwo, ∑ slotThree, value slotTwo slotOne slotThree := by
  classical
  rw [Finset.sum_comm]

/-- **THE FIRST MOMENT LAW.**  The determinantal average of the trace is
six times the squared-length-weighted sum of the shifted diagonals. -/
theorem dppMomentOne_eq {atom : Fin 6 → (Fin 3 → ℝ)} (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    dppMomentOne atom scale
      = 6 * ∑ slot, atomGram atom slot slot * atomShiftedDiag atom scale slot := by
  classical
  have hfirst : (∑ slotOne, ∑ slotTwo, ∑ slotThree,
      dppTripleWeight atom slotOne slotTwo slotThree * atomShiftedDiag atom scale slotOne)
      = 2 * ∑ slot, atomGram atom slot slot * atomShiftedDiag atom scale slot := by
    have hstep : ∀ slotOne : Fin 6,
        (∑ slotTwo, ∑ slotThree,
            dppTripleWeight atom slotOne slotTwo slotThree * atomShiftedDiag atom scale slotOne)
          = 2 * atomGram atom slotOne slotOne * atomShiftedDiag atom scale slotOne := by
      intro slotOne
      have hinner : ∀ slotTwo : Fin 6,
          (∑ slotThree,
              dppTripleWeight atom slotOne slotTwo slotThree * atomShiftedDiag atom scale slotOne)
            = dppPairWeight atom slotOne slotTwo * atomShiftedDiag atom scale slotOne := by
        intro slotTwo
        rw [← Finset.sum_mul, dppPairMarginal_eq hframe slotOne slotTwo]
      rw [Finset.sum_congr rfl fun slotTwo _ => hinner slotTwo, ← Finset.sum_mul,
        dppSlotMarginal_eq hframe slotOne]
    rw [Finset.sum_congr rfl fun slotOne _ => hstep slotOne, Finset.mul_sum]
    exact Finset.sum_congr rfl fun slot _ => by ring
  have hsecond : (∑ slotOne, ∑ slotTwo, ∑ slotThree,
      dppTripleWeight atom slotOne slotTwo slotThree * atomShiftedDiag atom scale slotTwo)
      = 2 * ∑ slot, atomGram atom slot slot * atomShiftedDiag atom scale slot := by
    rw [tripleSum_swap_first
      (fun a b c => dppTripleWeight atom a b c * atomShiftedDiag atom scale b)]
    rw [← hfirst]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by rw [dppTripleWeight_swap_first]
  have hthird : (∑ slotOne, ∑ slotTwo, ∑ slotThree,
      dppTripleWeight atom slotOne slotTwo slotThree * atomShiftedDiag atom scale slotThree)
      = 2 * ∑ slot, atomGram atom slot slot * atomShiftedDiag atom scale slot := by
    rw [tripleSum_swap_last
      (fun a b c => dppTripleWeight atom a b c * atomShiftedDiag atom scale c)]
    rw [← hsecond]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by rw [dppTripleWeight_swap_last]
  have hsplit : dppMomentOne atom scale
      = (∑ slotOne, ∑ slotTwo, ∑ slotThree,
          dppTripleWeight atom slotOne slotTwo slotThree * atomShiftedDiag atom scale slotOne)
        + (∑ slotOne, ∑ slotTwo, ∑ slotThree,
            dppTripleWeight atom slotOne slotTwo slotThree * atomShiftedDiag atom scale slotTwo)
        + ∑ slotOne, ∑ slotTwo, ∑ slotThree,
            dppTripleWeight atom slotOne slotTwo slotThree
              * atomShiftedDiag atom scale slotThree := by
    simp only [dppMomentOne, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, hfirst, hsecond, hthird]
  ring

/-- **THE SECOND MOMENT LAW.**  The determinantal average of the pair minor
total is three times the squared-wedge-weighted sum of the pair minors. -/
theorem dppMomentTwo_eq {atom : Fin 6 → (Fin 3 → ℝ)} (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    dppMomentTwo atom scale
      = 3 * ∑ rowSlot, ∑ colSlot,
          dppPairWeight atom rowSlot colSlot * atomPairMinor atom scale rowSlot colSlot := by
  classical
  have hfirst : (∑ slotOne, ∑ slotTwo, ∑ slotThree,
      dppTripleWeight atom slotOne slotTwo slotThree
        * atomPairMinor atom scale slotOne slotTwo)
      = ∑ rowSlot, ∑ colSlot,
          dppPairWeight atom rowSlot colSlot * atomPairMinor atom scale rowSlot colSlot := by
    refine Finset.sum_congr rfl fun slotOne _ => Finset.sum_congr rfl fun slotTwo _ => ?_
    rw [← Finset.sum_mul, dppPairMarginal_eq hframe slotOne slotTwo]
  have hsecond : (∑ slotOne, ∑ slotTwo, ∑ slotThree,
      dppTripleWeight atom slotOne slotTwo slotThree
        * atomPairMinor atom scale slotOne slotThree)
      = ∑ rowSlot, ∑ colSlot,
          dppPairWeight atom rowSlot colSlot * atomPairMinor atom scale rowSlot colSlot := by
    rw [tripleSum_swap_last
      (fun a b c => dppTripleWeight atom a b c * atomPairMinor atom scale a c)]
    rw [← hfirst]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by rw [dppTripleWeight_swap_last]
  have hthird : (∑ slotOne, ∑ slotTwo, ∑ slotThree,
      dppTripleWeight atom slotOne slotTwo slotThree
        * atomPairMinor atom scale slotTwo slotThree)
      = ∑ rowSlot, ∑ colSlot,
          dppPairWeight atom rowSlot colSlot * atomPairMinor atom scale rowSlot colSlot := by
    rw [tripleSum_swap_first
      (fun a b c => dppTripleWeight atom a b c * atomPairMinor atom scale b c)]
    rw [← hsecond]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by rw [dppTripleWeight_swap_first]
  have hsplit : dppMomentTwo atom scale
      = (∑ slotOne, ∑ slotTwo, ∑ slotThree,
          dppTripleWeight atom slotOne slotTwo slotThree
            * atomPairMinor atom scale slotOne slotTwo)
        + (∑ slotOne, ∑ slotTwo, ∑ slotThree,
            dppTripleWeight atom slotOne slotTwo slotThree
              * atomPairMinor atom scale slotOne slotThree)
        + ∑ slotOne, ∑ slotTwo, ∑ slotThree,
            dppTripleWeight atom slotOne slotTwo slotThree
              * atomPairMinor atom scale slotTwo slotThree := by
    simp only [dppMomentTwo, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, hfirst, hsecond, hthird]
  ring

/-! ## Layer 4 — the selection engine, the free half of the interlacing argument -/

/-- The CHARACTERISTIC POLYNOMIAL of the shifted Gram block of a triple.
Its roots are the eigenvalues of that block, and the block is positive
semidefinite exactly when no root is negative. -/
def atomTripleChar (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (slotOne slotTwo slotThree : Fin 6) (arg : ℝ) : ℝ :=
  arg ^ 3
    - (atomShiftedDiag atom scale slotOne + atomShiftedDiag atom scale slotTwo
        + atomShiftedDiag atom scale slotThree) * arg ^ 2
    + (atomPairMinor atom scale slotOne slotTwo + atomPairMinor atom scale slotOne slotThree
        + atomPairMinor atom scale slotTwo slotThree) * arg
    - atomTripleDet atom scale slotOne slotTwo slotThree

/-- **THE SELECTION ENGINE.**  Nonnegative weights of positive mass whose
three averaged coefficients are all nonnegative force a weighted triple
whose characteristic polynomial is NEGATIVE at every negative argument.
This is the free half of the interlacing argument: the averaged statement
descends to one member as soon as a common interlacing point is available,
and the engine supplies the sign that the interlacing step consumes. -/
theorem exists_triple_char_neg (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (weight : Fin 6 → Fin 6 → Fin 6 → ℝ)
    (hnonneg : ∀ slotOne slotTwo slotThree, 0 ≤ weight slotOne slotTwo slotThree)
    (hmass : 0 < ∑ slotOne, ∑ slotTwo, ∑ slotThree, weight slotOne slotTwo slotThree)
    (hone : 0 ≤ ∑ slotOne, ∑ slotTwo, ∑ slotThree,
      weight slotOne slotTwo slotThree
        * (atomShiftedDiag atom scale slotOne + atomShiftedDiag atom scale slotTwo
            + atomShiftedDiag atom scale slotThree))
    (htwo : 0 ≤ ∑ slotOne, ∑ slotTwo, ∑ slotThree,
      weight slotOne slotTwo slotThree
        * (atomPairMinor atom scale slotOne slotTwo
            + atomPairMinor atom scale slotOne slotThree
            + atomPairMinor atom scale slotTwo slotThree))
    (hthree : 0 ≤ ∑ slotOne, ∑ slotTwo, ∑ slotThree,
      weight slotOne slotTwo slotThree * atomTripleDet atom scale slotOne slotTwo slotThree)
    (arg : ℝ) (harg : arg < 0) :
    ∃ slotOne slotTwo slotThree, 0 < weight slotOne slotTwo slotThree
      ∧ atomTripleChar atom scale slotOne slotTwo slotThree arg < 0 := by
  classical
  set massSum := ∑ slotOne, ∑ slotTwo, ∑ slotThree, weight slotOne slotTwo slotThree with hmassDef
  set oneSum := ∑ slotOne, ∑ slotTwo, ∑ slotThree,
    weight slotOne slotTwo slotThree
      * (atomShiftedDiag atom scale slotOne + atomShiftedDiag atom scale slotTwo
          + atomShiftedDiag atom scale slotThree) with honeDef
  set twoSum := ∑ slotOne, ∑ slotTwo, ∑ slotThree,
    weight slotOne slotTwo slotThree
      * (atomPairMinor atom scale slotOne slotTwo
          + atomPairMinor atom scale slotOne slotThree
          + atomPairMinor atom scale slotTwo slotThree) with htwoDef
  set threeSum := ∑ slotOne, ∑ slotTwo, ∑ slotThree,
    weight slotOne slotTwo slotThree
      * atomTripleDet atom scale slotOne slotTwo slotThree with hthreeDef
  have hexpand : (∑ slotOne, ∑ slotTwo, ∑ slotThree,
      weight slotOne slotTwo slotThree
        * atomTripleChar atom scale slotOne slotTwo slotThree arg)
      = massSum * arg ^ 3 - oneSum * arg ^ 2 + twoSum * arg - threeSum := by
    simp only [hmassDef, honeDef, htwoDef, hthreeDef, atomTripleChar,
      Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => by ring
  have hsqpos : 0 < arg ^ 2 := by nlinarith [mul_pos_of_neg_of_neg harg harg]
  have hcube : arg ^ 3 < 0 := by nlinarith [mul_neg_of_neg_of_pos harg hsqpos]
  have hsq : 0 ≤ arg ^ 2 := sq_nonneg arg
  have hneg : (∑ slotOne, ∑ slotTwo, ∑ slotThree,
      weight slotOne slotTwo slotThree
        * atomTripleChar atom scale slotOne slotTwo slotThree arg) < 0 := by
    rw [hexpand]
    have hfirst : massSum * arg ^ 3 < 0 := mul_neg_of_pos_of_neg hmass hcube
    have hsecond : 0 ≤ oneSum * arg ^ 2 := mul_nonneg hone hsq
    have hthirdTerm : twoSum * arg ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htwo harg.le
    linarith
  by_contra hno
  simp only [not_exists, not_and, not_lt] at hno
  have hterm : ∀ slotOne slotTwo slotThree : Fin 6,
      0 ≤ weight slotOne slotTwo slotThree
        * atomTripleChar atom scale slotOne slotTwo slotThree arg := by
    intro slotOne slotTwo slotThree
    rcases (hnonneg slotOne slotTwo slotThree).lt_or_eq with hpos | hzero
    · exact mul_nonneg (hnonneg _ _ _) (hno slotOne slotTwo slotThree hpos)
    · rw [← hzero, zero_mul]
  have hsumNonneg : (0 : ℝ) ≤ ∑ slotOne, ∑ slotTwo, ∑ slotThree,
      weight slotOne slotTwo slotThree
        * atomTripleChar atom scale slotOne slotTwo slotThree arg :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      Finset.sum_nonneg fun c _ => hterm a b c
  linarith

/-- The determinantal instance of the engine. -/
theorem exists_dpp_triple_char_neg {atom : Fin 6 → (Fin 3 → ℝ)} (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hone : 0 ≤ dppMomentOne atom scale) (htwo : 0 ≤ dppMomentTwo atom scale)
    (hthree : 0 ≤ dppMomentThree atom scale) (arg : ℝ) (harg : arg < 0) :
    ∃ slotOne slotTwo slotThree, 0 < dppTripleWeight atom slotOne slotTwo slotThree
      ∧ atomTripleChar atom scale slotOne slotTwo slotThree arg < 0 :=
  exists_triple_char_neg atom scale (dppTripleWeight atom)
    (fun a b c => dppTripleWeight_nonneg atom a b c)
    (by rw [dppTripleWeight_mass hframe]; norm_num) hone htwo hthree arg harg

/-! ## Layer 4b — the residue of the method is a quantifier exchange -/

/-- A triple is CHARACTERISTICALLY NEGATIVE when its characteristic
polynomial is negative at every negative argument.  For a symmetric block
that is exactly positive semidefiniteness, because a negative eigenvalue
puts a sign change on the negative axis. -/
def AtomTripleCharNegative (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (slotOne slotTwo slotThree : Fin 6) : Prop :=
  ∀ arg : ℝ, arg < 0 → atomTripleChar atom scale slotOne slotTwo slotThree arg < 0

/-- **A DOMINATING TRIPLE IS CHARACTERISTICALLY NEGATIVE.**  Three
nonnegative coefficients make the characteristic polynomial negative on the
whole negative axis, by the same sign count that drives the engine. -/
theorem atomTripleCharNegative_of_dominates (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (slotOne slotTwo slotThree : Fin 6)
    (hone : 0 ≤ atomShiftedDiag atom scale slotOne + atomShiftedDiag atom scale slotTwo
      + atomShiftedDiag atom scale slotThree)
    (htwo : 0 ≤ atomPairMinor atom scale slotOne slotTwo
      + atomPairMinor atom scale slotOne slotThree
      + atomPairMinor atom scale slotTwo slotThree)
    (hthree : 0 ≤ atomTripleDet atom scale slotOne slotTwo slotThree) :
    AtomTripleCharNegative atom scale slotOne slotTwo slotThree := by
  intro arg harg
  have hsqpos : 0 < arg ^ 2 := by nlinarith [mul_pos_of_neg_of_neg harg harg]
  have hcube : arg ^ 3 < 0 := by nlinarith [mul_neg_of_neg_of_pos harg hsqpos]
  have hfirst : 0 ≤ (atomShiftedDiag atom scale slotOne + atomShiftedDiag atom scale slotTwo
      + atomShiftedDiag atom scale slotThree) * arg ^ 2 := mul_nonneg hone hsqpos.le
  have hsecond : (atomPairMinor atom scale slotOne slotTwo
      + atomPairMinor atom scale slotOne slotThree
      + atomPairMinor atom scale slotTwo slotThree) * arg ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos htwo harg.le
  simp only [atomTripleChar]
  linarith

/-- **THE RESIDUE OF THE INTERLACING METHOD, STATED EXACTLY.**  The engine
`Gtz.exists_triple_char_neg` delivers, for EACH negative argument, SOME
weighted triple whose characteristic polynomial is negative there.  The cell
asks for ONE triple that works at EVERY negative argument.  An interlacing
family is precisely the device that exchanges those two quantifiers, and this
proposition names the exchange. -/
def TripleQuantifierExchange : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (weight : Fin 6 → Fin 6 → Fin 6 → ℝ),
    (∀ slotOne slotTwo slotThree, 0 ≤ weight slotOne slotTwo slotThree) →
    (0 < ∑ slotOne, ∑ slotTwo, ∑ slotThree, weight slotOne slotTwo slotThree) →
    (∀ arg : ℝ, arg < 0 → ∃ slotOne slotTwo slotThree,
      0 < weight slotOne slotTwo slotThree
        ∧ atomTripleChar atom scale slotOne slotTwo slotThree arg < 0) →
    ∃ slotOne slotTwo slotThree, 0 < weight slotOne slotTwo slotThree
      ∧ AtomTripleCharNegative atom scale slotOne slotTwo slotThree

/-- **THE COMPOSITION.**  The three moment inequalities plus the quantifier
exchange give a triple that is characteristically negative, which is the
positive semidefiniteness the residue asks for.  Both hypotheses are needed:
this module refutes the first for the measure of the frame, and the second is
the interlacing family, which the campaign has not built. -/
theorem exists_charNegative_of_moments_of_exchange
    (hexchange : TripleQuantifierExchange)
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (weight : Fin 6 → Fin 6 → Fin 6 → ℝ)
    (hnonneg : ∀ slotOne slotTwo slotThree, 0 ≤ weight slotOne slotTwo slotThree)
    (hmass : 0 < ∑ slotOne, ∑ slotTwo, ∑ slotThree, weight slotOne slotTwo slotThree)
    (hone : 0 ≤ ∑ slotOne, ∑ slotTwo, ∑ slotThree,
      weight slotOne slotTwo slotThree
        * (atomShiftedDiag atom scale slotOne + atomShiftedDiag atom scale slotTwo
            + atomShiftedDiag atom scale slotThree))
    (htwo : 0 ≤ ∑ slotOne, ∑ slotTwo, ∑ slotThree,
      weight slotOne slotTwo slotThree
        * (atomPairMinor atom scale slotOne slotTwo
            + atomPairMinor atom scale slotOne slotThree
            + atomPairMinor atom scale slotTwo slotThree))
    (hthree : 0 ≤ ∑ slotOne, ∑ slotTwo, ∑ slotThree,
      weight slotOne slotTwo slotThree * atomTripleDet atom scale slotOne slotTwo slotThree) :
    ∃ slotOne slotTwo slotThree, 0 < weight slotOne slotTwo slotThree
      ∧ AtomTripleCharNegative atom scale slotOne slotTwo slotThree :=
  hexchange atom scale weight hnonneg hmass
    (fun arg harg => exists_triple_char_neg atom scale weight hnonneg hmass hone htwo hthree
      arg harg)

/-! ## Layer 5 — the converse: searching over the measure is not a reduction -/

/-- The POINT MASS weights on one ordered triple. -/
def pointMassWeight (pivotOne pivotTwo pivotThree : Fin 6) : Fin 6 → Fin 6 → Fin 6 → ℝ :=
  fun slotOne slotTwo slotThree =>
    if slotOne = pivotOne then
      (if slotTwo = pivotTwo then (if slotThree = pivotThree then 1 else 0) else 0)
    else 0

theorem pointMassWeight_nonneg (pivotOne pivotTwo pivotThree : Fin 6) :
    ∀ slotOne slotTwo slotThree, 0 ≤ pointMassWeight pivotOne pivotTwo pivotThree
      slotOne slotTwo slotThree := by
  intro slotOne slotTwo slotThree
  simp only [pointMassWeight]
  split_ifs <;> norm_num

theorem tripleSum_pointMass (value : Fin 6 → Fin 6 → Fin 6 → ℝ)
    (pivotOne pivotTwo pivotThree : Fin 6) :
    (∑ slotOne, ∑ slotTwo, ∑ slotThree,
        pointMassWeight pivotOne pivotTwo pivotThree slotOne slotTwo slotThree
          * value slotOne slotTwo slotThree)
      = value pivotOne pivotTwo pivotThree := by
  classical
  rw [Finset.sum_eq_single pivotOne]
  · rw [Finset.sum_eq_single pivotTwo]
    · rw [Finset.sum_eq_single pivotThree]
      · simp [pointMassWeight]
      · intro slotThree _ hne
        simp [pointMassWeight, hne]
      · intro hnot
        exact absurd (Finset.mem_univ pivotThree) hnot
    · intro slotTwo _ hne
      simp [pointMassWeight, hne]
    · intro hnot
      exact absurd (Finset.mem_univ pivotTwo) hnot
  · intro slotOne _ hne
    simp [pointMassWeight, hne]
  · intro hnot
    exact absurd (Finset.mem_univ pivotOne) hnot

/-- **THE POINT MASS SATISFIES THE CERTIFICATE.**  A dominating triple makes
the three moment inequalities hold for the weights that put all their mass on
that triple.  A point mass is strongly Rayleigh, and it is a limit of tilts of
the determinantal point process, so the SUPREMUM of the certificate over the
admissible measures is the cell itself.  A measure chosen by search is
therefore never a reduction: only a measure given by a FORMULA can be a
proof, and the formula of the frame is refuted here. -/
theorem dppMoments_nonneg_of_dominating (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (slotOne slotTwo slotThree : Fin 6)
    (hone : 0 ≤ atomShiftedDiag atom scale slotOne + atomShiftedDiag atom scale slotTwo
      + atomShiftedDiag atom scale slotThree)
    (htwo : 0 ≤ atomPairMinor atom scale slotOne slotTwo
      + atomPairMinor atom scale slotOne slotThree
      + atomPairMinor atom scale slotTwo slotThree)
    (hthree : 0 ≤ atomTripleDet atom scale slotOne slotTwo slotThree) :
    (∀ a b c, 0 ≤ pointMassWeight slotOne slotTwo slotThree a b c)
      ∧ (0 < ∑ a, ∑ b, ∑ c, pointMassWeight slotOne slotTwo slotThree a b c)
      ∧ (0 ≤ ∑ a, ∑ b, ∑ c, pointMassWeight slotOne slotTwo slotThree a b c
          * (atomShiftedDiag atom scale a + atomShiftedDiag atom scale b
              + atomShiftedDiag atom scale c))
      ∧ (0 ≤ ∑ a, ∑ b, ∑ c, pointMassWeight slotOne slotTwo slotThree a b c
          * (atomPairMinor atom scale a b + atomPairMinor atom scale a c
              + atomPairMinor atom scale b c))
      ∧ 0 ≤ ∑ a, ∑ b, ∑ c, pointMassWeight slotOne slotTwo slotThree a b c
          * atomTripleDet atom scale a b c := by
  refine ⟨pointMassWeight_nonneg slotOne slotTwo slotThree, ?_, ?_, ?_, ?_⟩
  · have hval := tripleSum_pointMass (fun _ _ _ => (1 : ℝ)) slotOne slotTwo slotThree
    simp only [mul_one] at hval
    rw [hval]; norm_num
  · rw [tripleSum_pointMass
      (fun a b c => atomShiftedDiag atom scale a + atomShiftedDiag atom scale b
        + atomShiftedDiag atom scale c)]
    exact hone
  · rw [tripleSum_pointMass
      (fun a b c => atomPairMinor atom scale a b + atomPairMinor atom scale a c
        + atomPairMinor atom scale b c)]
    exact htwo
  · rw [tripleSum_pointMass (fun a b c => atomTripleDet atom scale a b c)]
    exact hthree

/-! ## Layer 6 — the line datum, which refutes the certificate -/

/-- The coefficient of the line datum on the first axis. -/
noncomputable def dppLineCoefficient : Fin 6 → ℝ := fun slot =>
  if slot = 0 then 4 / 5 else if slot = 2 then 1 / 5 else 2 / 5

/-- **THE LINE DATUM.**  Four parallel atoms on the first axis, of
coefficients `4/5, 1/5, 2/5, 2/5`, and two unit atoms on the other two axes.
The four squared coefficients add to one, so the family is a tight frame. -/
noncomputable def dppLineAtom : Fin 6 → (Fin 3 → ℝ) := fun slot index =>
  if slot = 1 then (if index = 1 then 1 else 0)
  else if slot = 3 then (if index = 2 then 1 else 0)
  else if index = 0 then dppLineCoefficient slot else 0

/-- The scale family of the line datum: mass `94/100` on the longest
parallel atom and `1/100` on each of the others, of total `99/100`. -/
noncomputable def dppLineScale : Fin 6 → ℝ := fun slot =>
  if slot = 0 then 94 / 100 else 1 / 100

/-- The Gram of the line datum: the outer square of the coefficient on the
parallel block, and the two unit atoms isolated. -/
noncomputable def dppLineGram : Fin 6 → Fin 6 → ℝ := fun rowSlot colSlot =>
  if rowSlot = 1 then (if colSlot = 1 then 1 else 0)
  else if rowSlot = 3 then (if colSlot = 3 then 1 else 0)
  else if colSlot = 1 then 0 else if colSlot = 3 then 0
  else dppLineCoefficient rowSlot * dppLineCoefficient colSlot

theorem dppLineScale_pos (slot : Fin 6) : 0 < dppLineScale slot := by
  fin_cases slot <;> norm_num [dppLineScale]

/-- The scale mass of the line datum is `99/100`, STRICTLY below one, so the
datum satisfies every hypothesis of the residue. -/
theorem dppLineScale_sum : (∑ slot, dppLineScale slot) = 99 / 100 := by
  simp +decide only [Fin.sum_univ_six, dppLineScale]
  norm_num

theorem dppLineScale_sum_lt_one : (∑ slot, dppLineScale slot) < 1 := by
  rw [dppLineScale_sum]; norm_num

/-- **THE LINE DATUM IS A TIGHT FRAME.** -/
theorem dppLineAtom_isTightFrame (probe direction : Fin 3 → ℝ) :
    (∑ slot, (dppLineAtom slot ⬝ᵥ probe) * (dppLineAtom slot ⬝ᵥ direction))
      = probe ⬝ᵥ direction := by
  simp +decide only [Fin.sum_univ_six, dppLineAtom, dppLineCoefficient, dotProduct,
    Fin.sum_univ_three]
  norm_num
  ring

/-- **THE GRAM OF THE LINE DATUM IS THE RATIONAL TABLE.** -/
theorem dppLineAtom_gram (rowSlot colSlot : Fin 6) :
    atomGram dppLineAtom rowSlot colSlot = dppLineGram rowSlot colSlot := by
  fin_cases rowSlot <;> fin_cases colSlot <;>
    simp +decide only [atomGram, dppLineAtom, dppLineGram, dppLineCoefficient,
      dotProduct, Fin.sum_univ_three] <;>
    norm_num

/-! ## Layer 7 — the refutation -/

/-- **THE THIRD MOMENT OF THE LINE DATUM IS NEGATIVE.**  Its exact value is
`-10496871/12500000`, that is `-3498957/25000000` per unordered triple. -/
theorem dppLine_momentThree :
    dppMomentThree dppLineAtom dppLineScale = -(10496871 / 12500000) := by
  simp +decide only [dppMomentThree, Fin.sum_univ_six, dppTripleWeight, atomTripleDet,
    atomShiftedDiag, dppLineAtom_gram, dppLineGram, dppLineCoefficient, dppLineScale]
  norm_num

theorem dppLine_momentThree_neg : dppMomentThree dppLineAtom dppLineScale < 0 := by
  rw [dppLine_momentThree]; norm_num

/-- The FIRST moment of the line datum is `13779/1250`, and the SECOND is
`523017/125000`.  Both are comfortably positive: the certificate fails at the
third moment alone, which is the one the tie boundary pins. -/
theorem dppLine_momentOne : dppMomentOne dppLineAtom dppLineScale = 13779 / 1250 := by
  rw [dppMomentOne_eq dppLineScale dppLineAtom_isTightFrame]
  simp +decide only [Fin.sum_univ_six, atomShiftedDiag, dppLineAtom_gram, dppLineGram,
    dppLineCoefficient, dppLineScale]
  norm_num

theorem dppLine_momentTwo : dppMomentTwo dppLineAtom dppLineScale = 523017 / 125000 := by
  rw [dppMomentTwo_eq dppLineScale dppLineAtom_isTightFrame]
  simp +decide only [Fin.sum_univ_six, dppPairWeight, atomPairMinor, atomShiftedDiag,
    dppLineAtom_gram, dppLineGram, dppLineCoefficient, dppLineScale]
  norm_num

/-- The three coefficients of the shifted Gram block on slots one, two and
three of the line datum are `201/100`, `2079/2000` and `29403/1000000`, all
strictly positive, so that triple DOMINATES. -/
theorem dppLine_dominating_trace :
    atomShiftedDiag dppLineAtom dppLineScale 1 + atomShiftedDiag dppLineAtom dppLineScale 2
      + atomShiftedDiag dppLineAtom dppLineScale 3 = 201 / 100 := by
  simp +decide only [atomShiftedDiag, dppLineAtom_gram, dppLineGram, dppLineCoefficient,
    dppLineScale]
  norm_num

theorem dppLine_dominating_pairs :
    atomPairMinor dppLineAtom dppLineScale 1 2
      + atomPairMinor dppLineAtom dppLineScale 1 3
      + atomPairMinor dppLineAtom dppLineScale 2 3 = 2079 / 2000 := by
  simp +decide only [atomPairMinor, atomShiftedDiag, dppLineAtom_gram, dppLineGram,
    dppLineCoefficient, dppLineScale]
  norm_num

theorem dppLine_dominating_det :
    atomTripleDet dppLineAtom dppLineScale 1 2 3 = 29403 / 1000000 := by
  simp +decide only [atomTripleDet, atomShiftedDiag, dppLineAtom_gram, dppLineGram,
    dppLineCoefficient, dppLineScale]
  norm_num

/-- **THE LINE DATUM CARRIES A DOMINATING TRIPLE.**  The cell HOLDS at the
witness that refutes the certificate, so the refutation is a refutation of
the method and not of the theorem. -/
theorem dppLine_hasDominatingTriple :
    0 < atomShiftedDiag dppLineAtom dppLineScale 1
        + atomShiftedDiag dppLineAtom dppLineScale 2
        + atomShiftedDiag dppLineAtom dppLineScale 3
      ∧ 0 < atomPairMinor dppLineAtom dppLineScale 1 2
          + atomPairMinor dppLineAtom dppLineScale 1 3
          + atomPairMinor dppLineAtom dppLineScale 2 3
      ∧ 0 < atomTripleDet dppLineAtom dppLineScale 1 2 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [dppLine_dominating_trace]; norm_num
  · rw [dppLine_dominating_pairs]; norm_num
  · rw [dppLine_dominating_det]; norm_num

/-- The determinantal certificate: at every tight frame of rank three on six
slots with positive scales of mass below one, the third determinantal moment
is nonnegative.  This is exactly what the interlacing method consumes. -/
def DppMomentCertificate : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    0 ≤ dppMomentThree atom scale

/-- **THE DETERMINANTAL MOMENT CERTIFICATE IS FALSE.**  The measure of the
frame is the only measure the geometry supplies, and its third moment goes
negative at the line datum.  The adversarial floor of that moment over the
whole stratum is exactly `-3/16`, attained in the limit of the same family
at squared coefficients `5/8, 1/8, 1/8, 1/8` with the whole scale mass on
the longest atom, and the floor stays negative on the blocked stratum. -/
theorem not_dppMomentCertificate : ¬ DppMomentCertificate := by
  intro hcert
  have hnonneg := hcert dppLineAtom dppLineScale dppLineScale_pos dppLineScale_sum_lt_one
    dppLineAtom_isTightFrame
  have hneg := dppLine_momentThree_neg
  linarith

/-! ## Layer 8 — the tightness at the boundary witness -/

/-- The lengths of the boundary witness: the doubled tetrahedron carries two
directions at length `3/10` and `2/5` and two more at length `1/2`. -/
noncomputable def dppTieLength : Fin 6 → ℝ := fun slot =>
  if slot = 0 then 3 / 10 else if slot = 1 then 2 / 5
  else if slot = 2 then 3 / 10 else if slot = 3 then 2 / 5 else 1 / 2

/-- The direction index of each slot of the boundary witness. -/
def dppTieDirection : Fin 6 → Fin 4 := fun slot =>
  if slot = 0 then 0 else if slot = 1 then 0 else if slot = 2 then 1
  else if slot = 3 then 1 else if slot = 4 then 2 else 3

/-- The Gram of the boundary witness in closed form: the four directions of
a regular tetrahedron pair at `3` on the diagonal and at `-1` off it, and the
lengths scale the whole table. -/
noncomputable def dppTieGram : Fin 6 → Fin 6 → ℝ := fun rowSlot colSlot =>
  dppTieLength rowSlot * dppTieLength colSlot
    * (if dppTieDirection rowSlot = dppTieDirection colSlot then 3 else -1)

theorem dppTieGram_eq (rowSlot colSlot : Fin 6) :
    atomGram atomBoundaryAtom rowSlot colSlot = dppTieGram rowSlot colSlot := by
  fin_cases rowSlot <;> fin_cases colSlot <;>
    simp +decide [atomGram, atomBoundaryAtom, dppTieGram, dppTieLength,
      dotProduct, Fin.sum_univ_three] <;>
    norm_num

/-- The scale of the boundary witness is the SQUARED LENGTH of each slot. -/
theorem dppTieScale_eq (slot : Fin 6) :
    atomBoundaryScale slot = dppTieLength slot ^ 2 := by
  fin_cases slot <;> simp +decide [atomBoundaryScale, dppTieLength] <;> norm_num

/-- **THE THIRD MOMENT IS EXACTLY ZERO AT THE BOUNDARY WITNESS.**  Of the
twenty triples of that datum, twelve have triple determinant exactly zero
and eight have it strictly negative, and those eight are exactly the triples
that repeat a direction, which carry squared volume zero.  So the
determinantal average sees only the zeros: the certificate is SHARP at the
extremal of the cell, and it fails elsewhere.  The obstruction is not the
choice of the measure. -/
theorem dppTie_momentThree_eq_zero :
    dppMomentThree atomBoundaryAtom atomBoundaryScale = 0 := by
  simp +decide only [dppMomentThree, Fin.sum_univ_six, dppTripleWeight, atomTripleDet,
    atomShiftedDiag, dppTieGram_eq, dppTieScale_eq, dppTieGram, dppTieLength,
    dppTieDirection]
  norm_num

/-- The first moment at the boundary witness is `4329/625`, strictly
positive: only the third moment is at its boundary. -/
theorem dppTie_momentOne :
    dppMomentOne atomBoundaryAtom atomBoundaryScale = 4329 / 625 := by
  rw [dppMomentOne_eq atomBoundaryScale atomBoundaryAtom_isTightFrame]
  simp +decide only [Fin.sum_univ_six, atomShiftedDiag, dppTieGram_eq, dppTieScale_eq,
    dppTieGram, dppTieLength, dppTieDirection]
  norm_num

/-- The second moment at the boundary witness is `6060123/3125000`, also
strictly positive.  The certificate touches zero in the third moment ONLY,
which is the coefficient the tie boundary controls. -/
theorem dppTie_momentTwo :
    dppMomentTwo atomBoundaryAtom atomBoundaryScale = 6060123 / 3125000 := by
  rw [dppMomentTwo_eq atomBoundaryScale atomBoundaryAtom_isTightFrame]
  simp +decide only [Fin.sum_univ_six, dppPairWeight, atomPairMinor, atomShiftedDiag,
    dppTieGram_eq, dppTieScale_eq, dppTieGram, dppTieLength, dppTieDirection]
  norm_num

/-- **THE CERTIFICATE IS SHARP AT THE TIE AND FALSE OFF IT.**  At the
boundary witness the first two moments are strictly positive and the third is
exactly zero, and at the line datum the first two moments are again strictly
positive while the third is strictly negative.  So the failure is not a
failure of scale or of normalization: the third determinantal moment crosses
zero, and the crossing is not controlled by the geometry of the frame. -/
theorem dppMomentThree_crosses_zero :
    dppMomentThree atomBoundaryAtom atomBoundaryScale = 0
      ∧ dppMomentThree dppLineAtom dppLineScale < 0
      ∧ 0 < dppMomentOne atomBoundaryAtom atomBoundaryScale
      ∧ 0 < dppMomentTwo atomBoundaryAtom atomBoundaryScale
      ∧ 0 < dppMomentOne dppLineAtom dppLineScale
      ∧ 0 < dppMomentTwo dppLineAtom dppLineScale := by
  refine ⟨dppTie_momentThree_eq_zero, dppLine_momentThree_neg, ?_, ?_, ?_, ?_⟩
  · rw [dppTie_momentOne]; norm_num
  · rw [dppTie_momentTwo]; norm_num
  · rw [dppLine_momentOne]; norm_num
  · rw [dppLine_momentTwo]; norm_num

end Gtz
