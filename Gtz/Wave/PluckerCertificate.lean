import Gtz.Wave.InterlacingSelection
import Gtz.Wave.AtomVertexSelection
import Gtz.Wave.SignatureSelection
import Gtz.Uniform.SpectralWhitening

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6400000

/-!
# The Plücker certificate: the spread law, and the dual face of the residue

Six atoms of rank three that resolve the identity carry twenty determinantal
weights, one for each triple of slots.  The landed interlacing module proves
that the residue reads the datum ONLY through those weights and the scales, and
that the weights of a real family obey the three term Plücker relation exactly,
while the weights of a Hermitian family obey only the three triangle
inequalities.  That single difference is the whole separation of the two fields.

This module builds two things on that difference.

## The spread law, and it is new

`Gtz.dppPlucker_spread`: fix one pivot slot and four other slots.  The six
determinantal weights through that pivot obey

  `2 * (the smallest) ^ 2 <= (the largest) ^ 2`.

The proof is one step of the landed dominance law.  One paired product is at
least the sum of the other two.  Each of the other two is at least the square of
the smallest, and the dominant one is at most the square of the largest.

The law is REAL ONLY, and `Gtz.exists_triangle_without_spread` proves it.  Six
equal positive weights obey all three triangle inequalities, which is everything
the Hermitian field gives, and they break the spread law.  So the spread law is
not a consequence of the field agnostic data.

Two consequences follow at once.

* `Gtz.dppTripleWeight_eq_zero_of_uniform`: if the six weights through a pivot
  and four slots are all EQUAL, they are all ZERO.
* `Gtz.not_uniform_dppTripleWeight`: a real rank three frame of six atoms NEVER
  carries twenty equal determinantal weights.  The determinantal point process
  of a real frame is never the uniform one.  Measured against the icosahedral
  frame, which is the most balanced real frame of this size, the twenty weights
  split ten and ten at the ratio `(3 + sqrt 5) / 2`.

## The dual face of the residue, and it is a new face

The residue asks for a triple whose scaled atoms dominate the identity.  One
symmetric congruence turns that question inside out.  Write `V` for the scaled
second moment of the atoms.  Whiten by the inverse square root of `V` and divide
each atom by the square root of its scale.  The result is again a Parseval
frame, and the residue becomes:

  SOME TRIPLE OF THE NEW FRAME READS AT LEAST AS MUCH ENERGY, IN EVERY
  DIRECTION, AS THE SCALE WEIGHTED TOTAL OF THE WHOLE FRAME.

`Gtz.AtomDualSelectionClosed` states that, and
`Gtz.atomDualSelectionClosed_iff_atomTripleBoundary` proves it EQUIVALENT to the
residue.  `Gtz.gtzWeighted_six_three_of_atomDualSelection` composes it to the
cell.  The congruence engine is `Gtz.whitenedFrame`, and it is reusable at any
family and any positive weights.

The dual face moves ALL the scales to ONE side.  In the residue both sides of
the comparison move with the triple.  In the dual face the left side is a FIXED
quadratic form and only the right side moves.  Three consequences follow with no
minor and no determinant:

* `Gtz.atomDualTriple_of_cap`: a triple whose reading energy reaches the largest
  scale in every direction satisfies the dual comparison.
* `Gtz.atomDualTriple_iff_complement`: the dual comparison is exactly the
  statement that the three slots outside the triple pay less than the shifted
  reading of the three inside it.
* `Gtz.atomDualSelectionClosed_of_uniformCover`: a covering law that returns a
  triple of least reading at least the largest scale gives the whole dual face,
  and the largest scale of a mass one datum is at least one sixth.

## The marginal dictionary

`Gtz.dppTripleMarginal_eq` completes the marginal ladder of the interlacing
module.  The determinantal weights of the ordered triples through one slot add
to twice the squared length of that slot.  With the two landed marginals this
says that every principal minor of order at most three is a marginal of the
twenty weights.  The residue is a statement about a point of the Grassmannian
and the scales, and about nothing else.

## What this module does not claim

The spread law does not decide the residue.  It forbids the uniform weight
profile and it bounds the spread of every six weight family through a pivot.
The dual face is an equivalence and not a narrowing.
`Gtz.atomDualSelectionClosed_iff_atomTripleBoundary` runs in both directions, so
nothing is hidden by it.
-/

namespace Gtz

open Matrix
open GeneralRankReach

/-! ## Layer 1 — the one point marginal of the determinantal weights -/

/-- **THE ONE POINT MARGINAL OF THE TRIPLE WEIGHTS.**  The squared volumes of
the ordered triples through one slot add to twice the squared length of that
slot.  With `Gtz.dppPairMarginal_eq` and `Gtz.dppSlotMarginal_eq` this completes
the marginal ladder: every principal minor of order at most three is a marginal
of the twenty determinantal weights. -/
theorem dppTripleMarginal_eq {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot : Fin 6) :
    (∑ slotTwo, ∑ slotThree, dppTripleWeight atom rowSlot slotTwo slotThree)
      = 2 * atomGram atom rowSlot rowSlot := by
  classical
  have hinner : ∀ slotTwo : Fin 6,
      (∑ slotThree, dppTripleWeight atom rowSlot slotTwo slotThree)
        = dppPairWeight atom rowSlot slotTwo := fun slotTwo =>
    dppPairMarginal_eq hframe rowSlot slotTwo
  rw [Finset.sum_congr rfl fun slotTwo _ => hinner slotTwo]
  exact dppSlotMarginal_eq hframe rowSlot

/-- The determinantal mass through one slot is at most two, because the squared
length of an atom of a tight frame is at most one. -/
theorem dppTripleMarginal_le {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot : Fin 6) :
    (∑ slotTwo, ∑ slotThree, dppTripleWeight atom rowSlot slotTwo slotThree) ≤ 2 := by
  rw [dppTripleMarginal_eq hframe rowSlot]
  have hcap : atomGram atom rowSlot rowSlot ≤ 1 := atomGram_diag_le_one hframe rowSlot
  linarith

/-! ## Layer 2 — the Plücker leg calculus -/

/-- **THE THREE TERM SPLIT OF ABSOLUTE VALUES.**  Three reals in a three term
relation have one absolute value equal to the sum of the other two.  This is the
degenerate triangle of the Plücker law, written without a square root. -/
theorem abs_relation_split {first second third : ℝ}
    (hrel : first - second + third = 0) :
    |second| = |first| + |third| ∨ |first| = |second| + |third|
      ∨ |third| = |first| + |second| := by
  have hsecond : second = first + third := by linarith
  subst hsecond
  rcases le_or_gt 0 first with hfirst | hfirst
  · rcases le_or_gt 0 third with hthird | hthird
    · left
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ first + third), abs_of_nonneg hfirst,
        abs_of_nonneg hthird]
    · rcases le_or_gt 0 (first + third) with hsum | hsum
      · right; left
        rw [abs_of_nonneg hfirst, abs_of_nonneg hsum, abs_of_neg hthird]
        ring
      · right; right
        rw [abs_of_neg hthird, abs_of_nonneg hfirst, abs_of_neg hsum]
        ring
  · rcases le_or_gt 0 third with hthird | hthird
    · rcases le_or_gt 0 (first + third) with hsum | hsum
      · right; right
        rw [abs_of_nonneg hthird, abs_of_neg hfirst, abs_of_nonneg hsum]
        ring
      · right; left
        rw [abs_of_neg hfirst, abs_of_nonneg hthird, abs_of_neg hsum]
        ring
    · left
      rw [abs_of_neg (by linarith : first + third < 0), abs_of_neg hfirst,
        abs_of_neg hthird]
      ring

/-- **THE PLÜCKER LEG.**  The absolute value of one paired product of
determinants through a pivot.  Its square is the paired product of the two
determinantal weights. -/
noncomputable def dppLeg (atom : Fin 6 → (Fin 3 → ℝ))
    (pivot slotOne slotTwo slotThree slotFour : Fin 6) : ℝ :=
  |dppDet3 (atom pivot) (atom slotOne) (atom slotTwo)
    * dppDet3 (atom pivot) (atom slotThree) (atom slotFour)|

theorem dppLeg_nonneg (atom : Fin 6 → (Fin 3 → ℝ))
    (pivot slotOne slotTwo slotThree slotFour : Fin 6) :
    0 ≤ dppLeg atom pivot slotOne slotTwo slotThree slotFour := abs_nonneg _

/-- The square of a leg is the paired product of the two determinantal
weights. -/
theorem dppLeg_sq (atom : Fin 6 → (Fin 3 → ℝ))
    (pivot slotOne slotTwo slotThree slotFour : Fin 6) :
    dppLeg atom pivot slotOne slotTwo slotThree slotFour ^ 2
      = dppTripleWeight atom pivot slotOne slotTwo
        * dppTripleWeight atom pivot slotThree slotFour := by
  rw [dppLeg, sq_abs, dppTripleWeight_eq_det3_sq, dppTripleWeight_eq_det3_sq]
  ring

/-- **THE DEGENERATE TRIANGLE, ON THE LEGS.**  For every pivot and four other
slots ONE of the three legs is the SUM of the other two.  Over the Hermitian
field the three legs obey only the triangle inequalities, and this equality
fails. -/
theorem dppPlucker_legSum (atom : Fin 6 → (Fin 3 → ℝ))
    (pivot slotOne slotTwo slotThree slotFour : Fin 6) :
    dppLeg atom pivot slotOne slotThree slotTwo slotFour
        = dppLeg atom pivot slotOne slotTwo slotThree slotFour
          + dppLeg atom pivot slotOne slotFour slotTwo slotThree
      ∨ dppLeg atom pivot slotOne slotTwo slotThree slotFour
          = dppLeg atom pivot slotOne slotThree slotTwo slotFour
            + dppLeg atom pivot slotOne slotFour slotTwo slotThree
      ∨ dppLeg atom pivot slotOne slotFour slotTwo slotThree
          = dppLeg atom pivot slotOne slotTwo slotThree slotFour
            + dppLeg atom pivot slotOne slotThree slotTwo slotFour := by
  have hrel := dppDet3_plucker (atom pivot) (atom slotOne) (atom slotTwo)
    (atom slotThree) (atom slotFour)
  simpa only [dppLeg] using abs_relation_split hrel

/-- **THE HALF LAW.**  The three legs of a pivot and four slots add to exactly
twice one of them.  A degenerate triangle spends half its perimeter on its
longest side. -/
theorem dppPlucker_half (atom : Fin 6 → (Fin 3 → ℝ))
    (pivot slotOne slotTwo slotThree slotFour : Fin 6) :
    dppLeg atom pivot slotOne slotTwo slotThree slotFour
        + dppLeg atom pivot slotOne slotThree slotTwo slotFour
        + dppLeg atom pivot slotOne slotFour slotTwo slotThree
      = 2 * dppLeg atom pivot slotOne slotThree slotTwo slotFour
    ∨ dppLeg atom pivot slotOne slotTwo slotThree slotFour
        + dppLeg atom pivot slotOne slotThree slotTwo slotFour
        + dppLeg atom pivot slotOne slotFour slotTwo slotThree
      = 2 * dppLeg atom pivot slotOne slotTwo slotThree slotFour
    ∨ dppLeg atom pivot slotOne slotTwo slotThree slotFour
        + dppLeg atom pivot slotOne slotThree slotTwo slotFour
        + dppLeg atom pivot slotOne slotFour slotTwo slotThree
      = 2 * dppLeg atom pivot slotOne slotFour slotTwo slotThree := by
  rcases dppPlucker_legSum atom pivot slotOne slotTwo slotThree slotFour with
    hone | htwo | hthree
  · left; linarith
  · right; left; linarith
  · right; right; linarith

/-! ## Layer 3 — the spread law -/

/-- **THE SPREAD LAW OF THE DETERMINANTAL WEIGHTS, AND IT IS REAL ONLY.**  Fix
one pivot slot and four other slots.  The six determinantal weights through that
pivot obey `2 * (the smallest) ^ 2 <= (the largest) ^ 2`.

The proof is the landed dominance law.  One paired product is at least the sum
of the other two.  Each of the other two is a product of two weights, so it is
at least the square of the smallest.  The dominant one is at most the square of
the largest.

Over the Hermitian field the same six weights obey only the three triangle
inequalities, and six EQUAL weights obey those and break this law
(`Gtz.exists_triangle_without_spread`).  So the spread of the weights is a real
only reading of the datum. -/
theorem dppPlucker_spread (atom : Fin 6 → (Fin 3 → ℝ))
    (pivot slotOne slotTwo slotThree slotFour : Fin 6) (low high : ℝ)
    (hlow : 0 ≤ low)
    (hlowOneTwo : low ≤ dppTripleWeight atom pivot slotOne slotTwo)
    (hlowOneThree : low ≤ dppTripleWeight atom pivot slotOne slotThree)
    (hlowOneFour : low ≤ dppTripleWeight atom pivot slotOne slotFour)
    (hlowTwoThree : low ≤ dppTripleWeight atom pivot slotTwo slotThree)
    (hlowTwoFour : low ≤ dppTripleWeight atom pivot slotTwo slotFour)
    (hlowThreeFour : low ≤ dppTripleWeight atom pivot slotThree slotFour)
    (hhighOneTwo : dppTripleWeight atom pivot slotOne slotTwo ≤ high)
    (hhighOneThree : dppTripleWeight atom pivot slotOne slotThree ≤ high)
    (hhighOneFour : dppTripleWeight atom pivot slotOne slotFour ≤ high)
    (hhighTwoThree : dppTripleWeight atom pivot slotTwo slotThree ≤ high)
    (hhighTwoFour : dppTripleWeight atom pivot slotTwo slotFour ≤ high)
    (hhighThreeFour : dppTripleWeight atom pivot slotThree slotFour ≤ high) :
    2 * low ^ 2 ≤ high ^ 2 := by
  rcases dppPlucker_dominant atom pivot slotOne slotTwo slotThree slotFour with
    ⟨hdom, -⟩ | ⟨hdom, -⟩ | ⟨hdom, -⟩
  · nlinarith [hlowOneThree, hlowTwoFour, hlowOneFour, hlowTwoThree, hhighOneTwo,
      hhighThreeFour, hlow, hdom]
  · nlinarith [hlowOneTwo, hlowThreeFour, hlowOneFour, hlowTwoThree, hhighOneThree,
      hhighTwoFour, hlow, hdom]
  · nlinarith [hlowOneTwo, hlowThreeFour, hlowOneThree, hlowTwoFour, hhighOneFour,
      hhighTwoThree, hlow, hdom]

/-- **THE UNIFORM PROFILE IS THE ZERO PROFILE.**  If the six determinantal
weights through one pivot and four slots are all equal, they are all zero.  A
real family cannot spread its determinantal mass evenly over a pivot star. -/
theorem dppTripleWeight_eq_zero_of_uniform (atom : Fin 6 → (Fin 3 → ℝ))
    (pivot slotOne slotTwo slotThree slotFour : Fin 6) (value : ℝ)
    (hOneTwo : dppTripleWeight atom pivot slotOne slotTwo = value)
    (hOneThree : dppTripleWeight atom pivot slotOne slotThree = value)
    (hOneFour : dppTripleWeight atom pivot slotOne slotFour = value)
    (hTwoThree : dppTripleWeight atom pivot slotTwo slotThree = value)
    (hTwoFour : dppTripleWeight atom pivot slotTwo slotFour = value)
    (hThreeFour : dppTripleWeight atom pivot slotThree slotFour = value) :
    value = 0 := by
  have hnonneg : 0 ≤ value := by
    rw [← hOneTwo]; exact dppTripleWeight_nonneg atom pivot slotOne slotTwo
  have hspread : 2 * value ^ 2 ≤ value ^ 2 :=
    dppPlucker_spread atom pivot slotOne slotTwo slotThree slotFour value value hnonneg
      (le_of_eq hOneTwo.symm) (le_of_eq hOneThree.symm) (le_of_eq hOneFour.symm)
      (le_of_eq hTwoThree.symm) (le_of_eq hTwoFour.symm) (le_of_eq hThreeFour.symm)
      (le_of_eq hOneTwo) (le_of_eq hOneThree) (le_of_eq hOneFour)
      (le_of_eq hTwoThree) (le_of_eq hTwoFour) (le_of_eq hThreeFour)
  nlinarith [hspread, sq_nonneg value]

/-- **NO REAL FRAME CARRIES TWENTY EQUAL WEIGHTS.**  The determinantal point
process of a real rank three frame of six atoms is never the uniform one.  If
every triple of distinct slots carried the same weight, the spread law would
force that weight to be zero, and the determinantal mass of a tight frame is
six. -/
theorem not_uniform_dppTripleWeight {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (value : ℝ)
    (huniform : ∀ slotOne slotTwo slotThree : Fin 6, slotOne ≠ slotTwo →
      slotOne ≠ slotThree → slotTwo ≠ slotThree →
      dppTripleWeight atom slotOne slotTwo slotThree = value) : False := by
  have hzero : value = 0 :=
    dppTripleWeight_eq_zero_of_uniform atom 0 1 2 3 4 value
      (huniform 0 1 2 (by decide) (by decide) (by decide))
      (huniform 0 1 3 (by decide) (by decide) (by decide))
      (huniform 0 1 4 (by decide) (by decide) (by decide))
      (huniform 0 2 3 (by decide) (by decide) (by decide))
      (huniform 0 2 4 (by decide) (by decide) (by decide))
      (huniform 0 3 4 (by decide) (by decide) (by decide))
  have hmass := dppTripleWeight_mass hframe
  have hcell : ∀ slotOne slotTwo slotThree : Fin 6,
      dppTripleWeight atom slotOne slotTwo slotThree = 0 := by
    intro slotOne slotTwo slotThree
    by_cases hone : slotOne = slotTwo
    · rw [hone]; exact dppTripleWeight_self_first atom slotTwo slotThree
    by_cases htwo : slotOne = slotThree
    · rw [htwo]; exact dppTripleWeight_self_outer atom slotThree slotTwo
    by_cases hthree : slotTwo = slotThree
    · rw [hthree]; exact dppTripleWeight_self_last atom slotOne slotThree
    rw [huniform slotOne slotTwo slotThree hone htwo hthree, hzero]
  rw [Finset.sum_congr rfl fun slotOne _ =>
      Finset.sum_congr rfl fun slotTwo _ =>
        Finset.sum_congr rfl fun slotThree _ => hcell slotOne slotTwo slotThree] at hmass
  simp at hmass

/-- **THE HERMITIAN SIDE DOES NOT GIVE THE SPREAD LAW.**  Three equal positive
paired products obey the three triangle inequalities, which is everything the
Hermitian field supplies, and no one of them reaches the sum of the other two.
So the dominance law of the real field, and the spread law that follows from it,
are NOT consequences of the field agnostic data. -/
theorem exists_triangle_without_spread :
    ∃ first second third : ℝ, 0 < first ∧ 0 < second ∧ 0 < third
      ∧ first ≤ second + third ∧ second ≤ first + third ∧ third ≤ first + second
      ∧ ¬ (second + third ≤ first ∨ first + third ≤ second ∨ first + second ≤ third) := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_⟩
  rintro (h | h | h) <;> norm_num at h

/-- The Heron form of three equal positive numbers is strictly negative.  That
is the Hermitian reading, and the real reading is zero
(`Gtz.dppHeron_plucker_eq_zero`). -/
theorem dppHeron_neg_of_equal {value : ℝ} (hpos : 0 < value) :
    dppHeron value value value < 0 := by
  rw [dppHeron]
  nlinarith [hpos]

/-! ## Layer 4 — the whitening engine -/

/-- The WEIGHTED SECOND MOMENT of a family: the matrix of the weighted outer
products of the family vectors. -/
noncomputable def whitenedSecondMoment (fam : Fin 6 → (Fin 3 → ℝ)) (weight : Fin 6 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun rowIndex colIndex => ∑ slot, weight slot * (fam slot rowIndex * fam slot colIndex)

/-- The second moment reads a pair of directions as the weighted total of the
two readings. -/
theorem whitenedSecondMoment_reading (fam : Fin 6 → (Fin 3 → ℝ)) (weight : Fin 6 → ℝ)
    (probe direction : Fin 3 → ℝ) :
    probe ⬝ᵥ (whitenedSecondMoment fam weight).mulVec direction
      = ∑ slot, weight slot * ((fam slot ⬝ᵥ probe) * (fam slot ⬝ᵥ direction)) := by
  simp only [whitenedSecondMoment, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Fin.sum_univ_three, Fin.sum_univ_six]
  ring

/-- The second moment is symmetric. -/
theorem whitenedSecondMoment_symm (fam : Fin 6 → (Fin 3 → ℝ)) (weight : Fin 6 → ℝ)
    (rowIndex colIndex : Fin 3) :
    whitenedSecondMoment fam weight rowIndex colIndex
      = whitenedSecondMoment fam weight colIndex rowIndex := by
  simp only [whitenedSecondMoment, Matrix.of_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- A symmetric matrix moves across the dot product. -/
theorem symmetric_mulVec_dot {mat : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : ∀ rowIndex colIndex, mat rowIndex colIndex = mat colIndex rowIndex)
    (vecOne vecTwo : Fin 3 → ℝ) :
    (mat.mulVec vecOne) ⬝ᵥ vecTwo = vecOne ⬝ᵥ (mat.mulVec vecTwo) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [hsymm 1 0, hsymm 2 0, hsymm 2 1]
  ring

/-- The transpose form of the symmetry, for the matrices the square root
returns. -/
theorem symm_of_transpose_eq {mat : Matrix (Fin 3) (Fin 3) ℝ} (htrans : matᵀ = mat)
    (rowIndex colIndex : Fin 3) : mat rowIndex colIndex = mat colIndex rowIndex := by
  conv_lhs => rw [← htrans]
  rfl

/-- A nonzero real vector has strictly positive energy. -/
theorem dot_self_pos_of_ne_zero {probe : Fin 3 → ℝ} (hne : probe ≠ 0) :
    0 < probe ⬝ᵥ probe := by
  obtain ⟨index, hindex⟩ := Function.ne_iff.mp hne
  have hindexNe : probe index ≠ 0 := by simpa using hindex
  refine Finset.sum_pos' (fun position _ => mul_self_nonneg (probe position))
    ⟨index, Finset.mem_univ index, ?_⟩
  exact mul_self_pos.mpr hindexNe

/-- **THE SECOND MOMENT OF A PARSEVAL FAMILY AT POSITIVE WEIGHTS IS POSITIVE
DEFINITE.**  The frame law makes the total reading of a nonzero direction
positive, so at least one slot reads it, and the weight of that slot is
positive. -/
theorem whitenedSecondMoment_posDef {fam : Fin 6 → (Fin 3 → ℝ)} {weight : Fin 6 → ℝ}
    (hpos : ∀ slot, 0 < weight slot)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (fam slot ⬝ᵥ probe) * (fam slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (whitenedSecondMoment fam weight).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · show (whitenedSecondMoment fam weight)ᴴ = whitenedSecondMoment fam weight
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    ext rowIndex colIndex
    exact whitenedSecondMoment_symm fam weight colIndex rowIndex
  · intro probe hne
    have hstar : star probe = probe := rfl
    rw [hstar, whitenedSecondMoment_reading]
    have htotal : (∑ slot, (fam slot ⬝ᵥ probe) * (fam slot ⬝ᵥ probe)) = probe ⬝ᵥ probe :=
      hframe probe probe
    have hprobePos : 0 < probe ⬝ᵥ probe := dot_self_pos_of_ne_zero hne
    have hexists : ∃ slot ∈ (Finset.univ : Finset (Fin 6)),
        0 < (fam slot ⬝ᵥ probe) * (fam slot ⬝ᵥ probe) := by
      by_contra hnone
      push Not at hnone
      have hle : (∑ slot, (fam slot ⬝ᵥ probe) * (fam slot ⬝ᵥ probe)) ≤ 0 :=
        Finset.sum_nonpos fun slot hslot => hnone slot hslot
      rw [htotal] at hle
      linarith
    obtain ⟨slot, hslotMem, hslotPos⟩ := hexists
    refine Finset.sum_pos' (fun position _ =>
      mul_nonneg (hpos position).le (mul_self_nonneg _)) ⟨slot, hslotMem, ?_⟩
    exact mul_pos (hpos slot) hslotPos

/-- The MIXER of a family and its weights: the inverse square root of the
weighted second moment, acting on directions. -/
noncomputable def whitenedMixer (fam : Fin 6 → (Fin 3 → ℝ)) (weight : Fin 6 → ℝ)
    (direction : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ((gramRoot (whitenedSecondMoment fam weight))⁻¹).mulVec direction

/-- The WHITENED FRAME: divide by the square root of the weight and whiten by
the inverse square root of the weighted second moment.  The result is a Parseval
frame whatever the family and the positive weights were. -/
noncomputable def whitenedFrame (fam : Fin 6 → (Fin 3 → ℝ)) (weight : Fin 6 → ℝ) :
    Fin 6 → (Fin 3 → ℝ) := fun slot =>
  Real.sqrt (weight slot) • whitenedMixer fam weight (fam slot)

theorem whitenedMixer_symm (fam : Fin 6 → (Fin 3 → ℝ)) (weight : Fin 6 → ℝ)
    (vecOne vecTwo : Fin 3 → ℝ) :
    (whitenedMixer fam weight vecOne) ⬝ᵥ vecTwo
      = vecOne ⬝ᵥ (whitenedMixer fam weight vecTwo) :=
  symmetric_mulVec_dot
    (symm_of_transpose_eq (transpose_inv_gramRoot (whitenedSecondMoment fam weight)))
    vecOne vecTwo

/-- A whitened frame vector reads a direction as the scaled reading of the
family vector against the mixed direction. -/
theorem whitenedFrame_dot (fam : Fin 6 → (Fin 3 → ℝ)) (weight : Fin 6 → ℝ)
    (slot : Fin 6) (direction : Fin 3 → ℝ) :
    whitenedFrame fam weight slot ⬝ᵥ direction
      = Real.sqrt (weight slot) * (fam slot ⬝ᵥ whitenedMixer fam weight direction) := by
  have hmove : (whitenedMixer fam weight (fam slot)) ⬝ᵥ direction
      = fam slot ⬝ᵥ whitenedMixer fam weight direction :=
    whitenedMixer_symm fam weight (fam slot) direction
  rw [whitenedFrame, ← hmove]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- **THE WHITENED FRAME IS A PARSEVAL FRAME.**  The congruence by the inverse
square root of the weighted second moment turns that moment into the
identity. -/
theorem whitenedFrame_isTightFrame {fam : Fin 6 → (Fin 3 → ℝ)} {weight : Fin 6 → ℝ}
    (hpos : ∀ slot, 0 < weight slot)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (fam slot ⬝ᵥ probe) * (fam slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (probe direction : Fin 3 → ℝ) :
    (∑ slot, (whitenedFrame fam weight slot ⬝ᵥ probe)
        * (whitenedFrame fam weight slot ⬝ᵥ direction)) = probe ⬝ᵥ direction := by
  have hposDef : (whitenedSecondMoment fam weight).PosDef :=
    whitenedSecondMoment_posDef hpos hframe
  have hcell : ∀ slot : Fin 6,
      (whitenedFrame fam weight slot ⬝ᵥ probe)
          * (whitenedFrame fam weight slot ⬝ᵥ direction)
        = weight slot * ((fam slot ⬝ᵥ whitenedMixer fam weight probe)
            * (fam slot ⬝ᵥ whitenedMixer fam weight direction)) := by
    intro slot
    rw [whitenedFrame_dot, whitenedFrame_dot]
    have hsq : Real.sqrt (weight slot) * Real.sqrt (weight slot) = weight slot :=
      Real.mul_self_sqrt (hpos slot).le
    linear_combination ((fam slot ⬝ᵥ whitenedMixer fam weight probe)
      * (fam slot ⬝ᵥ whitenedMixer fam weight direction)) * hsq
  rw [Finset.sum_congr rfl fun slot _ => hcell slot,
    ← whitenedSecondMoment_reading fam weight (whitenedMixer fam weight probe)
      (whitenedMixer fam weight direction)]
  have htrans : ((gramRoot (whitenedSecondMoment fam weight))⁻¹)ᵀ
      = (gramRoot (whitenedSecondMoment fam weight))⁻¹ :=
    transpose_inv_gramRoot _
  have hconj : (gramRoot (whitenedSecondMoment fam weight))⁻¹
      * whitenedSecondMoment fam weight * (gramRoot (whitenedSecondMoment fam weight))⁻¹ = 1 := by
    have hstep := conj_inv_gramRoot hposDef
    rwa [htrans] at hstep
  calc (whitenedMixer fam weight probe)
        ⬝ᵥ (whitenedSecondMoment fam weight).mulVec (whitenedMixer fam weight direction)
      = probe ⬝ᵥ (whitenedMixer fam weight
          ((whitenedSecondMoment fam weight).mulVec (whitenedMixer fam weight direction))) :=
        whitenedMixer_symm fam weight probe _
    _ = probe ⬝ᵥ (((gramRoot (whitenedSecondMoment fam weight))⁻¹
          * whitenedSecondMoment fam weight
          * (gramRoot (whitenedSecondMoment fam weight))⁻¹).mulVec direction) := by
        simp only [whitenedMixer, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
    _ = probe ⬝ᵥ direction := by rw [hconj, Matrix.one_mulVec]

/-- The mixer is onto: every direction is the mix of the direction that the
square root sends to it. -/
theorem exists_whitenedMixer_eq {fam : Fin 6 → (Fin 3 → ℝ)} {weight : Fin 6 → ℝ}
    (hpos : ∀ slot, 0 < weight slot)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (fam slot ⬝ᵥ probe) * (fam slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (direction : Fin 3 → ℝ) :
    ∃ source : Fin 3 → ℝ, whitenedMixer fam weight source = direction := by
  have hposDef : (whitenedSecondMoment fam weight).PosDef :=
    whitenedSecondMoment_posDef hpos hframe
  refine ⟨(gramRoot (whitenedSecondMoment fam weight)).mulVec direction, ?_⟩
  rw [whitenedMixer, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_det_gramRoot hposDef), Matrix.one_mulVec]

/-- **THE ENERGY OF A MIXED SOURCE.**  The square root of the weighted second
moment sends a direction to a source whose energy is the weighted total reading
of that direction. -/
theorem whitenedMixer_source_energy {fam : Fin 6 → (Fin 3 → ℝ)} {weight : Fin 6 → ℝ}
    (hpos : ∀ slot, 0 < weight slot)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (fam slot ⬝ᵥ probe) * (fam slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (direction : Fin 3 → ℝ) :
    ((gramRoot (whitenedSecondMoment fam weight)).mulVec direction)
        ⬝ᵥ ((gramRoot (whitenedSecondMoment fam weight)).mulVec direction)
      = ∑ slot, weight slot * (fam slot ⬝ᵥ direction) ^ 2 := by
  have hposDef : (whitenedSecondMoment fam weight).PosDef :=
    whitenedSecondMoment_posDef hpos hframe
  have hsymm : ∀ rowIndex colIndex,
      gramRoot (whitenedSecondMoment fam weight) rowIndex colIndex
        = gramRoot (whitenedSecondMoment fam weight) colIndex rowIndex :=
    symm_of_transpose_eq (transpose_gramRoot (whitenedSecondMoment fam weight))
  have hstep : ((gramRoot (whitenedSecondMoment fam weight)).mulVec direction)
      ⬝ᵥ ((gramRoot (whitenedSecondMoment fam weight)).mulVec direction)
      = direction ⬝ᵥ ((gramRoot (whitenedSecondMoment fam weight)
          * gramRoot (whitenedSecondMoment fam weight)).mulVec direction) := by
    rw [symmetric_mulVec_dot hsymm direction _, Matrix.mulVec_mulVec]
  rw [hstep, gramRoot_mul_self hposDef, whitenedSecondMoment_reading]
  exact Finset.sum_congr rfl fun slot _ => by ring

/-! ## Layer 5 — the dual face of the residue -/

/-- **THE DUAL SELECTION FACE.**  A rank three Parseval frame of six atoms and
positive scales of mass one carry a triple whose reading energy is at least the
SCALE WEIGHTED TOTAL reading energy, in every direction.

The left side of the comparison does not move with the triple.  That is the
whole difference from the residue, where both sides move. -/
def AtomDualSelectionClosed : Prop :=
  ∀ (frame : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (frame slot ⬝ᵥ probe) * (frame slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ ∀ direction : Fin 3 → ℝ,
            (∑ slot, scale slot * (frame slot ⬝ᵥ direction) ^ 2)
              ≤ (frame slotOne ⬝ᵥ direction) ^ 2 + (frame slotTwo ⬝ᵥ direction) ^ 2
                + (frame slotThree ⬝ᵥ direction) ^ 2

/-- **THE DUAL FACE GIVES THE OPERATOR FACE.**  Whiten the atoms by the inverse
square root of the scaled second moment and divide each atom by the square root
of its scale.  The result is a Parseval frame, the scale weighted total reading
of that frame is the energy of the mixed direction, and the reading of a triple
is the scaled reading of the original triple. -/
theorem atomTripleOperatorClosed_of_atomDualSelection
    (hdual : AtomDualSelectionClosed) : AtomTripleOperatorClosed := by
  intro atom scale hpos hmass hframe
  set weight : Fin 6 → ℝ := fun slot => (scale slot)⁻¹ with hweightDef
  have hweightApp : ∀ slot, weight slot = (scale slot)⁻¹ := fun _ => rfl
  have hweightPos : ∀ slot, 0 < weight slot := fun slot => by
    rw [hweightApp slot]; exact inv_pos.mpr (hpos slot)
  have hframeTight : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (whitenedFrame atom weight slot ⬝ᵥ probe)
        * (whitenedFrame atom weight slot ⬝ᵥ direction)) = probe ⬝ᵥ direction :=
    whitenedFrame_isTightFrame hweightPos hframe
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hread⟩ :=
    hdual (whitenedFrame atom weight) scale hpos hmass hframeTight
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, ?_⟩
  intro direction
  obtain ⟨source, hsource⟩ := exists_whitenedMixer_eq hweightPos hframe direction
  have hstep := hread source
  have hcell : ∀ slot : Fin 6,
      (whitenedFrame atom weight slot ⬝ᵥ source) ^ 2
        = (atom slot ⬝ᵥ direction) ^ 2 / scale slot := by
    intro slot
    rw [whitenedFrame_dot, hsource, mul_pow, hweightApp slot]
    have hsq : Real.sqrt ((scale slot)⁻¹) ^ 2 = (scale slot)⁻¹ :=
      Real.sq_sqrt (inv_pos.mpr (hpos slot)).le
    rw [hsq]
    field_simp
  have hscaleCell : ∀ slot : Fin 6,
      scale slot * (whitenedFrame atom weight slot ⬝ᵥ source) ^ 2
        = (atom slot ⬝ᵥ direction) * (atom slot ⬝ᵥ direction) := by
    intro slot
    have hne : scale slot ≠ 0 := (hpos slot).ne'
    rw [hcell slot]
    field_simp
  rw [Finset.sum_congr rfl fun slot _ => hscaleCell slot, hframe direction direction,
    hcell slotOne, hcell slotTwo, hcell slotThree] at hstep
  exact hstep

/-- **THE OPERATOR FACE GIVES THE DUAL FACE.**  The same congruence in the other
direction: whiten the frame by the inverse square root of the scale weighted
second moment and multiply each vector by the square root of its scale.  The
source that the square root returns carries exactly the scale weighted total
reading as its energy. -/
theorem atomDualSelectionClosed_of_atomTripleOperator
    (hoperator : AtomTripleOperatorClosed) : AtomDualSelectionClosed := by
  intro frame scale hpos hmass hframe
  have hatomTight : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (whitenedFrame frame scale slot ⬝ᵥ probe)
        * (whitenedFrame frame scale slot ⬝ᵥ direction)) = probe ⬝ᵥ direction :=
    whitenedFrame_isTightFrame hpos hframe
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hread⟩ :=
    hoperator (whitenedFrame frame scale) scale hpos hmass hatomTight
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, ?_⟩
  intro direction
  have hstep := hread ((gramRoot (whitenedSecondMoment frame scale)).mulVec direction)
  have henergy := whitenedMixer_source_energy hpos hframe direction
  have hmixBack : whitenedMixer frame scale
      ((gramRoot (whitenedSecondMoment frame scale)).mulVec direction) = direction := by
    have hposDef : (whitenedSecondMoment frame scale).PosDef :=
      whitenedSecondMoment_posDef hpos hframe
    rw [whitenedMixer, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_det_gramRoot hposDef), Matrix.one_mulVec]
  have hcell : ∀ slot : Fin 6,
      (whitenedFrame frame scale slot
          ⬝ᵥ (gramRoot (whitenedSecondMoment frame scale)).mulVec direction) ^ 2 / scale slot
        = (frame slot ⬝ᵥ direction) ^ 2 := by
    intro slot
    have hne : scale slot ≠ 0 := (hpos slot).ne'
    rw [whitenedFrame_dot, hmixBack, mul_pow,
      Real.sq_sqrt (hpos slot).le]
    field_simp
  rw [henergy] at hstep
  rw [hcell slotOne, hcell slotTwo, hcell slotThree] at hstep
  exact hstep

/-- **THE DUAL FACE IS THE RESIDUE.**  The two statements are equivalent, so the
dual face hides nothing. -/
theorem atomDualSelectionClosed_iff_atomTripleBoundary :
    AtomDualSelectionClosed ↔ AtomTripleBoundaryClosed := by
  constructor
  · intro hdual
    exact atomTripleBoundaryClosed_of_atomTripleOperator
      (atomTripleOperatorClosed_of_atomDualSelection hdual)
  · intro hboundary
    exact atomDualSelectionClosed_of_atomTripleOperator
      ((atomTripleOperatorClosed_iff_atomTripleBoundary).mpr hboundary)

/-- **THE DUAL FACE CLOSES THE CELL.**  Composing the equivalence with the
landed ceiling passage gives the weighted cell at six slots and rank three. -/
theorem gtzWeighted_six_three_of_atomDualSelection
    (hdual : AtomDualSelectionClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomTripleCeiling
    (atomTripleCeilingClosed_of_atomTripleBoundary
      (atomDualSelectionClosed_iff_atomTripleBoundary.mp hdual))

/-! ## Layer 6 — unconditional criteria in the dual face -/

/-- **THE COMPLEMENT READING OF THE DUAL COMPARISON.**  The dual comparison at a
triple says exactly that the three slots outside the triple pay less than the
shifted reading of the three inside it.  No side of this identity carries a
minor or a determinant. -/
theorem atomDualTriple_iff_complement {frame : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    {slotOne slotTwo slotThree : Fin 6} (direction : Fin 3 → ℝ) :
    ((∑ slot, scale slot * (frame slot ⬝ᵥ direction) ^ 2)
        ≤ (frame slotOne ⬝ᵥ direction) ^ 2 + (frame slotTwo ⬝ᵥ direction) ^ 2
          + (frame slotThree ⬝ᵥ direction) ^ 2)
      ↔ ((∑ slot, scale slot * (frame slot ⬝ᵥ direction) ^ 2)
            - scale slotOne * (frame slotOne ⬝ᵥ direction) ^ 2
            - scale slotTwo * (frame slotTwo ⬝ᵥ direction) ^ 2
            - scale slotThree * (frame slotThree ⬝ᵥ direction) ^ 2
          ≤ (1 - scale slotOne) * (frame slotOne ⬝ᵥ direction) ^ 2
            + (1 - scale slotTwo) * (frame slotTwo ⬝ᵥ direction) ^ 2
            + (1 - scale slotThree) * (frame slotThree ⬝ᵥ direction) ^ 2) := by
  constructor <;> intro hstep <;> nlinarith [hstep]

/-- **THE CAP CRITERION.**  A triple whose reading energy reaches the largest
scale, in every direction, satisfies the dual comparison.  The proof is the
frame law: the scale weighted total reading never passes the largest scale times
the energy. -/
theorem atomDualTriple_of_cap {frame : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (frame slot ⬝ᵥ probe) * (frame slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {cap : ℝ} (hcap : ∀ slot, scale slot ≤ cap)
    {slotOne slotTwo slotThree : Fin 6}
    (hcover : ∀ direction : Fin 3 → ℝ,
      cap * (direction ⬝ᵥ direction)
        ≤ (frame slotOne ⬝ᵥ direction) ^ 2 + (frame slotTwo ⬝ᵥ direction) ^ 2
          + (frame slotThree ⬝ᵥ direction) ^ 2)
    (direction : Fin 3 → ℝ) :
    (∑ slot, scale slot * (frame slot ⬝ᵥ direction) ^ 2)
      ≤ (frame slotOne ⬝ᵥ direction) ^ 2 + (frame slotTwo ⬝ᵥ direction) ^ 2
        + (frame slotThree ⬝ᵥ direction) ^ 2 := by
  have hcapBound : (∑ slot, scale slot * (frame slot ⬝ᵥ direction) ^ 2)
      ≤ ∑ slot, cap * (frame slot ⬝ᵥ direction) ^ 2 :=
    Finset.sum_le_sum fun slot _ =>
      mul_le_mul_of_nonneg_right (hcap slot) (sq_nonneg _)
  have hframeEnergy : (∑ slot, (frame slot ⬝ᵥ direction) ^ 2) = direction ⬝ᵥ direction := by
    rw [← hframe direction direction]
    exact Finset.sum_congr rfl fun slot _ => by ring
  rw [← Finset.mul_sum, hframeEnergy] at hcapBound
  exact le_trans hcapBound (hcover direction)

/-- **THE UNIFORM COVER GIVES THE WHOLE DUAL FACE.**  A covering law that
returns, at every rank three Parseval frame of six atoms and every positive
level, a triple whose least reading reaches that level, gives the dual face at
the largest scale of the datum.  This is the exact sense in which the residue is
the UNWEIGHTED covering statement read at one level. -/
theorem atomDualSelectionClosed_of_uniformCover
    (hcover : ∀ (frame : Fin 6 → (Fin 3 → ℝ)) (level : ℝ),
      (∀ probe direction : Fin 3 → ℝ,
        (∑ slot, (frame slot ⬝ᵥ probe) * (frame slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
      level ≤ 1 →
      (∃ slotOne slotTwo slotThree : Fin 6,
        slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
          ∧ ∀ direction : Fin 3 → ℝ,
              level * (direction ⬝ᵥ direction)
                ≤ (frame slotOne ⬝ᵥ direction) ^ 2 + (frame slotTwo ⬝ᵥ direction) ^ 2
                  + (frame slotThree ⬝ᵥ direction) ^ 2)) :
    AtomDualSelectionClosed := by
  classical
  intro frame scale hpos hmass hframe
  obtain ⟨cap, hcapMem, hcapMax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 6)) scale ⟨0, Finset.mem_univ 0⟩
  have hcapLe : ∀ slot, scale slot ≤ scale cap := fun slot => hcapMax slot (Finset.mem_univ slot)
  have hcapOne : scale cap ≤ 1 := by
    have hrest : (0:ℝ) ≤ ∑ slot ∈ Finset.univ.erase cap, scale slot :=
      Finset.sum_nonneg fun slot _ => (hpos slot).le
    have hsplit : scale cap + ∑ slot ∈ Finset.univ.erase cap, scale slot
        = ∑ slot, scale slot :=
      Finset.add_sum_erase _ scale (Finset.mem_univ cap)
    rw [hmass] at hsplit
    linarith
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hcell⟩ :=
    hcover frame (scale cap) hframe hcapOne
  exact ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree,
    fun direction => atomDualTriple_of_cap hframe hcapLe hcell direction⟩

/-- **THE LARGEST SCALE OF A MASS ONE DATUM IS AT LEAST ONE SIXTH.**  So the
level the uniform cover has to reach is never smaller than one sixth, and the
uniform cover at level one sixth is exactly the unweighted covering statement of
six atoms at rank three. -/
theorem exists_scale_ge_one_sixth {scale : Fin 6 → ℝ} (hmass : (∑ slot, scale slot) = 1) :
    ∃ slot : Fin 6, (1:ℝ) / 6 ≤ scale slot := by
  by_contra hnone
  push Not at hnone
  have hstrict : (∑ slot : Fin 6, scale slot) < ∑ _slot : Fin 6, (1:ℝ) / 6 :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun slot _ => hnone slot
  rw [hmass] at hstrict
  simp at hstrict

/-- **THE SPREAD LAW AS A RATIO.**  The largest of the six determinantal weights
through a pivot and four slots is at least the square root of two times the
smallest.  The constant is the one the dominance law gives, and the icosahedral
frame, the most balanced real frame of this size, carries the much larger ratio
`(3 + sqrt 5) / 2`. -/
theorem dppPlucker_spread_sqrt (atom : Fin 6 → (Fin 3 → ℝ))
    (pivot slotOne slotTwo slotThree slotFour : Fin 6) (low high : ℝ)
    (hlow : 0 ≤ low)
    (hlowOneTwo : low ≤ dppTripleWeight atom pivot slotOne slotTwo)
    (hlowOneThree : low ≤ dppTripleWeight atom pivot slotOne slotThree)
    (hlowOneFour : low ≤ dppTripleWeight atom pivot slotOne slotFour)
    (hlowTwoThree : low ≤ dppTripleWeight atom pivot slotTwo slotThree)
    (hlowTwoFour : low ≤ dppTripleWeight atom pivot slotTwo slotFour)
    (hlowThreeFour : low ≤ dppTripleWeight atom pivot slotThree slotFour)
    (hhighOneTwo : dppTripleWeight atom pivot slotOne slotTwo ≤ high)
    (hhighOneThree : dppTripleWeight atom pivot slotOne slotThree ≤ high)
    (hhighOneFour : dppTripleWeight atom pivot slotOne slotFour ≤ high)
    (hhighTwoThree : dppTripleWeight atom pivot slotTwo slotThree ≤ high)
    (hhighTwoFour : dppTripleWeight atom pivot slotTwo slotFour ≤ high)
    (hhighThreeFour : dppTripleWeight atom pivot slotThree slotFour ≤ high) :
    Real.sqrt 2 * low ≤ high := by
  have hspread : 2 * low ^ 2 ≤ high ^ 2 :=
    dppPlucker_spread atom pivot slotOne slotTwo slotThree slotFour low high hlow
      hlowOneTwo hlowOneThree hlowOneFour hlowTwoThree hlowTwoFour hlowThreeFour
      hhighOneTwo hhighOneThree hhighOneFour hhighTwoThree hhighTwoFour hhighThreeFour
  have hhighNonneg : 0 ≤ high := le_trans hlow (le_trans hlowOneTwo hhighOneTwo)
  have hrootSq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hrootNonneg : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [hspread, hhighNonneg, hrootSq, hrootNonneg, hlow]

/-- **A DETERMINANTAL WEIGHT FLOOR.**  Some ordered triple of a rank three
Parseval frame of six atoms carries a determinantal weight of at least one
thirty sixth.  The determinantal mass of the two hundred and sixteen ordered
triples is six. -/
theorem exists_dppTripleWeight_ge {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      (1:ℝ) / 36 ≤ dppTripleWeight atom slotOne slotTwo slotThree := by
  by_contra hnone
  push Not at hnone
  have hmass := dppTripleWeight_mass hframe
  have hinner : ∀ slotOne slotTwo : Fin 6,
      (∑ slotThree, dppTripleWeight atom slotOne slotTwo slotThree)
        < ∑ _slotThree : Fin 6, (1:ℝ) / 36 := fun slotOne slotTwo =>
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩
      fun slotThree _ => hnone slotOne slotTwo slotThree
  have hmid : ∀ slotOne : Fin 6,
      (∑ slotTwo, ∑ slotThree, dppTripleWeight atom slotOne slotTwo slotThree)
        < ∑ _slotTwo : Fin 6, ∑ _slotThree : Fin 6, (1:ℝ) / 36 := fun slotOne =>
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun slotTwo _ => hinner slotOne slotTwo
  have htop : (∑ slotOne, ∑ slotTwo, ∑ slotThree, dppTripleWeight atom slotOne slotTwo slotThree)
      < ∑ _slotOne : Fin 6, ∑ _slotTwo : Fin 6, ∑ _slotThree : Fin 6, (1:ℝ) / 36 :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun slotOne _ => hmid slotOne
  rw [hmass] at htop
  norm_num at htop

/-! ## Layer 7 — the split criterion of the dual face -/

/-- The three slots of a triple, as a set. -/
def atomTripleCar (slotOne slotTwo slotThree : Fin 6) : Finset (Fin 6) :=
  {slotOne, slotTwo, slotThree}

theorem atomTripleCar_sum {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) (value : Fin 6 → ℝ) :
    (∑ slot ∈ atomTripleCar slotOne slotTwo slotThree, value slot)
      = value slotOne + value slotTwo + value slotThree := by
  classical
  rw [atomTripleCar, Finset.sum_insert (by simp [honeTwo, honeThree]),
    Finset.sum_insert (by simp [htwoThree]), Finset.sum_singleton]
  ring

theorem atomTripleCar_mem_compl {slotOne slotTwo slotThree slot : Fin 6}
    (hmem : slot ∈ (atomTripleCar slotOne slotTwo slotThree)ᶜ) :
    slot ≠ slotOne ∧ slot ≠ slotTwo ∧ slot ≠ slotThree := by
  classical
  rw [Finset.mem_compl, atomTripleCar] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
  exact hmem

/-- **THE SPLIT CRITERION OF THE DUAL FACE.**  A triple satisfies the dual
comparison at a direction exactly when the three slots outside it pay less than
the SHIFTED reading of the three inside it.  This is the exact rearrangement,
with no loss, and it is the form every criterion of the dual face uses. -/
theorem atomDualTriple_of_split {frame : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) (direction : Fin 3 → ℝ)
    (hstep : (∑ slot ∈ (atomTripleCar slotOne slotTwo slotThree)ᶜ,
          scale slot * (frame slot ⬝ᵥ direction) ^ 2)
        ≤ (1 - scale slotOne) * (frame slotOne ⬝ᵥ direction) ^ 2
          + (1 - scale slotTwo) * (frame slotTwo ⬝ᵥ direction) ^ 2
          + (1 - scale slotThree) * (frame slotThree ⬝ᵥ direction) ^ 2) :
    (∑ slot, scale slot * (frame slot ⬝ᵥ direction) ^ 2)
      ≤ (frame slotOne ⬝ᵥ direction) ^ 2 + (frame slotTwo ⬝ᵥ direction) ^ 2
        + (frame slotThree ⬝ᵥ direction) ^ 2 := by
  classical
  have hsplit : (∑ slot, scale slot * (frame slot ⬝ᵥ direction) ^ 2)
      = (∑ slot ∈ atomTripleCar slotOne slotTwo slotThree,
          scale slot * (frame slot ⬝ᵥ direction) ^ 2)
        + ∑ slot ∈ (atomTripleCar slotOne slotTwo slotThree)ᶜ,
            scale slot * (frame slot ⬝ᵥ direction) ^ 2 :=
    (Finset.sum_add_sum_compl (atomTripleCar slotOne slotTwo slotThree) _).symm
  rw [hsplit, atomTripleCar_sum honeTwo honeThree htwoThree
    (fun slot => scale slot * (frame slot ⬝ᵥ direction) ^ 2)]
  linarith [hstep]

/-- **THE REFINED CAP CRITERION, AND IT IS STRICTLY STRONGER THAN THE PLAIN
ONE.**  Let `outside` bound the scales of the three slots outside the triple and
let `inside` bound the scales of the three inside it.  The triple satisfies the
dual comparison as soon as its reading energy reaches
`outside / (1 + outside - inside)` times the energy.

When the triple carries the three heaviest slots the outside bound is the fourth
largest scale, which a mass one datum caps at one quarter, while the plain cap
criterion has to reach the LARGEST scale, which can approach one.  So this
criterion is the one to use on a spread datum. -/
theorem atomDualTriple_of_refinedCap {frame : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (frame slot ⬝ᵥ probe) * (frame slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree) {outside inside : ℝ}
    (houtside : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo → slot ≠ slotThree →
      scale slot ≤ outside)
    (hinsideOne : scale slotOne ≤ inside) (hinsideTwo : scale slotTwo ≤ inside)
    (hinsideThree : scale slotThree ≤ inside) (direction : Fin 3 → ℝ)
    (hcover : outside * (direction ⬝ᵥ direction)
      ≤ (1 + outside - inside) * ((frame slotOne ⬝ᵥ direction) ^ 2
          + (frame slotTwo ⬝ᵥ direction) ^ 2 + (frame slotThree ⬝ᵥ direction) ^ 2)) :
    (∑ slot, scale slot * (frame slot ⬝ᵥ direction) ^ 2)
      ≤ (frame slotOne ⬝ᵥ direction) ^ 2 + (frame slotTwo ⬝ᵥ direction) ^ 2
        + (frame slotThree ⬝ᵥ direction) ^ 2 := by
  classical
  refine atomDualTriple_of_split honeTwo honeThree htwoThree direction ?_
  have houtsideBound : (∑ slot ∈ (atomTripleCar slotOne slotTwo slotThree)ᶜ,
        scale slot * (frame slot ⬝ᵥ direction) ^ 2)
      ≤ ∑ slot ∈ (atomTripleCar slotOne slotTwo slotThree)ᶜ,
          outside * (frame slot ⬝ᵥ direction) ^ 2 := by
    refine Finset.sum_le_sum fun slot hslot => ?_
    obtain ⟨hone, htwo, hthree⟩ := atomTripleCar_mem_compl hslot
    exact mul_le_mul_of_nonneg_right (houtside slot hone htwo hthree) (sq_nonneg _)
  have hcarEnergy : (∑ slot ∈ atomTripleCar slotOne slotTwo slotThree,
        (frame slot ⬝ᵥ direction) ^ 2)
      = (frame slotOne ⬝ᵥ direction) ^ 2 + (frame slotTwo ⬝ᵥ direction) ^ 2
        + (frame slotThree ⬝ᵥ direction) ^ 2 :=
    atomTripleCar_sum honeTwo honeThree htwoThree
      (fun slot => (frame slot ⬝ᵥ direction) ^ 2)
  have hwhole : (∑ slot, (frame slot ⬝ᵥ direction) ^ 2) = direction ⬝ᵥ direction := by
    rw [← hframe direction direction]
    exact Finset.sum_congr rfl fun slot _ => by ring
  have hcompl : (∑ slot ∈ (atomTripleCar slotOne slotTwo slotThree)ᶜ,
        (frame slot ⬝ᵥ direction) ^ 2)
      = direction ⬝ᵥ direction
        - ((frame slotOne ⬝ᵥ direction) ^ 2 + (frame slotTwo ⬝ᵥ direction) ^ 2
          + (frame slotThree ⬝ᵥ direction) ^ 2) := by
    have hboth := (Finset.sum_add_sum_compl (atomTripleCar slotOne slotTwo slotThree)
      (fun slot => (frame slot ⬝ᵥ direction) ^ 2))
    rw [hcarEnergy] at hboth
    rw [hwhole] at hboth
    linarith [hboth]
  rw [← Finset.mul_sum, hcompl] at houtsideBound
  nlinarith [houtsideBound, hcover, hinsideOne, hinsideTwo, hinsideThree,
    sq_nonneg (frame slotOne ⬝ᵥ direction), sq_nonneg (frame slotTwo ⬝ᵥ direction),
    sq_nonneg (frame slotThree ⬝ᵥ direction)]

/-! ## Layer 8 — the dual face against the other faces of the residue -/

/-- The dual face and the vertex cover face are the same statement. -/
theorem atomDualSelectionClosed_iff_atomVertexCover :
    AtomDualSelectionClosed ↔ AtomVertexCoverClosed :=
  atomDualSelectionClosed_iff_atomTripleBoundary.trans
    atomVertexCoverClosed_iff_atomTripleBoundary.symm

/-- The dual face and the operator face are the same statement. -/
theorem atomDualSelectionClosed_iff_atomTripleOperator :
    AtomDualSelectionClosed ↔ AtomTripleOperatorClosed :=
  ⟨atomTripleOperatorClosed_of_atomDualSelection, atomDualSelectionClosed_of_atomTripleOperator⟩

/-- The dual face and the quad drop factorization are the same statement. -/
theorem atomDualSelectionClosed_iff_atomQuadDropSome :
    AtomDualSelectionClosed ↔ AtomQuadDropSomeClosed :=
  atomDualSelectionClosed_iff_atomVertexCover.trans
    atomQuadDropSomeClosed_iff_atomVertexCover.symm

end Gtz
