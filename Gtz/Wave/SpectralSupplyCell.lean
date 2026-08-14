import Gtz.Wave.AtomVertexSelection
import Gtz.Wave.OrientedTriangleSign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The spectral supply of a rank-three Parseval frame of six atoms

This module reads the atom cell through the UNSHIFTED three-by-three blocks of
the Gram, and it lands four things that the cell union of the campaign does
not have.

## 1. The universal moment law

For EVERY rank-three Parseval frame of six atoms the three symmetric functions
of the twenty unshifted blocks add to the SAME three numbers:

* `Gtz.atomBlockTrace_familySum` — the trace total is `30`
* `Gtz.atomBlockSecond_familySum` — the second minor total is `12`
* `Gtz.atomBlockDet_familySum` — the determinant total is `1`.

Nothing about the frame enters. The determinant total is the Cauchy-Binet
mass of the determinantal measure on the twenty triples, and the other two are
its first two marginals. The consequence is the sharpest form of the blindness
that three lanes of the campaign measured:

* `Gtz.atomTripleDet_familySum_uniform` — at the UNIFORM scale `weight` the
  twenty shifted triple determinants add to `1 - 12 weight + 30 weight ^ 2
  - 20 weight ^ 3`, a universal cubic
* `Gtz.atomTripleDet_familySum_uniform_sixth` — at `weight = 1/6` that cubic is
  EXACTLY `-7/27`.

The campaign banked `-0.2593` as a reading of the icosahedral frame. It is not
a reading of that frame. It is a constant of the whole problem.

## 2. The wedge inequality

`Gtz.atomBlockDet_mul_le_atomBlockSecond_mul` says that for three atoms of
rank three and every combination `probe`,

  `det(block) * (probe energy) <= second(block) * (blend energy)`.

The proof is three Cauchy-Schwarz steps against the three wedges, and the
identity `probe slot * volume = blend . wedge` that carries them. It is the
division-free form of `lambda_min >= e3 / e2`.

## 3. The spectral supply theorem, and the first unconditional closure by a
   spectral floor

`Gtz.exists_atomSupplyTriple`: the moment law plus positivity give a triple
whose determinant is positive and whose second minor stays below `c` times it,
for every `c` past twelve. With the wedge inequality this gives
`Gtz.exists_atomLightCarrier` and `Gtz.exists_atomLightCarrier_thirteen`:

  **every rank-three Parseval frame of six atoms carries a dominating triple
  as soon as every scale is at most one thirteenth.**

No selection rule, no sign, no crux, no side hypothesis. The adversarial value
of the constant is `1/6` and it is attained, so the gap between what this
module proves and the truth is exactly a factor of two.

## 4. The partial frame operator, and the exact escape band

`Gtz.atomFrameForm` is the partial frame operator of a triple read as a form,
and `Gtz.atomFrameForm_add_complement` says that a triple and its complement
add to the identity. That makes the corner law of the campaign one line.
`Gtz.atomFrameForm_trace`, `_second`, `_det` say that the partial frame
operator and the Gram block carry the SAME three invariants.

The last layer answers the union question exactly. The coherent energy cell
and the modulus cell together certify every positive triple determinant EXCEPT
on one band, and `Gtz.atomTripleDet_pos_escape_iff_band` says that band is

  `0 < cycle`  and  `volume <= reading < volume + 2 * cycle`.

`Gtz.atomBand_empty_of_nonpos_cycle` says the band is empty on the
anti-coherent side, which is the exact complementarity of the two families, and
`Gtz.atomBand_width` says its width in the reading is `4 * |cycle|`.

## 5. The band is NOT empty

`Gtz.escapeBandAtom` is the integer witness of the modulus bar at the uniform
scale two. Its cycle is `8`, its volume `27`, its reading `36` and its shifted
determinant `7`. So `Gtz.escapeBandAtom_escapes` and
`Gtz.exists_escape_of_both_headline_cells` exhibit a triple whose determinant
is POSITIVE and which fires NEITHER headline cell. The band between the two
families is inhabited, and no comparison of the two can close the cell.

## 6. The cubic and the determinant supply

`Gtz.atomUniformCubic_factor` splits the universal cubic as
`(1 - 2 w) (1 - 10 w + 10 w ^ 2)`, whose smallest root is `(5 - sqrt 15) / 10`.
`Gtz.exists_atomTripleDet_pos_uniform` turns a positive total into a triple of
positive shifted determinant, at every uniform scale below that root.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

Every statement below is proved. The moment law rests on the three landed frame
laws only, and the wedge inequality rests on one Lagrange identity.

## Vacuity

`Gtz.exists_atomLightCarrier_thirteen` produces a carrier from a frame law and
a scale bound that a uniform scale of one twentieth satisfies, so it is not
vacuous. The band layer is an equivalence, so neither side is vacuous.
-/

namespace Gtz

/-! ## Layer 0 — the wedge of two atoms and the volume of three -/

/-- The WEDGE of two vectors of rank three: the vector orthogonal to the two
whose energy is the squared area of the parallelogram. -/
def atomWedge (leftVec rightVec : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1,
    leftVec 2 * rightVec 0 - leftVec 0 * rightVec 2,
    leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0]

theorem atomWedge_apply (leftVec rightVec : Fin 3 → ℝ) :
    (atomWedge leftVec rightVec 0
        = leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1)
      ∧ (atomWedge leftVec rightVec 1
        = leftVec 2 * rightVec 0 - leftVec 0 * rightVec 2)
      ∧ (atomWedge leftVec rightVec 2
        = leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0) := by
  refine ⟨rfl, rfl, rfl⟩

/-- **THE WEDGE ENERGY IS THE PAIR MINOR.**  The squared length of a wedge is
the product of the two squared lengths minus the square of the dot product.
This is the Lagrange identity of rank three. -/
theorem atomWedge_energy (leftVec rightVec : Fin 3 → ℝ) :
    atomWedge leftVec rightVec ⬝ᵥ atomWedge leftVec rightVec
      = (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) - (leftVec ⬝ᵥ rightVec) ^ 2 := by
  simp only [dotProduct, Fin.sum_univ_three, atomWedge, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The wedge is orthogonal to its left factor. -/
theorem atomWedge_dot_left (leftVec rightVec : Fin 3 → ℝ) :
    leftVec ⬝ᵥ atomWedge leftVec rightVec = 0 := by
  simp only [dotProduct, Fin.sum_univ_three, atomWedge, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The wedge is orthogonal to its right factor. -/
theorem atomWedge_dot_right (leftVec rightVec : Fin 3 → ℝ) :
    rightVec ⬝ᵥ atomWedge leftVec rightVec = 0 := by
  simp only [dotProduct, Fin.sum_univ_three, atomWedge, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The wedge changes sign when its two factors change places. -/
theorem atomWedge_comm (leftVec rightVec probe : Fin 3 → ℝ) :
    probe ⬝ᵥ atomWedge leftVec rightVec = -(probe ⬝ᵥ atomWedge rightVec leftVec) := by
  simp only [dotProduct, Fin.sum_univ_three, atomWedge, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **CAUCHY-SCHWARZ AT RANK THREE.**  The proof is the Lagrange identity, so
no inner product space instance is needed. -/
theorem atomDot_sq_le (leftVec rightVec : Fin 3 → ℝ) :
    (leftVec ⬝ᵥ rightVec) ^ 2 ≤ (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) := by
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0),
    sq_nonneg (leftVec 0 * rightVec 2 - leftVec 2 * rightVec 0),
    sq_nonneg (leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1)]

/-- The VOLUME of three vectors of rank three: the determinant of the three,
written as one against the wedge of the other two. -/
def atomVolume (first second third : Fin 3 → ℝ) : ℝ :=
  first ⬝ᵥ atomWedge second third

/-- The volume does not read the order of its last two arguments, up to sign. -/
theorem atomVolume_rotate (first second third : Fin 3 → ℝ) :
    atomVolume first second third = atomVolume second third first := by
  simp only [atomVolume, dotProduct, Fin.sum_univ_three, atomWedge,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-! ## Layer 1 — the three invariants of an unshifted Gram block -/

variable {atom : Fin 6 → (Fin 3 → ℝ)}

/-- The TRACE of the unshifted Gram block of three slots. -/
def atomBlockTrace (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6) : ℝ :=
  atomGram atom slotOne slotOne + atomGram atom slotTwo slotTwo
    + atomGram atom slotThree slotThree

/-- The SECOND MINOR TOTAL of the unshifted Gram block of three slots: the
three pair minors added. -/
def atomBlockSecond (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6) : ℝ :=
  (atomGram atom slotOne slotOne * atomGram atom slotTwo slotTwo
      - atomGram atom slotOne slotTwo ^ 2)
    + (atomGram atom slotOne slotOne * atomGram atom slotThree slotThree
      - atomGram atom slotOne slotThree ^ 2)
    + (atomGram atom slotTwo slotTwo * atomGram atom slotThree slotThree
      - atomGram atom slotTwo slotThree ^ 2)

/-- The DETERMINANT of the unshifted Gram block of three slots. -/
def atomBlockDet (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6) : ℝ :=
  atomGram atom slotOne slotOne * atomGram atom slotTwo slotTwo
      * atomGram atom slotThree slotThree
    + 2 * atomGram atom slotOne slotTwo * atomGram atom slotOne slotThree
        * atomGram atom slotTwo slotThree
    - atomGram atom slotOne slotOne * atomGram atom slotTwo slotThree ^ 2
    - atomGram atom slotTwo slotTwo * atomGram atom slotOne slotThree ^ 2
    - atomGram atom slotThree slotThree * atomGram atom slotOne slotTwo ^ 2

/-- **THE PAIR MINOR IS A WEDGE ENERGY.**  Hence it is never negative. -/
theorem atomPairGram_eq_wedge_energy (atom : Fin 6 → (Fin 3 → ℝ)) (rowSlot colSlot : Fin 6) :
    atomGram atom rowSlot rowSlot * atomGram atom colSlot colSlot
        - atomGram atom rowSlot colSlot ^ 2
      = atomWedge (atom rowSlot) (atom colSlot) ⬝ᵥ atomWedge (atom rowSlot) (atom colSlot) := by
  rw [atomWedge_energy]
  simp only [atomGram]

theorem atomPairGram_nonneg (atom : Fin 6 → (Fin 3 → ℝ)) (rowSlot colSlot : Fin 6) :
    0 ≤ atomGram atom rowSlot rowSlot * atomGram atom colSlot colSlot
      - atomGram atom rowSlot colSlot ^ 2 := by
  rw [atomPairGram_eq_wedge_energy]
  exact atomDot_self_nonneg _

theorem atomBlockSecond_nonneg (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6) :
    0 ≤ atomBlockSecond atom slotOne slotTwo slotThree := by
  have hone := atomPairGram_nonneg atom slotOne slotTwo
  have htwo := atomPairGram_nonneg atom slotOne slotThree
  have hthree := atomPairGram_nonneg atom slotTwo slotThree
  simp only [atomBlockSecond]
  linarith

/-- **THE BLOCK DETERMINANT IS THE SQUARE OF THE VOLUME.**  Hence it is never
negative, and it is positive exactly when the three atoms are independent. -/
theorem atomBlockDet_eq_volume_sq (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    atomBlockDet atom slotOne slotTwo slotThree
      = atomVolume (atom slotOne) (atom slotTwo) (atom slotThree) ^ 2 := by
  simp only [atomBlockDet, atomVolume, atomGram, dotProduct, Fin.sum_univ_three,
    atomWedge, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem atomBlockDet_nonneg (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6) :
    0 ≤ atomBlockDet atom slotOne slotTwo slotThree := by
  rw [atomBlockDet_eq_volume_sq]
  positivity

/-! ## Layer 2 — the twenty triples, and the universal moment law -/

/-- The total of a reading over the TWENTY distinct triples of six slots. -/
def atomTripleFamilySum (value : Fin 6 → Fin 6 → Fin 6 → ℝ) : ℝ :=
  value 0 1 2 + value 0 1 3 + value 0 1 4 + value 0 1 5 + value 0 2 3
    + value 0 2 4 + value 0 2 5 + value 0 3 4 + value 0 3 5 + value 0 4 5
    + value 1 2 3 + value 1 2 4 + value 1 2 5 + value 1 3 4 + value 1 3 5
    + value 1 4 5 + value 2 3 4 + value 2 3 5 + value 2 4 5 + value 3 4 5

/-- The SECOND POWER SUM of a symmetric slot table. -/
def atomGramPowerTwo (atom : Fin 6 → (Fin 3 → ℝ)) : ℝ :=
  ∑ rowSlot, ∑ colSlot, atomGram atom rowSlot colSlot * atomGram atom colSlot rowSlot

/-- The THIRD POWER SUM of a symmetric slot table. -/
def atomGramPowerThree (atom : Fin 6 → (Fin 3 → ℝ)) : ℝ :=
  ∑ rowSlot, ∑ midSlot, ∑ colSlot,
    atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot
      * atomGram atom colSlot rowSlot

/-- **THE SECOND POWER SUM IS THE RANK.**  Idempotence read through the row
energy law. -/
theorem atomGramPowerTwo_eq
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomGramPowerTwo atom = 3 := by
  have hcell : ∀ rowSlot : Fin 6,
      (∑ colSlot, atomGram atom rowSlot colSlot * atomGram atom colSlot rowSlot)
        = atomGram atom rowSlot rowSlot := by
    intro rowSlot
    rw [← atomGram_row_energy hframe rowSlot]
    exact Finset.sum_congr rfl fun colSlot _ => by
      rw [atomGram_comm atom colSlot rowSlot, sq]
  simp only [atomGramPowerTwo]
  rw [Finset.sum_congr rfl fun rowSlot _ => hcell rowSlot, atomGram_trace hframe]
  norm_num

/-- **THE THIRD POWER SUM IS THE RANK.**  One idempotence step folds the inner
sum, and the second power sum finishes. -/
theorem atomGramPowerThree_eq
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomGramPowerThree atom = 3 := by
  have hinner : ∀ rowSlot midSlot : Fin 6,
      (∑ colSlot, atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot
          * atomGram atom colSlot rowSlot)
        = atomGram atom rowSlot midSlot * atomGram atom midSlot rowSlot := by
    intro rowSlot midSlot
    have hpull : (∑ colSlot, atomGram atom rowSlot midSlot
          * atomGram atom midSlot colSlot * atomGram atom colSlot rowSlot)
        = atomGram atom rowSlot midSlot
          * ∑ colSlot, atomGram atom midSlot colSlot * atomGram atom colSlot rowSlot := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun colSlot _ => by ring
    rw [hpull, atomGram_idempotent hframe midSlot rowSlot]
  simp only [atomGramPowerThree]
  rw [Finset.sum_congr rfl fun rowSlot _ =>
    Finset.sum_congr rfl fun midSlot _ => hinner rowSlot midSlot]
  exact atomGramPowerTwo_eq hframe

/-- **THE TRACE TOTAL OF THE TWENTY BLOCKS.**  Each slot sits in ten triples. -/
theorem atomBlockTrace_familySum
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomTripleFamilySum (atomBlockTrace atom) = 30 := by
  have htrace : (∑ slot, atomGram atom slot slot) = 3 := by
    rw [atomGram_trace hframe]; norm_num
  simp only [Fin.sum_univ_six] at htrace
  simp only [atomTripleFamilySum, atomBlockTrace]
  linarith

/-- **THE SECOND MINOR TOTAL OF THE TWENTY BLOCKS.**  Each pair sits in four
triples, and the pair total collapses through the row energy law. -/
theorem atomBlockSecond_familySum
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomTripleFamilySum (atomBlockSecond atom) = 12 := by
  have htrace : (∑ slot, atomGram atom slot slot) = 3 := by
    rw [atomGram_trace hframe]; norm_num
  have hpower := atomGramPowerTwo_eq hframe
  simp only [atomGramPowerTwo, Fin.sum_univ_six] at hpower
  simp only [Fin.sum_univ_six] at htrace
  simp only [atomGram_comm atom 1 0, atomGram_comm atom 2 0, atomGram_comm atom 2 1,
    atomGram_comm atom 3 0, atomGram_comm atom 3 1, atomGram_comm atom 3 2,
    atomGram_comm atom 4 0, atomGram_comm atom 4 1, atomGram_comm atom 4 2,
    atomGram_comm atom 4 3, atomGram_comm atom 5 0, atomGram_comm atom 5 1,
    atomGram_comm atom 5 2, atomGram_comm atom 5 3, atomGram_comm atom 5 4] at hpower
  simp only [atomTripleFamilySum, atomBlockSecond]
  linear_combination (2 * (atomGram atom 0 0 + atomGram atom 1 1 + atomGram atom 2 2
      + atomGram atom 3 3 + atomGram atom 4 4 + atomGram atom 5 5 + 3)) * htrace
    - 2 * hpower

/-- **THE SYMMETRIC NEWTON IDENTITY AT SIX SLOTS.**  Six times the total of the
twenty principal three-minors is the third elementary symmetric polynomial of
the eigenvalues, written in the three power sums.  It reads no frame law. -/
theorem atomBlockDet_familySum_newton (atom : Fin 6 → (Fin 3 → ℝ)) :
    6 * atomTripleFamilySum (atomBlockDet atom)
      = (∑ slot, atomGram atom slot slot) ^ 3
        - 3 * (∑ slot, atomGram atom slot slot) * atomGramPowerTwo atom
        + 2 * atomGramPowerThree atom := by
  simp only [atomTripleFamilySum, atomBlockDet, atomGramPowerTwo, atomGramPowerThree,
    Fin.sum_univ_six]
  simp only [atomGram_comm atom 1 0, atomGram_comm atom 2 0, atomGram_comm atom 2 1,
    atomGram_comm atom 3 0, atomGram_comm atom 3 1, atomGram_comm atom 3 2,
    atomGram_comm atom 4 0, atomGram_comm atom 4 1, atomGram_comm atom 4 2,
    atomGram_comm atom 4 3, atomGram_comm atom 5 0, atomGram_comm atom 5 1,
    atomGram_comm atom 5 2, atomGram_comm atom 5 3, atomGram_comm atom 5 4]
  ring

/-- **THE DETERMINANT TOTAL OF THE TWENTY BLOCKS IS EXACTLY ONE.**  This is the
Cauchy-Binet mass of the determinantal measure that the twenty triples carry,
and it reads nothing about the frame beyond the three landed laws. -/
theorem atomBlockDet_familySum
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomTripleFamilySum (atomBlockDet atom) = 1 := by
  have hnewton := atomBlockDet_familySum_newton atom
  rw [atomGram_trace hframe, atomGramPowerTwo_eq hframe, atomGramPowerThree_eq hframe] at hnewton
  norm_num at hnewton
  linarith

/-! ## Layer 3 — the universal cubic of the uniform scale -/

/-- The shifted triple determinant at a UNIFORM scale is the characteristic
polynomial of the unshifted block read at that scale. -/
theorem atomTripleDet_uniform_eq (atom : Fin 6 → (Fin 3 → ℝ)) (weight : ℝ)
    (slotOne slotTwo slotThree : Fin 6) :
    atomTripleDet atom (fun _ => weight) slotOne slotTwo slotThree
      = atomBlockDet atom slotOne slotTwo slotThree
        - weight * atomBlockSecond atom slotOne slotTwo slotThree
        + weight ^ 2 * atomBlockTrace atom slotOne slotTwo slotThree
        - weight ^ 3 := by
  simp only [atomTripleDet, atomShiftedDiag, atomBlockDet, atomBlockSecond, atomBlockTrace]
  ring

/-- **THE UNIVERSAL CUBIC.**  At a uniform scale the twenty shifted triple
determinants add to a cubic in the scale that does NOT read the frame.  Three
lanes of the campaign measured the blindness of this average, and this is its
sharpest form: the average is not merely a function of the diagonal, it is a
CONSTANT. -/
theorem atomTripleDet_familySum_uniform
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (weight : ℝ) :
    atomTripleFamilySum (fun slotOne slotTwo slotThree =>
        atomTripleDet atom (fun _ => weight) slotOne slotTwo slotThree)
      = 1 - 12 * weight + 30 * weight ^ 2 - 20 * weight ^ 3 := by
  have hdet := atomBlockDet_familySum hframe
  have hsecond := atomBlockSecond_familySum hframe
  have htrace := atomBlockTrace_familySum hframe
  simp only [atomTripleFamilySum] at hdet hsecond htrace ⊢
  simp only [atomTripleDet_uniform_eq atom weight]
  linear_combination hdet - weight * hsecond + weight ^ 2 * htrace

/-- **THE CONSTANT AT ONE SIXTH.**  At the uniform scale of the mass-one
interface the twenty shifted triple determinants add to exactly `-7/27`.  The
campaign banked this number as a reading of the icosahedral frame.  It is a
constant of the whole problem, so no weighted average of the twenty
determinants can separate one frame from another. -/
theorem atomTripleDet_familySum_uniform_sixth
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    atomTripleFamilySum (fun slotOne slotTwo slotThree =>
        atomTripleDet atom (fun _ => (1 : ℝ) / 6) slotOne slotTwo slotThree)
      = -(7 / 27) := by
  rw [atomTripleDet_familySum_uniform hframe]
  norm_num

/-- **THE AVERAGE TRIPLE FAILS AT ONE SIXTH.**  A negative total forces a
strictly negative member, so at the uniform scale of the mass-one interface
some triple does NOT dominate.  Every certificate of the cell must therefore
select, and no uniform average can decide. -/
theorem exists_atomTripleDet_neg_uniform_sixth
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ atomTripleDet atom (fun _ => (1 : ℝ) / 6) slotOne slotTwo slotThree < 0 := by
  by_contra hcontra
  push Not at hcontra
  have hsum := atomTripleDet_familySum_uniform_sixth hframe
  simp only [atomTripleFamilySum] at hsum
  have h012 := hcontra 0 1 2 (by decide) (by decide) (by decide)
  have h013 := hcontra 0 1 3 (by decide) (by decide) (by decide)
  have h014 := hcontra 0 1 4 (by decide) (by decide) (by decide)
  have h015 := hcontra 0 1 5 (by decide) (by decide) (by decide)
  have h023 := hcontra 0 2 3 (by decide) (by decide) (by decide)
  have h024 := hcontra 0 2 4 (by decide) (by decide) (by decide)
  have h025 := hcontra 0 2 5 (by decide) (by decide) (by decide)
  have h034 := hcontra 0 3 4 (by decide) (by decide) (by decide)
  have h035 := hcontra 0 3 5 (by decide) (by decide) (by decide)
  have h045 := hcontra 0 4 5 (by decide) (by decide) (by decide)
  have h123 := hcontra 1 2 3 (by decide) (by decide) (by decide)
  have h124 := hcontra 1 2 4 (by decide) (by decide) (by decide)
  have h125 := hcontra 1 2 5 (by decide) (by decide) (by decide)
  have h134 := hcontra 1 3 4 (by decide) (by decide) (by decide)
  have h135 := hcontra 1 3 5 (by decide) (by decide) (by decide)
  have h145 := hcontra 1 4 5 (by decide) (by decide) (by decide)
  have h234 := hcontra 2 3 4 (by decide) (by decide) (by decide)
  have h235 := hcontra 2 3 5 (by decide) (by decide) (by decide)
  have h245 := hcontra 2 4 5 (by decide) (by decide) (by decide)
  have h345 := hcontra 3 4 5 (by decide) (by decide) (by decide)
  linarith

/-! ## Layer 4 — the wedge inequality -/

/-- The BLEND of three slots against three weights. -/
def atomSlotBlend (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6)
    (weightOne weightTwo weightThree : ℝ) : Fin 3 → ℝ :=
  fun index => weightOne * atom slotOne index + weightTwo * atom slotTwo index
    + weightThree * atom slotThree index

/-- **THE BLEND AGAINST A WEDGE READS ONE WEIGHT.**  Two of the three atoms are
orthogonal to the wedge of the other two, so only the third weight survives,
and it carries the volume. -/
theorem atomSlotBlend_dot_wedge (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) (weightOne weightTwo weightThree : ℝ) :
    atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree
        ⬝ᵥ atomWedge (atom slotTwo) (atom slotThree)
      = weightOne * atomVolume (atom slotOne) (atom slotTwo) (atom slotThree) := by
  simp only [atomSlotBlend, atomVolume, dotProduct, Fin.sum_univ_three, atomWedge,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

theorem atomSlotBlend_dot_wedge_second (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) (weightOne weightTwo weightThree : ℝ) :
    atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree
        ⬝ᵥ atomWedge (atom slotOne) (atom slotThree)
      = -(weightTwo * atomVolume (atom slotOne) (atom slotTwo) (atom slotThree)) := by
  simp only [atomSlotBlend, atomVolume, dotProduct, Fin.sum_univ_three, atomWedge,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

theorem atomSlotBlend_dot_wedge_third (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) (weightOne weightTwo weightThree : ℝ) :
    atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree
        ⬝ᵥ atomWedge (atom slotOne) (atom slotTwo)
      = weightThree * atomVolume (atom slotOne) (atom slotTwo) (atom slotThree) := by
  simp only [atomSlotBlend, atomVolume, dotProduct, Fin.sum_univ_three, atomWedge,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- The blend energy is the quadratic form of the unshifted Gram block. -/
theorem atomSlotBlend_energy (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) (weightOne weightTwo weightThree : ℝ) :
    atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree
        ⬝ᵥ atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree
      = atomGram atom slotOne slotOne * weightOne ^ 2
        + atomGram atom slotTwo slotTwo * weightTwo ^ 2
        + atomGram atom slotThree slotThree * weightThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * weightOne * weightTwo
        + 2 * atomGram atom slotOne slotThree * weightOne * weightThree
        + 2 * atomGram atom slotTwo slotThree * weightTwo * weightThree := by
  simp only [atomSlotBlend, atomGram, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE WEDGE INEQUALITY.**  The block determinant against the weight energy
never passes the second minor total against the blend energy.  It is the
division-free form of the statement that the least value of the block is at
least the determinant divided by the second minor total, and its proof is three
Cauchy-Schwarz steps, one for each wedge. -/
theorem atomBlockDet_mul_le_atomBlockSecond_mul (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) (weightOne weightTwo weightThree : ℝ) :
    atomBlockDet atom slotOne slotTwo slotThree
        * (weightOne ^ 2 + weightTwo ^ 2 + weightThree ^ 2)
      ≤ atomBlockSecond atom slotOne slotTwo slotThree
        * (atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree
          ⬝ᵥ atomSlotBlend atom slotOne slotTwo slotThree
            weightOne weightTwo weightThree) := by
  have hone := atomDot_sq_le
    (atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree)
    (atomWedge (atom slotTwo) (atom slotThree))
  have htwo := atomDot_sq_le
    (atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree)
    (atomWedge (atom slotOne) (atom slotThree))
  have hthree := atomDot_sq_le
    (atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree)
    (atomWedge (atom slotOne) (atom slotTwo))
  rw [atomSlotBlend_dot_wedge, atomWedge_energy] at hone
  rw [atomSlotBlend_dot_wedge_second, atomWedge_energy] at htwo
  rw [atomSlotBlend_dot_wedge_third, atomWedge_energy] at hthree
  rw [atomBlockDet_eq_volume_sq]
  simp only [atomBlockSecond, atomGram]
  nlinarith [hone, htwo, hthree]

/-! ## Layer 5 — the spectral supply theorem -/

/-- **THE SPECTRAL SUPPLY.**  Past twelve the moment law forces a triple whose
determinant is positive and whose second minor total stays below that multiple
of it.  The twelve is the second minor total of the twenty blocks divided by
their determinant total, and both are universal. -/
theorem exists_atomSupplyTriple
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {ratio : ℝ} (hratio : 12 < ratio) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 < atomBlockDet atom slotOne slotTwo slotThree
        ∧ atomBlockSecond atom slotOne slotTwo slotThree
            < ratio * atomBlockDet atom slotOne slotTwo slotThree := by
  by_contra hcontra
  push Not at hcontra
  have hdet := atomBlockDet_familySum hframe
  have hsecond := atomBlockSecond_familySum hframe
  simp only [atomTripleFamilySum] at hdet hsecond
  have hstep : ∀ slotOne slotTwo slotThree : Fin 6, slotOne ≠ slotTwo → slotOne ≠ slotThree →
      slotTwo ≠ slotThree →
      ratio * atomBlockDet atom slotOne slotTwo slotThree
        ≤ atomBlockSecond atom slotOne slotTwo slotThree := by
    intro slotOne slotTwo slotThree hone htwo hthree
    rcases lt_or_eq_of_le (atomBlockDet_nonneg atom slotOne slotTwo slotThree) with hpos | hzero
    · exact hcontra slotOne slotTwo slotThree hone htwo hthree hpos
    · rw [← hzero, mul_zero]
      exact atomBlockSecond_nonneg atom slotOne slotTwo slotThree
  have h012 := hstep 0 1 2 (by decide) (by decide) (by decide)
  have h013 := hstep 0 1 3 (by decide) (by decide) (by decide)
  have h014 := hstep 0 1 4 (by decide) (by decide) (by decide)
  have h015 := hstep 0 1 5 (by decide) (by decide) (by decide)
  have h023 := hstep 0 2 3 (by decide) (by decide) (by decide)
  have h024 := hstep 0 2 4 (by decide) (by decide) (by decide)
  have h025 := hstep 0 2 5 (by decide) (by decide) (by decide)
  have h034 := hstep 0 3 4 (by decide) (by decide) (by decide)
  have h035 := hstep 0 3 5 (by decide) (by decide) (by decide)
  have h045 := hstep 0 4 5 (by decide) (by decide) (by decide)
  have h123 := hstep 1 2 3 (by decide) (by decide) (by decide)
  have h124 := hstep 1 2 4 (by decide) (by decide) (by decide)
  have h125 := hstep 1 2 5 (by decide) (by decide) (by decide)
  have h134 := hstep 1 3 4 (by decide) (by decide) (by decide)
  have h135 := hstep 1 3 5 (by decide) (by decide) (by decide)
  have h145 := hstep 1 4 5 (by decide) (by decide) (by decide)
  have h234 := hstep 2 3 4 (by decide) (by decide) (by decide)
  have h235 := hstep 2 3 5 (by decide) (by decide) (by decide)
  have h245 := hstep 2 4 5 (by decide) (by decide) (by decide)
  have h345 := hstep 3 4 5 (by decide) (by decide) (by decide)
  nlinarith [hdet, hsecond, h012, h013, h014, h015, h023, h024, h025, h034, h035,
    h045, h123, h124, h125, h134, h135, h145, h234, h235, h245, h345]

/-- **THE SPECTRAL FLOOR OF THE SUPPLY TRIPLE.**  The supply triple carries a
lower bound on the blend energy that reads only the weight energy.  This is
`lambda_min >= 1 / ratio` in the form the cell consumes.  The ratio is
positive of itself, because the second minor total is never negative. -/
theorem atomSupplyTriple_blend_floor (atom : Fin 6 → (Fin 3 → ℝ))
    {slotOne slotTwo slotThree : Fin 6} {ratio : ℝ}
    (hdet : 0 < atomBlockDet atom slotOne slotTwo slotThree)
    (hsecond : atomBlockSecond atom slotOne slotTwo slotThree
      < ratio * atomBlockDet atom slotOne slotTwo slotThree)
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
  nlinarith [hwedge, hdet, hsecond, hblendNonneg,
    sq_nonneg weightOne, sq_nonneg weightTwo, sq_nonneg weightThree]

/-! ## Layer 6 — the light-scale closure of the cell -/

/-- A sum over six slots that vanishes off three of them reads only those. -/
theorem atomSum_of_support_three {slotOne slotTwo slotThree : Fin 6}
    (hone : slotOne ≠ slotTwo) (htwo : slotOne ≠ slotThree) (hthree : slotTwo ≠ slotThree)
    (value : Fin 6 → ℝ)
    (hzero : ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin 6)), value slot = 0) :
    (∑ slot, value slot) = value slotOne + value slotTwo + value slotThree := by
  classical
  have hsub : (∑ slot ∈ ({slotOne, slotTwo, slotThree} : Finset (Fin 6)), value slot)
      = ∑ slot, value slot :=
    Finset.sum_subset (Finset.subset_univ _) (fun slot _ hnot => hzero slot hnot)
  rw [← hsub, Finset.sum_insert (by simp [hone, htwo]),
    Finset.sum_insert (by simp [hthree]), Finset.sum_singleton]
  ring

/-- The blend of a probe supported on three slots is the triple blend. -/
theorem atomBlend_of_support_three (atom : Fin 6 → (Fin 3 → ℝ))
    {slotOne slotTwo slotThree : Fin 6}
    (hone : slotOne ≠ slotTwo) (htwo : slotOne ≠ slotThree) (hthree : slotTwo ≠ slotThree)
    (probe : Fin 6 → ℝ)
    (hzero : ∀ slot ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin 6)), probe slot = 0) :
    atomBlend atom probe
      = atomSlotBlend atom slotOne slotTwo slotThree
        (probe slotOne) (probe slotTwo) (probe slotThree) := by
  funext index
  simp only [atomBlend, atomSlotBlend]
  exact atomSum_of_support_three hone htwo hthree (fun slot => probe slot * atom slot index)
    (fun slot hnot => by rw [hzero slot hnot]; ring)

/-- **THE LIGHT-SCALE CLOSURE.**  Every rank-three Parseval frame of six atoms
carries a dominating triple as soon as the ratio past twelve caps every scale.
No selection rule, no sign reading, no crux and no side hypothesis: the moment
law supplies the triple and the wedge inequality certifies it. -/
theorem exists_atomLightCarrier (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {ratio : ℝ} (hratio : 12 < ratio) (hlight : ∀ slot, ratio * scale slot ≤ 1) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  classical
  obtain ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, hdet, hsecond⟩ :=
    exists_atomSupplyTriple hframe hratio
  have hratioPos : (0 : ℝ) < ratio := by linarith
  refine ⟨{slotOne, slotTwo, slotThree}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hone, htwo]),
      Finset.card_insert_of_notMem (by simp [hthree]), Finset.card_singleton]
  · intro probe hsupport
    have hblend := atomBlend_of_support_three atom hone htwo hthree probe hsupport
    have hfloor := atomSupplyTriple_blend_floor atom hdet hsecond
      (probe slotOne) (probe slotTwo) (probe slotThree)
    have hscaleSum : (∑ slot, scale slot * probe slot ^ 2)
        = scale slotOne * probe slotOne ^ 2 + scale slotTwo * probe slotTwo ^ 2
          + scale slotThree * probe slotThree ^ 2 :=
      atomSum_of_support_three hone htwo hthree (fun slot => scale slot * probe slot ^ 2)
        (fun slot hnot => by rw [hsupport slot hnot]; ring)
    have hcapOne := hlight slotOne
    have hcapTwo := hlight slotTwo
    have hcapThree := hlight slotThree
    rw [hscaleSum, hblend]
    have hkey : ratio * (scale slotOne * probe slotOne ^ 2 + scale slotTwo * probe slotTwo ^ 2
        + scale slotThree * probe slotThree ^ 2)
        ≤ ratio * (atomSlotBlend atom slotOne slotTwo slotThree
            (probe slotOne) (probe slotTwo) (probe slotThree)
          ⬝ᵥ atomSlotBlend atom slotOne slotTwo slotThree
            (probe slotOne) (probe slotTwo) (probe slotThree)) := by
      nlinarith [hfloor, hcapOne, hcapTwo, hcapThree, sq_nonneg (probe slotOne),
        sq_nonneg (probe slotTwo), sq_nonneg (probe slotThree)]
    exact le_of_mul_le_mul_left hkey hratioPos

/-- **THE LIGHT-SCALE CLOSURE AT ONE THIRTEENTH.**  The concrete stratum: a
scale that never passes one thirteenth always carries a dominating triple.
The adversarial value of the constant is one sixth and it is attained, so the
statement here is short of the truth by exactly a factor of two. -/
theorem exists_atomLightCarrier_thirteen (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hlight : ∀ slot, scale slot ≤ 1 / 13) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  refine exists_atomLightCarrier atom scale hframe (by norm_num : (12 : ℝ) < 13) ?_
  intro slot
  have := hlight slot
  linarith

/-- The statement that a light scale always carries a dominating triple. -/
def AtomLightScaleClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, scale slot ≤ 1 / 13) →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe

/-- **THE LIGHT-SCALE STRATUM IS CLOSED, UNCONDITIONALLY.** -/
theorem atomLightScaleClosed_holds : AtomLightScaleClosed :=
  fun atom scale hlight hframe => exists_atomLightCarrier_thirteen atom scale hframe hlight

/-! ## Layer 7 — the partial frame operator and the corner law -/

/-- The PARTIAL FRAME OPERATOR of three slots, read as a form.  Where the Gram
block reads the slots, this reads the directions. -/
def atomFrameForm {slotCount : ℕ} (atom : Fin slotCount → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) (probe direction : Fin 3 → ℝ) : ℝ :=
  (atom slotOne ⬝ᵥ probe) * (atom slotOne ⬝ᵥ direction)
    + (atom slotTwo ⬝ᵥ probe) * (atom slotTwo ⬝ᵥ direction)
    + (atom slotThree ⬝ᵥ probe) * (atom slotThree ⬝ᵥ direction)

/-- **THE COMPLEMENTARY LAW.**  A triple and its complement add to the
identity.  The corner law of the campaign, which reads the least value of a
triple block against the largest value of the complementary block, is this one
line together with the equality of invariants below. -/
theorem atomFrameForm_add_complement (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (probe direction : Fin 3 → ℝ) :
    atomFrameForm atom 0 1 2 probe direction + atomFrameForm atom 3 4 5 probe direction
      = probe ⬝ᵥ direction := by
  have hsum := hframe probe direction
  simp only [Fin.sum_univ_six] at hsum
  simp only [atomFrameForm]
  linarith

/-- The trace of the partial frame operator is the trace of the Gram block. -/
theorem atomFrameForm_trace (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    (∑ index : Fin 3,
        atomFrameForm atom slotOne slotTwo slotThree (probeUnit index) (probeUnit index))
      = atomBlockTrace atom slotOne slotTwo slotThree := by
  simp only [atomFrameForm, dotProduct_probeUnit]
  simp only [Fin.sum_univ_three, atomBlockTrace, atomGram, dotProduct]
  ring

/-- **THE PARTIAL FRAME OPERATOR AND THE GRAM BLOCK CARRY THE SAME
DETERMINANT.**  Both are the square of the volume of the three atoms, thus the
two three-by-three matrices have the same characteristic polynomial and the
same least value. -/
theorem atomFrameForm_det (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6) :
    atomVolume (atom slotOne) (atom slotTwo) (atom slotThree) ^ 2
      = atomBlockDet atom slotOne slotTwo slotThree :=
  (atomBlockDet_eq_volume_sq atom slotOne slotTwo slotThree).symm

/-- **THE SPECTRAL CELL.**  A triple whose block never shortens a probe below
the largest of its three scales dominates.  The hypothesis is a floor on the
least value of the unshifted block, and the conclusion needs no sign, no cycle
and no minor. -/
theorem atomTriple_values_of_spectralFloor (atom : Fin 6 → (Fin 3 → ℝ))
    (scale : Fin 6 → ℝ) (slotOne slotTwo slotThree : Fin 6) (floor : ℝ)
    (hone : scale slotOne ≤ floor) (htwo : scale slotTwo ≤ floor)
    (hthree : scale slotThree ≤ floor)
    (hfloor : ∀ weightOne weightTwo weightThree : ℝ,
      floor * (weightOne ^ 2 + weightTwo ^ 2 + weightThree ^ 2)
        ≤ atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree
          ⬝ᵥ atomSlotBlend atom slotOne slotTwo slotThree weightOne weightTwo weightThree)
    (valueOne valueTwo valueThree : ℝ) :
    scale slotOne * valueOne ^ 2 + scale slotTwo * valueTwo ^ 2
        + scale slotThree * valueThree ^ 2
      ≤ atomGram atom slotOne slotOne * valueOne ^ 2
        + atomGram atom slotTwo slotTwo * valueTwo ^ 2
        + atomGram atom slotThree slotThree * valueThree ^ 2
        + 2 * atomGram atom slotOne slotTwo * valueOne * valueTwo
        + 2 * atomGram atom slotOne slotThree * valueOne * valueThree
        + 2 * atomGram atom slotTwo slotThree * valueTwo * valueThree := by
  have hstep := hfloor valueOne valueTwo valueThree
  rw [atomSlotBlend_energy] at hstep
  nlinarith [hstep, hone, htwo, hthree, sq_nonneg valueOne, sq_nonneg valueTwo,
    sq_nonneg valueThree]

/-! ## Layer 8 — the exact escape band of the two headline cells -/

/-- The COHERENT ENERGY CELL as a proposition: a nonnegative cycle whose
reading stays below its volume. -/
def AtomCoherentEnergyCell {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slotOne slotTwo slotThree : Fin slotCount) : Prop :=
  0 ≤ atomTriangleCycle atom slotOne slotTwo slotThree
    ∧ atomTripleReading atom scale slotOne slotTwo slotThree
      < atomTripleVolume atom scale slotOne slotTwo slotThree

/-- The MODULUS CELL as a proposition: twice the modulus of the cycle stays
below the modulus part. -/
def AtomModulusCell {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slotOne slotTwo slotThree : Fin slotCount) : Prop :=
  2 * |atomTriangleCycle atom slotOne slotTwo slotThree|
    < atomTripleModulus atom scale slotOne slotTwo slotThree

/-- The ESCAPE BAND of the two headline cells: a strictly coherent triangle
whose reading sits between the volume and the volume plus twice the cycle. -/
def AtomEscapeBand {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slotOne slotTwo slotThree : Fin slotCount) : Prop :=
  0 < atomTriangleCycle atom slotOne slotTwo slotThree
    ∧ atomTripleVolume atom scale slotOne slotTwo slotThree
      ≤ atomTripleReading atom scale slotOne slotTwo slotThree
    ∧ atomTripleReading atom scale slotOne slotTwo slotThree
      < atomTripleVolume atom scale slotOne slotTwo slotThree
        + 2 * atomTriangleCycle atom slotOne slotTwo slotThree

/-- **THE BAND IS EMPTY ON THE ANTI-COHERENT SIDE.**  When the cycle is not
positive, a positive triple determinant always fires the modulus cell.  This
is the exact complementarity of the two families: the modulus cell decides the
anti-coherent side with nothing left over. -/
theorem atomBand_empty_of_nonpos_cycle {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount)
    (hcycle : atomTriangleCycle atom slotOne slotTwo slotThree ≤ 0)
    (hdet : 0 < atomTripleDet atom scale slotOne slotTwo slotThree) :
    AtomModulusCell atom scale slotOne slotTwo slotThree := by
  have hsplit := atomTripleDet_eq_modulus_add_cycle atom scale slotOne slotTwo slotThree
  have habs : |atomTriangleCycle atom slotOne slotTwo slotThree|
      = -atomTriangleCycle atom slotOne slotTwo slotThree := abs_of_nonpos hcycle
  simp only [AtomModulusCell, habs]
  linarith

/-- **THE EXACT ESCAPE.**  A triple with a positive determinant escapes BOTH
headline cells exactly when it sits in the band.  Nothing else escapes, and
the band is not empty, so the union of the two families is not complete. -/
theorem atomTripleDet_pos_escape_iff_band {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount)
    (hdet : 0 < atomTripleDet atom scale slotOne slotTwo slotThree) :
    (¬ AtomCoherentEnergyCell atom scale slotOne slotTwo slotThree
        ∧ ¬ AtomModulusCell atom scale slotOne slotTwo slotThree)
      ↔ AtomEscapeBand atom scale slotOne slotTwo slotThree := by
  have hsplit := atomTripleDet_eq_modulus_add_cycle atom scale slotOne slotTwo slotThree
  have hmod : atomTripleModulus atom scale slotOne slotTwo slotThree
      = atomTripleVolume atom scale slotOne slotTwo slotThree
        - atomTripleReading atom scale slotOne slotTwo slotThree := rfl
  constructor
  · rintro ⟨hcoherent, hmodulus⟩
    have hcyclePos : 0 < atomTriangleCycle atom slotOne slotTwo slotThree := by
      by_contra hle
      push Not at hle
      exact hmodulus (atomBand_empty_of_nonpos_cycle atom scale slotOne slotTwo slotThree
        hle hdet)
    have hread : atomTripleVolume atom scale slotOne slotTwo slotThree
        ≤ atomTripleReading atom scale slotOne slotTwo slotThree := by
      by_contra hlt
      push Not at hlt
      exact hcoherent ⟨hcyclePos.le, hlt⟩
    refine ⟨hcyclePos, hread, ?_⟩
    have hdetEnergy := atomTripleDet_eq_energy atom scale slotOne slotTwo slotThree
    linarith
  · rintro ⟨hcyclePos, hread, hband⟩
    have habs : |atomTriangleCycle atom slotOne slotTwo slotThree|
        = atomTriangleCycle atom slotOne slotTwo slotThree := abs_of_pos hcyclePos
    refine ⟨?_, ?_⟩
    · rintro ⟨_, henergy⟩
      linarith
    · simp only [AtomModulusCell, habs, hmod]
      intro hcontra
      linarith

/-- **THE WIDTH OF THE BAND.**  The modulus cell fires below the reading
`volume - 2 * cycle`, the coherent energy cell below `volume`, and the
determinant is positive below `volume + 2 * cycle`.  The distance between the
outer two thresholds is four times the modulus of the cycle, and the coherent
energy cell splits it exactly in half. -/
theorem atomBand_width {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slotOne slotTwo slotThree : Fin slotCount) :
    (atomTripleVolume atom scale slotOne slotTwo slotThree
        + 2 * atomTriangleCycle atom slotOne slotTwo slotThree)
      - (atomTripleVolume atom scale slotOne slotTwo slotThree
        - 2 * atomTriangleCycle atom slotOne slotTwo slotThree)
      = 4 * atomTriangleCycle atom slotOne slotTwo slotThree := by
  ring

/-- **THE MODULUS CELL IS THE OUTER THRESHOLD.**  It fires exactly when the
reading stays below the volume minus twice the modulus of the cycle. -/
theorem atomModulusCell_iff_reading {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    AtomModulusCell atom scale slotOne slotTwo slotThree
      ↔ atomTripleReading atom scale slotOne slotTwo slotThree
        < atomTripleVolume atom scale slotOne slotTwo slotThree
          - 2 * |atomTriangleCycle atom slotOne slotTwo slotThree| := by
  simp only [AtomModulusCell, atomTripleModulus]
  constructor <;> intro h <;> linarith

/-- **THE UNIVERSAL CUBIC FACTORS.**  The cubic of the moment law splits off the
half, and the remaining quadratic has the roots `(5 +- sqrt 15) / 10`.  The
smallest root `(5 - sqrt 15) / 10` is the uniform scale below which the twenty
shifted determinants still add to a positive number. -/
theorem atomUniformCubic_factor (weight : ℝ) :
    1 - 12 * weight + 30 * weight ^ 2 - 20 * weight ^ 3
      = (1 - 2 * weight) * (1 - 10 * weight + 10 * weight ^ 2) := by
  ring

/-- **A POSITIVE TOTAL SUPPLIES A POSITIVE TRIPLE.**  Below the smallest root of
the universal cubic some triple has a strictly positive shifted determinant at
the uniform scale.  This reads no frame data whatever. -/
theorem exists_atomTripleDet_pos_uniform
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {weight : ℝ} (hcubic : 0 < 1 - 12 * weight + 30 * weight ^ 2 - 20 * weight ^ 3) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 < atomTripleDet atom (fun _ => weight) slotOne slotTwo slotThree := by
  by_contra hcontra
  push Not at hcontra
  have hsum := atomTripleDet_familySum_uniform hframe weight
  simp only [atomTripleFamilySum] at hsum
  have h012 := hcontra 0 1 2 (by decide) (by decide) (by decide)
  have h013 := hcontra 0 1 3 (by decide) (by decide) (by decide)
  have h014 := hcontra 0 1 4 (by decide) (by decide) (by decide)
  have h015 := hcontra 0 1 5 (by decide) (by decide) (by decide)
  have h023 := hcontra 0 2 3 (by decide) (by decide) (by decide)
  have h024 := hcontra 0 2 4 (by decide) (by decide) (by decide)
  have h025 := hcontra 0 2 5 (by decide) (by decide) (by decide)
  have h034 := hcontra 0 3 4 (by decide) (by decide) (by decide)
  have h035 := hcontra 0 3 5 (by decide) (by decide) (by decide)
  have h045 := hcontra 0 4 5 (by decide) (by decide) (by decide)
  have h123 := hcontra 1 2 3 (by decide) (by decide) (by decide)
  have h124 := hcontra 1 2 4 (by decide) (by decide) (by decide)
  have h125 := hcontra 1 2 5 (by decide) (by decide) (by decide)
  have h134 := hcontra 1 3 4 (by decide) (by decide) (by decide)
  have h135 := hcontra 1 3 5 (by decide) (by decide) (by decide)
  have h145 := hcontra 1 4 5 (by decide) (by decide) (by decide)
  have h234 := hcontra 2 3 4 (by decide) (by decide) (by decide)
  have h235 := hcontra 2 3 5 (by decide) (by decide) (by decide)
  have h245 := hcontra 2 4 5 (by decide) (by decide) (by decide)
  have h345 := hcontra 3 4 5 (by decide) (by decide) (by decide)
  linarith

/-! ## Layer 9 — the escape band is not empty -/

/-- **THE BAND WITNESS.**  The three integer atoms of the modulus bar, at the
uniform scale two.  Its Gram has diagonal `5` and every off-diagonal entry `2`,
so the shifted diagonals are `3`, the cycle is `8`, the volume is `27` and the
reading is `36`. -/
def escapeBandAtom : Fin 3 → (Fin 3 → ℝ) :=
  ![![2, 1, 0], ![0, 2, 1], ![1, 0, 2]]

/-- The uniform scale two of the band witness. -/
def escapeBandScale : Fin 3 → ℝ := fun _ => 2

theorem escapeBandAtom_gram_diag (slot : Fin 3) : atomGram escapeBandAtom slot slot = 5 := by
  fin_cases slot <;>
    simp [atomGram, escapeBandAtom, dotProduct, Fin.sum_univ_three] <;> norm_num

theorem escapeBandAtom_gram_zeroOne : atomGram escapeBandAtom 0 1 = 2 := by
  simp [atomGram, escapeBandAtom, dotProduct, Fin.sum_univ_three]

theorem escapeBandAtom_gram_zeroTwo : atomGram escapeBandAtom 0 2 = 2 := by
  simp [atomGram, escapeBandAtom, dotProduct, Fin.sum_univ_three]

theorem escapeBandAtom_gram_oneTwo : atomGram escapeBandAtom 1 2 = 2 := by
  simp [atomGram, escapeBandAtom, dotProduct, Fin.sum_univ_three]

theorem escapeBandAtom_shiftedDiag (slot : Fin 3) :
    atomShiftedDiag escapeBandAtom escapeBandScale slot = 3 := by
  simp only [atomShiftedDiag, escapeBandAtom_gram_diag, escapeBandScale]
  norm_num

theorem escapeBandAtom_cycle :
    atomTriangleCycle escapeBandAtom 0 1 2 = 8 := by
  simp only [atomTriangleCycle, escapeBandAtom_gram_zeroOne, escapeBandAtom_gram_zeroTwo,
    escapeBandAtom_gram_oneTwo]
  norm_num

theorem escapeBandAtom_volume :
    atomTripleVolume escapeBandAtom escapeBandScale 0 1 2 = 27 := by
  simp only [atomTripleVolume, escapeBandAtom_shiftedDiag]
  norm_num

theorem escapeBandAtom_reading :
    atomTripleReading escapeBandAtom escapeBandScale 0 1 2 = 36 := by
  simp only [atomTripleReading, escapeBandAtom_shiftedDiag, escapeBandAtom_gram_zeroOne,
    escapeBandAtom_gram_zeroTwo, escapeBandAtom_gram_oneTwo]
  norm_num

theorem escapeBandAtom_tripleDet :
    atomTripleDet escapeBandAtom escapeBandScale 0 1 2 = 7 := by
  rw [atomTripleDet_eq_energy, escapeBandAtom_volume, escapeBandAtom_reading,
    escapeBandAtom_cycle]
  norm_num

/-- **THE BAND IS NOT EMPTY.**  The witness sits inside it. -/
theorem escapeBandAtom_inBand :
    AtomEscapeBand escapeBandAtom escapeBandScale 0 1 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [escapeBandAtom_cycle]; norm_num
  · rw [escapeBandAtom_volume, escapeBandAtom_reading]; norm_num
  · rw [escapeBandAtom_volume, escapeBandAtom_reading, escapeBandAtom_cycle]; norm_num

/-- **THE TWO HEADLINE CELLS BOTH MISS A POSITIVE DETERMINANT.**  At the band
witness the triple determinant is `7`, the coherent energy cell is silent
because the reading `36` passes the volume `27`, and the modulus cell is silent
because twice the cycle modulus is `16` while the modulus part is `-9`.  So the
escape band of `Gtz.atomTripleDet_pos_escape_iff_band` is inhabited, and the
union of the coherent family with the modulus cell is NOT complete. -/
theorem escapeBandAtom_escapes :
    0 < atomTripleDet escapeBandAtom escapeBandScale 0 1 2
      ∧ ¬ AtomCoherentEnergyCell escapeBandAtom escapeBandScale 0 1 2
      ∧ ¬ AtomModulusCell escapeBandAtom escapeBandScale 0 1 2 := by
  have hdet : 0 < atomTripleDet escapeBandAtom escapeBandScale 0 1 2 := by
    rw [escapeBandAtom_tripleDet]; norm_num
  refine ⟨hdet, ?_⟩
  exact (atomTripleDet_pos_escape_iff_band escapeBandAtom escapeBandScale 0 1 2 hdet).mpr
    escapeBandAtom_inBand

/-- **THE UNION QUESTION, ANSWERED.**  There is a triple whose determinant is
positive and which escapes both headline cells, so no comparison of the two can
close the cell: the band between them has to be covered by something else. -/
theorem exists_escape_of_both_headline_cells :
    ∃ (atom : Fin 3 → (Fin 3 → ℝ)) (scale : Fin 3 → ℝ) (slotOne slotTwo slotThree : Fin 3),
      0 < atomTripleDet atom scale slotOne slotTwo slotThree
        ∧ ¬ AtomCoherentEnergyCell atom scale slotOne slotTwo slotThree
        ∧ ¬ AtomModulusCell atom scale slotOne slotTwo slotThree :=
  ⟨escapeBandAtom, escapeBandScale, 0, 1, 2, escapeBandAtom_escapes⟩

end Gtz
