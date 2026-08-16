/-
# The price of a gap determinant at every size and every rank

## The question this file answers

`Gtz.weightProduct_mul_det_gap_eq_selfReading_sub_complementVolume`
(Gtz/Wave/GapDeterminantSignComplement.lean:576) prices the gap determinant of a
triple of a `(6, 3)` design against ONE non-negative number, the volume of the
three labels the triple omits.  That law needs the omitted labels to be a triple
as well, so it needs `size = 2 * rank`.  The two off-path hinges live at
`2 * rank <= size` and at the threshold cell `size = rank * (rank + 1) / 2`, and
those cells are OFF that locus at every rank above three.

This file settles the transport.  The answer has three parts.

* The frame half transports with no change.  Only `|C| = rank` is used, never
  `|Cᶜ| = rank`.  The selected atoms carry `det (S_C - 1) = det (G_C - 1)` and
  `det (deficiency mass) = product of one-minus-weights times squared bracket`
  at every size and every rank (section 3).
* The COMPLEMENT half does NOT transport.  Above `size = 2 * rank` the omitted
  labels outnumber the rank, so their Gram is singular and the complement volume
  is IDENTICALLY ZERO (section 5).  It is not a different number there.  It
  carries no information at all.
* The right complement object at general size is the omitted labels' weighted
  mass `Gtz.baseResidual`, a `rank` by `rank` positive semidefinite MATRIX, and
  the price law becomes multiplicative rather than additive (section 4):

    `det (S_C - 1) = (product of one-minus-weights) * (bracket)^2
                       * det (1 - deficiencyMass⁻¹ * baseResidual)` .

## What is new here, against what the tree already holds

`Gtz.det_pickSum_eq_prod_weight_mul_det_sq` (Gtz/Design/ComplementFrame.lean:422)
is the same determinant law for the DESIGN weights, proved through square roots.
Section 1 proves it for an arbitrary real scale vector with no square root and no
positivity, which is what the deficiency scale `1 - t_c` needs.

`Gtz.subsetSum_sub_one_eq_freeMass_sub_boundMass`
(Gtz/Design/BalancedStratum.lean:225) is the additive split of the gap.  It is
CONSUMED here, not proved again.

`Gtz.det_mul_transpose_sub_one_comm` (Gtz/Quantitative/ChartHadamard.lean:822) is
the Sylvester flip at general dimension.  It is CONSUMED here.

## The new criterion, and what it costs

Section 6 reads the complement through Cauchy-Schwarz alone:

  `baseResidual D C  <=  (rank - share of C) * 1` .

So a card-`rank` subset whose deficiency mass beats the complement's TOTAL SHARE
dominates strictly.  That criterion asks for no deflation, no predecessor cell
and no leverage floor, which every other producer of the two hinges consumes.
Section 7 turns it into producers for both off-path obligations.

Section 8 records the price of the relaxation honestly.  At a tie the tight
direction turns the same two bounds into

  `share of C  <=  rank - 1 + largest weight in C` ,

a necessary condition on EVERY weakly dominating card-`rank` subset of a tie, at
every size and every rank.  At the threshold cell the best available share is
`2 * rank / (rank + 1)`, which is below `rank - 1` from rank three onward, so the
criterion does not close the cell and the report says so.

## MEASURED, 2026-08-16

A C probe with OpenMP at 200 threads, 39,000,000 label-and-subset pairs across
seven cells and three weight skews, with the whitened Parseval residual checked
below `1e-9` at every design.  The calibration anchor is the `(4,3)` tetrahedron
tie, at which neither criterion fires, as neither must.

* SOUNDNESS.  Zero pairs fired either criterion at a subset that is not
  positive definite.  Both theorems are consistent with every measured pair.
* THE MASS CRITERION OF SECTION 6 IS THE LIVE ONE.  Its per-design firing rate
  on the ALL-HEAVY stratum is `97%` at `(6,3)`, `96%` at `(8,4)`, `94%` at the
  rank-four threshold cell `(10,4)` and `78%` at the rank-five threshold cell
  `(15,5)`.  It is NOT total, so it does not close either obligation.
* THE CLOSED-FORM CRITERION OF SECTION 10 IS BADLY LOSSY.  The same rates fall
  to `61%`, `39%`, `23%` and `3%`.  The determinant-trace step is what costs
  them, and its cost grows with the rank.
* THE RESIDUAL IS NOT THE TIE BOUNDARY.  At `(15,5)` every one of the 490
  all-heavy designs the mass criterion missed has a subset dominating with least
  eigenvalue at least one.  So the miss set is not aligned with the campaign's
  own margin, and no refinement of the SELECTION inside this lane can close it.

Uniform sampling is not adversarial, so every rate above is an upper bound on
what an adversary would leave.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Design.ComplementFrame
import Gtz.Quantitative.ChartHadamard
import Gtz.Quantitative.SubsetDeterminantBound
import Gtz.Reduction.BranchTransferConstants
import Gtz.Wave.AllHeavyHingeSchur

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Finset Matrix

/-! ## 1. The scale-generic outer sum

A slot-indexed family of vectors in its own dimension gives a square matrix of
columns.  Scaling the slots by ARBITRARY reals and summing the outer products is
one matrix triple product, so the determinant is the scale product times the
squared column determinant.  No square root appears, and no scale is asked to be
positive. -/

section ScaleGeneric

variable {rank : ℕ}

/-- The square matrix whose COLUMNS are a slot-indexed family of vectors. -/
def slotColumns (vec : Fin rank → (Fin rank → ℝ)) : Matrix (Fin rank) (Fin rank) ℝ :=
  Matrix.of fun coordIndex slotIndex => vec slotIndex coordIndex

theorem slotColumns_apply (vec : Fin rank → (Fin rank → ℝ)) (coordIndex slotIndex : Fin rank) :
    slotColumns vec coordIndex slotIndex = vec slotIndex coordIndex := rfl

/-- **THE TRIPLE PRODUCT.**  Columns, a diagonal of scales, columns transposed. -/
theorem slotColumns_mul_diagonal_mul_transpose (vec : Fin rank → (Fin rank → ℝ))
    (scale : Fin rank → ℝ) :
    slotColumns vec * Matrix.diagonal scale * (slotColumns vec)ᵀ
      = ∑ slotIndex, scale slotIndex • atomMatrix (vec slotIndex) := by
  ext rowCoord colCoord
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, slotColumns_apply, Matrix.sum_apply,
    Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun slotIndex _ => by ring

/-- **THE SCALE-GENERIC DETERMINANT LAW.**  The scale product times the squared
column determinant, at arbitrary real scales.

This strictly generalizes `Gtz.det_pickSum_eq_prod_weight_mul_det_sq`, whose
scales are design weights and whose proof runs through `Real.sqrt`. -/
theorem det_scaledOuterSum (vec : Fin rank → (Fin rank → ℝ)) (scale : Fin rank → ℝ) :
    (∑ slotIndex, scale slotIndex • atomMatrix (vec slotIndex)).det
      = (∏ slotIndex, scale slotIndex) * (slotColumns vec).det ^ 2 := by
  rw [← slotColumns_mul_diagonal_mul_transpose, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-- The unscaled outer sum is the columns against their transpose. -/
theorem slotColumns_mul_transpose (vec : Fin rank → (Fin rank → ℝ)) :
    slotColumns vec * (slotColumns vec)ᵀ = ∑ slotIndex, atomMatrix (vec slotIndex) := by
  have hone := slotColumns_mul_diagonal_mul_transpose vec (fun _ => (1 : ℝ))
  rw [show (Matrix.diagonal (fun _ : Fin rank => (1 : ℝ))) = 1 from Matrix.diagonal_one,
    Matrix.mul_one] at hone
  rw [hone]
  exact Finset.sum_congr rfl fun slotIndex _ => one_smul _ _

/-- The Gram of a slot family: the pairings of the vectors, as a square matrix. -/
def slotGram (vec : Fin rank → (Fin rank → ℝ)) : Matrix (Fin rank) (Fin rank) ℝ :=
  (slotColumns vec)ᵀ * slotColumns vec

theorem slotGram_apply (vec : Fin rank → (Fin rank → ℝ)) (leftSlot rightSlot : Fin rank) :
    slotGram vec leftSlot rightSlot = vec leftSlot ⬝ᵥ vec rightSlot := by
  simp only [slotGram, Matrix.mul_apply, Matrix.transpose_apply, slotColumns_apply, dotProduct]

/-- The Gram determinant is the squared column determinant. -/
theorem det_slotGram (vec : Fin rank → (Fin rank → ℝ)) :
    (slotGram vec).det = (slotColumns vec).det ^ 2 := by
  rw [slotGram, Matrix.det_mul, Matrix.det_transpose, ← pow_two]

/-- **THE GAP DETERMINANT IS THE GRAM GAP DETERMINANT, AT EVERY RANK.**  The
`(6, 3)` bridge `Gtz.det_subsetSum_triple_sub_one_eq_det_tripleGram_sub_one` at
general rank, from the landed Sylvester flip.  The two shifted matrices have the
same dimension, so no sign correction survives. -/
theorem det_outerSum_sub_one_eq_det_slotGram_sub_one (vec : Fin rank → (Fin rank → ℝ)) :
    ((∑ slotIndex, atomMatrix (vec slotIndex)) - 1).det = (slotGram vec - 1).det := by
  rw [← slotColumns_mul_transpose, slotGram]
  exact det_mul_transpose_sub_one_comm (slotColumns vec)

end ScaleGeneric

/-! ## 2. The design instance of the slot family

A `pick` enumerates `rank` labels.  Its atoms are a slot family, its columns are
the landed `Gtz.atomColumnsOfPick`, and its unscaled outer sum is the subset sum
of the picked labels. -/

section PickedFamily

variable {size rank : ℕ}

/-- The atoms a pick selects, as a slot family. -/
def pickAtoms (design : WeightedDesign size rank) (pick : Fin rank → Fin size) :
    Fin rank → (Fin rank → ℝ) := fun slotIndex => design.atom (pick slotIndex)

theorem slotColumns_pickAtoms (design : WeightedDesign size rank) (pick : Fin rank → Fin size) :
    slotColumns (pickAtoms design pick) = atomColumnsOfPick design pick := rfl

/-- The image of an injective pick has exactly `rank` labels. -/
theorem card_image_pick (pick : Fin rank → Fin size) (hinjective : Function.Injective pick) :
    (Finset.image pick Finset.univ).card = rank := by
  classical
  rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]

/-- The subset sum over a pick's image is the unscaled outer sum of its atoms. -/
theorem subsetSum_image_pick (design : WeightedDesign size rank) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick) :
    subsetSum design (Finset.image pick Finset.univ)
      = ∑ slotIndex, atomMatrix (pickAtoms design pick slotIndex) := by
  classical
  rw [subsetSum, Finset.sum_image fun _ _ _ _ hequal => hinjective hequal]
  rfl

/-- The weighted mass over a pick's image, written on the slots. -/
theorem weightedSum_image_pick (design : WeightedDesign size rank) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick) :
    ∑ label ∈ Finset.image pick Finset.univ, design.weight label • atomMatrix (design.atom label)
      = ∑ slotIndex, design.weight (pick slotIndex)
          • atomMatrix (pickAtoms design pick slotIndex) := by
  classical
  rw [Finset.sum_image fun _ _ _ _ hequal => hinjective hequal]
  rfl

end PickedFamily

/-! ## 3. The deficiency mass and the additive price

The gap of a selection is the selected atoms' UNSPENT weight minus the omitted
atoms' spent weight.  The first term is the deficiency mass, whose determinant
section 1 reads in closed form.  The second term is the landed
`Gtz.baseResidual`. -/

section DeficiencyMass

variable {size rank : ℕ}

/-- **THE DEFICIENCY MASS OF A PICK.**  Each selected atom carries the part of
its own outer form that the design does NOT already spend on it. -/
def deficiencyMass (design : WeightedDesign size rank) (pick : Fin rank → Fin size) :
    Matrix (Fin rank) (Fin rank) ℝ :=
  ∑ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex))
    • atomMatrix (pickAtoms design pick slotIndex)

/-- **THE ADDITIVE PRICE, AT EVERY SIZE AND EVERY RANK.**  Restoring the omitted
labels' weighted mass to the gap leaves the deficiency mass.  Parseval alone. -/
theorem gap_add_baseResidual_eq_deficiencyMass (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick) :
    (subsetSum design (Finset.image pick Finset.univ) - 1)
        + baseResidual design (Finset.image pick Finset.univ)
      = deficiencyMass design pick := by
  classical
  have hsplit : ∑ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex))
        • atomMatrix (pickAtoms design pick slotIndex)
      = (∑ slotIndex, atomMatrix (pickAtoms design pick slotIndex))
        - ∑ slotIndex, design.weight (pick slotIndex)
            • atomMatrix (pickAtoms design pick slotIndex) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun slotIndex _ => by rw [sub_smul, one_smul]
  rw [baseResidual, subsetSum_image_pick design pick hinjective,
    weightedSum_image_pick design pick hinjective, deficiencyMass, hsplit]
  abel

/-- The gap is the deficiency mass minus the omitted labels' weighted mass. -/
theorem gap_eq_deficiencyMass_sub_baseResidual (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick) :
    subsetSum design (Finset.image pick Finset.univ) - 1
      = deficiencyMass design pick
        - baseResidual design (Finset.image pick Finset.univ) := by
  rw [← gap_add_baseResidual_eq_deficiencyMass design pick hinjective]
  abel

/-- **THE DEFICIENCY DETERMINANT IN CLOSED FORM.**  The product of the selected
one-minus-weights times the squared bracket of the selected atoms.  Section 1
supplies it at arbitrary scales, which is exactly what `1 - t_c` needs. -/
theorem det_deficiencyMass (design : WeightedDesign size rank) (pick : Fin rank → Fin size) :
    (deficiencyMass design pick).det
      = (∏ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex)))
        * (atomColumnsOfPick design pick).det ^ 2 := by
  rw [deficiencyMass, det_scaledOuterSum, slotColumns_pickAtoms]

/-- Every one-minus-weight of a design of size at least two is strictly positive. -/
theorem one_sub_weight_pos (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (label : Fin size) : (0 : ℝ) < 1 - design.weight label := by
  have hlt : design.weight label < 1 := weight_lt_one design hsize label
  linarith

/-- The one-minus-weight product of a pick is strictly positive. -/
theorem prod_one_sub_weight_pos (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick : Fin rank → Fin size) :
    (0 : ℝ) < ∏ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex)) :=
  Finset.prod_pos fun slotIndex _ => one_sub_weight_pos design hsize (pick slotIndex)

/-- **THE DEFICIENCY MASS IS POSITIVE SEMIDEFINITE.**  A non-negative combination
of outer forms. -/
theorem posSemidef_deficiencyMass (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick : Fin rank → Fin size) : (deficiencyMass design pick).PosSemidef := by
  rw [deficiencyMass]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ hleft hright => hleft.add hright)
    ?_ ?_
  · exact Matrix.PosSemidef.zero
  · exact fun slotIndex _ =>
      (posSemidef_atomMatrix _).smul (one_sub_weight_pos design hsize (pick slotIndex)).le

/-- **THE DEFICIENCY MASS IS POSITIVE DEFINITE EXACTLY ON A BASIS.** -/
theorem posDef_deficiencyMass_iff (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick : Fin rank → Fin size) :
    (deficiencyMass design pick).PosDef ↔ (atomColumnsOfPick design pick).det ≠ 0 := by
  rw [(posSemidef_deficiencyMass design hsize pick).posDef_iff_det_ne_zero,
    det_deficiencyMass]
  have hprodPos := prod_one_sub_weight_pos design hsize pick
  constructor
  · intro hdetNe hcolumnsZero
    exact hdetNe (by rw [hcolumnsZero]; ring)
  · intro hcolumnsNe hproductZero
    rcases mul_eq_zero.mp hproductZero with hscaleZero | hsquareZero
    · exact absurd hscaleZero (ne_of_gt hprodPos)
    · exact hcolumnsNe (sq_eq_zero_iff.mp hsquareZero)

/-- The quadratic form of the deficiency mass, in the design's own vocabulary. -/
theorem dotProduct_deficiencyMass_mulVec (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (probe : Fin rank → ℝ) :
    probe ⬝ᵥ (deficiencyMass design pick *ᵥ probe)
      = ∑ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex))
          * (design.atom (pick slotIndex) ⬝ᵥ probe) ^ 2 := by
  rw [deficiencyMass, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun slotIndex _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [atomMatrix, pickAtoms, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, sq,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end DeficiencyMass

/-! ## 4. The multiplicative price law

Determinants are not additive, so the additive split of section 3 does not price
the gap determinant by itself.  Factoring the deficiency mass out of the gap
does, and the complement then enters as ONE determinant of a `rank` by `rank`
matrix.  This is the general-size replacement for the `(6, 3)` two-scalar
reading. -/

section MultiplicativePrice

/-- Factoring an invertible matrix out of a difference. -/
theorem det_sub_eq_det_mul_det_one_sub_inv_mul {dimension : ℕ}
    (leftMat rightMat : Matrix (Fin dimension) (Fin dimension) ℝ) (hunit : IsUnit leftMat.det) :
    (leftMat - rightMat).det = leftMat.det * (1 - leftMat⁻¹ * rightMat).det := by
  have hfactor : leftMat * (1 - leftMat⁻¹ * rightMat) = leftMat - rightMat := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mul]
  rw [← hfactor, Matrix.det_mul]

variable {size rank : ℕ}

/-- **THE PRICE OF THE GAP DETERMINANT, AT EVERY SIZE AND EVERY RANK.**

The selected atoms contribute a manifestly non-negative factor, read entirely
inside the selection.  The omitted labels contribute ONE determinant, of the
deficiency mass inverted against the omitted labels' weighted mass.

At `size = 2 * rank` the second factor is the `(6, 3)` complement volume in
disguise.  Above that cell it is still a `rank` by `rank` determinant, while the
complement volume has collapsed to zero (section 5). -/
theorem det_gap_eq_deficiency_mul_complementFactor (design : WeightedDesign size rank)
    (hsize : 2 ≤ size) (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (hbracket : (atomColumnsOfPick design pick).det ≠ 0) :
    (subsetSum design (Finset.image pick Finset.univ) - 1).det
      = (∏ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex)))
        * (atomColumnsOfPick design pick).det ^ 2
        * (1 - (deficiencyMass design pick)⁻¹
            * baseResidual design (Finset.image pick Finset.univ)).det := by
  have hunit : IsUnit (deficiencyMass design pick).det := by
    rw [det_deficiencyMass]
    exact isUnit_iff_ne_zero.mpr (by
      have hprodPos := prod_one_sub_weight_pos design hsize pick
      have hsq : (0 : ℝ) < (atomColumnsOfPick design pick).det ^ 2 := by positivity
      positivity)
  rw [gap_eq_deficiencyMass_sub_baseResidual design pick hinjective,
    det_sub_eq_det_mul_det_one_sub_inv_mul _ _ hunit, det_deficiencyMass]

/-- **THE SIGN OF THE GAP DETERMINANT IS THE SIGN OF THE COMPLEMENT FACTOR.**
The selected atoms' factor is strictly positive on every basis, so nothing below
the complement determinant can change the sign. -/
theorem det_gap_pos_iff_complementFactor_pos (design : WeightedDesign size rank)
    (hsize : 2 ≤ size) (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (hbracket : (atomColumnsOfPick design pick).det ≠ 0) :
    0 < (subsetSum design (Finset.image pick Finset.univ) - 1).det
      ↔ 0 < (1 - (deficiencyMass design pick)⁻¹
          * baseResidual design (Finset.image pick Finset.univ)).det := by
  have hfactorPos : (0 : ℝ) < (∏ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex)))
      * (atomColumnsOfPick design pick).det ^ 2 := by
    have hprodPos := prod_one_sub_weight_pos design hsize pick
    have hsq : (0 : ℝ) < (atomColumnsOfPick design pick).det ^ 2 := by positivity
    positivity
  rw [det_gap_eq_deficiency_mul_complementFactor design hsize pick hinjective hbracket]
  exact mul_pos_iff_of_pos_left hfactorPos

end MultiplicativePrice

/-! ## 5. Why the `(6, 3)` complement volume does not transport

The complement volume of the `(6, 3)` law is a weight product times the Gram
determinant of the OMITTED labels.  Above `size = 2 * rank` the omitted labels
outnumber the rank, so their Gram is a singular matrix and that volume is
identically zero.  The obstruction is not that the number changes.  It is that
the number carries nothing. -/

section ComplementCollapse

/-- **A GRAM OF MORE VECTORS THAN THE DIMENSION IS SINGULAR.**  Pure linear
algebra, at every pair of dimensions. -/
theorem det_transpose_mul_self_eq_zero_of_lt {rowCount colCount : ℕ}
    (hlt : rowCount < colCount) (frameMat : Matrix (Fin rowCount) (Fin colCount) ℝ) :
    (frameMatᵀ * frameMat).det = 0 := by
  by_contra hne
  have hinjective : Function.Injective (Matrix.mulVecLin frameMat) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro probe hprobe
    have hzero : (frameMatᵀ * frameMat) *ᵥ probe = 0 := by
      rw [← Matrix.mulVec_mulVec]
      have hstep : frameMat *ᵥ probe = 0 := hprobe
      rw [hstep, Matrix.mulVec_zero]
    exact Matrix.eq_zero_of_mulVec_eq_zero hne hzero
  have hdim := LinearMap.finrank_le_finrank_of_injective hinjective
  simp only [Module.finrank_fin_fun] at hdim
  omega

variable {size rank : ℕ}

/-- The Gram of an arbitrary list of design labels, as a square matrix on the
list's own index. -/
def labelGram (design : WeightedDesign size rank) {listCount : ℕ}
    (list : Fin listCount → Fin size) : Matrix (Fin listCount) (Fin listCount) ℝ :=
  Matrix.of fun leftIndex rightIndex => design.atom (list leftIndex) ⬝ᵥ design.atom (list rightIndex)

/-- The label columns of a list, as a `rank` by `listCount` matrix. -/
def labelColumns (design : WeightedDesign size rank) {listCount : ℕ}
    (list : Fin listCount → Fin size) : Matrix (Fin rank) (Fin listCount) ℝ :=
  Matrix.of fun coordIndex listIndex => design.atom (list listIndex) coordIndex

theorem labelGram_eq_transpose_mul_self (design : WeightedDesign size rank) {listCount : ℕ}
    (list : Fin listCount → Fin size) :
    labelGram design list = (labelColumns design list)ᵀ * labelColumns design list := by
  ext leftIndex rightIndex
  simp only [labelGram, labelColumns, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    dotProduct]

/-- **THE COMPLEMENT VOLUME COLLAPSES ABOVE `size = 2 * rank`.**  As soon as the
omitted labels outnumber the rank their Gram determinant is zero, whatever the
design and whatever the labels.

So the `(6, 3)` law's complement term is not merely different at the threshold
cell.  It is identically zero from rank four onward, because the threshold cell
omits `rank * (rank - 1) / 2` labels and that exceeds `rank` there. -/
theorem det_labelGram_eq_zero_of_rank_lt (design : WeightedDesign size rank) {listCount : ℕ}
    (hlt : rank < listCount) (list : Fin listCount → Fin size) :
    (labelGram design list).det = 0 := by
  rw [labelGram_eq_transpose_mul_self]
  exact det_transpose_mul_self_eq_zero_of_lt hlt (labelColumns design list)

/-- The omitted-label count at the threshold cell exceeds the rank from rank four
onward, so the collapse above is not vacuous there. -/
theorem rank_lt_thresholdCell_complement_card {rankValue : ℕ} (hrank : 4 ≤ rankValue) :
    rankValue < rankValue * (rankValue + 1) / 2 - rankValue := by
  have hbig : 4 * rankValue < rankValue * (rankValue + 1) := by nlinarith
  have hdouble : 2 * (rankValue * (rankValue + 1) / 2) = rankValue * (rankValue + 1) := by
    rcases Nat.even_or_odd rankValue with ⟨half, hhalf⟩ | ⟨half, hhalf⟩
    · subst hhalf; ring_nf; omega
    · subst hhalf; ring_nf; omega
  generalize hprod : rankValue * (rankValue + 1) = prodValue at hbig hdouble ⊢
  omega

/-- The sub-threshold band's lower edge is exactly the locus where the omitted
labels are as many as the rank, so the `(6, 3)` reading survives only there. -/
theorem complement_card_eq_rank_iff_double {sizeValue rankValue : ℕ} (hle : rankValue ≤ sizeValue) :
    sizeValue - rankValue = rankValue ↔ sizeValue = 2 * rankValue := by omega

end ComplementCollapse

/-! ## 6. The complement share bound and a deflation-free criterion

The omitted labels' weighted mass is bounded by ONE scalar through
Cauchy-Schwarz: its total share.  So a selection whose deficiency mass beats that
scalar dominates strictly, and the criterion asks for no deflation, no
predecessor cell and no leverage floor. -/

section ShareCriterion

variable {size rank : ℕ}

/-- **THE COMPLEMENT MASS IS CAPPED BY ITS TOTAL SHARE.**  Termwise
Cauchy-Schwarz, at every size and every rank, with no positivity beyond the
weights. -/
theorem dotProduct_baseResidual_mulVec_le (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ) :
    probe ⬝ᵥ (baseResidual design selected *ᵥ probe)
      ≤ (∑ label ∈ selectedᶜ, atomShare design label) * (probe ⬝ᵥ probe) := by
  classical
  rw [baseResidual_eq_complementSum, Matrix.sum_mulVec, dotProduct_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun label _ => ?_
  have hform : probe ⬝ᵥ ((design.weight label • atomMatrix (design.atom label)) *ᵥ probe)
      = design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    congr 1
    simp only [atomMatrix, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, sq,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hcauchy : (design.atom label ⬝ᵥ probe) ^ 2
      ≤ leverageOf (design.atom label) * (probe ⬝ᵥ probe) := by
    have hraw := dotProduct_sq_le_mul (design.atom label) probe
    rwa [show design.atom label ⬝ᵥ design.atom label = leverageOf (design.atom label) from
      dotProduct_self_eq_sum_sq _] at hraw
  rw [hform, atomShare]
  nlinarith [hcauchy, (design.weight_pos label).le]

/-- The complement's total share is the rank minus the selection's share. -/
theorem sum_compl_atomShare_eq (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    ∑ label ∈ selectedᶜ, atomShare design label
      = (rank : ℝ) - ∑ label ∈ selected, atomShare design label := by
  classical
  have hsplit := Finset.sum_add_sum_compl selected (fun label => atomShare design label)
  rw [sum_atomShare_eq_rank design] at hsplit
  linarith

/-- **THE DEFLATION-FREE STRICT CRITERION.**  A card-`rank` selection whose
deficiency mass strictly beats the complement's total share dominates strictly.

Every other producer of the two off-path hinges consumes the deflation, hence the
predecessor cell.  This one consumes neither.  Its cost is the Cauchy-Schwarz
relaxation of the complement mass to one scalar, and section 8 prices that
cost. -/
theorem posDef_gap_of_deficiency_beats_complementShare (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (hbeat : ∀ probe : Fin rank → ℝ, probe ≠ 0 →
      (∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label) * (probe ⬝ᵥ probe)
        < probe ⬝ᵥ (deficiencyMass design pick *ᵥ probe)) :
    (subsetSum design (Finset.image pick Finset.univ) - 1).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one_eq design _), fun probe hne => ?_⟩
  rw [star_trivial, gap_eq_deficiencyMass_sub_baseResidual design pick hinjective,
    Matrix.sub_mulVec, dotProduct_sub, sub_pos]
  exact lt_of_le_of_lt
    (dotProduct_baseResidual_mulVec_le design (Finset.image pick Finset.univ) probe)
    (hbeat probe hne)

/-- The criterion in the design's own vocabulary: squared readings against
deficiency weights, tested against the complement's share. -/
theorem posDef_gap_of_readings_beat_complementShare (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (hbeat : ∀ probe : Fin rank → ℝ, probe ≠ 0 →
      (∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label) * (probe ⬝ᵥ probe)
        < ∑ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex))
            * (design.atom (pick slotIndex) ⬝ᵥ probe) ^ 2) :
    (subsetSum design (Finset.image pick Finset.univ) - 1).PosDef :=
  posDef_gap_of_deficiency_beats_complementShare design pick hinjective fun probe hne => by
    rw [dotProduct_deficiencyMass_mulVec]
    exact hbeat probe hne

end ShareCriterion

/-! ## 7. The producers for the two off-path obligations

The criterion refutes a tie outright, so both registry statements follow with no
predecessor cell spent on the witness and no heaviness hypothesis anywhere. -/

section MassProducers

variable {size rank : ℕ}

/-- The witness the criterion asks for, at one design. -/
def HasMassWitness (design : WeightedDesign size rank) : Prop :=
  ∃ pick : Fin rank → Fin size, Function.Injective pick ∧
    ∀ probe : Fin rank → ℝ, probe ≠ 0 →
      (∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label) * (probe ⬝ᵥ probe)
        < probe ⬝ᵥ (deficiencyMass design pick *ᵥ probe)

/-- **THE MASS WITNESS REFUTES THE TIE.**  No predecessor cell, no deflation, no
leverage floor. -/
theorem not_isTie_of_hasMassWitness (design : WeightedDesign size rank)
    (hwitness : HasMassWitness design) : ¬ IsTie design := by
  classical
  obtain ⟨pick, hinjective, hbeat⟩ := hwitness
  intro htie
  exact htie.2 (Finset.image pick Finset.univ) (card_image_pick pick hinjective)
    (posDef_gap_of_deficiency_beats_complementShare design pick hinjective hbeat)

/-- The hinge conclusion from one mass witness. -/
theorem hasParallelPair_of_isTie_of_hasMassWitness (design : WeightedDesign size rank)
    (hwitness : HasMassWitness design) (htie : IsTie design) : HasParallelPair design :=
  absurd htie (not_isTie_of_hasMassWitness design hwitness)

/-- **A PRODUCER FOR THE THRESHOLD-CELL HINGE, WITH THE PREDECESSOR CELL
UNSPENT.**  Its hypothesis asks, at every design of the cell, for ONE card-`rank`
selection whose deficiency mass beats the complement's total share. -/
theorem obligationThresholdCellHingeRankFourAndUp_of_massWitness
    (hmass : ∀ rankValue : ℕ, 4 ≤ rankValue →
      ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
        HasMassWitness design) :
    ∀ rankValue : ℕ, 4 ≤ rankValue →
      GtzWeighted (rankValue * (rankValue + 1) / 2 - 1) rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          IsTie design → HasParallelPair design := fun rankValue hrank _ design htie =>
  hasParallelPair_of_isTie_of_hasMassWitness design (hmass rankValue hrank design) htie

/-- **A PRODUCER FOR THE SUB-THRESHOLD BAND HINGE, WITH THE PREDECESSOR CELL
UNSPENT.** -/
theorem obligationSubThresholdBandHinge_of_massWitness
    (hmass : ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
      sizeValue < rankValue * (rankValue + 1) / 2 →
      ∀ design : WeightedDesign sizeValue rankValue, HasMassWitness design) :
    ∀ rankValue : ℕ, 3 ≤ rankValue →
      ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
          GtzWeighted (sizeValue - 1) rankValue →
            ∀ design : WeightedDesign sizeValue rankValue,
              IsTie design → HasParallelPair design :=
  fun rankValue hrank sizeValue hlow hhigh _ design htie =>
    hasParallelPair_of_isTie_of_hasMassWitness design
      (hmass rankValue hrank sizeValue hlow hhigh design) htie

/-- **AT `(6,3)` THE MASS WITNESS CLOSES THE HINGE OUTRIGHT.** -/
theorem hingeConclusion_sixThree_of_massWitness
    (hmass : ∀ design : WeightedDesign 6 3, HasMassWitness design) :
    ∀ design : WeightedDesign 6 3, IsTie design → HasParallelPair design :=
  fun design htie => hasParallelPair_of_isTie_of_hasMassWitness design (hmass design) htie

end MassProducers

/-! ## 8. The exact price of the relaxation

The criterion of section 6 replaces the complement's mass matrix by its trace.
This section prices that replacement against a tie, and the price is a NECESSARY
condition on every weakly dominating card-`rank` subset of a tie: its share falls
short of the rank by at least one minus its largest weight. -/

section TieCeiling

variable {size rank : ℕ}

/-- The deficiency reading at a direction the selection reads exactly at its own
norm is bounded below by one minus the largest selected weight. -/
theorem dotProduct_deficiencyMass_ge_of_tight (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    {cap : ℝ} (hcap : ∀ slotIndex : Fin rank, design.weight (pick slotIndex) ≤ cap)
    (probe : Fin rank → ℝ)
    (htight : probe ⬝ᵥ ((subsetSum design (Finset.image pick Finset.univ) - 1) *ᵥ probe) = 0) :
    ((1 : ℝ) - cap) * (probe ⬝ᵥ probe)
      ≤ probe ⬝ᵥ (deficiencyMass design pick *ᵥ probe) := by
  classical
  have hread : probe ⬝ᵥ (subsetSum design (Finset.image pick Finset.univ) *ᵥ probe)
      = ∑ slotIndex, (design.atom (pick slotIndex) ⬝ᵥ probe) ^ 2 := by
    rw [subsetSum_image_pick design pick hinjective, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun slotIndex _ => ?_
    simp only [atomMatrix, pickAtoms, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, sq,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hnorm : ∑ slotIndex, (design.atom (pick slotIndex) ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
    rw [← hread]
    have hgap : probe ⬝ᵥ ((subsetSum design (Finset.image pick Finset.univ) - 1) *ᵥ probe)
        = probe ⬝ᵥ (subsetSum design (Finset.image pick Finset.univ) *ᵥ probe)
          - probe ⬝ᵥ probe := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
    rw [hgap] at htight
    linarith
  rw [dotProduct_deficiencyMass_mulVec]
  have hterm : ∀ slotIndex : Fin rank,
      ((1 : ℝ) - cap) * (design.atom (pick slotIndex) ⬝ᵥ probe) ^ 2
        ≤ ((1 : ℝ) - design.weight (pick slotIndex))
          * (design.atom (pick slotIndex) ⬝ᵥ probe) ^ 2 := fun slotIndex =>
    mul_le_mul_of_nonneg_right (by linarith [hcap slotIndex]) (sq_nonneg _)
  calc ((1 : ℝ) - cap) * (probe ⬝ᵥ probe)
      = ∑ slotIndex, ((1 : ℝ) - cap) * (design.atom (pick slotIndex) ⬝ᵥ probe) ^ 2 := by
        rw [← Finset.mul_sum, hnorm]
    _ ≤ ∑ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex))
          * (design.atom (pick slotIndex) ⬝ᵥ probe) ^ 2 :=
        Finset.sum_le_sum fun slotIndex _ => hterm slotIndex

/-- **THE SHARE CEILING AT A TIGHT DIRECTION.**  If a card-`rank` selection has a
nonzero direction it reads exactly at that direction's own norm, then the
selection's share misses the rank by at least one minus its largest weight.

This is the exact price of the Cauchy-Schwarz relaxation, and it is a NECESSARY
condition at every tie, since the tie's weak dominator carries such a direction
(`Gtz.isTie_yields_tightDirection`).  It holds at every size and every rank, with
no deflation and no predecessor cell. -/
theorem sum_atomShare_le_of_tight (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    {cap : ℝ} (hcap : ∀ slotIndex : Fin rank, design.weight (pick slotIndex) ≤ cap)
    (probe : Fin rank → ℝ) (hne : probe ≠ 0)
    (htight : probe ⬝ᵥ ((subsetSum design (Finset.image pick Finset.univ) - 1) *ᵥ probe) = 0) :
    ∑ label ∈ Finset.image pick Finset.univ, atomShare design label
      ≤ (rank : ℝ) - 1 + cap := by
  classical
  have hnormPos : (0 : ℝ) < probe ⬝ᵥ probe := dotProduct_self_pos hne
  have hlow := dotProduct_deficiencyMass_ge_of_tight design pick hinjective hcap probe htight
  have hgapSplit : probe ⬝ᵥ ((subsetSum design (Finset.image pick Finset.univ) - 1) *ᵥ probe)
      = probe ⬝ᵥ (deficiencyMass design pick *ᵥ probe)
        - probe ⬝ᵥ (baseResidual design (Finset.image pick Finset.univ) *ᵥ probe) := by
    rw [gap_eq_deficiencyMass_sub_baseResidual design pick hinjective, Matrix.sub_mulVec,
      dotProduct_sub]
  rw [hgapSplit, sub_eq_zero] at htight
  have hhigh := dotProduct_baseResidual_mulVec_le design (Finset.image pick Finset.univ) probe
  rw [← htight] at hhigh
  have hchain : ((1 : ℝ) - cap) * (probe ⬝ᵥ probe)
      ≤ (∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label)
        * (probe ⬝ᵥ probe) := le_trans hlow hhigh
  have hshare : (1 : ℝ) - cap
      ≤ ∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label :=
    le_of_mul_le_mul_right (by linarith [hchain]) hnormPos
  rw [sum_compl_atomShare_eq design (Finset.image pick Finset.univ)] at hshare
  linarith

/-- **THE TIE'S WEAK DOMINATOR IS SHARE-STARVED.**  Assembled statement: at a tie
some card-`rank` subset dominates weakly and carries a tight direction, and its
share is then capped by the rank minus one plus its largest weight.

At the threshold cell the largest share any card-`rank` subset can be guaranteed
is `2 * rank / (rank + 1)`, which is below `rank - 1` from rank three onward.  So
this ceiling does NOT close either off-path cell, and it is recorded as the exact
distance the deflation-free criterion still has to travel. -/
theorem exists_tightDirection_share_ceiling (design : WeightedDesign size rank)
    (htie : IsTie design) :
    ∃ (selected : Finset (Fin size)) (tightDir : Fin rank → ℝ),
      selected.card = rank ∧ Dominates design selected ∧ tightDir ≠ 0 ∧
        tightDir ⬝ᵥ ((subsetSum design selected - 1) *ᵥ tightDir) = 0 :=
  isTie_yields_tightDirection htie

end TieCeiling

/-! ## 9. The two readings agree at the calibration cell

At `size = 2 * rank` the omitted labels are as many as the rank, so the omitted
mass is itself a pick sum and its determinant is the `(6, 3)` complement volume.
This section states that agreement at general rank, which is the exact locus on
which the landed `(6, 3)` law lives. -/

section CalibrationCell

variable {size rank : ℕ}

/-- **THE COMPLEMENT MASS IS A PICK SUM EXACTLY WHEN THE OMITTED LABELS ARE AS
MANY AS THE RANK.**  Landed plumbing, read at general rank. -/
theorem baseResidual_det_eq_complementVolume (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (outPick : Fin rank → Fin size)
    (hinjective : Function.Injective outPick)
    (himage : Finset.image outPick Finset.univ = selectedᶜ) :
    (baseResidual design selected).det
      = (∏ slotIndex, design.weight (outPick slotIndex))
        * (atomColumnsOfPick design outPick).det ^ 2 := by
  rw [baseResidual_eq_pickSum design selected outPick hinjective himage,
    det_pickSum_eq_prod_weight_mul_det_sq]

/-- **THE COMPLEMENT VOLUME IS NON-NEGATIVE WHEREVER IT EXISTS.**  The `(6, 3)`
law's sign hypothesis, at general rank on the calibration locus. -/
theorem baseResidual_det_nonneg (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (outPick : Fin rank → Fin size)
    (hinjective : Function.Injective outPick)
    (himage : Finset.image outPick Finset.univ = selectedᶜ) :
    0 ≤ (baseResidual design selected).det := by
  rw [baseResidual_det_eq_complementVolume design selected outPick hinjective himage]
  have hprodPos : (0 : ℝ) < ∏ slotIndex, design.weight (outPick slotIndex) :=
    Finset.prod_pos fun slotIndex _ => design.weight_pos (outPick slotIndex)
  positivity

/-- **THE PRICE LAW AT THE CALIBRATION CELL.**  When the omitted labels are as
many as the rank, both halves read at once: the gap determinant factors through
the complement factor of section 4, and that complement's own determinant IS the
`(6, 3)` complement volume.  This is the exact statement whose `(6, 3)` shadow is
`Gtz.weightProduct_mul_det_gap_eq_selfReading_sub_complementVolume`. -/
theorem det_gap_calibration (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick outPick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (houtInjective : Function.Injective outPick)
    (himage : Finset.image outPick Finset.univ = (Finset.image pick Finset.univ)ᶜ)
    (hbracket : (atomColumnsOfPick design pick).det ≠ 0) :
    (subsetSum design (Finset.image pick Finset.univ) - 1).det
        = (∏ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex)))
          * (atomColumnsOfPick design pick).det ^ 2
          * (1 - (deficiencyMass design pick)⁻¹
              * baseResidual design (Finset.image pick Finset.univ)).det
      ∧ (baseResidual design (Finset.image pick Finset.univ)).det
        = (∏ slotIndex, design.weight (outPick slotIndex))
          * (atomColumnsOfPick design outPick).det ^ 2 :=
  ⟨det_gap_eq_deficiency_mul_complementFactor design hsize pick hinjective hbracket,
    baseResidual_det_eq_complementVolume design (Finset.image pick Finset.univ) outPick
      houtInjective himage⟩

end CalibrationCell

/-! ## 10. The trace reduction, and a closed-form criterion with no deflation

The criterion of section 6 compares a MATRIX against a SCALAR.  Its trace shadow
is an identity: the deficiency mass beats the complement's share in trace by
exactly the selected atoms' total excess leverage.  So on the all-heavy stratum
the criterion holds in trace at EVERY card-`rank` selection, and the whole open
content is the spread of the deficiency spectrum.

The landed determinant-trace floor `Gtz.detTraceFloor` closes that spread with a
determinant, and the result is a criterion whose every term is a polynomial in
the design's own data. -/

section TraceReduction

variable {size rank : ℕ}

/-- The trace of the deficiency mass: deficiency weights against leverages. -/
theorem trace_deficiencyMass (design : WeightedDesign size rank) (pick : Fin rank → Fin size) :
    Matrix.trace (deficiencyMass design pick)
      = ∑ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex))
          * leverageOf (design.atom (pick slotIndex)) := by
  rw [deficiencyMass, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun slotIndex _ => by
    rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]
    rfl

/-- The trace of the omitted labels' weighted mass is their total share. -/
theorem trace_baseResidual (design : WeightedDesign size rank) (selected : Finset (Fin size)) :
    Matrix.trace (baseResidual design selected)
      = ∑ label ∈ selectedᶜ, atomShare design label := by
  classical
  rw [baseResidual_eq_complementSum, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul, atomShare]

/-- **THE TRACE SHADOW OF THE CRITERION IS AN IDENTITY.**  The deficiency mass
beats the complement's total share in trace by exactly the selected atoms' total
excess leverage.  No hypothesis at all beyond injectivity of the pick. -/
theorem trace_deficiencyMass_sub_complementShare (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick) :
    Matrix.trace (deficiencyMass design pick)
        - ∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label
      = ∑ slotIndex, (leverageOf (design.atom (pick slotIndex)) - 1) := by
  classical
  have hshare : ∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label
      = (rank : ℝ) - ∑ slotIndex, atomShare design (pick slotIndex) := by
    rw [sum_compl_atomShare_eq design (Finset.image pick Finset.univ),
      Finset.sum_image fun _ _ _ _ hequal => hinjective hequal]
  rw [trace_deficiencyMass, hshare]
  have hleft : ∑ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex))
        * leverageOf (design.atom (pick slotIndex))
      = (∑ slotIndex, leverageOf (design.atom (pick slotIndex)))
        - ∑ slotIndex, atomShare design (pick slotIndex) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun slotIndex _ => by rw [atomShare]; ring
  have hright : ∑ slotIndex, (leverageOf (design.atom (pick slotIndex)) - 1)
      = (∑ slotIndex, leverageOf (design.atom (pick slotIndex))) - (rank : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  rw [hleft, hright]
  ring

/-- **ON THE ALL-HEAVY STRATUM THE CRITERION ALWAYS HOLDS IN TRACE.**  Every
card-`rank` selection of an all-heavy design has deficiency trace at least the
complement's total share, at every size and every rank.

So nothing in the criterion of section 6 is out of reach on average.  What is
open is only the spread of the deficiency spectrum around that average. -/
theorem complementShare_le_trace_deficiencyMass_of_allHeavy (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (hheavy : ∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) :
    ∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label
      ≤ Matrix.trace (deficiencyMass design pick) := by
  have hsurplus := trace_deficiencyMass_sub_complementShare design pick hinjective
  have hnonneg : 0 ≤ ∑ slotIndex, (leverageOf (design.atom (pick slotIndex)) - 1) :=
    Finset.sum_nonneg fun slotIndex _ => by linarith [hheavy (pick slotIndex)]
  linarith

/-- **THE CLOSED-FORM CRITERION, SPECTRAL SHAPE.**  A card-`rank` selection whose
deficiency mass has determinant-trace floor above the complement's total share
dominates strictly.  No deflation, no predecessor cell, no leverage floor. -/
theorem posDef_gap_of_detTraceFloor (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (hfire : (∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label)
      < detTraceFloor rank (deficiencyMass design pick).det
          (Matrix.trace (deficiencyMass design pick))) :
    (subsetSum design (Finset.image pick Finset.univ) - 1).PosDef := by
  refine posDef_gap_of_deficiency_beats_complementShare design pick hinjective fun probe hne => ?_
  have hfloor :=
    posSemidef_sub_detTraceFloor_smul_one (posSemidef_deficiencyMass design hsize pick)
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hfloor).2 probe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, sub_nonneg] at hform
  have hnormPos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hne
  nlinarith [hform, hfire, hnormPos]

/-- **THE CLOSED-FORM CRITERION, POLYNOMIAL SHAPE.**  Every term is a polynomial
in the design's own data: the selected deficiency weights, the selected
leverages, the selected bracket and the omitted labels' shares.

  `(rank - 1)^(rank - 1) * (product of one-minus-weights) * (bracket)^2
     > (complement share) * (deficiency trace)^(rank - 1)` .

This is the object the two off-path obligations reduce to under this lane.  It
carries no deflation, so it consumes no predecessor cell, and it carries no
leverage hypothesis. -/
theorem posDef_gap_of_bracket_beats_share (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (htracePos : 0 < ∑ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex))
        * leverageOf (design.atom (pick slotIndex)))
    (hfire : (∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label)
        * (∑ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex))
            * leverageOf (design.atom (pick slotIndex))) ^ (rank - 1)
      < (((rank - 1 : ℕ) : ℝ)) ^ (rank - 1)
        * ((∏ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex)))
          * (atomColumnsOfPick design pick).det ^ 2)) :
    (subsetSum design (Finset.image pick Finset.univ) - 1).PosDef := by
  refine posDef_gap_of_detTraceFloor design hsize pick hinjective ?_
  rw [detTraceFloor, det_deficiencyMass, trace_deficiencyMass,
    lt_div_iff₀ (pow_pos htracePos (rank - 1))]
  linarith [hfire]

end TraceReduction

/-! ## 11. The ceiling on the bracket

The criterion of section 10 needs a large selected bracket.  The determinantal
marginal caps it: the weight product times the squared bracket never exceeds one,
at every size and every rank.  So the criterion's room is bounded, and section 12
records what that leaves. -/

section BracketCeiling

/-- **A POSITIVE SEMIDEFINITE FORM BELOW THE IDENTITY HAS DETERMINANT AT MOST
ONE.**  Every eigenvalue sits in the unit interval. -/
theorem det_le_one_of_posSemidef_of_one_sub_posSemidef {dim : ℕ}
    {form : Matrix (Fin dim) (Fin dim) ℝ} (hpsd : form.PosSemidef)
    (hgap : ((1 : Matrix (Fin dim) (Fin dim) ℝ) - form).PosSemidef) : form.det ≤ 1 := by
  classical
  have hdet : form.det = ∏ index : Fin dim, hpsd.1.eigenvalues index := by
    simpa using hpsd.1.det_eq_prod_eigenvalues
  have hnonneg : ∀ index : Fin dim, 0 ≤ hpsd.1.eigenvalues index := hpsd.eigenvalues_nonneg
  have hcap : ∀ index : Fin dim, hpsd.1.eigenvalues index ≤ 1 := by
    intro index
    have hunit : (hpsd.1.eigenvectorBasis index).ofLp ⬝ᵥ (hpsd.1.eigenvectorBasis index).ofLp
        = 1 := by
      rw [dotProduct_ofLp]
      simp
    have hact : form *ᵥ (hpsd.1.eigenvectorBasis index).ofLp
        = hpsd.1.eigenvalues index • (hpsd.1.eigenvectorBasis index).ofLp :=
      hpsd.1.mulVec_eigenvectorBasis index
    have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hgap).2
      (hpsd.1.eigenvectorBasis index).ofLp
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hact,
      dotProduct_smul, smul_eq_mul, hunit] at hform
    linarith
  rw [hdet]
  exact Finset.prod_le_one (fun index _ => hnonneg index) (fun index _ => hcap index)

variable {size rank : ℕ}

/-- The omitted labels' weighted mass is positive semidefinite. -/
theorem posSemidef_baseResidual (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) : (baseResidual design selected).PosSemidef := by
  classical
  rw [baseResidual_eq_complementSum]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ hleft hright => hleft.add hright)
    Matrix.PosSemidef.zero ?_
  exact fun label _ => (posSemidef_atomMatrix _).smul (design.weight_pos label).le

/-- **THE DETERMINANTAL MARGINAL CEILING.**  The weight product of a card-`rank`
selection times its squared bracket never exceeds one, at every size and every
rank.  The lower bound is free from positive semidefiniteness.

The `(6, 3)` shadow of the upper bound is `Gtz.det_complementGram_le_one`, and the
rank-three shadow of the lower bound is `Gtz.det_complementTriple_nonneg`.  Both
are cell-bound.  This is neither. -/
theorem weightProduct_mul_sq_bracket_le_one (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick) :
    0 ≤ (∏ slotIndex, design.weight (pick slotIndex))
          * (atomColumnsOfPick design pick).det ^ 2
      ∧ (∏ slotIndex, design.weight (pick slotIndex))
          * (atomColumnsOfPick design pick).det ^ 2 ≤ 1 := by
  classical
  have hprodPos : (0 : ℝ) < ∏ slotIndex, design.weight (pick slotIndex) :=
    Finset.prod_pos fun slotIndex _ => design.weight_pos (pick slotIndex)
  refine ⟨by positivity, ?_⟩
  have hpickSum : ∑ slotIndex, design.weight (pick slotIndex)
        • atomMatrix (design.atom (pick slotIndex))
      = ∑ label ∈ Finset.image pick Finset.univ,
          design.weight label • atomMatrix (design.atom label) :=
    (weightedSum_image_pick design pick hinjective).symm
  have hgap : ((1 : Matrix (Fin rank) (Fin rank) ℝ)
      - ∑ slotIndex, design.weight (pick slotIndex)
          • atomMatrix (design.atom (pick slotIndex))).PosSemidef := by
    rw [hpickSum, ← baseResidual]
    exact posSemidef_baseResidual design (Finset.image pick Finset.univ)
  have hbound := det_le_one_of_posSemidef_of_one_sub_posSemidef
    (posSemidef_pickSum design pick) hgap
  rwa [det_pickSum_eq_prod_weight_mul_det_sq] at hbound

end BracketCeiling

/-! ## 12. The closed-form producers

The polynomial criterion of section 10 refutes a tie outright, so both registry
statements follow from it.  These producers spend NO predecessor cell on the
witness and carry NO heaviness hypothesis. -/

section BracketProducers

variable {size rank : ℕ}

/-- The closed-form witness, at one design: a card-`rank` selection whose
deficiency trace is positive and whose bracket beats the complement share. -/
def HasBracketWitness (design : WeightedDesign size rank) : Prop :=
  ∃ pick : Fin rank → Fin size, Function.Injective pick ∧
    0 < (∑ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex))
        * leverageOf (design.atom (pick slotIndex))) ∧
    (∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label)
        * (∑ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex))
            * leverageOf (design.atom (pick slotIndex))) ^ (rank - 1)
      < (((rank - 1 : ℕ) : ℝ)) ^ (rank - 1)
        * ((∏ slotIndex, ((1 : ℝ) - design.weight (pick slotIndex)))
          * (atomColumnsOfPick design pick).det ^ 2)

/-- **THE CLOSED-FORM WITNESS REFUTES THE TIE.** -/
theorem not_isTie_of_hasBracketWitness (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (hwitness : HasBracketWitness design) : ¬ IsTie design := by
  classical
  obtain ⟨pick, hinjective, htracePos, hfire⟩ := hwitness
  intro htie
  exact htie.2 (Finset.image pick Finset.univ) (card_image_pick pick hinjective)
    (posDef_gap_of_bracket_beats_share design hsize pick hinjective htracePos hfire)

/-- The hinge conclusion from one closed-form witness. -/
theorem hasParallelPair_of_isTie_of_hasBracketWitness (design : WeightedDesign size rank)
    (hsize : 2 ≤ size) (hwitness : HasBracketWitness design) (htie : IsTie design) :
    HasParallelPair design :=
  absurd htie (not_isTie_of_hasBracketWitness design hsize hwitness)

/-- Every closed-form witness is a mass witness, so the closed-form producers are
weaker than the section-7 producers and both are landed. -/
theorem hasMassWitness_of_hasBracketWitness (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (hwitness : HasBracketWitness design) : HasMassWitness design := by
  classical
  obtain ⟨pick, hinjective, htracePos, hfire⟩ := hwitness
  refine ⟨pick, hinjective, fun probe hne => ?_⟩
  have hfloor :=
    posSemidef_sub_detTraceFloor_smul_one (posSemidef_deficiencyMass design hsize pick)
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hfloor).2 probe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, sub_nonneg] at hform
  have hlt : (∑ label ∈ (Finset.image pick Finset.univ)ᶜ, atomShare design label)
      < detTraceFloor rank (deficiencyMass design pick).det
          (Matrix.trace (deficiencyMass design pick)) := by
    rw [detTraceFloor, det_deficiencyMass, trace_deficiencyMass,
      lt_div_iff₀ (pow_pos htracePos (rank - 1))]
    linarith [hfire]
  have hnormPos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hne
  nlinarith [hform, hlt, hnormPos]

/-- **A CLOSED-FORM PRODUCER FOR THE THRESHOLD-CELL HINGE.**  Its hypothesis is
one polynomial inequality at one card-`rank` selection of every design of the
cell, with no deflation anywhere in it. -/
theorem obligationThresholdCellHingeRankFourAndUp_of_bracketWitness
    (hbracket : ∀ rankValue : ℕ, 4 ≤ rankValue →
      ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
        HasBracketWitness design) :
    ∀ rankValue : ℕ, 4 ≤ rankValue →
      GtzWeighted (rankValue * (rankValue + 1) / 2 - 1) rankValue →
        ∀ design : WeightedDesign (rankValue * (rankValue + 1) / 2) rankValue,
          IsTie design → HasParallelPair design := by
  intro rankValue hrank _ design htie
  have hsize : 2 ≤ rankValue * (rankValue + 1) / 2 := by
    have hmono : 4 * 5 / 2 ≤ rankValue * (rankValue + 1) / 2 :=
      Nat.div_le_div_right (Nat.mul_le_mul hrank (by omega))
    omega
  exact hasParallelPair_of_isTie_of_hasBracketWitness design hsize
    (hbracket rankValue hrank design) htie

/-- **A CLOSED-FORM PRODUCER FOR THE SUB-THRESHOLD BAND HINGE.** -/
theorem obligationSubThresholdBandHinge_of_bracketWitness
    (hbracket : ∀ rankValue : ℕ, 3 ≤ rankValue → ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
      sizeValue < rankValue * (rankValue + 1) / 2 →
      ∀ design : WeightedDesign sizeValue rankValue, HasBracketWitness design) :
    ∀ rankValue : ℕ, 3 ≤ rankValue →
      ∀ sizeValue : ℕ, 2 * rankValue ≤ sizeValue →
        sizeValue < rankValue * (rankValue + 1) / 2 →
          GtzWeighted (sizeValue - 1) rankValue →
            ∀ design : WeightedDesign sizeValue rankValue,
              IsTie design → HasParallelPair design := by
  intro rankValue hrank sizeValue hlow hhigh _ design htie
  exact hasParallelPair_of_isTie_of_hasBracketWitness design (by omega)
    (hbracket rankValue hrank sizeValue hlow hhigh design) htie

/-- **AT `(6,3)` THE CLOSED-FORM WITNESS CLOSES THE HINGE OUTRIGHT.** -/
theorem hingeConclusion_sixThree_of_bracketWitness
    (hbracket : ∀ design : WeightedDesign 6 3, HasBracketWitness design) :
    ∀ design : WeightedDesign 6 3, IsTie design → HasParallelPair design :=
  fun design htie => hasParallelPair_of_isTie_of_hasBracketWitness design (by norm_num)
    (hbracket design) htie

end BracketProducers

end Gtz
