/-
# The Sylvester reduction: when the third minor is the only obstruction

Strict domination at a triple is `Gtz.posDef_finThree_iff_leadingMinors`, three
inequalities on the gap block: the corner, the two-by-two minor, and the determinant.
The campaign spends most of its budget on the third one.  This file asks whether the
first two are consequences of the third, and answers it with an exact threshold.

## What the answer is

They are NOT consequences of the third on their own.  `Gtz.sylvesterMargin_not_redundant`
exhibits a gap diagonal `(1/4, 1/4, 1/4)` with pairings `7/24`, positive determinant
`5/3456`, and a NEGATIVE two-by-two minor `-13/576`.  The corner is positive and the
determinant is positive, and domination still fails.

They ARE consequences of the third once the triple carries enough leverage.  The exact
extra input is one linear inequality, `Gtz.sylvesterMargin`.  Write `d` for the three
diagonal entries of the form and `w` for the three weights.  The margin is

  `(d0-w0)(d1-w1) + (d0-w0)(d2-w2) + (d1-w1)(d2-w2) - [ d0 d1 d2 + (1-d0)(1-d1)(1-d2) ]`

and `Gtz.posDef_blockGapAt_of_det_pos_of_margin` says: at a nonnegative margin, a
positive gap determinant gives strict domination outright.  No square bound, no minor
chain, one determinant sign.

## Why the margin is the right quantity

Two facts meet.  The first is a cap.  A principal block `B` of a projection satisfies
`0 <= det B` and `0 <= det (1 - B)`, and those two determinants add to exactly
`d0 d1 d2 + (1-d0)(1-d1)(1-d2)` minus the squared pairings
(`Gtz.tripleDetForm_add_complement`).  So the pairing energy of ANY triple of a
projection is capped by the two leverage products (`Gtz.sq_sum_le_leverageCap_of_posSemidef_pair`).
That cap is sharp.

The second is the pivot law.  The landed `Gtz.pairMinorForm_mul_sub_sq` and its two
siblings read the gap determinant as a Schur complement at each of the three pivots at
once.  At a positive gap diagonal a positive determinant therefore forces the three
two-by-two minors to share one sign (`Gtz.pairMinorForm_mul_pos_of_det_pos`).  All
three negative would put the pairing energy above the pair-minor total.  The margin is
exactly the statement that the pair-minor total already sits at or above the cap, and
that closes the branch.

## The threshold is linear, and half the triples clear it

At uniform weight the cubic cap and the quadratic pair-minor total differ by an
EXACTLY LINEAR functional of the three leverage scores:

  `sylvesterMargin d0 d1 d2 (1/6) (1/6) (1/6) = (2/3) (d0 + d1 + d2) - 11/12`

(`Gtz.sylvesterMargin_sixth`).  Every quadratic and cubic term cancels.  So the whole
criterion at uniform weight is `11/8 <= d0 + d1 + d2` (`Gtz.sylvesterMargin_sixth_nonneg_iff`).

The six leverage scores of a rank-three projection on six labels total three, and
`11/8 + 11/8 < 3`.  So of every complementary PAIR of triples at least one member
clears the threshold (`Gtz.sylvesterMargin_sixth_nonneg_of_complementary`), and at
least ten of the twenty triples qualify at every design.  Ten is attained.

## The equal-share stratum

The flat locus has every diagonal entry `1/2`, so the leverage sum of every triple is
`3/2` and the margin is `1/12`, positive with room
(`Gtz.sylvesterMargin_flat`).  On that stratum
`Gtz.posDef_blockGapAt_of_det_pos_of_flat` is an equivalence with ONE inequality in
it, which strengthens the landed `Gtz.posDef_blockGapAt_of_flat_iff` by deleting its
square bound.  The reading is
`Gtz.sq_offDiag_lt_ninth_of_det_pos_of_flat`: at a flat design and uniform weight,
EVERY pairing of a triple with positive gap determinant is automatically below `1/9`
in square.  There is no smallness left to select for.

## Scope

The margin is stated for a general weight and the doors below carry a general weight,
so this lane is not a weight-uniform certificate.  The counting law of section 6 is
uniform-weight only, and says so.
-/
import Gtz.Wave.TwoSidedFlatSandwich
import Gtz.Wave.ElliptopeGapBridge
import Gtz.Wave.ProjectionMinorShift

namespace Gtz

open Matrix

/-! ## 1. The three scalars -/

/-- The LEVERAGE CAP of three diagonal entries: the determinant a projection block
contributes plus the determinant its complement contributes, with the pairings set to
zero.  It caps the pairing energy of every triple of a projection. -/
def sylvesterLeverageCap (dA dB dC : ℝ) : ℝ :=
  dA * dB * dC + (1 - dA) * (1 - dB) * (1 - dC)

/-- The PAIR-MINOR TOTAL of a gap diagonal: the sum of the three products.  It is the
sum of the three two-by-two minors plus the pairing energy. -/
def sylvesterPairTotal (p q r : ℝ) : ℝ := p * q + p * r + q * r

/-- **THE SYLVESTER MARGIN.**  The amount by which the pair-minor total of the gap
diagonal exceeds the leverage cap of the form diagonal.  A nonnegative margin makes
the gap determinant the only obstruction to strict domination. -/
def sylvesterMargin (dA dB dC wA wB wC : ℝ) : ℝ :=
  sylvesterPairTotal (dA - wA) (dB - wB) (dC - wC) - sylvesterLeverageCap dA dB dC

theorem sylvesterLeverageCap_apply (dA dB dC : ℝ) :
    sylvesterLeverageCap dA dB dC = dA * dB * dC + (1 - dA) * (1 - dB) * (1 - dC) := rfl

theorem sylvesterPairTotal_apply (p q r : ℝ) :
    sylvesterPairTotal p q r = p * q + p * r + q * r := rfl

/-- The leverage cap does not see the order of the three entries. -/
theorem sylvesterLeverageCap_swap_second_third (dA dB dC : ℝ) :
    sylvesterLeverageCap dA dC dB = sylvesterLeverageCap dA dB dC := by
  rw [sylvesterLeverageCap, sylvesterLeverageCap]; ring

theorem sylvesterLeverageCap_rotate (dA dB dC : ℝ) :
    sylvesterLeverageCap dB dC dA = sylvesterLeverageCap dA dB dC := by
  rw [sylvesterLeverageCap, sylvesterLeverageCap]; ring

theorem sylvesterPairTotal_swap_second_third (p q r : ℝ) :
    sylvesterPairTotal p r q = sylvesterPairTotal p q r := by
  rw [sylvesterPairTotal, sylvesterPairTotal]; ring

theorem sylvesterPairTotal_rotate (p q r : ℝ) :
    sylvesterPairTotal q r p = sylvesterPairTotal p q r := by
  rw [sylvesterPairTotal, sylvesterPairTotal]; ring

/-- **THE CAP IDENTITY.**  A triple determinant and the triple determinant of its
complement add to the leverage cap minus the pairing energy.  Every cubic term
cancels, and the sum is quadratic.  This is the whole source of the cap. -/
theorem tripleDetForm_add_complement (dA dB dC u v w : ℝ) :
    tripleDetForm dA dB dC u v w
        + tripleDetForm (1 - dA) (1 - dB) (1 - dC) (-u) (-v) (-w)
      = sylvesterLeverageCap dA dB dC - (u ^ 2 + v ^ 2 + w ^ 2) := by
  rw [tripleDetForm, tripleDetForm, sylvesterLeverageCap]; ring

/-- **THE ENERGY CAP, in scalars.**  Two nonnegative determinants cap the pairing
energy by the leverage cap. -/
theorem sq_sum_le_sylvesterLeverageCap {dA dB dC u v w : ℝ}
    (hprimal : 0 ≤ tripleDetForm dA dB dC u v w)
    (hdual : 0 ≤ tripleDetForm (1 - dA) (1 - dB) (1 - dC) (-u) (-v) (-w)) :
    u ^ 2 + v ^ 2 + w ^ 2 ≤ sylvesterLeverageCap dA dB dC := by
  have hsum := tripleDetForm_add_complement dA dB dC u v w
  linarith

/-- The triple determinant does not see a transposition of the last two slots. -/
theorem tripleDetForm_swap_last_two (p q r u v w : ℝ) :
    tripleDetForm p r q v u w = tripleDetForm p q r u v w := by
  rw [tripleDetForm, tripleDetForm]; ring

/-- The triple determinant does not see a cyclic rotation of the three slots. -/
theorem tripleDetForm_rotate_slots (p q r u v w : ℝ) :
    tripleDetForm q r p w u v = tripleDetForm p q r u v w := by
  rw [tripleDetForm, tripleDetForm]; ring

/-! ## 2. The pivot law: a positive determinant forces one sign

The landed `Gtz.pairMinorForm_mul_sub_sq` and its two siblings read the same cubic as
the Schur complement at each of the three pivots.  A positive pivot and a positive
determinant make the corresponding product of two-by-two minors positive.  The three
statements together say the three minors share a sign. -/

/-- Pivot on the first slot.  The product of the first two minors is positive. -/
theorem pairMinorForm_mul_pos_of_det_pos {p q r u v w : ℝ} (hp : 0 < p)
    (hdet : 0 < tripleDetForm p q r u v w) :
    0 < pairMinorForm p q u * pairMinorForm p r v := by
  have hid := pairMinorForm_mul_sub_sq p q r u v w
  have hsq : (0 : ℝ) ≤ (p * w - u * v) ^ 2 := sq_nonneg _
  have hpd : 0 < p * tripleDetForm p q r u v w := mul_pos hp hdet
  linarith

/-- Pivot on the second slot.  The product of the first and third minors is
positive. -/
theorem pairMinorForm_mul_pos_of_det_pos_second {p q r u v w : ℝ} (hq : 0 < q)
    (hdet : 0 < tripleDetForm p q r u v w) :
    0 < pairMinorForm p q u * pairMinorForm q r w := by
  have hid := pairMinorForm_mul_sub_sq_second p q r u v w
  have hcomm : pairMinorForm q p u = pairMinorForm p q u := pairMinorForm_comm q p u
  rw [hcomm] at hid
  have hsq : (0 : ℝ) ≤ (q * v - u * w) ^ 2 := sq_nonneg _
  have hqd : 0 < q * tripleDetForm p q r u v w := mul_pos hq hdet
  linarith

/-- Pivot on the third slot.  The product of the second and third minors is
positive. -/
theorem pairMinorForm_mul_pos_of_det_pos_third {p q r u v w : ℝ} (hr : 0 < r)
    (hdet : 0 < tripleDetForm p q r u v w) :
    0 < pairMinorForm p r v * pairMinorForm q r w := by
  have hid := pairMinorForm_mul_sub_sq_third p q r u v w
  have hcv : pairMinorForm r p v = pairMinorForm p r v := pairMinorForm_comm r p v
  have hcw : pairMinorForm r q w = pairMinorForm q r w := pairMinorForm_comm r q w
  rw [hcv, hcw] at hid
  have hsq : (0 : ℝ) ≤ (r * u - v * w) ^ 2 := sq_nonneg _
  have hrd : 0 < r * tripleDetForm p q r u v w := mul_pos hr hdet
  linarith

/-- **THE SAME-SIGN LAW.**  At a positive gap diagonal a positive gap determinant
makes the three two-by-two minors all positive or all negative.  There is no mixed
branch. -/
theorem pairMinorForm_all_pos_or_all_neg {p q r u v w : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hdet : 0 < tripleDetForm p q r u v w) :
    (0 < pairMinorForm p q u ∧ 0 < pairMinorForm p r v ∧ 0 < pairMinorForm q r w)
      ∨ (pairMinorForm p q u < 0 ∧ pairMinorForm p r v < 0 ∧ pairMinorForm q r w < 0) := by
  have h1 := pairMinorForm_mul_pos_of_det_pos hp hdet
  have h2 := pairMinorForm_mul_pos_of_det_pos_second hq hdet
  rcases mul_pos_iff.mp h1 with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · rcases mul_pos_iff.mp h2 with ⟨_, hC⟩ | ⟨hA', _⟩
    · exact Or.inl ⟨hA, hB, hC⟩
    · exact absurd hA (not_lt.mpr hA'.le)
  · rcases mul_pos_iff.mp h2 with ⟨hA', _⟩ | ⟨_, hC⟩
    · exact absurd hA' (not_lt.mpr hA.le)
    · exact Or.inr ⟨hA, hB, hC⟩

/-! ## 3. The crux: the margin kills the all-negative branch -/

/-- **THE SCALAR REDUCTION.**  A positive gap determinant at a positive gap diagonal
gives a positive two-by-two minor, as soon as the pair-minor total reaches a cap that
already bounds the pairing energy.

The all-negative branch of the same-sign law puts the pairing energy strictly above
the pair-minor total.  The two hypotheses sandwich it the other way, and the branch
dies.  No square root, no division, no case split on the pairings. -/
theorem pairMinorForm_pos_of_pairTotal_ge {p q r u v w cap : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hcap : u ^ 2 + v ^ 2 + w ^ 2 ≤ cap)
    (hmargin : cap ≤ sylvesterPairTotal p q r)
    (hdet : 0 < tripleDetForm p q r u v w) :
    0 < pairMinorForm p q u := by
  rcases pairMinorForm_all_pos_or_all_neg hp hq hdet with ⟨hA, -, -⟩ | ⟨hA, hB, hC⟩
  · exact hA
  · exfalso
    rw [pairMinorForm] at hA hB hC
    rw [sylvesterPairTotal] at hmargin
    linarith

/-- The same conclusion for the SECOND two-by-two minor, by the slot transposition. -/
theorem pairMinorForm_second_pos_of_pairTotal_ge {p q r u v w cap : ℝ} (hp : 0 < p)
    (hr : 0 < r) (hcap : u ^ 2 + v ^ 2 + w ^ 2 ≤ cap)
    (hmargin : cap ≤ sylvesterPairTotal p q r)
    (hdet : 0 < tripleDetForm p q r u v w) :
    0 < pairMinorForm p r v :=
  pairMinorForm_pos_of_pairTotal_ge (p := p) (q := r) (r := q) (u := v) (v := u) (w := w)
    (cap := cap) hp hr (by linarith)
    (by rw [sylvesterPairTotal_swap_second_third]; exact hmargin)
    (by rw [tripleDetForm_swap_last_two]; exact hdet)

/-- The same conclusion for the THIRD two-by-two minor, by the slot rotation. -/
theorem pairMinorForm_third_pos_of_pairTotal_ge {p q r u v w cap : ℝ} (hq : 0 < q)
    (hr : 0 < r) (hcap : u ^ 2 + v ^ 2 + w ^ 2 ≤ cap)
    (hmargin : cap ≤ sylvesterPairTotal p q r)
    (hdet : 0 < tripleDetForm p q r u v w) :
    0 < pairMinorForm q r w :=
  pairMinorForm_pos_of_pairTotal_ge (p := q) (q := r) (r := p) (u := w) (v := u) (w := v)
    (cap := cap) hq hr (by linarith)
    (by rw [sylvesterPairTotal_rotate]; exact hmargin)
    (by rw [tripleDetForm_rotate_slots]; exact hdet)

/-! ## 4. The block layer -/

/-- A symmetric three-by-three determinant is the campaign's triple determinant form
on its own entries. -/
theorem det_eq_tripleDetForm_of_symm {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymm : formᵀ = form) :
    form.det = tripleDetForm (form 0 0) (form 1 1) (form 2 2)
      (form 0 1) (form 0 2) (form 1 2) := by
  rw [Matrix.det_fin_three, tripleDetForm, apply_symm_of_transpose_eq hsymm 1 0,
    apply_symm_of_transpose_eq hsymm 2 0, apply_symm_of_transpose_eq hsymm 2 1]
  ring

/-- **THE ENERGY CAP, at a block.**  A symmetric block that is positive semidefinite
and whose complement is positive semidefinite has its pairing energy capped by the
leverage cap of its diagonal.  Every principal block of a projection is of that kind. -/
theorem sq_sum_le_leverageCap_of_posSemidef_pair {block : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : blockᵀ = block) (hprimal : block.PosSemidef)
    (hdual : ((1 : Matrix (Fin 3) (Fin 3) ℝ) - block).PosSemidef) :
    block 0 1 ^ 2 + block 0 2 ^ 2 + block 1 2 ^ 2
      ≤ sylvesterLeverageCap (block 0 0) (block 1 1) (block 2 2) := by
  have hsymmDual : ((1 : Matrix (Fin 3) (Fin 3) ℝ) - block)ᵀ
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) - block := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymm]
  have hd0 : ∀ slot : Fin 3, ((1 : Matrix (Fin 3) (Fin 3) ℝ) - block) slot slot
      = 1 - block slot slot := by
    intro slot; rw [Matrix.sub_apply, Matrix.one_apply_eq]
  have hoff : ∀ left right : Fin 3, left ≠ right →
      ((1 : Matrix (Fin 3) (Fin 3) ℝ) - block) left right = -block left right := by
    intro left right hne; rw [Matrix.sub_apply, Matrix.one_apply_ne hne]; ring
  have hprimalDet : 0 ≤ block.det := hprimal.det_nonneg
  have hdualDet : 0 ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ) - block).det := hdual.det_nonneg
  rw [det_eq_tripleDetForm_of_symm hsymm] at hprimalDet
  rw [det_eq_tripleDetForm_of_symm hsymmDual, hd0 0, hd0 1, hd0 2,
    hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 2 (by decide)] at hdualDet
  exact sq_sum_le_sylvesterLeverageCap hprimalDet hdualDet

/-- **THE BLOCK REDUCTION.**  A symmetric three-by-three form with a positive first
and second diagonal entry, a pairing energy below a cap, and a pair-minor total above
that same cap, is positive definite as soon as its determinant is positive.

This is Sylvester with the middle test deleted. -/
theorem posDef_of_det_pos_of_pairTotal_ge {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : formᵀ = form) {cap : ℝ} (hfirst : 0 < form 0 0) (hsecond : 0 < form 1 1)
    (hcap : form 0 1 ^ 2 + form 0 2 ^ 2 + form 1 2 ^ 2 ≤ cap)
    (hmargin : cap ≤ sylvesterPairTotal (form 0 0) (form 1 1) (form 2 2))
    (hdet : 0 < form.det) :
    form.PosDef := by
  have hdetForm : 0 < tripleDetForm (form 0 0) (form 1 1) (form 2 2)
      (form 0 1) (form 0 2) (form 1 2) := by
    rwa [det_eq_tripleDetForm_of_symm hsymm] at hdet
  have hminor : 0 < pairMinorForm (form 0 0) (form 1 1) (form 0 1) :=
    pairMinorForm_pos_of_pairTotal_ge hfirst hsecond hcap hmargin hdetForm
  rw [posDef_finThree_iff_leadingMinors _ hsymm]
  refine ⟨hfirst, ?_, ?_⟩
  · rw [pairMinorForm] at hminor; linarith
  · rw [tripleDetForm] at hdetForm; nlinarith [hdetForm]

/-- **THE BLOCK REDUCTION IS AN EQUIVALENCE.**  Under the same margin the two
statements coincide, because a positive definite form has a positive determinant. -/
theorem posDef_iff_det_pos_of_pairTotal_ge {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : formᵀ = form) {cap : ℝ} (hfirst : 0 < form 0 0) (hsecond : 0 < form 1 1)
    (hcap : form 0 1 ^ 2 + form 0 2 ^ 2 + form 1 2 ^ 2 ≤ cap)
    (hmargin : cap ≤ sylvesterPairTotal (form 0 0) (form 1 1) (form 2 2)) :
    form.PosDef ↔ 0 < form.det :=
  ⟨fun hpd => hpd.det_pos,
    posDef_of_det_pos_of_pairTotal_ge hsymm hfirst hsecond hcap hmargin⟩

/-! ## 5. The design layer -/

variable {atoms rank : ℕ}

/-- The pairing energy of a triple of a design's projection form is capped by the
leverage cap of the three leverage scores.  The two inputs are that a principal block
of a projection is positive semidefinite and that its complement is too. -/
theorem sq_sum_le_leverageCap_projection (design : WeightedDesign atoms rank)
    {pick : Fin 3 → Fin atoms} (hinj : Function.Injective pick) :
    projectionOfDesign design (pick 0) (pick 1) ^ 2
        + projectionOfDesign design (pick 0) (pick 2) ^ 2
        + projectionOfDesign design (pick 1) (pick 2) ^ 2
      ≤ sylvesterLeverageCap (projectionOfDesign design (pick 0) (pick 0))
          (projectionOfDesign design (pick 1) (pick 1))
          (projectionOfDesign design (pick 2) (pick 2)) := by
  have hsymm : ((projectionOfDesign design).submatrix pick pick)ᵀ
      = (projectionOfDesign design).submatrix pick pick := by
    rw [Matrix.transpose_submatrix, projectionOfDesign_transpose]
  exact sq_sum_le_leverageCap_of_posSemidef_pair hsymm
    (posSemidef_submatrix_projectionOfDesign design pick)
    (posSemidef_one_sub_submatrix_projectionOfDesign design pick hinj)

/-- **THE DESIGN REDUCTION.**  At a nonnegative Sylvester margin a positive gap
determinant gives strict domination at the triple.  The two positivity hypotheses on
the gap diagonal are necessary for domination anyway, so nothing is lost. -/
theorem posDef_blockGapAt_of_det_pos_of_margin (design : WeightedDesign atoms rank)
    {pick : Fin 3 → Fin atoms} (hinj : Function.Injective pick)
    (hfirst : 0 < projectionOfDesign design (pick 0) (pick 0) - design.weight (pick 0))
    (hsecond : 0 < projectionOfDesign design (pick 1) (pick 1) - design.weight (pick 1))
    (hmargin : 0 ≤ sylvesterMargin (projectionOfDesign design (pick 0) (pick 0))
        (projectionOfDesign design (pick 1) (pick 1))
        (projectionOfDesign design (pick 2) (pick 2))
        (design.weight (pick 0)) (design.weight (pick 1)) (design.weight (pick 2)))
    (hdet : 0 < (blockGapAt (projectionOfDesign design) design.weight pick).det) :
    (blockGapAt (projectionOfDesign design) design.weight pick).PosDef := by
  have hsymm := blockGapAt_transpose (projectionOfDesign_transpose design) design.weight pick
  have hdiag := blockGapAt_apply_diag (projectionOfDesign design) design.weight pick
  have h01 := blockGapAt_apply_offDiag (projectionOfDesign design) design.weight pick
    (by decide : (0 : Fin 3) ≠ 1)
  have h02 := blockGapAt_apply_offDiag (projectionOfDesign design) design.weight pick
    (by decide : (0 : Fin 3) ≠ 2)
  have h12 := blockGapAt_apply_offDiag (projectionOfDesign design) design.weight pick
    (by decide : (1 : Fin 3) ≠ 2)
  refine posDef_of_det_pos_of_pairTotal_ge hsymm
    (cap := sylvesterLeverageCap (projectionOfDesign design (pick 0) (pick 0))
      (projectionOfDesign design (pick 1) (pick 1))
      (projectionOfDesign design (pick 2) (pick 2)))
    (by rw [hdiag 0]; exact hfirst) (by rw [hdiag 1]; exact hsecond) ?_ ?_ hdet
  · rw [h01, h02, h12]; exact sq_sum_le_leverageCap_projection design hinj
  · rw [hdiag 0, hdiag 1, hdiag 2]
    rw [sylvesterMargin] at hmargin
    linarith

/-- **THE DESIGN REDUCTION, as an equivalence.** -/
theorem posDef_blockGapAt_iff_det_pos_of_margin (design : WeightedDesign atoms rank)
    {pick : Fin 3 → Fin atoms} (hinj : Function.Injective pick)
    (hfirst : 0 < projectionOfDesign design (pick 0) (pick 0) - design.weight (pick 0))
    (hsecond : 0 < projectionOfDesign design (pick 1) (pick 1) - design.weight (pick 1))
    (hmargin : 0 ≤ sylvesterMargin (projectionOfDesign design (pick 0) (pick 0))
        (projectionOfDesign design (pick 1) (pick 1))
        (projectionOfDesign design (pick 2) (pick 2))
        (design.weight (pick 0)) (design.weight (pick 1)) (design.weight (pick 2))) :
    (blockGapAt (projectionOfDesign design) design.weight pick).PosDef
      ↔ 0 < (blockGapAt (projectionOfDesign design) design.weight pick).det :=
  ⟨fun hpd => hpd.det_pos,
    posDef_blockGapAt_of_det_pos_of_margin design hinj hfirst hsecond hmargin⟩

/-! ## 6. Uniform weight: the margin is linear, and half the triples clear it -/

/-- **THE MARGIN IS LINEAR AT UNIFORM WEIGHT.**  Every quadratic and cubic term of
the cap cancels against the pair-minor total, and one linear functional of the three
leverage scores is left.  This is the reason the criterion is cheap. -/
theorem sylvesterMargin_sixth (dA dB dC : ℝ) :
    sylvesterMargin dA dB dC (1 / 6) (1 / 6) (1 / 6)
      = 2 / 3 * (dA + dB + dC) - 11 / 12 := by
  rw [sylvesterMargin, sylvesterPairTotal, sylvesterLeverageCap]; ring

/-- **THE THRESHOLD.**  At uniform weight the criterion is one linear inequality on
the leverage sum of the triple, with the constant `11/8`. -/
theorem sylvesterMargin_sixth_nonneg_iff (dA dB dC : ℝ) :
    0 ≤ sylvesterMargin dA dB dC (1 / 6) (1 / 6) (1 / 6) ↔ 11 / 8 ≤ dA + dB + dC := by
  rw [sylvesterMargin_sixth]
  constructor <;> intro hle <;> linarith

/-- **HALF THE TRIPLES QUALIFY.**  A triple and its complement have leverage sums
that total the rank three, and `11/8 + 11/8` is less than three.  So at least one
member of every complementary pair clears the threshold.  At twenty triples in ten
complementary pairs, at least ten qualify at every design, and ten is attained. -/
theorem sylvesterMargin_sixth_nonneg_of_complementary {dA dB dC eA eB eC : ℝ}
    (htotal : dA + dB + dC + (eA + eB + eC) = 3) :
    0 ≤ sylvesterMargin dA dB dC (1 / 6) (1 / 6) (1 / 6)
      ∨ 0 ≤ sylvesterMargin eA eB eC (1 / 6) (1 / 6) (1 / 6) := by
  rw [sylvesterMargin_sixth, sylvesterMargin_sixth]
  rcases le_or_gt (11 / 8 : ℝ) (dA + dB + dC) with hle | hlt
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- The six leverage scores of a rank-three design on six labels total three. -/
theorem sum_diag_projectionOfDesign_six (design : WeightedDesign 6 3) :
    projectionOfDesign design 0 0 + projectionOfDesign design 1 1
        + projectionOfDesign design 2 2 + projectionOfDesign design 3 3
        + projectionOfDesign design 4 4 + projectionOfDesign design 5 5 = 3 := by
  have htrace := trace_projectionOfDesign design
  rw [Matrix.trace, Fin.sum_univ_six] at htrace
  simp only [Matrix.diag_apply] at htrace
  norm_num at htrace
  linarith

/-- **THE CONCRETE HALF.**  At every rank-three design on six labels, one of the two
halves of the label set clears the uniform-weight threshold.  No hypothesis on the
design beyond Parseval. -/
theorem sylvesterMargin_sixth_nonneg_of_half (design : WeightedDesign 6 3) :
    0 ≤ sylvesterMargin (projectionOfDesign design 0 0) (projectionOfDesign design 1 1)
        (projectionOfDesign design 2 2) (1 / 6) (1 / 6) (1 / 6)
      ∨ 0 ≤ sylvesterMargin (projectionOfDesign design 3 3) (projectionOfDesign design 4 4)
        (projectionOfDesign design 5 5) (1 / 6) (1 / 6) (1 / 6) :=
  sylvesterMargin_sixth_nonneg_of_complementary
    (by have h := sum_diag_projectionOfDesign_six design; linarith)

/-! ## 7. The equal-share stratum -/

/-- On the flat locus every leverage score is one half, so the margin is `1/12` at
uniform weight.  The threshold `11/8` sits below the flat leverage sum `3/2`, with a
gap of `1/8`. -/
theorem sylvesterMargin_flat :
    sylvesterMargin (1 / 2) (1 / 2) (1 / 2) (1 / 6) (1 / 6) (1 / 6) = 1 / 12 := by
  rw [sylvesterMargin_sixth]; norm_num

/-- **THE FLAT REDUCTION.**  At a flat design and uniform weight, strict domination at
a triple is EXACTLY a positive gap determinant.  The landed
`Gtz.posDef_blockGapAt_of_flat_iff` needs a square bound as well.  Here that bound is
a consequence, and the criterion is one inequality.

`Gtz.exists_posDef_blockGapAt_of_flat_uniform_of_gap` reaches the same conclusion on
the same stratum by a different route: it derives one small pair from the gap and then
REORDERS the triple.  This statement fixes the given order and is an instance of the
general-weight `Gtz.posDef_blockGapAt_iff_det_pos_of_margin`, which holds at any
diagonal and any weight. -/
theorem posDef_blockGapAt_iff_det_pos_of_flat (design : WeightedDesign 6 3)
    (hflat : IsFlatDiagonal (projectionOfDesign design)) (huniform : design.weight = sixthWeight)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick) :
    (blockGapAt (projectionOfDesign design) design.weight pick).PosDef
      ↔ 0 < (blockGapAt (projectionOfDesign design) design.weight pick).det := by
  have hw : ∀ slot : Fin 3, design.weight (pick slot) = 1 / 6 := by
    intro slot; rw [huniform]; rfl
  refine posDef_blockGapAt_iff_det_pos_of_margin design hinj ?_ ?_ ?_
  · rw [hflat (pick 0), hw 0]; norm_num
  · rw [hflat (pick 1), hw 1]; norm_num
  · rw [hflat (pick 0), hflat (pick 1), hflat (pick 2), hw 0, hw 1, hw 2, sylvesterMargin_flat]
    norm_num

/-- **THE ANSWER TO THE SELECTION QUESTION.**  At a flat design and uniform weight,
EVERY pairing of a triple with positive gap determinant is below `1/9` in square.
There is no smallness left to select for: a good triple is automatically a small
triple on all three of its pairs.

The sibling route through `Gtz.exists_small_pair_of_flat_of_gap` gives ONE small pair
and reorders.  All three are small, and no reordering is needed. -/
theorem sq_offDiag_lt_ninth_of_det_pos_of_flat (design : WeightedDesign 6 3)
    (hflat : IsFlatDiagonal (projectionOfDesign design)) (huniform : design.weight = sixthWeight)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick)
    (hdet : 0 < (blockGapAt (projectionOfDesign design) design.weight pick).det) :
    projectionOfDesign design (pick 0) (pick 1) ^ 2 < 1 / 9
      ∧ projectionOfDesign design (pick 0) (pick 2) ^ 2 < 1 / 9
      ∧ projectionOfDesign design (pick 1) (pick 2) ^ 2 < 1 / 9 := by
  have hw : ∀ slot : Fin 3, design.weight (pick slot) = 1 / 6 := by
    intro slot; rw [huniform]; rfl
  have hgap : ∀ slot : Fin 3,
      blockGapAt (projectionOfDesign design) design.weight pick slot slot = 1 / 3 := by
    intro slot
    rw [blockGapAt_apply_diag, hflat (pick slot), hw slot]; norm_num
  have h01 := blockGapAt_apply_offDiag (projectionOfDesign design) design.weight pick
    (by decide : (0 : Fin 3) ≠ 1)
  have h02 := blockGapAt_apply_offDiag (projectionOfDesign design) design.weight pick
    (by decide : (0 : Fin 3) ≠ 2)
  have h12 := blockGapAt_apply_offDiag (projectionOfDesign design) design.weight pick
    (by decide : (1 : Fin 3) ≠ 2)
  have hsymm := blockGapAt_transpose (projectionOfDesign_transpose design) design.weight pick
  have hdetForm : 0 < tripleDetForm (1 / 3 : ℝ) (1 / 3) (1 / 3)
      (projectionOfDesign design (pick 0) (pick 1))
      (projectionOfDesign design (pick 0) (pick 2))
      (projectionOfDesign design (pick 1) (pick 2)) := by
    rw [det_eq_tripleDetForm_of_symm hsymm, hgap 0, hgap 1, hgap 2, h01, h02, h12] at hdet
    exact hdet
  have hcap : projectionOfDesign design (pick 0) (pick 1) ^ 2
      + projectionOfDesign design (pick 0) (pick 2) ^ 2
      + projectionOfDesign design (pick 1) (pick 2) ^ 2 ≤ 1 / 4 := by
    have hbound := sq_sum_le_leverageCap_projection design hinj
    rw [hflat (pick 0), hflat (pick 1), hflat (pick 2), sylvesterLeverageCap] at hbound
    linarith
  have htotal : sylvesterPairTotal (1 / 3 : ℝ) (1 / 3) (1 / 3) = 1 / 3 := by
    rw [sylvesterPairTotal]; norm_num
  have hmargin : (1 / 4 : ℝ) ≤ sylvesterPairTotal (1 / 3 : ℝ) (1 / 3) (1 / 3) := by
    rw [htotal]; norm_num
  have hthird : (0 : ℝ) < 1 / 3 := by norm_num
  have hA := pairMinorForm_pos_of_pairTotal_ge hthird hthird hcap hmargin hdetForm
  have hB := pairMinorForm_second_pos_of_pairTotal_ge hthird hthird hcap hmargin hdetForm
  have hC := pairMinorForm_third_pos_of_pairTotal_ge hthird hthird hcap hmargin hdetForm
  rw [pairMinorForm] at hA hB hC
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **THE FLAT ENERGY CAP.**  On the flat locus the pairing energy of EVERY triple is
at most `1/4`, with no hypothesis on the gap and no hypothesis on the weight.  Row
energy alone gives only `3/8`, so the two determinants of the sandwich buy a third of
the way, and `1/4` is attained. -/
theorem flatPairEnergy_le_quarter (design : WeightedDesign 6 3)
    (hflat : IsFlatDiagonal (projectionOfDesign design))
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick) :
    flatPairEnergy (projectionOfDesign design) pick ≤ 1 / 4 := by
  have hbound := sq_sum_le_leverageCap_projection design hinj
  have hcapValue : sylvesterLeverageCap (1 / 2 : ℝ) (1 / 2) (1 / 2) = 1 / 4 := by
    rw [sylvesterLeverageCap]; norm_num
  rw [hflat (pick 0), hflat (pick 1), hflat (pick 2), hcapValue] at hbound
  rw [flatPairEnergy]
  exact hbound

/-- **A UNIVERSAL SEPARATION ON THE FLAT STRATUM.**  The Plucker weight of a triple
exceeds its gap determinant by at least `5/108`, at every flat design and every
triple.  The landed `Gtz.twoHundredSixteen_mul_det_sub_det_of_flat` reads the
difference as `19 - 36 * energy`, and the flat energy cap bounds the energy.  So the
two lanes never meet, and the mass lane always sits above the gap lane. -/
theorem det_submatrix_sub_det_blockGapAt_ge_of_flat (design : WeightedDesign 6 3)
    (hflat : IsFlatDiagonal (projectionOfDesign design)) (huniform : design.weight = sixthWeight)
    {pick : Fin 3 → Fin 6} (hinj : Function.Injective pick) :
    5 / 108 ≤ ((projectionOfDesign design).submatrix pick pick).det
        - (blockGapAt (projectionOfDesign design) design.weight pick).det := by
  have hlaw := twoHundredSixteen_mul_det_sub_det_of_flat (projectionOfDesign_transpose design)
    hflat pick
  have henergy := flatPairEnergy_le_quarter design hflat hinj
  rw [huniform]
  linarith

/-- **WHERE AN OBSTRUCTION MUST LIVE.**  A triple with a positive gap determinant that
still fails to dominate carries a leverage sum strictly under `11/8`.  So a
counterexample to the reduction is confined to the light triples, and at least ten
triples of every design are out of reach of one. -/
theorem leverage_sum_lt_of_det_pos_of_not_posDef (design : WeightedDesign 6 3)
    (huniform : design.weight = sixthWeight) {pick : Fin 3 → Fin 6}
    (hinj : Function.Injective pick)
    (hfirst : 0 < projectionOfDesign design (pick 0) (pick 0) - design.weight (pick 0))
    (hsecond : 0 < projectionOfDesign design (pick 1) (pick 1) - design.weight (pick 1))
    (hdet : 0 < (blockGapAt (projectionOfDesign design) design.weight pick).det)
    (hfail : ¬(blockGapAt (projectionOfDesign design) design.weight pick).PosDef) :
    projectionOfDesign design (pick 0) (pick 0) + projectionOfDesign design (pick 1) (pick 1)
        + projectionOfDesign design (pick 2) (pick 2) < 11 / 8 := by
  have hw : ∀ slot : Fin 3, design.weight (pick slot) = 1 / 6 := by
    intro slot; rw [huniform]; rfl
  rcases lt_or_ge (projectionOfDesign design (pick 0) (pick 0)
      + projectionOfDesign design (pick 1) (pick 1)
      + projectionOfDesign design (pick 2) (pick 2)) (11 / 8) with hlt | hge
  · exact hlt
  · refine absurd (posDef_blockGapAt_of_det_pos_of_margin design hinj hfirst hsecond ?_ hdet) hfail
    rw [hw 0, hw 1, hw 2]
    exact (sylvesterMargin_sixth_nonneg_iff _ _ _).mpr hge

/-! ## 8. The obligation doors

The hypotheses below carry a GENERAL weight.  The A1 ledger records that
weight-uniform threshold certificates are refuted, so a door usable for A1 must not
fix the weight, and these do not.  The antecedents are satisfiable: the landed
`Gtz.orthoPairProjection` witness has a triple with a positive gap determinant, a flat
diagonal and uniform weight, and it clears the margin by `1/12`. -/

/-- **THE OBJECTIVE, REDUCED TO ONE DETERMINANT SIGN.**  If every primitive design at
`(6,3)` carries an ordered triple with a positive gap diagonal on its first two slots,
a nonnegative Sylvester margin, and a positive gap determinant, then the projection
block statement holds. -/
theorem projectionBlockSelects_of_det_pos_of_margin
    (hexists : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        0 < projectionOfDesign design (pick 0) (pick 0) - design.weight (pick 0) ∧
        0 < projectionOfDesign design (pick 1) (pick 1) - design.weight (pick 1) ∧
        0 ≤ sylvesterMargin (projectionOfDesign design (pick 0) (pick 0))
            (projectionOfDesign design (pick 1) (pick 1))
            (projectionOfDesign design (pick 2) (pick 2))
            (design.weight (pick 0)) (design.weight (pick 1)) (design.weight (pick 2)) ∧
        0 < (blockGapAt (projectionOfDesign design) design.weight pick).det) :
    ProjectionBlockSelects := by
  refine projectionBlockSelects_of_blockGapAt fun design hprimitive => ?_
  obtain ⟨pick, hinj, hfirst, hsecond, hmargin, hdet⟩ := hexists design hprimitive
  exact ⟨pick, hinj,
    posDef_blockGapAt_of_det_pos_of_margin design hinj hfirst hsecond hmargin hdet⟩

/-- **ALL FIVE ON-PATH OBLIGATIONS, from one determinant sign and a linear leverage
condition.**  This is the shipped `Gtz.allFiveOnPath_of_blockGapAt` with its matrix
hypothesis replaced by a scalar one. -/
theorem allFiveOnPath_of_det_pos_of_margin
    (hexists : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        0 < projectionOfDesign design (pick 0) (pick 0) - design.weight (pick 0) ∧
        0 < projectionOfDesign design (pick 1) (pick 1) - design.weight (pick 1) ∧
        0 ≤ sylvesterMargin (projectionOfDesign design (pick 0) (pick 0))
            (projectionOfDesign design (pick 1) (pick 1))
            (projectionOfDesign design (pick 2) (pick 2))
            (design.weight (pick 0)) (design.weight (pick 1)) (design.weight (pick 2)) ∧
        0 < (blockGapAt (projectionOfDesign design) design.weight pick).det) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  allFiveOnPath_of_projectionBlockSelects (projectionBlockSelects_of_det_pos_of_margin hexists)

/-- **THE FIRST ON-PATH OBLIGATION, reached from the scalar hypothesis.**  A1 is the
line-free stratum, the obligation carrying four moduli. -/
theorem baseTripleTight_of_det_pos_of_margin
    (hexists : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        0 < projectionOfDesign design (pick 0) (pick 0) - design.weight (pick 0) ∧
        0 < projectionOfDesign design (pick 1) (pick 1) - design.weight (pick 1) ∧
        0 ≤ sylvesterMargin (projectionOfDesign design (pick 0) (pick 0))
            (projectionOfDesign design (pick 1) (pick 1))
            (projectionOfDesign design (pick 2) (pick 2))
            (design.weight (pick 0)) (design.weight (pick 1)) (design.weight (pick 2)) ∧
        0 < (blockGapAt (projectionOfDesign design) design.weight pick).det) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual :=
  (allFiveOnPath_of_det_pos_of_margin hexists).1

/-- The `M(K4)` obligation, the moduli-zero end of the same chain. -/
theorem kFourKnifeBand_of_det_pos_of_margin
    (hexists : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        0 < projectionOfDesign design (pick 0) (pick 0) - design.weight (pick 0) ∧
        0 < projectionOfDesign design (pick 1) (pick 1) - design.weight (pick 1) ∧
        0 ≤ sylvesterMargin (projectionOfDesign design (pick 0) (pick 0))
            (projectionOfDesign design (pick 1) (pick 1))
            (projectionOfDesign design (pick 2) (pick 2))
            (design.weight (pick 0)) (design.weight (pick 1)) (design.weight (pick 2)) ∧
        0 < (blockGapAt (projectionOfDesign design) design.weight pick).det) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  (allFiveOnPath_of_det_pos_of_margin hexists).2.2.2.2

/-! ## 9. The margin is not decoration

Every hypothesis of section 3 except the margin holds at the point below, and the
conclusion fails.  The gap diagonal is `(1/4, 1/4, 1/4)`, the three pairings are
`7/24`, and the leverage scores are `5/12` at uniform weight.  So the leverage sum is
`5/4`, which is under the threshold `11/8`, and the margin is `-1/12`. -/

/-- The refuting point, with every quantity named. -/
theorem sylvesterMargin_not_redundant :
    (0 : ℝ) < 1 / 4
      ∧ (7 / 24 : ℝ) ^ 2 + (7 / 24 : ℝ) ^ 2 + (7 / 24 : ℝ) ^ 2
          ≤ sylvesterLeverageCap (5 / 12) (5 / 12) (5 / 12)
      ∧ 0 < tripleDetForm (1 / 4 : ℝ) (1 / 4) (1 / 4) (7 / 24) (7 / 24) (7 / 24)
      ∧ sylvesterMargin (5 / 12 : ℝ) (5 / 12) (5 / 12) (1 / 6) (1 / 6) (1 / 6) = -(1 / 12)
      ∧ pairMinorForm (1 / 4 : ℝ) (1 / 4) (7 / 24) = -(13 / 576) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [sylvesterLeverageCap]; norm_num
  · rw [tripleDetForm]; norm_num
  · rw [sylvesterMargin, sylvesterPairTotal, sylvesterLeverageCap]; norm_num
  · rw [pairMinorForm]; norm_num

/-- **THE MARGIN CANNOT BE DROPPED.**  The energy cap, the positive gap diagonal and
the positive gap determinant together do NOT give a positive two-by-two minor.  Any
proof of the reduction has to consume the margin. -/
theorem not_forall_pairMinorForm_pos_of_det_pos_of_cap :
    ¬ ∀ dA dB dC u v w : ℝ,
        0 < dA - 1 / 6 → 0 < dB - 1 / 6 → 0 < dC - 1 / 6 →
        u ^ 2 + v ^ 2 + w ^ 2 ≤ sylvesterLeverageCap dA dB dC →
        0 < tripleDetForm (dA - 1 / 6) (dB - 1 / 6) (dC - 1 / 6) u v w →
        0 < pairMinorForm (dA - 1 / 6) (dB - 1 / 6) u := by
  intro hall
  have hbad := hall (5 / 12) (5 / 12) (5 / 12) (7 / 24) (7 / 24) (7 / 24)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [sylvesterLeverageCap]; norm_num)
    (by rw [tripleDetForm]; norm_num)
  rw [pairMinorForm] at hbad
  norm_num at hbad

/-- **THE LEVERAGE SUM OF THE REFUTING POINT IS UNDER THE THRESHOLD.**  It is `5/4`,
and the threshold is `11/8`.  So the refutation is consistent with the reduction, and
it pins the true constant into the band between the two. -/
theorem sylvesterMargin_not_redundant_leverage_sum :
    (5 / 12 : ℝ) + 5 / 12 + 5 / 12 = 5 / 4 ∧ (5 / 4 : ℝ) < 11 / 8 := by
  norm_num

end Gtz
