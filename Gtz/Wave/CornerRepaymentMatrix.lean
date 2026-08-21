/-
# The repayment matrix: the three one-inside gap determinants are a DIAGONAL

The corank-two arm's remaining existence fact is E2 -- at a corner, some inside
atom REPAYS an admissible outside pair, `0 < tripleGapDet a b g_e` for some
`e` in the dominator.  Every instrument the arm ever found for it was the SUM
`sum_e tripleGapDet a b g_e`, and the sum is blind: it fires at only about nine
corners in ten.  The reason it was the only instrument is a landed theorem of
the lane -- the corner and its pair determine the first symmetric function of
the three determinants and NOTHING else.

This module explains that, and replaces it.  The three determinants are the
DIAGONAL of a single symmetric three-by-three matrix

  **`Gtz.repayEntry`:  `X_ef = D*c_e*c_f - Phi(r_e, r_f)`**

where `D = pairGapMinor a b`, `c` is the axis reading vector of the corner,
`r_e = (a . g_e, b . g_e)` are the pair readings, and `Phi` is the polarized
axis form of the pair.  `Gtz.repayEntry_diag_eq_tripleGapDet` proves the
diagonal claim.  Once the three numbers are a diagonal, the whole picture
follows from linear algebra rather than from search.

## What the matrix knows that its diagonal does not

* **The determinant is a perfect square** (`Gtz.repayEntry_det`):

    `det X = D^2 * readingBracket(c, al, be)^2`  ,

  hypothesis-free, one `ring`.  And the reading bracket factors by Cauchy-Binet
  (`Gtz.readingBracket_eq_bracket_mul`) into the AMBIENT brackets:

    `readingBracket = [u, a, b] * [g_1, g_2, g_3]`  ,

  so at a corner `det X = lam * D^2 * [u,a,b]^2` -- the arm's terminal currency,
  and a quantity the corner and its pair DO determine.
* **The form is capped by the axis** (`Gtz.repayEntry_form_le`): for every
  coordinate vector `x`,  `x' X x <= D * (c . x)^2`.  On an admissible pair the
  subtracted part is a positive semidefinite form, so `X` is nonpositive on the
  whole plane `c^perp`.  A corner's inside gap is rank one, so this says the
  repayment matrix has AT MOST ONE positive direction, and the gauge freedom of
  the corner is exactly the freedom to move the diagonal inside that spectrum.

## The producer that replaces the sum

A positive weighted sum of three reals that is positive has a positive term.
So ANY strictly positive weighting is a producer (`Gtz.exists_repay_of_weighted_sum_pos`,
`Gtz.subsetSum_posDef_of_weighted_repay`), and the plain sum is the single
weakest member of that family -- the weighting `omega = 1`.

[MEASURED on 40000 complement-refusing corners of the CORRECTED chart (the
older samplers pinned `lambda_min(N_O) >= 0.7` and could not reach the refusing
region at all).  Fire rate of "some admissible pair has positive weighted sum":

    omega = (t_e*l_e)^2      99.9725%        omega = t_e*(l_e-1)   99.7175%
    omega = t_e*l_e/(1-t_e)  99.9475%        omega = t_e           99.4850%
    omega = t_e + t_e*l_e    99.8900%        omega = l_e           95.0400%
    omega = t_e*l_e          99.8600%        omega = 1             90.7600%

against E2* itself at 100.0000%.  The design weights carry the instrument from
90.8% to 99.97%, which is what F49-8 predicted: the missing ingredient is the
Parseval equation, and a weighting is how it enters.  No weighting in the table
is total, so none of them is the theorem -- they are producers, and the residual
is recorded in scratchpad/NOTES-f68-etwo.txt.]

[ACCEPTANCE TEST PASSED.  At the reconstructed complex corank-two corner tie
(scratchpad/NOTES-f68-etwo.txt) every diagonal entry is negative on every
admissible pair -- `-3.36889, -2.46554, -2.65433`, `-5.90858, -4.51335,
-2.66467`, `-4.69841, -4.23306, -2.21968` -- and no weighting in the table
fires.  A law that fired there would be refuted, since E2* is false at that
point.]
-/
import Gtz.Wave.CornerPairAdjugate
import Gtz.Design.TripleGramSylvester

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The reading bracket, and Cauchy-Binet

Three probes read a triple of atoms into a three-by-three array.  Its
determinant factors into the two ambient brackets. -/

/-- The bracket of three reading vectors, as a determinant in the index space. -/
noncomputable def readingBracket (c₁ c₂ c₃ al₁ al₂ al₃ be₁ be₂ be₃ : ℝ) : ℝ :=
  c₁ * (al₂ * be₃ - al₃ * be₂) - c₂ * (al₁ * be₃ - al₃ * be₁)
    + c₃ * (al₁ * be₂ - al₂ * be₁)

/-- **THE READING BRACKET FACTORS.**  Cauchy-Binet at rank three: the three
probes read the three atoms into an array whose determinant is the product of
the probes' own bracket with the atoms' bracket.  One `ring`, no hypotheses. -/
theorem readingBracket_eq_bracket_mul (u a b g₁ g₂ g₃ : Fin 3 → ℝ) :
    readingBracket (u ⬝ᵥ g₁) (u ⬝ᵥ g₂) (u ⬝ᵥ g₃)
        (a ⬝ᵥ g₁) (a ⬝ᵥ g₂) (a ⬝ᵥ g₃) (b ⬝ᵥ g₁) (b ⬝ᵥ g₂) (b ⬝ᵥ g₃)
      = tripleBracket u a b * tripleBracket g₁ g₂ g₃ := by
  simp only [readingBracket, tripleBracket, Matrix.det_fin_three, dotProduct,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The reading bracket is linear in its first slot, so a rescaled axis rescales
it.  This is the only scaling the corner's axis normalization needs. -/
theorem readingBracket_smul_first (s c₁ c₂ c₃ al₁ al₂ al₃ be₁ be₂ be₃ : ℝ) :
    readingBracket (s * c₁) (s * c₂) (s * c₃) al₁ al₂ al₃ be₁ be₂ be₃
      = s * readingBracket c₁ c₂ c₃ al₁ al₂ al₃ be₁ be₂ be₃ := by
  simp only [readingBracket]; ring

/-! ## 2. The repayment matrix

Its entries are written in the pair's own scalars: the two leverages, the
pairing, and the readings.  Keeping them abstract is what lets `ring` see the
determinant identity. -/

/-- The polarized axis form of a pair, at two reading vectors.  Its diagonal is
the landed `Gtz.pairAxisForm`. -/
noncomputable def pairAxisPolar (la lb p alI beI alJ beJ : ℝ) : ℝ :=
  (1 - lb) * alI * alJ + p * (alI * beJ + beI * alJ) + (1 - la) * beI * beJ

/-- The polarized form on the diagonal is the axis form. -/
theorem pairAxisPolar_diag (la lb p al be : ℝ) :
    pairAxisPolar la lb p al be al be
      = (1 - lb) * al ^ 2 + 2 * p * al * be + (1 - la) * be ^ 2 := by
  simp only [pairAxisPolar]; ring

/-- The polarized form is symmetric in its two reading slots. -/
theorem pairAxisPolar_comm (la lb p alI beI alJ beJ : ℝ) :
    pairAxisPolar la lb p alI beI alJ beJ = pairAxisPolar la lb p alJ beJ alI beI := by
  simp only [pairAxisPolar]; ring

/-- **THE REPAYMENT MATRIX ENTRY.**  The pair minor against the axis readings,
plus the polarized axis form at the two pair readings. -/
noncomputable def repayEntry (la lb p cI cJ alI beI alJ beJ : ℝ) : ℝ :=
  ((la - 1) * (lb - 1) - p ^ 2) * cI * cJ + pairAxisPolar la lb p alI beI alJ beJ

/-- The repayment matrix is symmetric. -/
theorem repayEntry_comm (la lb p cI cJ alI beI alJ beJ : ℝ) :
    repayEntry la lb p cI cJ alI beI alJ beJ = repayEntry la lb p cJ cI alJ beJ alI beI := by
  simp only [repayEntry, pairAxisPolar]; ring

/-- **THE DIAGONAL IS THE GAP DETERMINANT.**  With the axis reading squaring to
the atom's leverage excess -- which is exactly the corner's own axis law -- the
`e`-th diagonal entry of the repayment matrix is the one-inside gap determinant
`tripleGapDet a b g_e`.  So the three numbers the arm has been hunting are a
diagonal, and every invariant of the matrix is available to it. -/
theorem repayEntry_diag_eq_tripleGapDet (a b g : Fin 3 → ℝ) {c : ℝ}
    (hc : c ^ 2 = leverageOf g - 1) :
    repayEntry (leverageOf a) (leverageOf b) (a ⬝ᵥ b) c c
        (a ⬝ᵥ g) (b ⬝ᵥ g) (a ⬝ᵥ g) (b ⬝ᵥ g)
      = tripleGapDet a b g := by
  rw [tripleGapDet_eq_pairAxisForm]
  simp only [repayEntry, pairAxisPolar, pairAxisForm, pairGapMinor]
  linear_combination ((leverageOf a - 1) * (leverageOf b - 1) - (a ⬝ᵥ b) ^ 2) * hc

/-! ## 3. The determinant is a perfect square -/

/-- **THE REPAYMENT DETERMINANT.**  The determinant of the repayment matrix is
the squared pair minor times the squared reading bracket.  Hypothesis-free, and
one `ring` after the three-by-three expansion.

The mechanism is that the subtracted part has rank at most two -- it is built
from the two reading vectors alone -- so the only surviving term of the rank-one
update is the adjugate reading, and that adjugate is the squared reading
bracket times the pair minor. -/
theorem repayEntry_det (la lb p c₁ c₂ c₃ al₁ al₂ al₃ be₁ be₂ be₃ : ℝ) :
    (!![repayEntry la lb p c₁ c₁ al₁ be₁ al₁ be₁,
        repayEntry la lb p c₁ c₂ al₁ be₁ al₂ be₂,
        repayEntry la lb p c₁ c₃ al₁ be₁ al₃ be₃;
        repayEntry la lb p c₂ c₁ al₂ be₂ al₁ be₁,
        repayEntry la lb p c₂ c₂ al₂ be₂ al₂ be₂,
        repayEntry la lb p c₂ c₃ al₂ be₂ al₃ be₃;
        repayEntry la lb p c₃ c₁ al₃ be₃ al₁ be₁,
        repayEntry la lb p c₃ c₂ al₃ be₃ al₂ be₂,
        repayEntry la lb p c₃ c₃ al₃ be₃ al₃ be₃]).det
      = ((la - 1) * (lb - 1) - p ^ 2) ^ 2
        * readingBracket c₁ c₂ c₃ al₁ al₂ al₃ be₁ be₂ be₃ ^ 2 := by
  simp only [Matrix.det_fin_three, repayEntry, pairAxisPolar, readingBracket,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-! ## 4. The form is capped by the axis

The subtracted part of the repayment matrix is a positive semidefinite form on
an admissible pair, so the whole matrix is nonpositive wherever the axis
reading vanishes. -/

/-- **THE SUBTRACTED FORM IS POSITIVE SEMIDEFINITE ON AN ADMISSIBLE PAIR.**  Its
matrix is the adjugate of the pair gap block, and a nonnegative pair minor with
BOTH atoms heavy makes that adjugate positive semidefinite.

Both heavy is necessary, not decorative: at `lb = 1` a nonnegative pair minor
forces the pairing to vanish and the form collapses to `(1 - la) * Y ^ 2`, which
is POSITIVE when the other atom is light.  The landed
`Gtz.one_lt_leverage_of_pairGapMinor_pos` supplies heaviness from a strictly
positive minor, so no caller pays for the extra hypothesis. -/
theorem pairAxisPolar_neg_nonneg {la lb p : ℝ} (ha : 1 ≤ la) (hb : 1 ≤ lb)
    (hmin : 0 ≤ (la - 1) * (lb - 1) - p ^ 2) (X Y : ℝ) :
    pairAxisPolar la lb p X Y X Y ≤ 0 := by
  simp only [pairAxisPolar]
  rcases eq_or_lt_of_le hb with heq | hlt
  · have hp : p = 0 := by nlinarith [sq_nonneg p]
    rw [hp, ← heq]; nlinarith [sq_nonneg Y]
  · have hpos : 0 < lb - 1 := by linarith
    have key : 0 ≤ (lb - 1) * (-((1 - lb) * X * X + p * (X * Y + Y * X)
        + (1 - la) * Y * Y)) := by
      nlinarith [sq_nonneg ((lb - 1) * X - p * Y), mul_nonneg hmin (sq_nonneg Y)]
    nlinarith [key, hpos]

/-- **THE REPAYMENT FORM IS CAPPED BY THE AXIS.**  For every coordinate vector
the repayment form is at most the pair minor times the squared axis reading.  On
the plane where the axis reading vanishes the form is nonpositive, so at a
corner -- where the inside gap is rank one -- the repayment matrix has at most
one positive direction.  That is the exact shape of the gauge freedom the lane
measured: the spectrum is pinned and only the diagonal moves. -/
theorem repayEntry_form_le {la lb p : ℝ} (ha : 1 ≤ la) (hb : 1 ≤ lb)
    (hmin : 0 ≤ (la - 1) * (lb - 1) - p ^ 2)
    (c₁ c₂ c₃ al₁ al₂ al₃ be₁ be₂ be₃ x₁ x₂ x₃ : ℝ) :
    x₁ * (x₁ * repayEntry la lb p c₁ c₁ al₁ be₁ al₁ be₁
          + x₂ * repayEntry la lb p c₁ c₂ al₁ be₁ al₂ be₂
          + x₃ * repayEntry la lb p c₁ c₃ al₁ be₁ al₃ be₃)
      + x₂ * (x₁ * repayEntry la lb p c₂ c₁ al₂ be₂ al₁ be₁
          + x₂ * repayEntry la lb p c₂ c₂ al₂ be₂ al₂ be₂
          + x₃ * repayEntry la lb p c₂ c₃ al₂ be₂ al₃ be₃)
      + x₃ * (x₁ * repayEntry la lb p c₃ c₁ al₃ be₃ al₁ be₁
          + x₂ * repayEntry la lb p c₃ c₂ al₃ be₃ al₂ be₂
          + x₃ * repayEntry la lb p c₃ c₃ al₃ be₃ al₃ be₃)
      ≤ ((la - 1) * (lb - 1) - p ^ 2) * (c₁ * x₁ + c₂ * x₂ + c₃ * x₃) ^ 2 := by
  have hform := pairAxisPolar_neg_nonneg ha hb hmin
    (x₁ * al₁ + x₂ * al₂ + x₃ * al₃) (x₁ * be₁ + x₂ * be₂ + x₃ * be₃)
  simp only [repayEntry, pairAxisPolar] at *
  nlinarith [hform]

/-! ## 5. The producer: any strictly positive weighting -/

/-- **A POSITIVE WEIGHTED SUM HAS A POSITIVE TERM.**  The elementary fact that
turns every strictly positive weighting into a producer for the repayment.  The
landed sum law is the member with all weights one, and it is the weakest one:
the design weights carry the same instrument from `90.8%` to `99.97%`. -/
theorem exists_pos_of_weighted_sum_pos {w₁ w₂ w₃ d₁ d₂ d₃ : ℝ}
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₃ : 0 < w₃)
    (hsum : 0 < w₁ * d₁ + w₂ * d₂ + w₃ * d₃) :
    0 < d₁ ∨ 0 < d₂ ∨ 0 < d₃ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h₁, h₂, h₃⟩ := hcon
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hw₁.le h₁,
    mul_nonpos_of_nonneg_of_nonpos hw₂.le h₂,
    mul_nonpos_of_nonneg_of_nonpos hw₃.le h₃]

/-- **THE WEIGHTED REPAYMENT PRODUCER.**  A strictly positive weighting whose
weighted total of the three one-inside gap determinants is positive names a
repaying inside atom. -/
theorem exists_repay_of_weighted_sum_pos (a b g₁ g₂ g₃ : Fin 3 → ℝ)
    {w₁ w₂ w₃ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₃ : 0 < w₃)
    (hsum : 0 < w₁ * tripleGapDet a b g₁ + w₂ * tripleGapDet a b g₂
              + w₃ * tripleGapDet a b g₃) :
    0 < tripleGapDet a b g₁ ∨ 0 < tripleGapDet a b g₂ ∨ 0 < tripleGapDet a b g₃ :=
  exists_pos_of_weighted_sum_pos hw₁ hw₂ hw₃ hsum

/-- **THE STRICT DOMINATOR FROM A WEIGHTED TOTAL.**  An admissible pair whose
three one-inside gap determinants have a positive weighted total gives a triple
whose Gram gap is positive definite.  Routed through the landed pair-only
Sylvester criterion, so no new positive-definiteness machinery is spent. -/
theorem tripleGram_posDef_of_weighted_repay {a b g₁ g₂ g₃ : Fin 3 → ℝ}
    (ha : 1 < leverageOf a) (hmin : 0 < pairGapMinor a b)
    {w₁ w₂ w₃ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₃ : 0 < w₃)
    (hsum : 0 < w₁ * tripleGapDet a b g₁ + w₂ * tripleGapDet a b g₂
              + w₃ * tripleGapDet a b g₃) :
    (tripleGram a b g₁ - 1).PosDef ∨ (tripleGram a b g₂ - 1).PosDef
      ∨ (tripleGram a b g₃ - 1).PosDef := by
  rcases exists_repay_of_weighted_sum_pos a b g₁ g₂ g₃ hw₁ hw₂ hw₃ hsum with h | h | h
  · exact Or.inl ((tripleGram_posDef_iff_pairVocabulary a b g₁).mpr ⟨by linarith, hmin, h⟩)
  · exact Or.inr (Or.inl ((tripleGram_posDef_iff_pairVocabulary a b g₂).mpr
      ⟨by linarith, hmin, h⟩))
  · exact Or.inr (Or.inr ((tripleGram_posDef_iff_pairVocabulary a b g₃).mpr
      ⟨by linarith, hmin, h⟩))

/-- **THE DESIGN READING.**  At a design, an admissible pair whose three
one-inside gap determinants carry a positive weighted total produces a strictly
dominating triple, hence refutes the tie. -/
theorem subsetSum_posDef_of_weighted_repay (D : WeightedDesign m 3)
    {x y : Fin m} {z₁ z₂ z₃ : Fin m}
    (hxy₁ : x ≠ y) (hxz₁ : x ≠ z₁) (hyz₁ : y ≠ z₁)
    (hxz₂ : x ≠ z₂) (hyz₂ : y ≠ z₂) (hxz₃ : x ≠ z₃) (hyz₃ : y ≠ z₃)
    (ha : 1 < leverageOf (D.atom x)) (hmin : 0 < pairGapMinor (D.atom x) (D.atom y))
    {w₁ w₂ w₃ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₃ : 0 < w₃)
    (hsum : 0 < w₁ * tripleGapDet (D.atom x) (D.atom y) (D.atom z₁)
              + w₂ * tripleGapDet (D.atom x) (D.atom y) (D.atom z₂)
              + w₃ * tripleGapDet (D.atom x) (D.atom y) (D.atom z₃)) :
    (subsetSum D ({x, y, z₁} : Finset (Fin m)) - 1).PosDef
      ∨ (subsetSum D ({x, y, z₂} : Finset (Fin m)) - 1).PosDef
      ∨ (subsetSum D ({x, y, z₃} : Finset (Fin m)) - 1).PosDef := by
  rcases exists_repay_of_weighted_sum_pos (D.atom x) (D.atom y) (D.atom z₁)
      (D.atom z₂) (D.atom z₃) hw₁ hw₂ hw₃ hsum with h | h | h
  · exact Or.inl ((subsetSum_posDef_iff_pairVocabulary D x y z₁ hxy₁ hxz₁ hyz₁).mpr
      ⟨by linarith, hmin, h⟩)
  · exact Or.inr (Or.inl ((subsetSum_posDef_iff_pairVocabulary D x y z₂ hxy₁ hxz₂ hyz₂).mpr
      ⟨by linarith, hmin, h⟩))
  · exact Or.inr (Or.inr ((subsetSum_posDef_iff_pairVocabulary D x y z₃ hxy₁ hxz₃ hyz₃).mpr
      ⟨by linarith, hmin, h⟩))

/-! ## 6. What a corner tie must pay

A tie has no strictly dominating triple, so at a tie EVERY strictly positive
weighting of every admissible pair has a nonpositive total.  That is a family of
inequalities the corner must satisfy, one for each weighting, and the landed sum
law is the single member with unit weights. -/

/-- **A TIE KILLS EVERY POSITIVE WEIGHTING.**  If no triple through an
admissible pair dominates strictly, then every strictly positive weighting of
the three one-inside gap determinants has a nonpositive total.  The contrapositive
of the producer, and the exact obligation a corank-two corner tie carries. -/
theorem weighted_sum_nonpos_of_no_repay {a b g₁ g₂ g₃ : Fin 3 → ℝ}
    (h₁ : tripleGapDet a b g₁ ≤ 0) (h₂ : tripleGapDet a b g₂ ≤ 0)
    (h₃ : tripleGapDet a b g₃ ≤ 0) {w₁ w₂ w₃ : ℝ}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) :
    w₁ * tripleGapDet a b g₁ + w₂ * tripleGapDet a b g₂
      + w₃ * tripleGapDet a b g₃ ≤ 0 := by
  have p₁ := mul_nonpos_of_nonneg_of_nonpos hw₁ h₁
  have p₂ := mul_nonpos_of_nonneg_of_nonpos hw₂ h₂
  have p₃ := mul_nonpos_of_nonneg_of_nonpos hw₃ h₃
  linarith

/-- **THE BRACKET FORM OF THE REPAYMENT DETERMINANT.**  Composing the
determinant identity with Cauchy-Binet writes the repayment determinant in the
arm's terminal currency: the squared pair minor, the squared bracket of the axis
against the outside pair, and the squared bracket of the dominator.  Every
factor is a quantity the corner and its pair determine, which is what the
diagonal alone never was. -/
theorem repayEntry_det_bracket (u a b g₁ g₂ g₃ : Fin 3 → ℝ) :
    (!![repayEntry (leverageOf a) (leverageOf b) (a ⬝ᵥ b) (u ⬝ᵥ g₁) (u ⬝ᵥ g₁)
          (a ⬝ᵥ g₁) (b ⬝ᵥ g₁) (a ⬝ᵥ g₁) (b ⬝ᵥ g₁),
        repayEntry (leverageOf a) (leverageOf b) (a ⬝ᵥ b) (u ⬝ᵥ g₁) (u ⬝ᵥ g₂)
          (a ⬝ᵥ g₁) (b ⬝ᵥ g₁) (a ⬝ᵥ g₂) (b ⬝ᵥ g₂),
        repayEntry (leverageOf a) (leverageOf b) (a ⬝ᵥ b) (u ⬝ᵥ g₁) (u ⬝ᵥ g₃)
          (a ⬝ᵥ g₁) (b ⬝ᵥ g₁) (a ⬝ᵥ g₃) (b ⬝ᵥ g₃);
        repayEntry (leverageOf a) (leverageOf b) (a ⬝ᵥ b) (u ⬝ᵥ g₂) (u ⬝ᵥ g₁)
          (a ⬝ᵥ g₂) (b ⬝ᵥ g₂) (a ⬝ᵥ g₁) (b ⬝ᵥ g₁),
        repayEntry (leverageOf a) (leverageOf b) (a ⬝ᵥ b) (u ⬝ᵥ g₂) (u ⬝ᵥ g₂)
          (a ⬝ᵥ g₂) (b ⬝ᵥ g₂) (a ⬝ᵥ g₂) (b ⬝ᵥ g₂),
        repayEntry (leverageOf a) (leverageOf b) (a ⬝ᵥ b) (u ⬝ᵥ g₂) (u ⬝ᵥ g₃)
          (a ⬝ᵥ g₂) (b ⬝ᵥ g₂) (a ⬝ᵥ g₃) (b ⬝ᵥ g₃);
        repayEntry (leverageOf a) (leverageOf b) (a ⬝ᵥ b) (u ⬝ᵥ g₃) (u ⬝ᵥ g₁)
          (a ⬝ᵥ g₃) (b ⬝ᵥ g₃) (a ⬝ᵥ g₁) (b ⬝ᵥ g₁),
        repayEntry (leverageOf a) (leverageOf b) (a ⬝ᵥ b) (u ⬝ᵥ g₃) (u ⬝ᵥ g₂)
          (a ⬝ᵥ g₃) (b ⬝ᵥ g₃) (a ⬝ᵥ g₂) (b ⬝ᵥ g₂),
        repayEntry (leverageOf a) (leverageOf b) (a ⬝ᵥ b) (u ⬝ᵥ g₃) (u ⬝ᵥ g₃)
          (a ⬝ᵥ g₃) (b ⬝ᵥ g₃) (a ⬝ᵥ g₃) (b ⬝ᵥ g₃)]).det
      = pairGapMinor a b ^ 2
        * (tripleBracket u a b * tripleBracket g₁ g₂ g₃) ^ 2 := by
  rw [repayEntry_det, ← readingBracket_eq_bracket_mul u a b g₁ g₂ g₃]
  rw [pairGapMinor]

end Gtz
