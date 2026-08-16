import Gtz.Quantitative.CauchyBinetValueFloor
import Gtz.Quantitative.ProjectionBasisCoordinates
import Gtz.Wave.TripleDeterminantCells
import Gtz.Wave.SelectionMarginLaws
import Gtz.Wave.SignBlindCeiling

/-!
# Quantitative margin bounds: turning a determinant floor into a margin floor

Every cell this campaign has shipped proves a block gap POSITIVE and stops.  A
conditional floor on the selection margin needs a NUMBER, not a sign.  This file
supplies the conversion and two quantitative cells.

**The bridge.**  The block gap `Z_C = P[C] - diag w_C` of a design is a
contraction, because `1 - Z_C = (1 - P)[C] + diag w_C` is a sum of two positive
semidefinite matrices.  The shipped
`Gtz.det_le_eigenvalue_of_posSemidef_of_posSemidef_one_sub` then puts `det Z_C`
below EVERY eigenvalue of `Z_C`.  So a lower bound on one determinant is a lower
bound on the margin, and `Gtz.marginReaches_of_lt_det_projectionBlockGap` feeds
it straight into the shipped `Gtz.MarginReaches`.  That trades a spectral
quantity for a polynomial one, which is what a floor argument can use.

**The slack-ratio cell, root-free.**  The shipped quarter-slack cell asks
`4 u^2 < p q` at all three pairs and returns positivity.  Carrying the ratio
through gives a number.  Writing the ratio as `s^2` keeps every step polynomial:
under `s^2 u^2 <= p q` at all three pairs,

  `s^3 * tripleDetForm p q r u v w  >=  p q r (s+1)^2 (s-2)`.

The cubic `s^3 - 3 s - 2` factors as `(s+1)^2 (s-2)`, so the bound is positive
exactly for `s > 2`, which recovers the shipped constant four as `s^2`.  No
square root appears anywhere.

**The diagonal-shift residual.**  The shipped `Gtz.det_sub_diagonal_fin_three`
expands `det (M - diag d)` into a linear part and a remainder.  That remainder is
`Gtz.detShiftResidual`, and dropping it leaves
`det (M - diag d) >= det M - sum_c d_c * minor_c`.  Heaviness of the three labels
is SUFFICIENT for the remainder to be nonnegative and it is NOT necessary, which
`Gtz.not_forall_detShiftLinear_le_det_sub_diagonal` witnesses at an explicit
rational point.

**The sharp sum cell, made quantitative.**  The shipped
`Gtz.signFreeMargin_pos_of_weightedPairEnergy_lt` reads one inequality and
returns a sign.  Its two ingredients — the cube bound on the cross term and the
factorisation `27 E^2 T - 4 (T - E)^3 = (4 E - T) (E + 2 T)^2` — already carry a
number, and keeping it gives `Gtz.slack_mul_sq_le_sharpSum`, which needs NO cell
hypothesis at all.  Under the cell, `Gtz.sharpSumSlack_le_signFreeMargin` turns
that into a lower bound on the sign-free margin itself, in the cell's own slack
`4 E - T`.

**What these bounds do not reach.**  The sign-free margin is at most the
determinant, and the shipped `Gtz.residue_iff` names the gap exactly: a triple
with positive determinant and non-positive margin has `0 < u v w`.  So every
bound here covers every triple with a nonpositive triple product exactly, and the
coherent triples inside that interval are handed over rather than stretched to.
-/

namespace Gtz

open Matrix Finset Pointwise

/-! ## 1. The strict Loewner shift -/

/-- The strict companion of `Gtz.posSemidef_sub_smul_one_of_eigenvalue_ge`: a
level strictly below every eigenvalue gives a positive definite shift. -/
theorem posDef_sub_smul_one_of_eigenvalue_gt {dim : ℕ} {form : Matrix (Fin dim) (Fin dim) ℝ}
    (hHermitian : form.IsHermitian) (level : ℝ)
    (hFloor : ∀ eigenIndex, level < hHermitian.eigenvalues eigenIndex) :
    (form - level • (1 : Matrix (Fin dim) (Fin dim) ℝ)).PosDef := by
  have hShiftHermitian := isHermitian_sub_smul_one hHermitian level
  refine hShiftHermitian.posDef_iff_eigenvalues_pos.mpr ?_
  intro shiftIndex
  have hScalar : (level : ℝ) • (1 : Matrix (Fin dim) (Fin dim) ℝ)
      = algebraMap ℝ (Matrix (Fin dim) (Fin dim) ℝ) level :=
    (Algebra.algebraMap_eq_smul_one level).symm
  have hMember : hShiftHermitian.eigenvalues shiftIndex
      ∈ Set.range hHermitian.eigenvalues - ({level} : Set ℝ) := by
    rw [← hHermitian.spectrum_real_eq_range_eigenvalues, spectrum.sub_singleton_eq, ← hScalar]
    exact hShiftHermitian.eigenvalues_mem_spectrum_real shiftIndex
  obtain ⟨originalValue, hOriginal, shiftAmount, hShiftAmount, hDecompose⟩ := hMember
  obtain ⟨originalIndex, hOriginalIndex⟩ := hOriginal
  simp only [Set.mem_singleton_iff] at hShiftAmount
  subst hShiftAmount
  linarith [hFloor originalIndex, hOriginalIndex ▸ hDecompose]

/-! ## 2. The block gap is a contraction -/

variable {size rank : ℕ}

/-- The block gap of a design, along an arbitrary index map: `P[C] - diag w_C`.
This is `Gtz.projectionBlockGap` with the selection presented as a map rather
than a `Finset`, which is the shape the margin object uses. -/
noncomputable def pickBlockGap (design : WeightedDesign size rank) {chosen : ℕ}
    (pick : Fin chosen → Fin size) : Matrix (Fin chosen) (Fin chosen) ℝ :=
  (projectionOfDesign design).submatrix pick pick
    - Matrix.diagonal (fun slot => design.weight (pick slot))

theorem pickBlockGap_apply (design : WeightedDesign size rank) {chosen : ℕ}
    (pick : Fin chosen → Fin size) (left right : Fin chosen) :
    pickBlockGap design pick left right
      = projectionOfDesign design (pick left) (pick right)
        - (if left = right then design.weight (pick left) else 0) := by
  simp [pickBlockGap, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.diagonal_apply]

/-- The projection form is entrywise symmetric. -/
theorem projectionOfDesign_symm (design : WeightedDesign size rank) (left right : Fin size) :
    projectionOfDesign design right left = projectionOfDesign design left right := by
  have := congrFun (congrFun (projectionOfDesign_transpose design) left) right
  simpa [Matrix.transpose_apply] using this

theorem isHermitian_pickBlockGap (design : WeightedDesign size rank) {chosen : ℕ}
    (pick : Fin chosen → Fin size) : (pickBlockGap design pick).IsHermitian := by
  ext left right
  simp only [Matrix.conjTranspose_apply, star_trivial, pickBlockGap, Matrix.sub_apply,
    Matrix.submatrix_apply, Matrix.diagonal_apply, projectionOfDesign_symm design (pick left)]
  rcases eq_or_ne left right with rfl | hne
  · simp
  · rw [if_neg hne, if_neg (Ne.symm hne)]

/-- The weight diagonal is positive semidefinite. -/
theorem posSemidef_weightDiagonal (design : WeightedDesign size rank) {chosen : ℕ}
    (pick : Fin chosen → Fin size) :
    (Matrix.diagonal (fun slot => design.weight (pick slot))).PosSemidef :=
  Matrix.posSemidef_diagonal_iff.mpr fun slot => (design.weight_pos (pick slot)).le

/-- **THE CONTRACTION.**  `1 - (P[C] - diag w_C) = (1 - P)[C] + diag w_C`, a sum
of two positive semidefinite matrices.  So every block gap is a contraction, with
no hypothesis on the selection at all. -/
theorem posSemidef_one_sub_pickBlockGap (design : WeightedDesign size rank) {chosen : ℕ}
    (pick : Fin chosen → Fin size) (hinj : Function.Injective pick) :
    ((1 : Matrix (Fin chosen) (Fin chosen) ℝ) - pickBlockGap design pick).PosSemidef := by
  have hsplit : (1 : Matrix (Fin chosen) (Fin chosen) ℝ) - pickBlockGap design pick
      = ((1 : Matrix (Fin size) (Fin size) ℝ) - projectionOfDesign design).submatrix pick pick
        + Matrix.diagonal (fun slot => design.weight (pick slot)) := by
    ext left right
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.submatrix_apply, Matrix.one_apply,
      Matrix.diagonal_apply, pickBlockGap]
    rcases eq_or_ne left right with rfl | hne
    · rw [if_pos rfl, if_pos rfl, if_pos rfl]; ring
    · rw [if_neg hne, if_neg hne, if_neg (fun hcontra => hne (hinj hcontra))]; ring
  rw [hsplit]
  exact ((posSemidef_one_sub_projectionOfDesign design).submatrix pick).add
    (posSemidef_weightDiagonal design pick)

/-! ## 3. The bridge: a determinant floor is a margin floor -/

/-- **THE BRIDGE.**  At a positive semidefinite block gap the determinant sits
below every eigenvalue, because the gap is a contraction.  This is the shipped
contraction lemma applied to the one matrix the campaign cares about. -/
theorem det_pickBlockGap_le_eigenvalue (design : WeightedDesign size rank) {chosen : ℕ}
    (pick : Fin chosen → Fin size) (hinj : Function.Injective pick)
    (hpsd : (pickBlockGap design pick).PosSemidef)
    (eigenIndex : Fin chosen) :
    (pickBlockGap design pick).det ≤ hpsd.1.eigenvalues eigenIndex :=
  det_le_eigenvalue_of_posSemidef_of_posSemidef_one_sub hpsd
    (posSemidef_one_sub_pickBlockGap design pick hinj) eigenIndex

/-- **THE HEADLINE.**  A determinant strictly above a level makes the block gap
clear that level in the Loewner order.  So any lower bound on one block
determinant is a lower bound on the selection margin. -/
theorem posDef_blockMarginGap_of_lt_det (design : WeightedDesign size rank) {chosen : ℕ}
    (pick : Fin chosen → Fin size) (hinj : Function.Injective pick)
    (hpsd : (pickBlockGap design pick).PosSemidef)
    {level : ℝ} (hlevel : level < (pickBlockGap design pick).det) :
    (blockMarginGap (projectionOfDesign design) design.weight pick level).PosDef := by
  have hshift : blockMarginGap (projectionOfDesign design) design.weight pick level
      = pickBlockGap design pick - level • (1 : Matrix (Fin chosen) (Fin chosen) ℝ) := by
    ext left right
    simp [blockMarginGap, pickBlockGap, Matrix.sub_apply, Matrix.submatrix_apply,
      Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
    split <;> ring
  rw [hshift]
  refine posDef_sub_smul_one_of_eigenvalue_gt hpsd.1 level fun eigenIndex => ?_
  exact lt_of_lt_of_le hlevel (det_pickBlockGap_le_eigenvalue design pick hinj hpsd eigenIndex)

/-- **THE INTERFACE.**  One selection whose block gap is positive semidefinite
and whose determinant beats a level makes the shipped margin object reach that
level.  This is the statement a conditional-floor argument consumes. -/
theorem marginReaches_of_lt_det_pickBlockGap (design : WeightedDesign size rank) {chosen : ℕ}
    (pick : Fin chosen → Fin size) (hinj : Function.Injective pick)
    (hpsd : (pickBlockGap design pick).PosSemidef)
    {level : ℝ} (hlevel : level < (pickBlockGap design pick).det) :
    MarginReaches (projectionOfDesign design) design.weight chosen level :=
  ⟨pick, hinj, posDef_blockMarginGap_of_lt_det design pick hinj hpsd hlevel⟩

/-! ## 4. The diagonal shift: a linear part and a residual -/

/-- The part of `det (M - diag d)` that is linear in the shift. -/
def detShiftLinear (form : Matrix (Fin 3) (Fin 3) ℝ) (shift : Fin 3 → ℝ) : ℝ :=
  form.det
    - shift 0 * (form 1 1 * form 2 2 - form 1 2 ^ 2)
    - shift 1 * (form 0 0 * form 2 2 - form 0 2 ^ 2)
    - shift 2 * (form 0 0 * form 1 1 - form 0 1 ^ 2)

/-- The quadratic-and-cubic remainder of the same expansion. -/
def detShiftResidual (form : Matrix (Fin 3) (Fin 3) ℝ) (shift : Fin 3 → ℝ) : ℝ :=
  shift 0 * shift 1 * form 2 2 + shift 0 * shift 2 * form 1 1 + shift 1 * shift 2 * form 0 0
    - shift 0 * shift 1 * shift 2

/-- The shipped expansion, split into its linear part and its residual. -/
theorem det_sub_diagonal_eq_linear_add_residual (form : Matrix (Fin 3) (Fin 3) ℝ)
    (shift : Fin 3 → ℝ) (hsymmetric : form.transpose = form) :
    (form - Matrix.diagonal shift).det
      = detShiftLinear form shift + detShiftResidual form shift := by
  rw [det_sub_diagonal_fin_three form shift hsymmetric, detShiftLinear, detShiftResidual]
  ring

/-- **HEAVINESS PAYS FOR THE RESIDUAL.**  When every shift is positive and sits
below its own diagonal entry, the residual is nonnegative: the first product
alone already covers the cubic term, and the other two are nonnegative. -/
theorem detShiftResidual_nonneg_of_heavy (form : Matrix (Fin 3) (Fin 3) ℝ) (shift : Fin 3 → ℝ)
    (hpos : ∀ slot, 0 < shift slot) (hheavy : ∀ slot, shift slot ≤ form slot slot) :
    0 ≤ detShiftResidual form shift := by
  have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
  have k0 := hheavy 0; have k1 := hheavy 1; have k2 := hheavy 2
  have hcover : shift 0 * shift 1 * shift 2 ≤ shift 0 * shift 1 * form 2 2 :=
    mul_le_mul_of_nonneg_left k2 (mul_pos h0 h1).le
  have hsecond : 0 ≤ shift 0 * shift 2 * form 1 1 :=
    mul_nonneg (mul_pos h0 h2).le (h1.le.trans k1)
  have hthird : 0 ≤ shift 1 * shift 2 * form 0 0 :=
    mul_nonneg (mul_pos h1 h2).le (h0.le.trans k0)
  rw [detShiftResidual]; linarith

/-- **THE LINEAR BOUND.**  Dropping the residual leaves a determinant lower bound
that reads only the determinant, the three pair minors and the shifts. -/
theorem detShiftLinear_le_det_sub_diagonal (form : Matrix (Fin 3) (Fin 3) ℝ) (shift : Fin 3 → ℝ)
    (hsymmetric : form.transpose = form) (hpos : ∀ slot, 0 < shift slot)
    (hheavy : ∀ slot, shift slot ≤ form slot slot) :
    detShiftLinear form shift ≤ (form - Matrix.diagonal shift).det := by
  rw [det_sub_diagonal_eq_linear_add_residual form shift hsymmetric]
  linarith [detShiftResidual_nonneg_of_heavy form shift hpos hheavy]

/-- The residual of a scalar form under a constant shift. -/
theorem detShiftResidual_smul_one (scale level : ℝ) :
    detShiftResidual (scale • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun _ => level)
      = 3 * level ^ 2 * scale - level ^ 3 := by
  simp [detShiftResidual, Matrix.smul_apply]
  ring

/-- **HEAVINESS IS NOT NECESSARY, AND IT IS NOT FREE EITHER.**  At leverage one
hundredth against weight three tenths the residual is `-243/10000`, so the linear
bound FAILS.  The hypothesis in `Gtz.detShiftLinear_le_det_sub_diagonal` is
therefore doing real work, and it cannot simply be dropped. -/
theorem not_forall_detShiftLinear_le_det_sub_diagonal :
    ¬ ∀ (form : Matrix (Fin 3) (Fin 3) ℝ) (shift : Fin 3 → ℝ),
        form.transpose = form → (∀ slot, 0 < shift slot) →
        detShiftLinear form shift ≤ (form - Matrix.diagonal shift).det := by
  intro hall
  set scale : ℝ := (1 : ℝ) / 100 with hscale
  set level : ℝ := (3 : ℝ) / 10 with hlevel
  have hsymm : (scale • (1 : Matrix (Fin 3) (Fin 3) ℝ)).transpose
      = scale • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.transpose_smul, Matrix.transpose_one]
  have hpos : ∀ slot : Fin 3, (0 : ℝ) < (fun _ => level) slot := by
    intro _; rw [hlevel]; norm_num
  have hbound := hall (scale • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun _ => level) hsymm hpos
  rw [det_sub_diagonal_eq_linear_add_residual _ _ hsymm,
    detShiftResidual_smul_one scale level] at hbound
  have hresidual : (0 : ℝ) ≤ 3 * level ^ 2 * scale - level ^ 3 := by linarith
  rw [hscale, hlevel] at hresidual
  norm_num at hresidual

/-! ## 5. The slack-ratio cell, root-free -/

/-- The cubic that governs the slack-ratio cell factors, and the factorisation is
what makes the threshold `s = 2` visible without a square root. -/
theorem slackCubic_factor (s : ℝ) : s ^ 3 - 3 * s - 2 = (s + 1) ^ 2 * (s - 2) := by ring

/-- **THE SLACK-RATIO CELL.**  Writing the pair-minor ratio as `s ^ 2` keeps every
step polynomial.  Each subtracted term is at most `p q r / s ^ 2`, and the cross
term is at least `- p q r / s ^ 3`, because its square is at most the product of
the three hypotheses.  Multiplying through by `s ^ 3` clears every denominator. -/
theorem tripleDetForm_mul_cube_ge_of_slackRatio (p q r u v w s : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (hu : s ^ 2 * u ^ 2 ≤ p * q) (hv : s ^ 2 * v ^ 2 ≤ p * r)
    (hw : s ^ 2 * w ^ 2 ≤ q * r) :
    p * q * r * ((s + 1) ^ 2 * (s - 2)) ≤ s ^ 3 * tripleDetForm p q r u v w := by
  have hpqr : 0 < p * q * r := by positivity
  have hru : s ^ 3 * (r * u ^ 2) ≤ s * (p * q * r) :=
    calc s ^ 3 * (r * u ^ 2) = s * r * (s ^ 2 * u ^ 2) := by ring
      _ ≤ s * r * (p * q) := mul_le_mul_of_nonneg_left hu (mul_nonneg hs.le hr.le)
      _ = s * (p * q * r) := by ring
  have hqv : s ^ 3 * (q * v ^ 2) ≤ s * (p * q * r) :=
    calc s ^ 3 * (q * v ^ 2) = s * q * (s ^ 2 * v ^ 2) := by ring
      _ ≤ s * q * (p * r) := mul_le_mul_of_nonneg_left hv (mul_nonneg hs.le hq.le)
      _ = s * (p * q * r) := by ring
  have hpw : s ^ 3 * (p * w ^ 2) ≤ s * (p * q * r) :=
    calc s ^ 3 * (p * w ^ 2) = s * p * (s ^ 2 * w ^ 2) := by ring
      _ ≤ s * p * (q * r) := mul_le_mul_of_nonneg_left hw (mul_nonneg hs.le hp.le)
      _ = s * (p * q * r) := by ring
  have hprod : (s ^ 2 * u ^ 2) * ((s ^ 2 * v ^ 2) * (s ^ 2 * w ^ 2))
      ≤ (p * q) * ((p * r) * (q * r)) :=
    mul_le_mul hu (mul_le_mul hv hw (by positivity) (by positivity)) (by positivity)
      (by positivity)
  have hsq : (s ^ 3 * (u * v * w)) ^ 2 ≤ (p * q * r) ^ 2 := by nlinarith [hprod]
  have hcross : -(p * q * r) ≤ s ^ 3 * (u * v * w) := by
    nlinarith [hsq, hpqr, sq_nonneg (s ^ 3 * (u * v * w) + p * q * r)]
  rw [tripleDetForm]
  nlinarith [hru, hqv, hpw, hcross]

/-- Above the threshold the cell returns a strictly positive number. -/
theorem tripleDetForm_pos_of_slackRatio (p q r u v w s : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 2 < s)
    (hu : s ^ 2 * u ^ 2 ≤ p * q) (hv : s ^ 2 * v ^ 2 ≤ p * r)
    (hw : s ^ 2 * w ^ 2 ≤ q * r) :
    0 < tripleDetForm p q r u v w := by
  have hspos : (0 : ℝ) < s := by linarith
  have hbound := tripleDetForm_mul_cube_ge_of_slackRatio p q r u v w s hp hq hr hspos hu hv hw
  have hpqr : 0 < p * q * r := by positivity
  have hfactor : 0 < p * q * r * ((s + 1) ^ 2 * (s - 2)) := by
    have : (0 : ℝ) < (s + 1) ^ 2 * (s - 2) := by nlinarith
    positivity
  have hcube : 0 < s ^ 3 := by positivity
  nlinarith [hbound, hfactor, hcube]

/-! ## 6. The sharp sum cell, made quantitative -/

/-- **THE QUANTITATIVE SHARP-SUM BOUND, AND IT NEEDS NO CELL HYPOTHESIS.**  The
shipped `Gtz.signFreeMargin_pos_of_weightedPairEnergy_lt` turns one inequality
into a sign.  Carrying the same two ingredients through without discarding
either turns it into a number: the shipped cube bound caps the cross term and the
shipped factorisation names the slack, and what is left is an inequality between
polynomials that holds for every nonnegative surplus triple.

Writing `E` for the even part and `T` for the surplus product, the cell's own
slack is `4 E - T`, positive exactly when the weighted pairing energy sits below
three quarters of `T`. -/
theorem slack_mul_sq_le_sharpSum (p q r u v w : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    (4 * evenTripleDetPart p q r u v w - p * q * r)
        * (evenTripleDetPart p q r u v w + 2 * (p * q * r)) ^ 2
      ≤ 27 * (p * q * r)
          * (evenTripleDetPart p q r u v w ^ 2 - 4 * (u * v * w) ^ 2) := by
  have hcube := twentySeven_mul_cross_sq_le_energy_cube p q r u v w hp hq hr
  have henergy : weightedPairEnergy p q r u v w
      = p * q * r - evenTripleDetPart p q r u v w := by
    rw [evenTripleDetPart_eq_sub_weightedPairEnergy]; ring
  rw [henergy] at hcube
  have hfac := sharp_sum_factorization (evenTripleDetPart p q r u v w) (p * q * r)
  nlinarith [hcube, hfac]

/-- **THE MAXIMAL CELL, MADE QUANTITATIVE.**  The shipped
`Gtz.signFreeMargin_pos_iff_evenPart_sq` decides a positive margin by
`4 (u v w) ^ 2 < E ^ 2`.  The same difference of squares bounds the margin from
below, because the margin is the difference of the two factors and their sum is
at most `2 E`.  Since that criterion is an IFF for the whole sign-blind class,
this is the quantitative form of the class and not of one cell inside it. -/
theorem evenPartSq_le_two_mul_evenPart_mul_signFreeMargin (p q r u v w : ℝ)
    (hmargin : 0 < signFreeMargin p q r u v w) :
    evenTripleDetPart p q r u v w ^ 2 - 4 * (u * v * w) ^ 2
      ≤ 2 * evenTripleDetPart p q r u v w * signFreeMargin p q r u v w := by
  have hsplit : signFreeMargin p q r u v w
      = evenTripleDetPart p q r u v w - 2 * |u * v * w| :=
    signFreeMargin_eq_evenPart_sub_abs p q r u v w
  have habs : 0 ≤ |u * v * w| := abs_nonneg _
  have hsqabs : |u * v * w| ^ 2 = (u * v * w) ^ 2 := sq_abs _
  rw [hsplit]
  rw [hsplit] at hmargin
  nlinarith [habs, hsqabs, hmargin]

/-- **THE MARGIN ITSELF, BOUNDED BELOW BY THE CELL'S OWN SLACK.**  Under the
sharp sum cell the sign-free margin is positive, so the even part exceeds twice
the absolute cross term, so `E + 2|u v w|` is below `2 E`.  Dividing the
difference of squares by that smaller quantity gives the margin directly, with no
square root and no eigenvalue. -/
theorem sharpSumSlack_le_signFreeMargin (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hcell : weightedPairEnergy p q r u v w < 3 / 4 * (p * q * r)) :
    (4 * evenTripleDetPart p q r u v w - p * q * r)
        * (evenTripleDetPart p q r u v w + 2 * (p * q * r)) ^ 2
      ≤ 54 * (p * q * r) * evenTripleDetPart p q r u v w
          * signFreeMargin p q r u v w := by
  have hT : 0 < p * q * r := by positivity
  have hE : evenTripleDetPart p q r u v w = p * q * r - weightedPairEnergy p q r u v w :=
    evenTripleDetPart_eq_sub_weightedPairEnergy p q r u v w
  have hEpos : 0 < evenTripleDetPart p q r u v w := by rw [hE]; linarith
  have hmarginPos : 0 < signFreeMargin p q r u v w :=
    signFreeMargin_pos_of_weightedPairEnergy_lt p q r u v w hp hq hr hcell
  have hsplit : signFreeMargin p q r u v w
      = evenTripleDetPart p q r u v w - 2 * |u * v * w| :=
    signFreeMargin_eq_evenPart_sub_abs p q r u v w
  have habs : 0 ≤ |u * v * w| := abs_nonneg _
  have hsqabs : |u * v * w| ^ 2 = (u * v * w) ^ 2 := sq_abs _
  have hdiff := evenPartSq_le_two_mul_evenPart_mul_signFreeMargin p q r u v w hmarginPos
  have hkey := slack_mul_sq_le_sharpSum p q r u v w hp.le hq.le hr.le
  nlinarith [hkey, hdiff, hT]

/-! ## 7. The coherent quantitative bound -/

/-- With a nonnegative triple product the cross term only helps, so the
determinant is at least the sign-free part.  No slack ratio is needed. -/
theorem tripleDetForm_ge_of_nonneg_cross (p q r u v w : ℝ) (hcoherent : 0 ≤ u * v * w) :
    p * q * r - p * w ^ 2 - q * v ^ 2 - r * u ^ 2 ≤ tripleDetForm p q r u v w := by
  rw [tripleDetForm]; linarith

/-! ## 8. The composite -/

/-- **THE COMPOSITE.**  At a heavy selection of three labels the margin is at
least the linear part of the block determinant, which is a polynomial in the
projection entries and the weights: the block determinant minus the three pair
minors weighted by their own labels. -/
theorem marginReaches_of_lt_detShiftLinear (design : WeightedDesign size rank)
    (pick : Fin 3 → Fin size) (hinj : Function.Injective pick)
    (hpsd : (pickBlockGap design pick).PosSemidef)
    (hheavy : ∀ slot, design.weight (pick slot)
      ≤ (projectionOfDesign design).submatrix pick pick slot slot)
    {level : ℝ}
    (hlevel : level
      < detShiftLinear ((projectionOfDesign design).submatrix pick pick)
          (fun slot => design.weight (pick slot))) :
    MarginReaches (projectionOfDesign design) design.weight 3 level := by
  have hsymm : ((projectionOfDesign design).submatrix pick pick).transpose
      = (projectionOfDesign design).submatrix pick pick := by
    ext left right
    simpa [Matrix.transpose_apply, Matrix.submatrix_apply] using
      projectionOfDesign_symm design (pick left) (pick right)
  have hpos : ∀ slot : Fin 3, 0 < design.weight (pick slot) :=
    fun slot => design.weight_pos (pick slot)
  have hlinear := detShiftLinear_le_det_sub_diagonal
    ((projectionOfDesign design).submatrix pick pick)
    (fun slot => design.weight (pick slot)) hsymm hpos hheavy
  exact marginReaches_of_lt_det_pickBlockGap design pick hinj hpsd
    (lt_of_lt_of_le hlevel hlinear)

/-- The block gap determinant IS the selected Gram determinant, scaled by the
strictly positive product of the selected weights.  This is the shipped
positive-diagonal congruence read on `Gtz.pickBlockGap`. -/
theorem det_pickBlockGap_eq_weightProd_mul_gramDet (design : WeightedDesign size rank)
    {chosen : ℕ} (pick : Fin chosen → Fin size) :
    (pickBlockGap design pick).det
      = (∏ slot, design.weight (pick slot))
        * (selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ - 1).det :=
  det_projectionBlock_sub_weightDiagonal design pick

/-- The weight product along a selection is strictly positive. -/
theorem weightProd_pos (design : WeightedDesign size rank) {chosen : ℕ}
    (pick : Fin chosen → Fin size) : 0 < ∏ slot, design.weight (pick slot) :=
  Finset.prod_pos fun slot _ => design.weight_pos (pick slot)

/-- **THE END-TO-END COMPOSITION.**  A lower bound on the selected Gram
determinant becomes a margin floor, once it is scaled by the weight product.  So
every quantitative cell in the scalar vocabulary reaches the margin object
without leaving polynomials. -/
theorem marginReaches_of_lt_weightProd_mul_gramDet (design : WeightedDesign size rank)
    {chosen : ℕ} (pick : Fin chosen → Fin size) (hinj : Function.Injective pick)
    (hpsd : (pickBlockGap design pick).PosSemidef) {level : ℝ}
    (hlevel : level < (∏ slot, design.weight (pick slot))
      * (selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ - 1).det) :
    MarginReaches (projectionOfDesign design) design.weight chosen level := by
  refine marginReaches_of_lt_det_pickBlockGap design pick hinj hpsd ?_
  rwa [det_pickBlockGap_eq_weightProd_mul_gramDet design pick]

end Gtz
