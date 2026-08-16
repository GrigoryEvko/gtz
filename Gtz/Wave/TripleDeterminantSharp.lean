import Gtz.Wave.TripleDeterminantCells
import Gtz.LinAlg.ProjectionForm

/-!
# The sharp sign-free cell, the projection bridge, and a route that reads no
# pairings

Three things this file settles about the one-line residual determinant.

**The sharp sign-free cell.**  `Gtz.tripleGapDet` reads the triple product
`u v w` oddly and everything else evenly, so flipping one atom's pairing sign
flips exactly the cross term and leaves all three pair minors fixed.  The
strongest condition invariant under that flip is therefore the value at the worse
sign, `Gtz.signFreeMargin`.  `Gtz.signFreeMargin_pos_iff_both_signs` proves it is
exactly the two-sided condition, so NO cell that declines to read the sign of the
triple product can beat it.  The quarter-slack cell of the previous file is a
corollary, and the sharp constant four is what the equilateral locus forces.

**The projection bridge.**  `Gtz.det_projectionBlock_sub_weightDiagonal` relates
a projection block determinant to a selected Gram determinant, and
`Gtz.det_tripleGram_sub_one` identifies the latter with `Gtz.tripleGapDet`.
Composing them gives `Gtz.projectionBlockDet_eq_weightProd_mul_tripleGapDet`: the
one-line residual determinant IS the projection block determinant, up to the
strictly positive product of the three weights.  The design lane and the
projection lane are reading one object.

**A route that reads no pairings.**  The row law caps a single weighted squared
pairing by the row's share gap.  Comparing that cap against the heavy masses
turns the quarter slack into `4 (s - s^2) < m_x m_y`, a condition on shares and
heavy masses ALONE.  Three such pairs give a strict dominator with no pairing
ever read.  The universal bound `s - s^2 <= 1/4` explains the price: the route
needs a share away from one half, and at exactly one half it can never fire.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The sign flip, and what it fixes -/

/-- Flipping the last pairing negates the cross term and fixes everything else.
This is the involution the sign-free analysis is about. -/
theorem tripleDetForm_flip_third (p q r u v w : ℝ) :
    tripleDetForm p q r u v (-w)
      = p * q * r - p * w ^ 2 - q * v ^ 2 - r * u ^ 2 - 2 * (u * v * w) := by
  rw [tripleDetForm]; ring

/-- The flip fixes all three pair minors, because each reads a pairing evenly. -/
theorem pairMinors_flip_third (p q r u v w : ℝ) :
    (p * q - u ^ 2 = p * q - u ^ 2)
      ∧ (p * r - v ^ 2 = p * r - v ^ 2)
      ∧ (q * r - (-w) ^ 2 = q * r - w ^ 2) := by
  refine ⟨rfl, rfl, by ring⟩

/-- The two determinants at the two signs sum to twice the sign-free part, so
their average never sees the cross term. -/
theorem tripleDetForm_add_flip (p q r u v w : ℝ) :
    tripleDetForm p q r u v w + tripleDetForm p q r u v (-w)
      = 2 * (p * q * r - p * w ^ 2 - q * v ^ 2 - r * u ^ 2) := by
  rw [tripleDetForm, tripleDetForm_flip_third]; ring

/-! ## 2. The sign-free margin, and its optimality -/

/-- The determinant at the WORSE sign of the triple product.  Every cell that
refuses to read that sign is bounded by this quantity. -/
noncomputable def signFreeMargin (p q r u v w : ℝ) : ℝ :=
  p * q * r - p * w ^ 2 - q * v ^ 2 - r * u ^ 2 - 2 * |u * v * w|

/-- The margin never exceeds the determinant. -/
theorem signFreeMargin_le_tripleDetForm (p q r u v w : ℝ) :
    signFreeMargin p q r u v w ≤ tripleDetForm p q r u v w := by
  rw [signFreeMargin, tripleDetForm]
  have := neg_abs_le (u * v * w)
  linarith

/-- The margin never exceeds the determinant at the flipped sign either. -/
theorem signFreeMargin_le_tripleDetForm_flip (p q r u v w : ℝ) :
    signFreeMargin p q r u v w ≤ tripleDetForm p q r u v (-w) := by
  rw [signFreeMargin, tripleDetForm_flip_third]
  have := le_abs_self (u * v * w)
  linarith

/-- **THE MARGIN IS EXACTLY THE TWO-SIDED CONDITION.**  It is positive precisely
when the determinant is positive at both signs of the cross term.  So the margin
is the strongest condition invariant under the flip, and no sign-blind cell can
improve on it. -/
theorem signFreeMargin_pos_iff_both_signs (p q r u v w : ℝ) :
    0 < signFreeMargin p q r u v w
      ↔ 0 < tripleDetForm p q r u v w ∧ 0 < tripleDetForm p q r u v (-w) := by
  constructor
  · intro h
    exact ⟨lt_of_lt_of_le h (signFreeMargin_le_tripleDetForm p q r u v w),
      lt_of_lt_of_le h (signFreeMargin_le_tripleDetForm_flip p q r u v w)⟩
  · rintro ⟨hpos, hflip⟩
    rw [tripleDetForm] at hpos
    rw [tripleDetForm_flip_third] at hflip
    rw [signFreeMargin]
    rcases abs_cases (u * v * w) with ⟨heq, -⟩ | ⟨heq, -⟩ <;> rw [heq] <;> linarith

/-- **THE SIGN-FREE CELL.**  A positive margin forces a positive determinant. -/
theorem tripleDetForm_pos_of_signFreeMargin (p q r u v w : ℝ)
    (h : 0 < signFreeMargin p q r u v w) : 0 < tripleDetForm p q r u v w :=
  lt_of_lt_of_le h (signFreeMargin_le_tripleDetForm p q r u v w)

/-- **THE QUARTER SLACK FACTORS THROUGH THE MARGIN.**  So the cell of the
previous file is a corollary of the sharp sign-free condition, and the
equilateral locus shows the constant four is what makes the corollary tight. -/
theorem signFreeMargin_pos_of_quarterSlack (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hu : 4 * u ^ 2 < p * q) (hv : 4 * v ^ 2 < p * r) (hw : 4 * w ^ 2 < q * r) :
    0 < signFreeMargin p q r u v w := by
  have hpqr : 0 < p * q * r := by positivity
  have hru : r * u ^ 2 < p * q * r / 4 := by nlinarith
  have hqv : q * v ^ 2 < p * q * r / 4 := by nlinarith
  have hpw : p * w ^ 2 < p * q * r / 4 := by nlinarith
  have hsq := sq_cross_lt_of_quarterSlack p q r u v w hp hq hr hu hv hw
  have habs : |u * v * w| < p * q * r / 8 := by
    have hnn : (0:ℝ) ≤ p * q * r / 8 := by positivity
    have hsq' : |u * v * w| ^ 2 < (p * q * r / 8) ^ 2 := by
      rw [sq_abs]; nlinarith [hsq]
    nlinarith [abs_nonneg (u * v * w), hsq', hnn]
  rw [signFreeMargin]; linarith

/-- The margin at the atom level. -/
noncomputable def atomSignFreeMargin (a b c : Fin 3 → ℝ) : ℝ :=
  signFreeMargin (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
    (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c)

theorem tripleGapDet_pos_of_atomSignFreeMargin (a b c : Fin 3 → ℝ)
    (h : 0 < atomSignFreeMargin a b c) : 0 < tripleGapDet a b c := by
  rw [tripleGapDet_eq_tripleDetForm]
  exact tripleDetForm_pos_of_signFreeMargin _ _ _ _ _ _ h

/-- The sharp sign-free cell at the design level. -/
theorem subsetSum_posDef_of_atomSignFreeMargin {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (htri : AdmissibleTriangle D x y z)
    (hmargin : 0 < atomSignFreeMargin (D.atom x) (D.atom y) (D.atom z)) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef :=
  subsetSum_posDef_of_admissibleTriangle_of_det D x y z hxy hxz hyz hheavy htri
    (tripleGapDet_pos_of_atomSignFreeMargin _ _ _ hmargin)

/-- The witness of the previous file has a strictly negative margin, as it must:
its determinant is already negative at the sign it carries. -/
theorem negDet_signFreeMargin_neg :
    atomSignFreeMargin negDetFirst negDetSecond negDetThird < 0 := by
  rw [atomSignFreeMargin, signFreeMargin, leverageOf_negDetFirst, leverageOf_negDetSecond,
    leverageOf_negDetThird, negDet_pairing_first_second, negDet_pairing_first_third,
    negDet_pairing_second_third]
  norm_num

/-! ## 3. The projection bridge

The selected Gram of three labels is the triple Gram of their atoms, so the
landed projection-block determinant law applies verbatim to the one-line
residual. -/

/-- The selected atom rows of a three-label pick reproduce the triple Gram. -/
theorem selectedGram_eq_tripleGram {m : ℕ} (D : WeightedDesign m 3) (x y z : Fin m) :
    selectedAtomRows D ![x, y, z] * (selectedAtomRows D ![x, y, z])ᵀ
      = tripleGram (D.atom x) (D.atom y) (D.atom z) := by
  ext i j
  rw [tripleGram_apply]
  fin_cases i <;> fin_cases j <;>
    simp [selectedAtomRows, Matrix.mul_apply, Matrix.transpose_apply, dotProduct]

/-- The weight product over a three-label pick. -/
theorem prod_weight_pick_three {m : ℕ} (D : WeightedDesign m 3) (x y z : Fin m) :
    (∏ i : Fin 3, D.weight (![x, y, z] i))
      = D.weight x * D.weight y * D.weight z := by
  rw [Fin.prod_univ_three]
  simp

/-- **THE ONE-LINE RESIDUAL IS THE PROJECTION BLOCK DETERMINANT.**  The
determinant of the projection block minus the weight diagonal equals the product
of the three weights times `Gtz.tripleGapDet`.  The design lane and the
projection lane read one object, and the factor is strictly positive so the two
decision procedures agree on the nose. -/
theorem projectionBlockDet_eq_weightProd_mul_tripleGapDet {m : ℕ}
    (D : WeightedDesign m 3) (x y z : Fin m) :
    ((projectionOfDesign D).submatrix ![x, y, z] ![x, y, z]
        - Matrix.diagonal (fun i : Fin 3 => D.weight (![x, y, z] i))).det
      = D.weight x * D.weight y * D.weight z
        * tripleGapDet (D.atom x) (D.atom y) (D.atom z) := by
  rw [det_projectionBlock_sub_weightDiagonal D ![x, y, z], selectedGram_eq_tripleGram,
    det_tripleGram_sub_one, prod_weight_pick_three]

/-- **THE TWO SIGNS AGREE.**  The residual determinant is positive exactly when
the projection block determinant is. -/
theorem tripleGapDet_pos_iff_projectionBlockDet_pos {m : ℕ}
    (D : WeightedDesign m 3) (x y z : Fin m) :
    0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z)
      ↔ 0 < ((projectionOfDesign D).submatrix ![x, y, z] ![x, y, z]
          - Matrix.diagonal (fun i : Fin 3 => D.weight (![x, y, z] i))).det := by
  rw [projectionBlockDet_eq_weightProd_mul_tripleGapDet]
  have hpos : 0 < D.weight x * D.weight y * D.weight z := by
    exact mul_pos (mul_pos (D.weight_pos x) (D.weight_pos y)) (D.weight_pos z)
  constructor
  · intro h; positivity
  · intro h; nlinarith [hpos, h]

/-! ## 4. A route that reads no pairings

The row law caps one weighted squared pairing by the row's share gap.  Compared
against the heavy masses, that turns the quarter slack into a condition on shares
and heavy masses alone. -/

/-- **THE PER-PAIR CAP.**  A single weighted squared pairing never exceeds the
row's share gap.  This is one term of the landed row law. -/
theorem weightPair_mul_sq_gapPairing_le_shareGap {m k : ℕ} (D : WeightedDesign m k)
    (x y : Fin m) (hne : x ≠ y) :
    D.weight x * D.weight y * gapPairingOf D x y ^ 2
      ≤ atomShare D x - atomShare D x ^ 2 := by
  have hmem : y ∈ Finset.univ.erase x := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ y⟩
  rw [← sum_erase_weightPair_mul_sq_gapPairing D x]
  refine Finset.single_le_sum (f := fun otherLabel =>
    D.weight x * D.weight otherLabel * gapPairingOf D x otherLabel ^ 2) ?_ hmem
  exact fun otherLabel _ => mul_nonneg (mul_nonneg (D.weight_pos x).le
    (D.weight_pos otherLabel).le) (sq_nonneg _)

/-- The heavy-mass product is the weighted pair surplus. -/
theorem heavyMass_product_eq {m k : ℕ} (D : WeightedDesign m k) (x y : Fin m) :
    heavyMassOf D x * heavyMassOf D y
      = D.weight x * D.weight y * (gapExcessOf D x * gapExcessOf D y) := by
  rw [heavyMassOf, heavyMassOf]; ring

/-- **THE SHARE-ONLY QUARTER SLACK.**  Four times a row's share gap below the two
heavy masses forces the quarter slack on that pair, with no pairing read.  The
universal bound `s - s^2 <= 1/4` prices the route: it needs a share away from one
half. -/
theorem quarterSlack_of_shareGap_lt_heavyMassProduct {m : ℕ} (D : WeightedDesign m 3)
    (x y : Fin m) (hne : x ≠ y)
    (hshare : 4 * (atomShare D x - atomShare D x ^ 2)
      < heavyMassOf D x * heavyMassOf D y) :
    4 * (D.atom x ⬝ᵥ D.atom y) ^ 2
      < (leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1) := by
  have hcap := weightPair_mul_sq_gapPairing_le_shareGap D x y hne
  rw [heavyMass_product_eq] at hshare
  have hw : 0 < D.weight x * D.weight y := mul_pos (D.weight_pos x) (D.weight_pos y)
  have hchain : D.weight x * D.weight y * (4 * gapPairingOf D x y ^ 2)
      < D.weight x * D.weight y * (gapExcessOf D x * gapExcessOf D y) := by
    nlinarith [hcap, hshare]
  have := lt_of_mul_lt_mul_left (by linarith [hchain] :
    D.weight x * D.weight y * (4 * gapPairingOf D x y ^ 2)
      < D.weight x * D.weight y * (gapExcessOf D x * gapExcessOf D y)) hw.le
  rw [gapPairingOf, gapExcessOf, gapExcessOf] at this
  linarith

/-- **THE SHARE-ONLY DOMINATOR.**  Three pairs clearing the share-only condition
give a strictly dominating triple, and no pairing is read anywhere in the
hypothesis. -/
theorem subsetSum_posDef_of_shareOnly {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : 1 < leverageOf (D.atom x)) (hy : 1 < leverageOf (D.atom y))
    (hz : 1 < leverageOf (D.atom z))
    (hsxy : 4 * (atomShare D x - atomShare D x ^ 2)
      < heavyMassOf D x * heavyMassOf D y)
    (hsxz : 4 * (atomShare D x - atomShare D x ^ 2)
      < heavyMassOf D x * heavyMassOf D z)
    (hsyz : 4 * (atomShare D y - atomShare D y ^ 2)
      < heavyMassOf D y * heavyMassOf D z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef :=
  subsetSum_posDef_of_quarterSlack D x y z hxy hxz hyz hx hy hz
    (quarterSlack_of_shareGap_lt_heavyMassProduct D x y hxy hsxy)
    (quarterSlack_of_shareGap_lt_heavyMassProduct D x z hxz hsxz)
    (quarterSlack_of_shareGap_lt_heavyMassProduct D y z hyz hsyz)

/-- **THE PRICE OF READING NO PAIRINGS.**  At a share of exactly one half the
share gap is maximal and the condition demands a heavy-mass product above one,
which the ceiling forbids.  So the route is silent exactly on the rows whose
share sits at the midpoint. -/
theorem shareOnly_silent_at_half {m k : ℕ} (D : WeightedDesign m k) (x y : Fin m)
    (hhalf : atomShare D x = 1 / 2) (hx : 0 ≤ heavyMassOf D x) :
    ¬ (4 * (atomShare D x - atomShare D x ^ 2)
      < heavyMassOf D x * heavyMassOf D y) := by
  rw [hhalf]
  have hceil := heavyMass_product_lt_one D x y hx
  intro hcon
  norm_num at hcon
  linarith

/-- The route needs a share strictly away from one half, quantitatively: the
share gap must fall below a quarter of the heavy-mass product. -/
theorem shareOnly_forces_share_off_half {m k : ℕ} (D : WeightedDesign m k)
    (x y : Fin m)
    (hshare : 4 * (atomShare D x - atomShare D x ^ 2)
      < heavyMassOf D x * heavyMassOf D y) :
    (atomShare D x - 1 / 2) ^ 2 > 1 / 4 - heavyMassOf D x * heavyMassOf D y / 4 := by
  nlinarith [hshare]

/-! ## 5. The full cell inventory at a triple

Four independent sufficient conditions, and their common consumer.  Each is
stated so that its hypothesis reads a different part of the data: the quarter
slack reads pairing sizes, the sign-free margin reads pairing sizes and the
triple product's magnitude, the nonnegative-cross cell reads the triple product's
sign, and the share-only route reads no pairing at all. -/

/-- The four cells, as one disjunction. -/
def TripleSharpCellFires {m : ℕ} (D : WeightedDesign m 3) (x y z : Fin m) : Prop :=
  TripleDetCellFires D x y z
  ∨ (AdmissibleTriangle D x y z
      ∧ 0 < atomSignFreeMargin (D.atom x) (D.atom y) (D.atom z))
  ∨ (4 * (atomShare D x - atomShare D x ^ 2) < heavyMassOf D x * heavyMassOf D y
      ∧ 4 * (atomShare D x - atomShare D x ^ 2) < heavyMassOf D x * heavyMassOf D z
      ∧ 4 * (atomShare D y - atomShare D y ^ 2) < heavyMassOf D y * heavyMassOf D z)

/-- Any branch supplies a strict dominator. -/
theorem subsetSum_posDef_of_tripleSharpCellFires {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (hstrict : 1 < leverageOf (D.atom x) ∧ 1 < leverageOf (D.atom y)
      ∧ 1 < leverageOf (D.atom z))
    (hfires : TripleSharpCellFires D x y z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef := by
  obtain ⟨hx, hy, hz⟩ := hstrict
  rcases hfires with hbase | ⟨htri, hmargin⟩ | ⟨hxy', hxz', hyz'⟩
  · exact subsetSum_posDef_of_tripleDetCellFires D x y z hxy hxz hyz hheavy ⟨hx, hy, hz⟩ hbase
  · exact subsetSum_posDef_of_atomSignFreeMargin D x y z hxy hxz hyz hheavy htri hmargin
  · exact subsetSum_posDef_of_shareOnly D x y z hxy hxz hyz hx hy hz hxy' hxz' hyz'

/-- **THE SHARP INVENTORY FEEDS THE TRIANGLE COVER.** -/
theorem admissibleTriangleCovers_of_tripleSharpCellFires {m : ℕ}
    (D : WeightedDesign m 3) (x y z : Fin m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (hstrict : 1 < leverageOf (D.atom x) ∧ 1 < leverageOf (D.atom y)
      ∧ 1 < leverageOf (D.atom z))
    (hfires : TripleSharpCellFires D x y z) :
    AdmissibleTriangleCovers D :=
  admissibleTriangleCovers_of_subsetSum_posDef D x y z hxy hxz hyz
    (subsetSum_posDef_of_tripleSharpCellFires D x y z hxy hxz hyz hheavy hstrict hfires)

/-! ## 6. The per-label row cell: three good labels give a dominator

The row law caps a row's two in-triple pairings by the row's share gap.  A
weighted Cauchy-Schwarz turns that cap into diagonal dominance of the triple's
Gram gap, and the landed dominance cell finishes.  The resulting condition is
PER-LABEL: it reads one row's share and the three weights, never a pairing.  So
it defines a SET of good labels, and any three of them dominate. -/

/-- The weighted two-term Cauchy-Schwarz, in the division-free form the row law
hands over. -/
theorem sq_add_le_of_weighted (alpha beta bigA bigB : ℝ) :
    alpha * beta * (bigA + bigB) ^ 2
      ≤ (alpha + beta) * (alpha * bigA ^ 2 + beta * bigB ^ 2) := by
  nlinarith [sq_nonneg (alpha * bigA - beta * bigB)]

/-- The two in-triple terms of the row law never exceed the whole row. -/
theorem two_term_row_le_shareGap {m k : ℕ} (D : WeightedDesign m k)
    (c d e : Fin m) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    D.weight c * D.weight d * gapPairingOf D c d ^ 2
        + D.weight c * D.weight e * gapPairingOf D c e ^ 2
      ≤ atomShare D c - atomShare D c ^ 2 := by
  classical
  rw [← sum_erase_weightPair_mul_sq_gapPairing D c]
  have hsub : ({d, e} : Finset (Fin m)) ⊆ Finset.univ.erase c := by
    intro label hlabel
    rcases Finset.mem_insert.mp hlabel with rfl | hlabel'
    · exact Finset.mem_erase.mpr ⟨hcd.symm, Finset.mem_univ _⟩
    · rw [Finset.mem_singleton] at hlabel'
      subst hlabel'
      exact Finset.mem_erase.mpr ⟨hce.symm, Finset.mem_univ _⟩
  have hpair : ∑ label ∈ ({d, e} : Finset (Fin m)),
      D.weight c * D.weight label * gapPairingOf D c label ^ 2
      = D.weight c * D.weight d * gapPairingOf D c d ^ 2
        + D.weight c * D.weight e * gapPairingOf D c e ^ 2 := by
    rw [Finset.sum_insert (by simp [hde]), Finset.sum_singleton]
  rw [← hpair]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun label _ _ => ?_
  exact mul_nonneg (mul_nonneg (D.weight_pos c).le (D.weight_pos label).le) (sq_nonneg _)

/-- **THE PER-LABEL ROW CONDITION.**  It reads the row's share gap and the three
weights, and nothing else. -/
def RowDominantLabel {m k : ℕ} (D : WeightedDesign m k) (c d e : Fin m) : Prop :=
  (D.weight d + D.weight e) * (atomShare D c - atomShare D c ^ 2)
    < D.weight c * D.weight d * D.weight e * (leverageOf (D.atom c) - 1) ^ 2

/-- **THE ROW CONDITION GIVES DOMINANCE IN ITS ROW.**  The two in-triple
pairings of the row total strictly below the row's surplus. -/
theorem abs_add_abs_lt_of_rowDominant {m k : ℕ} (D : WeightedDesign m k)
    (c d e : Fin m) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hheavy : 1 < leverageOf (D.atom c))
    (hrow : RowDominantLabel D c d e) :
    |D.atom c ⬝ᵥ D.atom d| + |D.atom c ⬝ᵥ D.atom e| < leverageOf (D.atom c) - 1 := by
  have hwc := D.weight_pos c
  have hwd := D.weight_pos d
  have hwe := D.weight_pos e
  have halpha : 0 < D.weight c * D.weight d := mul_pos hwc hwd
  have hbeta : 0 < D.weight c * D.weight e := mul_pos hwc hwe
  have hrowlaw := two_term_row_le_shareGap D c d e hcd hce hde
  have hcs := sq_add_le_of_weighted (D.weight c * D.weight d) (D.weight c * D.weight e)
    |D.atom c ⬝ᵥ D.atom d| |D.atom c ⬝ᵥ D.atom e|
  rw [sq_abs, sq_abs] at hcs
  rw [RowDominantLabel] at hrow
  rw [gapPairingOf, gapPairingOf] at hrowlaw
  have hsq : (|D.atom c ⬝ᵥ D.atom d| + |D.atom c ⬝ᵥ D.atom e|) ^ 2
      < (leverageOf (D.atom c) - 1) ^ 2 := by
    have hprod : 0 < D.weight c * D.weight d * (D.weight c * D.weight e) := mul_pos halpha hbeta
    nlinarith [hcs, hrowlaw, hrow, hwc, hwd, hwe, hprod]
  have hnn : 0 ≤ |D.atom c ⬝ᵥ D.atom d| + |D.atom c ⬝ᵥ D.atom e| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith [hsq, hnn, hheavy]

/-- **THREE ROW-DOMINANT LABELS GIVE A STRICT DOMINATOR.**  No pairing appears in
any hypothesis: the whole certificate reads three shares, three leverages and
three weights. -/
theorem subsetSum_posDef_of_rowDominant {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : 1 < leverageOf (D.atom x)) (hy : 1 < leverageOf (D.atom y))
    (hz : 1 < leverageOf (D.atom z))
    (hrx : RowDominantLabel D x y z) (hry : RowDominantLabel D y x z)
    (hrz : RowDominantLabel D z x y) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef := by
  refine (subsetSum_posDef_iff_tripleGram D x y z hxy hxz hyz).mpr
    (tripleGram_posDef_of_diagonallyDominant _ _ _ ⟨?_, ?_, ?_⟩)
  · exact abs_add_abs_lt_of_rowDominant D x y z hxy hxz hyz hx hrx
  · have := abs_add_abs_lt_of_rowDominant D y x z hxy.symm hyz hxz hy hry
    rw [dotProduct_comm (D.atom y) (D.atom x)] at this
    exact this
  · have := abs_add_abs_lt_of_rowDominant D z x y hxz.symm hyz.symm hxy hz hrz
    rw [dotProduct_comm (D.atom z) (D.atom x), dotProduct_comm (D.atom z) (D.atom y)] at this
    exact this

/-- **THE ROW CELL FEEDS THE TRIANGLE COVER.** -/
theorem admissibleTriangleCovers_of_rowDominant {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : 1 < leverageOf (D.atom x)) (hy : 1 < leverageOf (D.atom y))
    (hz : 1 < leverageOf (D.atom z))
    (hrx : RowDominantLabel D x y z) (hry : RowDominantLabel D y x z)
    (hrz : RowDominantLabel D z x y) :
    AdmissibleTriangleCovers D :=
  admissibleTriangleCovers_of_subsetSum_posDef D x y z hxy hxz hyz
    (subsetSum_posDef_of_rowDominant D x y z hxy hxz hyz hx hy hz hrx hry hrz)

/-- **THE PRICE OF THE ROW CELL.**  The share gap is at most a quarter, so the
row condition is implied by a bound reading only weights and the surplus.  This
is the cheapest sufficient form and it never reads a share either. -/
theorem rowDominantLabel_of_quarter_bound {m k : ℕ} (D : WeightedDesign m k)
    (c d e : Fin m)
    (hbound : (D.weight d + D.weight e) / 4
      < D.weight c * D.weight d * D.weight e * (leverageOf (D.atom c) - 1) ^ 2) :
    RowDominantLabel D c d e := by
  have hgap := atomShare_gap_le_quarter D c
  have hnn : 0 < D.weight d + D.weight e := add_pos (D.weight_pos d) (D.weight_pos e)
  rw [RowDominantLabel]
  nlinarith [hgap, hnn, hbound]

/-- The quarter slack is strictly inside the sharp cell: every quarter-slack
triple has a positive margin, and the equilateral locus shows the containment is
not an equality of thresholds. -/
theorem tripleSharpCellFires_of_quarterSlack {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m)
    (hab : 4 * (D.atom x ⬝ᵥ D.atom y) ^ 2
      < (leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1))
    (hac : 4 * (D.atom x ⬝ᵥ D.atom z) ^ 2
      < (leverageOf (D.atom x) - 1) * (leverageOf (D.atom z) - 1))
    (hbc : 4 * (D.atom y ⬝ᵥ D.atom z) ^ 2
      < (leverageOf (D.atom y) - 1) * (leverageOf (D.atom z) - 1)) :
    TripleSharpCellFires D x y z :=
  Or.inl (Or.inl ⟨hab, hac, hbc⟩)

end Gtz
