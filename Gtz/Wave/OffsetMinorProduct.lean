/-
# The offset against the pivot minor product: locality, the shifted row law, and the
direction of the ceiling

`Gtz.tripleDetForm_pos_iff_sq_lt` reads a triple's third minor at a positive pivot as

    (p * w - u * v) ^ 2 < pairMinorForm p q u * pairMinorForm p r v

so the objective asks for a label carrying two pair minors whose product beats its own
squared offset.  This file settles three questions about that shape.

## 1. The offset is NOT two-local, and the threshold is

The campaign's marginal machinery closes on quantities that decompose ADDITIVELY into
terms reading at most two labels each.  `Gtz.thresholdForm` does: its pivot surplus `p`
and its far pairing `w` never occur in the same monomial, so the mixed second difference
in those two slots vanishes identically (`Gtz.thresholdForm_mixed_difference`).

The offset does not.  `Gtz.offsetForm p u v w = p * w - u * v` carries the monomial
`p * w`, a product across DISJOINT label sets — the pivot alone against the far pair —
and its mixed second difference is the constant one
(`Gtz.offsetForm_mixed_difference`).  A single nonvanishing mixed difference rules out
every decomposition into a sum of terms each omitting `p` or each omitting `w`
(`Gtz.offsetForm_not_additive`, `Gtz.offsetForm_not_split`).  The same computation kills
it for `Gtz.tripleDetForm` itself (`Gtz.tripleDetForm_mixed_difference`).

**So the offset is genuinely three-local and the marginal machinery does not apply to it
as written.**  What survives is weaker and still useful: the offset's FIRST marginal
closes, because summing `u * v` over the far labels is a squared row sum minus a row
energy, and both are landed (`Gtz.sum_offDiagProduct_erase`).

## 2. The shifted row law

The criterion reads the pair minors of the SHIFTED form `Gtz.diagonalShiftForm`, whose
diagonal is the excess `P c c - w c` and whose off-diagonal is `P c d`.  These are not
the projection pair minors that `Gtz.sum_pairMinor_projection` totals.  The shifted row
law is new:

    ∑ over d ≠ c of pairMinorAt (diagonalShiftForm D) c d
      = excess c * ((rank - 1) - excess c) - P c c * (1 - P c c)

(`Gtz.sum_pairMinorAt_diagonalShift_erase`), from the landed trace of the shift and the
landed row energy, with no Cauchy-Binet.  At `(6,3)` the first factor carries `2`.

## 3. The ceiling is a refuter, not a producer

`Gtz.tripleDetForm_le_minorProduct_div` bounds the third minor ABOVE by
`pairMinorForm p q u * pairMinorForm p r v / p`.  An upper bound can never certify
existence, and this file records that in kernel: a positive ceiling does not imply a
positive minor (`Gtz.not_tripleDetForm_pos_of_minorProductCeiling_pos`), while a
nonpositive ceiling does force a nonpositive minor
(`Gtz.tripleDetForm_nonpos_of_minorProductCeiling_nonpos`).  So the ceiling's value is
refutation, and every summed or maximised form of it is vacuous for the objective by
direction alone.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Wave.ProjectionMinorShift
import Gtz.Wave.ProjectionBlockObjective
import Gtz.Wave.ElliptopeGapBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ### 1. The offset form -/

/-- The **offset**: the quantity whose square the pivot minor product must beat.  It is
the numerator of the interval's centre, `p * w - u * v`. -/
def offsetForm (p u v w : ℝ) : ℝ := p * w - u * v

theorem offsetForm_apply (p u v w : ℝ) : offsetForm p u v w = p * w - u * v := rfl

theorem offsetForm_neg_far (p u v w : ℝ) :
    offsetForm p u v (-w) = -(p * w) - u * v := by
  rw [offsetForm]; ring

/-- Flipping the sign of BOTH pivot pairings fixes the offset. -/
theorem offsetForm_neg_both (p u v w : ℝ) :
    offsetForm p (-u) (-v) w = offsetForm p u v w := by
  rw [offsetForm, offsetForm]; ring

/-- The pivot Schur identity in the offset vocabulary. -/
theorem pairMinorForm_mul_sub_offsetForm_sq (p q r u v w : ℝ) :
    pairMinorForm p q u * pairMinorForm p r v - offsetForm p u v w ^ 2
      = p * tripleDetForm p q r u v w := by
  rw [offsetForm]; exact pairMinorForm_mul_sub_sq p q r u v w

/-- The exact criterion, restated with the offset. -/
theorem tripleDetForm_pos_iff_offsetForm_sq_lt {p : ℝ} (hp : 0 < p) (q r u v w : ℝ) :
    0 < tripleDetForm p q r u v w
      ↔ offsetForm p u v w ^ 2 < pairMinorForm p q u * pairMinorForm p r v := by
  rw [offsetForm]; exact tripleDetForm_pos_iff_sq_lt hp q r u v w

/-! ### 2. Locality: the mixed second difference in the pivot and the far pairing -/

/-- The **threshold form**: the sign-free obstruction `sigma2 - sigma1 + 1` written on
the same six scalars.  Every monomial reads at most two of the three labels. -/
def thresholdForm (p q r u v w : ℝ) : ℝ :=
  (p * q - u ^ 2) + (p * r - v ^ 2) + (q * r - w ^ 2) - (p + q + r) + 1

theorem thresholdForm_apply (p q r u v w : ℝ) :
    thresholdForm p q r u v w
      = (p * q - u ^ 2) + (p * r - v ^ 2) + (q * r - w ^ 2) - (p + q + r) + 1 := rfl

/-- **THE THRESHOLD IS TWO-LOCAL.**  Its mixed second difference in the pivot surplus
and the far pairing vanishes identically, because no monomial carries both. -/
theorem thresholdForm_mixed_difference (q r u v : ℝ) (p₀ p₁ w₀ w₁ : ℝ) :
    thresholdForm p₁ q r u v w₁ - thresholdForm p₁ q r u v w₀
      - thresholdForm p₀ q r u v w₁ + thresholdForm p₀ q r u v w₀ = 0 := by
  rw [thresholdForm, thresholdForm, thresholdForm, thresholdForm]; ring

/-- **THE OFFSET IS NOT TWO-LOCAL.**  Its mixed second difference in the pivot surplus
and the far pairing is the product of the two increments, never zero when both move. -/
theorem offsetForm_mixed_difference (u v : ℝ) (p₀ p₁ w₀ w₁ : ℝ) :
    offsetForm p₁ u v w₁ - offsetForm p₁ u v w₀
      - offsetForm p₀ u v w₁ + offsetForm p₀ u v w₀ = (p₁ - p₀) * (w₁ - w₀) := by
  rw [offsetForm, offsetForm, offsetForm, offsetForm]; ring

/-- The unit instance of the mixed difference. -/
theorem offsetForm_mixed_difference_one (u v : ℝ) :
    offsetForm 1 u v 1 - offsetForm 1 u v 0 - offsetForm 0 u v 1 + offsetForm 0 u v 0 = 1 := by
  rw [offsetForm_mixed_difference]; ring

/-- **NO ADDITIVE DECOMPOSITION.**  The offset is not a sum of four functions each
reading one slot. -/
theorem offsetForm_not_additive :
    ¬ ∃ f g h k : ℝ → ℝ, ∀ p u v w : ℝ, offsetForm p u v w = f p + g u + h v + k w := by
  rintro ⟨f, g, h, k, hall⟩
  have hone := offsetForm_mixed_difference_one 0 0
  rw [hall 1 0 0 1, hall 1 0 0 0, hall 0 0 0 1, hall 0 0 0 0] at hone
  linarith

/-- **NO SPLIT ACROSS THE PIVOT AND THE FAR PAIR.**  Stronger than the additive form:
the offset is not a sum of one function that ignores the pivot surplus and one that
ignores the far pairing.  Every genuinely two-local decomposition has that shape,
because the pivot label and the far pair are disjoint. -/
theorem offsetForm_not_split :
    ¬ ∃ f g : ℝ → ℝ → ℝ → ℝ,
        ∀ p u v w : ℝ, offsetForm p u v w = f u v w + g p u v := by
  rintro ⟨f, g, hall⟩
  have hone := offsetForm_mixed_difference_one 0 0
  rw [hall 1 0 0 1, hall 1 0 0 0, hall 0 0 0 1, hall 0 0 0 0] at hone
  linarith

/-- The same computation kills two-locality for the third minor itself. -/
theorem tripleDetForm_mixed_difference (q r u v : ℝ) (p₀ p₁ w₀ w₁ : ℝ) :
    tripleDetForm p₁ q r u v w₁ - tripleDetForm p₁ q r u v w₀
      - tripleDetForm p₀ q r u v w₁ + tripleDetForm p₀ q r u v w₀
      = -((p₁ - p₀) * (w₁ - w₀) * (w₁ + w₀)) := by
  rw [tripleDetForm, tripleDetForm, tripleDetForm, tripleDetForm]; ring

theorem tripleDetForm_not_split :
    ¬ ∃ f g : ℝ → ℝ → ℝ → ℝ,
        ∀ p q r u v w : ℝ, tripleDetForm p q r u v w = f q r w + g p q r := by
  rintro ⟨f, g, hall⟩
  have h11 := hall 1 0 0 0 0 1
  have h10 := hall 1 0 0 0 0 0
  have h01 := hall 0 0 0 0 0 1
  have h00 := hall 0 0 0 0 0 0
  rw [tripleDetForm] at h11 h10 h01 h00
  norm_num at h11 h10 h01 h00
  linarith

/-- The squared offset inherits the failure: its mixed difference at the unit corner is
also nonzero, so no two-local decomposition of the criterion's left side exists. -/
theorem sq_offsetForm_mixed_difference_ne_zero :
    offsetForm 1 0 0 1 ^ 2 - offsetForm 1 0 0 0 ^ 2
      - offsetForm 0 0 0 1 ^ 2 + offsetForm 0 0 0 0 ^ 2 = 1 := by
  rw [offsetForm, offsetForm, offsetForm, offsetForm]; norm_num

theorem sq_offsetForm_not_split :
    ¬ ∃ f g : ℝ → ℝ → ℝ → ℝ,
        ∀ p u v w : ℝ, offsetForm p u v w ^ 2 = f u v w + g p u v := by
  rintro ⟨f, g, hall⟩
  have hone := sq_offsetForm_mixed_difference_ne_zero
  rw [hall 1 0 0 1, hall 1 0 0 0, hall 0 0 0 1, hall 0 0 0 0] at hone
  linarith

/-! ### 3. The shifted form and its pair minors -/

/-- The excess at a label: the diagonal of the shifted form. -/
theorem diagonalShiftForm_diag_eq (design : WeightedDesign size rank) (label : Fin size) :
    diagonalShiftForm design label label
      = projectionOfDesign design label label - design.weight label :=
  diagonalShiftForm_diag design label

/-- The pair minor of the shifted form, expanded. -/
theorem pairMinorAt_diagonalShift_eq (design : WeightedDesign size rank)
    {first second : Fin size} (hne : first ≠ second) :
    pairMinorAt (diagonalShiftForm design) first second
      = (projectionOfDesign design first first - design.weight first)
          * (projectionOfDesign design second second - design.weight second)
        - projectionOfDesign design first second ^ 2 := by
  rw [pairMinorAt, diagonalShiftForm_diag, diagonalShiftForm_diag,
    diagonalShiftForm_offDiag design hne]

/-- The shifted diagonal totals `rank - 1`: the projection diagonal sums to the rank and
the weights sum to one. -/
theorem sum_diagonalShiftForm_diag (design : WeightedDesign size rank) :
    ∑ label : Fin size, diagonalShiftForm design label label = (rank : ℝ) - 1 := by
  have hshift : ∀ label : Fin size,
      diagonalShiftForm design label label
        = projectionOfDesign design label label - design.weight label :=
    fun label => diagonalShiftForm_diag design label
  rw [Finset.sum_congr rfl fun label _ => hshift label, Finset.sum_sub_distrib,
    sum_projectionDiagonal_eq_rank design, design.weight_sum_one]

/-- **THE SHIFTED ROW LAW.**  The pair minors of the shifted form along one row are
pinned by that row's excess and its projection diagonal alone.  The landed
`Gtz.sum_pairMinor_projection` is the unshifted statement and does NOT supply this: the
weight shift moves the diagonal but not the off-diagonal, so the two rows differ. -/
theorem sum_pairMinorAt_diagonalShift_erase (design : WeightedDesign size rank)
    (label : Fin size) :
    ∑ other ∈ Finset.univ.erase label, pairMinorAt (diagonalShiftForm design) label other
      = diagonalShiftForm design label label
          * ((rank : ℝ) - 1 - diagonalShiftForm design label label)
        - projectionOfDesign design label label
            * (1 - projectionOfDesign design label label) := by
  classical
  have hexpand : ∀ other ∈ Finset.univ.erase label,
      pairMinorAt (diagonalShiftForm design) label other
        = diagonalShiftForm design label label * diagonalShiftForm design other other
          - projectionOfDesign design label other ^ 2 := by
    intro other hother
    have hne : label ≠ other := (Finset.ne_of_mem_erase hother).symm
    rw [pairMinorAt, diagonalShiftForm_offDiag design hne]
  rw [Finset.sum_congr rfl hexpand, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_erase_sq_projectionRow design label]
  have hrest : ∑ other ∈ Finset.univ.erase label, diagonalShiftForm design other other
      = ((rank : ℝ) - 1) - diagonalShiftForm design label label := by
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun other : Fin size => diagonalShiftForm design other other)
      (Finset.mem_univ label)
    rw [sum_diagonalShiftForm_diag design] at hsplit
    linarith
  rw [hrest]

/-- The `(6,3)` instance: the shifted diagonal totals two. -/
theorem sum_pairMinorAt_diagonalShift_erase_sixThree (design : WeightedDesign 6 3)
    (label : Fin 6) :
    ∑ other ∈ Finset.univ.erase label, pairMinorAt (diagonalShiftForm design) label other
      = diagonalShiftForm design label label
          * (2 - diagonalShiftForm design label label)
        - projectionOfDesign design label label
            * (1 - projectionOfDesign design label label) := by
  rw [sum_pairMinorAt_diagonalShift_erase design label]
  norm_num

/-- The row total in the excess vocabulary. -/
theorem sum_pairMinorAt_diagonalShift_erase_excess (design : WeightedDesign 6 3)
    (label : Fin 6) :
    ∑ other ∈ Finset.univ.erase label, pairMinorAt (diagonalShiftForm design) label other
      = (projectionOfDesign design label label - design.weight label)
          * (2 - (projectionOfDesign design label label - design.weight label))
        - projectionOfDesign design label label
            * (1 - projectionOfDesign design label label) := by
  rw [sum_pairMinorAt_diagonalShift_erase_sixThree design label,
    diagonalShiftForm_diag design label]

/-- **THE ROW SUM IS POSITIVE AT A HEAVY ENOUGH LABEL.**  Writing `t` for the projection
diagonal and `e` for the excess, the row total is `e * (2 - e) - t * (1 - t)`, so a label
whose excess exceeds its own coupling carries a positive row of shifted pair minors. -/
theorem sum_pairMinorAt_diagonalShift_erase_pos (design : WeightedDesign 6 3)
    (label : Fin 6)
    (hgt : projectionOfDesign design label label
        * (1 - projectionOfDesign design label label)
      < (projectionOfDesign design label label - design.weight label)
          * (2 - (projectionOfDesign design label label - design.weight label))) :
    0 < ∑ other ∈ Finset.univ.erase label,
        pairMinorAt (diagonalShiftForm design) label other := by
  rw [sum_pairMinorAt_diagonalShift_erase_excess design label]
  linarith

/-! ### 4. The one-label pigeonhole -/

/-- **THE FIXED-PARTNER PIGEONHOLE.**  Once one partner is spent, the remaining four
share the rest of the row, so one of them carries at least a quarter of it.  This is the
statement the criterion can consume, because the criterion needs a PAIR of partners at a
common pivot and the row law pins only their total. -/
theorem exists_pairMinorAt_diagonalShift_ge (design : WeightedDesign 6 3)
    (label partner : Fin 6) (hne : partner ≠ label) :
    ∃ other ∈ (Finset.univ.erase label).erase partner,
      (∑ d ∈ Finset.univ.erase label, pairMinorAt (diagonalShiftForm design) label d
          - pairMinorAt (diagonalShiftForm design) label partner) / 4
        ≤ pairMinorAt (diagonalShiftForm design) label other := by
  classical
  set rowTotal := ∑ d ∈ Finset.univ.erase label,
    pairMinorAt (diagonalShiftForm design) label d with hrow
  set spent := pairMinorAt (diagonalShiftForm design) label partner with hspent
  set rest := (Finset.univ.erase label).erase partner with hrest
  have hpartner : partner ∈ Finset.univ.erase label :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ partner⟩
  have hsum : ∑ d ∈ rest, pairMinorAt (diagonalShiftForm design) label d
      = rowTotal - spent := by
    have := Finset.add_sum_erase (Finset.univ.erase label)
      (fun d : Fin 6 => pairMinorAt (diagonalShiftForm design) label d) hpartner
    rw [hrow, hspent, hrest]
    linarith [this]
  have hcard : rest.card = 4 := by
    rw [hrest, Finset.card_erase_of_mem hpartner, Finset.card_erase_of_mem
      (Finset.mem_univ label)]
    simp
  have hne_empty : rest.Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  by_contra hcon
  push Not at hcon
  have hstrict : ∑ d ∈ rest, pairMinorAt (diagonalShiftForm design) label d
      < ∑ _d ∈ rest, (rowTotal - spent) / 4 := by
    refine Finset.sum_lt_sum_of_nonempty hne_empty ?_
    intro d hd
    exact hcon d hd
  rw [Finset.sum_const, hcard, hsum] at hstrict
  simp only [nsmul_eq_mul] at hstrict
  push_cast at hstrict
  linarith

/-- The product form: a positive spent partner turns the pigeonhole into a lower bound on
the pivot minor PRODUCT, which is the criterion's right-hand side. -/
theorem exists_pairMinorAt_product_ge (design : WeightedDesign 6 3)
    (label partner : Fin 6) (hne : partner ≠ label)
    (hpos : 0 < pairMinorAt (diagonalShiftForm design) label partner) :
    ∃ other ∈ (Finset.univ.erase label).erase partner,
      pairMinorAt (diagonalShiftForm design) label partner
          * ((∑ d ∈ Finset.univ.erase label,
                pairMinorAt (diagonalShiftForm design) label d
              - pairMinorAt (diagonalShiftForm design) label partner) / 4)
        ≤ pairMinorAt (diagonalShiftForm design) label partner
            * pairMinorAt (diagonalShiftForm design) label other := by
  obtain ⟨other, hmem, hge⟩ :=
    exists_pairMinorAt_diagonalShift_ge design label partner hne
  exact ⟨other, hmem, by nlinarith [hge, hpos]⟩

/-! ### 5. The sign obstruction: a row total cannot force a positive product -/

/-- Two entries of the same strict sign give a positive product.  This is the only
unconditional way a row produces a positive pivot minor product. -/
theorem mul_pos_of_both_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := mul_pos ha hb

theorem mul_pos_of_both_neg {a b : ℝ} (ha : a < 0) (hb : b < 0) : 0 < a * b :=
  mul_pos_of_neg_of_neg ha hb

/-- **THE ROW TOTAL ALONE IS NOT ENOUGH.**  Five reals can total any positive value with
every pairwise product zero, so no bound derived from the shifted row law by itself can
force a positive pivot minor product.  The witness puts the whole row on one partner. -/
theorem not_forall_exists_pos_product_of_sum_pos :
    ¬ ∀ M : Fin 5 → ℝ, 0 < ∑ i, M i →
        ∃ i j : Fin 5, i ≠ j ∧ 0 < M i * M j := by
  intro hall
  have hsum : (0 : ℝ) < ∑ i : Fin 5, (if i = 0 then (1 : ℝ) else 0) := by
    simp
  obtain ⟨i, j, hij, hpos⟩ := hall (fun i => if i = 0 then 1 else 0) hsum
  rcases Decidable.em (i = 0) with hi | hi
  · rcases Decidable.em (j = 0) with hj | hj
    · exact hij (hi.trans hj.symm)
    · simp only [hi, hj, if_true, if_false, mul_zero] at hpos
      exact lt_irrefl 0 hpos
  · simp only [hi, if_false, zero_mul] at hpos
    exact lt_irrefl 0 hpos

/-- The complementary positive statement: if two partners of a row carry strictly
positive shifted pair minors then that row does supply a positive product. -/
theorem exists_pos_product_of_two_pos (design : WeightedDesign 6 3)
    (label first second : Fin 6)
    (hfirst : 0 < pairMinorAt (diagonalShiftForm design) label first)
    (hsecond : 0 < pairMinorAt (diagonalShiftForm design) label second) :
    0 < pairMinorAt (diagonalShiftForm design) label first
        * pairMinorAt (diagonalShiftForm design) label second :=
  mul_pos hfirst hsecond

/-- Two NEGATIVE partners work equally well, which is why the criterion survives at the
`(+, -, -)` signature the campaign already exhibits. -/
theorem exists_pos_product_of_two_neg (design : WeightedDesign 6 3)
    (label first second : Fin 6)
    (hfirst : pairMinorAt (diagonalShiftForm design) label first < 0)
    (hsecond : pairMinorAt (diagonalShiftForm design) label second < 0) :
    0 < pairMinorAt (diagonalShiftForm design) label first
        * pairMinorAt (diagonalShiftForm design) label second :=
  mul_pos_of_neg_of_neg hfirst hsecond

/-! ### 6. The ceiling is a refuter, not a producer -/

/-- The **minor product ceiling**: the largest third minor a pivot's two pair minors
permit, attained exactly when the far pairing sits at the interval's centre. -/
noncomputable def minorProductCeiling (p q r u v : ℝ) : ℝ :=
  pairMinorForm p q u * pairMinorForm p r v / p

theorem minorProductCeiling_apply (p q r u v : ℝ) :
    minorProductCeiling p q r u v = pairMinorForm p q u * pairMinorForm p r v / p := rfl

/-- The ceiling bounds the third minor above, at every far pairing. -/
theorem tripleDetForm_le_minorProductCeiling {p : ℝ} (hp : 0 < p) (q r u v w : ℝ) :
    tripleDetForm p q r u v w ≤ minorProductCeiling p q r u v := by
  rw [minorProductCeiling]
  exact tripleDetForm_le_minorProduct_div hp q r u v w

/-- **THE REFUTER FORM.**  A nonpositive ceiling forces a nonpositive third minor, so no
triple at that pivot dominates.  This is the only direction an upper bound can be used. -/
theorem tripleDetForm_nonpos_of_minorProductCeiling_nonpos {p : ℝ} (hp : 0 < p)
    (q r u v w : ℝ) (hceil : minorProductCeiling p q r u v ≤ 0) :
    tripleDetForm p q r u v w ≤ 0 :=
  le_trans (tripleDetForm_le_minorProductCeiling hp q r u v w) hceil

/-- **THE CEILING IS NOT A PRODUCER, AND THIS IS A THEOREM RATHER THAN A REMARK.**  A
strictly positive ceiling does not imply a positive third minor: at `p = q = r = 1`,
`u = v = 0` the ceiling is one for every far pairing, while `w = 1` makes the minor
vanish and `w = 2` makes it strictly negative.  So every summed or maximised form of the
ceiling is vacuous for the objective by direction alone. -/
theorem not_tripleDetForm_pos_of_minorProductCeiling_pos :
    ¬ ∀ p q r u v w : ℝ, 0 < p → 0 < minorProductCeiling p q r u v →
        0 < tripleDetForm p q r u v w := by
  intro hall
  have hceil : (0 : ℝ) < minorProductCeiling 1 1 1 0 0 := by
    simp only [minorProductCeiling, pairMinorForm]; norm_num
  have hpos := hall 1 1 1 0 0 2 (by norm_num) hceil
  rw [tripleDetForm] at hpos
  norm_num at hpos

/-- The witness values, recorded exactly. -/
theorem witness_minorProductCeiling : minorProductCeiling 1 1 1 0 0 = 1 := by
  simp only [minorProductCeiling, pairMinorForm]; norm_num

theorem witness_tripleDetForm_neg : tripleDetForm 1 1 1 0 0 2 = -3 := by
  rw [tripleDetForm]; norm_num

/-- The gap between the ceiling and the truth is exactly the squared offset over the
pivot, so the ceiling is attained precisely at the interval's centre. -/
theorem minorProductCeiling_sub_tripleDetForm {p : ℝ} (hp : 0 < p) (q r u v w : ℝ) :
    minorProductCeiling p q r u v - tripleDetForm p q r u v w
      = offsetForm p u v w ^ 2 / p := by
  rw [minorProductCeiling, offsetForm]
  field_simp
  nlinarith [pairMinorForm_mul_sub_sq p q r u v w]

/-! ### 7. The salvage: the offset's first marginal does close -/

/-- Summing a product of two distinct entries of one row is the squared row sum less the
row energy.  Pure `Finset` algebra, stated for an arbitrary family. -/
theorem sum_sq_sub_sum_sq_eq_sum_erase {α : Type*} [DecidableEq α] (s : Finset α)
    (x : α → ℝ) :
    ∑ b ∈ s, ∑ c ∈ s.erase b, x b * x c
      = (∑ b ∈ s, x b) ^ 2 - ∑ b ∈ s, x b ^ 2 := by
  have hinner : ∀ b ∈ s, ∑ c ∈ s.erase b, x b * x c
      = (∑ c ∈ s, x b * x c) - x b * x b := by
    intro b hb
    have := Finset.add_sum_erase s (fun c => x b * x c) hb
    linarith [this]
  rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib]
  have hsq : ∑ b ∈ s, ∑ c ∈ s, x b * x c = (∑ b ∈ s, x b) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  rw [hsq]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [sq]

/-- **THE OFFSET'S FIRST MARGINAL CLOSES.**  Even though the offset is not two-local, its
sum over the ordered far pairs at a fixed pivot reduces to the pivot's squared row sum
and the landed row energy, with no new invariant.  This is the exact sense in which the
marginal machinery still reaches the offset. -/
theorem sum_offDiagProduct_erase (design : WeightedDesign size rank) (label : Fin size) :
    ∑ first ∈ Finset.univ.erase label,
        ∑ second ∈ (Finset.univ.erase label).erase first,
          projectionOfDesign design label first * projectionOfDesign design label second
      = (∑ first ∈ Finset.univ.erase label, projectionOfDesign design label first) ^ 2
        - projectionOfDesign design label label
            * (1 - projectionOfDesign design label label) := by
  classical
  rw [sum_sq_sub_sum_sq_eq_sum_erase (Finset.univ.erase label)
    (fun first => projectionOfDesign design label first),
    sum_erase_sq_projectionRow design label]

/-! ### 8. The row total and an unconditional positive row -/

/-- The uniform-weight row total is affine in the projection diagonal alone. -/
theorem sum_pairMinorAt_diagonalShift_erase_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ c : Fin 6, design.weight c = (6 : ℝ)⁻¹) (label : Fin 6) :
    ∑ other ∈ Finset.univ.erase label, pairMinorAt (diagonalShiftForm design) label other
      = 4 * projectionOfDesign design label label / 3 - 13 / 36 := by
  rw [sum_pairMinorAt_diagonalShift_erase_excess design label, huniform label]
  ring

/-- **CALIBRATION AGAINST THE LANDED TOTAL.**  Summing the new row law over the six
labels returns `11/6`, which is exactly the value the landed
`Gtz.sum_pairMinorAt_diagonalShift_uniform` gives for the level-two total at `(6,3)`.
The corpus had the TOTAL and not the ROW, and the row refines it. -/
theorem sum_sum_pairMinorAt_diagonalShift_erase_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ c : Fin 6, design.weight c = (6 : ℝ)⁻¹) :
    ∑ label : Fin 6, ∑ other ∈ Finset.univ.erase label,
        pairMinorAt (diagonalShiftForm design) label other = 11 / 6 := by
  classical
  rw [Finset.sum_congr rfl fun label _ =>
    sum_pairMinorAt_diagonalShift_erase_uniform design huniform label]
  rw [Finset.sum_sub_distrib]
  have hdiag : ∑ _label : Fin 6, (13 : ℝ) / 36 = 13 / 6 := by simp; norm_num
  have hlead : ∑ label : Fin 6, 4 * projectionOfDesign design label label / 3 = 4 := by
    have : ∀ label : Fin 6, 4 * projectionOfDesign design label label / 3
        = (4 / 3) * projectionOfDesign design label label := fun label => by ring
    rw [Finset.sum_congr rfl fun label _ => this label, ← Finset.mul_sum,
      sum_projectionDiagonal_eq_rank design]
    norm_num
  rw [hdiag, hlead]
  norm_num

/-- **SOME LABEL ALWAYS CARRIES A POSITIVE ROW, AT UNIFORM WEIGHT, UNCONDITIONALLY.**
The projection diagonal totals the rank, so some label is at least one half, and the
uniform row total is affine and already positive there.  The one-label pigeonhole on the
THRESHOLD is dead by theorem; the same pigeonhole on the shifted pair minors is alive,
and this is the difference between the two sides of the criterion. -/
theorem exists_pos_sum_pairMinorAt_diagonalShift_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ c : Fin 6, design.weight c = (6 : ℝ)⁻¹) :
    ∃ label : Fin 6, 0 < ∑ other ∈ Finset.univ.erase label,
      pairMinorAt (diagonalShiftForm design) label other := by
  classical
  have hsum : ∑ _c : Fin 6, (1 / 2 : ℝ)
      ≤ ∑ c : Fin 6, projectionOfDesign design c c := by
    rw [sum_projectionDiagonal_eq_rank design]
    simp
    norm_num
  obtain ⟨label, -, hlabel⟩ :=
    Finset.exists_le_of_sum_le (Finset.univ_nonempty) hsum
  refine ⟨label, ?_⟩
  rw [sum_pairMinorAt_diagonalShift_erase_uniform design huniform label]
  linarith

/-- The explicit floor at such a label. -/
theorem sum_pairMinorAt_diagonalShift_ge_of_half (design : WeightedDesign 6 3)
    (huniform : ∀ c : Fin 6, design.weight c = (6 : ℝ)⁻¹) (label : Fin 6)
    (hhalf : (1 : ℝ) / 2 ≤ projectionOfDesign design label label) :
    (11 : ℝ) / 36 ≤ ∑ other ∈ Finset.univ.erase label,
      pairMinorAt (diagonalShiftForm design) label other := by
  rw [sum_pairMinorAt_diagonalShift_erase_uniform design huniform label]
  linarith

end Gtz
