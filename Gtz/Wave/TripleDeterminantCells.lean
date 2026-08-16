import Gtz.Wave.AdmissiblePairGraph
import Gtz.Design.LivePairExistence

/-!
# The third Sylvester minor: cells, a sharp constant, and the witness that the
# residual is genuinely open

`Gtz.posDef_iff_thirdInvariant_of_admissibleTriangle` reduced the one-line
residual to ONE determinant sign at an admissible triangle.  This file settles
what that sign costs.

Write `p = l_a - 1`, `q = l_b - 1`, `r = l_c - 1` and `u = a . b`, `v = a . c`,
`w = b . c`.  Then `Gtz.tripleGapDet` is the polynomial

  `p q r - p w^2 - q v^2 - r u^2 + 2 u v w`

and the triangle hypothesis says exactly `u^2 < p q`, `v^2 < p r`, `w^2 < q r`.

THE TRIANGLE DOES NOT FORCE THE SIGN.  On the equilateral locus `p = q = r = P`,
`u = v = w = -t` the polynomial factors as `(P - 2 t) (P + t)^2`, so it is
negative for every `t` in `(P/2, P)` while all three pair minors `P^2 - t^2` stay
positive.  `Gtz.not_forall_tripleGapDet_pos_of_admissibleTriangle` exhibits an
explicit rational NON-DEGENERATE triple with this behaviour.  The campaign had a
measured failure rate at triangles and no witness; this is that witness.

What does force the sign is a QUARTER SLACK: strengthening each pair minor to
`4 u^2 < p q` makes the determinant positive for BOTH signs of the triple
product `u v w`, and the equilateral factorization shows the constant four is
attained.  `Gtz.not_forall_tripleDetForm_pos_of_doubleSlack` shows two does not
suffice, so the optimal constant lies in `(2, 4]`.

The second cell reads the sign instead of the size: when `u v w` is nonnegative
the cross term helps, and a plain sum condition suffices.  The two cells are
incomparable, and both are incomparable with the landed diagonal-dominance cell.

The last section records why a cell reading no pairings can never work here.  The
row law caps every pairing by `4 w_c w_d (a_c . a_d)^2 <= 1`, while the heavy
mass ceiling gives `w_c (l_c - 1) < 1`; the two are exactly complementary, so the
cap can never certify a quarter slack.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The determinant as a scalar polynomial -/

/-- The third Sylvester minor as a polynomial in three surpluses and three
pairings.  Separating it from the atoms is what lets the sharpness analysis run
on a locus no rational vector triple realises. -/
def tripleDetForm (p q r u v w : ℝ) : ℝ :=
  p * q * r - p * w ^ 2 - q * v ^ 2 - r * u ^ 2 + 2 * (u * v * w)

theorem tripleGapDet_eq_tripleDetForm (a b c : Fin 3 → ℝ) :
    tripleGapDet a b c
      = tripleDetForm (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
          (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c) := by
  rw [tripleGapDet, tripleDetForm]; ring

/-- The pair minor as a polynomial in two surpluses and their pairing. -/
theorem pairGapMinor_eq_sub_sq (a b : Fin 3 → ℝ) :
    pairGapMinor a b = (leverageOf a - 1) * (leverageOf b - 1) - (a ⬝ᵥ b) ^ 2 := rfl

/-- **THE THIRD MINOR IS A MATRIX DETERMINANT.**  `Gtz.tripleGapDet` is defined as
a polynomial and used through `Gtz.tripleGram_posDef_iff_pairVocabulary`, which
reaches it through leading minors.  This identifies it with the determinant
itself, which is what lets the projection-block bridge apply to it. -/
theorem det_tripleGram_sub_one (a b c : Fin 3 → ℝ) :
    (tripleGram a b c - 1).det = tripleGapDet a b c := by
  rw [Matrix.det_fin_three]
  simp only [gap_zero_zero, gap_zero_one, gap_zero_two, gap_one_zero, gap_one_one,
    gap_one_two, gap_two_zero, gap_two_one, gap_two_two, tripleGapDet]
  ring

/-! ### The permutation action

`tripleGapDet` is a determinant, so it is invariant under relabelling the three
atoms.  In the scalar form the surpluses permute and the pairings permute with
them.  The corpus carries the invariance only at the `PosDef` level
(`Gtz.subsetSum_posDef_iff_tripleGram_swap`); these are the scalar identities. -/

theorem tripleDetForm_swap_first_second (p q r u v w : ℝ) :
    tripleDetForm q p r u w v = tripleDetForm p q r u v w := by
  rw [tripleDetForm, tripleDetForm]; ring

theorem tripleDetForm_swap_second_third (p q r u v w : ℝ) :
    tripleDetForm p r q v u w = tripleDetForm p q r u v w := by
  rw [tripleDetForm, tripleDetForm]; ring

theorem tripleDetForm_swap_first_third (p q r u v w : ℝ) :
    tripleDetForm r q p w v u = tripleDetForm p q r u v w := by
  rw [tripleDetForm, tripleDetForm]; ring

theorem tripleDetForm_rotate (p q r u v w : ℝ) :
    tripleDetForm q r p w u v = tripleDetForm p q r u v w := by
  rw [tripleDetForm, tripleDetForm]; ring

/-- The cross term is the only place the pairings enter oddly, so flipping the
sign of one atom leaves the determinant fixed.  This is why the sign of the
triple product is intrinsic to the triple and cannot be chosen. -/
theorem tripleDetForm_neg_first (p q r u v w : ℝ) :
    tripleDetForm p q r (-u) (-v) w = tripleDetForm p q r u v w := by
  rw [tripleDetForm, tripleDetForm]; ring

theorem tripleDetForm_neg_second (p q r u v w : ℝ) :
    tripleDetForm p q r (-u) v (-w) = tripleDetForm p q r u v w := by
  rw [tripleDetForm, tripleDetForm]; ring

theorem tripleDetForm_neg_third (p q r u v w : ℝ) :
    tripleDetForm p q r u (-v) (-w) = tripleDetForm p q r u v w := by
  rw [tripleDetForm, tripleDetForm]; ring

/-! ## 2. The equilateral locus, and where the sharp constant comes from -/

/-- **THE EQUILATERAL FACTORIZATION.**  On the locus of equal surpluses and equal
negative pairings the third minor factors completely.  Everything about the sharp
constant is visible in this one identity. -/
theorem tripleDetForm_equilateral (bigP smallT : ℝ) :
    tripleDetForm bigP bigP bigP (-smallT) (-smallT) (-smallT)
      = (bigP - 2 * smallT) * (bigP + smallT) ^ 2 := by
  rw [tripleDetForm]; ring

/-- On the equilateral locus the triangle hypothesis is exactly `t < P`. -/
theorem equilateral_pairMinor_pos_iff (bigP smallT : ℝ) (hP : 0 < bigP)
    (hT : 0 ≤ smallT) :
    0 < bigP * bigP - (-smallT) ^ 2 ↔ smallT < bigP := by
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **THE CONSTANT FOUR IS ATTAINED.**  On the equilateral locus the determinant
is positive exactly when the quarter slack holds, so no constant below four can
be sound and four itself is not wasteful. -/
theorem tripleDetForm_equilateral_pos_iff (bigP smallT : ℝ) (hP : 0 < bigP)
    (hT : 0 ≤ smallT) :
    0 < tripleDetForm bigP bigP bigP (-smallT) (-smallT) (-smallT)
      ↔ 4 * smallT ^ 2 < bigP * bigP := by
  rw [tripleDetForm_equilateral]
  have hsq : 0 < (bigP + smallT) ^ 2 := by positivity
  constructor
  · intro h
    have hlin : 0 < bigP - 2 * smallT := by
      by_contra hcon
      push Not at hcon
      nlinarith
    nlinarith
  · intro h
    have hlin : 0 < bigP - 2 * smallT := by nlinarith
    positivity

/-- The equilateral locus is genuinely inside the triangle region for every `t`
strictly between `P/2` and `P`, so the failure is not a boundary artifact. -/
theorem tripleDetForm_equilateral_neg_of_between (bigP smallT : ℝ) (hP : 0 < bigP)
    (hlow : bigP < 2 * smallT) (hhigh : smallT < bigP) :
    tripleDetForm bigP bigP bigP (-smallT) (-smallT) (-smallT) < 0
      ∧ 0 < bigP * bigP - (-smallT) ^ 2 := by
  have hTpos : 0 < smallT := by linarith
  refine ⟨?_, by nlinarith⟩
  rw [tripleDetForm_equilateral]
  have hsq : 0 < (bigP + smallT) ^ 2 := by positivity
  nlinarith

/-! ## 3. The quarter-slack cell -/

/-- The quarter slack forces the pair minor, so the cell subsumes the triangle
rather than assuming it. -/
theorem pairMinor_pos_of_quarterSlack (p q u : ℝ) (_hp : 0 < p) (_hq : 0 < q)
    (hslack : 4 * u ^ 2 < p * q) : 0 < p * q - u ^ 2 := by
  nlinarith [sq_nonneg u]

/-- The product of the three slacks bounds the square of the cross term.  This is
the step that makes the cell sign-free: it never reads the sign of `u v w`, only
its magnitude. -/
theorem sq_cross_lt_of_quarterSlack (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hu : 4 * u ^ 2 < p * q) (hv : 4 * v ^ 2 < p * r) (hw : 4 * w ^ 2 < q * r) :
    (2 * (u * v * w)) ^ 2 < (p * q * r / 4) ^ 2 := by
  have hpq : 0 < p * q := mul_pos hp hq
  have hpr : 0 < p * r := mul_pos hp hr
  have hqr : 0 < q * r := mul_pos hq hr
  have huv : u ^ 2 * v ^ 2 < (p * q / 4) * (p * r / 4) := by
    nlinarith [sq_nonneg u, sq_nonneg v, hpq, hpr]
  have hprod : u ^ 2 * v ^ 2 * w ^ 2 < (p * q / 4) * (p * r / 4) * (q * r / 4) := by
    nlinarith [sq_nonneg w, sq_nonneg (u * v), mul_pos hpq hpr, hqr]
  nlinarith [hprod]

/-- **THE QUARTER-SLACK CELL.**  Strengthening every pair minor by a factor four
forces the third minor positive, for either sign of the triple product.  The
constant is attained on the equilateral locus. -/
theorem tripleDetForm_pos_of_quarterSlack (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hu : 4 * u ^ 2 < p * q) (hv : 4 * v ^ 2 < p * r) (hw : 4 * w ^ 2 < q * r) :
    0 < tripleDetForm p q r u v w := by
  have hpqr : 0 < p * q * r := by positivity
  have hru : r * u ^ 2 < p * q * r / 4 := by nlinarith
  have hqv : q * v ^ 2 < p * q * r / 4 := by nlinarith
  have hpw : p * w ^ 2 < p * q * r / 4 := by nlinarith
  have hsq := sq_cross_lt_of_quarterSlack p q r u v w hp hq hr hu hv hw
  have hcross : -(p * q * r / 4) < 2 * (u * v * w) := by nlinarith [hsq, hpqr]
  rw [tripleDetForm]; linarith

/-- The quarter-slack cell at the atom level. -/
theorem tripleGapDet_pos_of_quarterSlack (a b c : Fin 3 → ℝ)
    (ha : 1 < leverageOf a) (hb : 1 < leverageOf b) (hc : 1 < leverageOf c)
    (hab : 4 * (a ⬝ᵥ b) ^ 2 < (leverageOf a - 1) * (leverageOf b - 1))
    (hac : 4 * (a ⬝ᵥ c) ^ 2 < (leverageOf a - 1) * (leverageOf c - 1))
    (hbc : 4 * (b ⬝ᵥ c) ^ 2 < (leverageOf b - 1) * (leverageOf c - 1)) :
    0 < tripleGapDet a b c := by
  rw [tripleGapDet_eq_tripleDetForm]
  exact tripleDetForm_pos_of_quarterSlack _ _ _ _ _ _ (by linarith) (by linarith)
    (by linarith) hab hac hbc

/-- The quarter slack gives the whole Sylvester chain, so it is a standalone
cell: it needs no triangle hypothesis and no heaviness beyond its own. -/
theorem tripleGram_posDef_of_quarterSlack (a b c : Fin 3 → ℝ)
    (ha : 1 < leverageOf a) (hb : 1 < leverageOf b) (hc : 1 < leverageOf c)
    (hab : 4 * (a ⬝ᵥ b) ^ 2 < (leverageOf a - 1) * (leverageOf b - 1))
    (hac : 4 * (a ⬝ᵥ c) ^ 2 < (leverageOf a - 1) * (leverageOf c - 1))
    (hbc : 4 * (b ⬝ᵥ c) ^ 2 < (leverageOf b - 1) * (leverageOf c - 1)) :
    (tripleGram a b c - 1).PosDef := by
  rw [tripleGram_posDef_iff_pairVocabulary]
  refine ⟨by linarith, ?_, tripleGapDet_pos_of_quarterSlack a b c ha hb hc hab hac hbc⟩
  rw [pairGapMinor]
  exact pairMinor_pos_of_quarterSlack _ _ _ (by linarith) (by linarith) hab

/-- The quarter-slack cell at the design level. -/
theorem subsetSum_posDef_of_quarterSlack {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : 1 < leverageOf (D.atom x)) (hy : 1 < leverageOf (D.atom y))
    (hz : 1 < leverageOf (D.atom z))
    (hxyS : 4 * (D.atom x ⬝ᵥ D.atom y) ^ 2
      < (leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1))
    (hxzS : 4 * (D.atom x ⬝ᵥ D.atom z) ^ 2
      < (leverageOf (D.atom x) - 1) * (leverageOf (D.atom z) - 1))
    (hyzS : 4 * (D.atom y ⬝ᵥ D.atom z) ^ 2
      < (leverageOf (D.atom y) - 1) * (leverageOf (D.atom z) - 1)) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef :=
  (subsetSum_posDef_iff_tripleGram D x y z hxy hxz hyz).mpr
    (tripleGram_posDef_of_quarterSlack _ _ _ hx hy hz hxyS hxzS hyzS)

/-! ## 4. The sign-aware cell -/

/-- **THE SIGN-AWARE CELL.**  When the triple product is nonnegative the cross
term only helps, and a plain sum condition suffices.  This fires on triples the
quarter slack rejects, because it reads the sign the quarter slack refuses to
look at. -/
theorem tripleDetForm_pos_of_nonneg_cross (p q r u v w : ℝ)
    (hcross : 0 ≤ u * v * w)
    (hsum : r * u ^ 2 + q * v ^ 2 + p * w ^ 2 < p * q * r) :
    0 < tripleDetForm p q r u v w := by
  rw [tripleDetForm]; linarith

theorem tripleGapDet_pos_of_nonneg_cross (a b c : Fin 3 → ℝ)
    (hcross : 0 ≤ (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c))
    (hsum : (leverageOf c - 1) * (a ⬝ᵥ b) ^ 2 + (leverageOf b - 1) * (a ⬝ᵥ c) ^ 2
        + (leverageOf a - 1) * (b ⬝ᵥ c) ^ 2
      < (leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1)) :
    0 < tripleGapDet a b c := by
  rw [tripleGapDet_eq_tripleDetForm]
  exact tripleDetForm_pos_of_nonneg_cross _ _ _ _ _ _ hcross hsum

/-- The sign-aware cell at the design level, with the triangle supplying the two
lower minors. -/
theorem subsetSum_posDef_of_admissibleTriangle_of_nonneg_cross {m : ℕ}
    (D : WeightedDesign m 3) (x y z : Fin m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (htri : AdmissibleTriangle D x y z)
    (hcross : 0 ≤ (D.atom x ⬝ᵥ D.atom y) * (D.atom x ⬝ᵥ D.atom z)
      * (D.atom y ⬝ᵥ D.atom z))
    (hsum : (leverageOf (D.atom z) - 1) * (D.atom x ⬝ᵥ D.atom y) ^ 2
        + (leverageOf (D.atom y) - 1) * (D.atom x ⬝ᵥ D.atom z) ^ 2
        + (leverageOf (D.atom x) - 1) * (D.atom y ⬝ᵥ D.atom z) ^ 2
      < (leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1)
        * (leverageOf (D.atom z) - 1)) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef :=
  subsetSum_posDef_of_admissibleTriangle_of_det D x y z hxy hxz hyz hheavy htri
    (tripleGapDet_pos_of_nonneg_cross _ _ _ hcross hsum)

/-! ## 5. The witness: an admissible triangle with a negative determinant

Three explicit rational vectors, pairwise admissible, with a strictly negative
third minor and a nonzero bracket.  The campaign measured a failure rate at
triangles across four boxes and carried no witness; this is that witness, and it
shows the residual determinant is genuinely open rather than a formality. -/

/-- First witness atom. -/
def negDetFirst : Fin 3 → ℝ := ![3, 1, 0]

/-- Second witness atom. -/
def negDetSecond : Fin 3 → ℝ := ![-2, 2, 0]

/-- Third witness atom. -/
def negDetThird : Fin 3 → ℝ := ![-1, -3, 1]

theorem leverageOf_negDetFirst : leverageOf negDetFirst = 10 := by
  simp [leverageOf, negDetFirst, Fin.sum_univ_three]; norm_num

theorem leverageOf_negDetSecond : leverageOf negDetSecond = 8 := by
  simp [leverageOf, negDetSecond, Fin.sum_univ_three]; norm_num

theorem leverageOf_negDetThird : leverageOf negDetThird = 11 := by
  simp [leverageOf, negDetThird, Fin.sum_univ_three]; norm_num

theorem negDet_pairing_first_second : negDetFirst ⬝ᵥ negDetSecond = -4 := by
  simp [negDetFirst, negDetSecond, dotProduct, Fin.sum_univ_three]; norm_num

theorem negDet_pairing_first_third : negDetFirst ⬝ᵥ negDetThird = -6 := by
  simp [negDetFirst, negDetThird, dotProduct, Fin.sum_univ_three]; norm_num

theorem negDet_pairing_second_third : negDetSecond ⬝ᵥ negDetThird = -4 := by
  simp [negDetSecond, negDetThird, dotProduct, Fin.sum_univ_three]; norm_num

theorem negDet_pairMinor_first_second :
    pairGapMinor negDetFirst negDetSecond = 47 := by
  rw [pairGapMinor, leverageOf_negDetFirst, leverageOf_negDetSecond,
    negDet_pairing_first_second]; norm_num

theorem negDet_pairMinor_first_third :
    pairGapMinor negDetFirst negDetThird = 54 := by
  rw [pairGapMinor, leverageOf_negDetFirst, leverageOf_negDetThird,
    negDet_pairing_first_third]; norm_num

theorem negDet_pairMinor_second_third :
    pairGapMinor negDetSecond negDetThird = 54 := by
  rw [pairGapMinor, leverageOf_negDetSecond, leverageOf_negDetThird,
    negDet_pairing_second_third]; norm_num

/-- All three pairs are admissible: the witness sits inside the triangle
region. -/
theorem negDet_admissible_triple :
    0 < pairGapMinor negDetFirst negDetSecond
      ∧ 0 < pairGapMinor negDetFirst negDetThird
      ∧ 0 < pairGapMinor negDetSecond negDetThird := by
  rw [negDet_pairMinor_first_second, negDet_pairMinor_first_third,
    negDet_pairMinor_second_third]
  norm_num

/-- Every atom of the witness is strictly heavy. -/
theorem negDet_heavy :
    1 < leverageOf negDetFirst ∧ 1 < leverageOf negDetSecond
      ∧ 1 < leverageOf negDetThird := by
  rw [leverageOf_negDetFirst, leverageOf_negDetSecond, leverageOf_negDetThird]
  norm_num

/-- The determinant is strictly negative. -/
theorem negDet_tripleGapDet :
    tripleGapDet negDetFirst negDetSecond negDetThird = -118 := by
  rw [tripleGapDet, leverageOf_negDetFirst, leverageOf_negDetSecond,
    leverageOf_negDetThird, negDet_pairing_first_second, negDet_pairing_first_third,
    negDet_pairing_second_third]; norm_num

/-- **THE TRIANGLE DOES NOT FORCE THE SIGN.**  There is a strictly heavy,
pairwise admissible triple whose third minor is strictly negative.  So
`Gtz.posDef_iff_thirdInvariant_of_admissibleTriangle` leaves genuine content and
not a formality. -/
theorem not_forall_tripleGapDet_pos_of_admissibleTriangle :
    ¬ (∀ a b c : Fin 3 → ℝ, 1 < leverageOf a → 1 < leverageOf b → 1 < leverageOf c →
        0 < pairGapMinor a b → 0 < pairGapMinor a c → 0 < pairGapMinor b c →
        0 < tripleGapDet a b c) := by
  intro hall
  obtain ⟨hone, htwo, hthree⟩ := negDet_heavy
  obtain ⟨hab, hac, hbc⟩ := negDet_admissible_triple
  have := hall negDetFirst negDetSecond negDetThird hone htwo hthree hab hac hbc
  rw [negDet_tripleGapDet] at this
  norm_num at this

/-- The witness is NOT degenerate: its bracket is nonzero, so the three atoms
span and the failure is not an artifact of coplanarity. -/
theorem negDet_bracket : tripleBracket negDetFirst negDetSecond negDetThird = 8 := by
  simp only [tripleBracket, Matrix.det_fin_three, negDetFirst, negDetSecond, negDetThird,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

theorem negDet_bracket_ne_zero :
    tripleBracket negDetFirst negDetSecond negDetThird ≠ 0 := by
  rw [negDet_bracket]; norm_num

/-! ### The same witness bounds the sharp constant from below -/

/-- The witness clears every pair minor with a factor two of slack, and still
fails.  So the constant two is unsound. -/
theorem negDet_doubleSlack :
    2 * (negDetFirst ⬝ᵥ negDetSecond) ^ 2
        < (leverageOf negDetFirst - 1) * (leverageOf negDetSecond - 1)
      ∧ 2 * (negDetFirst ⬝ᵥ negDetThird) ^ 2
        < (leverageOf negDetFirst - 1) * (leverageOf negDetThird - 1)
      ∧ 2 * (negDetSecond ⬝ᵥ negDetThird) ^ 2
        < (leverageOf negDetSecond - 1) * (leverageOf negDetThird - 1) := by
  rw [leverageOf_negDetFirst, leverageOf_negDetSecond, leverageOf_negDetThird,
    negDet_pairing_first_second, negDet_pairing_first_third,
    negDet_pairing_second_third]
  norm_num

/-- **TWO DOES NOT SUFFICE.**  With the quarter-slack cell above, the optimal
constant lies in `(2, 4]`, and the equilateral factorization shows four is
attained. -/
theorem not_forall_tripleGapDet_pos_of_doubleSlack :
    ¬ (∀ a b c : Fin 3 → ℝ, 1 < leverageOf a → 1 < leverageOf b → 1 < leverageOf c →
        2 * (a ⬝ᵥ b) ^ 2 < (leverageOf a - 1) * (leverageOf b - 1) →
        2 * (a ⬝ᵥ c) ^ 2 < (leverageOf a - 1) * (leverageOf c - 1) →
        2 * (b ⬝ᵥ c) ^ 2 < (leverageOf b - 1) * (leverageOf c - 1) →
        0 < tripleGapDet a b c) := by
  intro hall
  obtain ⟨hone, htwo, hthree⟩ := negDet_heavy
  obtain ⟨hab, hac, hbc⟩ := negDet_doubleSlack
  have := hall negDetFirst negDetSecond negDetThird hone htwo hthree hab hac hbc
  rw [negDet_tripleGapDet] at this
  norm_num at this

/-- The witness also has a strictly negative triple product, which is what the
sign-aware cell refuses.  The two cells and the witness are consistent. -/
theorem negDet_cross_neg :
    (negDetFirst ⬝ᵥ negDetSecond) * (negDetFirst ⬝ᵥ negDetThird)
      * (negDetSecond ⬝ᵥ negDetThird) < 0 := by
  rw [negDet_pairing_first_second, negDet_pairing_first_third,
    negDet_pairing_second_third]; norm_num

/-! ## 6. The bridge to the older pair vocabulary

`Gtz.pairGapExcessOf` and `Gtz.pairGapMinor` are the same scalar written in two
generations of vocabulary.  Stating the identity lets the landed pair-existence
theorems feed the triangle machinery directly. -/

theorem pairGapExcessOf_eq_pairGapMinor {m : ℕ} (D : WeightedDesign m 3)
    (x y : Fin m) :
    pairGapExcessOf D x y = pairGapMinor (D.atom x) (D.atom y) := by
  rw [pairGapExcessOf, pairGapMinor, gapExcessOf, gapExcessOf, gapPairingOf]

theorem admissiblePair_iff_pairGapExcessOf_pos {m : ℕ} (D : WeightedDesign m 3)
    (x y : Fin m) :
    AdmissiblePair (D.atom x) (D.atom y) ↔ 0 < pairGapExcessOf D x y := by
  rw [AdmissiblePair, pairGapExcessOf_eq_pairGapMinor]

theorem admissibleEdge_iff_pairGapExcessOf_pos {m : ℕ} (D : WeightedDesign m 3)
    (x y : Fin m) :
    AdmissibleEdge D x y ↔ 0 < pairGapExcessOf D x y :=
  admissiblePair_iff_pairGapExcessOf_pos D x y

/-- **AN ADMISSIBLE EDGE WITH TWO STRICTLY HEAVY ENDPOINTS ALWAYS EXISTS.**  The
landed pair-existence theorem returns a live pair, which is more than adjacency:
both endpoints are strictly heavy as well.  Carried into the graph vocabulary,
this says the admissible-pair graph is never empty and always has an edge inside
the heavy set.  So the open question at the one-line stratum is triangles, not
edges. -/
theorem exists_admissibleEdge_heavy {m : ℕ} (D : WeightedDesign m 3) :
    ∃ x y : Fin m, x ≠ y ∧ AdmissibleEdge D x y
      ∧ 0 < gapExcessOf D x ∧ 0 < gapExcessOf D y := by
  obtain ⟨x, y, hne, hfirst, hsecond, hpair⟩ := exists_pos_pairGapExcessOf D (le_refl 3)
  exact ⟨x, y, hne, (admissibleEdge_iff_pairGapExcessOf_pos D x y).mpr hpair,
    hfirst, hsecond⟩

/-- The bare edge-existence consequence. -/
theorem exists_admissibleEdge {m : ℕ} (D : WeightedDesign m 3) :
    ∃ x y : Fin m, x ≠ y ∧ AdmissibleEdge D x y := by
  obtain ⟨x, y, hne, hedge, -, -⟩ := exists_admissibleEdge_heavy D
  exact ⟨x, y, hne, hedge⟩

/-! ## 7. Why no cell reading only shares and weights can work

The row law caps every weighted pairing square by the row's share gap, and the
share gap never exceeds a quarter.  That gives a universal cap on every pairing.
The heavy mass ceiling gives a universal cap on every surplus.  The two are
exactly complementary: the pairing cap can never certify a quarter slack, and it
can never certify even a bare pair minor. -/

/-- **THE UNIVERSAL PAIRING CAP.**  At any design of any rank, four times the
weighted squared pairing of a pair never exceeds one.  A single term of the
landed row law, capped by the landed quarter bound. -/
theorem four_mul_weight_mul_sq_gapPairing_le_one {m k : ℕ} (D : WeightedDesign m k)
    (x y : Fin m) (hne : x ≠ y) :
    4 * (D.weight x * D.weight y * gapPairingOf D x y ^ 2) ≤ 1 := by
  have hmem : y ∈ Finset.univ.erase x := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ y⟩
  have hterm : D.weight x * D.weight y * gapPairingOf D x y ^ 2
      ≤ atomShare D x - atomShare D x ^ 2 := by
    rw [← sum_erase_weightPair_mul_sq_gapPairing D x]
    refine Finset.single_le_sum (f := fun otherLabel =>
      D.weight x * D.weight otherLabel * gapPairingOf D x otherLabel ^ 2) ?_ hmem
    exact fun otherLabel _ => mul_nonneg (mul_nonneg (D.weight_pos x).le
      (D.weight_pos otherLabel).le) (sq_nonneg _)
  have hquarter := atomShare_gap_le_quarter D x
  linarith

/-- **THE CAP AND THE CEILING ARE COMPLEMENTARY.**  The heavy masses of the two
atoms of a pair never reach one, while certifying even a bare pair minor from the
universal cap alone would need their product to exceed one.  So no bound that
reads only shares and weights can decide a pair, let alone a triangle. -/
theorem heavyMass_product_lt_one {m k : ℕ} (D : WeightedDesign m k) (x y : Fin m)
    (hx : 0 ≤ heavyMassOf D x) :
    heavyMassOf D x * heavyMassOf D y < 1 := by
  have hxlt := heavyMassOf_lt_one D x
  have hylt := heavyMassOf_lt_one D y
  nlinarith

/-- The pairing cap rewritten against the pair minor.  The cap certifies the pair
minor exactly when the heavy masses multiply above one, which the ceiling
forbids.  This is the precise sense in which the share-and-weight reading is
exhausted. -/
theorem pairMinor_certified_by_cap_iff {m : ℕ} (D : WeightedDesign m 3)
    (x y : Fin m) (hx : 0 < D.weight x) (hy : 0 < D.weight y) :
    (1 / (D.weight x * D.weight y)
        < (leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1))
      ↔ 1 < heavyMassOf D x * heavyMassOf D y := by
  have hprod : 0 < D.weight x * D.weight y := mul_pos hx hy
  rw [heavyMassOf, heavyMassOf, gapExcessOf, gapExcessOf]
  rw [div_lt_iff₀ hprod]
  constructor <;> intro h <;> nlinarith [h]

/-! ## 8. The cell union, and the covering shape it feeds -/

/-- The two new cells, as one disjunction at a triple. -/
def TripleDetCellFires {m : ℕ} (D : WeightedDesign m 3) (x y z : Fin m) : Prop :=
  (4 * (D.atom x ⬝ᵥ D.atom y) ^ 2
      < (leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1)
    ∧ 4 * (D.atom x ⬝ᵥ D.atom z) ^ 2
      < (leverageOf (D.atom x) - 1) * (leverageOf (D.atom z) - 1)
    ∧ 4 * (D.atom y ⬝ᵥ D.atom z) ^ 2
      < (leverageOf (D.atom y) - 1) * (leverageOf (D.atom z) - 1))
  ∨ (AdmissibleTriangle D x y z
    ∧ 0 ≤ (D.atom x ⬝ᵥ D.atom y) * (D.atom x ⬝ᵥ D.atom z) * (D.atom y ⬝ᵥ D.atom z)
    ∧ (leverageOf (D.atom z) - 1) * (D.atom x ⬝ᵥ D.atom y) ^ 2
        + (leverageOf (D.atom y) - 1) * (D.atom x ⬝ᵥ D.atom z) ^ 2
        + (leverageOf (D.atom x) - 1) * (D.atom y ⬝ᵥ D.atom z) ^ 2
      < (leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1)
        * (leverageOf (D.atom z) - 1))

/-- Either branch of the union supplies a strict dominator. -/
theorem subsetSum_posDef_of_tripleDetCellFires {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (hstrict : 1 < leverageOf (D.atom x) ∧ 1 < leverageOf (D.atom y)
      ∧ 1 < leverageOf (D.atom z))
    (hfires : TripleDetCellFires D x y z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef := by
  obtain ⟨hx, hy, hz⟩ := hstrict
  rcases hfires with ⟨hab, hac, hbc⟩ | ⟨htri, hcross, hsum⟩
  · exact subsetSum_posDef_of_quarterSlack D x y z hxy hxz hyz hx hy hz hab hac hbc
  · exact subsetSum_posDef_of_admissibleTriangle_of_nonneg_cross D x y z hxy hxz hyz
      hheavy htri hcross hsum

/-- **THE CELL UNION FEEDS THE TRIANGLE COVER.**  A firing triple discharges
`Gtz.AdmissibleTriangleCovers`, which is the covering shape the one-line
obligation consumes. -/
theorem admissibleTriangleCovers_of_tripleDetCellFires {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (hstrict : 1 < leverageOf (D.atom x) ∧ 1 < leverageOf (D.atom y)
      ∧ 1 < leverageOf (D.atom z))
    (hfires : TripleDetCellFires D x y z) :
    AdmissibleTriangleCovers D :=
  admissibleTriangleCovers_of_subsetSum_posDef D x y z hxy hxz hyz
    (subsetSum_posDef_of_tripleDetCellFires D x y z hxy hxz hyz hheavy hstrict hfires)

/-- The union is not vacuous: an orthogonal heavy triple fires the quarter-slack
branch with room to spare. -/
theorem tripleDetCellFires_of_orthogonal {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m)
    (hx : 1 < leverageOf (D.atom x)) (hy : 1 < leverageOf (D.atom y))
    (hz : 1 < leverageOf (D.atom z))
    (hxy : D.atom x ⬝ᵥ D.atom y = 0) (hxz : D.atom x ⬝ᵥ D.atom z = 0)
    (hyz : D.atom y ⬝ᵥ D.atom z = 0) :
    TripleDetCellFires D x y z := by
  refine Or.inl ⟨?_, ?_, ?_⟩
  · rw [hxy]; nlinarith [hx, hy]
  · rw [hxz]; nlinarith [hx, hz]
  · rw [hyz]; nlinarith [hy, hz]

end Gtz
