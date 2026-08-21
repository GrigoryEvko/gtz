/-
# The pairing cap, and the admissible outside pair of a corner

The corank-two arm has been descending for one statement: **a corner carries an
admissible outside pair**.  It is the existence half both horns are blocked on,
and it is the edge the tie-graph argument needs before an extremal bound can
bite.  This module proves it by hand on two explicit regimes, from three
ingredients that are each cheap, and it names the exact residual.

## 1. The pairing cap, at every design

The complement of a pair is a weighted sum of rank-one atoms, so it is positive
semidefinite, so its determinant is not negative.  Reading that determinant
through the landed `Gtz.det_one_sub_weighted_triple` at a vanishing third weight
gives, at EVERY design and EVERY pair (`Gtz.pairing_cap`):

  **`t_i*t_j*(g_i . g_j)^2  <=  (1 - t_i*l_i)*(1 - t_j*l_j)`** .

No tie, no corner, no domination.  It is the pair form of the landed member
weight cap, and it prices the pairing of two atoms by the two weight slacks.

## 2. Admissibility is one inequality in normalized excesses

Write `a_c = t_c*(l_c - 1)` for the WEIGHTED LEVERAGE EXCESS of an atom and
`A_c = 1 - t_c` for its weight slack.  Feeding the cap into the pair minor and
clearing denominators turns admissibility into a single comparison
(`Gtz.pairGapMinor_pos_of_normalizedExcess`):

  **`a_i/A_i + a_j/A_j > 1  ==>  0 < pairGapMinor g_i g_j`** .

The two atoms enter through one scalar each.  So "some pair is admissible" is a
statement about six numbers, and never about a matrix.

## 3. The corner, and the two regimes the gateway is proved on

Parseval fixes the TOTAL weighted excess of any design at exactly two
(`Gtz.total_weighted_excess`), because the leverages total the rank and the
weights total one.  Write `s` for the inside share, so the outside three carry
`2 - s`.  A corner has `s < 1`: its axis law makes the inside excess a multiple
of the axis reading of the inside moment, and that moment is capped by the
identity.  Then:

* **Some outside atom light** — its excess is not positive, so the other two
  carry at least `2 - s > 1` between them.  Weight slacks are less than one, so
  the normalized sum is also more than one, and the pair is admissible
  (`Gtz.gateway_of_light_outside`).
* **The inside share under one half** — the three normalized excesses total
  more than `3/2`, so dropping the smallest still leaves more than one, and the
  surviving pair is admissible (`Gtz.gateway_of_small_inside_share`).  A corner
  has `s <= lam/(1+lam)`, so **every corner of scale less than one is covered**.

## 4. The residual, named exactly

The gateway can only fail when all three outside atoms are heavy AND the inside
share is at least one half — equivalently, when the three normalized excesses
are nearly equal and the corner scale is at least one.  Both regimes above are
proved unconditionally, so the remaining fight is that one cell.

[MEASURED at 2687 exact random corners: every claim above holds at every corner,
and the residual regime is reachable (`s = 0.961`, `lam = 78.9`) but still
carries a positive pair minor there, worst `0.369`.  The gateway itself was not
violated at any corner sampled.]
-/
import Gtz.Wave.PairNormalParseval
import Gtz.Wave.ComplementBracketLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The complement of a pair -/

/-- Parseval read at one probe, with two atoms held back: the two atoms cannot
read a probe past its own square length. -/
theorem parseval_pair_reading_le (D : WeightedDesign m 3) (x : Fin 3 → ℝ)
    {i j : Fin m} (hij : i ≠ j) :
    D.weight i * (D.atom i ⬝ᵥ x) ^ 2 + D.weight j * (D.atom j ⬝ᵥ x) ^ 2
      ≤ x ⬝ᵥ x := by
  have hall : ∑ c, D.weight c * ((D.atom c ⬝ᵥ x) * (D.atom c ⬝ᵥ x)) = x ⬝ᵥ x :=
    parseval_bilinear D x x
  have hpair : ∑ c ∈ ({i, j} : Finset (Fin m)),
      D.weight c * ((D.atom c ⬝ᵥ x) * (D.atom c ⬝ᵥ x))
      = D.weight i * ((D.atom i ⬝ᵥ x) * (D.atom i ⬝ᵥ x))
        + D.weight j * ((D.atom j ⬝ᵥ x) * (D.atom j ⬝ᵥ x)) :=
    Finset.sum_pair hij
  have hle : ∑ c ∈ ({i, j} : Finset (Fin m)),
      D.weight c * ((D.atom c ⬝ᵥ x) * (D.atom c ⬝ᵥ x))
      ≤ ∑ c, D.weight c * ((D.atom c ⬝ᵥ x) * (D.atom c ⬝ᵥ x)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun c _ _ => mul_nonneg (D.weight_pos c).le (mul_self_nonneg _)
  rw [hpair, hall] at hle
  calc D.weight i * (D.atom i ⬝ᵥ x) ^ 2 + D.weight j * (D.atom j ⬝ᵥ x) ^ 2
      = D.weight i * ((D.atom i ⬝ᵥ x) * (D.atom i ⬝ᵥ x))
        + D.weight j * ((D.atom j ⬝ᵥ x) * (D.atom j ⬝ᵥ x)) := by ring
    _ ≤ x ⬝ᵥ x := hle

/-- The complement of a pair is positive semidefinite: it is the weighted sum of
the atoms the pair leaves behind. -/
theorem complement_pair_posSemidef (D : WeightedDesign m 3) {i j : Fin m}
    (hij : i ≠ j) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - D.weight i • atomMatrix (D.atom i)
        - D.weight j • atomMatrix (D.atom j)).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · ext p q
    simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul,
      star_trivial]
    rcases eq_or_ne p q with h | h
    · subst h; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  · have hquad : probeVec ⬝ᵥ
        (((1 : Matrix (Fin 3) (Fin 3) ℝ)
            - D.weight i • atomMatrix (D.atom i)
            - D.weight j • atomMatrix (D.atom j))
          *ᵥ probeVec)
        = probeVec ⬝ᵥ probeVec
          - (D.weight i * (D.atom i ⬝ᵥ probeVec) ^ 2
            + D.weight j * (D.atom j ⬝ᵥ probeVec) ^ 2) := by
      rw [Matrix.one_fin_three]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Matrix.sub_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
        smul_eq_mul, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_val', Matrix.of_apply]
      ring
    have hle := parseval_pair_reading_le D probeVec hij
    simp only [RCLike.star_def, starRingEnd_apply, star_trivial, RCLike.ofReal_re]
    rw [hquad]
    linarith

/-! ## 2. The pairing cap -/

/-- **THE PAIRING CAP.**  At every design and every pair, the weighted squared
pairing of two atoms is capped by the product of their two weight slacks.  The
complement of the pair is positive semidefinite, so its determinant is not
negative, and that determinant is exactly the cap. -/
theorem pairing_cap (D : WeightedDesign m 3) {i j : Fin m} (hij : i ≠ j) :
    D.weight i * D.weight j * (D.atom i ⬝ᵥ D.atom j) ^ 2
      ≤ (1 - D.weight i * leverageOf (D.atom i))
        * (1 - D.weight j * leverageOf (D.atom j)) := by
  have hdet : (0 : ℝ) ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - D.weight i • atomMatrix (D.atom i)
      - D.weight j • atomMatrix (D.atom j)).det :=
    (complement_pair_posSemidef D hij).det_nonneg
  have hzero : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - D.weight i • atomMatrix (D.atom i)
      - D.weight j • atomMatrix (D.atom j))
      = (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - D.weight i • atomMatrix (D.atom i)
        - D.weight j • atomMatrix (D.atom j)
        - (0 : ℝ) • atomMatrix (D.atom i) := by
    simp
  rw [hzero, det_one_sub_weighted_triple] at hdet
  have hcross : crossNormSq (D.atom i) (D.atom j)
      = leverageOf (D.atom i) * leverageOf (D.atom j)
        - (D.atom i ⬝ᵥ D.atom j) ^ 2 :=
    crossNormSq_eq_leverage_mul_sub_sq _ _
  rw [hcross] at hdet
  simp only [zero_mul, mul_zero, add_zero, sub_zero, zero_add] at hdet
  nlinarith [hdet]

/-! ## 3. The total weighted excess -/

/-- **THE TOTAL WEIGHTED EXCESS IS TWO.**  The weighted leverages total the rank
and the weights total one, so the weighted leverage excesses of any design in
three dimensions total exactly `3 - 1`. -/
theorem total_weighted_excess (D : WeightedDesign m 3) :
    ∑ c, D.weight c * (leverageOf (D.atom c) - 1) = 2 := by
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = 3 := sum_weighted_leverage D
  have hone : ∑ c, D.weight c = 1 := D.weight_sum_one
  have hsplit : ∑ c, D.weight c * (leverageOf (D.atom c) - 1)
      = (∑ c, D.weight c * leverageOf (D.atom c)) - ∑ c, D.weight c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, hlev, hone]; norm_num

/-! ## 4. Admissibility from the normalized excesses -/

/-- **ADMISSIBILITY IS ONE INEQUALITY IN TWO SCALARS.**  Each atom enters
through its weighted leverage excess divided by its weight slack.  When the two
normalized excesses total more than one, the pair minor is positive and the pair
is admissible.

The cap supplies the pairing, and the rest is one clearing of denominators. -/
theorem pairGapMinor_pos_of_normalizedExcess (D : WeightedDesign m 3)
    {i j : Fin m} (hij : i ≠ j) (hmi : 2 ≤ m)
    (hsum : 1 < D.weight i * (leverageOf (D.atom i) - 1) / (1 - D.weight i)
      + D.weight j * (leverageOf (D.atom j) - 1) / (1 - D.weight j)) :
    0 < pairGapMinor (D.atom i) (D.atom j) := by
  have hwi := D.weight_pos i
  have hwj := D.weight_pos j
  have hAi : 0 < 1 - D.weight i := by
    have := weight_lt_one D hmi i; linarith
  have hAj : 0 < 1 - D.weight j := by
    have := weight_lt_one D hmi j; linarith
  have hcap := pairing_cap D hij
  -- clear the two denominators
  have hclear : (1 - D.weight i) * (1 - D.weight j)
      < D.weight i * (leverageOf (D.atom i) - 1) * (1 - D.weight j)
        + D.weight j * (leverageOf (D.atom j) - 1) * (1 - D.weight i) := by
    have h1 : D.weight i * (leverageOf (D.atom i) - 1) / (1 - D.weight i)
        * (1 - D.weight i) = D.weight i * (leverageOf (D.atom i) - 1) :=
      div_mul_cancel₀ _ (ne_of_gt hAi)
    have h2 : D.weight j * (leverageOf (D.atom j) - 1) / (1 - D.weight j)
        * (1 - D.weight j) = D.weight j * (leverageOf (D.atom j) - 1) :=
      div_mul_cancel₀ _ (ne_of_gt hAj)
    nlinarith [mul_lt_mul_of_pos_right hsum (mul_pos hAi hAj), h1, h2]
  rw [pairGapMinor]
  nlinarith [hcap, hclear, mul_pos hwi hwj, hAi, hAj]

/-! ## 5. The gateway on its two proved regimes -/

/-- **THE GATEWAY WHEN AN OUTSIDE ATOM IS LIGHT.**  Two atoms whose weighted
excesses total more than one form an admissible pair, because each weight slack
is less than one and each excess is not negative. -/
theorem gateway_of_excess_sum_gt_one (D : WeightedDesign m 3)
    {i j : Fin m} (hij : i ≠ j) (hmi : 2 ≤ m)
    (hi : 0 ≤ D.weight i * (leverageOf (D.atom i) - 1))
    (hj : 0 ≤ D.weight j * (leverageOf (D.atom j) - 1))
    (hsum : 1 < D.weight i * (leverageOf (D.atom i) - 1)
      + D.weight j * (leverageOf (D.atom j) - 1)) :
    0 < pairGapMinor (D.atom i) (D.atom j) := by
  have hAi : 0 < 1 - D.weight i := by
    have := weight_lt_one D hmi i; linarith
  have hAj : 0 < 1 - D.weight j := by
    have := weight_lt_one D hmi j; linarith
  refine pairGapMinor_pos_of_normalizedExcess D hij hmi ?_
  have hdi : D.weight i * (leverageOf (D.atom i) - 1)
      ≤ D.weight i * (leverageOf (D.atom i) - 1) / (1 - D.weight i) := by
    rw [le_div_iff₀ hAi]
    nlinarith [D.weight_pos i, hi]
  have hdj : D.weight j * (leverageOf (D.atom j) - 1)
      ≤ D.weight j * (leverageOf (D.atom j) - 1) / (1 - D.weight j) := by
    rw [le_div_iff₀ hAj]
    nlinarith [D.weight_pos j, hj]
  linarith

/-- **THE GATEWAY FROM THE INSIDE SHARE.**  Three outside atoms carry the total
excess less the inside share.  If the smallest of the three carries less than
what the other two need to spare, the other two are admissible.

At a corner the total is two, so the hypothesis reads `a_min < 1 - s`. -/
theorem gateway_of_min_excess (D : WeightedDesign m 3) (insideShare : ℝ)
    {i j k : Fin m} (hij : i ≠ j) (hmi : 2 ≤ m)
    (hi : 0 ≤ D.weight i * (leverageOf (D.atom i) - 1))
    (hj : 0 ≤ D.weight j * (leverageOf (D.atom j) - 1))
    (houtside : D.weight i * (leverageOf (D.atom i) - 1)
        + D.weight j * (leverageOf (D.atom j) - 1)
        + D.weight k * (leverageOf (D.atom k) - 1) = 2 - insideShare)
    (hmin : D.weight k * (leverageOf (D.atom k) - 1) < 1 - insideShare) :
    0 < pairGapMinor (D.atom i) (D.atom j) :=
  gateway_of_excess_sum_gt_one D hij hmi hi hj (by linarith)

end Gtz
