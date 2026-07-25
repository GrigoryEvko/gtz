import Mathlib
import Gtz.Reduction.BranchTwoRational

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Adversarial audit A — the rank-three completeness half the builder left open

The builder's report lists, under `whatDidNotWork`, the non-strict completeness
half — *"`Dominates D C` implies every `(k-1)`-subgate has `det (S_G - 1) <= 0`"* —
as blocked on a `Finset` / `Fin k` reindexing.  At rank three the reindexing is
not needed: take the triple as three explicit vectors, use the repo's own
`Gtz.transpose_mul_self_eq_sum_rows` and `Gtz.posSemidef_transpose_mul_sub_one_comm`
to move from `S_C - I` to `Gram(C) - I`, and read off a `2 x 2` principal
submatrix.

The consequence is that `Gtz.exists_dominatingTriple_withoutStrictGate` is SHARP:
a dominating triple's pair gates can degenerate but can never go strictly the
wrong way, so the rank-three producer's blind spot is exactly the zero set.
-/

namespace Gtz

open Matrix

/-- The `3 x 3` matrix whose rows are the triple. -/
def tripleRows (first second third : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![first, second, third]

/-- `S_C` is the row matrix's Gram from the left. -/
theorem tripleRows_transpose_mul (first second third : Fin 3 → ℝ) :
    (tripleRows first second third)ᵀ * tripleRows first second third
      = atomMatrix first + atomMatrix second + atomMatrix third := by
  rw [transpose_mul_self_eq_sum_rows, Fin.sum_univ_three]
  rfl

/-- **`Gram(C) - I` is positive semidefinite whenever `S_C - I` is.**  The square
expansion transfer, specialised to a triple at rank three. -/
theorem gramShift_posSemidef_of_dominatingTriple (first second third : Fin 3 → ℝ)
    (hdom : (atomMatrix first + atomMatrix second + atomMatrix third
              - 1).PosSemidef) :
    (tripleRows first second third * (tripleRows first second third)ᵀ
      - 1).PosSemidef := by
  refine (posSemidef_transpose_mul_sub_one_comm
    (tripleRows first second third)).mp ?_
  rwa [tripleRows_transpose_mul]

/-- **The rank-three completeness half.**  A dominating triple can never have a
pair gate whose shifted-leverage determinant is NEGATIVE: domination forces
`(l_a - 1)(l_b - 1) >= <g_a, g_b>^2` on every one of its three pairs.

Equivalently `det (S_G - 1) <= 0` for every two-element gate `G` inside a
dominating triple, so `dominates_of_pairGate`'s hypothesis `hgateDet` can
only fail by EQUALITY.  Together with
`exists_dominatingTriple_withoutStrictGate` this pins the rank-three
producer's blind spot exactly: it is the zero set of the three pair slacks and
nothing else. -/
theorem pairSlack_nonneg_of_dominatingTriple (first second third : Fin 3 → ℝ)
    (hdom : (atomMatrix first + atomMatrix second + atomMatrix third
              - 1).PosSemidef) :
    0 ≤ ((first ⬝ᵥ first) - 1) * ((second ⬝ᵥ second) - 1)
          - (first ⬝ᵥ second) ^ 2 := by
  have hgram := gramShift_posSemidef_of_dominatingTriple first second third hdom
  have hblock := hgram.submatrix (![0, 1] : Fin 2 → Fin 3)
  have hdet := hblock.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.transpose_apply, tripleRows, Matrix.of_apply, Matrix.one_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_three] at hdet
  norm_num at hdet
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [hdet]

/-- The same fact in the file's own determinant language: every two-element gate
inside a dominating triple has NONPOSITIVE gate determinant, so branch (b)'s
side condition `det (S_G - 1) < 0` can only fail at `0`. -/
theorem pairGramShift_det_nonpos_of_dominatingTriple
    (first second third : Fin 3 → ℝ)
    (hdom : (atomMatrix first + atomMatrix second + atomMatrix third
              - 1).PosSemidef) :
    (pairGramShift first second).det ≤ 0 := by
  rw [pairGramShift_det]
  have := pairSlack_nonneg_of_dominatingTriple first second third hdom
  linarith



/-! ## Branch (b) at rank three is complete off the tie locus

`exists_dominatingTriple_withoutStrictGate` shows the rank-three producer has
a blind spot.  This section measures the blind spot exactly: a dominating triple
with a degenerate pair gate has `det (S_C - 1) = 0`, i.e. it dominates only
WEAKLY.  Contrapositive: every STRICT dominating triple has all three pair gates
strict, so `dominates_of_pairGate` certifies it.

Consequence for the builder's stated next brick -- *"can a design be degenerate at
EVERY one of its dominating triples at once?"* -- the search space collapses to
the TIE variety: such a design has no strict dominator at all. -/

/-- **The scalar core.**  For a symmetric `3 x 3` form with nonnegative diagonal
corner `a`, nonnegative `b` and nonnegative determinant, a vanishing leading
`2 x 2` minor forces the determinant to vanish.  The engine is the identity
`a * det + (a*f - d*e)^2 = (a*b - d^2) * (a*c - e^2)`. -/
theorem symmetricDet_eq_zero_of_degenerateMinor (cornerA cornerB cornerC
    crossD crossE crossF : ℝ)
    (hcornerA : 0 ≤ cornerA) (hcornerB : 0 ≤ cornerB)
    (hdetNonneg : 0 ≤ cornerA * cornerB * cornerC + 2 * crossD * crossE * crossF
                        - cornerA * crossF ^ 2 - cornerB * crossE ^ 2
                        - cornerC * crossD ^ 2)
    (hminorZero : cornerA * cornerB - crossD ^ 2 = 0) :
    cornerA * cornerB * cornerC + 2 * crossD * crossE * crossF
      - cornerA * crossF ^ 2 - cornerB * crossE ^ 2 - cornerC * crossD ^ 2 = 0 := by
  rcases eq_or_lt_of_le hcornerA with hzero | hpos
  · have hcrossZero : crossD = 0 := by nlinarith [sq_nonneg crossD]
    have hcollapse : cornerA * cornerB * cornerC + 2 * crossD * crossE * crossF
        - cornerA * crossF ^ 2 - cornerB * crossE ^ 2 - cornerC * crossD ^ 2
        = -(cornerB * crossE ^ 2) := by
      rw [hcrossZero, ← hzero]; ring
    rw [hcollapse] at hdetNonneg ⊢
    nlinarith [mul_nonneg hcornerB (sq_nonneg crossE)]
  · have hkey : cornerA * (cornerA * cornerB * cornerC
        + 2 * crossD * crossE * crossF - cornerA * crossF ^ 2
        - cornerB * crossE ^ 2 - cornerC * crossD ^ 2)
        = -((cornerA * crossF - crossD * crossE) ^ 2) := by
      linear_combination (cornerA * cornerC - crossE ^ 2) * hminorZero
    nlinarith [sq_nonneg (cornerA * crossF - crossD * crossE), hpos, hdetNonneg,
      hkey]

/-- The excess determinant read off the triple's own inner products.  For a square
row matrix the characteristic polynomials of `MᵀM` and `MMᵀ` agree, so
`det (S_C - 1)` is the shifted GRAM determinant; at rank three that is a
polynomial identity in nine real variables, closed by `ring`. -/
theorem excessDet_eq_gramDet (first second third : Fin 3 → ℝ) :
    (atomMatrix first + atomMatrix second + atomMatrix third - 1).det
      = ((first ⬝ᵥ first) - 1) * ((second ⬝ᵥ second) - 1) * ((third ⬝ᵥ third) - 1)
        + 2 * (first ⬝ᵥ second) * (first ⬝ᵥ third) * (second ⬝ᵥ third)
        - ((first ⬝ᵥ first) - 1) * (second ⬝ᵥ third) ^ 2
        - ((second ⬝ᵥ second) - 1) * (first ⬝ᵥ third) ^ 2
        - ((third ⬝ᵥ third) - 1) * (first ⬝ᵥ second) ^ 2 := by
  have hdiag : ∀ i : Fin 3, (1 : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 := by
    intro i; simp
  have hoff : ∀ i j : Fin 3, i ≠ j → (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := by
    intro i j hne; simpa using Matrix.one_apply_ne hne
  simp only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.add_apply, atomMatrix,
    Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_three, hdiag,
    hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 0 (by decide),
    hoff 1 2 (by decide), hoff 2 0 (by decide), hoff 2 1 (by decide)]
  ring

/-- The shifted leverages of a dominating triple are nonnegative (they are the
`1 x 1` principal minors of `Gram(C) - I`). -/
theorem shiftedLeverage_nonneg_of_dominatingTriple (first second third : Fin 3 → ℝ)
    (hdom : (atomMatrix first + atomMatrix second + atomMatrix third
              - 1).PosSemidef) :
    0 ≤ (first ⬝ᵥ first) - 1 := by
  have hgram := gramShift_posSemidef_of_dominatingTriple first second third hdom
  have hdet := (hgram.submatrix (![0] : Fin 1 → Fin 3)).det_nonneg
  rw [Matrix.det_fin_one] at hdet
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.transpose_apply, tripleRows, Matrix.of_apply, Matrix.one_apply,
    Matrix.cons_val_zero, Fin.sum_univ_three] at hdet
  norm_num at hdet
  simp only [dotProduct, Fin.sum_univ_three]
  linarith

/-- **A degenerate pair gate forces a singular excess.**  A dominating triple one
of whose pair slacks is exactly `0` has `det (S_C - 1) = 0`, so it dominates only
weakly. -/
theorem excessDet_eq_zero_of_degenerateGate (first second third : Fin 3 → ℝ)
    (hdom : (atomMatrix first + atomMatrix second + atomMatrix third
              - 1).PosSemidef)
    (hgateZero : ((first ⬝ᵥ first) - 1) * ((second ⬝ᵥ second) - 1)
                   - (first ⬝ᵥ second) ^ 2 = 0) :
    (atomMatrix first + atomMatrix second + atomMatrix third - 1).det = 0 := by
  have hswap : atomMatrix second + atomMatrix first + atomMatrix third - 1
      = atomMatrix first + atomMatrix second + atomMatrix third - 1 := by abel
  have hsecondNonneg : 0 ≤ (second ⬝ᵥ second) - 1 :=
    shiftedLeverage_nonneg_of_dominatingTriple second first third (by rwa [hswap])
  rw [excessDet_eq_gramDet]
  exact symmetricDet_eq_zero_of_degenerateMinor _ _ _ _ _ _
    (shiftedLeverage_nonneg_of_dominatingTriple first second third hdom)
    hsecondNonneg
    (by rw [← excessDet_eq_gramDet]; exact hdom.det_nonneg)
    hgateZero

/-- **Branch (b) at rank three certifies every STRICT dominating triple.**  A
strictly dominating triple has positive excess determinant, so no pair gate can
degenerate; with `AuditA.pairSlack_nonneg_of_dominatingTriple` every pair slack is
then strictly positive, which is exactly `dominates_of_pairGate`'s `hgateDet`.

So the blind spot exhibited by `exists_dominatingTriple_withoutStrictGate` is
confined to NON-STRICT dominators, and a design all of whose dominators are
gate-degenerate has no strict dominator at all. -/
theorem pairSlack_pos_of_strictDominatingTriple (first second third : Fin 3 → ℝ)
    (hdom : (atomMatrix first + atomMatrix second + atomMatrix third
              - 1).PosDef) :
    0 < ((first ⬝ᵥ first) - 1) * ((second ⬝ᵥ second) - 1)
          - (first ⬝ᵥ second) ^ 2 := by
  rcases eq_or_lt_of_le (pairSlack_nonneg_of_dominatingTriple first second third
    hdom.posSemidef) with hzero | hpos
  · exact absurd (excessDet_eq_zero_of_degenerateGate first second third
      hdom.posSemidef hzero.symm) (ne_of_gt hdom.det_pos)
  · exact hpos

/-- The same in the file's gate-determinant language: a strictly dominating
triple's every two-element gate has STRICTLY negative determinant, so branch (b)'s
only side condition is automatic there. -/
theorem pairGramShift_det_neg_of_strictDominatingTriple
    (first second third : Fin 3 → ℝ)
    (hdom : (atomMatrix first + atomMatrix second + atomMatrix third
              - 1).PosDef) :
    (pairGramShift first second).det < 0 := by
  rw [pairGramShift_det]
  have := pairSlack_pos_of_strictDominatingTriple first second third hdom
  linarith


end Gtz
