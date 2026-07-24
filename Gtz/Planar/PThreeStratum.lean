/-
# The P3 stratum theorem: two tight pairs force the third

The smallest candidate refuter of GAP-S — a three-atom equality design whose
tight graph is a path — does not exist: the path always closes into the
triangle family. The mechanized content is one determinant factorization.

Coordinates: directions at angles `2a, 0, −2b`, middle conic value `ν₂ = n`,
tightness of the two path edges pinning `ν₁ = cos²a/n` and `ν₃ = cos²b/n`,
hence leverages `ℓ₁(n−cos²a) = n`, `ℓ₂(1−n) = 1`, `ℓ₃(n−cos²b) = n`. The
weight system (weight, closure ×2, trace) is four equations in three unknowns;
its 4×4 compatibility determinant, cleared of denominators, factors EXACTLY:

  `det · (n−cos²a)(n−cos²b)(n−1) = (n−1) · 4n·sin(a+b) · G`,
  `G = n·cos(a+b) + cos a·cos b`,

while the third pair's tightness gap is the difference of squares

  `n²cos²(a+b) − cos²a·cos²b = (n·cos(a+b) − cos a cos b)·G`.

Feasibility forces the determinant to vanish; away from clones
(`sin(a+b) ≠ 0`) and degenerate levels this means `G = 0`, and `G = 0`
annihilates the third gap: **the third pair is tight**. The certificates were
extracted by polynomial division against the two Pythagorean relations and are
consumed here verbatim by `linear_combination`.
-/
import Mathlib

namespace Gtz

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
/-- The 4×4 cofactor expansion along the first row, proven once generically. -/
theorem det_fin_four_expand (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.det
      = M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
          - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
          + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
        - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
          - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
          + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
        + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
          - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
          + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
        - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)
          - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
          + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  norm_num [Matrix.det_fin_three, Fin.succAbove, Fin.lt_def,
    Matrix.submatrix_apply,
    show (Fin.succ 0 : Fin 4) = 1 from rfl,
    show (Fin.succ 1 : Fin 4) = 2 from rfl,
    show (Fin.succ 2 : Fin 4) = 3 from rfl,
    show (Fin.castSucc 0 : Fin 4) = 0 from rfl,
    show (Fin.castSucc 1 : Fin 4) = 1 from rfl,
    show (Fin.castSucc 2 : Fin 4) = 2 from rfl]
  ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
/-- **The compatibility determinant factors.** The four design equations of the
P3 configuration are compatible only where `4n·sin(a+b)·G` vanishes. -/
theorem p3_compatibility_factors
    (ca sa cb sb n l1 l2 l3 : ℝ)
    (hpythA : ca ^ 2 + sa ^ 2 = 1) (hpythB : cb ^ 2 + sb ^ 2 = 1)
    (hl1 : l1 * (n - ca ^ 2) = n) (hl2 : l2 * (1 - n) = 1)
    (hl3 : l3 * (n - cb ^ 2) = n) :
    (Matrix.det !![(1 : ℝ), 1, 1, 1;
        l1 * (ca ^ 2 - sa ^ 2), l2, l3 * (cb ^ 2 - sb ^ 2), 0;
        l1 * (2 * ca * sa), 0, -(l3 * (2 * cb * sb)), 0;
        l1, l2, l3, 2])
      * ((n - ca ^ 2) * (n - cb ^ 2) * (n - 1))
    = (n - 1) * (4 * n * (sa * cb + ca * sb)
        * (n * (ca * cb - sa * sb) + ca * cb)) := by
  rw [det_fin_four_expand]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Matrix.of_apply]
  linear_combination
    (-2 * (-cb ^ 2 + n) * (n - 1)
      * (ca ^ 2 * cb * l2 * l3 * sb - 2 * ca ^ 2 * cb * l3 * sb
        + ca * cb ^ 2 * l2 * l3 * sa - 2 * ca * cb ^ 2 * l3 * sa
        - ca * l2 * l3 * sa * sb ^ 2 - ca * l2 * l3 * sa + 2 * ca * l2 * sa
        + 2 * ca * l3 * sa * sb ^ 2 - cb * l2 * l3 * sa ^ 2 * sb
        - cb * l2 * l3 * sb + 2 * cb * l3 * sa ^ 2 * sb)) * hl1
    + (2 * (-cb ^ 2 + n)
      * (ca ^ 2 * cb * l3 * n * sb - 2 * ca ^ 2 * cb * l3 * sb
        + ca * cb ^ 2 * l3 * n * sa - ca * l3 * n * sa * sb ^ 2
        - ca * l3 * n * sa + 2 * ca * n * sa - cb * l3 * n * sa ^ 2 * sb
        + cb * l3 * n * sb)) * hl2
    + (2 * (2 * ca ^ 2 * cb * n ^ 2 * sb - ca ^ 2 * cb * n * sb
        - 2 * ca ^ 2 * cb * sb + 2 * ca * cb ^ 2 * n ^ 2 * sa
        - ca * cb ^ 2 * n * sa - 2 * ca * n ^ 2 * sa * sb ^ 2
        + ca * n * sa * sb ^ 2 - ca * n * sa - 2 * cb * n ^ 2 * sa ^ 2 * sb
        + cb * n * sa ^ 2 * sb + cb * n * sb)) * hl3
    + (-2 * cb * n ^ 2 * sb) * hpythA
    + (-2 * ca * n ^ 2 * sa) * hpythB

/-- **The third pair's tightness gap is a difference of squares** carrying the
same factor `G`. -/
theorem p3_thirdGap_factors (ca sa cb sb n : ℝ) :
    n ^ 2 * (ca * cb - sa * sb) ^ 2 - ca ^ 2 * cb ^ 2
      = (n * (ca * cb - sa * sb) - ca * cb)
        * (n * (ca * cb - sa * sb) + ca * cb) := by
  ring

/-- **The P3 stratum IS the triangle family**: a feasible two-edge path of
tight pairs, away from clones and degenerate levels, forces the third pair
tight. There is no path-shaped equality design — the smallest candidate
refuter of GAP-S does not exist. -/
theorem p3_stratum_is_family
    (ca sa cb sb n l1 l2 l3 : ℝ)
    (hpythA : ca ^ 2 + sa ^ 2 = 1) (hpythB : cb ^ 2 + sb ^ 2 = 1)
    (hl1 : l1 * (n - ca ^ 2) = n) (hl2 : l2 * (1 - n) = 1)
    (hl3 : l3 * (n - cb ^ 2) = n)
    (hcompat : Matrix.det !![(1 : ℝ), 1, 1, 1;
        l1 * (ca ^ 2 - sa ^ 2), l2, l3 * (cb ^ 2 - sb ^ 2), 0;
        l1 * (2 * ca * sa), 0, -(l3 * (2 * cb * sb)), 0;
        l1, l2, l3, 2] = 0)
    (hnoClone : sa * cb + ca * sb ≠ 0)
    (hlevel : n ≠ 0) (hlevelOne : n ≠ 1) :
    n ^ 2 * (ca * cb - sa * sb) ^ 2 = ca ^ 2 * cb ^ 2 := by
  have hfactor := p3_compatibility_factors ca sa cb sb n l1 l2 l3
    hpythA hpythB hl1 hl2 hl3
  rw [hcompat, zero_mul] at hfactor
  have hgap : n - 1 ≠ 0 := sub_ne_zero.mpr hlevelOne
  have hfour : (4 : ℝ) * n ≠ 0 := by
    exact mul_ne_zero (by norm_num) hlevel
  -- peel the nonzero factors off the vanishing product
  have hproduct : (n - 1) * (4 * n * (sa * cb + ca * sb))
      * (n * (ca * cb - sa * sb) + ca * cb) = 0 := by
    linear_combination -hfactor
  have hfocal : n * (ca * cb - sa * sb) + ca * cb = 0 := by
    rcases mul_eq_zero.mp hproduct with hleft | hfocal
    · rcases mul_eq_zero.mp hleft with hone | hclone
      · exact absurd hone hgap
      · rcases mul_eq_zero.mp hclone with hfn | hsin
        · exact absurd hfn hfour
        · exact absurd hsin hnoClone
    · exact hfocal
  have hthird := p3_thirdGap_factors ca sa cb sb n
  rw [hfocal, mul_zero] at hthird
  linarith

end Gtz
