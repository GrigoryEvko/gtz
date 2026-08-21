/-
# Eliminating the axis: a corner statement in leverages, readings and pair minors

`Gtz.quadForm_sum_of_corner` says a corner reads EVERY form at total
`tr A + lam*<u, A u>`.  Read at the rank-one form of a single vector it prices
that vector's squared readings against the inside triple, and read at the pair
normal it prices the squared brackets.  Both totals still name the axis `u`.

This module removes it.  The mixed pair minors of an outside atom against the
inside triple carry exactly the same axis information
(`Gtz.corner_mixedPairMinor_sum`), so solving one total for `<u,d>^2` and
substituting into the other leaves

  **`Gtz.corner_reading_sq_sum_axisFree`:
   sum_{e in C} (d.g_e)^2 = lam*(l_d - 1) - sum_{e in C} pairGapMinor g_e d`** .

THE AXIS IS GONE.  Combined with the bracket-free split of
`Gtz.tripleGapDet_eq_pairAxisForm`, a corner statement about a one-inside triple
now carries NEITHER the axis NOR the bracket: only leverages, readings and pair
minors.

## What the smaller alphabet buys

`Gtz.corner_exists_tripleGapDet_pos_axisFree` is the producer in that alphabet.
Over an admissible outside pair `{a,b}` with trace `T = l_a + l_b - 2`, writing
`Q` for the total mixed pair minor of the pair against the inside triple, some
inside atom strictly dominates as soon as

  `T * (lam*T - Q)  <  lam * pairGapMinor a b` .

Every symbol is a leverage or a pair minor.  No axis, no bracket, no adjugate,
no matrix.

## Honest scope

This producer is an aggregation, and `Gtz.corner_pairSum_pos_lam_threshold`
already proves that aggregating over the three inside atoms cannot discharge the
branch by itself -- the pair-only part of the sum law is strictly negative on an
admissible pair and the axis form only subtracts.  The value here is the
ALPHABET, not extra strength: the same fight is now stated without the two
symbols that blocked every previous elimination.
-/
import Gtz.Wave.CornerPairAdjugate
import Gtz.Wave.KOneWedgeCeiling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. Two readings of the corner quadratic total -/

/-- The rank-one form of a vector reads another vector at the squared pairing. -/
theorem atomMatrix_quadForm (d g : Fin 3 → ℝ) :
    g ⬝ᵥ (atomMatrix d *ᵥ g) = (d ⬝ᵥ g) ^ 2 := by
  simp only [atomMatrix, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  ring

/-- The trace of a rank-one atom is its leverage. -/
theorem trace_atomMatrix_eq_leverage (d : Fin 3 → ℝ) :
    Matrix.trace (atomMatrix d) = leverageOf d := by
  simp only [atomMatrix, Matrix.trace_fin_three, Matrix.vecMulVec_apply,
    leverageOf, Fin.sum_univ_three]
  ring

/-- **THE READING TOTAL.**  A corner prices any vector's squared readings against
its inside triple at that vector's leverage plus the scale against its squared
axis reading. -/
theorem corner_reading_sq_sum (d gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u) :
    (d ⬝ᵥ gx) ^ 2 + (d ⬝ᵥ gy) ^ 2 + (d ⬝ᵥ gz) ^ 2
      = leverageOf d + lam * (d ⬝ᵥ u) ^ 2 := by
  have h := quadForm_sum_of_corner (atomMatrix d) gx gy gz u hcorner
  rw [atomMatrix_quadForm, atomMatrix_quadForm, atomMatrix_quadForm,
    atomMatrix_quadForm, trace_atomMatrix_eq_leverage] at h
  exact h

/-- **THE BRACKET TOTAL.**  Read at the pair normal, the same law prices the three
squared brackets of the inside atoms against an outside pair by that pair's wedge
plus the scale against the axis bracket. -/
theorem corner_bracketNormal_sq_sum (a b gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u) :
    (bracketNormal a b ⬝ᵥ gx) ^ 2 + (bracketNormal a b ⬝ᵥ gy) ^ 2
        + (bracketNormal a b ⬝ᵥ gz) ^ 2
      = crossNormSq a b + lam * (bracketNormal a b ⬝ᵥ u) ^ 2 := by
  rw [corner_reading_sq_sum (bracketNormal a b) gx gy gz u hcorner, crossNormSq]
  simp only [leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-! ## 2. The mixed pair minors carry the same axis information -/

/-- **THE MIXED PAIR MINOR TOTAL.**  The pair minors of an outside atom against
the three inside atoms total to pure leverage-and-scale data less the axis
reading.  Nothing here needs a tie or an admissible pair. -/
theorem corner_mixedPairMinor_sum (d gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hu : leverageOf u = 1) :
    pairGapMinor gx d + pairGapMinor gy d + pairGapMinor gz d
      = (lam - 1) * leverageOf d - lam * (d ⬝ᵥ u) ^ 2 - lam := by
  have hread := corner_reading_sq_sum d gx gy gz u hcorner
  have hbudget := corner_leverageExcess_sum gx gy gz u hcorner hu
  simp only [pairGapMinor]
  have hdx : (gx ⬝ᵥ d) = (d ⬝ᵥ gx) := dotProduct_comm _ _
  have hdy : (gy ⬝ᵥ d) = (d ⬝ᵥ gy) := dotProduct_comm _ _
  have hdz : (gz ⬝ᵥ d) = (d ⬝ᵥ gz) := dotProduct_comm _ _
  rw [hdx, hdy, hdz]
  linear_combination (leverageOf d - 1) * hbudget - hread

/-- **THE AXIS READING, SOLVED.**  The squared axis reading of an outside atom is
a polynomial in its leverage, the scale, and its three mixed pair minors. -/
theorem corner_axis_reading_sq_eq (d gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hu : leverageOf u = 1) :
    lam * (d ⬝ᵥ u) ^ 2
      = (lam - 1) * leverageOf d - lam
        - (pairGapMinor gx d + pairGapMinor gy d + pairGapMinor gz d) := by
  have h := corner_mixedPairMinor_sum d gx gy gz u hcorner hu
  linarith

/-- **THE AXIS IS GONE.**  Substituting the solved reading into the reading total
leaves a corner law in leverages and pair minors only.  No axis, no bracket, no
matrix. -/
theorem corner_reading_sq_sum_axisFree (d gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hu : leverageOf u = 1) :
    (d ⬝ᵥ gx) ^ 2 + (d ⬝ᵥ gy) ^ 2 + (d ⬝ᵥ gz) ^ 2
      = lam * (leverageOf d - 1)
        - (pairGapMinor gx d + pairGapMinor gy d + pairGapMinor gz d) := by
  have hread := corner_reading_sq_sum d gx gy gz u hcorner
  have hsolved := corner_axis_reading_sq_eq d gx gy gz u hcorner hu
  linarith

/-! ## 3. The producer in the smaller alphabet -/

/-- **THE AXIS-FREE PRODUCER.**  Over an admissible outside pair, one inside atom
strictly beats the pair as soon as the pair's trace against its total mixed
readings falls below the scale against the pair minor.  Every symbol is a
leverage or a pair minor. -/
theorem corner_exists_tripleGapDet_pos_axisFree {a b : Fin 3 → ℝ}
    (gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hu : leverageOf u = 1) (ha : 1 < leverageOf a)
    (hmin : 0 < pairGapMinor a b)
    (hbeat : (leverageOf a + leverageOf b - 2)
        * (lam * (leverageOf a + leverageOf b - 2)
          - ((pairGapMinor gx a + pairGapMinor gy a + pairGapMinor gz a)
            + (pairGapMinor gx b + pairGapMinor gy b + pairGapMinor gz b)))
      < lam * pairGapMinor a b) :
    0 < tripleGapDet a b gx ∨ 0 < tripleGapDet a b gy
      ∨ 0 < tripleGapDet a b gz := by
  have hA := corner_reading_sq_sum_axisFree a gx gy gz u hcorner hu
  have hB := corner_reading_sq_sum_axisFree b gx gy gz u hcorner hu
  have hbudget := corner_leverageExcess_sum gx gy gz u hcorner hu
  -- the three per-atom slacks total to a positive number
  by_contra hcon
  push Not at hcon
  obtain ⟨hx, hy, hz⟩ := hcon
  have hsx := (tripleGapDet_nonpos_iff_excess_le_cost a b gx).mp hx
  have hsy := (tripleGapDet_nonpos_iff_excess_le_cost a b gy).mp hy
  have hsz := (tripleGapDet_nonpos_iff_excess_le_cost a b gz).mp hz
  have hcx := pairAxisForm_ge_neg_trace_mul ha hmin (a ⬝ᵥ gx) (b ⬝ᵥ gx)
  have hcy := pairAxisForm_ge_neg_trace_mul ha hmin (a ⬝ᵥ gy) (b ⬝ᵥ gy)
  have hcz := pairAxisForm_ge_neg_trace_mul ha hmin (a ⬝ᵥ gz) (b ⬝ᵥ gz)
  have hdx : (a ⬝ᵥ gx) = (gx ⬝ᵥ a) := dotProduct_comm _ _
  have hdy : (a ⬝ᵥ gy) = (gy ⬝ᵥ a) := dotProduct_comm _ _
  have hdz : (a ⬝ᵥ gz) = (gz ⬝ᵥ a) := dotProduct_comm _ _
  have hex : (b ⬝ᵥ gx) = (gx ⬝ᵥ b) := dotProduct_comm _ _
  have hey : (b ⬝ᵥ gy) = (gy ⬝ᵥ b) := dotProduct_comm _ _
  have hez : (b ⬝ᵥ gz) = (gz ⬝ᵥ b) := dotProduct_comm _ _
  set T : ℝ := leverageOf a + leverageOf b - 2 with hT
  -- each inside atom pays its leverage excess against the cost of its readings
  have kx : (leverageOf gx - 1) * pairGapMinor a b
      ≤ T * ((a ⬝ᵥ gx) ^ 2 + (b ⬝ᵥ gx) ^ 2) := by linarith [hsx, hcx]
  have ky : (leverageOf gy - 1) * pairGapMinor a b
      ≤ T * ((a ⬝ᵥ gy) ^ 2 + (b ⬝ᵥ gy) ^ 2) := by linarith [hsy, hcy]
  have kz : (leverageOf gz - 1) * pairGapMinor a b
      ≤ T * ((a ⬝ᵥ gz) ^ 2 + (b ⬝ᵥ gz) ^ 2) := by linarith [hsz, hcz]
  -- total them, then eliminate the axis on the right
  have hleft : lam * pairGapMinor a b
      = (leverageOf gx - 1) * pairGapMinor a b
        + (leverageOf gy - 1) * pairGapMinor a b
        + (leverageOf gz - 1) * pairGapMinor a b := by
    rw [← hbudget]; ring
  have hright : T * ((a ⬝ᵥ gx) ^ 2 + (b ⬝ᵥ gx) ^ 2)
      + T * ((a ⬝ᵥ gy) ^ 2 + (b ⬝ᵥ gy) ^ 2)
      + T * ((a ⬝ᵥ gz) ^ 2 + (b ⬝ᵥ gz) ^ 2)
      = T * (lam * T
        - ((pairGapMinor gx a + pairGapMinor gy a + pairGapMinor gz a)
          + (pairGapMinor gx b + pairGapMinor gy b + pairGapMinor gz b))) := by
    have hAB : ((a ⬝ᵥ gx) ^ 2 + (a ⬝ᵥ gy) ^ 2 + (a ⬝ᵥ gz) ^ 2)
        + ((b ⬝ᵥ gx) ^ 2 + (b ⬝ᵥ gy) ^ 2 + (b ⬝ᵥ gz) ^ 2)
        = lam * T
          - ((pairGapMinor gx a + pairGapMinor gy a + pairGapMinor gz a)
            + (pairGapMinor gx b + pairGapMinor gy b + pairGapMinor gz b)) := by
      rw [hA, hB, hT]; ring
    linear_combination T * hAB
  linarith [kx, ky, kz, hleft, hright, hbeat]

/-! ## 4. The corner's own scale ceiling -/

/-- **A CORNER DETERMINANT IS ONE PLUS ITS SCALE.**  Reading the corner equation
through the determinant of a rank-one update. -/
theorem corner_det_eq_one_add_scale (u : Fin 3 → ℝ) {lam : ℝ}
    (hu : leverageOf u = 1) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) + lam • atomMatrix u).det = 1 + lam := by
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_fin_three,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  simp only [leverageOf, Fin.sum_univ_three] at hu
  linear_combination lam * hu

/-- **THE INSIDE WEDGE CEILING AT A CORNER.**  A corner weakly dominates, so the
landed wedge ceiling caps every wedge of its inside triple by the corner
determinant, which is one plus the scale.  Free: no tie, no admissible pair. -/
theorem corner_inside_crossNormSq_le (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    crossNormSq (D.atom x) (D.atom y)
      ≤ tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 :=
  crossNormSq_le_tripleBracket_sq_of_dominates D hxy hxz hyz
    (corner_dominates D _ hlam hgap)

end Gtz
