/-
# The wedge ceiling: a dominating triple caps every pair wedge by its bracket

The campaign prices a triple from below.  `Gtz.e2_mul_form_ge_det_mul_normSq`
gives `det A * ‖ξ‖² ≤ e₂(A) * (ξᵀAξ)`, the spectral-free floor `λmin ≥ e₃/e₂`,
and `Gtz.isTie_block_tax` spends it at a tie.  Every instrument in that family
is a FLOOR, and a floor produces dominators.

This module lands the CEILING, and it is elementary.  Probe the gap of a triple
at the normal of one of its pairs.  That normal is orthogonal to the two atoms
that make it, so the whole quadratic form of the atom sum collapses onto the
third atom, where it reads the bracket:

  `bracketNormal a b ⬝ᵥ (S_{a,b,c} *ᵥ bracketNormal a b) = tripleBracket a b c ^ 2`

while the identity contributes `crossNormSq a b`, the pair wedge, BY
DEFINITION.  Positive semidefiniteness of the gap therefore says

  **`crossNormSq a b ≤ tripleBracket a b c ^ 2`**   (`Gtz.crossNormSq_le_tripleBracket_sq_of_dominates`)

— at a DOMINATING triple every pair wedge is at most the squared bracket.  Two
lines, no adjugate, no eigenvalue, no tie hypothesis.

## What it buys

The contrapositive is a REFUSAL PRODUCER that costs nothing:
`Gtz.not_dominates_of_tripleBracket_sq_lt_crossNormSq` refuses a triple the
moment ONE of its three pair wedges beats its squared bracket.  No tie, no
corner, no stratum — it is available in every lane, and it is stated in the two
terminal currencies of the hinge (wedge and bracket) and in nothing else.

Summing the three pairs gives `Gtz.triplePairAreaSum_le_three_mul_bracket_sq`,
which closes a sandwich around the landed floor: with `e₂(S_T)` the pair area
sum and `det(S_T)` the squared bracket,

  `e₂ ≤ det`  ⟹  dominates  (the landed teeth)
  dominates   ⟹  `e₂ ≤ 3 * det`  (here)

so the two differ by exactly the factor three, and no more.

## What it does NOT buy, measured in kernel

Section 5 evaluates the ceiling on the K1 normal form, where the live pair
carries `crossNormSq = s²` and the triple carries `tripleBracket ^ 2 = γ²s²`.
The ceiling there reads `s² ≤ γ²s²`, i.e. `(γ² − 1) * s² ≥ 0`, which is the
corank-one condition itself.  **The ceiling is exactly sharp on the K1 live
pair and supplies nothing beyond corank one there.**  It cannot kill K1 alone,
and the next attempt must not spend a round rediscovering that.
-/
import Gtz.Design.TripleGramSylvester

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The pair normal as a probe -/

/-- The quadratic form of a rank-one atom at a probe is the squared reading. -/
theorem atomMatrix_dotProduct_mulVec (atomVec probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (atomMatrix atomVec *ᵥ probe) = (atomVec ⬝ᵥ probe) ^ 2 := by
  simp only [atomMatrix, Matrix.vecMulVec, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.of_apply]
  ring

/-- The pair normal is orthogonal to the left atom that makes it. -/
theorem dotProduct_bracketNormal_left (leftVec rightVec : Fin 3 → ℝ) :
    leftVec ⬝ᵥ bracketNormal leftVec rightVec = 0 := by
  simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The pair normal is orthogonal to the right atom that makes it. -/
theorem dotProduct_bracketNormal_right (leftVec rightVec : Fin 3 → ℝ) :
    rightVec ⬝ᵥ bracketNormal leftVec rightVec = 0 := by
  simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The third atom reads the pair normal as the bracket. -/
theorem dotProduct_bracketNormal_third (leftVec midVec thirdVec : Fin 3 → ℝ) :
    thirdVec ⬝ᵥ bracketNormal leftVec midVec = tripleBracket leftVec midVec thirdVec := by
  simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    tripleBracket_eq]
  ring

/-- **THE PROBE IDENTITY.**  The gap of a triple, read at the normal of its
first pair, is the squared bracket minus the pair wedge.  Both atoms of the
pair drop out, so the whole form is carried by the third atom. -/
theorem bracketNormal_gap_form (leftVec midVec thirdVec : Fin 3 → ℝ) :
    bracketNormal leftVec midVec ⬝ᵥ
        ((atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec - 1)
          *ᵥ bracketNormal leftVec midVec)
      = tripleBracket leftVec midVec thirdVec ^ 2 - crossNormSq leftVec midVec := by
  have hprobe : bracketNormal leftVec midVec ⬝ᵥ
      ((atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec - 1)
        *ᵥ bracketNormal leftVec midVec)
      = (leftVec ⬝ᵥ bracketNormal leftVec midVec) ^ 2
        + (midVec ⬝ᵥ bracketNormal leftVec midVec) ^ 2
        + (thirdVec ⬝ᵥ bracketNormal leftVec midVec) ^ 2
        - bracketNormal leftVec midVec ⬝ᵥ bracketNormal leftVec midVec := by
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_add, atomMatrix_dotProduct_mulVec]
  rw [hprobe, dotProduct_bracketNormal_left, dotProduct_bracketNormal_right,
    dotProduct_bracketNormal_third, crossNormSq]
  ring

/-! ## 2. The ceiling -/

/-- **THE WEDGE CEILING, AT THE VECTOR LEVEL.**  If the gap of a triple is
positive semidefinite, the wedge of its first pair is at most the squared
bracket of the triple. -/
theorem crossNormSq_le_tripleBracket_sq_of_posSemidef (leftVec midVec thirdVec : Fin 3 → ℝ)
    (hgap : (atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec
      - 1).PosSemidef) :
    crossNormSq leftVec midVec ≤ tripleBracket leftVec midVec thirdVec ^ 2 := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hgap).2
    (bracketNormal leftVec midVec)
  rw [star_trivial, bracketNormal_gap_form] at hform
  linarith

/-- The same ceiling read at the second pair. -/
theorem crossNormSq_le_tripleBracket_sq_of_posSemidef_mid
    (leftVec midVec thirdVec : Fin 3 → ℝ)
    (hgap : (atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec
      - 1).PosSemidef) :
    crossNormSq midVec thirdVec ≤ tripleBracket leftVec midVec thirdVec ^ 2 := by
  have hperm : atomMatrix midVec + atomMatrix thirdVec + atomMatrix leftVec
      = atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec := by abel
  have hgap' : (atomMatrix midVec + atomMatrix thirdVec + atomMatrix leftVec
      - 1).PosSemidef := by rw [hperm]; exact hgap
  have hmain := crossNormSq_le_tripleBracket_sq_of_posSemidef midVec thirdVec leftVec hgap'
  have hcyc : tripleBracket midVec thirdVec leftVec ^ 2
      = tripleBracket leftVec midVec thirdVec ^ 2 := by
    simp only [tripleBracket_eq]; ring
  linarith [hmain, hcyc.ge, hcyc.le]

/-- The same ceiling read at the third pair. -/
theorem crossNormSq_le_tripleBracket_sq_of_posSemidef_outer
    (leftVec midVec thirdVec : Fin 3 → ℝ)
    (hgap : (atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec
      - 1).PosSemidef) :
    crossNormSq thirdVec leftVec ≤ tripleBracket leftVec midVec thirdVec ^ 2 := by
  have hperm : atomMatrix thirdVec + atomMatrix leftVec + atomMatrix midVec
      = atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec := by abel
  have hgap' : (atomMatrix thirdVec + atomMatrix leftVec + atomMatrix midVec
      - 1).PosSemidef := by rw [hperm]; exact hgap
  have hmain := crossNormSq_le_tripleBracket_sq_of_posSemidef thirdVec leftVec midVec hgap'
  have hcyc : tripleBracket thirdVec leftVec midVec ^ 2
      = tripleBracket leftVec midVec thirdVec ^ 2 := by
    simp only [tripleBracket_eq]; ring
  linarith [hmain, hcyc.ge, hcyc.le]

/-- **THE AREA SUM CEILING.**  A dominating triple carries pair area at most
three times its squared bracket.  With the landed floor `e₂ ≤ det ⟹ dominates`
this brackets domination between the two multiples of the bracket, and the gap
between them is exactly the factor three. -/
theorem triplePairAreaSum_le_three_mul_tripleBracket_sq
    (leftVec midVec thirdVec : Fin 3 → ℝ)
    (hgap : (atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec
      - 1).PosSemidef) :
    triplePairAreaSum leftVec midVec thirdVec
      ≤ 3 * tripleBracket leftVec midVec thirdVec ^ 2 := by
  have h1 := crossNormSq_le_tripleBracket_sq_of_posSemidef leftVec midVec thirdVec hgap
  have h2 := crossNormSq_le_tripleBracket_sq_of_posSemidef_mid leftVec midVec thirdVec hgap
  have h3 := crossNormSq_le_tripleBracket_sq_of_posSemidef_outer leftVec midVec thirdVec hgap
  have hsym : crossNormSq thirdVec leftVec = crossNormSq leftVec thirdVec := by
    simp only [crossNormSq, bracketNormal, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [triplePairAreaSum, ← hsym]
  linarith

/-! ## 3. The refusal producer -/

/-- **A FREE REFUSAL.**  One pair wedge beating the squared bracket refuses the
triple outright.  There is no tie hypothesis, no corner, and no stratum: this
is available wherever three atoms are. -/
theorem not_posSemidef_of_tripleBracket_sq_lt_crossNormSq
    (leftVec midVec thirdVec : Fin 3 → ℝ)
    (hbeat : tripleBracket leftVec midVec thirdVec ^ 2 < crossNormSq leftVec midVec) :
    ¬ (atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec - 1).PosSemidef := by
  intro hgap
  exact absurd (crossNormSq_le_tripleBracket_sq_of_posSemidef leftVec midVec thirdVec hgap)
    (not_le.mpr hbeat)

/-! ## 4. The design level -/

/-- The atom sum of an explicit triple. -/
theorem subsetSum_triple_eq_add (design : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    subsetSum design ({x, y, z} : Finset (Fin m))
      = atomMatrix (design.atom x) + atomMatrix (design.atom y)
        + atomMatrix (design.atom z) := by
  rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton, add_assoc]

/-- **THE WEDGE CEILING AT A DESIGN.**  Every pair wedge of a dominating triple
is at most the squared bracket of that triple. -/
theorem crossNormSq_le_tripleBracket_sq_of_dominates (design : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates design ({x, y, z} : Finset (Fin m))) :
    crossNormSq (design.atom x) (design.atom y)
      ≤ tripleBracket (design.atom x) (design.atom y) (design.atom z) ^ 2 := by
  rw [Dominates, subsetSum_triple_eq_add design hxy hxz hyz] at hdom
  exact crossNormSq_le_tripleBracket_sq_of_posSemidef _ _ _ hdom

/-- **THE FREE REFUSAL AT A DESIGN.**  A pair wedge above the squared bracket
refuses the triple, with no tie hypothesis. -/
theorem not_dominates_of_tripleBracket_sq_lt_crossNormSq (design : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hbeat : tripleBracket (design.atom x) (design.atom y) (design.atom z) ^ 2
      < crossNormSq (design.atom x) (design.atom y)) :
    ¬ Dominates design ({x, y, z} : Finset (Fin m)) := by
  intro hdom
  exact absurd (crossNormSq_le_tripleBracket_sq_of_dominates design hxy hxz hyz hdom)
    (not_le.mpr hbeat)

/-! ## 5. The ceiling is exactly sharp on the K1 live pair

The K1 normal form puts the null direction in the first coordinate, the live
pair in the plane it spans with the second, and the erased atom in the last two.
Writing `s` for the square root of the pinned wedge, the live atoms are
`(βy, s·βz, 0)` and `(βz, −s·βy, 0)` and the erased atom is `(0, α, γ)`.
-/

/-- The live pair of the K1 normal form. -/
def kOneLiveLeft (betaY betaZ scale : ℝ) : Fin 3 → ℝ := ![betaY, scale * betaZ, 0]

/-- The second live atom of the K1 normal form. -/
def kOneLiveRight (betaY betaZ scale : ℝ) : Fin 3 → ℝ := ![betaZ, -(scale * betaY), 0]

/-- The erased atom of the K1 normal form: it has no null reading. -/
def kOneErased (alpha gamma : ℝ) : Fin 3 → ℝ := ![0, alpha, gamma]

/-- **THE LIVE PAIR CARRIES EXACTLY THE PINNED WEDGE.**  On the unit circle of
readings the wedge of the live pair is the scale squared, with no dependence on
where the pair sits on that circle. -/
theorem crossNormSq_kOneLive (betaY betaZ scale : ℝ) (hunit : betaY ^ 2 + betaZ ^ 2 = 1) :
    crossNormSq (kOneLiveLeft betaY betaZ scale) (kOneLiveRight betaY betaZ scale)
      = scale ^ 2 := by
  simp only [crossNormSq, bracketNormal, kOneLiveLeft, kOneLiveRight, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination (scale ^ 2 * (betaY ^ 2 + betaZ ^ 2 + 1)) * hunit

/-- **THE K1 BRACKET.**  The squared bracket of the K1 triple is the scale
squared times the squared transverse reading of the erased atom. -/
theorem tripleBracket_sq_kOne (betaY betaZ scale alpha gamma : ℝ)
    (hunit : betaY ^ 2 + betaZ ^ 2 = 1) :
    tripleBracket (kOneLiveLeft betaY betaZ scale) (kOneLiveRight betaY betaZ scale)
        (kOneErased alpha gamma) ^ 2
      = gamma ^ 2 * scale ^ 2 := by
  simp only [tripleBracket_eq, kOneLiveLeft, kOneLiveRight, kOneErased,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination (scale ^ 2 * gamma ^ 2 * (betaY ^ 2 + betaZ ^ 2 + 1)) * hunit

/-- **THE CEILING IS THE CORANK CONDITION, AND NOTHING MORE.**  On the K1
normal form the wedge ceiling at the live pair says exactly
`(γ² − 1) · s² ≥ 0`.  Since corank one already carries `γ² > 1`, the ceiling
adds NO information on this stratum.  A K1 kill must come from elsewhere. -/
theorem kOne_wedge_ceiling_is_corank_condition (betaY betaZ scale alpha gamma : ℝ)
    (hunit : betaY ^ 2 + betaZ ^ 2 = 1) :
    (crossNormSq (kOneLiveLeft betaY betaZ scale) (kOneLiveRight betaY betaZ scale)
        ≤ tripleBracket (kOneLiveLeft betaY betaZ scale) (kOneLiveRight betaY betaZ scale)
            (kOneErased alpha gamma) ^ 2)
      ↔ 0 ≤ (gamma ^ 2 - 1) * scale ^ 2 := by
  rw [crossNormSq_kOneLive betaY betaZ scale hunit,
    tripleBracket_sq_kOne betaY betaZ scale alpha gamma hunit]
  constructor <;> intro h <;> nlinarith [h]

end Gtz
