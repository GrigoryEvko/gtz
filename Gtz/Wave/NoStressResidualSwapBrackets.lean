import Gtz.Design.StressFreeStratum
import Gtz.Design.StressFreeClassSplit
import Gtz.Design.CapSlack
import Gtz.Design.PairDifferenceCover
import Gtz.Wave.VeroneseWeightElimination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The free-mass budget of a triple, read in brackets

`Gtz.NoStressResidual 6` assumes that NO triple of a primitive stress-free design
carries a certificate.  One half of that hypothesis is the failure of the free-mass
budget of `Gtz.posDef_gap_of_freeMassBudget`, and that budget is written with a
matrix inverse:

    `budget(C) = Σ_{a ∉ C} t_a · (g_a ⬝ᵥ Y_C⁻¹ g_a)` ,   `Y_C = Σ_{c ∈ C} (1 − t_c) g_c g_cᵀ` .

Nobody can spend a hypothesis in that shape.  This file removes the inverse.  For a
rank-three design and a spanning triple `C = {p, q, r}` the budget is a ratio of
BRACKETS — squared three-by-three determinants of atom triples — and nothing else:

    `budget(C) = Σ_{c ∈ C} Σ_{a ∉ C} (t_a / (1 − t_c)) · [C − c + a]² / [C]²`      (I)
    `budget(C) = Σ_{c ∈ C} ( ⟨C ∖ c⟩ / [C]² − t_c ) / (1 − t_c)`                    (II)

with `[B]` the bracket of a triple and `⟨d, e⟩ = |g_d|²|g_e|² − (g_d ⬝ᵥ g_e)²` the pair
Gram determinant.  Form (I) reads the budget on the EXCHANGE GRAPH: the nine triples
that differ from `C` in one label.  Form (II) collapses each of the three swap fans by
the two-point marginal `Gtz.sum_weight_mul_sq_tripleBracket`, and reads only the three
pair Gram determinants inside `C` against `C`'s own bracket.

## What this buys

* `Gtz.posDef_gap_of_pairSwapMass_lt` — a domination test in brackets only.  It is
  EQUIVALENT to the free-mass certificate, not weaker: form (II) is an identity.
* `Gtz.le_pairSwapMass_of_not_hasStrictCertificate` — the certificate-free hypothesis
  of `Gtz.NoStressResidual`, spent: at EVERY spanning triple of a certificate-free
  design the three pair Gram determinants beat the bracket, in the exact weighted
  sense of form (II).  That is the first reading of that hypothesis that carries no
  inverse and no eigenvalue.
* `Gtz.posDef_gap_of_sum_pairBracketSq_lt` — the WEIGHT-FREE corollary: a triple whose
  three pair Gram determinants total less than its squared bracket dominates strictly.
  Contrapositive: every spanning triple of a certificate-free design has
  `⟨q,r⟩ + ⟨p,r⟩ + ⟨p,q⟩ ≥ [p,q,r]²`, an inequality in the atom directions alone.
* `Gtz.tripleSwapMass_nonneg` — each numerator of form (II) is a swap mass, hence
  nonnegative: `⟨q,r⟩ − t_p [p,q,r]² = Σ_{a ∉ C} t_a [q,r,a]²`.

## The route

Three ingredients, each elementary.

* `Gtz.det_smul_atomMatrix_four` — the determinant of a four-atom combination is the
  bracket expansion `Σ_{|B| = 3} (∏_{i ∈ B} z_i) [B]²`.  A polynomial identity in
  twelve coordinates and four scalars, closed by `ring`.  At rank three four atoms
  carry four triples, so the expansion is affine in the fourth coefficient — which is
  exactly what makes the inverse form readable.
* `Gtz.det_add_atomMatrix` — the matrix determinant lemma, already in the tree.
  Together with the expansion it gives `Gtz.det_mul_inverseForm_eq_bracket_sum`:
  `det Y · (g_y ⬝ᵥ Y⁻¹ g_y)` is a bracket sum with no inverse left in it.
* `Gtz.sum_weight_mul_sq_tripleBracket` — the two-point marginal in brackets:
  `Σ_a t_a [d, e, a]² = ⟨d, e⟩`.  Parseval against the cross product, then Lagrange.
  This is the bracket twin of the projection-form marginal
  `Gtz.pairMinorAt_eq_sum_det_tripleBlock`, and it is what turns form (I) into (II).

## Calibration

At the `(6,3)` root design `Gtz.coordinateDiagonalDesign` every atom has leverage
three, every pair Gram determinant is `27/4` except the three orthogonal pairs where
it is `9`, and every spanning triple has bracket square `27/2`.  Form (II) then gives
`6/5` on the four triples with no orthogonal pair and `7/5` on the twelve with exactly
one.  Those are the two numbers the audit records as MEASURED at the `K4` star; here
they are arithmetic.  So the free-mass budget of a triple counts that triple's
orthogonal pairs, and the campaign's calibration object misses the certificate by the
exact amount `1/5` per non-orthogonal pair.
-/

namespace Gtz

open scoped BigOperators

open Matrix

variable {size : ℕ}

/-! ## 1. Brackets, pair Gram determinants, and the elementary identities -/

/-- The pair Gram determinant `⟨d, e⟩ = |g_d|² |g_e|² − (g_d ⬝ᵥ g_e)²`: the squared area
of the parallelogram the two atoms span. -/
def pairBracketSq (leftVec rightVec : Fin 3 → ℝ) : ℝ :=
  leverageOf leftVec * leverageOf rightVec - (leftVec ⬝ᵥ rightVec) ^ 2

/-- The pair Gram determinant is the squared length of the cross product — Lagrange. -/
theorem pairBracketSq_eq_bracketNormal (leftVec rightVec : Fin 3 → ℝ) :
    pairBracketSq leftVec rightVec
      = bracketNormal leftVec rightVec ⬝ᵥ bracketNormal leftVec rightVec := by
  rw [pairBracketSq, bracketNormal_self_dotProduct, leverageOf_eq_dotProduct_self,
    leverageOf_eq_dotProduct_self]

/-- A pair Gram determinant is never negative. -/
theorem pairBracketSq_nonneg (leftVec rightVec : Fin 3 → ℝ) :
    0 ≤ pairBracketSq leftVec rightVec := by
  rw [pairBracketSq_eq_bracketNormal]
  exact dotProduct_self_nonneg _

/-- A repeated slot kills the bracket. -/
theorem tripleBracket_self_left (leftVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec rightVec leftVec = 0 := by
  simp only [tripleBracket_eq]; ring

/-- A repeated slot kills the bracket, second shape. -/
theorem tripleBracket_self_right (leftVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec rightVec rightVec = 0 := by
  simp only [tripleBracket_eq]; ring

/-- The bracket is cyclic. -/
theorem tripleBracket_cycle (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket midVec rightVec leftVec = tripleBracket leftVec midVec rightVec := by
  simp only [tripleBracket_eq]; ring

/-- The bracket changes sign under a transposition of the first two slots. -/
theorem tripleBracket_swap_left (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket midVec leftVec rightVec = -tripleBracket leftVec midVec rightVec := by
  simp only [tripleBracket_eq]; ring

/-- **Cramer against a probe.**  A polynomial identity in twelve coordinates: the
bracket times the probe's own square is the probe's three Cramer readings.  This is the
only spanning fact the file needs, and it carries no inverse. -/
theorem tripleBracket_mul_dotProduct_self (leftVec midVec rightVec probe : Fin 3 → ℝ) :
    tripleBracket leftVec midVec rightVec * (probe ⬝ᵥ probe)
      = tripleBracket probe midVec rightVec * (leftVec ⬝ᵥ probe)
        + tripleBracket leftVec probe rightVec * (midVec ⬝ᵥ probe)
        + tripleBracket leftVec midVec probe * (rightVec ⬝ᵥ probe) := by
  simp only [tripleBracket_eq, dotProduct, Fin.sum_univ_three]
  ring

/-- **A spanning triple reads every probe.**  If a probe is orthogonal to three atoms of
nonzero bracket then the probe is zero. -/
theorem eq_zero_of_tripleBracket_ne_zero (leftVec midVec rightVec probe : Fin 3 → ℝ)
    (hbracket : tripleBracket leftVec midVec rightVec ≠ 0)
    (hleft : leftVec ⬝ᵥ probe = 0) (hmid : midVec ⬝ᵥ probe = 0)
    (hright : rightVec ⬝ᵥ probe = 0) : probe = 0 := by
  have hself : tripleBracket leftVec midVec rightVec * (probe ⬝ᵥ probe) = 0 := by
    rw [tripleBracket_mul_dotProduct_self, hleft, hmid, hright]; ring
  have hzero : probe ⬝ᵥ probe = 0 := by
    rcases mul_eq_zero.mp hself with hbad | hgood
    · exact absurd hbad hbracket
    · exact hgood
  exact dotProduct_self_eq_zero.mp hzero

/-! ## 2. The bracket expansion of a three- and a four-atom determinant -/

/-- **Three atoms.**  `det (a A_u + b A_v + c A_x) = a b c [u, v, x]²`.  A polynomial
identity in nine coordinates and three scalars. -/
theorem det_smul_atomMatrix_three (firstVec secondVec thirdVec : Fin 3 → ℝ)
    (firstCoeff secondCoeff thirdCoeff : ℝ) :
    (firstCoeff • atomMatrix firstVec + secondCoeff • atomMatrix secondVec
        + thirdCoeff • atomMatrix thirdVec).det
      = firstCoeff * secondCoeff * thirdCoeff
        * tripleBracket firstVec secondVec thirdVec ^ 2 := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    atomMatrix, Matrix.vecMulVec_apply, tripleBracket_eq]
  ring

/-- **Four atoms, at rank three.**  Four atoms carry exactly four triples, and the
determinant is their bracket expansion

    `det (a A_u + b A_v + c A_x + d A_y) = abc[u,v,x]² + abd[u,v,y]² + acd[u,x,y]² + bcd[v,x,y]²` .

Every term is a product of THREE coefficients, so the expression is affine in each
coefficient separately — the fact that makes the inverse form readable. -/
theorem det_smul_atomMatrix_four (firstVec secondVec thirdVec fourthVec : Fin 3 → ℝ)
    (firstCoeff secondCoeff thirdCoeff fourthCoeff : ℝ) :
    (firstCoeff • atomMatrix firstVec + secondCoeff • atomMatrix secondVec
        + thirdCoeff • atomMatrix thirdVec + fourthCoeff • atomMatrix fourthVec).det
      = firstCoeff * secondCoeff * thirdCoeff
          * tripleBracket firstVec secondVec thirdVec ^ 2
        + firstCoeff * secondCoeff * fourthCoeff
          * tripleBracket firstVec secondVec fourthVec ^ 2
        + firstCoeff * thirdCoeff * fourthCoeff
          * tripleBracket firstVec thirdVec fourthVec ^ 2
        + secondCoeff * thirdCoeff * fourthCoeff
          * tripleBracket secondVec thirdVec fourthVec ^ 2 := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    atomMatrix, Matrix.vecMulVec_apply, tripleBracket_eq]
  ring

/-! ## 3. The free-mass matrix of a spanning triple -/

/-- The free-mass matrix of three atoms with three positive coefficients is positive
definite exactly when the triple spans.  One direction, the one the certificate needs. -/
theorem posDef_smul_atomMatrix_three (firstVec secondVec thirdVec : Fin 3 → ℝ)
    {firstCoeff secondCoeff thirdCoeff : ℝ}
    (hfirst : 0 < firstCoeff) (hsecond : 0 < secondCoeff) (hthird : 0 < thirdCoeff)
    (hbracket : tripleBracket firstVec secondVec thirdVec ≠ 0) :
    (firstCoeff • atomMatrix firstVec + secondCoeff • atomMatrix secondVec
      + thirdCoeff • atomMatrix thirdVec).PosDef := by
  have hsymm : (firstCoeff • atomMatrix firstVec + secondCoeff • atomMatrix secondVec
      + thirdCoeff • atomMatrix thirdVec)ᵀ
      = firstCoeff • atomMatrix firstVec + secondCoeff • atomMatrix secondVec
        + thirdCoeff • atomMatrix thirdVec := by
    simp only [Matrix.transpose_add, Matrix.transpose_smul, atomMatrix_transpose]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  rw [star_trivial]
  have hform : probe ⬝ᵥ ((firstCoeff • atomMatrix firstVec + secondCoeff • atomMatrix secondVec
        + thirdCoeff • atomMatrix thirdVec) *ᵥ probe)
      = firstCoeff * (firstVec ⬝ᵥ probe) ^ 2 + secondCoeff * (secondVec ⬝ᵥ probe) ^ 2
        + thirdCoeff * (thirdVec ⬝ᵥ probe) ^ 2 := by
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      atomMatrix_mulVec_eq_dot_smul, smul_eq_mul]
    rw [dotProduct_comm probe firstVec, dotProduct_comm probe secondVec,
      dotProduct_comm probe thirdVec]
    ring
  rw [hform]
  rcases eq_or_ne (firstVec ⬝ᵥ probe) 0 with hfirstZero | hfirstNe
  · rcases eq_or_ne (secondVec ⬝ᵥ probe) 0 with hsecondZero | hsecondNe
    · rcases eq_or_ne (thirdVec ⬝ᵥ probe) 0 with hthirdZero | hthirdNe
      · exact absurd (eq_zero_of_tripleBracket_ne_zero firstVec secondVec thirdVec probe
          hbracket hfirstZero hsecondZero hthirdZero) hprobe
      · have := sq_pos_of_ne_zero hthirdNe
        nlinarith [sq_nonneg (firstVec ⬝ᵥ probe), sq_nonneg (secondVec ⬝ᵥ probe)]
    · have := sq_pos_of_ne_zero hsecondNe
      nlinarith [sq_nonneg (firstVec ⬝ᵥ probe), sq_nonneg (thirdVec ⬝ᵥ probe)]
  · have := sq_pos_of_ne_zero hfirstNe
    nlinarith [sq_nonneg (secondVec ⬝ᵥ probe), sq_nonneg (thirdVec ⬝ᵥ probe)]

/-- **The inverse form of a spanning triple is a bracket sum.**  With
`Y = a A_u + b A_v + c A_x` invertible,

    `det Y · (y ⬝ᵥ Y⁻¹ y) = ab [u,v,y]² + ac [u,x,y]² + bc [v,x,y]²` .

No inverse survives on the right.  The matrix determinant lemma supplies the left side
and the four-atom bracket expansion supplies the right. -/
theorem det_mul_inverseForm_eq_bracket_sum (firstVec secondVec thirdVec probe : Fin 3 → ℝ)
    (firstCoeff secondCoeff thirdCoeff : ℝ)
    (hunit : IsUnit (firstCoeff • atomMatrix firstVec + secondCoeff • atomMatrix secondVec
      + thirdCoeff • atomMatrix thirdVec).det) :
    (firstCoeff • atomMatrix firstVec + secondCoeff • atomMatrix secondVec
        + thirdCoeff • atomMatrix thirdVec).det
        * (probe ⬝ᵥ ((firstCoeff • atomMatrix firstVec + secondCoeff • atomMatrix secondVec
            + thirdCoeff • atomMatrix thirdVec)⁻¹ *ᵥ probe))
      = firstCoeff * secondCoeff * tripleBracket firstVec secondVec probe ^ 2
        + firstCoeff * thirdCoeff * tripleBracket firstVec thirdVec probe ^ 2
        + secondCoeff * thirdCoeff * tripleBracket secondVec thirdVec probe ^ 2 := by
  have hlemma := det_add_atomMatrix hunit probe
  have hexpand : (firstCoeff • atomMatrix firstVec + secondCoeff • atomMatrix secondVec
        + thirdCoeff • atomMatrix thirdVec + atomMatrix probe).det
      = firstCoeff * secondCoeff * thirdCoeff
          * tripleBracket firstVec secondVec thirdVec ^ 2
        + firstCoeff * secondCoeff * tripleBracket firstVec secondVec probe ^ 2
        + firstCoeff * thirdCoeff * tripleBracket firstVec thirdVec probe ^ 2
        + secondCoeff * thirdCoeff * tripleBracket secondVec thirdVec probe ^ 2 := by
    have hone := det_smul_atomMatrix_four firstVec secondVec thirdVec probe
      firstCoeff secondCoeff thirdCoeff 1
    rw [one_smul] at hone
    rw [hone]; ring
  rw [hexpand, det_smul_atomMatrix_three] at hlemma
  rw [det_smul_atomMatrix_three]
  linear_combination -hlemma

/-! ## 4. The two-point marginal, in brackets -/

/-- **THE TWO-POINT MARGINAL IN BRACKETS.**  For every pair of labels of every
rank-three weighted design,

    `Σ_a t_a · [d, e, a]² = ⟨d, e⟩` .

Parseval against the cross product of the pair, then Lagrange.  No projection form, no
minor total, no cardinality hypothesis: the sum runs over ALL labels, and the two terms
inside the pair contribute nothing because a repeated slot kills the bracket. -/
theorem sum_weight_mul_sq_tripleBracket (design : WeightedDesign size 3)
    (leftLabel rightLabel : Fin size) :
    ∑ third, design.weight third
        * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
            (design.atom third) ^ 2
      = pairBracketSq (design.atom leftLabel) (design.atom rightLabel) := by
  have hrewrite : ∀ third : Fin size,
      design.weight third
          * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
              (design.atom third) ^ 2
        = design.weight third
          * (design.atom third
              ⬝ᵥ bracketNormal (design.atom leftLabel) (design.atom rightLabel)) ^ 2 := by
    intro third
    rw [tripleBracket_eq_bracketNormal_dotProduct, dotProduct_comm]
  rw [Finset.sum_congr rfl fun third _ => hrewrite third,
    sum_weight_mul_sq_dotProduct_probe design
      (bracketNormal (design.atom leftLabel) (design.atom rightLabel)),
    leverageOf_eq_dotProduct_self, pairBracketSq_eq_bracketNormal]

/-- **The swap mass of one slot.**  Deleting a label from a spanning triple and putting
each outside label in its place gives a fan of nine triples in all, three per slot, and
the mass of one fan is the pair Gram determinant less the triple's own share:

    `Σ_{a ∉ C} t_a [d, e, a]² = ⟨d, e⟩ − t_c [d, e, c]²` ,   `C = {c, d, e}` .

In particular the right side is NONNEGATIVE at every spanning triple. -/
theorem sum_compl_weight_mul_sq_tripleBracket (design : WeightedDesign size 3)
    (pivot leftLabel rightLabel : Fin size)
    (hpivotLeft : pivot ≠ leftLabel) (hpivotRight : pivot ≠ rightLabel)
    (hleftRight : leftLabel ≠ rightLabel) :
    ∑ third ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight third
        * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
            (design.atom third) ^ 2
      = pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
        - design.weight pivot
          * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
              (design.atom pivot) ^ 2 := by
  classical
  have hsplit := Finset.sum_add_sum_compl ({pivot, leftLabel, rightLabel} : Finset (Fin size))
    (fun third => design.weight third
      * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
          (design.atom third) ^ 2)
  have hinner : ∑ third ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size)),
      design.weight third
        * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
            (design.atom third) ^ 2
      = design.weight pivot
        * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
            (design.atom pivot) ^ 2 := by
    rw [Finset.sum_insert (by simp [hpivotLeft, hpivotRight]),
      Finset.sum_insert (by simp [hleftRight]), Finset.sum_singleton,
      tripleBracket_self_left, tripleBracket_self_right]
    ring
  rw [hinner, sum_weight_mul_sq_tripleBracket] at hsplit
  linarith [hsplit]

/-! ## 5. The budget in brackets -/

/-- The free-mass matrix of a triple, in the exact shape the certificate reads. -/
noncomputable def freeMassTriple (design : WeightedDesign size 3) (pivot leftLabel rightLabel :
    Fin size) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ d ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size)),
    (1 - design.weight d) • atomMatrix (design.atom d)

/-- The free-mass matrix, written out on three distinct labels. -/
theorem freeMassTriple_eq (design : WeightedDesign size 3) {pivot leftLabel rightLabel : Fin size}
    (hpivotLeft : pivot ≠ leftLabel) (hpivotRight : pivot ≠ rightLabel)
    (hleftRight : leftLabel ≠ rightLabel) :
    freeMassTriple design pivot leftLabel rightLabel
      = (1 - design.weight pivot) • atomMatrix (design.atom pivot)
        + (1 - design.weight leftLabel) • atomMatrix (design.atom leftLabel)
        + (1 - design.weight rightLabel) • atomMatrix (design.atom rightLabel) := by
  classical
  rw [freeMassTriple, Finset.sum_insert (by simp [hpivotLeft, hpivotRight]),
    Finset.sum_insert (by simp [hleftRight]), Finset.sum_singleton, add_assoc]

/-- Every weight is strictly below one at two labels or more, so every free-mass
coefficient is strictly positive. -/
theorem one_sub_weight_pos (design : WeightedDesign size 3) {first second : Fin size}
    (hne : first ≠ second) (label : Fin size) : 0 < 1 - design.weight label := by
  classical
  have hsub : design.weight first + design.weight second
      ≤ ∑ c, design.weight c := by
    have hpair : ({first, second} : Finset (Fin size)) ⊆ Finset.univ := Finset.subset_univ _
    have hsum : ∑ c ∈ ({first, second} : Finset (Fin size)), design.weight c
        = design.weight first + design.weight second := by
      rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpair
      fun c _ _ => (design.weight_pos c).le
  rcases eq_or_ne label first with rfl | hlabelFirst
  · have := design.weight_pos second
    rw [design.weight_sum_one] at hsub
    linarith
  · rcases eq_or_ne label second with rfl | hlabelSecond
    · have := design.weight_pos first
      rw [design.weight_sum_one] at hsub
      linarith
    · have htriple : design.weight label + design.weight first + design.weight second
          ≤ ∑ c, design.weight c := by
        have hsum : ∑ c ∈ ({label, first, second} : Finset (Fin size)), design.weight c
            = design.weight label + design.weight first + design.weight second := by
          rw [Finset.sum_insert (by simp [hlabelFirst, hlabelSecond]),
            Finset.sum_insert (by simp [hne]), Finset.sum_singleton, add_assoc]
        rw [← hsum]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun c _ _ => (design.weight_pos c).le
      have hfirst := design.weight_pos first
      have hsecond := design.weight_pos second
      rw [design.weight_sum_one] at htriple
      linarith

/-- The free-mass matrix of a spanning triple is positive definite. -/
theorem posDef_freeMassTriple (design : WeightedDesign size 3) {pivot leftLabel rightLabel :
    Fin size} (hpivotLeft : pivot ≠ leftLabel) (hpivotRight : pivot ≠ rightLabel)
    (hleftRight : leftLabel ≠ rightLabel)
    (hbracket : tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ≠ 0) :
    (freeMassTriple design pivot leftLabel rightLabel).PosDef := by
  rw [freeMassTriple_eq design hpivotLeft hpivotRight hleftRight]
  exact posDef_smul_atomMatrix_three _ _ _
    (one_sub_weight_pos design hpivotLeft pivot)
    (one_sub_weight_pos design hpivotLeft leftLabel)
    (one_sub_weight_pos design hpivotLeft rightLabel) hbracket

/-- The determinant of the free-mass matrix of a spanning triple. -/
theorem det_freeMassTriple (design : WeightedDesign size 3) {pivot leftLabel rightLabel : Fin size}
    (hpivotLeft : pivot ≠ leftLabel) (hpivotRight : pivot ≠ rightLabel)
    (hleftRight : leftLabel ≠ rightLabel) :
    (freeMassTriple design pivot leftLabel rightLabel).det
      = (1 - design.weight pivot) * (1 - design.weight leftLabel)
        * (1 - design.weight rightLabel)
        * tripleBracket (design.atom pivot) (design.atom leftLabel)
            (design.atom rightLabel) ^ 2 := by
  rw [freeMassTriple_eq design hpivotLeft hpivotRight hleftRight, det_smul_atomMatrix_three]

/-- **The inverse form at one label, in brackets.**  The whole content of the free-mass
metric, with the inverse removed. -/
theorem det_freeMassTriple_mul_inverseForm (design : WeightedDesign size 3)
    {pivot leftLabel rightLabel : Fin size} (hpivotLeft : pivot ≠ leftLabel)
    (hpivotRight : pivot ≠ rightLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hbracket : tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ≠ 0) (probeLabel : Fin size) :
    (freeMassTriple design pivot leftLabel rightLabel).det
        * (design.atom probeLabel
            ⬝ᵥ ((freeMassTriple design pivot leftLabel rightLabel)⁻¹ *ᵥ design.atom probeLabel))
      = (1 - design.weight pivot) * (1 - design.weight leftLabel)
          * tripleBracket (design.atom pivot) (design.atom leftLabel)
              (design.atom probeLabel) ^ 2
        + (1 - design.weight pivot) * (1 - design.weight rightLabel)
          * tripleBracket (design.atom pivot) (design.atom rightLabel)
              (design.atom probeLabel) ^ 2
        + (1 - design.weight leftLabel) * (1 - design.weight rightLabel)
          * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
              (design.atom probeLabel) ^ 2 := by
  have hunit : IsUnit (freeMassTriple design pivot leftLabel rightLabel).det :=
    isUnit_iff_ne_zero.mpr
      (posDef_freeMassTriple design hpivotLeft hpivotRight hleftRight hbracket).det_pos.ne'
  rw [freeMassTriple_eq design hpivotLeft hpivotRight hleftRight] at hunit ⊢
  exact det_mul_inverseForm_eq_bracket_sum _ _ _ _ _ _ _ hunit

/-! ## 6. The budget itself -/

/-- **THE SWAP MASS OF A TRIPLE.**  The three pair Gram determinants of the triple, each
against the triple's own bracket, each discounted by its opposite label's free weight.
Form (II) of the header, cleared of the bracket denominator. -/
noncomputable def pairSwapMass (design : WeightedDesign size 3)
    (pivot leftLabel rightLabel : Fin size) : ℝ :=
  (pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
      - design.weight pivot
        * tripleBracket (design.atom pivot) (design.atom leftLabel)
            (design.atom rightLabel) ^ 2) / (1 - design.weight pivot)
  + (pairBracketSq (design.atom pivot) (design.atom rightLabel)
      - design.weight leftLabel
        * tripleBracket (design.atom pivot) (design.atom leftLabel)
            (design.atom rightLabel) ^ 2) / (1 - design.weight leftLabel)
  + (pairBracketSq (design.atom pivot) (design.atom leftLabel)
      - design.weight rightLabel
        * tripleBracket (design.atom pivot) (design.atom leftLabel)
            (design.atom rightLabel) ^ 2) / (1 - design.weight rightLabel)

/-- **Each numerator of the swap mass is a mass.**  It is the weighted total of the three
brackets obtained by exchanging one label of the triple for an outside label, so it is
nonnegative at every triple of every design. -/
theorem tripleSwapMass_nonneg (design : WeightedDesign size 3)
    {pivot leftLabel rightLabel : Fin size} (hpivotLeft : pivot ≠ leftLabel)
    (hpivotRight : pivot ≠ rightLabel) (hleftRight : leftLabel ≠ rightLabel) :
    0 ≤ pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
      - design.weight pivot
        * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
            (design.atom pivot) ^ 2 := by
  rw [← sum_compl_weight_mul_sq_tripleBracket design pivot leftLabel rightLabel
    hpivotLeft hpivotRight hleftRight]
  exact Finset.sum_nonneg fun third _ =>
    mul_nonneg (design.weight_pos third).le (sq_nonneg _)

/-- **THE BUDGET IS THE SWAP MASS.**  For every spanning triple of every rank-three
weighted design, the free-mass budget of `Gtz.posDef_gap_of_freeMassBudget` equals the
swap mass divided by the triple's squared bracket.  An identity: no inequality, no
hypothesis beyond spanning. -/
theorem freeMassBudget_eq_pairSwapMass (design : WeightedDesign size 3)
    {pivot leftLabel rightLabel : Fin size} (hpivotLeft : pivot ≠ leftLabel)
    (hpivotRight : pivot ≠ rightLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hbracket : tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ≠ 0) :
    ∑ c ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight c
        * (design.atom c
            ⬝ᵥ ((∑ d ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size)),
                (1 - design.weight d) • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c))
      = pairSwapMass design pivot leftLabel rightLabel
        / tripleBracket (design.atom pivot) (design.atom leftLabel)
            (design.atom rightLabel) ^ 2 := by
  classical
  show ∑ c ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight c
      * (design.atom c
          ⬝ᵥ ((freeMassTriple design pivot leftLabel rightLabel)⁻¹ *ᵥ design.atom c)) = _
  set freeMass := freeMassTriple design pivot leftLabel rightLabel with hfreeMass
  set bracket := tripleBracket (design.atom pivot) (design.atom leftLabel)
    (design.atom rightLabel) with hbracketDef
  have hpivotPos := one_sub_weight_pos design hpivotLeft pivot
  have hleftPos := one_sub_weight_pos design hpivotLeft leftLabel
  have hrightPos := one_sub_weight_pos design hpivotLeft rightLabel
  have hbracketSq : 0 < bracket ^ 2 := by positivity
  have hdet : freeMass.det
      = (1 - design.weight pivot) * (1 - design.weight leftLabel)
        * (1 - design.weight rightLabel) * bracket ^ 2 :=
    det_freeMassTriple design hpivotLeft hpivotRight hleftRight
  have hdetPos : 0 < freeMass.det := by rw [hdet]; positivity
  -- the inverse form of one label, scaled by the determinant
  have hform : ∀ probeLabel : Fin size, freeMass.det
      * (design.atom probeLabel ⬝ᵥ (freeMass⁻¹ *ᵥ design.atom probeLabel))
      = (1 - design.weight pivot) * (1 - design.weight leftLabel)
          * tripleBracket (design.atom pivot) (design.atom leftLabel)
              (design.atom probeLabel) ^ 2
        + (1 - design.weight pivot) * (1 - design.weight rightLabel)
          * tripleBracket (design.atom pivot) (design.atom rightLabel)
              (design.atom probeLabel) ^ 2
        + (1 - design.weight leftLabel) * (1 - design.weight rightLabel)
          * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
              (design.atom probeLabel) ^ 2 := fun probeLabel =>
    det_freeMassTriple_mul_inverseForm design hpivotLeft hpivotRight hleftRight hbracket
      probeLabel
  -- sum the scaled form over the complement
  have hsum : freeMass.det
      * ∑ c ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight c
          * (design.atom c ⬝ᵥ (freeMass⁻¹ *ᵥ design.atom c))
      = (1 - design.weight pivot) * (1 - design.weight leftLabel)
          * ∑ c ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight c
              * tripleBracket (design.atom pivot) (design.atom leftLabel)
                  (design.atom c) ^ 2
        + (1 - design.weight pivot) * (1 - design.weight rightLabel)
          * ∑ c ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight c
              * tripleBracket (design.atom pivot) (design.atom rightLabel)
                  (design.atom c) ^ 2
        + (1 - design.weight leftLabel) * (1 - design.weight rightLabel)
          * ∑ c ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight c
              * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
                  (design.atom c) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    linear_combination design.weight c * hform c
  -- the three fans
  have hfanOne : ∑ c ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight c
        * tripleBracket (design.atom pivot) (design.atom leftLabel) (design.atom c) ^ 2
      = pairBracketSq (design.atom pivot) (design.atom leftLabel)
        - design.weight rightLabel * bracket ^ 2 := by
    have hbase := sum_compl_weight_mul_sq_tripleBracket design rightLabel pivot leftLabel
      (Ne.symm hpivotRight) (Ne.symm hleftRight) hpivotLeft
    have hset : ({rightLabel, pivot, leftLabel} : Finset (Fin size))
        = ({pivot, leftLabel, rightLabel} : Finset (Fin size)) := by
      ext label; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hset] at hbase
    rw [hbase, hbracketDef, tripleBracket_cycle]
  have hfanTwo : ∑ c ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight c
        * tripleBracket (design.atom pivot) (design.atom rightLabel) (design.atom c) ^ 2
      = pairBracketSq (design.atom pivot) (design.atom rightLabel)
        - design.weight leftLabel * bracket ^ 2 := by
    have hbase := sum_compl_weight_mul_sq_tripleBracket design leftLabel pivot rightLabel
      (Ne.symm hpivotLeft) hleftRight hpivotRight
    have hset : ({leftLabel, pivot, rightLabel} : Finset (Fin size))
        = ({pivot, leftLabel, rightLabel} : Finset (Fin size)) := by
      ext label; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hset] at hbase
    rw [hbase, hbracketDef]
    have hsign : tripleBracket (design.atom pivot) (design.atom rightLabel)
        (design.atom leftLabel)
        = -tripleBracket (design.atom pivot) (design.atom leftLabel) (design.atom rightLabel) := by
      rw [← tripleBracket_cycle, tripleBracket_swap_left, tripleBracket_cycle]
    rw [hsign]; ring
  have hfanThree : ∑ c ∈ ({pivot, leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight c
        * tripleBracket (design.atom leftLabel) (design.atom rightLabel) (design.atom c) ^ 2
      = pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
        - design.weight pivot * bracket ^ 2 := by
    have hbase := sum_compl_weight_mul_sq_tripleBracket design pivot leftLabel rightLabel
      hpivotLeft hpivotRight hleftRight
    rw [hbase, hbracketDef, tripleBracket_cycle]
  rw [hfanOne, hfanTwo, hfanThree, hdet] at hsum
  have hpivotNe : (1 - design.weight pivot) ≠ 0 := ne_of_gt hpivotPos
  have hleftNe : (1 - design.weight leftLabel) ≠ 0 := ne_of_gt hleftPos
  have hrightNe : (1 - design.weight rightLabel) ≠ 0 := ne_of_gt hrightPos
  rw [eq_div_iff hbracketSq.ne', pairSwapMass, ← hbracketDef]
  field_simp
  linear_combination hsum

/-! ## 7. The domination test, and the certificate-free reading -/

/-- **THE BRACKET DOMINATION TEST.**  A spanning triple whose swap mass is below its own
squared bracket dominates STRICTLY.  Equivalent to the free-mass certificate, not
weaker: the budget identity is an equality. -/
theorem posDef_gap_of_pairSwapMass_lt (design : WeightedDesign size 3)
    {pivot leftLabel rightLabel : Fin size} (hpivotLeft : pivot ≠ leftLabel)
    (hpivotRight : pivot ≠ rightLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hbracket : tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ≠ 0)
    (hswap : pairSwapMass design pivot leftLabel rightLabel
      < tripleBracket (design.atom pivot) (design.atom leftLabel)
          (design.atom rightLabel) ^ 2) :
    (subsetSum design ({pivot, leftLabel, rightLabel} : Finset (Fin size)) - 1).PosDef := by
  have hbracketSq : 0 < tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ^ 2 := by positivity
  refine posDef_gap_of_freeMassBudget design _
    (posDef_freeMassTriple design hpivotLeft hpivotRight hleftRight hbracket) ?_
  rw [freeMassBudget_eq_pairSwapMass design hpivotLeft hpivotRight hleftRight hbracket,
    div_lt_one hbracketSq]
  exact hswap

/-- **THE CERTIFICATE-FREE HYPOTHESIS, SPENT.**  If no triple of the design carries a
strict certificate then EVERY spanning triple has swap mass at least its squared
bracket.  This is the free-mass half of the hypothesis of `Gtz.NoStressResidual`, in
coordinates that carry no inverse, no eigenvalue and no matrix. -/
theorem le_pairSwapMass_of_not_hasStrictCertificate (design : WeightedDesign size 3)
    {pivot leftLabel rightLabel : Fin size} (hpivotLeft : pivot ≠ leftLabel)
    (hpivotRight : pivot ≠ rightLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hbracket : tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ≠ 0)
    (hfree : ∀ selected : Finset (Fin size), selected.card = 3 →
      ¬ HasStrictCertificate design selected) :
    tripleBracket (design.atom pivot) (design.atom leftLabel) (design.atom rightLabel) ^ 2
      ≤ pairSwapMass design pivot leftLabel rightLabel := by
  classical
  by_contra hlt
  push_neg at hlt
  have hcard : ({pivot, leftLabel, rightLabel} : Finset (Fin size)).card = 3 :=
    Finset.card_eq_three.mpr ⟨pivot, leftLabel, rightLabel, hpivotLeft, hpivotRight,
      hleftRight, rfl⟩
  refine hfree _ hcard (Or.inr ⟨posDef_freeMassTriple design hpivotLeft hpivotRight
    hleftRight hbracket, ?_⟩)
  have hbracketSq : 0 < tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ^ 2 := by positivity
  rw [freeMassBudget_eq_pairSwapMass design hpivotLeft hpivotRight hleftRight hbracket,
    div_lt_one hbracketSq]
  exact hlt

/-- **THE WEIGHT-FREE COROLLARY.**  A spanning triple whose three pair Gram determinants
total less than its squared bracket dominates strictly, whatever the weights are.  The
swap mass is a weighted average of the three pair determinants against the bracket, and
under this hypothesis every one of them is already below the bracket. -/
theorem posDef_gap_of_sum_pairBracketSq_lt (design : WeightedDesign size 3)
    {pivot leftLabel rightLabel : Fin size} (hpivotLeft : pivot ≠ leftLabel)
    (hpivotRight : pivot ≠ rightLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hbracket : tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ≠ 0)
    (htotal : pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
        + pairBracketSq (design.atom pivot) (design.atom rightLabel)
        + pairBracketSq (design.atom pivot) (design.atom leftLabel)
      < tripleBracket (design.atom pivot) (design.atom leftLabel)
          (design.atom rightLabel) ^ 2) :
    (subsetSum design ({pivot, leftLabel, rightLabel} : Finset (Fin size)) - 1).PosDef := by
  refine posDef_gap_of_pairSwapMass_lt design hpivotLeft hpivotRight hleftRight hbracket ?_
  have hpivotPos := one_sub_weight_pos design hpivotLeft pivot
  have hleftPos := one_sub_weight_pos design hpivotLeft leftLabel
  have hrightPos := one_sub_weight_pos design hpivotLeft rightLabel
  have hsq := sq_nonneg (tripleBracket (design.atom pivot) (design.atom leftLabel)
    (design.atom rightLabel))
  have hone := pairBracketSq_nonneg (design.atom leftLabel) (design.atom rightLabel)
  have htwo := pairBracketSq_nonneg (design.atom pivot) (design.atom rightLabel)
  have hthree := pairBracketSq_nonneg (design.atom pivot) (design.atom leftLabel)
  -- each term of the swap mass sits below its own pair determinant
  have hbound : ∀ pairValue weightValue : ℝ, 0 ≤ pairValue → 0 < 1 - weightValue →
      0 < weightValue →
      pairValue ≤ tripleBracket (design.atom pivot) (design.atom leftLabel)
        (design.atom rightLabel) ^ 2 →
      (pairValue - weightValue * tripleBracket (design.atom pivot) (design.atom leftLabel)
        (design.atom rightLabel) ^ 2) / (1 - weightValue) ≤ pairValue := by
    intro pairValue weightValue hpairNonneg hfreePos hweightPos hpairLe
    rw [div_le_iff₀ hfreePos]
    nlinarith [hpairLe, hweightPos]
  rw [pairSwapMass]
  have hboundOne := hbound _ (design.weight pivot) hone hpivotPos (design.weight_pos pivot)
    (by linarith)
  have hboundTwo := hbound _ (design.weight leftLabel) htwo hleftPos
    (design.weight_pos leftLabel) (by linarith)
  have hboundThree := hbound _ (design.weight rightLabel) hthree hrightPos
    (design.weight_pos rightLabel) (by linarith)
  linarith [hboundOne, hboundTwo, hboundThree]

/-- **The weight-free necessary condition on the certificate-free stratum.**  Read the
last corollary against `Gtz.NoStressResidual`'s hypothesis: at a certificate-free design
every spanning triple's three pair Gram determinants total AT LEAST its squared bracket.
Only atom directions and lengths enter — the weights have left the statement. -/
theorem sq_tripleBracket_le_sum_pairBracketSq_of_not_hasStrictCertificate
    (design : WeightedDesign size 3) {pivot leftLabel rightLabel : Fin size}
    (hpivotLeft : pivot ≠ leftLabel) (hpivotRight : pivot ≠ rightLabel)
    (hleftRight : leftLabel ≠ rightLabel)
    (hbracket : tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ≠ 0)
    (hfree : ∀ selected : Finset (Fin size), selected.card = 3 →
      ¬ HasStrictCertificate design selected) :
    tripleBracket (design.atom pivot) (design.atom leftLabel) (design.atom rightLabel) ^ 2
      ≤ pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
        + pairBracketSq (design.atom pivot) (design.atom rightLabel)
        + pairBracketSq (design.atom pivot) (design.atom leftLabel) := by
  classical
  by_contra hlt
  push_neg at hlt
  have hcard : ({pivot, leftLabel, rightLabel} : Finset (Fin size)).card = 3 :=
    Finset.card_eq_three.mpr ⟨pivot, leftLabel, rightLabel, hpivotLeft, hpivotRight,
      hleftRight, rfl⟩
  have hposDef := posDef_gap_of_sum_pairBracketSq_lt design hpivotLeft hpivotRight
    hleftRight hbracket hlt
  refine hfree _ hcard (Or.inr ⟨posDef_freeMassTriple design hpivotLeft hpivotRight
    hleftRight hbracket, ?_⟩)
  have hbracketSq : 0 < tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ^ 2 := by positivity
  have hswap : pairSwapMass design pivot leftLabel rightLabel
      < tripleBracket (design.atom pivot) (design.atom leftLabel)
          (design.atom rightLabel) ^ 2 := by
    have hpivotPos := one_sub_weight_pos design hpivotLeft pivot
    have hleftPos := one_sub_weight_pos design hpivotLeft leftLabel
    have hrightPos := one_sub_weight_pos design hpivotLeft rightLabel
    have hone := pairBracketSq_nonneg (design.atom leftLabel) (design.atom rightLabel)
    have htwo := pairBracketSq_nonneg (design.atom pivot) (design.atom rightLabel)
    have hthree := pairBracketSq_nonneg (design.atom pivot) (design.atom leftLabel)
    have hbound : ∀ pairValue weightValue : ℝ, 0 ≤ pairValue → 0 < 1 - weightValue →
        0 < weightValue →
        pairValue ≤ tripleBracket (design.atom pivot) (design.atom leftLabel)
          (design.atom rightLabel) ^ 2 →
        (pairValue - weightValue * tripleBracket (design.atom pivot) (design.atom leftLabel)
          (design.atom rightLabel) ^ 2) / (1 - weightValue) ≤ pairValue := by
      intro pairValue weightValue hpairNonneg hfreePos hweightPos hpairLe
      rw [div_le_iff₀ hfreePos]
      nlinarith [hpairLe, hweightPos]
    rw [pairSwapMass]
    have hboundOne := hbound _ (design.weight pivot) hone hpivotPos (design.weight_pos pivot)
      (by linarith)
    have hboundTwo := hbound _ (design.weight leftLabel) htwo hleftPos
      (design.weight_pos leftLabel) (by linarith)
    have hboundThree := hbound _ (design.weight rightLabel) hthree hrightPos
      (design.weight_pos rightLabel) (by linarith)
    linarith [hboundOne, hboundTwo, hboundThree]
  rw [freeMassBudget_eq_pairSwapMass design hpivotLeft hpivotRight hleftRight hbracket,
    div_lt_one hbracketSq]
  exact hswap

/-! ## 8. The root design, in kernel

`Gtz.coordinateDiagonalDesign` is the campaign's certificate-free calibration object: the
six coordinate-plane diagonals at the uniform weight, which are the six edge directions
of a regular tetrahedron and therefore the six edge vectors of `K4`.  The audit records
its two free-mass budget values, `6/5` at a vertex star and `7/5` off it, as MEASURED.
The bracket form makes them arithmetic. -/

/-- Every atom of the root design is its pattern at the common scale. -/
theorem coordinateDiagonalDesign_atom_apply (atomLabel : Fin 6) (coord : Fin 3) :
    coordinateDiagonalDesign.atom atomLabel coord
      = diagonalScale * diagonalPattern atomLabel coord := rfl

/-- The squared scale. -/
theorem diagonalScale_pow_two : diagonalScale ^ 2 = 3 / 2 := by
  rw [pow_two]; exact diagonalScale_sq

/-- The sixth power of the scale, which is what a squared bracket reads. -/
theorem diagonalScale_pow_six : diagonalScale ^ 6 = 27 / 8 := by
  calc diagonalScale ^ 6 = (diagonalScale ^ 2) ^ 3 := by ring
    _ = 27 / 8 := by rw [diagonalScale_pow_two]; norm_num

/-- Pairings of the root design are the pattern pairings, at the squared scale. -/
theorem coordinateDiagonalDesign_dotProduct (firstLabel secondLabel : Fin 6) :
    coordinateDiagonalDesign.atom firstLabel ⬝ᵥ coordinateDiagonalDesign.atom secondLabel
      = 3 / 2 * (diagonalPattern firstLabel ⬝ᵥ diagonalPattern secondLabel) := by
  simp only [dotProduct, Fin.sum_univ_three, coordinateDiagonalDesign_atom_apply]
  linear_combination (diagonalPattern firstLabel 0 * diagonalPattern secondLabel 0
    + diagonalPattern firstLabel 1 * diagonalPattern secondLabel 1
    + diagonalPattern firstLabel 2 * diagonalPattern secondLabel 2) * diagonalScale_sq

/-- Brackets of the root design are the pattern brackets at the sixth power of the
scale — a rational number. -/
theorem coordinateDiagonalDesign_sq_tripleBracket (firstLabel secondLabel thirdLabel : Fin 6) :
    tripleBracket (coordinateDiagonalDesign.atom firstLabel)
        (coordinateDiagonalDesign.atom secondLabel)
        (coordinateDiagonalDesign.atom thirdLabel) ^ 2
      = 27 / 8 * tripleBracket (diagonalPattern firstLabel) (diagonalPattern secondLabel)
          (diagonalPattern thirdLabel) ^ 2 := by
  have hfactor : tripleBracket (coordinateDiagonalDesign.atom firstLabel)
      (coordinateDiagonalDesign.atom secondLabel) (coordinateDiagonalDesign.atom thirdLabel)
      = diagonalScale ^ 3 * tripleBracket (diagonalPattern firstLabel)
          (diagonalPattern secondLabel) (diagonalPattern thirdLabel) := by
    simp only [tripleBracket_eq, coordinateDiagonalDesign_atom_apply]; ring
  rw [hfactor, mul_pow, ← pow_mul]
  norm_num [diagonalScale_pow_six]

/-- The pair Gram determinant of the root design, from the pattern pairings alone. -/
theorem coordinateDiagonalDesign_pairBracketSq (firstLabel secondLabel : Fin 6) :
    pairBracketSq (coordinateDiagonalDesign.atom firstLabel)
        (coordinateDiagonalDesign.atom secondLabel)
      = 3 / 2 * (diagonalPattern firstLabel ⬝ᵥ diagonalPattern firstLabel)
          * (3 / 2 * (diagonalPattern secondLabel ⬝ᵥ diagonalPattern secondLabel))
        - (3 / 2 * (diagonalPattern firstLabel ⬝ᵥ diagonalPattern secondLabel)) ^ 2 := by
  rw [pairBracketSq, leverageOf_eq_dotProduct_self, leverageOf_eq_dotProduct_self,
    coordinateDiagonalDesign_dotProduct, coordinateDiagonalDesign_dotProduct,
    coordinateDiagonalDesign_dotProduct]

/-- Every weight of the root design is `1/6`. -/
theorem coordinateDiagonalDesign_weight_apply (atomLabel : Fin 6) :
    coordinateDiagonalDesign.weight atomLabel = 1 / 6 := rfl

/-- **THE STAR.**  At the vertex star `{0, 2, 4}` — three diagonals no two of which are
orthogonal — the swap mass is `6/5` of the squared bracket. -/
theorem pairSwapMass_coordinateDiagonalDesign_star :
    pairSwapMass coordinateDiagonalDesign 0 2 4
      = 6 / 5 * tripleBracket (coordinateDiagonalDesign.atom 0)
          (coordinateDiagonalDesign.atom 2) (coordinateDiagonalDesign.atom 4) ^ 2 := by
  rw [pairSwapMass, coordinateDiagonalDesign_sq_tripleBracket,
    coordinateDiagonalDesign_pairBracketSq, coordinateDiagonalDesign_pairBracketSq,
    coordinateDiagonalDesign_pairBracketSq, coordinateDiagonalDesign_weight_apply,
    coordinateDiagonalDesign_weight_apply, coordinateDiagonalDesign_weight_apply]
  simp only [diagonalPattern_zero, diagonalPattern_two, diagonalPattern_four, tripleBracket_eq,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- **OFF THE STAR.**  At `{0, 1, 2}` — a triple with exactly one orthogonal pair — the
swap mass is `7/5` of the squared bracket.  One orthogonal pair costs exactly `1/5`. -/
theorem pairSwapMass_coordinateDiagonalDesign_offStar :
    pairSwapMass coordinateDiagonalDesign 0 1 2
      = 7 / 5 * tripleBracket (coordinateDiagonalDesign.atom 0)
          (coordinateDiagonalDesign.atom 1) (coordinateDiagonalDesign.atom 2) ^ 2 := by
  rw [pairSwapMass, coordinateDiagonalDesign_sq_tripleBracket,
    coordinateDiagonalDesign_pairBracketSq, coordinateDiagonalDesign_pairBracketSq,
    coordinateDiagonalDesign_pairBracketSq, coordinateDiagonalDesign_weight_apply,
    coordinateDiagonalDesign_weight_apply, coordinateDiagonalDesign_weight_apply]
  simp only [diagonalPattern_zero, diagonalPattern_one, diagonalPattern_two, tripleBracket_eq,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- The star of the root design spans. -/
theorem coordinateDiagonalDesign_tripleBracket_star_ne_zero :
    tripleBracket (coordinateDiagonalDesign.atom 0) (coordinateDiagonalDesign.atom 2)
      (coordinateDiagonalDesign.atom 4) ≠ 0 := by
  intro hzero
  have hsq : tripleBracket (coordinateDiagonalDesign.atom 0) (coordinateDiagonalDesign.atom 2)
      (coordinateDiagonalDesign.atom 4) ^ 2 = 27 / 2 := by
    rw [coordinateDiagonalDesign_sq_tripleBracket]
    simp only [diagonalPattern_zero, diagonalPattern_two, diagonalPattern_four, tripleBracket_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    norm_num
  rw [hzero] at hsq
  norm_num at hsq

/-- The off-star triple of the root design spans. -/
theorem coordinateDiagonalDesign_tripleBracket_offStar_ne_zero :
    tripleBracket (coordinateDiagonalDesign.atom 0) (coordinateDiagonalDesign.atom 1)
      (coordinateDiagonalDesign.atom 2) ≠ 0 := by
  intro hzero
  have hsq : tripleBracket (coordinateDiagonalDesign.atom 0) (coordinateDiagonalDesign.atom 1)
      (coordinateDiagonalDesign.atom 2) ^ 2 = 27 / 2 := by
    rw [coordinateDiagonalDesign_sq_tripleBracket]
    simp only [diagonalPattern_zero, diagonalPattern_one, diagonalPattern_two, tripleBracket_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    norm_num
  rw [hzero] at hsq
  norm_num at hsq

/-- **THE MEASURED CONSTANT, IN KERNEL.**  The free-mass budget of the vertex star of the
root design is exactly `6/5`.  The audit records this number as a measurement. -/
theorem freeMassBudget_coordinateDiagonalDesign_star :
    ∑ c ∈ ({0, 2, 4} : Finset (Fin 6))ᶜ, coordinateDiagonalDesign.weight c
        * (coordinateDiagonalDesign.atom c
            ⬝ᵥ ((∑ d ∈ ({0, 2, 4} : Finset (Fin 6)),
                (1 - coordinateDiagonalDesign.weight d)
                  • atomMatrix (coordinateDiagonalDesign.atom d))⁻¹
              *ᵥ coordinateDiagonalDesign.atom c))
      = 6 / 5 := by
  have hbracket := coordinateDiagonalDesign_tripleBracket_star_ne_zero
  have hsq : (0 : ℝ) < tripleBracket (coordinateDiagonalDesign.atom 0)
      (coordinateDiagonalDesign.atom 2) (coordinateDiagonalDesign.atom 4) ^ 2 := by positivity
  rw [freeMassBudget_eq_pairSwapMass coordinateDiagonalDesign (by decide) (by decide) (by decide)
      hbracket, pairSwapMass_coordinateDiagonalDesign_star, mul_div_assoc,
    div_self hsq.ne', mul_one]

/-- **THE SECOND MEASURED CONSTANT, IN KERNEL.**  Off the star the budget is `7/5`. -/
theorem freeMassBudget_coordinateDiagonalDesign_offStar :
    ∑ c ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ, coordinateDiagonalDesign.weight c
        * (coordinateDiagonalDesign.atom c
            ⬝ᵥ ((∑ d ∈ ({0, 1, 2} : Finset (Fin 6)),
                (1 - coordinateDiagonalDesign.weight d)
                  • atomMatrix (coordinateDiagonalDesign.atom d))⁻¹
              *ᵥ coordinateDiagonalDesign.atom c))
      = 7 / 5 := by
  have hbracket := coordinateDiagonalDesign_tripleBracket_offStar_ne_zero
  have hsq : (0 : ℝ) < tripleBracket (coordinateDiagonalDesign.atom 0)
      (coordinateDiagonalDesign.atom 1) (coordinateDiagonalDesign.atom 2) ^ 2 := by positivity
  rw [freeMassBudget_eq_pairSwapMass coordinateDiagonalDesign (by decide) (by decide) (by decide)
      hbracket, pairSwapMass_coordinateDiagonalDesign_offStar, mul_div_assoc,
    div_self hsq.ne', mul_one]

/-- **THE HYPOTHESIS OF THE RESIDUAL IS INHABITED, BY ARITHMETIC.**  Neither the star nor
the off-star triple of the root design carries the free-mass certificate, because `6/5`
and `7/5` are both at least one.  No measurement enters. -/
theorem one_le_freeMassBudget_coordinateDiagonalDesign_star :
    (1 : ℝ) ≤ ∑ c ∈ ({0, 2, 4} : Finset (Fin 6))ᶜ, coordinateDiagonalDesign.weight c
        * (coordinateDiagonalDesign.atom c
            ⬝ᵥ ((∑ d ∈ ({0, 2, 4} : Finset (Fin 6)),
                (1 - coordinateDiagonalDesign.weight d)
                  • atomMatrix (coordinateDiagonalDesign.atom d))⁻¹
              *ᵥ coordinateDiagonalDesign.atom c)) := by
  rw [freeMassBudget_coordinateDiagonalDesign_star]; norm_num

/-- The same off the star. -/
theorem one_le_freeMassBudget_coordinateDiagonalDesign_offStar :
    (1 : ℝ) ≤ ∑ c ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ, coordinateDiagonalDesign.weight c
        * (coordinateDiagonalDesign.atom c
            ⬝ᵥ ((∑ d ∈ ({0, 1, 2} : Finset (Fin 6)),
                (1 - coordinateDiagonalDesign.weight d)
                  • atomMatrix (coordinateDiagonalDesign.atom d))⁻¹
              *ᵥ coordinateDiagonalDesign.atom c)) := by
  rw [freeMassBudget_coordinateDiagonalDesign_offStar]; norm_num

end Gtz
