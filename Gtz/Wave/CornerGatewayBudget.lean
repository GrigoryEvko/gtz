/-
# The pair minor budget of a weighted triple, and the gateway producers

The corank-two arm needs one existence fact: a corner carries an ADMISSIBLE
outside pair, a pair whose `Gtz.pairGapMinor` is positive.  It is the edge the
tie-graph argument needs before an extremal bound can bite, and both horns are
blocked on it.  `Gtz.exists_offDiag_pairMinor_pos` produces an admissible pair
SOMEWHERE in the design; a corner needs one whose two atoms both sit OUTSIDE the
dominator, because the corner's three inside pair minors are exactly zero.

This module supplies producers for that, from two new exact laws.

## 1. The pair minor budget of a weighted triple

Three vectors, three scalars, NO hypothesis whatever -- not Parseval, not a
design, not a corner.  Writing `x_i = l_i - 1` for the leverage excess,
`T = t1+t2+t3` and `S = t1*x1 + t2*x2 + t3*x3` for the weighted excess:

  **`sum_{i<j} t_i t_j (1 + q_ij)
      = (1 - T)*(S - 1) + sum_i t_i^2 * x_i
        + t1*t2*t3*[g1 g2 g3]^2 + det(1 - sum_i t_i A_i)`**

(`Gtz.weightedTriple_pairMinor_identity`).  It is the landed
`Gtz.det_one_sub_weighted_triple` read in the pair minor rather than the wedge:
the wedge is the pair minor shifted by the two leverages, and that shift is
exactly what turns a determinant formula into a budget.  One `ring`.

At a design the four right-hand terms acquire meaning.  Parseval makes `1 - T`
the weight of the complementary atoms and `S - 1` one less the complement's
excess share, and it makes the last term the determinant of the complementary
moment, which is positive semidefinite and so contributes nothing negative
(`Gtz.det_complementTriple_nonneg`).  The bracket term is a square.

## 2. The producers

Every term on the right except the first is manifestly nonnegative, so when the
plain weight combination `sum_{i<j} t_i t_j` falls BELOW what the right side
already commits to, some `1 + q_ij` must pass one and some pair minor is
positive.  Two forms:

* `Gtz.exists_pairMinor_pos_of_weightBudget` -- six numbers decide it, the three
  weights and the three leverages.  No matrix, no bracket.
* `Gtz.exists_pairMinor_pos_of_bracketBudget` -- the same with the squared
  bracket retained, strictly stronger, and the form that survives the extremal
  ray where one outside atom carries almost all the excess on almost no weight.

[MEASURED on 181249 exact random corners carrying three heavy outside atoms: the
weight producer fires at 99.6546 percent of them and the bracket producer at
99.9691 percent, and neither ever fires where all three outside pair minors are
nonpositive.  Together with the landed
`Gtz.pairGapMinor_pos_of_normalizedExcess` the cover is 100.0000 percent with
zero exceptions, and no corner sampled violated the gateway.  The joint cover is
a MEASUREMENT, not a theorem: each producer below is an unconditional
implication, but their disjunction is not proved exhaustive.  A witness shows
why the scalar relaxation cannot prove it: at `t = (0.00035, 0.473, 0.497)` with
normalised excesses `(0.96, 0.04, 0.04)` every weight-level consequence of
inadmissibility holds while the weight budget is `+0.215`, and only the bracket
term, worth `0.2245` there, removes the point.]

## 3. The currency bridge

The arm writes refusals in the gap determinant and admissibility in the pair
minor, and the hinge speaks in brackets.  One hypothesis-free identity converts
between all three (`Gtz.sq_tripleBracket_eq_gapDet_add_pairMinors`):

  **`[g1 g2 g3]^2 = tripleGapDet + (q12 + q13 + q23) + (x1 + x2 + x3) + 1`** .

The squared bracket is the gap determinant plus the pair minors plus the
leverage excesses plus one -- the characteristic polynomial of the Gram read at
one, with every coefficient a campaign currency.

## 4. The complementary adjugate law

A second exact law, general to every real `3x3` matrix
(`Gtz.adjugate_sub_adjugate_one_sub`):

  **`adj(A) - adj(1 - A) = (tr A - 1) * 1 - A`** .

Pure Cayley-Hamilton -- no design, no symmetry, no invertibility.  Read at a
design's split into a triple and its complement it says the two complementary
moments carry the same adjugate up to an affine term, which is the `Lambda^2`
shadow of Parseval's split.  With it the corner's plane reading closes:
`Gtz.corner_planeTrace_surplus` turns the axis law into the statement that the
outside plane moment exceeds the outside weight by exactly `s/lam`.
-/
import Gtz.Wave.CornerAdmissibleGateway
import Gtz.Wave.ComplementBracketLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The complementary adjugate law -/

/-- **THE COMPLEMENTARY ADJUGATE LAW.**  For every real `3x3` matrix, the
adjugate of the matrix and the adjugate of its complement to the identity differ
by an affine term in the matrix and its trace.  Pure Cayley-Hamilton: no design,
no symmetry, no invertibility. -/
theorem adjugate_sub_adjugate_one_sub (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.adjugate - (1 - A).adjugate
      = (A.trace - 1) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.trace_fin_three, Matrix.one_fin_three,
      Matrix.sub_apply, Matrix.smul_apply] <;> ring

/-- **THE PLANE TRACE SURPLUS.**  At a corner the axis law pins the axis mass of
the inside moment to `(1 + lam)/lam` times the inside excess share, so the
inside moment's PLANE trace is the inside weight less `s/lam`.  Complementing,
the outside plane moment exceeds the outside weight by exactly `s/lam` -- the
surplus that carries the gateway in the deep regime. -/
theorem corner_planeTrace_surplus {lam s tauC axisMass : ℝ} (hlam : 0 < lam)
    (haxis : lam * axisMass = (1 + lam) * s) :
    (tauC + s) - axisMass = tauC - s / lam := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  field_simp
  nlinarith [haxis]

/-! ## 2. The currency bridge -/

/-- **THE CURRENCY BRIDGE.**  The squared bracket of a triple is its gap
determinant, plus its three pair minors, plus its three leverage excesses, plus
one.  Hypothesis-free.

It is the characteristic polynomial of the Gram read at one, with every
coefficient a campaign currency: the refusal side speaks in the gap determinant,
admissibility in the pair minor, and the hinge in the bracket. -/
theorem sq_tripleBracket_eq_gapDet_add_pairMinors (a b c : Fin 3 → ℝ) :
    tripleBracket a b c ^ 2
      = tripleGapDet a b c
        + (pairGapMinor a b + pairGapMinor a c + pairGapMinor b c)
        + ((leverageOf a - 1) + (leverageOf b - 1) + (leverageOf c - 1))
        + 1 := by
  rw [sq_tripleBracket_eq_gramDet]
  simp only [tripleGapDet, pairGapMinor]
  ring

/-! ## 3. The pair minor budget of a weighted triple -/

/-- **THE PAIR MINOR BUDGET OF A WEIGHTED TRIPLE.**  Hypothesis-free: three
vectors, three scalars.  The weighted shifted pair minors of a triple total the
weight complement times the excess complement, plus the squared weights against
the leverage excesses, plus the weighted squared bracket, plus the determinant
of the complementary moment. -/
theorem weightedTriple_pairMinor_identity (t1 t2 t3 : ℝ) (g1 g2 g3 : Fin 3 → ℝ) :
    t1*t2*(1 + pairGapMinor g1 g2) + t1*t3*(1 + pairGapMinor g1 g3)
        + t2*t3*(1 + pairGapMinor g2 g3)
      = (1 - (t1 + t2 + t3))
          * ((t1*(leverageOf g1 - 1) + t2*(leverageOf g2 - 1)
              + t3*(leverageOf g3 - 1)) - 1)
        + (t1^2*(leverageOf g1 - 1) + t2^2*(leverageOf g2 - 1)
            + t3^2*(leverageOf g3 - 1))
        + t1*t2*t3 * tripleBracket g1 g2 g3 ^ 2
        + (1 - t1 • atomMatrix g1 - t2 • atomMatrix g2 - t3 • atomMatrix g3).det := by
  rw [det_one_sub_weighted_triple, crossNormSq_eq_leverage_mul_sub_sq,
    crossNormSq_eq_leverage_mul_sub_sq, crossNormSq_eq_leverage_mul_sub_sq]
  simp only [pairGapMinor]
  ring

/-! ## 4. The complement of a triple -/

/-- Parseval read at one probe with three atoms held back: three atoms cannot
read a probe past its own square length. -/
theorem parseval_triple_reading_le (D : WeightedDesign m 3) (x : Fin 3 → ℝ)
    {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3) :
    D.weight d1 * (D.atom d1 ⬝ᵥ x) ^ 2 + D.weight d2 * (D.atom d2 ⬝ᵥ x) ^ 2
        + D.weight d3 * (D.atom d3 ⬝ᵥ x) ^ 2
      ≤ x ⬝ᵥ x := by
  have hall : ∑ c, D.weight c * ((D.atom c ⬝ᵥ x) * (D.atom c ⬝ᵥ x)) = x ⬝ᵥ x :=
    parseval_bilinear D x x
  have hsub : ∑ c ∈ ({d1, d2, d3} : Finset (Fin m)),
      D.weight c * ((D.atom c ⬝ᵥ x) * (D.atom c ⬝ᵥ x))
      ≤ ∑ c, D.weight c * ((D.atom c ⬝ᵥ x) * (D.atom c ⬝ᵥ x)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun c _ _ => mul_nonneg (D.weight_pos c).le (mul_self_nonneg _)
  rw [hall] at hsub
  have htriple : ∑ c ∈ ({d1, d2, d3} : Finset (Fin m)),
      D.weight c * ((D.atom c ⬝ᵥ x) * (D.atom c ⬝ᵥ x))
      = D.weight d1 * ((D.atom d1 ⬝ᵥ x) * (D.atom d1 ⬝ᵥ x))
        + (D.weight d2 * ((D.atom d2 ⬝ᵥ x) * (D.atom d2 ⬝ᵥ x))
          + D.weight d3 * ((D.atom d3 ⬝ᵥ x) * (D.atom d3 ⬝ᵥ x))) := by
    rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton]
  rw [htriple] at hsub
  calc D.weight d1 * (D.atom d1 ⬝ᵥ x) ^ 2 + D.weight d2 * (D.atom d2 ⬝ᵥ x) ^ 2
        + D.weight d3 * (D.atom d3 ⬝ᵥ x) ^ 2
      = D.weight d1 * ((D.atom d1 ⬝ᵥ x) * (D.atom d1 ⬝ᵥ x))
        + (D.weight d2 * ((D.atom d2 ⬝ᵥ x) * (D.atom d2 ⬝ᵥ x))
          + D.weight d3 * ((D.atom d3 ⬝ᵥ x) * (D.atom d3 ⬝ᵥ x))) := by ring
    _ ≤ x ⬝ᵥ x := hsub

/-- The complement of a triple is positive semidefinite: it is the weighted sum
of the atoms the triple leaves behind. -/
theorem complement_triple_posSemidef (D : WeightedDesign m 3) {d1 d2 d3 : Fin m}
    (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - D.weight d1 • atomMatrix (D.atom d1)
        - D.weight d2 • atomMatrix (D.atom d2)
        - D.weight d3 • atomMatrix (D.atom d3)).PosSemidef := by
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
            - D.weight d1 • atomMatrix (D.atom d1)
            - D.weight d2 • atomMatrix (D.atom d2)
            - D.weight d3 • atomMatrix (D.atom d3))
          *ᵥ probeVec)
        = probeVec ⬝ᵥ probeVec
          - (D.weight d1 * (D.atom d1 ⬝ᵥ probeVec) ^ 2
            + D.weight d2 * (D.atom d2 ⬝ᵥ probeVec) ^ 2
            + D.weight d3 * (D.atom d3 ⬝ᵥ probeVec) ^ 2) := by
      rw [Matrix.one_fin_three]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Matrix.sub_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
        smul_eq_mul, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_val', Matrix.of_apply]
      ring
    have hle := parseval_triple_reading_le D probeVec h12 h13 h23
    simp only [RCLike.star_def, starRingEnd_apply, star_trivial, RCLike.ofReal_re]
    rw [hquad]
    linarith

/-- The determinant of the complementary moment of a triple is not negative. -/
theorem det_complementTriple_nonneg (D : WeightedDesign m 3) {d1 d2 d3 : Fin m}
    (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3) :
    (0 : ℝ) ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - D.weight d1 • atomMatrix (D.atom d1)
        - D.weight d2 • atomMatrix (D.atom d2)
        - D.weight d3 • atomMatrix (D.atom d3)).det :=
  (complement_triple_posSemidef D h12 h13 h23).det_nonneg

/-! ## 5. The gateway producers -/

/-- **THE BRACKET GATEWAY PRODUCER.**  If the plain weight combination of a
triple falls below the weight complement times the excess complement, plus the
squared weights against the excesses, plus the weighted squared bracket, then
one of the triple's three pairs is ADMISSIBLE.

The complementary determinant is the only term dropped, and it is not negative,
so the identity forces some shifted pair minor past one. -/
theorem exists_pairMinor_pos_of_bracketBudget (D : WeightedDesign m 3)
    {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hbudget :
      D.weight d1 * D.weight d2 + D.weight d1 * D.weight d3
          + D.weight d2 * D.weight d3
        < (1 - (D.weight d1 + D.weight d2 + D.weight d3))
            * ((D.weight d1 * (leverageOf (D.atom d1) - 1)
                + D.weight d2 * (leverageOf (D.atom d2) - 1)
                + D.weight d3 * (leverageOf (D.atom d3) - 1)) - 1)
          + (D.weight d1 ^ 2 * (leverageOf (D.atom d1) - 1)
              + D.weight d2 ^ 2 * (leverageOf (D.atom d2) - 1)
              + D.weight d3 ^ 2 * (leverageOf (D.atom d3) - 1))
          + D.weight d1 * D.weight d2 * D.weight d3
              * tripleBracket (D.atom d1) (D.atom d2) (D.atom d3) ^ 2) :
    0 < pairGapMinor (D.atom d1) (D.atom d2)
      ∨ 0 < pairGapMinor (D.atom d1) (D.atom d3)
      ∨ 0 < pairGapMinor (D.atom d2) (D.atom d3) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨q12, q13, q23⟩ := hcon
  have hw1 := D.weight_pos d1
  have hw2 := D.weight_pos d2
  have hw3 := D.weight_pos d3
  have hkey := weightedTriple_pairMinor_identity (D.weight d1) (D.weight d2)
    (D.weight d3) (D.atom d1) (D.atom d2) (D.atom d3)
  have hdet := det_complementTriple_nonneg D h12 h13 h23
  have c12 : D.weight d1 * D.weight d2 * (1 + pairGapMinor (D.atom d1) (D.atom d2))
      ≤ D.weight d1 * D.weight d2 := by nlinarith [mul_pos hw1 hw2]
  have c13 : D.weight d1 * D.weight d3 * (1 + pairGapMinor (D.atom d1) (D.atom d3))
      ≤ D.weight d1 * D.weight d3 := by nlinarith [mul_pos hw1 hw3]
  have c23 : D.weight d2 * D.weight d3 * (1 + pairGapMinor (D.atom d2) (D.atom d3))
      ≤ D.weight d2 * D.weight d3 := by nlinarith [mul_pos hw2 hw3]
  linarith

/-- **THE WEIGHT GATEWAY PRODUCER.**  Six numbers decide it: the three weights
and the three leverages.  No matrix, no bracket.  The squared bracket and the
complementary determinant are both dropped, and both are not negative. -/
theorem exists_pairMinor_pos_of_weightBudget (D : WeightedDesign m 3)
    {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hbudget :
      D.weight d1 * D.weight d2 + D.weight d1 * D.weight d3
          + D.weight d2 * D.weight d3
        < (1 - (D.weight d1 + D.weight d2 + D.weight d3))
            * ((D.weight d1 * (leverageOf (D.atom d1) - 1)
                + D.weight d2 * (leverageOf (D.atom d2) - 1)
                + D.weight d3 * (leverageOf (D.atom d3) - 1)) - 1)
          + (D.weight d1 ^ 2 * (leverageOf (D.atom d1) - 1)
              + D.weight d2 ^ 2 * (leverageOf (D.atom d2) - 1)
              + D.weight d3 ^ 2 * (leverageOf (D.atom d3) - 1))) :
    0 < pairGapMinor (D.atom d1) (D.atom d2)
      ∨ 0 < pairGapMinor (D.atom d1) (D.atom d3)
      ∨ 0 < pairGapMinor (D.atom d2) (D.atom d3) := by
  refine exists_pairMinor_pos_of_bracketBudget D h12 h13 h23 ?_
  have hbr : (0 : ℝ) ≤ D.weight d1 * D.weight d2 * D.weight d3
      * tripleBracket (D.atom d1) (D.atom d2) (D.atom d3) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (D.weight_pos d1).le (D.weight_pos d2).le)
      (D.weight_pos d3).le) (sq_nonneg _)
  linarith

/-- **THE REFINED BUDGET, IN GAP CURRENCY.**  Substituting the currency bridge
into the budget replaces the squared bracket by the gap determinant and moves
the whole pair minor contribution onto one side, where every coefficient is a
positive weight product:

  `weight slack of the triple = sum (-q_ij) * t_i t_j (1 - t_k)
      + t1 t2 t3 * tripleGapDet + det(complement)` .

Hypothesis-free, one `ring` over the two landed identities.  The coefficient
`t_i t_j (1 - t_k)` is what the crude budget throws away, and it is exactly the
term that removes the extremal ray: there one atom carries almost all the excess
on almost no weight, the squared bracket is enormous, and only the
`1 + sum x_i` correction inside the left side sees it. -/
theorem weightedTriple_pairMinor_gapForm (t1 t2 t3 : ℝ) (g1 g2 g3 : Fin 3 → ℝ) :
    (t1*t2 + t1*t3 + t2*t3)
        - (1 - (t1 + t2 + t3))
            * ((t1*(leverageOf g1 - 1) + t2*(leverageOf g2 - 1)
                + t3*(leverageOf g3 - 1)) - 1)
        - (t1^2*(leverageOf g1 - 1) + t2^2*(leverageOf g2 - 1)
            + t3^2*(leverageOf g3 - 1))
        - t1*t2*t3 * (1 + (leverageOf g1 - 1) + (leverageOf g2 - 1)
            + (leverageOf g3 - 1))
      = (-(pairGapMinor g1 g2)) * (t1*t2*(1 - t3))
        + (-(pairGapMinor g1 g3)) * (t1*t3*(1 - t2))
        + (-(pairGapMinor g2 g3)) * (t2*t3*(1 - t1))
        + t1*t2*t3 * tripleGapDet g1 g2 g3
        + (1 - t1 • atomMatrix g1 - t2 • atomMatrix g2 - t3 • atomMatrix g3).det := by
  have hid := weightedTriple_pairMinor_identity t1 t2 t3 g1 g2 g3
  have hbr := sq_tripleBracket_eq_gapDet_add_pairMinors g1 g2 g3
  rw [hbr] at hid
  linarith [hid]

end Gtz
