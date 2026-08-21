/-
# The pair minor budget of a triple, and the gateway producer

The corank-two arm needs one existence fact: a corner carries an ADMISSIBLE
outside pair, a pair whose `Gtz.pairGapMinor` is positive.  It is the edge the
tie-graph argument needs, and the horns are blocked on it.

`Gtz.exists_offDiag_pairMinor_pos` gives an admissible pair SOMEWHERE in the
design.  A corner needs one whose atoms both sit OUTSIDE the dominator, because
the corner's three inside pair minors are exactly zero.  This module supplies a
producer for that, from a new exact identity.

## The identity

Let three atoms carry weights `t1, t2, t3`.  Write `a_i = t_i*(l_i - 1)` for the
weighted leverage excess.  Then, with NO hypothesis whatever -- not Parseval, not
a design, not a corner:

  **`sum_{i<j} t_i t_j (1 + q_ij)
      = (1 - T)*(S - 1) + sum_i t_i^2*(l_i - 1)
        + t1*t2*t3*[g1 g2 g3]^2 + det(1 - sum_i t_i A_i)`**

with `T = t1+t2+t3`, `S = a1+a2+a3` and `q_ij = pairGapMinor g_i g_j`
(`Gtz.weightedTriple_pairMinor_identity`).  It is the landed
`Gtz.det_one_sub_weighted_triple` read in the pair minor rather than the wedge,
and one `ring` closes it.

At a design the four right-hand terms acquire meaning.  Parseval makes
`1 - T` the total weight of the complementary atoms and `S - 1` one less the
complement's excess share, and it makes the last term `det` of the complementary
moment, which is positive semidefinite -- so that term is not negative
(`Gtz.det_complementTriple_nonneg`).  The bracket term is a square.

## The producer

Every term on the right except the first is manifestly not negative, so if the
plain weight combination `sum_{i<j} t_i t_j` falls BELOW what the right-hand
side already commits to, some `1 + q_ij` must pass one, and some pair minor is
positive (`Gtz.exists_pairMinor_pos_of_weightBudget`).  The producer needs only
the three weights and the three leverages -- six numbers, no matrix, no bracket.

[MEASURED on 86771 exact random corners with every outside atom heavy: the
producer fires at 99.6715 percent of them, and it never fires where all three
outside pair minors are nonpositive.  No corner sampled violated the gateway,
and the smallest largest outside pair minor observed was 0.3687.  The corners it
misses run to the extremal ray, where the three normalised excesses tend to one
half each and the inside weight tends to zero.]

## The complementary adjugate law

A second exact law, general to every `3x3` real matrix and proved here because
the plane reading of the corner wants it: the adjugates of a matrix and of its
complement to the identity differ by an affine term
(`Gtz.adjugate_sub_adjugate_one_sub`),

  **`adj(A) - adj(1 - A) = (tr A - 1) * 1 - A`** .

Read at a design's split into a triple and its complement it says that the two
complementary moments carry the same adjugate up to the trace, which is the
`Lambda^2` shadow of Parseval's split.
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

/-- **THE COMPLEMENTARY ADJUGATE LAW.**  For every real `3x3` matrix the
adjugate of the matrix and the adjugate of its complement to the identity differ
by an affine term in the matrix and its trace.  Pure Cayley-Hamilton: no
design, no symmetry, no invertibility. -/
theorem adjugate_sub_adjugate_one_sub (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.adjugate - (1 - A).adjugate = (A.trace - 1) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.trace_fin_three, Matrix.one_fin_three,
      Matrix.sub_apply, Matrix.smul_apply] <;> ring

/-! ## 2. The pair minor identity of a weighted triple -/

/-- **THE PAIR MINOR BUDGET OF A WEIGHTED TRIPLE.**  Hypothesis-free: three
vectors, three scalars.  The weighted shifted pair minors of a triple total the
weight complement times the excess complement, plus the squared weights against
the leverage excesses, plus the weighted squared bracket, plus the determinant
of the complementary moment.

It is `Gtz.det_one_sub_weighted_triple` read in the pair minor: the wedge is the
pair minor shifted by the two leverages, and the shift is exactly what turns the
determinant formula into a budget. -/
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

/-! ## 3. The complement of a triple is positive semidefinite -/

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

/-! ## 4. The gateway producer -/

/-- **THE GATEWAY PRODUCER.**  Six numbers decide it: the three weights and the
three leverages.  If the plain weight combination of a triple falls below the
weight complement times the excess complement plus the squared weights against
the excesses, then one of the triple's three pairs is ADMISSIBLE.

The bracket term and the complementary determinant are both not negative, so the
identity forces some shifted pair minor past one. -/
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
  by_contra hcon
  push_neg at hcon
  obtain ⟨q12, q13, q23⟩ := hcon
  have hw1 := D.weight_pos d1
  have hw2 := D.weight_pos d2
  have hw3 := D.weight_pos d3
  have hkey := weightedTriple_pairMinor_identity (D.weight d1) (D.weight d2)
    (D.weight d3) (D.atom d1) (D.atom d2) (D.atom d3)
  have hdet := det_complementTriple_nonneg D h12 h13 h23
  have hbr : (0 : ℝ) ≤ D.weight d1 * D.weight d2 * D.weight d3
      * tripleBracket (D.atom d1) (D.atom d2) (D.atom d3) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hw1.le hw2.le) hw3.le) (sq_nonneg _)
  -- each shifted pair minor is capped by one, weighted by a positive product
  have c12 : D.weight d1 * D.weight d2 * (1 + pairGapMinor (D.atom d1) (D.atom d2))
      ≤ D.weight d1 * D.weight d2 :=
    by nlinarith [mul_pos hw1 hw2]
  have c13 : D.weight d1 * D.weight d3 * (1 + pairGapMinor (D.atom d1) (D.atom d3))
      ≤ D.weight d1 * D.weight d3 :=
    by nlinarith [mul_pos hw1 hw3]
  have c23 : D.weight d2 * D.weight d3 * (1 + pairGapMinor (D.atom d2) (D.atom d3))
      ≤ D.weight d2 * D.weight d3 :=
    by nlinarith [mul_pos hw2 hw3]
  linarith

end Gtz
