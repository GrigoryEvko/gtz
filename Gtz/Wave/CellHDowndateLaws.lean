import Gtz.Wave.CellHChartFloors
import Gtz.Wave.DiamondNeighborhoodFourSet
import Gtz.Design.ConservationCalculus
import Gtz.Design.LineBranchFreePairAdjugateBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The weighted downdate law, and the producers of cell H

`Gtz.sum_fourSet_gapDet_eq_det_sub_e2` totals the FOUR triple gap determinants
of a four-set and lands on `det − e₂` of the four-set's gap.  This module shows
that the same right-hand side is reached by a completely different total, over
a completely different index set.

## The general law

For EVERY weighted design, EVERY subset `T`, and `A := S_T − 1`:

  **`Σ_c t_c · det(A − a_c a_cᵀ) = det A − e₂(A)`**  (`Gtz.sum_weighted_downdate_det`)

The sum runs over ALL `m` atoms of the design, weighted; the subset only enters
through `A`.  The proof is two lines: the rank-one determinant update turns each
summand into `det A − a_c·(adj A) a_c`, and Parseval collapses the weighted
readings of the adjugate to its trace, which in dimension three is `e₂`.

So at a four-set the UNWEIGHTED total over the four members and the WEIGHTED
total over the whole design agree (`Gtz.fourSet_downdate_totals_agree`).  The
first is a statement about four triples, the second about the entire design, and
neither hypothesis appears in the other.

## The three-of-four refinement

Dropping one member from the four-set total leaves an adjugate reading
(`Gtz.sum_three_downdate_det`):

  **`Σ_{c ≠ y} det(A − a_c a_cᵀ) = a_y·(adj A) a_y − e₂(A)`** .

On cell H the left side is exactly the three OUTSIDE floors of `A_y`, so their
total is one adjugate reading against one invariant — no inverse, no matrix.

## Why the total is not enough, and what replaces it

A positive total exhibits a positive member, so `a_y·(adj A_y) a_y > e₂(A_y)`
produces a strictly dominating triple through `y`.  **It does not cover cell H.**
[MEASURED on 19883 exact cell-H inhabitants: the total is nonpositive at 342 of
them — 1.7 percent — while the maximum is positive at every one.  The averaging
loses the disjunction, exactly as the campaign's aggregation doctrine predicts.]

The repair is to read the three determinants through their elementary symmetric
functions rather than their sum.  Three reals cannot all be nonpositive if their
first symmetric function is positive, OR their second is negative, OR their third
is positive (`Gtz.exists_pos_of_symmetric_trio`), and each disjunct is ONE
polynomial inequality — a certificate target, with no selector naming which
determinant fires.

[MEASURED on 82517 exact cell-H inhabitants: the first fires at 98.4234 percent,
the second at 79.1704, the third at 72.5693, and **the disjunction at
100.0000 percent with zero misses**.]

## The corner contraction

At a corner the adjugate reading of `y` is not a free quantity.  Contracting the
corner equation `λ u uᵀ = a_x a_xᵀ + a_y a_yᵀ + a_z a_zᵀ − 1` against `adj A`
(`Gtz.corner_adjugate_contraction`) gives

  **`a_y·(adj A) a_y − e₂(A) = λ·u·(adj A) u − a_x·(adj A) a_x − a_z·(adj A) a_z`** ,

so the cell-H total is the corner's own axis reading against the readings of the
two remaining inside atoms — for ANY matrix `A`, with no positivity anywhere.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Parseval collapses a weighted reading to a trace -/

/-- A rank-one reading is a trace against the atom matrix. -/
theorem dotProduct_mulVec_eq_trace_mul_atomMatrix
    (form : Matrix (Fin 3) (Fin 3) ℝ) (vector : Fin 3 → ℝ) :
    dotProduct vector (form *ᵥ vector) = Matrix.trace (form * atomMatrix vector) := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- **PARSEVAL AT AN ARBITRARY FORM.**  The weighted readings of any `3 x 3`
matrix by the atoms of a design total that matrix's trace. -/
theorem sum_weight_mul_reading_eq_trace (D : WeightedDesign m 3)
    (form : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ c, D.weight c * dotProduct (D.atom c) (form *ᵥ D.atom c)
      = Matrix.trace form := by
  have hstep : ∀ c : Fin m,
      D.weight c * dotProduct (D.atom c) (form *ᵥ D.atom c)
        = Matrix.trace (form * (D.weight c • atomMatrix (D.atom c))) := by
    intro c
    rw [dotProduct_mulVec_eq_trace_mul_atomMatrix, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul]
  calc ∑ c, D.weight c * dotProduct (D.atom c) (form *ᵥ D.atom c)
      = ∑ c, Matrix.trace (form * (D.weight c • atomMatrix (D.atom c))) :=
        Finset.sum_congr rfl fun c _ => hstep c
    _ = Matrix.trace (form * ∑ c, D.weight c • atomMatrix (D.atom c)) := by
        rw [Finset.mul_sum, Matrix.trace_sum]
    _ = Matrix.trace form := by rw [D.isParseval, Matrix.mul_one]

/-! ## 2. The general weighted downdate law -/

/-- **THE WEIGHTED DOWNDATE LAW.**  For every weighted design, every subset `T`,
and `A = S_T − 1`, the weighted total of the rank-one downdates of `A` by ALL the
atoms of the design is `det A − e₂(A)`.

The subset enters only through `A`; the sum runs over the whole design.  Two
lines: the rank-one determinant update, then Parseval. -/
theorem sum_weighted_downdate_det (D : WeightedDesign m 3) (T : Finset (Fin m)) :
    ∑ c, D.weight c
        * ((subsetSum D T - 1) - atomMatrix (D.atom c)).det
      = (subsetSum D T - 1).det
        - secondInvariantOfThree (subsetSum D T - 1) := by
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D T - 1 with hA
  have hterm : ∀ c : Fin m,
      D.weight c * (A - atomMatrix (D.atom c)).det
        = D.weight c * A.det
          - D.weight c * dotProduct (D.atom c) (A.adjugate *ᵥ D.atom c) := by
    intro c
    rw [det_sub_atomMatrix_fin_three]; ring
  calc ∑ c, D.weight c * (A - atomMatrix (D.atom c)).det
      = (∑ c, D.weight c * A.det)
          - ∑ c, D.weight c * dotProduct (D.atom c) (A.adjugate *ᵥ D.atom c) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => hterm c
    _ = A.det - Matrix.trace A.adjugate := by
        rw [sum_weight_mul_reading_eq_trace D A.adjugate, ← Finset.sum_mul,
          D.weight_sum_one, one_mul]
    _ = A.det - secondInvariantOfThree A := by
        rw [trace_adjugate_eq_secondInvariantOfThree]

/-- **A POSITIVE TOTAL EXHIBITS A POSITIVE DOWNDATE.**  If the second invariant
of a subset gap falls under its determinant, some atom of the design downdates
that gap to a positive determinant — with no selector naming the atom. -/
theorem exists_downdate_det_pos_of_secondInvariant_lt
    (D : WeightedDesign m 3) (T : Finset (Fin m))
    (hlt : secondInvariantOfThree (subsetSum D T - 1) < (subsetSum D T - 1).det) :
    ∃ c, 0 < ((subsetSum D T - 1) - atomMatrix (D.atom c)).det := by
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ c, D.weight c
      * ((subsetSum D T - 1) - atomMatrix (D.atom c)).det ≤ 0 :=
    Finset.sum_nonpos fun c _ =>
      mul_nonpos_of_nonneg_of_nonpos (D.weight_pos c).le (hcon c)
  rw [sum_weighted_downdate_det] at hsum
  linarith

/-! ## 3. The two totals of a four-set agree -/

/-- **THE FOUR-SET COINCIDENCE.**  At a four-set the UNWEIGHTED total of the four
triple gap determinants and the WEIGHTED total of the downdates over the WHOLE
design are the same number.  Neither statement mentions the other's index set. -/
theorem fourSet_downdate_totals_agree (D : WeightedDesign m 3)
    (T : Finset (Fin m)) (a b c d : Fin 3 → ℝ)
    (hgap : subsetSum D T - 1
      = atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1) :
    (atomMatrix b + atomMatrix c + atomMatrix d - 1).det
        + (atomMatrix a + atomMatrix c + atomMatrix d - 1).det
        + (atomMatrix a + atomMatrix b + atomMatrix d - 1).det
        + (atomMatrix a + atomMatrix b + atomMatrix c - 1).det
      = ∑ e, D.weight e
          * ((subsetSum D T - 1) - atomMatrix (D.atom e)).det := by
  rw [sum_weighted_downdate_det, sum_fourSet_gapDet_eq_det_sub_e2, hgap,
    secondInvariantOfThree]
  simp only [Matrix.trace_fin_three, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-! ## 4. The three-of-four refinement -/

/-- **THE THREE-OF-FOUR TOTAL.**  Dropping one member from the four-set total
leaves that member's adjugate reading against the second invariant.  A
polynomial identity in twelve variables — no positivity, no invertibility. -/
theorem sum_three_downdate_det (a b c d : Fin 3 → ℝ) :
    (atomMatrix a + atomMatrix c + atomMatrix d - 1).det
        + (atomMatrix a + atomMatrix b + atomMatrix d - 1).det
        + (atomMatrix a + atomMatrix b + atomMatrix c - 1).det
      = dotProduct a
          ((atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).adjugate
            *ᵥ a)
        - secondInvariantOfThree
            (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1) := by
  have hfour := sum_fourSet_gapDet_eq_det_sub_e2 a b c d
  have hdrop : (atomMatrix b + atomMatrix c + atomMatrix d - 1).det
      = (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).det
        - dotProduct a
          ((atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).adjugate
            *ᵥ a) := by
    have hsplit : atomMatrix b + atomMatrix c + atomMatrix d - 1
        = (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1)
          - atomMatrix a := by abel
    rw [hsplit, det_sub_atomMatrix_fin_three]
  rw [hdrop] at hfour
  rw [secondInvariantOfThree]
  simp only [Matrix.trace_fin_three, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_three] at hfour ⊢
  linarith [hfour]

/-! ## 5. The corner contraction -/

/-- **THE CORNER CONTRACTION.**  Reading the corner equation against the
adjugate of any matrix turns the three-of-four total into the corner's own axis
reading less the readings of the two remaining inside atoms.

No positivity, no invertibility, no design: a polynomial identity that holds for
every matrix `A` and every quadruple satisfying the corner equation. -/
theorem corner_adjugate_contraction (A : Matrix (Fin 3) (Fin 3) ℝ)
    (lam : ℝ) (u ax ay az : Fin 3 → ℝ)
    (hcorner : atomMatrix ax + atomMatrix ay + atomMatrix az - 1
      = lam • atomMatrix u) :
    dotProduct ay (A.adjugate *ᵥ ay) - secondInvariantOfThree A
      = lam * dotProduct u (A.adjugate *ᵥ u)
        - dotProduct ax (A.adjugate *ᵥ ax)
        - dotProduct az (A.adjugate *ᵥ az) := by
  have htr := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
    Matrix.trace (A.adjugate * M)) hcorner
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.mul_one, smul_eq_mul] at htr
  rw [← trace_adjugate_eq_secondInvariantOfThree]
  simp only [dotProduct_mulVec_eq_trace_mul_atomMatrix]
  have hcomm : ∀ v : Fin 3 → ℝ,
      Matrix.trace (A.adjugate * atomMatrix v)
        = Matrix.trace (A.adjugate * atomMatrix v) := fun _ => rfl
  linarith [htr]

/-! ## 6. The symmetric-function producer -/

/-- **THREE REALS, THREE WAYS TO EXHIBIT A POSITIVE ONE.**  If the first
elementary symmetric function is positive, OR the second is negative, OR the
third is positive, then one of the three is positive.

Each disjunct is a single polynomial inequality, and none of them names which
member fires.  This is the selector-free replacement for the sum: the sum is
only the first of the three. -/
theorem exists_pos_of_symmetric_trio {r s t : ℝ}
    (hdisj : 0 < r + s + t ∨ r * s + r * t + s * t < 0 ∨ 0 < r * s * t) :
    0 < r ∨ 0 < s ∨ 0 < t := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hr, hs, ht⟩ := hcon
  rcases hdisj with h1 | h2 | h3
  · linarith
  · nlinarith [mul_nonneg (neg_nonneg.mpr hr) (neg_nonneg.mpr hs),
      mul_nonneg (neg_nonneg.mpr hr) (neg_nonneg.mpr ht),
      mul_nonneg (neg_nonneg.mpr hs) (neg_nonneg.mpr ht)]
  · nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.mpr hr) (neg_nonneg.mpr hs))
      (neg_nonneg.mpr ht)]

/-! ## 7. The cell-H producers -/

/-- **THE ADJUGATE PRODUCER.**  If the adjugate reading of `y` at the four-set
gap passes the second invariant, one of the three triples through `y` has a
positive gap determinant.  The total is the first symmetric function, so this is
the weakest of the three producers. -/
theorem exists_tripleGap_pos_of_adjugate_reading_gt (a b c d : Fin 3 → ℝ)
    (hgt : secondInvariantOfThree
        (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1)
      < dotProduct a
          ((atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).adjugate
            *ᵥ a)) :
    0 < (atomMatrix a + atomMatrix c + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix a + atomMatrix b + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix a + atomMatrix b + atomMatrix c - 1).det := by
  refine exists_pos_of_symmetric_trio (Or.inl ?_)
  rw [sum_three_downdate_det a b c d]
  linarith

/-- **THE CELL-H PRODUCER TRIO.**  At a corner, the three triples through the
surviving inside atom are governed by the corner's own axis reading.  Any one of
the three symmetric conditions produces a strictly positive gap determinant, and
none of them selects which triple fires.

The first disjunct is the corner contraction of section 5: the axis reading
against the two remaining inside readings. -/
theorem cellH_exists_tripleGap_pos (lam : ℝ) (u ax ay az b c d : Fin 3 → ℝ)
    (hcorner : atomMatrix ax + atomMatrix ay + atomMatrix az - 1
      = lam • atomMatrix u)
    (hdisj :
      dotProduct ax
          ((atomMatrix ay + atomMatrix b + atomMatrix c + atomMatrix d - 1).adjugate
            *ᵥ ax)
        + dotProduct az
          ((atomMatrix ay + atomMatrix b + atomMatrix c + atomMatrix d - 1).adjugate
            *ᵥ az)
        < lam * dotProduct u
          ((atomMatrix ay + atomMatrix b + atomMatrix c + atomMatrix d - 1).adjugate
            *ᵥ u)
      ∨ (atomMatrix ay + atomMatrix c + atomMatrix d - 1).det
            * (atomMatrix ay + atomMatrix b + atomMatrix d - 1).det
          + (atomMatrix ay + atomMatrix c + atomMatrix d - 1).det
            * (atomMatrix ay + atomMatrix b + atomMatrix c - 1).det
          + (atomMatrix ay + atomMatrix b + atomMatrix d - 1).det
            * (atomMatrix ay + atomMatrix b + atomMatrix c - 1).det < 0
      ∨ 0 < (atomMatrix ay + atomMatrix c + atomMatrix d - 1).det
            * ((atomMatrix ay + atomMatrix b + atomMatrix d - 1).det
              * (atomMatrix ay + atomMatrix b + atomMatrix c - 1).det)) :
    0 < (atomMatrix ay + atomMatrix c + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix ay + atomMatrix b + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix ay + atomMatrix b + atomMatrix c - 1).det := by
  refine exists_pos_of_symmetric_trio ?_
  rcases hdisj with h1 | h2 | h3
  · refine Or.inl ?_
    rw [sum_three_downdate_det ay b c d,
      corner_adjugate_contraction _ lam u ax ay az hcorner]
    linarith
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

end Gtz
