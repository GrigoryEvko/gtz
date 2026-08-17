import Gtz.Wave.NoStressResidualSwapBrackets
import Gtz.Quantitative.CauchyBinetLayerSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The trace-determinant cell: one polynomial in the unweighted moment covers a fifth of
the rank-three stratum

`Gtz.no_two_invariant_domination_test` closes the `(trace, second invariant)` chart: at
the root design two gaps carry the same trace and the same second invariant while their
determinants are `5/4` and `-49/4`, so no test written in those two numbers decides
domination.  The chart it leaves untouched is `(trace, determinant)`, and that chart
carries a certificate:

    `trace (S_C - 1) + 2 < det (S_C - 1)`   ==>   `S_C - 1` is positive definite.       (T)

`(T)` reads two invariants of the gap and nothing else -- no weight, no eigenvalue, no
inverse.  It is the bracket test `Gtz.posDef_gap_of_sum_pairBracketSq_lt` of the sibling
module in different clothing, because

    `det (S_C - 1) - trace (S_C - 1) - 2 = [p,q,r]^2 - <q,r> - <p,r> - <p,q>` ,         (I)

an identity in nine coordinates (`Gtz.det_sub_one_sub_trace_sub_two`).  In Gram
invariants it is `e3 - e2`, so `(T)` says `tr (Gram_C inverse) < 1`, which pushes every
Gram eigenvalue past one at a stroke.

## The aggregate, and the cell

The campaign already owns the Cauchy-Binet layer sums (`Gtz.sum_det_subsetSum_sub_one_eq`,
`Gtz.sum_principalMinorTotal_subsetSum_eq`).  Sum the left side of `(T)` over all
`C(m,3)` triples and the layer counts collapse:

    `sum over triples of [ det (S_C - 1) - trace (S_C - 1) - 2 ]  =  det N - (m-2) e2(N)`  (A)

with `N` the UNWEIGHTED second moment (`Gtz.sum_traceDetDefect_rankThree`).  The three
`C(m,3)` contributions cancel to nothing and the two `C(m-1,2) tr N` contributions cancel
each other, so the aggregate reads only two invariants of one `3 x 3` matrix, and the
size enters ONLY through the coefficient `m - 2`.  One polynomial inequality therefore
decides a whole cell at EVERY size:

    `(m-2) e2(N) < det N`   ==>   some triple dominates STRICTLY                        (C)

(`Gtz.exists_posDef_gap_of_secondMoment_lt_det`), and contrapositively every rank-three
tie -- primitive or not, stress-free or not, at any size -- obeys `det N <= (m-2) e2(N)`
(`Gtz.secondMoment_le_det_of_isTie`).  At `(6,3)` the coefficient is four and at `(7,3)`
it is five, so the campaign's two open cells both receive the criterion, and the second
costs nothing extra.  Read through the inverse, `(C)` is `tr (N inverse) < 1/(m-2)`, and
`tr (N inverse) = sum_a t_a (g_a . N inverse g_a)` is the weighted mean of the UNWEIGHTED
leverage scores, which always total three.  So the cell is exactly the region where a
design's weight sits on its low-leverage atoms.

## Calibration

At the root design `N = 6 . 1`, so `det N = 216`, `e2(N) = 108`, and `(A)` reads `-216`
(`Gtz.sum_traceDetDefect_coordinateDiagonalDesign`).  The cell misses the root design by
`216`, and the miss is visible triple by triple: `e3 - e2` is `-27/4` on the four vertex
stars, `-9` on the twelve other spanning triples and `-81/4` on the four degenerate ones,
and `4(-27/4) + 12(-9) + 4(-81/4) = -216`.

## What is measured and what is not

MEASURED, 2026-08-17, Julia at 48 threads, designs rebuilt from a rank-three projection
and a weight vector.  On 199946 uniform primitive stress-free `(6,3)` draws the identity
`(A)` holds to a worst relative error of `5.0e-10`, and the cell `(C)` fires on `18.638`
per cent of them.  That is a fifth of the stratum decided by one polynomial in the
unweighted moment.  The smallest `tr (N inverse)` seen under uniform sampling is
`0.00206`, far inside the threshold `1/4`.  A directed hunt drives `tr (N inverse)` to
zero along the vanishing-weight boundary, where the cell fires trivially.  None of that
is kernel.  What IS kernel is `(I)`, `(T)`, `(A)`, `(C)`, the two size readings and the
root-design value `-216`.
-/

namespace Gtz

open scoped BigOperators

open Matrix

variable {size : ℕ}

/-! ## 1. The identity behind the trace–determinant chart -/

/-- **THE TRACE–DETERMINANT DEFECT OF A TRIPLE, IN BRACKETS.**  A polynomial identity in
nine coordinates: the gap determinant less the gap trace less two is the triple's squared
bracket less its three pair Gram determinants.  In Gram invariants it is `e₃ − e₂`. -/
theorem det_sub_one_sub_trace_sub_two (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    (atomMatrix firstVec + atomMatrix secondVec + atomMatrix thirdVec - 1).det
        - Matrix.trace (atomMatrix firstVec + atomMatrix secondVec + atomMatrix thirdVec - 1)
        - 2
      = tripleBracket firstVec secondVec thirdVec ^ 2
        - pairBracketSq secondVec thirdVec - pairBracketSq firstVec thirdVec
        - pairBracketSq firstVec secondVec := by
  simp only [Matrix.one_fin_three, Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.sub_apply,
    Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply, tripleBracket_eq, pairBracketSq,
    leverageOf, dotProduct, Fin.sum_univ_three, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- The atom sum of an explicit triple, written out. -/
theorem subsetSum_of_three_labels (design : WeightedDesign size 3) {pivot leftLabel rightLabel : Fin size}
    (hpivotLeft : pivot ≠ leftLabel) (hpivotRight : pivot ≠ rightLabel)
    (hleftRight : leftLabel ≠ rightLabel) :
    subsetSum design ({pivot, leftLabel, rightLabel} : Finset (Fin size))
      = atomMatrix (design.atom pivot) + atomMatrix (design.atom leftLabel)
        + atomMatrix (design.atom rightLabel) := by
  classical
  rw [subsetSum, Finset.sum_insert (by simp [hpivotLeft, hpivotRight]),
    Finset.sum_insert (by simp [hleftRight]), Finset.sum_singleton, add_assoc]

/-! ## 2. The certificate in the trace–determinant chart -/

/-- **THE TRACE–DETERMINANT CERTIFICATE.**  A triple whose gap determinant passes its gap
trace plus two dominates STRICTLY.  Two invariants of one matrix decide, and the pair
`Gtz.no_two_invariant_domination_test` refutes is the OTHER pair — trace against the
second invariant — so this certificate is untouched by that no-go. -/
theorem posDef_gap_of_trace_add_two_lt_det (design : WeightedDesign size 3)
    {pivot leftLabel rightLabel : Fin size} (hpivotLeft : pivot ≠ leftLabel)
    (hpivotRight : pivot ≠ rightLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hdefect : Matrix.trace
          (subsetSum design ({pivot, leftLabel, rightLabel} : Finset (Fin size)) - 1) + 2
      < (subsetSum design ({pivot, leftLabel, rightLabel} : Finset (Fin size)) - 1).det) :
    (subsetSum design ({pivot, leftLabel, rightLabel} : Finset (Fin size)) - 1).PosDef := by
  rw [subsetSum_of_three_labels design hpivotLeft hpivotRight hleftRight] at hdefect
  have hbracketForm := det_sub_one_sub_trace_sub_two (design.atom pivot) (design.atom leftLabel)
    (design.atom rightLabel)
  have hsurplus : pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
      + pairBracketSq (design.atom pivot) (design.atom rightLabel)
      + pairBracketSq (design.atom pivot) (design.atom leftLabel)
      < tripleBracket (design.atom pivot) (design.atom leftLabel)
          (design.atom rightLabel) ^ 2 := by
    linarith [hbracketForm, hdefect]
  have hpairOne := pairBracketSq_nonneg (design.atom leftLabel) (design.atom rightLabel)
  have hpairTwo := pairBracketSq_nonneg (design.atom pivot) (design.atom rightLabel)
  have hpairThree := pairBracketSq_nonneg (design.atom pivot) (design.atom leftLabel)
  have hsq : 0 < tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ^ 2 := by linarith
  have hbracket : tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ≠ 0 := by
    intro hzero; rw [hzero] at hsq; norm_num at hsq
  exact posDef_gap_of_sum_pairBracketSq_lt design hpivotLeft hpivotRight hleftRight hbracket
    hsurplus

/-- The certificate on a card-three subset, with the labels extracted. -/
theorem posDef_gap_of_trace_add_two_lt_det_finset (design : WeightedDesign size 3)
    {selected : Finset (Fin size)} (hcard : selected.card = 3)
    (hdefect : Matrix.trace (subsetSum design selected - 1) + 2
      < (subsetSum design selected - 1).det) :
    (subsetSum design selected - 1).PosDef := by
  obtain ⟨pivot, leftLabel, rightLabel, hpivotLeft, hpivotRight, hleftRight, hset⟩ :=
    Finset.card_eq_three.mp hcard
  subst hset
  exact posDef_gap_of_trace_add_two_lt_det design hpivotLeft hpivotRight hleftRight hdefect

/-! ## 3. The aggregate over the triples, at EVERY size -/

/-- **THE TRACE–DETERMINANT AGGREGATE, AT EVERY SIZE AND RANK THREE.**  Summing the
certificate's defect over all `C(m,3)` triples leaves exactly `det N − (m−2)·e₂(N)`, with
`N` the UNWEIGHTED second moment.  The trace layer and the constant layer cancel the
determinant layer's own trace and constant terms — the three `C(m,3)` contributions
cancel to nothing and the `C(m−1,2) tr N` contributions cancel each other — so the
aggregate reads only two invariants of one `3 × 3` matrix, and the size enters ONLY
through the coefficient `m − 2`. -/
theorem sum_traceDetDefect_rankThree {m : ℕ} (design : WeightedDesign m 3) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard 3,
        ((subsetSum design selected - 1).det
          - Matrix.trace (subsetSum design selected - 1) - 2)
      = (subsetSum design Finset.univ).det
        - ((m - 2 : ℕ) : ℝ) * principalMinorTotal (subsetSum design Finset.univ) 2 := by
  classical
  set moment := subsetSum design Finset.univ with hmoment
  set tripleCount : ℝ := ((Nat.choose m 3 : ℕ) : ℝ) with htripleCount
  set atomLayer : ℝ := ((Nat.choose (m - 1) 2 : ℕ) : ℝ) with hatomLayer
  -- the determinant layer, expanded
  have hdet : ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard 3,
      (subsetSum design selected - 1).det
      = - tripleCount + atomLayer * Matrix.trace moment
        - ((m - 2 : ℕ) : ℝ) * principalMinorTotal moment 2 + moment.det := by
    have hlayer := sum_det_subsetSum_sub_one_eq design
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one] at hlayer
    have hzero : principalMinorTotal moment 0 = 1 := principalMinorTotal_zero moment
    have hone : principalMinorTotal moment 1 = Matrix.trace moment := principalMinorTotal_one moment
    have hthree : principalMinorTotal moment 3 = moment.det := by
      have hcard := principalMinorTotal_card moment
      rwa [Fintype.card_fin] at hcard
    rw [hlayer, hzero, hone, hthree]
    norm_num [Nat.choose_one_right, htripleCount, hatomLayer]
    ring
  -- the trace layer
  have htrace : ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard 3,
      Matrix.trace (subsetSum design selected) = atomLayer * Matrix.trace moment := by
    have hlayer := sum_principalMinorTotal_subsetSum_eq design 1 (by norm_num)
    simp only [principalMinorTotal_one] at hlayer
    rw [hlayer, hatomLayer, hmoment]
  have hshift : ∀ selected : Finset (Fin m),
      Matrix.trace (subsetSum design selected - 1)
        = Matrix.trace (subsetSum design selected) - 3 := by
    intro selected
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
    norm_num
  have hcount : ((Finset.univ : Finset (Fin m)).powersetCard 3).card = Nat.choose m 3 := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have htraceGap : ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard 3,
      Matrix.trace (subsetSum design selected - 1)
      = atomLayer * Matrix.trace moment - 3 * tripleCount := by
    rw [Finset.sum_congr rfl fun selected _ => hshift selected, Finset.sum_sub_distrib, htrace,
      Finset.sum_const, hcount, htripleCount, nsmul_eq_mul]
    ring
  have hconst : ∑ _selected ∈ (Finset.univ : Finset (Fin m)).powersetCard 3, (2 : ℝ)
      = 2 * tripleCount := by
    rw [Finset.sum_const, hcount, htripleCount, nsmul_eq_mul]; ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hdet, htraceGap, hconst]
  ring

/-! ## 4. The cell, at every size -/

/-- **THE TRACE–DETERMINANT CELL, AT EVERY SIZE AND RANK THREE.**  If the unweighted
second moment satisfies `(m−2)·e₂(N) < det N` then some triple dominates STRICTLY.  One
polynomial inequality in one `3 × 3` matrix, with no weight, no eigenvalue and no
inverse.  At `(6,3)` the coefficient is `4` and at `(7,3)` it is `5`. -/
theorem exists_posDef_gap_of_secondMoment_lt_det {m : ℕ} (design : WeightedDesign m 3)
    (hcell : ((m - 2 : ℕ) : ℝ) * principalMinorTotal (subsetSum design Finset.univ) 2
      < (subsetSum design Finset.univ).det) :
    ∃ selected : Finset (Fin m), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  have hsum := sum_traceDetDefect_rankThree design
  have hpos : 0 < ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard 3,
      ((subsetSum design selected - 1).det
        - Matrix.trace (subsetSum design selected - 1) - 2) := by
    rw [hsum]; linarith
  have hlt : ∑ _selected ∈ (Finset.univ : Finset (Fin m)).powersetCard 3, (0 : ℝ)
      < ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard 3,
        ((subsetSum design selected - 1).det
          - Matrix.trace (subsetSum design selected - 1) - 2) := by
    rw [Finset.sum_const_zero]; exact hpos
  obtain ⟨selected, hmem, hterm⟩ := Finset.exists_lt_of_sum_lt hlt
  have hcard : selected.card = 3 := (Finset.mem_powersetCard.mp hmem).2
  exact ⟨selected, hcard,
    posDef_gap_of_trace_add_two_lt_det_finset design hcard (by linarith [hterm])⟩

/-- **THE CELL EXCLUDES TIES, AT EVERY SIZE.** -/
theorem not_isTie_of_secondMoment_lt_det {m : ℕ} (design : WeightedDesign m 3)
    (hcell : ((m - 2 : ℕ) : ℝ) * principalMinorTotal (subsetSum design Finset.univ) 2
      < (subsetSum design Finset.univ).det) :
    ¬ IsTie design := by
  intro htie
  obtain ⟨selected, hcard, hposDef⟩ := exists_posDef_gap_of_secondMoment_lt_det design hcell
  exact htie.2 selected hcard hposDef

/-- **THE NECESSARY CONDITION ON EVERY RANK-THREE TIE.**  Contrapositive of the cell, and
the first aggregate obstruction the tie locus carries in the unweighted moment alone: no
weight, no primitivity, no stress-freeness, no size hypothesis. -/
theorem secondMoment_le_det_of_isTie {m : ℕ} (design : WeightedDesign m 3) (htie : IsTie design) :
    (subsetSum design Finset.univ).det
      ≤ ((m - 2 : ℕ) : ℝ) * principalMinorTotal (subsetSum design Finset.univ) 2 := by
  by_contra hlt
  push_neg at hlt
  exact not_isTie_of_secondMoment_lt_det design hlt htie

/-- The cell in the campaign's positive form: it produces a dominating triple. -/
theorem dominates_of_secondMoment_lt_det {m : ℕ} (design : WeightedDesign m 3)
    (hcell : ((m - 2 : ℕ) : ℝ) * principalMinorTotal (subsetSum design Finset.univ) 2
      < (subsetSum design Finset.univ).det) :
    ∃ selected : Finset (Fin m), selected.card = 3 ∧ Dominates design selected := by
  obtain ⟨selected, hcard, hposDef⟩ := exists_posDef_gap_of_secondMoment_lt_det design hcell
  exact ⟨selected, hcard, hposDef.posSemidef⟩

/-- **THE `(6,3)` READING**: the coefficient is four. -/
theorem exists_posDef_gap_of_four_mul_secondMoment_lt_det (design : WeightedDesign 6 3)
    (hcell : 4 * principalMinorTotal (subsetSum design Finset.univ) 2
      < (subsetSum design Finset.univ).det) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef :=
  exists_posDef_gap_of_secondMoment_lt_det design
    (by rw [show (((6 : ℕ) - 2 : ℕ) : ℝ) = 4 from by norm_num]; exact hcell)

/-- The `(6,3)` tie obstruction. -/
theorem four_mul_secondMoment_le_det_of_isTie (design : WeightedDesign 6 3) (htie : IsTie design) :
    (subsetSum design Finset.univ).det
      ≤ 4 * principalMinorTotal (subsetSum design Finset.univ) 2 := by
  have hgeneral := secondMoment_le_det_of_isTie design htie
  rw [show (((6 : ℕ) - 2 : ℕ) : ℝ) = 4 from by norm_num] at hgeneral
  exact hgeneral

/-- **THE `(7,3)` READING**: the coefficient is five.  The other open cell of the
campaign receives the same criterion, with no new work. -/
theorem exists_posDef_gap_of_five_mul_secondMoment_lt_det (design : WeightedDesign 7 3)
    (hcell : 5 * principalMinorTotal (subsetSum design Finset.univ) 2
      < (subsetSum design Finset.univ).det) :
    ∃ selected : Finset (Fin 7), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef :=
  exists_posDef_gap_of_secondMoment_lt_det design
    (by rw [show (((7 : ℕ) - 2 : ℕ) : ℝ) = 5 from by norm_num]; exact hcell)

/-- The `(7,3)` tie obstruction. -/
theorem five_mul_secondMoment_le_det_of_isTie (design : WeightedDesign 7 3) (htie : IsTie design) :
    (subsetSum design Finset.univ).det
      ≤ 5 * principalMinorTotal (subsetSum design Finset.univ) 2 := by
  have hgeneral := secondMoment_le_det_of_isTie design htie
  rw [show (((7 : ℕ) - 2 : ℕ) : ℝ) = 5 from by norm_num] at hgeneral
  exact hgeneral

/-- The `(6,3)` aggregate, in the shape the campaign's layer laws are written in. -/
theorem sum_traceDetDefect_sixThree (design : WeightedDesign 6 3) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        ((subsetSum design selected - 1).det
          - Matrix.trace (subsetSum design selected - 1) - 2)
      = (subsetSum design Finset.univ).det
        - 4 * principalMinorTotal (subsetSum design Finset.univ) 2 := by
  have hgeneral := sum_traceDetDefect_rankThree design
  rw [show (((6 : ℕ) - 2 : ℕ) : ℝ) = 4 from by norm_num] at hgeneral
  exact hgeneral

/-! ## 5. The root design, in kernel -/

/-- The unweighted second moment of the root design is `6 · 1`. -/
theorem subsetSum_univ_coordinateDiagonalDesign :
    subsetSum coordinateDiagonalDesign Finset.univ
      = (6 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  rw [subsetSum, Matrix.sum_apply]
  simp only [Fin.sum_univ_six, coordinateDiagonalDesign_atomMatrix_entry, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, diagonalPattern_zero, diagonalPattern_one, diagonalPattern_two,
    diagonalPattern_three, diagonalPattern_four, diagonalPattern_five]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;> norm_num

/-- **THE ROOT DESIGN MISSES THE CELL BY `216`.**  The twenty trace–determinant defects
total `−216`, so the cell is not merely tight at the campaign's calibration object — it
fails there by a wide margin, exactly as the free-mass arm does. -/
theorem sum_traceDetDefect_coordinateDiagonalDesign :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        ((subsetSum coordinateDiagonalDesign selected - 1).det
          - Matrix.trace (subsetSum coordinateDiagonalDesign selected - 1) - 2)
      = -216 := by
  rw [sum_traceDetDefect_sixThree, subsetSum_univ_coordinateDiagonalDesign,
    principalMinorTotal_smul_one, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
  norm_num

/-- The root design is outside the cell. -/
theorem not_four_mul_secondMoment_lt_det_coordinateDiagonalDesign :
    ¬ (4 * principalMinorTotal (subsetSum coordinateDiagonalDesign Finset.univ) 2
      < (subsetSum coordinateDiagonalDesign Finset.univ).det) := by
  rw [subsetSum_univ_coordinateDiagonalDesign, principalMinorTotal_smul_one, Matrix.det_smul,
    Matrix.det_one, Fintype.card_fin]
  norm_num

/-! ## 6. The residual, strictly narrowed

`Gtz.NoStressResidual 6` is the one open hypothesis of branch (i) of
`Gtz.sixThree_stress_trichotomy`.  The cell discharges it wherever it fires, so the
obligation survives only OFF the cell.  `Gtz.NoStressResidualOffCell` is that narrowing,
and `Gtz.noStressResidual_of_offCell` proves it is enough. -/

/-- **THE RESIDUAL OFF THE CELL.**  `Gtz.NoStressResidual`, with the extra antecedent
`det N <= (size-2) e2(N)`.  Strictly weaker than the residual: the cell region is removed
from the quantifier. -/
def NoStressResidualOffCell (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3,
    IsPrimitiveDesign design →
    (∀ stressCoeff : Fin size → ℝ,
        (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
          stressCoeff = 0) →
    (∀ selected : Finset (Fin size), selected.card = 3 →
        ¬ HasStrictCertificate design selected) →
    (subsetSum design Finset.univ).det
        ≤ ((size - 2 : ℕ) : ℝ) * principalMinorTotal (subsetSum design Finset.univ) 2 →
    ∃ dominatingTriple : Finset (Fin size), dominatingTriple.card = 3
      ∧ (subsetSum design dominatingTriple - 1).PosDef

/-- **THE NARROWING IS ENOUGH.**  The residual off the cell implies the residual.  On the
cell the trace-determinant aggregate produces the dominating triple with no hypothesis at
all -- not primitivity, not stress-freeness, not the absence of certificates. -/
theorem noStressResidual_of_offCell {size : ℕ} (hoff : NoStressResidualOffCell size) :
    ∀ design : WeightedDesign size 3,
      IsPrimitiveDesign design →
      (∀ stressCoeff : Fin size → ℝ,
          (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
            stressCoeff = 0) →
      (∀ selected : Finset (Fin size), selected.card = 3 →
          ¬ HasStrictCertificate design selected) →
      ∃ dominatingTriple : Finset (Fin size), dominatingTriple.card = 3
        ∧ (subsetSum design dominatingTriple - 1).PosDef := by
  intro design hprimitive hstressFree hfree
  by_cases hcell : ((size - 2 : ℕ) : ℝ)
      * principalMinorTotal (subsetSum design Finset.univ) 2
      < (subsetSum design Finset.univ).det
  · exact exists_posDef_gap_of_secondMoment_lt_det design hcell
  · push_neg at hcell
    exact hoff design hprimitive hstressFree hfree hcell

/-- **THE `(6,3)` NARROWING, in the campaign's own vocabulary.**  `Gtz.NoStressResidual 6`
follows from its restriction to the region `det N <= 4 e2(N)`.  Everything outside that
region is now closed in kernel, unconditionally. -/
theorem noStressResidual_six_of_offCell (hoff : NoStressResidualOffCell 6) :
    NoStressResidual 6 :=
  noStressResidual_of_offCell hoff

/-- **THE TIE FORM OF THE NARROWING.**  A primitive stress-free `(6,3)` tie must sit off
the cell, so the whole tie-freeness question lives on `det N <= 4 e2(N)`. -/
theorem four_mul_secondMoment_le_det_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) :
    (subsetSum design Finset.univ).det
      ≤ 4 * principalMinorTotal (subsetSum design Finset.univ) 2 :=
  four_mul_secondMoment_le_det_of_isTie design htie

end Gtz
