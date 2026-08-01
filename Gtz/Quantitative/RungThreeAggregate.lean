/-
# The rung-three aggregate: the ladder does not die at `j = rank`

`Gtz.Quantitative.PairRungAggregate` states, in its own words, that the averaging
ladder "climbs to `j = rank - 1` and dies at `j = rank`", and
`Gtz.Quantitative.ChartHadamard` records the reason it was believed dead: at a
UNIFORM weight the flat triple aggregate `Σ_C det(S_C - 1)` is the design-blind
constant `-56` (`Gtz.sum_det_subsetSum_sub_one_sixThree`), and at a non-uniform
weight the header says the aggregate "is NOT design-independent -- the gap is then
`P - diag t` and no scalar shift presents it", quoting the split tetrahedron's
`-64` against the uniform `-56`.

Both readings are about the FLAT sum.  The rung the ladder actually asks for is
the one whose rung-two predecessor is
`Gtz.sum_offDiag_weight_mul_pairMinor`, and that predecessor is not flat either:
it carries the factor `t_c t_d`.  The rung-three sum with the matching factor
`∏_{c ∈ C} t_c` is exactly `Σ_{|C| = 3} det (P - diag t)[C]` -- the third
elementary symmetric function of the SIX-BY-SIX chart gap.  It closes.

## What this file provides

* `Gtz.chartGapMatrix` -- the six-by-six gap `P - diag t`, the object whose
  `2 x 2` principal minors are the shipped `Gtz.chartGapPairMinor`.
* `Gtz.trace_chartGapMatrix`, `…_sq`, `…_cube` -- its first three power traces,
  in closed form in the weights and the shares.  Idempotence of `P` is the whole
  proof; the cube is the last one that closes, because `trace ((P - D)^4)`
  contains `trace (P D P D) = Σ_{c,d} t_c t_d P_cd²`, which is a genuinely new
  quantity.  THAT is why the ladder stops -- at level FOUR, not at level three,
  and the stop is a property of the LEVEL, not of the rank.
* `Gtz.rungThreeAggregate` and `Gtz.rungThreeAggregate_eq_sum_det_chartGapMinor`
  -- the design-side sum and its chart reading, via the shipped
  `Gtz.det_projectionBlock_sub_weightDiagonal`.
* `Gtz.exists_nonneg_det_subsetSum_sub_one_of_nonneg_rungThreeAggregate` -- the
  pigeonhole.  A nonnegative aggregate forces a triple whose tie determinant is
  nonnegative.

## The closed form -- MEASURED EXACTLY, NOT MECHANIZED HERE

Newton's identity on the three traces gives, at rank three,

    rungThreeAggregate D
      = Σ_c t_c s_c + Σ_c t_c² s_c − Σ_c t_c² − (1/3) Σ_c t_c³ − 2/3 ,

with `s_c = Gtz.atomShare D c`.  Verified exactly (sympy, rational and
`ℚ(√5)` arithmetic) on twelve reference `(6,3)` designs and on twenty random
exact designs at sizes four through eight, three independent ways: the direct
twenty-determinant sum, the closed form, and `e₃` of the six-by-six gap through
its power traces.  Reference values: `-7/27` at `Gtz.icosaDesign`, `-3/16` at the
symmetric split tetrahedron, `-307/1000` at the icosahedral sign-class witness.

The one Lean ingredient still missing is Newton's identity for `e₃` against the
power sums of the spectrum; the minor-to-spectrum half is already shipped as
`Gtz.sum_det_principalMinors_eq_sum_prod_eigenvalues`.

## Why the closed form matters

The aggregate is PAIRING-BLIND and SIGN-BLIND: it sees the design only through
the twelve numbers `(t_c, s_c)`.  At a uniform weight `Σ_c t_c s_c = (1/6)·3` and
`Σ_c t_c² s_c = (1/36)·3` regardless of the design, because `Σ_c s_c = rank`
(`Gtz.sum_atomShare_eq_rank`) -- which is exactly why the shipped `-56` is
design-blind, and exactly why that blindness is an artefact of uniformity and
nothing more.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.BranchTransferConstants
import Gtz.Quantitative.ChartHadamard
import Gtz.Reduction.CompactnessReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The six-by-six chart gap and its power traces -/

/-- **The chart gap** `N = P − diag t`.  Its `2 x 2` principal minors are the
shipped `Gtz.chartGapPairMinor`, and its `3 x 3` principal minors are the weighted
tie determinants of `Gtz.rungThreeAggregate` below. -/
noncomputable def chartGapMatrix (design : WeightedDesign size rank) :
    Matrix (Fin size) (Fin size) ℝ :=
  projectionOfDesign design - Matrix.diagonal design.weight

theorem chartGapMatrix_apply (design : WeightedDesign size rank)
    (rowIndex colIndex : Fin size) :
    chartGapMatrix design rowIndex colIndex
      = projectionOfDesign design rowIndex colIndex
        - (if rowIndex = colIndex then design.weight rowIndex else 0) := by
  simp [chartGapMatrix, Matrix.diagonal_apply]

/-- `trace (P · diag t) = Σ_c t_c s_c`, the first share-weight moment. -/
theorem trace_projectionOfDesign_mul_weightDiagonal (design : WeightedDesign size rank) :
    Matrix.trace (projectionOfDesign design * Matrix.diagonal design.weight)
      = ∑ atomIndex, design.weight atomIndex * atomShare design atomIndex := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_diagonal, projectionOfDesign_diagonal, atomShare]
  ring

/-- `trace (P · diag t · diag t) = Σ_c t_c² s_c`, the second share-weight moment. -/
theorem trace_projectionOfDesign_mul_weightDiagonal_sq (design : WeightedDesign size rank) :
    Matrix.trace (projectionOfDesign design * (Matrix.diagonal design.weight
        * Matrix.diagonal design.weight))
      = ∑ atomIndex, design.weight atomIndex ^ 2 * atomShare design atomIndex := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_diagonal, projectionOfDesign_diagonal, atomShare]
  ring

theorem trace_weightDiagonal_pow_two (design : WeightedDesign size rank) :
    Matrix.trace (Matrix.diagonal design.weight * Matrix.diagonal design.weight)
      = ∑ atomIndex, design.weight atomIndex ^ 2 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [Matrix.diag_apply, Matrix.diagonal_apply_eq]; ring

theorem trace_weightDiagonal_pow_three (design : WeightedDesign size rank) :
    Matrix.trace (Matrix.diagonal design.weight
        * (Matrix.diagonal design.weight * Matrix.diagonal design.weight))
      = ∑ atomIndex, design.weight atomIndex ^ 3 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [Matrix.diag_apply, Matrix.diagonal_apply_eq]; ring

/-- **THE GAP IS THE SHIPPED CHART GAP.**  `Gtz.chartGapMatrix` is the design-side
alias of `Gtz.chartPointGap` composed with `Gtz.chartPointOfDesign`, and the
identification is definitional.  Landed so the alias is CHECKED against the tree's
own object rather than merely resembling it: every power trace below is therefore a
statement about the shipped gap, not about a private copy of it. -/
theorem chartGapMatrix_eq_chartPointGap (design : WeightedDesign size rank) :
    chartGapMatrix design = chartPointGap (chartPointOfDesign design) := rfl

/-- **THE FIRST POWER TRACE.**  `trace N = rank − 1`.

This is the shipped `Gtz.trace_projectionOfDesign_sub_weightDiagonal`
(ChartHadamard.lean:179) read through the alias, and it is consumed rather than
re-derived: the harvested prototype proved it again from `Matrix.trace_sub`, which
is the same three-line proof the shipped lemma already carries. -/
theorem trace_chartGapMatrix (design : WeightedDesign size rank) :
    Matrix.trace (chartGapMatrix design) = (rank : ℝ) - 1 :=
  trace_projectionOfDesign_sub_weightDiagonal design

/-- **THE SECOND POWER TRACE.**  `trace (N · N) = rank − 2 Σ t_c s_c + Σ t_c²`.
Idempotence of the projection is the only design input. -/
theorem trace_chartGapMatrix_sq (design : WeightedDesign size rank) :
    Matrix.trace (chartGapMatrix design * chartGapMatrix design)
      = (rank : ℝ) - 2 * (∑ atomIndex, design.weight atomIndex * atomShare design atomIndex)
        + ∑ atomIndex, design.weight atomIndex ^ 2 := by
  have hcross : Matrix.trace (Matrix.diagonal design.weight * projectionOfDesign design)
      = Matrix.trace (projectionOfDesign design * Matrix.diagonal design.weight) :=
    Matrix.trace_mul_comm _ _
  rw [chartGapMatrix, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.trace_sub, Matrix.trace_sub, projectionOfDesign_mul_self, trace_projectionOfDesign,
    hcross, trace_projectionOfDesign_mul_weightDiagonal, trace_weightDiagonal_pow_two]
  ring

/-- **THE THIRD POWER TRACE, AND THE LAST ONE THAT CLOSES.**
`trace (N · N · N) = rank − 3 Σ t_c s_c + 3 Σ t_c² s_c − Σ t_c³`.

Every summand of the expansion of `(P − D)³` reduces, by idempotence and
cyclicity, to one of `trace P`, `trace (P D)`, `trace (P D²)`, `trace D³`.  The
FOURTH power is where that stops: `(P − D)⁴` contains `P D P D`, whose trace is
`Σ_{c,d} t_c t_d P_cd²` and is not a function of the weights and the shares. -/
theorem trace_chartGapMatrix_cube (design : WeightedDesign size rank) :
    Matrix.trace (chartGapMatrix design * (chartGapMatrix design * chartGapMatrix design))
      = (rank : ℝ) - 3 * (∑ atomIndex, design.weight atomIndex * atomShare design atomIndex)
        + 3 * (∑ atomIndex, design.weight atomIndex ^ 2 * atomShare design atomIndex)
        - ∑ atomIndex, design.weight atomIndex ^ 3 := by
  set projection := projectionOfDesign design with hprojection
  set diag := Matrix.diagonal design.weight with hdiag
  have hidem : projection * projection = projection := projectionOfDesign_mul_self design
  have hexpand : chartGapMatrix design * (chartGapMatrix design * chartGapMatrix design)
      = projection * (projection * projection)
        - projection * (projection * diag) - projection * (diag * projection)
        - diag * (projection * projection)
        + projection * (diag * diag) + diag * (projection * diag)
        + diag * (diag * projection) - diag * (diag * diag) := by
    simp only [chartGapMatrix, ← hprojection, ← hdiag, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have htrace1 : Matrix.trace (projection * (projection * diag))
      = Matrix.trace (projection * diag) := by
    rw [← Matrix.mul_assoc, hidem]
  have htrace2 : Matrix.trace (projection * (diag * projection))
      = Matrix.trace (projection * diag) := by
    rw [Matrix.trace_mul_comm projection (diag * projection), Matrix.mul_assoc, hidem,
      Matrix.trace_mul_comm]
  have htrace0 : Matrix.trace (projection * (projection * projection))
      = Matrix.trace projection := by
    rw [hidem, hidem]
  have htrace3 : Matrix.trace (diag * (projection * projection))
      = Matrix.trace (projection * diag) := by
    rw [hidem, Matrix.trace_mul_comm]
  have htrace4 : Matrix.trace (diag * (projection * diag))
      = Matrix.trace (projection * (diag * diag)) := by
    rw [Matrix.trace_mul_comm diag (projection * diag), Matrix.mul_assoc]
  have htrace5 : Matrix.trace (diag * (diag * projection))
      = Matrix.trace (projection * (diag * diag)) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [hexpand]
  simp only [Matrix.trace_add, Matrix.trace_sub, htrace0, htrace1, htrace2, htrace3,
    htrace4, htrace5]
  rw [trace_projectionOfDesign, hprojection, hdiag,
    trace_projectionOfDesign_mul_weightDiagonal,
    trace_projectionOfDesign_mul_weightDiagonal_sq, trace_weightDiagonal_pow_three]
  ring

/-! ## The rung-three aggregate and its pigeonhole -/

/-- **THE RUNG-THREE AGGREGATE.**  The `∏ t`-weighted total of the twenty tie
determinants.  The weighting is the one the rung-two law
`Gtz.sum_offDiag_weight_mul_pairMinor` already uses, not the flat one of
`Gtz.sum_det_subsetSum_sub_one_uniform`. -/
noncomputable def rungThreeAggregate (design : WeightedDesign size rank) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
    (∏ atomIndex ∈ selected, design.weight atomIndex) * (subsetSum design selected - 1).det

/-- **THE MINOR-BY-MINOR CHART READING.**  Each principal block determinant of the
six-by-six chart gap is the corresponding weighted tie determinant, by the shipped
positive-diagonal congruence `Gtz.det_projectionBlock_sub_weightDiagonal`. -/
theorem det_chartGapMatrix_block (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) :
    ((chartGapMatrix design).submatrix
        (Subtype.val : { c // c ∈ selected } → Fin size)
        (Subtype.val : { c // c ∈ selected } → Fin size)).det
      = (∏ atomIndex ∈ selected, design.weight atomIndex)
        * (subsetSum design selected - 1).det := by
  classical
  have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  have hreindex : ((chartGapMatrix design).submatrix
        (Subtype.val : { c // c ∈ selected } → Fin size)
        (Subtype.val : { c // c ∈ selected } → Fin size)).det
      = ((chartGapMatrix design).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)).det := by
    rw [← Matrix.det_submatrix_equiv_self (selected.orderIsoOfFin hcard).toEquiv,
      Matrix.submatrix_submatrix]
    rfl
  have hblock : (chartGapMatrix design).submatrix
        (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
      = (projectionOfDesign design).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)
        - Matrix.diagonal
            (fun slot => design.weight (selected.orderEmbOfFin hcard slot)) := by
    ext leftIndex rightIndex
    simp only [chartGapMatrix, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.diagonal_apply]
    by_cases hsame : leftIndex = rightIndex
    · subst hsame; simp
    · rw [if_neg fun hcollide =>
        hsame ((selected.orderEmbOfFin hcard).injective hcollide), if_neg hsame]
  have hprod : (∏ slot : Fin rank, design.weight (selected.orderEmbOfFin hcard slot))
      = ∏ atomIndex ∈ selected, design.weight atomIndex := by
    conv_rhs => rw [← himage]
    rw [Finset.prod_image (selected.orderEmbOfFin hcard).injective.injOn]
  rw [hreindex, hblock, det_projectionBlock_sub_weightDiagonal, hprod,
    det_mul_transpose_sub_one_comm,
    transpose_mul_selectedAtomRows design _ (selected.orderEmbOfFin hcard).injective, himage]

/-- **THE CHART READING OF THE AGGREGATE.**  It is the sum of the `rank`-sized
principal minors of the six-by-six chart gap, i.e. `e_rank (P - diag t)`. -/
theorem rungThreeAggregate_eq_sum_det_chartGapMinor (design : WeightedDesign size rank) :
    rungThreeAggregate design
      = ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
          ((chartGapMatrix design).submatrix
            (Subtype.val : { c // c ∈ selected } → Fin size)
            (Subtype.val : { c // c ∈ selected } → Fin size)).det :=
  Finset.sum_congr rfl fun _ hmember =>
    (det_chartGapMatrix_block design (Finset.mem_powersetCard.mp hmember).2).symm

/-- **THE PIGEONHOLE.**  A nonnegative rung-three aggregate forces a triple whose
tie determinant is nonnegative.  Unconditional: positive weights and a
nonnegative total cannot come from strictly negative summands. -/
theorem exists_nonneg_det_subsetSum_sub_one_of_nonneg_rungThreeAggregate
    {design : WeightedDesign size rank} (hnonneg : 0 ≤ rungThreeAggregate design)
    (hexists : ((Finset.univ : Finset (Fin size)).powersetCard rank).Nonempty) :
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ 0 ≤ (subsetSum design selected - 1).det := by
  classical
  by_contra hnone
  push Not at hnone
  have hstrict : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      (∏ atomIndex ∈ selected, design.weight atomIndex)
          * (subsetSum design selected - 1).det < 0 := by
    intro selected hmember
    have hcard : selected.card = rank := (Finset.mem_powersetCard.mp hmember).2
    have hweight : 0 < ∏ atomIndex ∈ selected, design.weight atomIndex :=
      Finset.prod_pos fun atomIndex _ => design.weight_pos atomIndex
    exact mul_neg_of_pos_of_neg hweight (hnone selected hcard)
  have hsum : rungThreeAggregate design < 0 :=
    Finset.sum_neg hstrict hexists
  exact absurd hnonneg (not_le.mpr hsum)

/-- The `(6,3)` reading: twenty triples, and the pigeonhole always has something
to pigeonhole into. -/
theorem exists_nonneg_det_subsetSum_sub_one_sixThree {design : WeightedDesign 6 3}
    (hnonneg : 0 ≤ rungThreeAggregate design) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ 0 ≤ (subsetSum design selected - 1).det := by
  refine exists_nonneg_det_subsetSum_sub_one_of_nonneg_rungThreeAggregate hnonneg ?_
  refine ⟨{0, 1, 2}, ?_⟩
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ _, by decide⟩

/-- **THE CONTRAPOSITIVE, IN CRUX SHAPE.**  If every triple has a strictly
negative tie determinant -- the shape a `(6,3)` crux takes whenever every
non-dominating block has exactly ONE eigenvalue below one -- then the aggregate is
strictly negative, hence so is its closed form in the weights and the shares. -/
theorem rungThreeAggregate_neg_of_forall_det_neg {design : WeightedDesign 6 3}
    (hneg : ∀ selected : Finset (Fin 6), selected.card = 3 →
      (subsetSum design selected - 1).det < 0) :
    rungThreeAggregate design < 0 := by
  by_contra hnonneg
  obtain ⟨selected, hcard, hdet⟩ :=
    exists_nonneg_det_subsetSum_sub_one_sixThree (not_lt.mp hnonneg)
  exact absurd hdet (not_le.mpr (hneg selected hcard))

end Gtz
