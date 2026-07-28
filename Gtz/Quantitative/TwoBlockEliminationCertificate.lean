/-
# THE TWO-BLOCK ELIMINATION STEP, DISCHARGED

`Gtz.Quantitative.ChartEmptinessCertificate` closes the negative-value half of the
two-block partition class of the `(6,3)` covering census under a named hypothesis it
does not prove, `Gtz.EliminatesChartTwoBlockValue`: that an admissible two-block datum
with both blocks occupied and a negative value satisfies `E(value) = 0`, where
`E(g) = 108 g^3 - 108 g^2 + 9 g + 5` is the eliminant of the two-block stationarity
system in the value variable.  `Gtz.Quantitative.CauchyBinetValueFloor` discharged the
OTHER hypothesis of that closure, the numeral `-(3/20) <= value`, and said in its own
words that the elimination step "remains, so what follows is the same class closure
with one hypothesis fewer -- not an unconditional one."

This file removes it.  `eliminatesChartTwoBlockValue_three` is a THEOREM.

## The theorem the elimination step is a corollary of

`value_eq_neg_inv_size_of_isChartTwoBlockFamily_of_negativeValue` -- a chart
stationarity datum whose active family is two complementary blocks and whose value is
NEGATIVE has

    `value = -1/size`   EXACTLY,   at every `size` and every `rank`.

The value is not merely constrained to a root set of a cubic; it is PINNED.  There is
no case split, no Groebner basis, no elimination and no admissibility hypothesis
anywhere in the proof, which is a trace argument in eight steps.  Write `Xi` for the
assembly, `T = diag t`, `N = value + T`, and `Q` for the orthogonal projection onto
the column space of `Xi`.

* `chartBlockDiagonalPart_mul_multiplier` -- the shipped same-block relation
  `Gtz.projection_mul_multiplier_apply_of_sameBlock`, packaged as a matrix identity:
  the BLOCK-DIAGONAL TRUNCATION of the chart acts on the assembly exactly as `N`.
  The global identity `P Xi = N Xi` is FALSE -- the cross-block entries of `P Xi` need
  not vanish -- and the truncation is what repairs it.
* The chart commutes with `Xi` (the bundle's `assembly_commutes` field), hence with
  `Q` (`commute_rangeProjection_of_commute`); the block indicator commutes with `Xi`
  by block diagonality, hence with `Q`, so `Q` is block diagonal; and the truncation
  minus `N` annihilates `Xi`, hence `Q` (`mul_rangeProjection_eq_zero_of_mul_eq_zero`).
  Those three transfers give `trace_projection_mul_rangeProjection`:

      `tr(P Q) = sum_c (value + t_c) Q_cc` .

* `tr Xi = 1` forces `Xi` nonzero, so `sum_c Q_cc = tr Q >= 1`; the diagonal of a
  symmetric idempotent lies in `[0,1]` and the weights sum to one, so
  `sum_c t_c Q_cc <= 1`; and `value < 0` then gives `tr(P Q) <= value + 1 < 1`.
* `P Q` is a symmetric idempotent, and a NONZERO one has trace at least one
  (`one_le_trace_of_symmetricIdempotent_of_ne_zero`, one application of the discrete
  Cauchy--Schwarz inequality to a fixed column).  So `P Q = 0`, so `P Xi = P Q Xi = 0`,
  so `tr(P Xi) = 0`.  The shipped forced diagonal
  `Gtz.trace_projection_mul_multiplier_of_isChartStationaryData` says
  `tr(P Xi) = value + 1/size`, and the value is pinned.

INTEGRALITY IS THE CRUX, and it is why the range projection has to be built.  The same
trace read against `Xi` itself gives only `value + 1/size >= 0`, which is the shipped
floor.  Read against `Q` it gives a quantity that is `0` or at least `1`, and `< 1`.

## What the proof does NOT use, stated because the sibling's header says otherwise

* ADMISSIBILITY.  `Gtz.IsChartArgmaxValue` appears nowhere in the value theorem, and
  `eliminatesChartTwoBlockValue_three` binds it and discards it.  The sibling header's
  justification for calling it load-bearing cites the uniform `(4,2)` witness
  `Gtz.chartTwoBlockUniformProjection_isChartStationaryData`, which lives at `size = 4`,
  where the rank-three statement is vacuous because two occupied blocks force
  `size = 2 * rank = 6`.  THAT BULLET NEEDS REVISION IN THE SIBLING; it is not revised
  here, because this file does not own that file.
* THE RANK.  The value theorem holds at every `(size, rank)`.  Rank three enters only
  in `eliminatesChartTwoBlockValue_three`, where `size = 6` is what makes `-1/6` a root
  of the `(6,3)` eliminant.
* BLOCK NONEMPTINESS.  `chosenSubset` and its complement partition the atoms whether or
  not both are inhabited, so the value theorem needs neither.  Nonemptiness is used
  only to pin `size = 2 * rank`.
* THE CAUCHY--BINET VALUE FLOOR.  `-3/20` is not load-bearing for this class.  The
  theorem lands on `-1/size`, which the SHIPPED strict floor
  `Gtz.neg_inv_size_lt_value_of_isChartStationaryData` already removes, and that
  theorem carries exactly the design and the admissibility the class closure carries
  anyway.  Cauchy--Binet still enters, through that strict floor; the VALUE floor
  `Gtz.cauchyBinetValueFloor` does not.  FLOOR-CB remains load-bearing for the
  Handelman interval certificate as an object, and for nothing else here.

What the proof DOES use, and where: the negativity of the value, exactly once, in the
trace bound, with no substitute -- at `value = 1/3` with pairwise distinct weights the
same bound reads `3 = 6/3 + 1` and is TIGHT; and the strict positivity of the weights,
exactly once, in `sum_c t_c Q_cc <= 1`.

## What this buys, at its true size

`zero_le_value_of_isChartTwoBlockFamily_of_design` and
`not_isChartStationaryData_of_isChartTwoBlockFamily_of_design_of_negativeValue` are
`Gtz.zero_le_value_of_isChartTwoBlockFamily_of_eliminates_of_design` and
`Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_negativeValue` with
`heliminates` and `hrank` BOTH removed.

Read the remaining hypotheses honestly.  They are `Gtz.IsChartStationaryData`, whose
variational derivation is not formalized and which is satisfied at admissible
non-minima; `Gtz.IsChartArgmaxValue`, the chart-side argmax field, which the strict
floor needs; and a design behind the chart, which Cauchy--Binet needs.  Every theorem
in this arc carries those three.  What is gone is the class-specific hypothesis.

This covers ONE class of the `(6,3)` covering census.  The census has 2069 orbits
after Caratheodory; the other 2068 are untouched by this file and nothing here bears
on them.  `(6,3)` is not closed.

## The rank-three witness, so nothing here is a statement about the empty set

`chartTwoBlockTripleProjection_isChartStationaryData` is an exact RATIONAL `(6,3)`
two-block datum at `value = -1/6 = -1/size`: uniform weights `1/6`, chart
`P = 1 - u uT - w wT - z zT` with `u`, `w` the two triples' normalised all-ones
directions and `z = (1,-1,0,1,-1,0)/2`, and assembly `1/6` inside the blocks and `0`
across.  The chart annihilates both tight directions, so the gap sends each to `-1/6`
times itself (`chartTwoBlockTripleGap_mulVec_support`).  The value theorem therefore
cannot be strengthened to
emptiness AT RANK THREE, where the shipped `(4,2)` uniform witness is vacuous, and
`eliminatesChartTwoBlockValue_three` is not vacuously true.

`not_chartTwoBlockTriple_isChartArgmaxValue` proves the witness INADMISSIBLE, by one
completed square on the triple `{0,1,5}`, where the gap's least eigenvalue is `+1/6`.
That is why it does not contradict the shipped strict floor, and it is the mechanized
form of the numerical note in the header of `Gtz.Quantitative.ChartTwoBlock` about
roots at `-1/6` with uniform weights.

## The cofactor certificates -- CORROBORATION OF THE ELIMINANT, NEVER THE DISCHARGE

`twoBlockEliminantCubic_eq_coreCofactorCombination` and
`twoBlockEliminantCubic_eq_couplingCofactorCombination` are two exact ideal
memberships over the rationals, in three and four variables, each exhibiting the
shipped eliminant as a cofactor combination of the generators of one gauge-fixed
branch of the two-block system.  Both are checked by `ring`: the verification is an
identity check and does not re-run any elimination.
`blockLevelSum_cubic_eq_idempotentCombination` is the pencil behind them -- "a sum of
two idempotent scalars is `0`, `1` or `2`" -- from which the eliminant's degree, its
leading coefficient and all three of its roots follow with no Groebner computation at
all.

NO SATURATION IS PERFORMED ANYWHERE IN THIS FILE.  Neither cofactor identity divides
by anything, carries a `g^N` multiplier, or invokes a nonvanishing side polynomial;
both are plain ideal memberships in the polynomial ring.  That is worth its own
paragraph, because the one place a saturation would naturally have entered is the
total multiplier mass `sum_c tau_c = 1 + 6 value`, which IS the factor `6 value + 1`
of the eliminant, whose root `-1/6` is exactly the value this file's theorem lands on.
Normalising by that mass would have deleted the whole content and manufactured a false
certificate.

NEITHER IDENTITY IS THE DISCHARGE, and no cofactor list could be.  The elimination
step has a SIGN antecedent, `value < 0`, and an ideal membership cannot see a sign.
The cofactors also cover only the branch in which each block carries a rank-one
multiplier, hence a single weight level per block; the trace argument is unrestricted
in multiplier rank.

## Provenance of the outside-Lean checks, quoted as what they are

The elimination ideal of the core system in `(g, p, q)` and of the rank-one branch
with the off-block coupling in `(g, p, q, c)` was recomputed by lexicographic Groebner
basis with the value variable last, in sympy, INDEPENDENTLY of the msolve run quoted
in the sibling's header, and is exactly `<108 g^3 - 108 g^2 + 9 g + 5>` in both cases
-- not a proper divisor, not a proper multiple, not a power.  Both cofactor identities
were expanded to residual exactly zero in exact rational arithmetic before being
transcribed.  None of that is inside Lean and none of it is a proof; what is inside
Lean is the two `ring`-checked identities, and they do not depend on it.

## Inherited honesty

Everything here is conditional on `Gtz.IsChartStationaryData`, which is a HYPOTHESIS:
the variational derivation that would produce it is not formalized, the system is
NECESSARY only, and it is satisfied at admissible non-minima.  Read the header of
`Gtz.Quantitative.ChartStationary` before reading anything here as a statement about
the conjecture.  One class of the covering census is one class.
-/
import Mathlib
import Gtz.Quantitative.ChartEmptinessCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## A symmetric-idempotent kit -/

variable {dimension : ℕ}

/-- Every diagonal entry of a symmetric idempotent is the squared length of its own
row: `M_cc = sum_e M_ce^2`. -/
theorem diagonal_eq_sum_sq_of_symmetricIdempotent
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hsymmetric : targetᵀ = target)
    (hidempotent : target * target = target) (atomIndex : Fin dimension) :
    target atomIndex atomIndex = ∑ otherIndex : Fin dimension, target atomIndex otherIndex ^ 2 := by
  have hentry : (target * target) atomIndex atomIndex
      = ∑ otherIndex : Fin dimension,
          target atomIndex otherIndex * target otherIndex atomIndex := Matrix.mul_apply
  rw [hidempotent] at hentry
  rw [hentry]
  refine Finset.sum_congr rfl fun otherIndex _ => ?_
  have hflip : target otherIndex atomIndex = target atomIndex otherIndex := by
    conv_rhs => rw [← hsymmetric]
    rw [Matrix.transpose_apply]
  rw [hflip, pow_two]

/-- A symmetric idempotent has a NONNEGATIVE diagonal. -/
theorem zero_le_diagonal_of_symmetricIdempotent
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hsymmetric : targetᵀ = target)
    (hidempotent : target * target = target) (atomIndex : Fin dimension) :
    0 ≤ target atomIndex atomIndex := by
  rw [diagonal_eq_sum_sq_of_symmetricIdempotent hsymmetric hidempotent atomIndex]
  exact Finset.sum_nonneg fun otherIndex _ => sq_nonneg _

/-- A symmetric idempotent has a diagonal bounded by ONE: the row's squared length
already contains the diagonal entry's own square. -/
theorem diagonal_le_one_of_symmetricIdempotent
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hsymmetric : targetᵀ = target)
    (hidempotent : target * target = target) (atomIndex : Fin dimension) :
    target atomIndex atomIndex ≤ 1 := by
  have hrow := diagonal_eq_sum_sq_of_symmetricIdempotent hsymmetric hidempotent atomIndex
  have hnonneg := zero_le_diagonal_of_symmetricIdempotent hsymmetric hidempotent atomIndex
  have hself : target atomIndex atomIndex ^ 2
      ≤ ∑ otherIndex : Fin dimension, target atomIndex otherIndex ^ 2 :=
    Finset.single_le_sum (f := fun otherIndex => target atomIndex otherIndex ^ 2)
      (fun otherIndex _ => sq_nonneg _) (Finset.mem_univ atomIndex)
  rw [← hrow] at hself
  nlinarith

/-- The trace of a symmetric idempotent is its squared Frobenius norm. -/
theorem trace_eq_sum_sq_of_symmetricIdempotent
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hsymmetric : targetᵀ = target)
    (hidempotent : target * target = target) :
    Matrix.trace target
      = ∑ rowIndex : Fin dimension, ∑ colIndex : Fin dimension, target rowIndex colIndex ^ 2 :=
  Finset.sum_congr rfl fun rowIndex _ =>
    diagonal_eq_sum_sq_of_symmetricIdempotent hsymmetric hidempotent rowIndex

/-- **A NONZERO SYMMETRIC IDEMPOTENT HAS TRACE AT LEAST ONE.**

The only ingredient beyond bookkeeping is the discrete Cauchy--Schwarz inequality.
Pick a nonzero column `v` of `M`; idempotence makes it a fixed vector, `M v = v`,
so coordinatewise `v_c^2 = (sum_e M_ce v_e)^2 <= (sum_e M_ce^2) |v|^2 = M_cc |v|^2`.
Summing over `c` gives `|v|^2 <= (tr M) |v|^2`, and `|v|^2 > 0`. -/
theorem one_le_trace_of_symmetricIdempotent_of_ne_zero
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hsymmetric : targetᵀ = target)
    (hidempotent : target * target = target) (hnonzero : target ≠ 0) :
    1 ≤ Matrix.trace target := by
  obtain ⟨witnessRow, witnessCol, hwitness⟩ : ∃ rowIndex colIndex : Fin dimension,
      target rowIndex colIndex ≠ 0 := by
    by_contra hallZero
    simp only [not_exists, not_not] at hallZero
    exact hnonzero (by ext rowIndex colIndex; simpa using hallZero rowIndex colIndex)
  set column : Fin dimension → ℝ := fun rowIndex => target rowIndex witnessCol with hcolumn
  have hfixed : ∀ rowIndex : Fin dimension,
      ∑ otherIndex : Fin dimension, target rowIndex otherIndex * column otherIndex
        = column rowIndex := by
    intro rowIndex
    have hentry : (target * target) rowIndex witnessCol
        = ∑ otherIndex : Fin dimension,
            target rowIndex otherIndex * target otherIndex witnessCol := Matrix.mul_apply
    rw [hidempotent] at hentry
    exact hentry.symm
  have hlengthPos : 0 < ∑ otherIndex : Fin dimension, column otherIndex ^ 2 := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun otherIndex => column otherIndex ^ 2) (fun otherIndex _ => sq_nonneg _)
      (Finset.mem_univ witnessRow))
    exact pow_pos (abs_pos.mpr hwitness) 2 |>.trans_le (le_of_eq (sq_abs _))
  have hrowBound : ∀ rowIndex : Fin dimension,
      column rowIndex ^ 2
        ≤ target rowIndex rowIndex * ∑ otherIndex : Fin dimension, column otherIndex ^ 2 := by
    intro rowIndex
    have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin dimension))
      (fun otherIndex => target rowIndex otherIndex) column
    rw [hfixed rowIndex] at hcauchy
    rwa [← diagonal_eq_sum_sq_of_symmetricIdempotent hsymmetric hidempotent rowIndex] at hcauchy
  have hsummed : (∑ otherIndex : Fin dimension, column otherIndex ^ 2)
      ≤ Matrix.trace target * ∑ otherIndex : Fin dimension, column otherIndex ^ 2 := by
    have hsum := Finset.sum_le_sum fun rowIndex (_ : rowIndex ∈ Finset.univ) => hrowBound rowIndex
    rwa [← Finset.sum_mul] at hsum
  nlinarith

/-! ## Conjugation by an orthogonal matrix -/

/-- **CONJUGATION BY AN ORTHOGONAL MATRIX IS MULTIPLICATIVE.**  With `Uᵀ U = 1`,
`(U A Uᵀ)(U B Uᵀ) = U (A B) Uᵀ`.  Three of the range-projection facts below are this
one identity read at different `A` and `B`. -/
theorem orthogonalConjugate_mul_orthogonalConjugate
    (orthogonalPart : Matrix (Fin dimension) (Fin dimension) ℝ)
    (horthogonal : orthogonalPartᵀ * orthogonalPart = 1)
    (firstFactor secondFactor : Matrix (Fin dimension) (Fin dimension) ℝ) :
    orthogonalPart * firstFactor * orthogonalPartᵀ
        * (orthogonalPart * secondFactor * orthogonalPartᵀ)
      = orthogonalPart * (firstFactor * secondFactor) * orthogonalPartᵀ := by
  calc orthogonalPart * firstFactor * orthogonalPartᵀ
        * (orthogonalPart * secondFactor * orthogonalPartᵀ)
      = orthogonalPart * firstFactor * (orthogonalPartᵀ * orthogonalPart)
          * (secondFactor * orthogonalPartᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = orthogonalPart * (firstFactor * secondFactor) * orthogonalPartᵀ := by
        rw [horthogonal, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

/-- **CONJUGATION BY AN ORTHOGONAL MATRIX IS INVERTIBLE**: with `U Uᵀ = 1`,
conjugating `Uᵀ A U` back by `U` returns `A`. -/
theorem orthogonalConjugate_orthogonalConjugate_symm
    (orthogonalPart : Matrix (Fin dimension) (Fin dimension) ℝ)
    (horthogonal : orthogonalPart * orthogonalPartᵀ = 1)
    (conjugatedTarget : Matrix (Fin dimension) (Fin dimension) ℝ) :
    orthogonalPart * (orthogonalPartᵀ * conjugatedTarget * orthogonalPart) * orthogonalPartᵀ
      = conjugatedTarget := by
  calc orthogonalPart * (orthogonalPartᵀ * conjugatedTarget * orthogonalPart) * orthogonalPartᵀ
      = orthogonalPart * orthogonalPartᵀ * conjugatedTarget * (orthogonalPart * orthogonalPartᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = conjugatedTarget := by rw [horthogonal, Matrix.one_mul, Matrix.mul_one]

/-- **CONJUGATION BY AN ORTHOGONAL MATRIX IS INJECTIVE.**  Equal conjugates have
equal middles. -/
theorem eq_of_orthogonalConjugate_eq
    (orthogonalPart : Matrix (Fin dimension) (Fin dimension) ℝ)
    (horthogonal : orthogonalPartᵀ * orthogonalPart = 1)
    {firstMiddle secondMiddle : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hconjugate : orthogonalPart * firstMiddle * orthogonalPartᵀ
      = orthogonalPart * secondMiddle * orthogonalPartᵀ) :
    firstMiddle = secondMiddle := by
  have hcollapse : ∀ middle : Matrix (Fin dimension) (Fin dimension) ℝ,
      orthogonalPartᵀ * (orthogonalPart * middle * orthogonalPartᵀ) * orthogonalPart = middle := by
    intro middle
    simp only [Matrix.mul_assoc]
    rw [horthogonal, Matrix.mul_one, ← Matrix.mul_assoc, horthogonal, Matrix.one_mul]
  calc firstMiddle
      = orthogonalPartᵀ * (orthogonalPart * firstMiddle * orthogonalPartᵀ) * orthogonalPart :=
        (hcollapse firstMiddle).symm
    _ = orthogonalPartᵀ * (orthogonalPart * secondMiddle * orthogonalPartᵀ) * orthogonalPart := by
        rw [hconjugate]
    _ = secondMiddle := hcollapse secondMiddle

/-! ## Transfer along a coarsening of the spectral levels

Two abstract lemmas about conjugated diagonals.  Both range-projection transfers
below are instances, with the level function `secondScale` a coarsening of
`firstScale`; nothing in either mentions eigenvalues, so neither is exposed to the
dependent-rewrite trap that the spectral decomposition carries. -/

/-- **THE COMMUTANT TRANSFER, ABSTRACTLY.**  If `secondScale` separates no pair that
`firstScale` does not separate, then everything commuting with `U diag(firstScale) Uᵀ`
commutes with `U diag(secondScale) Uᵀ`. -/
theorem commute_diagonalConjugate_of_commute
    (orthogonalPart : Matrix (Fin dimension) (Fin dimension) ℝ)
    (hleftOrthogonal : orthogonalPartᵀ * orthogonalPart = 1)
    (hrightOrthogonal : orthogonalPart * orthogonalPartᵀ = 1)
    (firstScale secondScale : Fin dimension → ℝ)
    (hcoarsens : ∀ rowIndex colIndex : Fin dimension,
      secondScale rowIndex ≠ secondScale colIndex → firstScale rowIndex ≠ firstScale colIndex)
    (other : Matrix (Fin dimension) (Fin dimension) ℝ)
    (hcommute : other * (orthogonalPart * Matrix.diagonal firstScale * orthogonalPartᵀ)
      = orthogonalPart * Matrix.diagonal firstScale * orthogonalPartᵀ * other) :
    other * (orthogonalPart * Matrix.diagonal secondScale * orthogonalPartᵀ)
      = orthogonalPart * Matrix.diagonal secondScale * orthogonalPartᵀ * other := by
  obtain ⟨conjugated, hrestore⟩ : ∃ conjugated : Matrix (Fin dimension) (Fin dimension) ℝ,
      orthogonalPart * conjugated * orthogonalPartᵀ = other :=
    ⟨orthogonalPartᵀ * other * orthogonalPart,
      orthogonalConjugate_orthogonalConjugate_symm orthogonalPart hrightOrthogonal other⟩
  have hconjugatedCommute : conjugated * Matrix.diagonal firstScale
      = Matrix.diagonal firstScale * conjugated := by
    refine eq_of_orthogonalConjugate_eq orthogonalPart hleftOrthogonal ?_
    rw [← orthogonalConjugate_mul_orthogonalConjugate orthogonalPart hleftOrthogonal conjugated
        (Matrix.diagonal firstScale),
      ← orthogonalConjugate_mul_orthogonalConjugate orthogonalPart hleftOrthogonal
        (Matrix.diagonal firstScale) conjugated, hrestore]
    exact hcommute
  have hsecondCommute : conjugated * Matrix.diagonal secondScale
      = Matrix.diagonal secondScale * conjugated := by
    ext rowIndex colIndex
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hsame : secondScale colIndex = secondScale rowIndex
    · rw [hsame]; ring
    · rw [offDiagonal_eq_zero_of_commute_diagonal conjugated firstScale hconjugatedCommute
        (hcoarsens rowIndex colIndex fun hequal => hsame hequal.symm)]
      ring
  rw [← hrestore, orthogonalConjugate_mul_orthogonalConjugate orthogonalPart hleftOrthogonal,
    orthogonalConjugate_mul_orthogonalConjugate orthogonalPart hleftOrthogonal, hsecondCommute]

/-- **THE ANNIHILATOR TRANSFER, ABSTRACTLY.**  If `secondScale` vanishes wherever
`firstScale` does, then everything annihilating `U diag(firstScale) Uᵀ` from the left
annihilates `U diag(secondScale) Uᵀ`. -/
theorem mul_diagonalConjugate_eq_zero_of_mul_eq_zero
    (orthogonalPart : Matrix (Fin dimension) (Fin dimension) ℝ)
    (hleftOrthogonal : orthogonalPartᵀ * orthogonalPart = 1)
    (firstScale secondScale : Fin dimension → ℝ)
    (hsupported : ∀ eigenIndex : Fin dimension, firstScale eigenIndex = 0 →
      secondScale eigenIndex = 0)
    (other : Matrix (Fin dimension) (Fin dimension) ℝ)
    (hannihilates : other * (orthogonalPart * Matrix.diagonal firstScale * orthogonalPartᵀ) = 0) :
    other * (orthogonalPart * Matrix.diagonal secondScale * orthogonalPartᵀ) = 0 := by
  have hfirstVanish : other * orthogonalPart * Matrix.diagonal firstScale = 0 := by
    have hright := congrArg (fun candidate => candidate * orthogonalPart) hannihilates
    simp only [Matrix.zero_mul] at hright
    calc other * orthogonalPart * Matrix.diagonal firstScale
        = other * (orthogonalPart * Matrix.diagonal firstScale * orthogonalPartᵀ)
            * orthogonalPart := by
          simp only [Matrix.mul_assoc]
          rw [hleftOrthogonal, Matrix.mul_one]
      _ = 0 := hright
  have hsecondVanish : other * orthogonalPart * Matrix.diagonal secondScale = 0 := by
    ext rowIndex eigenIndex
    rw [Matrix.mul_diagonal, Matrix.zero_apply]
    have hentry : (other * orthogonalPart) rowIndex eigenIndex * firstScale eigenIndex = 0 := by
      have hrow := congrFun (congrFun hfirstVanish rowIndex) eigenIndex
      rwa [Matrix.mul_diagonal, Matrix.zero_apply] at hrow
    rcases mul_eq_zero.mp hentry with hfactor | hfactor
    · rw [hfactor, zero_mul]
    · rw [hsupported eigenIndex hfactor, mul_zero]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hsecondVanish, Matrix.zero_mul]

/-! ## The range projection of a symmetric matrix -/

/-- The spectral indicator: one at every nonzero eigenvalue, zero at every zero one. -/
noncomputable def spectralIndicator {target : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hhermitian : target.IsHermitian) : Fin dimension → ℝ :=
  fun eigenIndex => if hhermitian.eigenvalues eigenIndex = 0 then (0 : ℝ) else 1

/-- **THE ORTHOGONAL PROJECTION ONTO THE RANGE** of a symmetric real matrix: the
spectral decomposition with every nonzero eigenvalue replaced by one and every zero
eigenvalue left at zero. -/
noncomputable def rangeProjection {target : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hhermitian : target.IsHermitian) : Matrix (Fin dimension) (Fin dimension) ℝ :=
  (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)
    * Matrix.diagonal (spectralIndicator hhermitian)
    * (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)ᵀ

/-- The eigenvector matrix is orthogonal: `Uᵀ U = 1`. -/
theorem transpose_mul_eigenvectorUnitary_self
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hhermitian : target.IsHermitian) :
    (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)ᵀ
        * (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ) = 1 := by
  have hstar := hhermitian.eigenvectorUnitary.2.1
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hstar

/-- The eigenvector matrix is orthogonal on the other side: `U Uᵀ = 1`. -/
theorem eigenvectorUnitary_mul_transpose_self
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hhermitian : target.IsHermitian) :
    (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)
        * (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)ᵀ = 1 := by
  have hstar := hhermitian.eigenvectorUnitary.2.2
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hstar

/-- The spectral theorem in the real transpose form: `A = U diag(lambda) Uᵀ`. -/
theorem eq_eigenvectorUnitary_mul_diagonal_mul_transpose
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hhermitian : target.IsHermitian) :
    target = (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)
      * Matrix.diagonal hhermitian.eigenvalues
      * (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)ᵀ := by
  have hcast : (RCLike.ofReal ∘ hhermitian.eigenvalues : Fin dimension → ℝ)
      = hhermitian.eigenvalues := by
    funext eigenIndex
    simp
  have hspectral := hhermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, hcast] at hspectral
  exact hspectral

/-- The spectral indicator is idempotent pointwise. -/
theorem spectralIndicator_mul_self
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hhermitian : target.IsHermitian)
    (eigenIndex : Fin dimension) :
    spectralIndicator hhermitian eigenIndex * spectralIndicator hhermitian eigenIndex
      = spectralIndicator hhermitian eigenIndex := by
  by_cases hzero : hhermitian.eigenvalues eigenIndex = 0 <;> simp [spectralIndicator, hzero]

/-- The spectral indicator is the identity on the eigenvalues. -/
theorem spectralIndicator_mul_eigenvalue
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hhermitian : target.IsHermitian)
    (eigenIndex : Fin dimension) :
    spectralIndicator hhermitian eigenIndex * hhermitian.eigenvalues eigenIndex
      = hhermitian.eigenvalues eigenIndex := by
  by_cases hzero : hhermitian.eigenvalues eigenIndex = 0 <;> simp [spectralIndicator, hzero]

/-- The spectral indicator is a COARSENING of the eigenvalues: it separates only pairs
the eigenvalues already separate. -/
theorem eigenvalues_ne_of_spectralIndicator_ne
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hhermitian : target.IsHermitian)
    (rowIndex colIndex : Fin dimension)
    (hdistinct : spectralIndicator hhermitian rowIndex ≠ spectralIndicator hhermitian colIndex) :
    hhermitian.eigenvalues rowIndex ≠ hhermitian.eigenvalues colIndex := by
  intro hequal
  exact hdistinct (by simp only [spectralIndicator, hequal])

/-- The spectral indicator vanishes wherever the eigenvalue does. -/
theorem spectralIndicator_eq_zero_of_eigenvalue_eq_zero
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hhermitian : target.IsHermitian)
    (eigenIndex : Fin dimension) (hzero : hhermitian.eigenvalues eigenIndex = 0) :
    spectralIndicator hhermitian eigenIndex = 0 := by
  simp [spectralIndicator, hzero]

/-- **The range projection is SYMMETRIC.** -/
theorem rangeProjection_transpose {target : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hhermitian : target.IsHermitian) :
    (rangeProjection hhermitian)ᵀ = rangeProjection hhermitian := by
  simp only [rangeProjection, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- **The range projection is IDEMPOTENT.** -/
theorem rangeProjection_mul_self {target : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hhermitian : target.IsHermitian) :
    rangeProjection hhermitian * rangeProjection hhermitian = rangeProjection hhermitian := by
  have hdiagonal : Matrix.diagonal (spectralIndicator hhermitian)
      * Matrix.diagonal (spectralIndicator hhermitian)
      = Matrix.diagonal (spectralIndicator hhermitian) := by
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext (spectralIndicator_mul_self hhermitian))
  rw [rangeProjection, orthogonalConjugate_mul_orthogonalConjugate _
    (transpose_mul_eigenvectorUnitary_self hhermitian), hdiagonal]

/-- **The range projection FIXES the matrix**: `Q A = A`, so the column space of `A`
lies inside the range of `Q`. -/
theorem rangeProjection_mul_eq_self {target : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hhermitian : target.IsHermitian) :
    rangeProjection hhermitian * target = target := by
  have hdiagonal : Matrix.diagonal (spectralIndicator hhermitian)
      * Matrix.diagonal hhermitian.eigenvalues = Matrix.diagonal hhermitian.eigenvalues := by
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext (spectralIndicator_mul_eigenvalue hhermitian))
  have hconjugated : rangeProjection hhermitian
      * ((hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)
          * Matrix.diagonal hhermitian.eigenvalues
          * (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)ᵀ)
      = (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)
          * Matrix.diagonal hhermitian.eigenvalues
          * (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)ᵀ := by
    rw [rangeProjection, orthogonalConjugate_mul_orthogonalConjugate _
      (transpose_mul_eigenvectorUnitary_self hhermitian), hdiagonal]
  rwa [← eq_eigenvectorUnitary_mul_diagonal_mul_transpose hhermitian] at hconjugated

/-- The range projection's trace counts the nonzero eigenvalues. -/
theorem trace_rangeProjection_eq_sum_spectralIndicator
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hhermitian : target.IsHermitian) :
    Matrix.trace (rangeProjection hhermitian)
      = ∑ eigenIndex : Fin dimension, spectralIndicator hhermitian eigenIndex := by
  rw [rangeProjection, Matrix.trace_mul_comm _
      ((hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)ᵀ),
    ← Matrix.mul_assoc, transpose_mul_eigenvectorUnitary_self hhermitian, Matrix.one_mul,
    Matrix.trace_diagonal]

/-- **THE RANGE PROJECTION IS NONTRIVIAL** when the matrix is: a matrix with nonzero
trace has a nonzero eigenvalue, and the projection's trace counts exactly those. -/
theorem one_le_trace_rangeProjection_of_trace_ne_zero
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hhermitian : target.IsHermitian)
    (htrace : Matrix.trace target ≠ 0) :
    1 ≤ Matrix.trace (rangeProjection hhermitian) := by
  obtain ⟨witnessIndex, hwitness⟩ : ∃ eigenIndex : Fin dimension,
      hhermitian.eigenvalues eigenIndex ≠ 0 := by
    by_contra hallZero
    simp only [not_exists, not_not] at hallZero
    refine htrace ?_
    have hvanish : Matrix.diagonal hhermitian.eigenvalues
        = (0 : Matrix (Fin dimension) (Fin dimension) ℝ) := by
      rw [← Matrix.diagonal_zero]
      exact congrArg Matrix.diagonal (funext hallZero)
    rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hhermitian, hvanish, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.trace_zero]
  rw [trace_rangeProjection_eq_sum_spectralIndicator]
  have hwitnessValue : spectralIndicator hhermitian witnessIndex = 1 := by
    simp [spectralIndicator, hwitness]
  have hbound := Finset.single_le_sum
    (f := fun eigenIndex : Fin dimension => spectralIndicator hhermitian eigenIndex)
    (fun eigenIndex _ => by
      by_cases hzero : hhermitian.eigenvalues eigenIndex = 0 <;> simp [spectralIndicator, hzero])
    (Finset.mem_univ witnessIndex)
  rwa [hwitnessValue] at hbound

/-- **THE COMMUTANT TRANSFER.**  Anything commuting with a symmetric matrix commutes
with its range projection. -/
theorem commute_rangeProjection_of_commute
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hhermitian : target.IsHermitian)
    {other : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hcommute : other * target = target * other) :
    other * rangeProjection hhermitian = rangeProjection hhermitian * other := by
  have hconverted : other
      * ((hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)
          * Matrix.diagonal hhermitian.eigenvalues
          * (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)ᵀ)
      = (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)
          * Matrix.diagonal hhermitian.eigenvalues
          * (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)ᵀ
        * other := by
    rw [← eq_eigenvectorUnitary_mul_diagonal_mul_transpose hhermitian]
    exact hcommute
  exact commute_diagonalConjugate_of_commute _
    (transpose_mul_eigenvectorUnitary_self hhermitian)
    (eigenvectorUnitary_mul_transpose_self hhermitian) _ (spectralIndicator hhermitian)
    (eigenvalues_ne_of_spectralIndicator_ne hhermitian) other hconverted

/-- **THE ANNIHILATOR TRANSFER.**  Anything annihilating a symmetric matrix from the
left annihilates its range projection: the two have the same column space. -/
theorem mul_rangeProjection_eq_zero_of_mul_eq_zero
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hhermitian : target.IsHermitian)
    {other : Matrix (Fin dimension) (Fin dimension) ℝ} (hannihilates : other * target = 0) :
    other * rangeProjection hhermitian = 0 := by
  have hconverted : other
      * ((hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)
          * Matrix.diagonal hhermitian.eigenvalues
          * (hhermitian.eigenvectorUnitary : Matrix (Fin dimension) (Fin dimension) ℝ)ᵀ)
      = 0 := by
    rw [← eq_eigenvectorUnitary_mul_diagonal_mul_transpose hhermitian]
    exact hannihilates
  exact mul_diagonalConjugate_eq_zero_of_mul_eq_zero _
    (transpose_mul_eigenvectorUnitary_self hhermitian) _ (spectralIndicator hhermitian)
    (spectralIndicator_eq_zero_of_eigenvalue_eq_zero hhermitian) other hconverted

/-! ## The two-block chart, block by block -/

variable {size : ℕ} {activeIndex : Type*}
variable {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
  {value : ℝ} {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
  {chosenSubset : Finset (Fin size)}

/-- **THE BLOCK-DIAGONAL TRUNCATION** of a matrix at a two-block partition: the entries
whose two atoms lie in the same block are kept, the rest are set to zero. -/
def chartBlockDiagonalPart (chosenSubset : Finset (Fin size))
    (target : Matrix (Fin size) (Fin size) ℝ) : Matrix (Fin size) (Fin size) ℝ :=
  Matrix.of fun rowAtom colAtom =>
    if rowAtom ∈ chosenSubset ↔ colAtom ∈ chosenSubset then target rowAtom colAtom else 0

theorem chartBlockDiagonalPart_apply_of_sameBlock (chosenSubset : Finset (Fin size))
    (target : Matrix (Fin size) (Fin size) ℝ) {rowAtom colAtom : Fin size}
    (hsame : rowAtom ∈ chosenSubset ↔ colAtom ∈ chosenSubset) :
    chartBlockDiagonalPart chosenSubset target rowAtom colAtom = target rowAtom colAtom := by
  rw [chartBlockDiagonalPart, Matrix.of_apply, if_pos hsame]

theorem chartBlockDiagonalPart_apply_of_crossBlock (chosenSubset : Finset (Fin size))
    (target : Matrix (Fin size) (Fin size) ℝ) {rowAtom colAtom : Fin size}
    (hcross : ¬ (rowAtom ∈ chosenSubset ↔ colAtom ∈ chosenSubset)) :
    chartBlockDiagonalPart chosenSubset target rowAtom colAtom = 0 := by
  rw [chartBlockDiagonalPart, Matrix.of_apply, if_neg hcross]

/-- **THE ASSEMBLY IS BLOCK DIAGONAL**, in the symmetric form: the entry at two atoms
of DIFFERENT blocks vanishes, whichever of the two carries the chosen block. -/
theorem chartMultiplierAssembly_apply_eq_zero_of_notSameBlock
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    {rowAtom colAtom : Fin size}
    (hcross : ¬ (rowAtom ∈ chosenSubset ↔ colAtom ∈ chosenSubset)) :
    chartMultiplierAssembly activeSet activeWeight tightDir rowAtom colAtom = 0 := by
  by_cases hrow : rowAtom ∈ chosenSubset
  · exact chartMultiplierAssembly_apply_eq_zero_of_crossBlock hdata hfamily hrow
      fun hcol => hcross ⟨fun _ => hcol, fun _ => hrow⟩
  · have hcol : colAtom ∈ chosenSubset := by
      by_contra hnotMem
      exact hcross ⟨fun hmem => absurd hmem hrow, fun hmem => absurd hmem hnotMem⟩
    rw [chartMultiplierAssembly_apply_comm]
    exact chartMultiplierAssembly_apply_eq_zero_of_crossBlock hdata hfamily hcol hrow

/-- The SHIFTED WEIGHT DIAGONAL `N = value + diag t`, the matrix the chart acts as on
each block's multiplier range. -/
noncomputable def chartShiftedWeightDiagonal (weight : Fin size → ℝ) (value : ℝ) :
    Matrix (Fin size) (Fin size) ℝ :=
  Matrix.diagonal fun atomIndex => value + weight atomIndex

/-- **THE BLOCKWISE EIGEN-RELATION, AS A MATRIX IDENTITY.**  The block-diagonal
truncation of the chart acts on the assembly exactly as the shifted weight diagonal:

    `blockPart(P) Xi = N Xi` .

Inside a block this is the shipped same-block relation
`Gtz.projection_mul_multiplier_apply_of_sameBlock`; across blocks both sides vanish,
the left because a nonzero factor would need an atom in both blocks at once and the
right because the assembly's cross-block entries are zero.

The GLOBAL identity `P Xi = N Xi` is FALSE — the cross-block entries of `P Xi` need
not vanish — which is exactly why the truncation appears. -/
theorem chartBlockDiagonalPart_mul_multiplier
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset) :
    chartBlockDiagonalPart chosenSubset projection
        * chartMultiplierAssembly activeSet activeWeight tightDir
      = chartShiftedWeightDiagonal weight value
        * chartMultiplierAssembly activeSet activeWeight tightDir := by
  ext rowAtom colAtom
  rw [Matrix.mul_apply, chartShiftedWeightDiagonal, Matrix.diagonal_mul]
  by_cases hsame : rowAtom ∈ chosenSubset ↔ colAtom ∈ chosenSubset
  · have hterms : ∀ midAtom : Fin size,
        chartBlockDiagonalPart chosenSubset projection rowAtom midAtom
            * chartMultiplierAssembly activeSet activeWeight tightDir midAtom colAtom
          = projection rowAtom midAtom
            * chartMultiplierAssembly activeSet activeWeight tightDir midAtom colAtom := by
      intro midAtom
      by_cases hrowMid : rowAtom ∈ chosenSubset ↔ midAtom ∈ chosenSubset
      · rw [chartBlockDiagonalPart_apply_of_sameBlock chosenSubset projection hrowMid]
      · rw [chartBlockDiagonalPart_apply_of_crossBlock chosenSubset projection hrowMid,
          chartMultiplierAssembly_apply_eq_zero_of_notSameBlock hdata hfamily
            fun hmidCol => hrowMid (hsame.trans hmidCol.symm)]
        ring
    rw [Finset.sum_congr rfl fun midAtom _ => hterms midAtom, ← Matrix.mul_apply]
    exact projection_mul_multiplier_apply_of_sameBlock hdata hfamily hsame
  · have hcolVanish : chartMultiplierAssembly activeSet activeWeight tightDir rowAtom colAtom
        = 0 := chartMultiplierAssembly_apply_eq_zero_of_notSameBlock hdata hfamily hsame
    rw [hcolVanish, mul_zero]
    refine Finset.sum_eq_zero fun midAtom _ => ?_
    by_cases hrowMid : rowAtom ∈ chosenSubset ↔ midAtom ∈ chosenSubset
    · rw [chartMultiplierAssembly_apply_eq_zero_of_notSameBlock hdata hfamily
        fun hmidCol => hsame (hrowMid.trans hmidCol), mul_zero]
    · rw [chartBlockDiagonalPart_apply_of_crossBlock chosenSubset projection hrowMid, zero_mul]

/-- The indicator of the chosen block, as a diagonal scale. -/
noncomputable def chartBlockIndicator (chosenSubset : Finset (Fin size)) : Fin size → ℝ :=
  fun atomIndex => if atomIndex ∈ chosenSubset then (1 : ℝ) else 0

/-- Two atoms of different blocks have different block indicators. -/
theorem chartBlockIndicator_ne_of_notSameBlock (chosenSubset : Finset (Fin size))
    {rowAtom colAtom : Fin size}
    (hcross : ¬ (rowAtom ∈ chosenSubset ↔ colAtom ∈ chosenSubset)) :
    chartBlockIndicator chosenSubset rowAtom ≠ chartBlockIndicator chosenSubset colAtom := by
  by_cases hrow : rowAtom ∈ chosenSubset
  · have hcol : colAtom ∉ chosenSubset := fun hmem => hcross ⟨fun _ => hmem, fun _ => hrow⟩
    simp [chartBlockIndicator, hrow, hcol]
  · have hcol : colAtom ∈ chosenSubset := by
      by_contra hnotMem
      exact hcross ⟨fun hmem => absurd hmem hrow, fun hmem => absurd hmem hnotMem⟩
    simp [chartBlockIndicator, hrow, hcol]

/-- **THE ASSEMBLY COMMUTES WITH THE BLOCK INDICATOR** — a restatement of block
diagonality, in the form the commutant transfer consumes. -/
theorem blockIndicator_mul_multiplier_comm
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset) :
    Matrix.diagonal (chartBlockIndicator chosenSubset)
        * chartMultiplierAssembly activeSet activeWeight tightDir
      = chartMultiplierAssembly activeSet activeWeight tightDir
        * Matrix.diagonal (chartBlockIndicator chosenSubset) := by
  ext rowAtom colAtom
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hsame : rowAtom ∈ chosenSubset ↔ colAtom ∈ chosenSubset
  · have hindicator : chartBlockIndicator chosenSubset rowAtom
        = chartBlockIndicator chosenSubset colAtom := by
      by_cases hrow : rowAtom ∈ chosenSubset
      · simp [chartBlockIndicator, hrow, hsame.mp hrow]
      · have hcol : colAtom ∉ chosenSubset := fun hmem => hrow (hsame.mpr hmem)
        simp [chartBlockIndicator, hrow, hcol]
    rw [hindicator]
    ring
  · rw [chartMultiplierAssembly_apply_eq_zero_of_notSameBlock hdata hfamily hsame]
    ring

/-! ## The trace of the chart against the multiplier's range projection -/

/-- The assembly is symmetric, in Mathlib's Hermitian vocabulary. -/
theorem isHermitian_chartMultiplierAssembly_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    (chartMultiplierAssembly activeSet activeWeight tightDir).IsHermitian :=
  (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata).1

/-- **THE MULTIPLIER'S RANGE PROJECTION IS BLOCK DIAGONAL.**  The block indicator
commutes with the assembly, hence with its range projection, and a matrix commuting
with a diagonal separates the indices whose diagonal entries differ. -/
theorem rangeProjection_apply_eq_zero_of_notSameBlock
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hhermitian : (chartMultiplierAssembly activeSet activeWeight tightDir).IsHermitian)
    {rowAtom colAtom : Fin size}
    (hcross : ¬ (rowAtom ∈ chosenSubset ↔ colAtom ∈ chosenSubset)) :
    rangeProjection hhermitian rowAtom colAtom = 0 :=
  offDiagonal_eq_zero_of_commute_diagonal _ (chartBlockIndicator chosenSubset)
    (commute_rangeProjection_of_commute hhermitian
      (blockIndicator_mul_multiplier_comm hdata hfamily)).symm
    (chartBlockIndicator_ne_of_notSameBlock chosenSubset hcross)

/-- **THE TRACE IDENTITY THE WHOLE ARGUMENT TURNS ON**:

    `tr(P Q) = sum_c (value + t_c) Q_cc` ,

with `Q` the range projection of the assembly.  Three facts meet here.  The
projection is block diagonal, so only same-block entries of the chart survive the
diagonal of `P Q`; on those the block-diagonal truncation of the chart agrees with
the chart; and the truncation acts on the assembly's range exactly as the shifted
weight diagonal, which the annihilator transfer carries from the assembly to its
range projection. -/
theorem trace_projection_mul_rangeProjection
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hhermitian : (chartMultiplierAssembly activeSet activeWeight tightDir).IsHermitian) :
    Matrix.trace (projection * rangeProjection hhermitian)
      = ∑ atomIndex : Fin size,
          (value + weight atomIndex) * rangeProjection hhermitian atomIndex atomIndex := by
  have hshift : chartBlockDiagonalPart chosenSubset projection * rangeProjection hhermitian
      = chartShiftedWeightDiagonal weight value * rangeProjection hhermitian := by
    have hannihilate : (chartBlockDiagonalPart chosenSubset projection
        - chartShiftedWeightDiagonal weight value) * rangeProjection hhermitian = 0 := by
      refine mul_rangeProjection_eq_zero_of_mul_eq_zero hhermitian ?_
      rw [Matrix.sub_mul, chartBlockDiagonalPart_mul_multiplier hdata hfamily, sub_self]
    rwa [Matrix.sub_mul, sub_eq_zero] at hannihilate
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  simp only [Matrix.diag_apply]
  have hblockCollapse : (projection * rangeProjection hhermitian) atomIndex atomIndex
      = (chartBlockDiagonalPart chosenSubset projection * rangeProjection hhermitian)
          atomIndex atomIndex := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun midAtom _ => ?_
    by_cases hsame : atomIndex ∈ chosenSubset ↔ midAtom ∈ chosenSubset
    · rw [chartBlockDiagonalPart_apply_of_sameBlock chosenSubset projection hsame]
    · rw [chartBlockDiagonalPart_apply_of_crossBlock chosenSubset projection hsame,
        rangeProjection_apply_eq_zero_of_notSameBlock hdata hfamily hhermitian
          fun hmidAtom => hsame hmidAtom.symm]
      ring
  rw [hblockCollapse, hshift, chartShiftedWeightDiagonal, Matrix.diagonal_mul]

/-! ## The elimination step, discharged -/

/-- **THE TWO-BLOCK VALUE AT A NEGATIVE VALUE IS EXACTLY `-1/size`.**

A chart stationarity datum whose active family is two complementary blocks and whose
value is NEGATIVE has `value = -1/size`, at every `size` and every `rank`.

The proof is a trace argument and needs no case split, no Groebner basis and no
elimination.  Write `Xi` for the assembly, `Q` for the orthogonal projection onto its
range, `N = value + diag t`.  The chart commutes with `Xi`, hence with `Q`, so `P Q`
is a symmetric idempotent; and `tr(P Q) = sum_c (value + t_c) Q_cc` by
`trace_projection_mul_rangeProjection`.  Now `tr Xi = 1` forces `Xi` nonzero, so
`sum_c Q_cc = tr Q >= 1`; the diagonal of a symmetric idempotent is at most one and
the weights sum to one, so `sum_c t_c Q_cc <= 1`; and `value < 0` then gives
`tr(P Q) <= value + 1 < 1`.  A NONZERO symmetric idempotent has trace at least one,
so `P Q = 0`, so `P Xi = P Q Xi = 0`, so `tr(P Xi) = 0`.  The shipped forced diagonal
says `tr(P Xi) = value + 1/size`, and the value is pinned.

WHAT IS NOT USED.  Admissibility (`Gtz.IsChartArgmaxValue`) appears nowhere; nor does
`hasTraceRank`; nor is either block required to be nonempty, because `chosenSubset`
and its complement partition the atoms whether or not both are inhabited.  The
NEGATIVITY is used exactly once, in the trace bound, and there is no substitute for
it: at `value = 1/3` with pairwise distinct weights the same bound reads `3 = 6/3 + 1`
and is TIGHT.

SHARPNESS.  The conclusion cannot be strengthened to emptiness: the shipped `(4,2)`
uniform datum `Gtz.chartTwoBlockUniformProjection_isChartStationaryData` is a
two-block datum at `value = -1/4 = -1/size`.  It is inadmissible, which is why it
does not contradict `Gtz.neg_inv_size_lt_value_of_isChartStationaryData`. -/
theorem value_eq_neg_inv_size_of_isChartTwoBlockFamily_of_negativeValue
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hnegative : value < 0) :
    value = -((size : ℝ))⁻¹ := by
  have hhermitian := isHermitian_chartMultiplierAssembly_of_isChartStationaryData hdata
  have hcommute : projection * rangeProjection hhermitian
      = rangeProjection hhermitian * projection :=
    commute_rangeProjection_of_commute hhermitian hdata.assembly_commutes
  have hproductSymmetric : (projection * rangeProjection hhermitian)ᵀ
      = projection * rangeProjection hhermitian := by
    rw [Matrix.transpose_mul, rangeProjection_transpose hhermitian, hdata.isSymmetric, ← hcommute]
  have hproductIdempotent : projection * rangeProjection hhermitian
      * (projection * rangeProjection hhermitian) = projection * rangeProjection hhermitian := by
    calc projection * rangeProjection hhermitian * (projection * rangeProjection hhermitian)
        = projection * (rangeProjection hhermitian * projection) * rangeProjection hhermitian := by
          simp only [Matrix.mul_assoc]
      _ = projection * (projection * rangeProjection hhermitian) * rangeProjection hhermitian := by
          rw [← hcommute]
      _ = projection * projection * (rangeProjection hhermitian * rangeProjection hhermitian) := by
          simp only [Matrix.mul_assoc]
      _ = projection * rangeProjection hhermitian := by
          rw [hdata.isIdempotent, rangeProjection_mul_self hhermitian]
  have htraceRangeProjection : (1 : ℝ)
      ≤ ∑ atomIndex : Fin size, rangeProjection hhermitian atomIndex atomIndex := by
    refine one_le_trace_rangeProjection_of_trace_ne_zero hhermitian ?_
    rw [trace_chartMultiplierAssembly_of_isChartStationaryData hdata]
    norm_num
  have hweightedBound : ∑ atomIndex : Fin size,
      weight atomIndex * rangeProjection hhermitian atomIndex atomIndex ≤ 1 := by
    have hterms := Finset.sum_le_sum fun atomIndex (_ : atomIndex ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left
        (diagonal_le_one_of_symmetricIdempotent (rangeProjection_transpose hhermitian)
          (rangeProjection_mul_self hhermitian) atomIndex)
        (hdata.weight_pos atomIndex).le
    simp only [mul_one] at hterms
    rwa [hdata.weight_sum_one] at hterms
  have hsplit : ∑ atomIndex : Fin size,
        (value + weight atomIndex) * rangeProjection hhermitian atomIndex atomIndex
      = value * (∑ atomIndex : Fin size, rangeProjection hhermitian atomIndex atomIndex)
        + ∑ atomIndex : Fin size,
            weight atomIndex * rangeProjection hhermitian atomIndex atomIndex := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  have hstrict : Matrix.trace (projection * rangeProjection hhermitian) < 1 := by
    rw [trace_projection_mul_rangeProjection hdata hfamily hhermitian, hsplit]
    nlinarith [mul_nonneg (neg_nonneg.mpr hnegative.le)
      (sub_nonneg.mpr htraceRangeProjection)]
  have hvanish : projection * rangeProjection hhermitian = 0 := by
    by_contra hnonzero
    exact absurd (one_le_trace_of_symmetricIdempotent_of_ne_zero hproductSymmetric
      hproductIdempotent hnonzero) (not_le.mpr hstrict)
  have hassemblyVanish :
      projection * chartMultiplierAssembly activeSet activeWeight tightDir = 0 := by
    calc projection * chartMultiplierAssembly activeSet activeWeight tightDir
        = projection * (rangeProjection hhermitian
            * chartMultiplierAssembly activeSet activeWeight tightDir) := by
          rw [rangeProjection_mul_eq_self hhermitian]
      _ = projection * rangeProjection hhermitian
            * chartMultiplierAssembly activeSet activeWeight tightDir := by
          rw [Matrix.mul_assoc]
      _ = 0 := by rw [hvanish, Matrix.zero_mul]
  have hforced := trace_projection_mul_multiplier_of_isChartStationaryData hdata
  rw [hassemblyVanish, Matrix.trace_zero] at hforced
  linarith

/-- **THE ELIMINATION STEP, DISCHARGED AT RANK THREE.**

`Gtz.EliminatesChartTwoBlockValue 3` — asserted, never proved, in the header of
`Gtz.Quantitative.ChartEmptinessCertificate` — is a THEOREM.

Both blocks occupied forces `size = 2 * rank = 6`
(`Gtz.size_eq_two_mul_rank_of_isChartTwoBlockFamily`), the theorem above pins the
value to `-1/6`, and `-1/6` is a root of the eliminant
(`Gtz.twoBlockEliminantCubic_eq_zero_iff_of_negativeValue`).

The admissibility antecedent `Gtz.IsChartArgmaxValue` is CONSUMED AND UNUSED: the
proof never looks at it.  It is not dropped from the statement because the statement
is the shipped definition, and a hypothesis in a definition is not this file's to
edit; what is recorded here is that discharging the definition does not need it. -/
theorem eliminatesChartTwoBlockValue_three :
    EliminatesChartTwoBlockValue (size := size) (activeIndex := activeIndex) 3 := by
  intro chartProjection chartWeight chartValue chartActiveSet chartActiveSubset chartActiveWeight
    chartTightDir chartChosenSubset hdata _hargmax hfamily hnonempty hnonemptyCompl hnegative
  have hsize : size = 2 * 3 :=
    size_eq_two_mul_rank_of_isChartTwoBlockFamily hdata hfamily hnonempty hnonemptyCompl
  have hvalue :=
    value_eq_neg_inv_size_of_isChartTwoBlockFamily_of_negativeValue hdata hfamily hnegative
  rw [hsize] at hvalue
  norm_num at hvalue
  rw [twoBlockEliminantCubic, hvalue]
  norm_num

/-- **THE TWO-BLOCK CLASS AT A NEGATIVE VALUE IS EMPTY, AT EVERY RANK AND WITH NO
ELIMINATION HYPOTHESIS.**

An admissible chart stationarity datum whose chart is a design's and whose active
family is two complementary blocks has a NONNEGATIVE value.

Compare `Gtz.zero_le_value_of_isChartTwoBlockFamily_of_eliminates_of_design`, which is
the same conclusion carrying `Gtz.EliminatesChartTwoBlockValue` and `rank = 3`.  Both
are gone here: the value theorem pins a negative value to `-1/size`, and the shipped
strict floor `Gtz.neg_inv_size_lt_value_of_isChartStationaryData` — which needs
exactly the design and the admissibility this statement already carries — excludes
that value.  The eliminant is not used at all, and neither is the Cauchy--Binet floor.

Neither block is required to be nonempty, because `chosenSubset` and its complement
partition the atoms whether or not both are inhabited.

READ THE REACH CORRECTLY.  This covers ONE class of the `(6,3)` covering census, the
class of two complementary triples, and says nothing whatever about the other 2068.
It is also conditional on `Gtz.IsChartStationaryData` and on `Gtz.IsChartArgmaxValue`,
both of which are hypotheses this development does not derive. -/
theorem zero_le_value_of_isChartTwoBlockFamily_of_design
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset) :
    0 ≤ value := by
  by_contra hnegative
  rw [not_le] at hnegative
  have hpinned :=
    value_eq_neg_inv_size_of_isChartTwoBlockFamily_of_negativeValue hdata hfamily hnegative
  have hstrict := neg_inv_size_lt_value_of_isChartStationaryData design hchart hargmax hdata
  rw [hpinned] at hstrict
  exact lt_irrefl _ hstrict

/-- **THE NON-EXISTENCE FORM.**  There is NO admissible chart stationarity datum whose
chart is a design's, whose active family is two complementary blocks, and whose value
is negative — at any rank, with no elimination hypothesis and no floor.

This is `Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_negativeValue` with
`heliminates` and `hrank` both removed. -/
theorem not_isChartStationaryData_of_isChartTwoBlockFamily_of_design_of_negativeValue
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hnegative : value < 0) :
    ¬ IsChartStationaryData rank projection weight value activeSet activeSubset activeWeight
        tightDir := by
  intro hdata
  exact absurd (zero_le_value_of_isChartTwoBlockFamily_of_design design hchart hdata hargmax hfamily)
    (not_le.mpr hnegative)

/-! ## The cofactor identities — CORROBORATION OF THE ELIMINANT, NOT THE DISCHARGE

Two exact ideal memberships over the rationals, both checked by `ring`.  Each says
that the shipped eliminant lies in the ideal of one gauge-fixed branch of the
two-block stationarity system, so each independently confirms that
`Gtz.twoBlockEliminantCubic` is the right polynomial.

NO SATURATION IS PERFORMED ANYWHERE.  Neither identity divides by anything, carries a
`g^N` multiplier, or invokes a nonvanishing side condition; both are plain ideal
memberships in the polynomial ring.  That matters, because the one place a saturation
would naturally have entered is the total multiplier mass `sum_c tau_c = 1 + 6 value`,
which IS the factor `6 value + 1` of the eliminant, whose root `-1/6` is precisely the
value this file's theorem lands on.  Normalising by that mass would have deleted the
whole content.

NEITHER IDENTITY IS THE DISCHARGE, and no cofactor list can be.  The elimination step
has a SIGN antecedent, `value < 0`, and an ideal membership cannot see a sign; the
discharge above is a trace inequality.  The cofactors also cover only the branch in
which each block carries a rank-one multiplier, hence one weight level per block. -/

/-- **COFACTOR CERTIFICATE 1** — the core system in three variables.  With `p` the
common weight on the chosen block, `q` the common weight on its complement and `g` the
value, the generators are the weight sum `3p + 3q - 1` and the two idempotence
relations `(g + p)^2 = g + p`, `(g + q)^2 = g + q` of the block levels.  Then

    `E(g) = h1 f1 + h2 f2 + h3 f3`

identically over the rationals, with the three cofactors written out below. -/
theorem twoBlockEliminantCubic_eq_coreCofactorCombination
    (value blockWeight complementWeight : ℝ) :
    twoBlockEliminantCubic value
      = (-54 * value ^ 2 - 27 * value * blockWeight - 27 * value * complementWeight + 45 * value
            - (9 / 2) * blockWeight ^ 2 - 9 * blockWeight * complementWeight + 12 * blockWeight
            - (9 / 2) * complementWeight ^ 2 + 12 * complementWeight - 5)
          * (3 * blockWeight + 3 * complementWeight - 1)
        + (54 * value + (27 / 2) * blockWeight + (81 / 2) * complementWeight - 27)
          * ((value + blockWeight) ^ 2 - (value + blockWeight))
        + (54 * value + (81 / 2) * blockWeight + (27 / 2) * complementWeight - 27)
          * ((value + complementWeight) ^ 2 - (value + complementWeight)) := by
  unfold twoBlockEliminantCubic
  ring

/-- **COFACTOR CERTIFICATE 2** — the rank-one branch with the off-block coupling `c`,
in four variables.  The three quadrics are the entries of `M^2 = M` for the `2x2`
compression `M = [[g + p, c], [c, g + q]]` of the chart to the plane spanned by the
two multiplier generators. -/
theorem twoBlockEliminantCubic_eq_couplingCofactorCombination
    (value blockWeight complementWeight offBlockCoupling : ℝ) :
    twoBlockEliminantCubic value
      = (18 * offBlockCoupling ^ 2 - 36 * value ^ 2 - 18 * value * blockWeight + 27 * value
            - 9 * blockWeight * complementWeight + (15 / 2) * blockWeight
            + 9 * complementWeight ^ 2 - (3 / 2) * complementWeight - 5)
          * (3 * blockWeight + 3 * complementWeight - 1)
        + (54 * value + 27 * complementWeight - 45 / 2)
          * ((value + blockWeight) ^ 2 - (value + blockWeight) + offBlockCoupling ^ 2)
        + (-54 * offBlockCoupling)
          * (offBlockCoupling * (2 * value + blockWeight + complementWeight - 1))
        + (54 * value - 27 * complementWeight - 27 / 2)
          * ((value + complementWeight) ^ 2 - (value + complementWeight)
            + offBlockCoupling ^ 2) := by
  unfold twoBlockEliminantCubic
  ring

/-- **THE PENCIL DERIVATION OF THE CUBIC.**  With `A = value + p` and `B = value + q`
the two block levels and `T = A + B` their sum, the statement "a sum of two idempotent
scalars is `0`, `1` or `2`" is an ideal membership on the nose:

    `T (T - 1) (T - 2) = (A + 3B - 2) (A^2 - A) + (3A + B - 2) (B^2 - B)` .

Modulo the weight sum `3p + 3q = 1` one has `T = (6 value + 1)/3`, so the left side is
`(6 value + 1)(6 value - 2)(6 value - 5)/27 = 2 E(value)/27` — which is where the
eliminant's degree, its leading coefficient and all three of its roots come from,
with no Groebner computation anywhere. -/
theorem blockLevelSum_cubic_eq_idempotentCombination (firstLevel secondLevel : ℝ) :
    (firstLevel + secondLevel) * (firstLevel + secondLevel - 1) * (firstLevel + secondLevel - 2)
      = (firstLevel + 3 * secondLevel - 2) * (firstLevel ^ 2 - firstLevel)
        + (3 * firstLevel + secondLevel - 2) * (secondLevel ^ 2 - secondLevel) := by
  ring

/-- The pencil identity's collapse: at `T = (6 value + 1)/3` the left side is
`2 E(value)/27`. -/
theorem twoBlockEliminantCubic_eq_levelSum_cubic (value : ℝ) :
    27 * twoBlockEliminantCubic value
      = 27 * ((6 * value + 1) / 3) * ((6 * value + 1) / 3 - 1) * ((6 * value + 1) / 3 - 2)
          * (27 / 2) := by
  unfold twoBlockEliminantCubic
  ring

/-! ## The rank-three witness — the discharged statement is about a NONEMPTY class

An exact RATIONAL `(6,3)` chart point carrying a two-block datum at
`value = -1/6 = -1/size`.  Six atoms at uniform weight `1/6`, blocks `{0,1,2}` and
`{3,4,5}`, and the chart

    `P = 1 - u uᵀ - w wᵀ - z zᵀ` ,   `u = (1,1,1,0,0,0)/sqrt 3` ,
                                     `w = (0,0,0,1,1,1)/sqrt 3` ,
                                     `z = (1,-1,0,1,-1,0)/2` ,

whose entries are all rational because the three subtracted projectors have rational
Gram data.  Each block's all-ones direction is annihilated by `P`, so the gap sends it
to `-1/6` times itself, and the two normalised all-ones directions with multiplier
`1/2` assemble to `1/6` inside the blocks and `0` across — constant diagonal `1/6`, and
`P Xi = 0` on the nose, so the commutation holds because BOTH products vanish.

Two readings, and both are the point of mechanizing it.  The theorem above cannot be
strengthened to emptiness AT RANK THREE, where the shipped `(4,2)` uniform witness
`Gtz.chartTwoBlockUniformProjection_isChartStationaryData` is vacuous.  And
`eliminatesChartTwoBlockValue_three` is not a statement about the empty set.

The datum is INADMISSIBLE — `not_chartTwoBlockTriple_isChartArgmaxValue` — which is why
it does not contradict `Gtz.neg_inv_size_lt_value_of_isChartStationaryData`, and which
is the mechanized form of the numerical note in the header of
`Gtz.Quantitative.ChartTwoBlock` about roots at `-1/6` with uniform weights. -/

/-- The block of an atom at `(6,3)`: atoms `0,1,2` share block `0`, atoms `3,4,5` share
block `1`. -/
def chartTwoBlockTripleAxis (atomIndex : Fin 6) : ℕ := (atomIndex : ℕ) / 3

/-- The alternating sign inside a block, twice the third subtracted direction:
`(1, -1, 0)` on each triple. -/
noncomputable def chartTwoBlockTripleSign (atomIndex : Fin 6) : ℝ :=
  if (atomIndex : ℕ) % 3 = 0 then 1 else if (atomIndex : ℕ) % 3 = 1 then -1 else 0

/-- The rank-three two-block chart, entrywise:
`1 - (1/3) [same block] - (sign * sign)/4`. -/
noncomputable def chartTwoBlockTripleProjection : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    (if rowIndex = colIndex then (1 : ℝ) else 0)
      - (if chartTwoBlockTripleAxis rowIndex = chartTwoBlockTripleAxis colIndex then
          (1 : ℝ) / 3 else 0)
      - chartTwoBlockTripleSign rowIndex * chartTwoBlockTripleSign colIndex / 4

/-- The uniform `(6,3)` weights. -/
noncomputable def chartTwoBlockTripleWeight : Fin 6 → ℝ := fun _ => (6 : ℝ)⁻¹

/-- The two triples. -/
def chartTwoBlockTripleSubset (blockLabel : Fin 2) : Finset (Fin 6) :=
  if blockLabel = 0 then {0, 1, 2} else {3, 4, 5}

/-- The uniform multipliers, one half on each block. -/
noncomputable def chartTwoBlockTripleMultiplierWeight : Fin 2 → ℝ := fun _ => (2 : ℝ)⁻¹

/-- The UNNORMALISED tight direction: the indicator of a triple, of squared length
three. -/
def chartTwoBlockTripleSupport (blockLabel : Fin 2) : Fin 6 → ℝ :=
  fun atomIndex => if chartTwoBlockTripleAxis atomIndex = (blockLabel : ℕ) then 1 else 0

/-- The tight direction: a triple's all-ones direction, normalised. -/
noncomputable def chartTwoBlockTripleTightDir (blockLabel : Fin 2) : Fin 6 → ℝ :=
  (Real.sqrt 3)⁻¹ • chartTwoBlockTripleSupport blockLabel

/-- The assembled multiplier: `1/6` inside each block, `0` across. -/
noncomputable def chartTwoBlockTripleMultiplier : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    if chartTwoBlockTripleAxis rowIndex = chartTwoBlockTripleAxis colIndex then 1 / 6 else 0

theorem chartTwoBlockTripleProjection_transpose :
    chartTwoBlockTripleProjectionᵀ = chartTwoBlockTripleProjection := by
  ext rowIndex colIndex
  simp only [Matrix.transpose_apply, chartTwoBlockTripleProjection, Matrix.of_apply]
  by_cases hequal : rowIndex = colIndex
  · rw [hequal]
  · rw [if_neg (Ne.symm hequal), if_neg hequal]
    by_cases haxis : chartTwoBlockTripleAxis rowIndex = chartTwoBlockTripleAxis colIndex
    · rw [if_pos haxis.symm, if_pos haxis]
      ring
    · rw [if_neg fun hflip => haxis hflip.symm, if_neg haxis]
      ring

theorem chartTwoBlockTripleProjection_mul_self :
    chartTwoBlockTripleProjection * chartTwoBlockTripleProjection
      = chartTwoBlockTripleProjection := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, Fin.sum_univ_six]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [chartTwoBlockTripleProjection, chartTwoBlockTripleAxis, chartTwoBlockTripleSign,
      Fin.ext_iff]

/-- The indicator of a triple has squared length three. -/
theorem chartTwoBlockTripleSupport_dotProduct_self (blockLabel : Fin 2) :
    chartTwoBlockTripleSupport blockLabel ⬝ᵥ chartTwoBlockTripleSupport blockLabel = 3 := by
  simp only [dotProduct, chartTwoBlockTripleSupport, chartTwoBlockTripleAxis, Fin.sum_univ_six]
  fin_cases blockLabel <;> norm_num

/-- An atom of a triple has that triple's block index. -/
theorem chartTwoBlockTripleAxis_of_mem (blockLabel : Fin 2) (atomIndex : Fin 6)
    (hmem : atomIndex ∈ chartTwoBlockTripleSubset blockLabel) :
    chartTwoBlockTripleAxis atomIndex = (blockLabel : ℕ) := by
  fin_cases blockLabel <;> fin_cases atomIndex <;>
    simp_all [chartTwoBlockTripleSubset, chartTwoBlockTripleAxis]

/-- An atom outside a triple does not have that triple's block index. -/
theorem chartTwoBlockTripleAxis_ne_of_notMem (blockLabel : Fin 2) (atomIndex : Fin 6)
    (hnotMem : atomIndex ∉ chartTwoBlockTripleSubset blockLabel) :
    chartTwoBlockTripleAxis atomIndex ≠ (blockLabel : ℕ) := by
  fin_cases blockLabel <;> fin_cases atomIndex <;>
    simp_all [chartTwoBlockTripleSubset, chartTwoBlockTripleAxis]

/-- **THE CHART ANNIHILATES EACH TRIPLE'S ALL-ONES DIRECTION**, so the gap sends it to
`-1/6` times itself at every atom of that triple. -/
theorem chartTwoBlockTripleGap_mulVec_support (blockLabel : Fin 2) (atomIndex : Fin 6)
    (hmem : atomIndex ∈ chartTwoBlockTripleSubset blockLabel) :
    (chartStationaryGap chartTwoBlockTripleProjection chartTwoBlockTripleWeight
        *ᵥ chartTwoBlockTripleSupport blockLabel) atomIndex = -(6 : ℝ)⁻¹ := by
  simp only [Matrix.mulVec, dotProduct, chartStationaryGap, Matrix.sub_apply,
    Matrix.diagonal_apply, chartTwoBlockTripleWeight, chartTwoBlockTripleProjection,
    Matrix.of_apply, chartTwoBlockTripleSupport, chartTwoBlockTripleAxis,
    chartTwoBlockTripleSign, Fin.sum_univ_six]
  revert hmem
  fin_cases blockLabel <;> fin_cases atomIndex <;>
    simp [chartTwoBlockTripleSubset, Fin.ext_iff] <;> norm_num

/-- The rank-three assembly is `1/6` inside the blocks and `0` across: each triple's
normalised all-ones projector carries multiplier `1/2`, and `(1/2)(1/3) = 1/6`. -/
theorem chartTwoBlockTripleMultiplierAssembly_eq :
    chartMultiplierAssembly (Finset.univ : Finset (Fin 2)) chartTwoBlockTripleMultiplierWeight
        chartTwoBlockTripleTightDir
      = chartTwoBlockTripleMultiplier := by
  have hscale : ∀ blockLabel : Fin 2,
      chartTwoBlockTripleMultiplierWeight blockLabel
          • atomMatrix (chartTwoBlockTripleTightDir blockLabel)
        = (6 : ℝ)⁻¹ • atomMatrix (chartTwoBlockTripleSupport blockLabel) := by
    intro blockLabel
    rw [chartTwoBlockTripleTightDir, atomMatrix_smul, inv_pow, sqrt_three_sq, smul_smul,
      chartTwoBlockTripleMultiplierWeight]
    norm_num
  rw [chartMultiplierAssembly, Finset.sum_congr rfl fun blockLabel _ => hscale blockLabel]
  ext rowIndex colIndex
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply,
    chartTwoBlockTripleSupport, chartTwoBlockTripleMultiplier, Matrix.of_apply,
    chartTwoBlockTripleAxis, Fin.sum_univ_two]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num

/-- **THE RANK-THREE TWO-BLOCK DATUM.**  Rank three, six atoms, `value = -1/6 = -1/size`,
two complementary triples, uniform weights, assembly `1/6` inside the blocks. -/
theorem chartTwoBlockTripleProjection_isChartStationaryData :
    IsChartStationaryData 3 chartTwoBlockTripleProjection chartTwoBlockTripleWeight
      (-(6 : ℝ)⁻¹) (Finset.univ : Finset (Fin 2)) chartTwoBlockTripleSubset
      chartTwoBlockTripleMultiplierWeight chartTwoBlockTripleTightDir where
  isSymmetric := chartTwoBlockTripleProjection_transpose
  isIdempotent := chartTwoBlockTripleProjection_mul_self
  hasTraceRank := by
    show ∑ atomIndex : Fin 6, chartTwoBlockTripleProjection atomIndex atomIndex = ((3 : ℕ) : ℝ)
    rw [Fin.sum_univ_six]
    norm_num [chartTwoBlockTripleProjection, chartTwoBlockTripleAxis, chartTwoBlockTripleSign]
  weight_pos := by intro atomIndex; norm_num [chartTwoBlockTripleWeight]
  weight_sum_one := by norm_num [chartTwoBlockTripleWeight, Fin.sum_univ_six]
  activeWeight_nonneg := by intro blockLabel _; norm_num [chartTwoBlockTripleMultiplierWeight]
  activeWeight_sum_one := by norm_num [chartTwoBlockTripleMultiplierWeight, Fin.sum_univ_two]
  activeSubset_card := by intro blockLabel _; fin_cases blockLabel <;> decide
  tightDir_unit := by
    intro blockLabel _
    have hinvRoot : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = (3 : ℝ)⁻¹ := by
      rw [← mul_inv, ← pow_two, sqrt_three_sq]
    rw [chartTwoBlockTripleTightDir, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hinvRoot, chartTwoBlockTripleSupport_dotProduct_self]
    norm_num
  tightDir_support := by
    intro blockLabel _ atomIndex hnotMem
    rw [chartTwoBlockTripleTightDir, Pi.smul_apply, chartTwoBlockTripleSupport,
      if_neg (chartTwoBlockTripleAxis_ne_of_notMem blockLabel atomIndex hnotMem), smul_zero]
  tightDir_isTight := by
    intro blockLabel _ atomIndex hmem
    rw [chartTwoBlockTripleTightDir, Matrix.mulVec_smul, Pi.smul_apply,
      chartTwoBlockTripleGap_mulVec_support blockLabel atomIndex hmem, Pi.smul_apply,
      chartTwoBlockTripleSupport,
      if_pos (chartTwoBlockTripleAxis_of_mem blockLabel atomIndex hmem)]
    simp only [smul_eq_mul]
    ring
  assembly_diagonal := by
    intro atomIndex
    rw [chartTwoBlockTripleMultiplierAssembly_eq, chartTwoBlockTripleMultiplier, Matrix.of_apply,
      if_pos rfl]
    norm_num
  assembly_commutes := by
    rw [chartTwoBlockTripleMultiplierAssembly_eq]
    ext rowIndex colIndex
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_six]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [chartTwoBlockTripleProjection, chartTwoBlockTripleMultiplier,
        chartTwoBlockTripleAxis, chartTwoBlockTripleSign, Fin.ext_iff]

/-- The rank-three family is two complementary triples, `{0,1,2}` and `{3,4,5}`. -/
theorem chartTwoBlockTriple_isChartTwoBlockFamily :
    IsChartTwoBlockFamily (Finset.univ : Finset (Fin 2)) chartTwoBlockTripleSubset
      ({0, 1, 2} : Finset (Fin 6)) := by
  intro blockLabel _
  fin_cases blockLabel <;> simp only [chartTwoBlockTripleSubset] <;> decide

/-- **THE DISCHARGED STATEMENT IS NOT ABOUT THE EMPTY SET.**  A rank-three chart
stationarity datum with two OCCUPIED complementary blocks and a NEGATIVE value exists,
at `value = -1/6` exactly — which is what
`value_eq_neg_inv_size_of_isChartTwoBlockFamily_of_negativeValue` predicts, and which
`eliminatesChartTwoBlockValue_three` then sends to a root of the eliminant. -/
theorem exists_isChartStationaryData_isChartTwoBlockFamily_rankThree_negativeValue :
    ∃ (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ)
      (activeSubset : Fin 2 → Finset (Fin 6)) (activeWeight : Fin 2 → ℝ)
      (tightDir : Fin 2 → (Fin 6 → ℝ)) (chosenSubset : Finset (Fin 6)),
      IsChartStationaryData 3 projection weight (-(6 : ℝ)⁻¹) (Finset.univ : Finset (Fin 2))
          activeSubset activeWeight tightDir ∧
        IsChartTwoBlockFamily (Finset.univ : Finset (Fin 2)) activeSubset chosenSubset ∧
        chosenSubset.Nonempty ∧ chosenSubsetᶜ.Nonempty ∧ (-(6 : ℝ)⁻¹ : ℝ) < 0 :=
  ⟨chartTwoBlockTripleProjection, chartTwoBlockTripleWeight, chartTwoBlockTripleSubset,
    chartTwoBlockTripleMultiplierWeight, chartTwoBlockTripleTightDir, {0, 1, 2},
    chartTwoBlockTripleProjection_isChartStationaryData,
    chartTwoBlockTriple_isChartTwoBlockFamily, ⟨0, by decide⟩, ⟨3, by decide⟩, by norm_num⟩

/-- **THE RANK-THREE WITNESS IS INADMISSIBLE**, and the certificate is one line of
completed square.  On the triple `{0,1,5}` the gap's quadratic form is

    `Q(x) = (1/4)(x_0^2 + x_1^2) - (1/6) x_0 x_1 + (1/2) x_5^2` ,

so on the unit sphere `Q(x) - 1/6 = (1/12)(x_0 - x_1)^2 + (1/3) x_5^2 >= 0`.  Every
unit probe supported there therefore has Rayleigh quotient at least `1/6`, and no
probe reaches `-1/6`.

This is why the datum does not contradict
`Gtz.neg_inv_size_lt_value_of_isChartStationaryData`, and it is the mechanized form of
the numerical note in the header of `Gtz.Quantitative.ChartTwoBlock` that the roots at
`-1/6` with uniform weights are all inadmissible. -/
theorem not_chartTwoBlockTriple_isChartArgmaxValue :
    ¬ IsChartArgmaxValue 3 chartTwoBlockTripleProjection chartTwoBlockTripleWeight
        (-(6 : ℝ)⁻¹) := by
  intro hargmax
  obtain ⟨probe, hunit, hsupport, hquotient⟩ := hargmax ({0, 1, 5} : Finset (Fin 6)) (by decide)
  have hsecondZero : probe 2 = 0 := hsupport 2 (by decide)
  have hthirdZero : probe 3 = 0 := hsupport 3 (by decide)
  have hfourthZero : probe 4 = 0 := hsupport 4 (by decide)
  have hunitExpanded : probe 0 ^ 2 + probe 1 ^ 2 + probe 5 ^ 2 = 1 := by
    rw [dotProduct, Fin.sum_univ_six, hsecondZero, hthirdZero, hfourthZero] at hunit
    nlinarith [hunit]
  have hformExpanded : probe ⬝ᵥ (chartStationaryGap chartTwoBlockTripleProjection
        chartTwoBlockTripleWeight *ᵥ probe)
      = (1 / 4) * (probe 0 ^ 2 + probe 1 ^ 2) - (1 / 6) * (probe 0 * probe 1)
        + (1 / 2) * probe 5 ^ 2 := by
    simp only [dotProduct, Matrix.mulVec, chartStationaryGap, Matrix.sub_apply,
      Matrix.diagonal_apply, chartTwoBlockTripleWeight, chartTwoBlockTripleProjection,
      Matrix.of_apply, chartTwoBlockTripleAxis, chartTwoBlockTripleSign, Fin.sum_univ_six]
    rw [hsecondZero, hthirdZero, hfourthZero]
    norm_num [Fin.ext_iff]
    ring
  rw [hformExpanded] at hquotient
  nlinarith [sq_nonneg (probe 0 - probe 1), sq_nonneg (probe 5), hunitExpanded, hquotient]

end Gtz
