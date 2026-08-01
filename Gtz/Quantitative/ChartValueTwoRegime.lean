/-
# THE A-PRIORI VALUE GAP: what a two-regime theorem is, and two strata that have one

`Gtz.Quantitative.TwoBlockEliminationCertificate` proves that a chart stationarity
datum whose active family is TWO COMPLEMENTARY BLOCKS and whose value is negative has
`value = -1/size` exactly.  That is the only two-regime value theorem in the tree, and
its engine is INTEGRALITY: `trace (P Q)` is the trace of a symmetric idempotent, so it
is `0` or at least `1`, and a negative value pushes it below `1`.

This file does two things with that engine.

## 1.  The engine is separated from the two-block hypothesis

The block structure enters the shipped proof at exactly one step, `trace (P Q) =
sum_c (value + t_c) Q_cc`, which needs the BLOCK-DIAGONAL TRUNCATION of the chart to
act on the assembly as `diag(value + t)` does.  What that step really wants is

    `W * Xi = value • Xi`,          `W = chartStationaryGap = P - diag t`,

i.e. every active tight direction is an eigenvector of the FULL chart gap at the
value, not merely of its own block.  Call such a datum GAP-ANNIHILATING.  Under that
hypothesis alone the whole argument runs, with no family hypothesis of any kind:
`zero_le_value_or_eq_neg_inv_size_of_gapAnnihilates`.

The two hypotheses are incomparable, so this is a genuinely different stratum, not a
weakening.  The shipped `(6,3)` two-block witness satisfies BOTH — its chart
annihilates both tight directions — so the theorem below is not vacuous at the open
cell (`gapAnnihilates_chartTwoBlockTripleProjection`).

## 2.  The general dichotomy, and the exact quantity a general theorem would need

Drop every structural hypothesis.  The shipped `trace (P Xi) = value + 1/size` plus
the bundle's `[P, Xi] = 0` say that `value + 1/size` is a sum of exactly `rank`
eigenvalues of the assembly — the ones whose eigenvectors span `range P`.  So either
all of them vanish, which pins `value = -1/size`, or one of them is a genuine nonzero
eigenvalue of `Xi`.  That is `value_eq_neg_inv_size_or_spectralLevel_le`: at every
datum, and at every `level` below the nonzero spectrum of the assembly,

    `value = -1/size`   or   `level <= value + 1/size` .

MEASURED, AND IT IS A NEGATIVE RESULT, recorded here so the route is not re-entered.
A `level` of `1/size` would empty the whole band `(-1/size, 0)` and close the cell.
The least positive eigenvalue of the assembly was measured at every witness the
campaign owns and is nowhere near `1/size`: `1/12` at the `(4,3)` tetrahedron against
`1/4`, `1/20` at the `(5,3)` diamond against `1/5`, and `0.0318` / `0.0180` at the two
admissible `(6,3)` data of the `|A| = 5` frontier against `1/6` — the second of those
below `1/54 = 1/6 - 4/27`, which is the whole crux window's width.  So the spectral
route supplies no unconditional gap, and the dichotomy's second branch is not a
constraint at the open cell.  The numbers are in the report of this rung; they are
60-digit recomputations, not floats.

## 3.  What an `eps0` would buy, stated so the target cannot be overstated

`ChartValueTwoRegime eps` says no admissible datum over a design has value in
`[-eps, 0)`.  Three facts pin its worth exactly:

* `isEmpty_sixThreeCrux_of_chartValueTwoRegime` — at `eps = 4/27` it CLOSES the cell,
  because the shipped crux window is `[-4/27, 0)`.  So `eps = 4/27` is not a lemma on
  the way to the conjecture; it is the conjecture, and any proof of it must consume
  realness (boundary condition B1).
* `chartObjective_lt_neg_of_chartValueTwoRegime` — at `eps < 4/27` it shrinks the crux
  value window from `[-4/27, 0)` to `[-4/27, -eps)`.  That is the only partial credit
  available on this lane, and it is real.
* `chartValueTwoRegime_of_isEmpty_sixThreeCrux` — the converse.  Emptiness of the crux
  implies the two-regime property at EVERY `eps`, so the naked existential
  "some `eps > 0` works" is implied by the conjecture and cannot be evidence for it.
  This is the value-lane form of the vacuity that `Gtz.SixThreeCrux.chartObjective_eq`
  exhibits on the margin lane: an unquantified gap closes nothing, and only an
  EXPLICIT numeral is worth proving.

NO SORRY, NO AXIOM, NO `native_decide`.
-/
import Mathlib
import Gtz.Quantitative.TwoBlockEliminationCertificate
import Gtz.Quantitative.SixThreeExclusionFrontier
import Gtz.Quantitative.ValueLaneBandExclusion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

open scoped BigOperators

variable {size rank : ℕ} {activeIndex : Type*}
  {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}
  {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## L1: the shifted weight diagonal, and the gap-annihilating hypothesis -/

/-- **THE GAP-ANNIHILATING STRATUM.**  Every active tight direction is an eigenvector
of the FULL chart gap `W = P - diag t` at the value, not merely of its own block.

The bundle's `tightDir_isTight` asserts the eigen-relation only at coordinates INSIDE
the active subset; off the subset the ambient product is generally nonzero, and the
off-block residual `(W - value) u_C` is exactly what this hypothesis kills. -/
def GapAnnihilatesAssembly (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ)) : Prop :=
  chartStationaryGap projection weight
      * chartMultiplierAssembly activeSet activeWeight tightDir
    = value • chartMultiplierAssembly activeSet activeWeight tightDir

/-- The chart minus the shifted weight diagonal is the gap minus the value. -/
theorem projection_sub_shiftedDiagonal (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) :
    projection - Matrix.diagonal (fun atomIndex => value + weight atomIndex)
      = chartStationaryGap projection weight
        - value • (1 : Matrix (Fin size) (Fin size) ℝ) := by
  ext rowIndex colIndex
  by_cases hdiag : rowIndex = colIndex
  · subst hdiag
    simp [chartStationaryGap, Matrix.diagonal]
    ring
  · simp [chartStationaryGap, Matrix.diagonal, hdiag]

/-! ## L2: the trace step, off the block structure -/

/-- **THE TRACE STEP UNDER GAP-ANNIHILATION.**  The shipped
`Gtz.trace_projection_mul_rangeProjection` reaches this conclusion from the two-block
family; the hypothesis here reaches it from the residual instead, and mentions no
family at all. -/
theorem trace_projection_mul_rangeProjection_of_gapAnnihilates
    (hgap : GapAnnihilatesAssembly projection weight value activeSet activeWeight tightDir)
    (hhermitian : (chartMultiplierAssembly activeSet activeWeight tightDir).IsHermitian) :
    Matrix.trace (projection * rangeProjection hhermitian)
      = ∑ atomIndex : Fin size,
          (value + weight atomIndex) * rangeProjection hhermitian atomIndex atomIndex := by
  have hannihilate : (projection - Matrix.diagonal (fun atomIndex => value + weight atomIndex))
      * chartMultiplierAssembly activeSet activeWeight tightDir = 0 := by
    rw [projection_sub_shiftedDiagonal, Matrix.sub_mul, hgap, Matrix.smul_mul, Matrix.one_mul,
      sub_self]
  have hrange : (projection - Matrix.diagonal (fun atomIndex => value + weight atomIndex))
      * rangeProjection hhermitian = 0 :=
    mul_rangeProjection_eq_zero_of_mul_eq_zero hhermitian hannihilate
  have hshift : projection * rangeProjection hhermitian
      = Matrix.diagonal (fun atomIndex => value + weight atomIndex)
        * rangeProjection hhermitian := by
    rw [Matrix.sub_mul] at hrange
    exact sub_eq_zero.mp hrange
  rw [hshift, Matrix.trace]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    simp [Matrix.diag_apply, Matrix.diagonal_mul]

/-! ## L3: the two-regime theorem on the gap-annihilating stratum -/

/-- **A GAP-ANNIHILATING DATUM HAS VALUE `>= 0` OR VALUE EXACTLY `-1/size`.**

The integrality engine of `Gtz.value_eq_neg_inv_size_of_isChartTwoBlockFamily_of_negativeValue`,
run off the residual instead of off the block structure.  `trace (P Q)` is the trace of
a symmetric idempotent, hence `0` or at least `1`; a negative value forces it strictly
below `1` through `trace Q >= 1` and `sum_c t_c Q_cc <= 1`; so it is `0`, so
`P Xi = 0`, so the shipped forced trace pins the value.

THE BAND `(-1/size, 0)` IS EMPTY ON THIS STRATUM.  That is a genuine a-priori value gap
of width `1/size`, wider than the `4/27` the `(6,3)` crux window needs — but only here,
and the stratum is small: `hgap` fails at the `(5,3)` diamond and at both admissible
`(6,3)` data of the `|A| = 5` frontier, all of which carry nonzero off-block residuals. -/
theorem zero_le_value_or_eq_neg_inv_size_of_gapAnnihilates
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hgap : GapAnnihilatesAssembly projection weight value activeSet activeWeight tightDir) :
    0 ≤ value ∨ value = -((size : ℝ))⁻¹ := by
  by_cases hnonneg : 0 ≤ value
  · exact Or.inl hnonneg
  refine Or.inr ?_
  have hnegative : value < 0 := not_le.mp hnonneg
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
    rw [trace_projection_mul_rangeProjection_of_gapAnnihilates hgap hhermitian, hsplit]
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

/-- **THE BAND IS EMPTY ON THE GAP-ANNIHILATING STRATUM.**  With the shipped strict
floor available the conclusion becomes an exclusion rather than a dichotomy: no
gap-annihilating datum over a design has value strictly between `-1/size` and `0`. -/
theorem zero_le_value_of_gapAnnihilates_of_lt_neg_inv_size
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hgap : GapAnnihilatesAssembly projection weight value activeSet activeWeight tightDir)
    (hfloor : -((size : ℝ))⁻¹ < value) :
    0 ≤ value := by
  rcases zero_le_value_or_eq_neg_inv_size_of_gapAnnihilates hdata hgap with hnonneg | hfloorEq
  · exact hnonneg
  · exact absurd hfloorEq (ne_of_gt hfloor)

/-! ## L3b: the stratum is inhabited at the OPEN CELL

Precedent: a second-order escape was once landed demanding flatness at twenty blocks,
a condition generically unsatisfiable — true and useless.  So the hypothesis is
exhibited at a genuine `(6,3)` datum before anything is claimed for it. -/

/-- **THE `(6,3)` TWO-BLOCK CHART ANNIHILATES ITS OWN ASSEMBLY AT THE VALUE.**  The
shipped `Gtz.chartTwoBlockTripleGap_mulVec_support` says this at the atoms INSIDE each
triple; off the triple the entry vanishes too, because each block's sign vector
`(1, -1, 0)` sums to zero, so the rank-one correction contributes nothing. -/
theorem chartTwoBlockTripleGap_mul_multiplier :
    chartStationaryGap chartTwoBlockTripleProjection chartTwoBlockTripleWeight
        * chartTwoBlockTripleMultiplier
      = (-(6 : ℝ)⁻¹) • chartTwoBlockTripleMultiplier := by
  ext rowIndex colIndex
  simp only [Matrix.mul_apply, chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply,
    chartTwoBlockTripleWeight, chartTwoBlockTripleProjection, Matrix.of_apply,
    chartTwoBlockTripleMultiplier, chartTwoBlockTripleAxis, chartTwoBlockTripleSign,
    Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_six]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Fin.ext_iff]

/-- **NON-VACUITY AT THE OPEN CELL.**  The shipped rank-three two-block datum is
gap-annihilating, so `zero_le_value_or_eq_neg_inv_size_of_gapAnnihilates` has a genuine
`(6,3)` instance and its hypothesis is not a disguised falsehood.

The datum sits on the `value = -1/size` branch, which is the branch the theorem
predicts and the only branch a negative value may occupy. -/
theorem gapAnnihilates_chartTwoBlockTripleProjection :
    GapAnnihilatesAssembly chartTwoBlockTripleProjection chartTwoBlockTripleWeight
      (-(6 : ℝ)⁻¹) (Finset.univ : Finset (Fin 2)) chartTwoBlockTripleMultiplierWeight
      chartTwoBlockTripleTightDir := by
  rw [GapAnnihilatesAssembly, chartTwoBlockTripleMultiplierAssembly_eq]
  exact chartTwoBlockTripleGap_mul_multiplier

/-! ## L4: the general dichotomy, with no structural hypothesis at all -/

/-- **THE SPECTRAL DICHOTOMY.**  `level` below the nonzero spectrum of the assembly is
expressed as `Xi - level • Q` positive semidefinite, `Q` the assembly's range
projection: that says exactly that every NONZERO eigenvalue of `Xi` is at least
`level`, and says nothing about the zero ones.

Then `value + 1/size = trace (P Xi)` is a sum of `rank` eigenvalues of `Xi`, so either
they all vanish — which is `P Xi = 0` and pins `value = -1/size` — or `level` fits
underneath.  No family hypothesis, no residual hypothesis, no admissibility.

This is the exact reduction the a-priori value gap asks for: an `eps0` on this route IS
a lower bound on the least positive eigenvalue of the assembly.  See the file header
for the measurement that says no useful such bound exists. -/
theorem value_eq_neg_inv_size_or_spectralLevel_le
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {level : ℝ} (hlevel : 0 ≤ level)
    (hspectral : (chartMultiplierAssembly activeSet activeWeight tightDir
        - level • rangeProjection
            (isHermitian_chartMultiplierAssembly_of_isChartStationaryData hdata)).PosSemidef) :
    value = -((size : ℝ))⁻¹ ∨ level ≤ value + ((size : ℝ))⁻¹ := by
  have hhermitian := isHermitian_chartMultiplierAssembly_of_isChartStationaryData hdata
  have hcommute : projection * rangeProjection hhermitian
      = rangeProjection hhermitian * projection :=
    commute_rangeProjection_of_commute hhermitian hdata.assembly_commutes
  by_cases hvanish : projection * rangeProjection hhermitian = 0
  · refine Or.inl ?_
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
  refine Or.inr ?_
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
  have honeLe : (1 : ℝ) ≤ Matrix.trace (projection * rangeProjection hhermitian) :=
    one_le_trace_of_symmetricIdempotent_of_ne_zero hproductSymmetric hproductIdempotent hvanish
  have hconj : (projection)ᴴ = projection := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hdata.isSymmetric
  have hsandwichNonneg : 0 ≤ Matrix.trace (projection
      * (chartMultiplierAssembly activeSet activeWeight tightDir
          - level • rangeProjection hhermitian) * projection) := by
    have := hspectral.mul_mul_conjTranspose_same projection
    rw [hconj] at this
    exact this.trace_nonneg
  have hcyclic : Matrix.trace (projection
        * (chartMultiplierAssembly activeSet activeWeight tightDir
            - level • rangeProjection hhermitian) * projection)
      = Matrix.trace (projection
        * (chartMultiplierAssembly activeSet activeWeight tightDir
            - level • rangeProjection hhermitian)) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hdata.isIdempotent]
  rw [hcyclic, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul,
    trace_projection_mul_multiplier_of_isChartStationaryData hdata] at hsandwichNonneg
  simp only [smul_eq_mul] at hsandwichNonneg
  nlinarith [mul_le_mul_of_nonneg_left honeLe hlevel]

/-! ## L5: what an explicit gap buys at the open cell -/

/-- **THE TWO-REGIME PREDICATE AT `(6,3)`.**  No admissible chart stationarity datum
over a design has value in the half-open band `[-gapWidth, 0)`.

Stated at the CHART OBJECTIVE rather than at a free `value` parameter, because that is
the form the crux supplies and the form a closure consumes. -/
def ChartValueTwoRegime (gapWidth : ℝ) : Prop :=
  ∀ design : WeightedDesign 6 3,
    ∀ (activeWeight : Finset (Fin 6) → ℝ) (tightDir : Finset (Fin 6) → (Fin 6 → ℝ)),
      IsChartArgmaxValue 3 (chartPointOfDesign design).chart (chartPointOfDesign design).weight
        (chartObjective (chartPointOfDesign design)) →
      IsChartStationaryData 3 (chartPointOfDesign design).chart
        (chartPointOfDesign design).weight (chartObjective (chartPointOfDesign design))
        (chartArgmaxFamily (chartPointOfDesign design))
        (id : Finset (Fin 6) → Finset (Fin 6)) activeWeight tightDir →
      -gapWidth ≤ chartObjective (chartPointOfDesign design) →
      0 ≤ chartObjective (chartPointOfDesign design)

/-- **AT `4/27` THE TWO-REGIME PROPERTY CLOSES THE CELL.**  The shipped crux window is
`[-4/27, 0)`, so a crux is exactly a design the property forbids.

READ THIS AS A CEILING, NOT A LEMMA.  It says the numeral `4/27` is not a step towards
the conjecture but a restatement of it, so any proof of it must consume realness
(boundary condition B1) — the whole chain cannot be field-blind. -/
theorem isEmpty_sixThreeCrux_of_chartValueTwoRegime
    (hregime : ChartValueTwoRegime (4 / 27)) : IsEmpty SixThreeCrux := by
  refine ⟨fun crux => ?_⟩
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  have hnonneg := hregime crux.design multiplier selection crux.isChartArgmaxValue hdata
    crux.neg_four_div_twentySeven_le_chartObjective
  exact absurd crux.hasNegativeChartValue (not_lt.mpr hnonneg)

/-- **BELOW `4/27` THE TWO-REGIME PROPERTY SHRINKS THE CRUX WINDOW.**  This is the
partial credit available on the value lane, and it is genuine: an `eps` of any size
moves the crux's value strictly below `-eps`, so the shipped window `[-4/27, 0)`
becomes `[-4/27, -eps)`. -/
theorem chartObjective_lt_neg_of_chartValueTwoRegime {gapWidth : ℝ}
    (hregime : ChartValueTwoRegime gapWidth) (crux : SixThreeCrux) :
    chartObjective (chartPointOfDesign crux.design) < -gapWidth := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  by_contra hnotBelow
  exact absurd crux.hasNegativeChartValue
    (not_lt.mpr (hregime crux.design multiplier selection crux.isChartArgmaxValue hdata
      (not_lt.mp hnotBelow)))

/-- **THE VACUITY OF THE UNQUANTIFIED GAP.**  If the crux is empty — which is exactly
the conjecture at rank three — then the two-regime property holds at EVERY width.

So `∃ eps > 0, ChartValueTwoRegime eps` is implied by the conjecture, and can never be
evidence for it: only an explicit numeral is worth proving, and the only numeral that
closes is `4/27`.  This is the value-lane twin of the margin-lane vacuity that
`Gtz.SixThreeCrux.chartObjective_eq` exhibits. -/
theorem chartValueTwoRegime_of_isEmpty_sixThreeCrux (hempty : IsEmpty SixThreeCrux)
    (gapWidth : ℝ) : ChartValueTwoRegime gapWidth := by
  intro design _activeWeight _tightDir _hargmax _hdata _hband
  have hgtz : GtzWeighted 6 3 := by
    by_contra hfail
    exact hempty.elim (nonempty_sixThreeCrux_of_not_gtzWeighted_six_three hfail).some
  obtain ⟨selected, hcard, hdominates⟩ := hgtz design
  exact (zero_le_chartObjective_iff_exists_chartDominates (chartPointOfDesign design)).mpr
    ⟨selected, hcard, (dominates_iff_chartDominates design selected hcard).mp hdominates⟩

/-! ## L6: the bridge to the crux-quantified band, and to the honesty layer

`Gtz.ChartValueTwoRegime` and the shipped `Gtz.ChartValueBandExclusion`
(ValueLaneBandExclusion.lean:244) are DIFFERENT objects and were produced by two
agents who could not see each other: this one quantifies over admissible chart
stationarity DATA over a design, the shipped one over CRUXES.  They are not
interchangeable, and the implication that does hold runs one way.  It is landed here
so the two are connected rather than merely adjacent. -/

/-- **THE TWO-REGIME PROPERTY IMPLIES THE BAND EXCLUSION, at the same width.**  A
crux supplies an admissible stationarity datum at its own chart objective, which is
exactly what the two-regime property consumes; the strict inequality it returns is
weakened to the band exclusion's non-strict one.

The converse does NOT hold, and should not be expected to: the band exclusion says
nothing about a datum over a design that is not a crux. -/
theorem chartValueBandExclusion_of_chartValueTwoRegime {gapWidth : ℝ}
    (hregime : ChartValueTwoRegime gapWidth) : ChartValueBandExclusion gapWidth :=
  fun crux => (chartObjective_lt_neg_of_chartValueTwoRegime hregime crux).le

/-- **THE CEILING, INHERITED.**  Through the bridge, the shipped
`Gtz.isEmpty_sixThreeCrux_of_bandExclusion_of_four_div_twentySeven_lt` applies to the
two-regime property as well: any width strictly above `4/27` makes it the whole cell.
Together with `Gtz.isEmpty_sixThreeCrux_of_chartValueTwoRegime`, which does the same
AT `4/27`, the honest target range for this lane is the half-open interval
`(0, 4/27)`. -/
theorem isEmpty_sixThreeCrux_of_chartValueTwoRegime_of_four_div_twentySeven_lt
    {gapWidth : ℝ} (hwide : (4 : ℝ) / 27 < gapWidth)
    (hregime : ChartValueTwoRegime gapWidth) : IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_bandExclusion_of_four_div_twentySeven_lt hwide
    (chartValueBandExclusion_of_chartValueTwoRegime hregime)

end Gtz
