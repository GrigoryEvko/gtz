/-
# The chart stationarity bundle is INHABITED, and inhabited non-degenerately

`Gtz.IsChartStationaryData` (`Gtz.Quantitative.ChartStationary`) is a HYPOTHESIS
structure: nothing in this repository derives it, and every theorem about it takes
it as an assumption.  A hypothesis structure nobody can instantiate proves
theorems about the empty class, and this repository has been bitten by exactly
that defect before — `Gtz/Audit.lean`'s own header records two coverage drifts, and
`Gtz.Quantitative.CriticalQuadric` carries its `degenerateQuadricStationary*`
witnesses for the same reason.  This file is the chart-side answer: explicit
chart points, with explicit rational multipliers, proved to satisfy the bundle.

`Gtz.Quantitative.ChartStationary` already ships two witnesses of its own — the
`(4,3)` tetrahedron at value `0` and the `(6,3)` octahedron at value `1/3`.  Both
are RAW matrices: the bundle is chart-primitive and never asks that its projection
factor as `V Vᵀ`, so neither witness needs a design behind it.  What this file adds
is the three things those two do not have.

## What is landed, and why each one is not redundant

**(1) THE TETRAHEDRON, AT A CERTIFIED TIE.**  `tetraDesign_isChartStationaryData`
carries the `(4,3)` datum on `projectionOfDesign tetraDesign` rather than on the
raw matrix, and `exists_isTie_and_isChartStationaryData` pairs it with
`Gtz.tetraDesign_isTie`.  So the bundle is inhabited at an object this repository
independently certifies as an exact tie of the GTZ problem — `max_C lambda_min(S_C)
= 1` on the nose, no subset dominating strictly — and not merely at a matrix that
happens to solve the equations.  The reference values `Xi = I_4/12 + J_4/6`,
`M = I_3/12`, `N = 3/4`, `Lambda = I_3/3` are already mechanized in
`Gtz.chartTetraMultiplierAssembly_eq`, `Gtz.chartSplitTetraRangeMultiplier_eq`,
`Gtz.chartSplitTetraKernelMultiplier_eq` and
`Gtz.chartSplitTetraQuadricMultiplier_eq`; they are CITED here, not re-derived.

**(2) A CORANK-ONE CHART POINT WITH NON-UNIFORM RATIONAL WEIGHTS.**  Both shipped
witnesses have UNIFORM weights, so in both of them the forced diagonal
`(P Xi)_cc = (value + t_c)/size` collapses to a constant and the weight-dependence
of `Gtz.diagonal_projection_mul_multiplier_of_isChartStationaryData`, of the weight
floor `Gtz.weight_ge_neg_value_of_isChartStationaryData` and of the dual bound
`Gtz.value_le_one_sub_weight_of_isChartStationaryData` is invisible.  The datum
below has weights `(1/13, 1/13, 1/13, 10/13)`, a ten-to-one spread, so those three
theorems are exercised at four genuinely different values.

**(3) THE SPLIT FAMILY AT THE OPEN CELL `(6,3)`, AT VALUE ZERO.**  The octahedron
witness sits at `(6,3)` but at `value = 1/3`, off the extremal locus and with
uniform weights.  `chartSplitSixDesign` is `Gtz.splitTetraDesign` at the balanced
split `(1/8, 1/8)`: a genuine `(6,3)` design, weights `(1/4, 1/4, 1/8, 1/8, 1/8,
1/8)`, an exact tie by `Gtz.splitTetraDesign_isTie`, and its chart carries a datum
at `value = 0` with a TWELVE-member active family.  All three of "open cell",
"non-uniform", "extremal" hold at once, which no shipped witness achieves.

## THE MULTIPLIERS AT `(6,3)` ARE NOT THE DESIGN-SIDE ONES — a correction

The campaign brief this file was built from records the split-`(6,3)` cone
multipliers as `1/144` on the four triples carrying both singleton atoms and
`1/288` on the other eight, i.e. in RATIO `2 : 1`.  That ratio is the DESIGN-side
answer, not the chart one.

On the design side the tight direction of a tied triple is the missed tetrahedron
direction `v_d`, normalised; the coverage law `sum_{C ∋ c} lambda_C ⟨u_C, g_c⟩² =
t_c * value` then reads `sum_{C ∋ c} lambda_C = 3 t_c`, whose solution is `1/8` on
the four and `1/16` on the eight — ratio `2 : 1`, and `1/144 : 1/288` after the
brief's normalisation.

In the chart the tight direction is instead proportional to `(1/sqrt t_c)` on the
triple, and the constant-diagonal condition `Xi_cc = 1/6` forces `1/9` on the four
and `5/72` on the eight — ratio `8 : 5`.  Feeding the design-side ratio into the
chart gives `Xi_00 = 7/40` against `Xi_22 = 13/80`, neither equal to `1/6`, so it
fails `assembly_diagonal` outright; `chartSplitSix_designMultiplier_not_constant_diagonal`
mechanizes that failure.  This is the same phenomenon
`Gtz.Quantitative.ChartStationary`'s header records for the `(7,3)` split seven —
residuals `1/140`, `1/1280`, `1/560` — now with an EXACT `(6,3)` witness on both
sides: the chart system IS satisfiable at that point, by a DIFFERENT multiplier
vector.  [The design-side values `1/8` and `1/16` are stated here as arithmetic,
outside Lean; only the chart values and the failure of the design-side ratio are
mechanized.]

## THE BRIEF'S CORANK-ONE WEIGHTS HAVE AN IRRATIONAL CHART — a second correction

The brief asks for the corank-one member at weights `(2/3, 1/9, 1/9, 1/9)`.  A
corank-one chart at `(4,3)` is `P = 1 - z zᵀ` with `|z| = 1`, and every subset
being tight at value `0` forces `z_c² = (1 - t_c)/3` — derived below the fold, and
visible in the data as `t_c = 1 - 3 z_c²`.  At the brief's weights that gives
`z_0² = 1/9` but `z_1² = 8/27`, whose product is not the square of a rational, so
`z_0 z_1` is irrational and the chart is NOT a rational matrix.  The rational
members are exactly those with `z` proportional to a rational vector; the smallest
non-uniform one is `z ∝ (2, 2, 2, 1)`, giving the weights `(1/13, 1/13, 1/13,
10/13)` used below.  Nothing is lost: the family is one-parameter-per-atom and the
brief's member and this one lie on the same locus.

## WHAT IS NOT CLAIMED

Instantiation is not derivation.  None of these three points is proved to BE a
critical point of the chart objective — the variational analysis that would
produce the bundle stays outside Lean, exactly as
`Gtz.Quantitative.ChartStationary`'s honesty section says.  Nor is any of them
proved ADMISSIBLE (`Gtz.IsChartArgmaxValue`): admissibility is an existential over
every `rank`-subset, and the bundle is satisfied at admissible non-minima anyway,
so establishing it would not upgrade a witness into an exclusion.  What these
theorems establish is exactly inhabitation — at a certified tie, at non-uniform
weights, and at the open cell.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.StressCertificate
import Gtz.Ties.SplitTetrahedronTie
import Gtz.Ties.TetrahedronCertifiedTie
import Gtz.Quantitative.ChartStationary
import Gtz.Quantitative.ChartMultiplierSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The tetrahedron, carried by the design and paired with its tie

`Gtz.chartTetraProjection_isChartStationaryData` states the datum for the raw
matrix `1 - J/4`.  `Gtz.projectionOfDesign_tetraDesign_eq` and
`Gtz.tetraDesign_weight_eq` identify that matrix and that weight vector with the
tetrahedron design's, so the datum transports to the design's chart verbatim.
Pairing it with `Gtz.tetraDesign_isTie` is what makes the inhabitation
non-degenerate: the point is an exact tie of the GTZ problem, certified elsewhere
in this repository by an argument that knows nothing about stationarity. -/

/-- **The tetrahedron datum, on the DESIGN's chart.**  Rank three, four atoms,
`value = 0`, four active triples, assembly `I_4/12 + J_4/6`. -/
theorem tetraDesign_isChartStationaryData :
    IsChartStationaryData 3 (projectionOfDesign tetraDesign) tetraDesign.weight 0
      (Finset.univ : Finset (Fin 4)) chartTetraSubset chartTetraMultiplierWeight
      chartTetraTightDir := by
  rw [projectionOfDesign_tetraDesign_eq, tetraDesign_weight_eq]
  exact chartTetraProjection_isChartStationaryData

/-- **THE BUNDLE IS INHABITED AT A CERTIFIED EXACT TIE.**  There is a weighted
`(4,3)` design which is an exact tie — its best subset dominates weakly and none
dominates strictly — whose chart carries a chart stationarity datum at value zero.

This is the non-degeneracy statement the file exists for.  `IsTie` is proved in
`Gtz.Ties.TetrahedronCertifiedTie` from the Gram data alone, with no reference to
multipliers, tight directions or stationarity of any kind; so the two halves of
this conjunction are established by arguments that do not share a hypothesis. -/
theorem exists_isTie_and_isChartStationaryData :
    ∃ (design : WeightedDesign 4 3) (activeSubset : Fin 4 → Finset (Fin 4))
      (activeWeight : Fin 4 → ℝ) (tightDir : Fin 4 → (Fin 4 → ℝ)),
      IsTie design ∧
        IsChartStationaryData 3 (projectionOfDesign design) design.weight 0
          (Finset.univ : Finset (Fin 4)) activeSubset activeWeight tightDir :=
  ⟨tetraDesign, chartTetraSubset, chartTetraMultiplierWeight, chartTetraTightDir,
    tetraDesign_isTie, tetraDesign_isChartStationaryData⟩

/-! ## A corank-one chart point at `(4,3)` with NON-UNIFORM rational weights

A corank-one chart at `(4,3)` is `P = 1 - z zᵀ` with `z` a unit vector, which is
symmetric, idempotent and of trace three for free.  Ask that all four triples be
tight at value zero: a vector `u` supported on the triple missing `d` satisfies
`W u = 0` on that triple exactly when `u_c (1 - t_c) = z_c (z · u)` there, so
either `z · u = 0`, which forces `u = 0` because every weight on a four-atom
simplex is strictly below one, or
`u_c ∝ z_c/(1 - t_c)` together with the secular equation
`sum_{c ≠ d} z_c²/(1 - t_c) = 1`.  Subtracting two of those four equations makes
every `z_c²/(1 - t_c)` equal, so each is `1/3`, and

    `t_c = 1 - 3 z_c²` ,        `u^{(d)}_c ∝ 1/z_c` on the triple missing `d`.

The weights then sum to one automatically, because `|z| = 1`.  So the family is
parametrised by the unit vector `z` alone, subject to `z_c² < 1/3` at every atom,
which is exactly `t_c > 0`.  RATIONALITY of the chart asks that every `z_c z_d` be
rational, i.e. that `z` be a rational vector times a scalar; the smallest
non-uniform choice is `z ∝ (2, 2, 2, 1)`, of squared length `13`.

Everything below is that instance, written out.  The multipliers come from the
constant-diagonal condition alone: with `mu_d := lambda_d / N_d` and
`N_d = sum_{c ≠ d} 1/z_c²`, condition (CS2) reads `sum_{d ≠ c} mu_d = z_c²/4`,
whose solution is `mu_d = 1/12 - z_d²/4`, and `sum_d lambda_d = 1` then holds
identically rather than by imposition.  The assembly also satisfies `Xi z = (3/4) z`
identically along the family, which is why it commutes with `P` — and why the
kernel block `N` is `3/4` at every member, not only at the tetrahedron. -/

/-- The kernel direction of the corank-one chart, cleared of its normalisation:
`(2, 2, 2, 1)`, of squared length `13`.  Atom `3` is the HEAVY one throughout this
section — the one whose kernel coordinate is small and whose weight is therefore
large.  The unit kernel vector is this over `sqrt 13`, and only the products
`z_c z_d = a_c a_d / 13` ever appear. -/
def chartCorankOneKernel : Fin 4 → ℝ := fun atomIndex => if atomIndex = 3 then 1 else 2

/-- The corank-one chart `P = 1 - z zᵀ`: `9/13` on the three light atoms' diagonal,
`12/13` on the heavy one's, `-4/13` between light atoms and `-2/13` between a light
atom and the heavy one. -/
noncomputable def chartCorankOneProjection : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    (if rowIndex = colIndex then 1 else 0)
      - chartCorankOneKernel rowIndex * chartCorankOneKernel colIndex / 13

/-- The NON-UNIFORM weights `t_c = 1 - 3 z_c²`, a ten-to-one spread. -/
noncomputable def chartCorankOneWeight : Fin 4 → ℝ :=
  fun atomIndex => if atomIndex = 3 then 10 / 13 else 1 / 13

/-- The multipliers `lambda_d = (1/12 - z_d²/4) * N_d`, forced by the constant
diagonal and summing to one identically. -/
noncomputable def chartCorankOneMultiplierWeight : Fin 4 → ℝ :=
  fun missingIndex => if missingIndex = 3 then 5 / 8 else 1 / 8

/-- The reciprocal kernel direction, cleared of denominators: `1/z_c` is
proportional to `(1, 1, 1, 2)`. -/
def chartCorankOneReciprocal : Fin 4 → ℝ := fun atomIndex => if atomIndex = 3 then 2 else 1

/-- The UNNORMALISED tight direction of the triple missing `missingIndex`: the
reciprocal kernel direction, cut down to that triple. -/
def chartCorankOneSupport (missingIndex : Fin 4) : Fin 4 → ℝ :=
  fun atomIndex => if atomIndex = missingIndex then 0 else chartCorankOneReciprocal atomIndex

/-- The squared length of the unnormalised tight direction: `3` when the heavy atom
is the one omitted, `6` otherwise. -/
def chartCorankOneNormSq (missingIndex : Fin 4) : ℝ := if missingIndex = 3 then 3 else 6

/-- The tight direction of the triple missing `missingIndex`, normalised. -/
noncomputable def chartCorankOneTightDir (missingIndex : Fin 4) : Fin 4 → ℝ :=
  (Real.sqrt (chartCorankOneNormSq missingIndex))⁻¹ • chartCorankOneSupport missingIndex

/-- The corank-one assembly `Xi`: `1/4` on the diagonal — which is `1/size`, as
(CS2) demands — `11/48` between light atoms, and `1/12` between a light atom and
the heavy one. -/
noncomputable def chartCorankOneMultiplier : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    if rowIndex = colIndex then 1 / 4
    else if rowIndex = 3 ∨ colIndex = 3 then 1 / 12
    else 11 / 48

theorem chartCorankOneNormSq_pos (missingIndex : Fin 4) :
    0 < chartCorankOneNormSq missingIndex := by
  fin_cases missingIndex <;> norm_num [chartCorankOneNormSq, Fin.ext_iff]

theorem chartCorankOneProjection_transpose :
    chartCorankOneProjectionᵀ = chartCorankOneProjection := by
  ext rowIndex colIndex
  simp only [Matrix.transpose_apply, chartCorankOneProjection, Matrix.of_apply]
  by_cases hequal : rowIndex = colIndex
  · rw [hequal]
  · rw [if_neg (Ne.symm hequal), if_neg hequal]
    ring

theorem chartCorankOneProjection_mul_self :
    chartCorankOneProjection * chartCorankOneProjection = chartCorankOneProjection := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [chartCorankOneProjection, chartCorankOneKernel, Fin.ext_iff]

/-- The corank-one gap `W = P - diag t`: `8/13` and `2/13` on the diagonal,
`-4/13` and `-2/13` off it. -/
theorem chartCorankOneGap_apply (rowIndex colIndex : Fin 4) :
    chartStationaryGap chartCorankOneProjection chartCorankOneWeight rowIndex colIndex
      = (if rowIndex = colIndex then (if rowIndex = 3 then 2 / 13 else 8 / 13)
          else if rowIndex = 3 ∨ colIndex = 3 then -(2 / 13) else -(4 / 13)) := by
  simp only [chartStationaryGap, Matrix.sub_apply, chartCorankOneProjection, Matrix.of_apply,
    Matrix.diagonal_apply, chartCorankOneWeight]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [chartCorankOneKernel, Fin.ext_iff]

/-- The unnormalised tight direction has the squared length its name records. -/
theorem chartCorankOneSupport_dotProduct_self (missingIndex : Fin 4) :
    chartCorankOneSupport missingIndex ⬝ᵥ chartCorankOneSupport missingIndex
      = chartCorankOneNormSq missingIndex := by
  simp only [dotProduct, chartCorankOneSupport, chartCorankOneReciprocal, chartCorankOneNormSq,
    Fin.sum_univ_four]
  fin_cases missingIndex <;> norm_num [Fin.ext_iff]

/-- **THE CHART POINT IS EXTREMAL**: the gap annihilates each triple's tight
direction, coordinatewise ON that triple.  Off the triple the same product is
nonzero, which is exactly why the bundle's tightness field is restricted to the
subset. -/
theorem chartCorankOneGap_mulVec_support (missingIndex atomIndex : Fin 4)
    (hdistinct : atomIndex ≠ missingIndex) :
    (chartStationaryGap chartCorankOneProjection chartCorankOneWeight *ᵥ
        chartCorankOneSupport missingIndex) atomIndex = 0 := by
  simp only [Matrix.mulVec, dotProduct, chartCorankOneGap_apply, chartCorankOneSupport,
    chartCorankOneReciprocal, Fin.sum_univ_four]
  fin_cases missingIndex <;> fin_cases atomIndex <;> simp_all [Fin.ext_iff] <;> norm_num

/-- **THE CORANK-ONE ASSEMBLY**: `1/4` on the diagonal, `11/48` between light atoms,
`1/12` against the heavy atom.  Each triple contributes its multiplier over its
squared length — `1/48` for the three triples containing the heavy atom and `5/24`
for the one that omits it. -/
theorem chartCorankOneMultiplierAssembly_eq :
    chartMultiplierAssembly (Finset.univ : Finset (Fin 4)) chartCorankOneMultiplierWeight
        chartCorankOneTightDir
      = chartCorankOneMultiplier := by
  have hscale : ∀ missingIndex : Fin 4,
      chartCorankOneMultiplierWeight missingIndex • atomMatrix (chartCorankOneTightDir missingIndex)
        = (chartCorankOneMultiplierWeight missingIndex / chartCorankOneNormSq missingIndex)
            • atomMatrix (chartCorankOneSupport missingIndex) := by
    intro missingIndex
    have hsquare : (Real.sqrt (chartCorankOneNormSq missingIndex)) ^ 2
        = chartCorankOneNormSq missingIndex :=
      Real.sq_sqrt (chartCorankOneNormSq_pos missingIndex).le
    rw [chartCorankOneTightDir, atomMatrix_smul, inv_pow, hsquare, smul_smul, div_eq_mul_inv]
  rw [chartMultiplierAssembly, Finset.sum_congr rfl fun missingIndex _ => hscale missingIndex]
  ext rowIndex colIndex
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
    Matrix.vecMulVec_apply, chartCorankOneSupport, chartCorankOneReciprocal,
    chartCorankOneMultiplierWeight, chartCorankOneNormSq, chartCorankOneMultiplier,
    Matrix.of_apply, Fin.sum_univ_four]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Fin.ext_iff]

/-- **THE CORANK-ONE DATUM, AT NON-UNIFORM WEIGHTS.**  Rank three, four atoms,
weights `(1/13, 1/13, 1/13, 10/13)`, `value = 0`, four active triples, assembly
`Xi` with constant diagonal `1/4`.

The weight spread is the point.  `Gtz.diagonal_projection_mul_multiplier_of_isChartStationaryData`
reads `(P Xi)_cc = t_c/4` here, which is `1/52` at three atoms and `10/52` at the
fourth; at a uniform witness that theorem cannot be distinguished from a constant.

The active family is `Gtz.chartTetraSubset`, reused rather than redeclared: at
`(4,3)` the `rank`-subsets are exactly the complements of single atoms, so the
tetrahedron's index family is the corank-one family too. -/
theorem chartCorankOneProjection_isChartStationaryData :
    IsChartStationaryData 3 chartCorankOneProjection chartCorankOneWeight 0
      (Finset.univ : Finset (Fin 4)) chartTetraSubset chartCorankOneMultiplierWeight
      chartCorankOneTightDir where
  isSymmetric := chartCorankOneProjection_transpose
  isIdempotent := chartCorankOneProjection_mul_self
  hasTraceRank := by
    show ∑ atomIndex : Fin 4, chartCorankOneProjection atomIndex atomIndex = ((3 : ℕ) : ℝ)
    rw [Fin.sum_univ_four]
    norm_num [chartCorankOneProjection, chartCorankOneKernel, Fin.ext_iff]
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;> norm_num [chartCorankOneWeight, Fin.ext_iff]
  weight_sum_one := by norm_num [chartCorankOneWeight, Fin.sum_univ_four, Fin.ext_iff]
  activeWeight_nonneg := by
    intro missingIndex _
    fin_cases missingIndex <;> norm_num [chartCorankOneMultiplierWeight, Fin.ext_iff]
  activeWeight_sum_one := by
    norm_num [chartCorankOneMultiplierWeight, Fin.sum_univ_four, Fin.ext_iff]
  activeSubset_card := by intro missingIndex _; fin_cases missingIndex <;> decide
  tightDir_unit := by
    intro missingIndex _
    have hpositive := chartCorankOneNormSq_pos missingIndex
    have hsquare : Real.sqrt (chartCorankOneNormSq missingIndex)
        * Real.sqrt (chartCorankOneNormSq missingIndex) = chartCorankOneNormSq missingIndex :=
      Real.mul_self_sqrt hpositive.le
    rw [chartCorankOneTightDir, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      chartCorankOneSupport_dotProduct_self, ← mul_assoc, ← mul_inv, hsquare]
    exact inv_mul_cancel₀ (ne_of_gt hpositive)
  tightDir_support := by
    intro missingIndex _ atomIndex hnotMem
    have hequal : atomIndex = missingIndex := by
      by_contra hdistinct
      exact hnotMem (Finset.mem_erase.mpr ⟨hdistinct, Finset.mem_univ atomIndex⟩)
    simp only [chartCorankOneTightDir, Pi.smul_apply, chartCorankOneSupport, if_pos hequal,
      smul_zero]
  tightDir_isTight := by
    intro missingIndex _ atomIndex hmem
    simp only [chartTetraSubset] at hmem
    have hdistinct : atomIndex ≠ missingIndex := Finset.ne_of_mem_erase hmem
    rw [chartCorankOneTightDir, Matrix.mulVec_smul, Pi.smul_apply,
      chartCorankOneGap_mulVec_support missingIndex atomIndex hdistinct, smul_zero, zero_mul]
  assembly_diagonal := by
    intro atomIndex
    rw [chartCorankOneMultiplierAssembly_eq, chartCorankOneMultiplier, Matrix.of_apply, if_pos rfl]
    norm_num
  assembly_commutes := by
    rw [chartCorankOneMultiplierAssembly_eq]
    ext rowIndex colIndex
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [chartCorankOneProjection, chartCorankOneKernel, chartCorankOneMultiplier,
        Fin.ext_iff]

/-- **The bundle is inhabited at NON-UNIFORM weights.**  So the weight-dependent
consequences — the forced diagonal, the weight floor, the dual bound — are not
statements whose weight argument could be a constant in disguise. -/
theorem exists_isChartStationaryData_weight_ne :
    ∃ (projection : Matrix (Fin 4) (Fin 4) ℝ) (weight : Fin 4 → ℝ)
      (activeSubset : Fin 4 → Finset (Fin 4)) (activeWeight : Fin 4 → ℝ)
      (tightDir : Fin 4 → (Fin 4 → ℝ)),
      IsChartStationaryData 3 projection weight 0 (Finset.univ : Finset (Fin 4))
          activeSubset activeWeight tightDir
        ∧ weight 0 ≠ weight 3 :=
  ⟨chartCorankOneProjection, chartCorankOneWeight, chartTetraSubset,
    chartCorankOneMultiplierWeight, chartCorankOneTightDir,
    chartCorankOneProjection_isChartStationaryData, by norm_num [chartCorankOneWeight, Fin.ext_iff]⟩

/-! ## The split family at the OPEN cell `(6,3)`, at value zero

`Gtz.splitTetraDesign` keeps two tetrahedron directions and DUPLICATES the other
two, splitting each duplicated direction's weight `1/4` between its two copies.
At the balanced split the weights are `(1/4, 1/4, 1/8, 1/8, 1/8, 1/8)`, and
`Gtz.splitTetraDesign_isTie` proves the design is an exact tie.

The tie structure is direction-theoretic and reads straight off the tetrahedron's
Gram data.  All four tetrahedron directions pair to `-1`, so a triple carrying
three DISTINCT directions has `Gram - 1 = 3 - J` on that triple, which is positive
semidefinite with the all-ones direction in its kernel; a triple that repeats a
direction has a `+3` off the diagonal and is indefinite.  There are exactly twelve
of the first kind — two directions supply one atom each and two supply two, so
`2 + 2 + 4 + 4 = 12` — and every one of them is tight at chart value ZERO.

The congruence `W[C] = D_C^{1/2} (Gram_C - 1) D_C^{1/2}` moves the all-ones kernel
vector to `(1/sqrt t_c)` on the triple, which is `chartSplitSixScale` up to the
factor two.  So the tight direction is `1` at a singleton atom and `sqrt 2` at a
duplicated one, of squared length `4` on the four triples carrying both singleton
atoms and `5` on the other eight — and those are the only two irrationalities in
the whole section. -/

/-- The split tetrahedron at the balanced split: a genuine `(6,3)` design with
weights `(1/4, 1/4, 1/8, 1/8, 1/8, 1/8)`, and an exact tie. -/
noncomputable def chartSplitSixDesign : WeightedDesign 6 3 :=
  splitTetraDesign (1 / 8) (1 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The split design's weights: `1/4` at the two singleton atoms, `1/8` at the four
duplicated ones. -/
noncomputable def chartSplitSixWeight : Fin 6 → ℝ :=
  fun atomIndex => if (atomIndex : ℕ) < 2 then 1 / 4 else 1 / 8

/-- The square roots of those weights. -/
noncomputable def chartSplitSixRoot : Fin 6 → ℝ :=
  fun atomIndex => if (atomIndex : ℕ) < 2 then 1 / 2 else Real.sqrt 2 / 4

theorem chartSplitSixWeight_pos (atomIndex : Fin 6) : 0 < chartSplitSixWeight atomIndex := by
  simp only [chartSplitSixWeight]
  split <;> norm_num

theorem chartSplitSixDesign_weight_eq : chartSplitSixDesign.weight = chartSplitSixWeight := by
  funext atomIndex
  simp only [chartSplitSixDesign, splitTetraDesign_weight, chartSplitSixWeight]
  fin_cases atomIndex <;> norm_num

/-- The square root of a split weight, in closed form. -/
theorem sqrt_chartSplitSixWeight (atomIndex : Fin 6) :
    Real.sqrt (chartSplitSixWeight atomIndex) = chartSplitSixRoot atomIndex := by
  simp only [chartSplitSixWeight, chartSplitSixRoot]
  by_cases hsingle : (atomIndex : ℕ) < 2
  · rw [if_pos hsingle, if_pos hsingle, show (1 : ℝ) / 4 = ((1 : ℝ) / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  · rw [if_neg hsingle, if_neg hsingle,
      show (1 : ℝ) / 8 = (Real.sqrt 2 / 4) ^ 2 by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num,
      Real.sqrt_sq (by positivity)]

/-- The atom pairing `⟨g_c, g_d⟩`: the two atoms carry tetrahedron directions, and
all four of those pair to `-1` off the diagonal and to `3` on it. -/
def chartSplitSixPairing (rowIndex colIndex : Fin 6) : ℝ :=
  if splitTetraDirIndex rowIndex = splitTetraDirIndex colIndex then 3 else -1

/-- **The tetrahedron Gram data, read along the duplication map**: `3` when two
atoms carry the same direction and `-1` when they do not. -/
theorem chartSplitSixDesign_atom_dotProduct (rowIndex colIndex : Fin 6) :
    chartSplitSixDesign.atom rowIndex ⬝ᵥ chartSplitSixDesign.atom colIndex
      = chartSplitSixPairing rowIndex colIndex := by
  simp only [chartSplitSixDesign, splitTetraDesign_atom, splitTetraAtom, chartSplitSixPairing]
  by_cases hsame : splitTetraDirIndex rowIndex = splitTetraDirIndex colIndex
  · rw [if_pos hsame, hsame, tetraAtom_dot_self]
  · rw [if_neg hsame, tetraAtom_dot_of_ne hsame]

/-- The split design's chart, entrywise: `P_cd = sqrt(t_c t_d) * ⟨g_c, g_d⟩`. -/
noncomputable def chartSplitSixProjection : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    chartSplitSixRoot rowIndex * chartSplitSixRoot colIndex * chartSplitSixPairing rowIndex colIndex

theorem projectionOfDesign_chartSplitSixDesign_eq :
    projectionOfDesign chartSplitSixDesign = chartSplitSixProjection := by
  ext rowIndex colIndex
  rw [projectionOfDesign_apply, chartSplitSixDesign_weight_eq, sqrt_chartSplitSixWeight,
    sqrt_chartSplitSixWeight, chartSplitSixDesign_atom_dotProduct, chartSplitSixProjection,
    Matrix.of_apply]

/-- The split gap `W = P - diag t`, entrywise. -/
theorem chartSplitSixGap_apply (rowIndex colIndex : Fin 6) :
    chartStationaryGap chartSplitSixProjection chartSplitSixWeight rowIndex colIndex
      = chartSplitSixRoot rowIndex * chartSplitSixRoot colIndex
          * chartSplitSixPairing rowIndex colIndex
        - (if rowIndex = colIndex then chartSplitSixWeight rowIndex else 0) := by
  simp only [chartStationaryGap, Matrix.sub_apply, chartSplitSixProjection, Matrix.of_apply,
    Matrix.diagonal_apply]

/-- The twelve triples carrying three DISTINCT tetrahedron directions.  Labels
`0`-`3` carry both singleton atoms; labels `4`-`11` carry exactly one. -/
def chartSplitSixSubset : Fin 12 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5},
    {0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5},
    {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 3, 5}]

/-- **THE CHART MULTIPLIERS**, forced by the constant diagonal: `1/9` on the four
triples carrying both singleton atoms and `5/72` on the other eight.  The ratio is
`8 : 5`, NOT the design side's `2 : 1` — see the header. -/
noncomputable def chartSplitSixMultiplierWeight : Fin 12 → ℝ :=
  fun activeLabel => if (activeLabel : ℕ) < 4 then 1 / 9 else 5 / 72

/-- The per-atom scale of a tight direction, `1/(2 sqrt t_c)`: `1` at a singleton
atom and `sqrt 2` at a duplicated one. -/
noncomputable def chartSplitSixScale : Fin 6 → ℝ :=
  fun atomIndex => if (atomIndex : ℕ) < 2 then 1 else Real.sqrt 2

/-- The UNNORMALISED tight direction of an active triple: the scale, cut down to
the triple. -/
noncomputable def chartSplitSixSupport (activeLabel : Fin 12) : Fin 6 → ℝ :=
  fun atomIndex =>
    if atomIndex ∈ chartSplitSixSubset activeLabel then chartSplitSixScale atomIndex else 0

/-- The squared length of that support: `4` on the four triples carrying both
singleton atoms, `5` on the other eight. -/
noncomputable def chartSplitSixNormSq : Fin 12 → ℝ :=
  fun activeLabel => if (activeLabel : ℕ) < 4 then 4 else 5

/-- The tight direction of an active triple, normalised. -/
noncomputable def chartSplitSixTightDir (activeLabel : Fin 12) : Fin 6 → ℝ :=
  (Real.sqrt (chartSplitSixNormSq activeLabel))⁻¹ • chartSplitSixSupport activeLabel

theorem chartSplitSixNormSq_pos (activeLabel : Fin 12) : 0 < chartSplitSixNormSq activeLabel := by
  simp only [chartSplitSixNormSq]
  split <;> norm_num

theorem chartSplitSixSupport_dotProduct_self (activeLabel : Fin 12) :
    chartSplitSixSupport activeLabel ⬝ᵥ chartSplitSixSupport activeLabel
      = chartSplitSixNormSq activeLabel := by
  have hroot : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [dotProduct, chartSplitSixSupport, chartSplitSixScale, chartSplitSixNormSq,
    Fin.sum_univ_six]
  fin_cases activeLabel <;> simp [chartSplitSixSubset, hroot] <;> norm_num

/-- **The scale undoes the square root**: `scale_c * sqrt(t_c) = 1/2` at every
atom.  This is the ONE identity in the section that consumes `sqrt 2 * sqrt 2 = 2`,
and every later computation is rational because of it. -/
theorem chartSplitSixScale_mul_root (atomIndex : Fin 6) :
    chartSplitSixScale atomIndex * chartSplitSixRoot atomIndex = 1 / 2 := by
  have hroot : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [chartSplitSixScale, chartSplitSixRoot]
  split
  · norm_num
  · rw [← mul_div_assoc, hroot]
    norm_num

theorem chartSplitSixWeight_eq_root_mul_root (atomIndex : Fin 6) :
    chartSplitSixWeight atomIndex
      = chartSplitSixRoot atomIndex * chartSplitSixRoot atomIndex := by
  rw [← sqrt_chartSplitSixWeight]
  exact (Real.mul_self_sqrt (chartSplitSixWeight_pos atomIndex).le).symm

/-- **THE SQUARE ROOTS CANCEL.**  Scaling a gap entry by the tight direction's
scale leaves a RATIONAL multiple of one square root:

    `W_cd * scale_d = sqrt(t_c) * (⟨g_c, g_d⟩ / 2 - [c = d] / 2)` .

Everything downstream is this identity summed over a triple. -/
theorem chartSplitSixGap_mul_scale (rowIndex colIndex : Fin 6) :
    chartStationaryGap chartSplitSixProjection chartSplitSixWeight rowIndex colIndex
        * chartSplitSixScale colIndex
      = chartSplitSixRoot rowIndex
          * (chartSplitSixPairing rowIndex colIndex / 2
             - (if rowIndex = colIndex then 1 / 2 else 0)) := by
  have hscale := chartSplitSixScale_mul_root colIndex
  rw [chartSplitSixGap_apply]
  by_cases hdiagonal : rowIndex = colIndex
  · subst hdiagonal
    rw [if_pos rfl, if_pos rfl, chartSplitSixWeight_eq_root_mul_root]
    linear_combination (chartSplitSixRoot rowIndex * chartSplitSixPairing rowIndex rowIndex
      - chartSplitSixRoot rowIndex) * hscale
  · rw [if_neg hdiagonal, if_neg hdiagonal]
    linear_combination (chartSplitSixRoot rowIndex * chartSplitSixPairing rowIndex colIndex)
      * hscale

set_option maxHeartbeats 1000000 in
/-- **THE COMBINATORIAL CORE**: an active triple carries three DISTINCT tetrahedron
directions, so an atom of it pairs `3` with itself and `-1` with each of the other
two — total `1`, which the diagonal correction then cancels.  This is the only
place the twelve triples are inspected one by one, and the arithmetic is rational. -/
theorem chartSplitSixPairingSum (activeLabel : Fin 12) (atomIndex : Fin 6)
    (hmem : atomIndex ∈ chartSplitSixSubset activeLabel) :
    ∑ colIndex : Fin 6,
        (if colIndex ∈ chartSplitSixSubset activeLabel then
          chartSplitSixPairing atomIndex colIndex / 2
            - (if atomIndex = colIndex then 1 / 2 else 0)
         else 0) = 0 := by
  simp only [chartSplitSixPairing, Fin.sum_univ_six]
  fin_cases activeLabel <;> fin_cases atomIndex <;>
    simp_all [chartSplitSixSubset, splitTetraDirIndex, Fin.ext_iff] <;> norm_num

/-- **THE SPLIT CHART POINT IS EXTREMAL**: the gap annihilates every active
triple's tight direction, coordinatewise ON that triple.

Off the triple the same product is nonzero, which is why the bundle's tightness
field is restricted to the subset. -/
theorem chartSplitSixGap_mulVec_support (activeLabel : Fin 12) (atomIndex : Fin 6)
    (hmem : atomIndex ∈ chartSplitSixSubset activeLabel) :
    (chartStationaryGap chartSplitSixProjection chartSplitSixWeight *ᵥ
        chartSplitSixSupport activeLabel) atomIndex = 0 := by
  have hterm : ∀ colIndex : Fin 6,
      chartStationaryGap chartSplitSixProjection chartSplitSixWeight atomIndex colIndex
          * chartSplitSixSupport activeLabel colIndex
        = chartSplitSixRoot atomIndex
            * (if colIndex ∈ chartSplitSixSubset activeLabel then
                chartSplitSixPairing atomIndex colIndex / 2
                  - (if atomIndex = colIndex then 1 / 2 else 0)
               else 0) := by
    intro colIndex
    simp only [chartSplitSixSupport]
    by_cases hinSubset : colIndex ∈ chartSplitSixSubset activeLabel
    · rw [if_pos hinSubset, if_pos hinSubset, chartSplitSixGap_mul_scale]
    · rw [if_neg hinSubset, if_neg hinSubset, mul_zero, mul_zero]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun colIndex _ => hterm colIndex, ← Finset.mul_sum,
    chartSplitSixPairingSum activeLabel atomIndex hmem, mul_zero]

/-- **THE SPLIT ASSEMBLY** `Xi`: `1/6` on the diagonal — which is `1/size`, as (CS2)
demands — `1/9` between the two singleton atoms, `sqrt 2 / 18` between a singleton
and a duplicated atom, `0` between two copies of the SAME direction, and `1/18`
between copies of different directions. -/
noncomputable def chartSplitSixMultiplier : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    if rowIndex = colIndex then 1 / 6
    else if (rowIndex : ℕ) < 2 then (if (colIndex : ℕ) < 2 then 1 / 9 else Real.sqrt 2 / 18)
    else if (colIndex : ℕ) < 2 then Real.sqrt 2 / 18
    else if splitTetraDirIndex rowIndex = splitTetraDirIndex colIndex then 0
    else 1 / 18

set_option maxHeartbeats 1000000 in
/-- Each active triple contributes its multiplier over its squared length: `1/36`
on the four carrying both singleton atoms, `1/72` on the other eight. -/
theorem chartSplitSixMultiplierAssembly_eq :
    chartMultiplierAssembly (Finset.univ : Finset (Fin 12)) chartSplitSixMultiplierWeight
        chartSplitSixTightDir
      = chartSplitSixMultiplier := by
  have hroot : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hnormalise : ∀ activeLabel : Fin 12,
      chartSplitSixMultiplierWeight activeLabel • atomMatrix (chartSplitSixTightDir activeLabel)
        = (chartSplitSixMultiplierWeight activeLabel / chartSplitSixNormSq activeLabel)
            • atomMatrix (chartSplitSixSupport activeLabel) := by
    intro activeLabel
    have hsquare : (Real.sqrt (chartSplitSixNormSq activeLabel)) ^ 2
        = chartSplitSixNormSq activeLabel :=
      Real.sq_sqrt (chartSplitSixNormSq_pos activeLabel).le
    rw [chartSplitSixTightDir, atomMatrix_smul, inv_pow, hsquare, smul_smul, div_eq_mul_inv]
  rw [chartMultiplierAssembly, Finset.sum_congr rfl fun activeLabel _ => hnormalise activeLabel]
  ext rowIndex colIndex
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
    Matrix.vecMulVec_apply, chartSplitSixSupport, chartSplitSixScale,
    chartSplitSixMultiplierWeight, chartSplitSixNormSq, chartSplitSixMultiplier, Matrix.of_apply]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [chartSplitSixSubset, splitTetraDirIndex, Fin.ext_iff, hroot, Fin.sum_univ_succ] <;>
    ring

/-- **The split chart, as a rational table plus one linear `sqrt 2`.**  Between two
singleton atoms the entries are `3/4` and `-1/4`; between a singleton and a
duplicated atom, `-sqrt 2 / 8`; between two duplicated atoms, `3/8` when they carry
the same direction and `-1/8` when they do not.  Stating it this way is what keeps
the commutation computation below inside a rational ring extended by one square
root. -/
theorem chartSplitSixProjection_apply (rowIndex colIndex : Fin 6) :
    chartSplitSixProjection rowIndex colIndex
      = if (rowIndex : ℕ) < 2 then
          (if (colIndex : ℕ) < 2 then (if rowIndex = colIndex then 3 / 4 else -(1 / 4))
           else -(Real.sqrt 2 / 8))
        else if (colIndex : ℕ) < 2 then -(Real.sqrt 2 / 8)
        else if splitTetraDirIndex rowIndex = splitTetraDirIndex colIndex then 3 / 8
        else -(1 / 8) := by
  have hroot : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [chartSplitSixProjection, Matrix.of_apply, chartSplitSixRoot, chartSplitSixPairing]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [splitTetraDirIndex, Fin.ext_iff] <;>
    linarith [hroot]

set_option maxHeartbeats 1000000 in
/-- **THE SPLIT ASSEMBLY COMMUTES WITH THE CHART.**  This is the Grassmannian half
of stationarity, and unlike the octahedron's scalar assembly it is a genuine
condition: `Xi` here is not a multiple of the identity. -/
theorem chartSplitSixProjection_mul_multiplier_comm :
    chartSplitSixProjection * chartSplitSixMultiplier
      = chartSplitSixMultiplier * chartSplitSixProjection := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_six]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num +decide [chartSplitSixProjection_apply, chartSplitSixMultiplier] <;> ring

/-- **THE SPLIT DATUM AT THE OPEN CELL.**  Rank three, six atoms, weights
`(1/4, 1/4, 1/8, 1/8, 1/8, 1/8)`, `value = 0`, TWELVE active triples, assembly with
constant diagonal `1/6`.

Three of the five fields that are cheap here are cheap because the projection is a
DESIGN's chart: symmetry, idempotence and the trace come from
`Gtz.projectionOfDesign_transpose`, `Gtz.projectionOfDesign_mul_self` and
`Gtz.trace_projectionOfDesign`, so Parseval is doing the work rather than a
six-by-six computation. -/
theorem chartSplitSixProjection_isChartStationaryData :
    IsChartStationaryData 3 chartSplitSixProjection chartSplitSixWeight 0
      (Finset.univ : Finset (Fin 12)) chartSplitSixSubset chartSplitSixMultiplierWeight
      chartSplitSixTightDir where
  isSymmetric := by
    rw [← projectionOfDesign_chartSplitSixDesign_eq]
    exact projectionOfDesign_transpose chartSplitSixDesign
  isIdempotent := by
    rw [← projectionOfDesign_chartSplitSixDesign_eq]
    exact projectionOfDesign_mul_self chartSplitSixDesign
  hasTraceRank := by
    rw [← projectionOfDesign_chartSplitSixDesign_eq]
    exact trace_projectionOfDesign chartSplitSixDesign
  weight_pos := chartSplitSixWeight_pos
  weight_sum_one := by
    simp only [chartSplitSixWeight, Fin.sum_univ_six]
    norm_num
  activeWeight_nonneg := by
    intro activeLabel _
    simp only [chartSplitSixMultiplierWeight]
    split <;> norm_num
  activeWeight_sum_one := by
    simp only [chartSplitSixMultiplierWeight]
    norm_num [Fin.sum_univ_succ]
  activeSubset_card := by intro activeLabel _; fin_cases activeLabel <;> decide
  tightDir_unit := by
    intro activeLabel _
    have hpositive := chartSplitSixNormSq_pos activeLabel
    have hsquare : Real.sqrt (chartSplitSixNormSq activeLabel)
        * Real.sqrt (chartSplitSixNormSq activeLabel) = chartSplitSixNormSq activeLabel :=
      Real.mul_self_sqrt hpositive.le
    rw [chartSplitSixTightDir, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      chartSplitSixSupport_dotProduct_self, ← mul_assoc, ← mul_inv, hsquare]
    exact inv_mul_cancel₀ (ne_of_gt hpositive)
  tightDir_support := by
    intro activeLabel _ atomIndex hnotMem
    simp only [chartSplitSixTightDir, Pi.smul_apply, chartSplitSixSupport, if_neg hnotMem,
      smul_zero]
  tightDir_isTight := by
    intro activeLabel _ atomIndex hmem
    rw [chartSplitSixTightDir, Matrix.mulVec_smul, Pi.smul_apply,
      chartSplitSixGap_mulVec_support activeLabel atomIndex hmem, smul_zero, zero_mul]
  assembly_diagonal := by
    intro atomIndex
    rw [chartSplitSixMultiplierAssembly_eq, chartSplitSixMultiplier, Matrix.of_apply, if_pos rfl]
    norm_num
  assembly_commutes := by
    rw [chartSplitSixMultiplierAssembly_eq]
    exact chartSplitSixProjection_mul_multiplier_comm

/-- The same datum, carried by the DESIGN's chart. -/
theorem chartSplitSixDesign_isChartStationaryData :
    IsChartStationaryData 3 (projectionOfDesign chartSplitSixDesign) chartSplitSixDesign.weight 0
      (Finset.univ : Finset (Fin 12)) chartSplitSixSubset chartSplitSixMultiplierWeight
      chartSplitSixTightDir := by
  rw [projectionOfDesign_chartSplitSixDesign_eq, chartSplitSixDesign_weight_eq]
  exact chartSplitSixProjection_isChartStationaryData

/-- The split design at the balanced split is an exact tie, by
`Gtz.splitTetraDesign_isTie`. -/
theorem chartSplitSixDesign_isTie : IsTie chartSplitSixDesign :=
  splitTetraDesign_isTie (1 / 8) (1 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **THE BUNDLE IS INHABITED AT THE OPEN CELL `(6,3)`, AT A TIE, AT NON-UNIFORM
WEIGHTS, AND AT VALUE ZERO — all four at once.**

`Gtz.exists_isChartStationaryData` already puts a witness at `(6,3)`, but at the
octahedron: uniform weights, `value = 1/3`, and no design behind the matrix.  This
one is a genuine weighted design, its weights spread two to one, its chart value is
exactly the extremal `0`, and `Gtz.splitTetraDesign_isTie` certifies the tie by an
argument that never mentions stationarity. -/
theorem exists_isTie_and_isChartStationaryData_sixThree :
    ∃ (design : WeightedDesign 6 3) (activeSubset : Fin 12 → Finset (Fin 6))
      (activeWeight : Fin 12 → ℝ) (tightDir : Fin 12 → (Fin 6 → ℝ)),
      IsTie design ∧ design.weight 0 ≠ design.weight 2 ∧
        IsChartStationaryData 3 (projectionOfDesign design) design.weight 0
          (Finset.univ : Finset (Fin 12)) activeSubset activeWeight tightDir := by
  refine ⟨chartSplitSixDesign, chartSplitSixSubset, chartSplitSixMultiplierWeight,
    chartSplitSixTightDir, chartSplitSixDesign_isTie, ?_, chartSplitSixDesign_isChartStationaryData⟩
  rw [chartSplitSixDesign_weight_eq]
  norm_num [chartSplitSixWeight]

/-! ### The design-side multipliers do NOT solve the chart system

On the design side the coverage law `sum_{C ∋ c} lambda_C ⟨u_C, g_c⟩² = t_c * value`
with the missed tetrahedron direction as the tight direction reads
`sum_{C ∋ c} lambda_C = 3 t_c`, whose solution is `1/8` on the four triples carrying
both singleton atoms and `1/16` on the other eight — the campaign brief's `1/144`
and `1/288` up to normalisation, in ratio `2 : 1`.  Feeding that vector into the
CHART assembly puts `7/40` on the first diagonal entry, not `1/6`. -/

/-- The design-side multipliers, in ratio `2 : 1`. -/
noncomputable def chartSplitSixDesignMultiplierWeight : Fin 12 → ℝ :=
  fun activeLabel => if (activeLabel : ℕ) < 4 then 1 / 8 else 1 / 16

/-- With the design-side multipliers the chart assembly has `7/40` at the first
atom: four triples contribute `(1/8)/4` and four more `(1/16)/5`. -/
theorem chartSplitSixDesignMultiplier_assembly_diagonal :
    chartMultiplierAssembly (Finset.univ : Finset (Fin 12)) chartSplitSixDesignMultiplierWeight
        chartSplitSixTightDir 0 0 = 7 / 40 := by
  have hnormalise : ∀ activeLabel : Fin 12,
      chartSplitSixDesignMultiplierWeight activeLabel
          • atomMatrix (chartSplitSixTightDir activeLabel)
        = (chartSplitSixDesignMultiplierWeight activeLabel / chartSplitSixNormSq activeLabel)
            • atomMatrix (chartSplitSixSupport activeLabel) := by
    intro activeLabel
    have hsquare : (Real.sqrt (chartSplitSixNormSq activeLabel)) ^ 2
        = chartSplitSixNormSq activeLabel :=
      Real.sq_sqrt (chartSplitSixNormSq_pos activeLabel).le
    rw [chartSplitSixTightDir, atomMatrix_smul, inv_pow, hsquare, smul_smul, div_eq_mul_inv]
  rw [chartMultiplierAssembly, Finset.sum_congr rfl fun activeLabel _ => hnormalise activeLabel]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
    Matrix.vecMulVec_apply, chartSplitSixSupport, chartSplitSixScale,
    chartSplitSixDesignMultiplierWeight, chartSplitSixNormSq]
  norm_num +decide [chartSplitSixSubset, Fin.sum_univ_succ]

/-- **THE DESIGN-SIDE MULTIPLIERS ARE NOT THE CHART ONES.**  At the very chart
point where `chartSplitSixProjection_isChartStationaryData` succeeds with `1/9` and
`5/72`, the design-side vector `1/8`, `1/16` fails the constant-diagonal condition
outright — `7/40` against the required `1/6`.

This is the `(6,3)` instance of the transport failure
`Gtz.Quantitative.ChartStationary`'s header records at `(7,3)`, and it is exact on
both sides rather than a residual: the chart system IS satisfiable here, but only
by a different multiplier vector.  A theorem obtained on the design side may
therefore not be carried across by renaming its multipliers. -/
theorem not_isChartStationaryData_of_designSideMultiplier :
    ¬ IsChartStationaryData 3 chartSplitSixProjection chartSplitSixWeight 0
      (Finset.univ : Finset (Fin 12)) chartSplitSixSubset chartSplitSixDesignMultiplierWeight
      chartSplitSixTightDir := by
  intro hdata
  have hdiagonal := hdata.assembly_diagonal 0
  rw [chartSplitSixDesignMultiplier_assembly_diagonal] at hdiagonal
  norm_num at hdiagonal

end Gtz
