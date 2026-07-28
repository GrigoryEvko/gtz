/-
# The TWO-BLOCK class at a NEGATIVE value — an emptiness certificate

A companion to `Gtz.Quantitative.ChartTwoBlock`, which owns the class.  That file
defines `Gtz.IsChartTwoBlockFamily` — every active subset of a chart stationarity
datum is either `chosenSubset` or its complement — and closes it UNDER A SIDE
CONDITION: with pairwise distinct weights inside each block the value is forced to
`(rank - 1)/size ≥ 0`, so no such datum is a counterexample
(`Gtz.zero_le_value_of_isChartTwoBlockFamily`).  It then states, in its own words,
that the complementary branch — a REPEATED weight inside a block — "is NOT treated
here, is not sorried, and must not be claimed", and it mechanizes a `(4,2)` witness
at `value = -1/size` to prove that branch inhabited
(`Gtz.not_forall_zero_le_value_of_isChartTwoBlockFamily`).

**READ THAT PARAGRAPH BEFORE READING THIS FILE AS NEW.**  The two-block class is
not opened here and is not first closed here.  What this file adds is one thing:
the EXACT CERTIFICATE that closes the negative-value half of the repeated-weight
branch, given an elimination step that stays outside Lean as a named hypothesis.

## What is proved here, unconditionally

`twoBlockEliminantCubic value = 108 value^3 - 108 value^2 + 9 value + 5` is the
generator of the elimination ideal of the two-block stationarity system in the
value variable [computed outside Lean; see the provenance section].  About it:

* `twoBlockEliminantCubic_eq_handelmanCombination` — **THE CERTIFICATE**, an exact
  identity over the rationals,

      `27 E(g) = 6844 (-g)^3 + 78960 (g + 3/20) (-g)^2`
                `+ 109200 (g + 3/20)^2 (-g) + 40000 (g + 3/20)^3` ,

  with all four Handelman coefficients strictly positive.  On `-3/20 ≤ g ≤ 0` both
  `-g` and `g + 3/20` are nonnegative, so every term is, and `E ≥ 0` follows with
  no case analysis (`twoBlockEliminantCubic_nonneg_of_mem_flooredWindow`).  This is
  a degree-three Handelman decomposition in the Bernstein basis of the interval,
  not an SOS decomposition and not a Positivstellensatz on the stationarity ideal —
  see the impossibility note below for the difference and why it matters.
* `handelmanMargin_le_twoBlockEliminantCubic` — the SHARP form, `E ≥ 1711/2000` on
  the same interval, from the square-root-free monotone reading: with `w = -g`,
  `E = 5 - 9w - 108w^2 - 108w^3` is strictly decreasing in `w ≥ 0`, so the minimum
  over `w ∈ [0, 3/20]` is `E(3/20) = 1711/2000`.  Hence
  `twoBlockEliminantCubic_ne_zero_of_flooredNegativeValue`: the system
  `{E(g) = 0, -3/20 ≤ g < 0}` has NO real solution.  That is the emptiness result.
* `twoBlockEliminantCubic_eq_zero_iff` — the root set is EXACTLY `{-1/6, 1/3, 5/6}`,
  from the factorisation `E = (6g+1)(3g-1)(6g-5)`, and
  `twoBlockEliminantCubic_eq_zero_iff_of_negativeValue` — on the whole negative
  axis the ONLY root is `-1/6`.

## Why the improved floor is load-bearing, stated as a theorem

`-1/6` is a root.  It is also `-1/size` at `size = 6`, i.e. exactly the endpoint of
the window that `Gtz.neg_inv_size_le_value_of_isChartStationaryData` supplies.  So
interval positivity on the SHIPPED window `[-1/6, 0]` is FALSE
(`not_forall_pos_twoBlockEliminantCubic_on_shippedWindow`), and the certificate
above needs the strictly better floor `-3/20`, which the unique negative root fails
(`not_flooredWindow_neg_inv_six`).  The improvement itself — the Cauchy–Binet floor
`value ≥ -(1/m)(1 - 1/C(m-1,k-1))`, which is `-3/20` at `(6,3)` — is NOT proved in
this file and is not this file's scope; it enters every statement below as the
numeric hypothesis `-(3/20) ≤ value` and nowhere else.

## An internal corroboration worth its six lines

`twoBlockEliminantCubic_eq_zero_iff_chartLandmark` says the three roots are exactly

    `-1/size` ,   `(rank - 1)/size` ,   `1 - 1/size`    at `size = 6, rank = 3`,

which are, in order, the shipped floor
(`Gtz.neg_inv_size_le_value_of_isChartStationaryData`), the shipped two-block value
(`Gtz.value_eq_rank_sub_one_div_size_of_isChartTwoBlockFamily`), and the shipped
dual ceiling at uniform weight (`Gtz.value_le_one_sub_weight_of_isChartStationaryData`).
Three independent theorems of this development each land on one root of a cubic
computed by an entirely separate elimination.  That is evidence the eliminant is
the right object; it is not a proof that it is, and it is not offered as one.

## What is ASSUMED, named so the hole is citable

`EliminatesChartTwoBlockValue` is a HYPOTHESIS, in the same sense and with the same
firewall as `Gtz.IsChartArgmaxValue` and `Gtz.ChartPointHasDesign`: it says that an
ADMISSIBLE two-block datum with both blocks occupied and a NEGATIVE value has
`E(value) = 0`.  It is asserted, outside Lean, only at `size = 6, rank = 3`; the
coefficients of `E` are `(6,3)` arithmetic (`sum tau = 1 + 6 value`, assembly
diagonal `1/6`) and nothing here claims otherwise.  It is not proved, not sorried,
and no theorem below is a statement about the conjecture without it.

Three antecedents of that hypothesis are load-bearing and none is decoration.

* ADMISSIBILITY.  Without `Gtz.IsChartArgmaxValue` the conclusion is false already
  at the smaller size where the branch first exists: the uniform `(4,2)` witness
  `Gtz.chartTwoBlockUniformProjection_isChartStationaryData` satisfies every field
  of the bundle and the two-block structure at `value = -1/4 = -1/size`, and
  `Gtz.not_forall_zero_le_value_of_isChartTwoBlockFamily` is exactly the statement
  that no argument from the bundle alone can exclude it.
* NEGATIVITY.  The elimination's trace step needs `value < 0`; the numerical census
  of this class finds converged roots at `value = 0` and `value = 1/2` as well, and
  neither is a root of `E`.  So `E(value) = 0` is FALSE as an unconditional
  statement about the class, and the antecedent is not removable.
* BOTH BLOCKS OCCUPIED.  `Gtz.IsChartTwoBlockFamily` permits `chosenSubset = ∅`;
  the nonemptiness of both blocks is what makes it a two-block PARTITION, and it is
  what `Gtz.size_eq_two_mul_rank_of_isChartTwoBlockFamily` needs.

## Provenance of the eliminant — numerics, quoted as numerics

None of this is inside Lean and none of it is a proof.

* GROEBNER: the elimination ideal of the gauge-fixed rank-one branch of the
  two-block system at `(6,3)` — 16 variables, 25 equations — is principal with
  generator `108 g^3 - 108 g^2 + 9 g + 5`, by msolve 0.10.1 over the rationals in
  2.27 s wall.  A companion run reported the ideal to be the unit ideal; that run
  is a KNOWN FALSE EMPTINESS — msolve silently truncates rational coefficients over
  a finite field, so `x - 1/6` parses as `x - 1`.  No emptiness report from that
  tool may be believed without first exhibiting a solution of the same input.
* MULTISTART: 4317 converged roots of the full residual for this class from 5400
  random starts, with the multiplier blocks Cholesky-parameterised so that all
  ranks are reachable.  Distinct values found: `-1/6, 0, 1/3, 1/2, 5/6`.  Number
  with value in `(-1/6, 0)`: ZERO.
* HAND ELIMINATION: the rank-one case of the argument gives, for the shared block
  multiplier `rho = value + 1/6` and the off-block coupling `kappa` with
  `kappa^2 = rho(1 - rho)`, that `rho ± kappa ∈ {0,1}`; the three solutions are
  `value ∈ {-1/6, 1/3, 5/6}`, matching the Groebner generator's root set exactly.

## The impossibility this file does NOT overcome

The certificate is univariate.  It closes a one-dimensional system that an
elimination has already produced, and it says nothing about the chart variables.
A Positivstellensatz on the STATIONARITY IDEAL itself, in the chart variables, is a
different object and is out of reach for a structural reason rather than a size
one: admissibility at a triple is `lambda_min(W[C]) ≤ value`, i.e. the DISJUNCTION
of three characteristic-coefficient sign conditions, so at `(6,3)` it is a
disjunction over `3^20` branches; and it cannot simply be dropped, because the
ideal carries genuine solutions at `value = -1/6` that admissibility and nothing
else rejects.  This is the chart-side companion of the leg-side obstruction the
repository already records as `Gtz.not_hasUniformTieAggregate_seven`.

## Inherited honesty

Everything below is conditional on `Gtz.IsChartStationaryData`, which is a
HYPOTHESIS: the variational derivation that would produce it is not formalized, the
system is NECESSARY only, and it is satisfied at admissible non-minima.  Read the
header of `Gtz.Quantitative.ChartStationary` before reading anything here as a
statement about the conjecture.  One class of the `(6,3)` covering census is one
class; the census has 2069 of them.
-/
import Mathlib
import Gtz.Quantitative.ChartTwoBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

variable {size : ℕ} {activeIndex : Type*}

/-! ## The eliminant of the two-block system -/

/-- **The two-block eliminant** `E(g) = 108 g^3 - 108 g^2 + 9 g + 5`.

The generator of the elimination ideal of the two-block chart stationarity system
in the value variable, at `size = 6, rank = 3`.  A DEFINITION of a cubic and
nothing more: that it IS that generator is recorded in the file header as outside
arithmetic, and is used below only through the named hypothesis
`EliminatesChartTwoBlockValue`. -/
def twoBlockEliminantCubic (value : ℝ) : ℝ :=
  108 * value ^ 3 - 108 * value ^ 2 + 9 * value + 5

/-- **The eliminant factors over the rationals**, with the three roots visible:
`E = (6g + 1)(3g - 1)(6g - 5)`. -/
theorem twoBlockEliminantCubic_eq_prod (value : ℝ) :
    twoBlockEliminantCubic value = (6 * value + 1) * (3 * value - 1) * (6 * value - 5) := by
  unfold twoBlockEliminantCubic
  ring

/-- **THE HANDELMAN CERTIFICATE** — an exact identity over the rationals,

    `27 E(g) = 6844 (-g)^3 + 78960 (g + 3/20)(-g)^2`
              `+ 109200 (g + 3/20)^2 (-g) + 40000 (g + 3/20)^3` ,

all four coefficients strictly positive.  This is the degree-three Handelman
decomposition of `E` in the Bernstein basis of `[-3/20, 0]`, whose two generators
are `-g ≥ 0` and `g + 3/20 ≥ 0`; the Bernstein coefficients are
`(1711/2000, 329/100, 91/20, 5)` and the factor `8000/27 = (20/3)^3` between them
and the integers above is the cube of the interval's reciprocal length.

Proved by ring normalisation, which is the whole point of a certificate: the
verification is an identity check and does not re-run the search that found it. -/
theorem twoBlockEliminantCubic_eq_handelmanCombination (value : ℝ) :
    27 * twoBlockEliminantCubic value
      = 6844 * (-value) ^ 3 + 78960 * (value + 3 / 20) * (-value) ^ 2
        + 109200 * (value + 3 / 20) ^ 2 * (-value) + 40000 * (value + 3 / 20) ^ 3 := by
  unfold twoBlockEliminantCubic
  ring

/-- **The eliminant is nonnegative on the floored window**, straight off the
Handelman certificate: on `-3/20 ≤ g ≤ 0` both generators are nonnegative, so all
four terms of the identity are, and no case analysis is needed anywhere.

The strict form is `twoBlockEliminantCubic_pos_of_mem_flooredWindow`, which needs
one more line and gets it from the sharp margin rather than from this identity. -/
theorem twoBlockEliminantCubic_nonneg_of_mem_flooredWindow (value : ℝ)
    (hfloor : -(3 / 20 : ℝ) ≤ value) (hceiling : value ≤ 0) :
    0 ≤ twoBlockEliminantCubic value := by
  have hdescending : (0 : ℝ) ≤ -value := by linarith
  have hascending : (0 : ℝ) ≤ value + 3 / 20 := by linarith
  have hcombination := twoBlockEliminantCubic_eq_handelmanCombination value
  have hcube : (0 : ℝ) ≤ (-value) ^ 3 := pow_nonneg hdescending 3
  have hmixedFirst : (0 : ℝ) ≤ (value + 3 / 20) * (-value) ^ 2 :=
    mul_nonneg hascending (pow_nonneg hdescending 2)
  have hmixedSecond : (0 : ℝ) ≤ (value + 3 / 20) ^ 2 * (-value) :=
    mul_nonneg (pow_nonneg hascending 2) hdescending
  have hcubeAscending : (0 : ℝ) ≤ (value + 3 / 20) ^ 3 := pow_nonneg hascending 3
  linarith

/-! ## The sharp margin, in the square-root-free monotone form -/

/-- **The margin identity**: `E(g) - 1711/2000 = (g + 3/20)(108 g^2 - (621/5) g + 2763/100)`.

The right factor has a nonnegative value wherever `g ≤ 0`, and the left one wherever
`g ≥ -3/20`, so the product is nonnegative on the window and `1711/2000` is a
LOWER BOUND rather than merely a value.  It is also attained, at `g = -3/20`, which
is why no better constant is available from this window. -/
theorem twoBlockEliminantCubic_sub_margin_eq_prod (value : ℝ) :
    twoBlockEliminantCubic value - 1711 / 2000
      = (value + 3 / 20) * (108 * value ^ 2 - (621 / 5) * value + 2763 / 100) := by
  unfold twoBlockEliminantCubic
  ring

/-- **THE SHARP MARGIN**: `1711/2000 ≤ E(g)` for `-3/20 ≤ g ≤ 0`.

Equivalently, with `w = -g ∈ [0, 3/20]`, `E = 5 - 9w - 108w^2 - 108w^3` is strictly
decreasing in `w ≥ 0`, so its minimum over the window is `E(3/20) = 1711/2000`.
The constant is EXACT and attained at the left endpoint of the window. -/
theorem handelmanMargin_le_twoBlockEliminantCubic (value : ℝ)
    (hfloor : -(3 / 20 : ℝ) ≤ value) (hceiling : value ≤ 0) :
    (1711 / 2000 : ℝ) ≤ twoBlockEliminantCubic value := by
  have hascending : (0 : ℝ) ≤ value + 3 / 20 := by linarith
  have hquadratic : (0 : ℝ) ≤ 108 * value ^ 2 - (621 / 5) * value + 2763 / 100 := by
    nlinarith [sq_nonneg value]
  have hmargin := twoBlockEliminantCubic_sub_margin_eq_prod value
  nlinarith [mul_nonneg hascending hquadratic]

/-- **The eliminant is strictly positive on the floored window.** -/
theorem twoBlockEliminantCubic_pos_of_mem_flooredWindow (value : ℝ)
    (hfloor : -(3 / 20 : ℝ) ≤ value) (hceiling : value ≤ 0) :
    0 < twoBlockEliminantCubic value := by
  have hmargin := handelmanMargin_le_twoBlockEliminantCubic value hfloor hceiling
  linarith

/-! ## The emptiness result -/

/-- **THE EMPTINESS CERTIFICATE.**  The one-variable system

    `E(value) = 0` ,   `-3/20 ≤ value` ,   `value < 0`

has NO real solution.  The certificate is the Handelman identity together with the
margin; nothing here is a search, and the verification is an identity check. -/
theorem twoBlockEliminantCubic_ne_zero_of_flooredNegativeValue (value : ℝ)
    (hfloor : -(3 / 20 : ℝ) ≤ value) (hnegative : value < 0) :
    twoBlockEliminantCubic value ≠ 0 := by
  have hpositive := twoBlockEliminantCubic_pos_of_mem_flooredWindow value hfloor hnegative.le
  exact ne_of_gt hpositive

/-- The emptiness result in existential form: the floored negative window contains
no root of the eliminant. -/
theorem not_exists_flooredNegativeValue_root_twoBlockEliminantCubic :
    ¬ ∃ value : ℝ, -(3 / 20 : ℝ) ≤ value ∧ value < 0 ∧ twoBlockEliminantCubic value = 0 := by
  rintro ⟨value, hfloor, hnegative, hroot⟩
  exact twoBlockEliminantCubic_ne_zero_of_flooredNegativeValue value hfloor hnegative hroot

/-! ## The root set, and why the improved floor is load-bearing -/

/-- **The root set is exactly `{-1/6, 1/3, 5/6}`**, read off the factorisation. -/
theorem twoBlockEliminantCubic_eq_zero_iff (value : ℝ) :
    twoBlockEliminantCubic value = 0 ↔ value = -(1 / 6) ∨ value = 1 / 3 ∨ value = 5 / 6 := by
  rw [twoBlockEliminantCubic_eq_prod]
  constructor
  · intro hroot
    rcases mul_eq_zero.mp hroot with hleadingPair | hlastFactor
    · rcases mul_eq_zero.mp hleadingPair with hfirstFactor | hsecondFactor
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  · rintro (hroot | hroot | hroot) <;> rw [hroot] <;> ring

/-- **On the negative axis the eliminant has exactly ONE root, `-1/6`.**  The other
two are positive, hence outside the target region of the exclusion programme: a
counterexample has no dominating subset, so its chart value is strictly negative,
and stationary data at `1/3` or `5/6` is not what has to be excluded. -/
theorem twoBlockEliminantCubic_eq_zero_iff_of_negativeValue (value : ℝ) (hnegative : value < 0) :
    twoBlockEliminantCubic value = 0 ↔ value = -(1 / 6) := by
  rw [twoBlockEliminantCubic_eq_zero_iff]
  constructor
  · rintro (hroot | hroot | hroot)
    · exact hroot
    · exact absurd (hroot ▸ hnegative) (by norm_num)
    · exact absurd (hroot ▸ hnegative) (by norm_num)
  · exact Or.inl

/-- **The three roots are three shipped chart landmarks** at `size = 6, rank = 3`:
the floor `-1/size` of `Gtz.neg_inv_size_le_value_of_isChartStationaryData`, the
two-block value `(rank - 1)/size` of
`Gtz.value_eq_rank_sub_one_div_size_of_isChartTwoBlockFamily`, and the dual ceiling
`1 - 1/size` of `Gtz.value_le_one_sub_weight_of_isChartStationaryData` at uniform
weight.

Three theorems of this development, each proved for its own reasons, each land on a
root of a cubic produced by an independent elimination.  Corroboration, not proof:
the eliminant is still assumed, and this theorem is arithmetic about the cubic. -/
theorem twoBlockEliminantCubic_eq_zero_iff_chartLandmark (value : ℝ) :
    twoBlockEliminantCubic value = 0 ↔
      value = -((6 : ℝ))⁻¹ ∨ value = ((3 : ℝ) - 1) / 6 ∨ value = 1 - ((6 : ℝ))⁻¹ := by
  rw [twoBlockEliminantCubic_eq_zero_iff]
  have hfloorLandmark : -((6 : ℝ))⁻¹ = -(1 / 6 : ℝ) := by norm_num
  have hvalueLandmark : ((3 : ℝ) - 1) / 6 = (1 / 3 : ℝ) := by norm_num
  have hceilingLandmark : (1 : ℝ) - ((6 : ℝ))⁻¹ = (5 / 6 : ℝ) := by norm_num
  rw [hfloorLandmark, hvalueLandmark, hceilingLandmark]

/-- **The unique negative root is NOT in the floored window.**  `-1/6 < -3/20`, so
the improvement of the floor from `-1/size` to `-(1/size)(1 - 1/C(m-1,k-1))` is
exactly what makes the certificate above possible, and is load-bearing rather than
cosmetic. -/
theorem not_flooredWindow_neg_inv_six : ¬ (-(3 / 20 : ℝ) ≤ -(1 / 6 : ℝ)) := by
  norm_num

/-- **INTERVAL POSITIVITY FAILS ON THE SHIPPED WINDOW.**  There is no certificate of
the shape above over `[-1/size, 0]` at `size = 6`, for the plain reason that the
eliminant VANISHES at the endpoint.  So `Gtz.neg_inv_size_le_value_of_isChartStationaryData`
does not suffice to close this branch, and neither does its strict form
`Gtz.neg_inv_size_lt_value_of_isChartStationaryData`, which removes the endpoint but
leaves every interior point of `(-1/6, 0)` to be excluded by something. -/
theorem not_forall_pos_twoBlockEliminantCubic_on_shippedWindow :
    ¬ ∀ value : ℝ, -(1 / 6 : ℝ) ≤ value → value ≤ 0 → 0 < twoBlockEliminantCubic value := by
  intro hpositivity
  have hendpoint := hpositivity (-(1 / 6 : ℝ)) le_rfl (by norm_num)
  rw [twoBlockEliminantCubic_eq_prod] at hendpoint
  norm_num at hendpoint

/-! ## Where the increment over the shipped two-block closure lives -/

variable {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
  {value : ℝ} {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
  {chosenSubset : Finset (Fin size)}

/-- **A NEGATIVE-VALUE TWO-BLOCK DATUM HAS A REPEATED WEIGHT INSIDE A BLOCK.**

The contrapositive of the shipped closure `Gtz.zero_le_value_of_isChartTwoBlockFamily`,
and the statement that locates precisely what this file adds: the distinct-weight
half of the class is already closed, so the certificate below is needed only on the
repeated-weight half, which `Gtz.Quantitative.ChartTwoBlock` declares out of scope
and proves inhabited. -/
theorem not_hasDistinctWeightsOn_both_of_negativeValue_of_isChartTwoBlockFamily
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hnegative : value < 0) :
    ¬ (HasDistinctWeightsOn weight chosenSubset ∧ HasDistinctWeightsOn weight chosenSubsetᶜ) := by
  rintro ⟨hdistinct, hdistinctCompl⟩
  exact absurd (zero_le_value_of_isChartTwoBlockFamily hdata hfamily hdistinct hdistinctCompl)
    (not_le.mpr hnegative)

/-! ## The elimination step, as a named hypothesis, and the exclusion it buys -/

/-- **THE ELIMINATION STEP, AS A HYPOTHESIS** — that an ADMISSIBLE two-block datum
with both blocks occupied and a NEGATIVE value satisfies `E(value) = 0`.

Named and defined separately rather than baked into a theorem, exactly as
`Gtz.IsChartArgmaxValue` is, so that the hole is citable.  It is NOT proved here.
Outside Lean it is asserted only at `size = 6, rank = 3`, where the block traces,
the assembly diagonal `1/6` and the mass identity `sum tau = 1 + 6 value` that
produce the coefficients of `E` are available; the argument runs through the block
diagonality of the assembly, the commutation `[N_i, Theta_i] = 0`, a trace bound
that forces the two multiplier ranks to sum to at most three when the value is
negative, and a two-case analysis on those ranks.  Every antecedent beyond the
bundle itself is load-bearing — admissibility, negativity, and both blocks
occupied; the file header names the witness or the census that forces each.

Instantiating this at any other size is possible and meaningless: nothing supplies
it there, and a hypothesis nobody can discharge proves nothing. -/
def EliminatesChartTwoBlockValue (rank : ℕ) : Prop :=
  ∀ (projection : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ) (value : ℝ)
    (activeSet : Finset activeIndex) (activeSubset : activeIndex → Finset (Fin size))
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    (chosenSubset : Finset (Fin size)),
    IsChartStationaryData rank projection weight value activeSet activeSubset activeWeight
        tightDir →
      IsChartArgmaxValue rank projection weight value →
        IsChartTwoBlockFamily activeSet activeSubset chosenSubset →
          chosenSubset.Nonempty → chosenSubsetᶜ.Nonempty → value < 0 →
            twoBlockEliminantCubic value = 0

/-- **THE CLOSURE OF THE NEGATIVE-VALUE BRANCH, given the elimination step.**  An
admissible two-block datum with both blocks occupied whose value is at or above the
Cauchy–Binet floor `-3/20` has a NONNEGATIVE value — with no distinctness side
condition, which is the whole of the increment over
`Gtz.zero_le_value_of_isChartTwoBlockFamily`.

Read the hypotheses honestly.  Three of them are supplied elsewhere and one is not
supplied at all: the datum and the two-block structure are the shipped bundle,
admissibility is the shipped `Gtz.IsChartArgmaxValue`, the floor `-3/20` is the
Cauchy–Binet floor at `(6,3)` and is a numeral here, and `EliminatesChartTwoBlockValue`
is an assumption this development does not discharge. -/
theorem zero_le_value_of_isChartTwoBlockFamily_of_eliminates
    (heliminates : EliminatesChartTwoBlockValue (size := size) (activeIndex := activeIndex) rank)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hnonempty : chosenSubset.Nonempty) (hnonemptyCompl : chosenSubsetᶜ.Nonempty)
    (hfloor : -(3 / 20 : ℝ) ≤ value) :
    0 ≤ value := by
  by_contra hnegative
  rw [not_le] at hnegative
  exact twoBlockEliminantCubic_ne_zero_of_flooredNegativeValue value hfloor hnegative
    (heliminates projection weight value activeSet activeSubset activeWeight tightDir
      chosenSubset hdata hargmax hfamily hnonempty hnonemptyCompl hnegative)

/-- **THE EMPTINESS OF THE CLASS ON THE FLOORED NEGATIVE WINDOW.**  Given the
elimination step, there is NO admissible chart stationarity datum whose active
family is two occupied complementary blocks and whose value lies in `[-3/20, 0)`.

This is the exclusion the certificate buys, stated as a non-existence.  It covers
exactly one class of the `(6,3)` covering census — the class of two complementary
triples, the one the paper's third-symmetric-function corollary sets aside — and
says nothing whatever about the other 2068. -/
theorem not_isChartStationaryData_of_isChartTwoBlockFamily_of_flooredNegativeValue
    (heliminates : EliminatesChartTwoBlockValue (size := size) (activeIndex := activeIndex) rank)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hnonempty : chosenSubset.Nonempty) (hnonemptyCompl : chosenSubsetᶜ.Nonempty)
    (hfloor : -(3 / 20 : ℝ) ≤ value) (hnegative : value < 0) :
    ¬ IsChartStationaryData rank projection weight value activeSet activeSubset activeWeight
        tightDir := by
  intro hdata
  exact absurd
    (zero_le_value_of_isChartTwoBlockFamily_of_eliminates heliminates hdata hargmax hfamily
      hnonempty hnonemptyCompl hfloor)
    (not_le.mpr hnegative)

end Gtz
