/-
# The subset-determinant laws: the Cauchy–Binet cap, and the determinant–trace floor

Two independent things live here, and the first is mostly a completion rather than a
construction.

## C2 was already shipped, and this file says exactly what it adds

`Gtz.Quantitative.VolumeAverageLaw` already carries the elementary-symmetric bound in
full: `Gtz.weightElementary` (the definition `e_level(t) = ∑_{|C| = level} ∏_{c ∈ C} t_c`),
`Gtz.weightElementary_pos`, `Gtz.exists_detSubsetSum_ge_inv_weightElementary` (the bound
`det S_C ≥ 1/e_rank(t)`), `Gtz.weightElementary_of_uniformWeight`,
`Gtz.exists_detSubsetSum_ge_pow_div_choose` (the uniform-weight form
`det S_C ≥ size^rank / C(size,rank)`), the degenerate-case pair
`Gtz.sum_shadowDeterminant_div_detSubsetSum_eq_independentWeightProduct` /
`Gtz.sum_independentWeightProduct_lt_weightElementary_of_dependentSubset`, and the
tetrahedron sharpness triple `Gtz.tetraDesign_detSubsetSum_eq`,
`Gtz.tetraDesign_weightElementary_three`,
`Gtz.tetraDesign_detSubsetSum_eq_inv_weightElementary`.  None of that is restated below,
and re-proving any of it would be a defect.

What this file adds to that block is four things and no more.

1.  **The division-free primitive.**  `one_le_capValue_mul_weightElementary` says: if
    every `rank`-subset determinant is at most `cap`, then `1 ≤ cap · e_rank(t)`.  This
    is the Cauchy–Binet inequality before any division and before any maximum — the
    shipped statement is its division form, obtained by supplying the argmax as the cap
    and dividing by `e_rank(t) > 0`.  Stated against an arbitrary cap it needs neither
    `e_rank(t) > 0` nor a nonempty family, and it is the form other files can sum
    against.  `exists_one_le_detSubsetSum_mul_weightElementary` is the shipped
    existential cleared of its inverse, for the comparison below.
2.  **The supersession, measured.**  The shipped docstring asserts that the bound
    supersedes `Gtz.exists_shadowDeterminant_ge_inv_binomial`, and it justifies that by
    `1/e_rank(t) ≥ size^rank/C(size,rank)` — which is Maclaurin's inequality, not
    available here (see 4).  `exists_inv_choose_le_weightElementary_mul_detSubsetSum`
    measures the same gap with no Maclaurin at all: the binomial pigeonhole yields
    `1/C(size,rank) ≤ e_rank(t) · det S_C` on exactly the scale where the Cauchy–Binet
    bound yields `1`, so the improvement is the factor `C(size,rank)`, uniformly and
    unconditionally.
3.  **The numerals at the cells.**  `16` at `(4,3)`, `54/5` at `(6,3)`, `49/5` at
    `(7,3)`, as theorems rather than as quoted arithmetic.  These need NO Maclaurin
    inequality: at uniform weights `e_rank(t) = C(size,rank)·size^{-rank}` is an exact
    evaluation (`Gtz.weightElementary_of_uniformWeight`), so the uniform instantiation
    is an equality substituted into the shipped bound.
4.  **The weight-free form, with its missing ingredient named.**
    `exists_detSubsetSum_ge_pow_div_choose_of_maclaurin` derives
    `det S_C ≥ size^rank/C(size,rank)` for arbitrary weights from the EXPLICIT hypothesis
    `e_rank(t) ≤ C(size,rank)·size^{-rank}`.  That hypothesis is Maclaurin's inequality,
    which Mathlib does not have (it has Newton's identities and nothing above them), and
    it is not proved here.  The corollary is therefore conditional and says so.

## C4: the determinant–trace floor on the eigenvalues, and its ceiling

For a positive semidefinite `A` of size `dim`, AM–GM on the eigenvalues other than a
chosen one gives, for EVERY eigenvalue index,

    `(dim − 1)^(dim − 1) · det A  ≤  λ_j(A) · (tr A)^(dim − 1)` ,

`pow_pred_mul_det_le_eigenvalue_mul_trace_pow`, unconditional and with no case split on
the dimension: at `dim ≤ 1` the empty product makes it an identity.  Solved for the
eigenvalue it is `detTraceFloor`, and `posSemidef_sub_detTraceFloor_smul_one` puts it in
the Loewner form the rest of the repository speaks.  The AM–GM step is
`prod_le_pow_sum_div_card` / `pow_card_mul_prod_le_pow_sum`, proved here in the
natural-power form because Mathlib carries only the real-exponent weighted version
`Real.geom_mean_le_arith_mean_weighted`.

**This is matrix analysis, and it is NOT offered as progress toward GTZ.**  The ceiling
is a theorem of this file.  At rank three the pair `(det, tr) = (27/2, 9)` is realised by
positive semidefinite matrices on both sides of the domination threshold —
`dominatingFibreForm` with spectrum `(6, 3/2, 3/2)` dominates, `slackFibreForm` with
spectrum `(3 − 3√2/2, 3, 3 + 3√2/2)` does not — so
`detTraceFloorFunction_le_slackFibreLeast` bounds EVERY function of the pair by
`3 − 3√2/2 < 1` there, and `detTraceFloorFunction_lt_one` reads that off: no floor
computed from the determinant and the trace alone can certify domination at rank three.
Those two spectra are exactly the two realised by the sixteen independent triples of the
`D₃` root design `Gtz.rootKillDesign` — twelve at `3 − 3√2/2`, four at `3/2`, all on the
one fibre — which is where the obstruction was found; the theorems below assert only the
fibre statement, since identifying the witnesses with those triples is a separate
computation this file does not perform.  `detTraceFloor_rankThreeFibre` evaluates the
floor there to `2/3`, strictly below the ceiling, so C4 is not even sharp for its own
method on that fibre.

## The C6 companion: the matrix average, and the derandomisation gap

Concavity of the least eigenvalue in the below-spectrum vocabulary is already shipped as
`Gtz.posSemidef_expectedSubsetSum_sub_volumeSamplingAverage_smul_one`, and it is not
restated.  Two things are added.

* `posSemidef_expectedSubsetSum_sub_one` — `E_π[S_C] ⪰ 1` for every weighted design,
  UNCONDITIONALLY.  The shipped `Gtz.posSemidef_leverageWeightedAtomSum_sub_one` is about
  the leverage-weighted atom sum; identifying that with the volume-sampling expectation
  needs the one-point marginal, which was an undischarged `Prop` until
  `Gtz.isProjectionOnePointMarginal` landed.  This is that identification spent.
* `exists_family_flooring_average_without_flooring_member` — the gap, in the kernel: a
  two-member positive semidefinite family whose uniform average is exactly the identity
  while NO member admits any positive Loewner floor.  So a floor on the average is not a
  floor on any member, which is the whole content of the volume-average law's refutation
  (`Gtz.Quantitative.VolumeAverageLaw`, refuted there at an exact rational `(3,2)`
  design) in a form that does not depend on that design.

`E_π[tr S_C] ≥ rank²` is `Gtz.sq_rank_le_expectedElementary_one`, shipped and
unconditional; it is not restated.

## What is NOT claimed

* No cell is closed and no covering class is excluded.  Every determinant bound here
  bounds `λ_min` from ABOVE, never below, and the fibre ceiling says the trace does not
  repair that.
* Maclaurin's inequality is assumed where it is used, never proved.
* The witnesses of the fibre section are diagonal representatives of the two spectra, not
  the `D₃` triples themselves.
-/
import Mathlib
import Gtz.Quantitative.ProjectionOnePointMarginal
import Gtz.Quantitative.VolumeAverageLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## C2's division-free primitive, and the supersession measured

The Cauchy–Binet identity `∑_{|C| = rank} det P_C = 1` and the factorisation
`det P_C = (∏_{c ∈ C} t_c)·det S_C` are both shipped; everything in this section is a sum
over them. -/

section CauchyBinetCap

variable {size rank : ℕ}

/-- **THE DIVISION-FREE CAP.**  A uniform upper bound on the subset determinants forces
`1 ≤ cap · e_rank(t)`.  Stated against an arbitrary cap, so no maximum is needed as a
gadget, no positivity of `e_rank(t)` is used, and the degenerate family is not a special
case.

This is `Gtz.exists_detSubsetSum_ge_inv_weightElementary` before the division: the shipped
statement supplies the argmax as the cap and then divides by `e_rank(t) > 0`.  Nothing
here re-proves it. -/
theorem one_le_capValue_mul_weightElementary (design : WeightedDesign size rank)
    {capValue : ℝ}
    (hcap : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      (subsetSum design selected).det ≤ capValue) :
    1 ≤ capValue * weightElementary design rank := by
  have hterm : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      shadowDeterminant design selected
        ≤ (∏ atomIndex ∈ selected, design.weight atomIndex) * capValue := by
    intro selected hmem
    rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum design
      (Finset.mem_powersetCard.mp hmem).2]
    exact mul_le_mul_of_nonneg_left (hcap selected hmem)
      (subsetWeightProduct_pos design selected).le
  have hsummed := Finset.sum_le_sum hterm
  rw [sum_shadowDeterminant_eq_one design, ← Finset.sum_mul, ← weightElementary,
    mul_comm] at hsummed
  exact hsummed

/-- **The shipped bound, cleared of its inverse.**  Some `rank`-subset satisfies
`1 ≤ det S_C · e_rank(t)`.  Multiplying `Gtz.exists_detSubsetSum_ge_inv_weightElementary`
by `e_rank(t) > 0`; recorded because the comparison below needs both bounds on one
scale. -/
theorem exists_one_le_detSubsetSum_mul_weightElementary (design : WeightedDesign size rank) :
    ∃ selected : Finset (Fin size), selected.card = rank ∧
      1 ≤ (subsetSum design selected).det * weightElementary design rank := by
  obtain ⟨best, hcard, hbound⟩ := exists_detSubsetSum_ge_inv_weightElementary design
  refine ⟨best, hcard, ?_⟩
  have hpositive := weightElementary_pos design
  have hscaled := mul_le_mul_of_nonneg_right hbound hpositive.le
  rwa [inv_mul_cancel₀ hpositive.ne'] at hscaled

/-- **THE SUPERSESSION, MEASURED.**  On the same scale `e_rank(t)·det S_C` the binomial
pigeonhole `Gtz.exists_shadowDeterminant_ge_inv_binomial` delivers only
`1/C(size,rank)`, where `exists_one_le_detSubsetSum_mul_weightElementary` delivers `1`.
The improvement is therefore the factor `C(size,rank)` exactly — `20` at `(6,3)`, `35` at
`(7,3)` — and the comparison uses no AM–GM and no Maclaurin inequality, only that a
weight product over one `rank`-subset is one term of the nonnegative sum `e_rank(t)` and
that a subset atom sum has nonnegative determinant. -/
theorem exists_inv_choose_le_weightElementary_mul_detSubsetSum
    (design : WeightedDesign size rank) :
    ∃ selected : Finset (Fin size), selected.card = rank ∧
      (((size.choose rank : ℕ)) : ℝ)⁻¹
        ≤ weightElementary design rank * (subsetSum design selected).det := by
  obtain ⟨best, hcard, hbound⟩ := exists_shadowDeterminant_ge_inv_binomial design
  refine ⟨best, hcard, le_trans hbound ?_⟩
  rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum design hcard, weightElementary]
  refine mul_le_mul_of_nonneg_right ?_ (posSemidef_subsetSum design best).det_nonneg
  exact Finset.single_le_sum
    (f := fun selected => ∏ atomIndex ∈ selected, design.weight atomIndex)
    (fun selected _ => (subsetWeightProduct_pos design selected).le)
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ best, hcard⟩)

end CauchyBinetCap

/-! ## The weight-free form, and the ingredient it is missing

`Gtz.exists_detSubsetSum_ge_pow_div_choose` reaches `size^rank/C(size,rank)` at UNIFORM
weights, by exact evaluation of `e_rank(t)`.  Reaching the same constant at arbitrary
weights needs `e_rank(t) ≤ C(size,rank)·size^{-rank}`, which is Maclaurin's inequality:
the elementary symmetric functions of a probability vector are maximised at the
barycentre.  Mathlib does not carry it, so it is a hypothesis below and nothing else in
this file depends on the corollary. -/

section Maclaurin

variable {size rank : ℕ}

/-- **The weight-free bound, CONDITIONAL on Maclaurin's inequality.**  Given
`e_rank(t) ≤ C(size,rank)·size^{-rank}` — which is Maclaurin at the top level, ASSUMED —
some `rank`-subset has `det S_C ≥ size^rank/C(size,rank)` at arbitrary weights.  The
hypothesis is an equality at uniform weights, where
`Gtz.exists_detSubsetSum_ge_pow_div_choose` gives the conclusion outright and this
corollary is not needed. -/
theorem exists_detSubsetSum_ge_pow_div_choose_of_maclaurin (design : WeightedDesign size rank)
    (hmaclaurin : weightElementary design rank
      ≤ ((size.choose rank : ℕ) : ℝ) * ((size : ℝ)⁻¹) ^ rank) :
    ∃ selected : Finset (Fin size), selected.card = rank ∧
      (size : ℝ) ^ rank / ((size.choose rank : ℕ) : ℝ) ≤ (subsetSum design selected).det := by
  obtain ⟨best, hcard, hbound⟩ := exists_detSubsetSum_ge_inv_weightElementary design
  refine ⟨best, hcard, le_trans ?_ hbound⟩
  have hinvMono := inv_anti₀ (weightElementary_pos design) hmaclaurin
  rw [inv_pow, mul_inv, inv_inv] at hinvMono
  rw [div_eq_mul_inv, mul_comm]
  exact hinvMono

end Maclaurin

/-! ## The uniform-weight numerals at the cells

Maclaurin plays no part here: at uniform weights `e_rank(t) = C(size,rank)·size^{-rank}`
is an exact evaluation, so each of these is the shipped uniform bound with its constant
computed. -/

/-- **`16` at `(4,3)`**, attained by the regular tetrahedron: every triple there has
determinant exactly `16` (`Gtz.tetraDesign_detSubsetSum_eq`), so this instance of the
bound has zero slack. -/
theorem exists_detSubsetSum_ge_sixteen_of_uniformWeight (design : WeightedDesign 4 3)
    (huniform : ∀ atomIndex : Fin 4, design.weight atomIndex = 1 / 4) :
    ∃ selected : Finset (Fin 4), selected.card = 3 ∧ 16 ≤ (subsetSum design selected).det := by
  obtain ⟨best, hcard, hbound⟩ := exists_detSubsetSum_ge_pow_div_choose design
    fun atomIndex => by rw [huniform atomIndex]; norm_num
  refine ⟨best, hcard, le_trans (le_of_eq ?_) hbound⟩
  have hchoose : Nat.choose 4 3 = 4 := by decide
  rw [hchoose]
  norm_num

/-- **`54/5` at `(6,3)`**, one of the two open cells. -/
theorem exists_detSubsetSum_ge_fiftyFour_div_five_of_uniformWeight (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = 1 / 6) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      54 / 5 ≤ (subsetSum design selected).det := by
  obtain ⟨best, hcard, hbound⟩ := exists_detSubsetSum_ge_pow_div_choose design
    fun atomIndex => by rw [huniform atomIndex]; norm_num
  refine ⟨best, hcard, le_trans (le_of_eq ?_) hbound⟩
  have hchoose : Nat.choose 6 3 = 20 := by decide
  rw [hchoose]
  norm_num

/-- **`49/5` at `(7,3)`**, the other open cell. -/
theorem exists_detSubsetSum_ge_fortyNine_div_five_of_uniformWeight (design : WeightedDesign 7 3)
    (huniform : ∀ atomIndex : Fin 7, design.weight atomIndex = 1 / 7) :
    ∃ selected : Finset (Fin 7), selected.card = 3 ∧
      49 / 5 ≤ (subsetSum design selected).det := by
  obtain ⟨best, hcard, hbound⟩ := exists_detSubsetSum_ge_pow_div_choose design
    fun atomIndex => by rw [huniform atomIndex]; norm_num
  refine ⟨best, hcard, le_trans (le_of_eq ?_) hbound⟩
  have hchoose : Nat.choose 7 3 = 35 := by decide
  rw [hchoose]
  norm_num

/-! ## AM–GM in natural-power form

Mathlib carries the weighted real-exponent AM–GM `Real.geom_mean_le_arith_mean_weighted`
and no natural-power version over a `Finset`.  Both statements below hold on the empty
family, where each side is `1`, so C4 needs no case split on the dimension. -/

section ArithmeticGeometricMean

variable {index : Type*}

/-- **AM–GM, natural-power form.**  A product of nonnegatives is at most the
`card`-th power of their mean.  The real-exponent weighted inequality at the uniform
weight `1/card`, raised to the `card`-th power. -/
theorem prod_le_pow_sum_div_card (support : Finset index) (value : index → ℝ)
    (hnonneg : ∀ element ∈ support, 0 ≤ value element) :
    ∏ element ∈ support, value element
      ≤ ((∑ element ∈ support, value element) / (support.card : ℝ)) ^ support.card := by
  classical
  rcases Finset.eq_empty_or_nonempty support with rfl | hnonempty
  · simp
  · have hcardPos : (0 : ℝ) < (support.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hnonempty
    have hweightSum : ∑ _element ∈ support, ((support.card : ℝ))⁻¹ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcardPos.ne']
    have hgeom := Real.geom_mean_le_arith_mean_weighted support
      (fun _ => ((support.card : ℝ))⁻¹) value (fun _ _ => (inv_pos.mpr hcardPos).le)
      hweightSum hnonneg
    have hmean : ∑ element ∈ support, ((support.card : ℝ))⁻¹ * value element
        = (∑ element ∈ support, value element) / (support.card : ℝ) := by
      rw [← Finset.mul_sum, div_eq_inv_mul]
    have hrootsNonneg : 0 ≤ ∏ element ∈ support, (value element) ^ (((support.card : ℝ))⁻¹) :=
      Finset.prod_nonneg fun element hmem => Real.rpow_nonneg (hnonneg element hmem) _
    have hraised := pow_le_pow_left₀ hrootsNonneg (hmean ▸ hgeom) support.card
    refine le_trans (le_of_eq ?_) hraised
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun element hmem => ?_
    rw [← Real.rpow_natCast ((value element) ^ (((support.card : ℝ))⁻¹)) support.card,
      ← Real.rpow_mul (hnonneg element hmem), inv_mul_cancel₀ hcardPos.ne', Real.rpow_one]

/-- **AM–GM cleared of division**, which is the form C4 consumes: no hypothesis on the
family and no division anywhere. -/
theorem pow_card_mul_prod_le_pow_sum (support : Finset index) (value : index → ℝ)
    (hnonneg : ∀ element ∈ support, 0 ≤ value element) :
    ((support.card : ℝ)) ^ support.card * ∏ element ∈ support, value element
      ≤ (∑ element ∈ support, value element) ^ support.card := by
  classical
  rcases Finset.eq_empty_or_nonempty support with rfl | hnonempty
  · simp
  · have hcardPos : (0 : ℝ) < (support.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hnonempty
    have hscaled := mul_le_mul_of_nonneg_left (prod_le_pow_sum_div_card support value hnonneg)
      (pow_nonneg hcardPos.le support.card)
    have hcancel : ((support.card : ℝ)) ^ support.card
        * (((∑ element ∈ support, value element) / (support.card : ℝ)) ^ support.card)
        = (∑ element ∈ support, value element) ^ support.card := by
      rw [div_pow]
      field_simp
    rwa [hcancel] at hscaled

end ArithmeticGeometricMean

/-! ## C4: the determinant–trace floor on the eigenvalues

Pure matrix analysis, stated at every dimension and for every eigenvalue index.  It is
NOT a step toward GTZ: it bounds a least eigenvalue by a function of the determinant and
the trace, and the fibre section below shows that no such function reaches the domination
threshold at rank three. -/

section DeterminantTrace

variable {dim : ℕ}

/-- **C4 BEFORE DIVISION.**  For a positive semidefinite form and EVERY eigenvalue index,

    `(dim − 1)^(dim − 1) · det A ≤ λ_j(A) · (tr A)^(dim − 1)` .

The determinant is `λ_j` times the product of the others, AM–GM caps that product by the
`(dim−1)`-th power of their mean, and the others sum to at most the trace because `λ_j` is
nonnegative.  At `dim ≤ 1` the erased family is empty and both sides agree, so no case
split on the dimension appears. -/
theorem pow_pred_mul_det_le_eigenvalue_mul_trace_pow {form : Matrix (Fin dim) (Fin dim) ℝ}
    (hpsd : form.PosSemidef) (eigenIndex : Fin dim) :
    (((dim - 1 : ℕ)) : ℝ) ^ (dim - 1) * form.det
      ≤ hpsd.1.eigenvalues eigenIndex * Matrix.trace form ^ (dim - 1) := by
  classical
  have hnonneg : ∀ index : Fin dim, 0 ≤ hpsd.1.eigenvalues index := hpsd.eigenvalues_nonneg
  have hdet : form.det = ∏ index : Fin dim, hpsd.1.eigenvalues index := by
    simpa using hpsd.1.det_eq_prod_eigenvalues
  have htrace : Matrix.trace form = ∑ index : Fin dim, hpsd.1.eigenvalues index := by
    simpa using hpsd.1.trace_eq_sum_eigenvalues
  have hrestCard : ((Finset.univ : Finset (Fin dim)).erase eigenIndex).card = dim - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ eigenIndex), Finset.card_univ, Fintype.card_fin]
  have hsplitProd : form.det
      = hpsd.1.eigenvalues eigenIndex
        * ∏ index ∈ (Finset.univ : Finset (Fin dim)).erase eigenIndex,
            hpsd.1.eigenvalues index := by
    rw [hdet, Finset.mul_prod_erase _ _ (Finset.mem_univ eigenIndex)]
  have hsplitSum : Matrix.trace form
      = (∑ index ∈ (Finset.univ : Finset (Fin dim)).erase eigenIndex, hpsd.1.eigenvalues index)
        + hpsd.1.eigenvalues eigenIndex := by
    rw [htrace, Finset.sum_erase_add _ _ (Finset.mem_univ eigenIndex)]
  have hrestSumNonneg :
      0 ≤ ∑ index ∈ (Finset.univ : Finset (Fin dim)).erase eigenIndex, hpsd.1.eigenvalues index :=
    Finset.sum_nonneg fun index _ => hnonneg index
  have hrestSumLe :
      (∑ index ∈ (Finset.univ : Finset (Fin dim)).erase eigenIndex, hpsd.1.eigenvalues index)
        ≤ Matrix.trace form := by
    rw [hsplitSum]
    linarith [hnonneg eigenIndex]
  have hmeanBound := pow_card_mul_prod_le_pow_sum
    ((Finset.univ : Finset (Fin dim)).erase eigenIndex)
    (fun index => hpsd.1.eigenvalues index) fun index _ => hnonneg index
  rw [hrestCard] at hmeanBound
  have hraised : (∑ index ∈ (Finset.univ : Finset (Fin dim)).erase eigenIndex,
        hpsd.1.eigenvalues index) ^ (dim - 1)
      ≤ Matrix.trace form ^ (dim - 1) :=
    pow_le_pow_left₀ hrestSumNonneg hrestSumLe (dim - 1)
  have hchain : ((dim - 1 : ℕ) : ℝ) ^ (dim - 1)
      * ∏ index ∈ (Finset.univ : Finset (Fin dim)).erase eigenIndex, hpsd.1.eigenvalues index
      ≤ Matrix.trace form ^ (dim - 1) := le_trans hmeanBound hraised
  have hscaled := mul_le_mul_of_nonneg_left hchain (hnonneg eigenIndex)
  rw [hsplitProd]
  nlinarith [hscaled]

/-- **THE DETERMINANT–TRACE FLOOR** `(dim − 1)^(dim − 1)·det / tr^(dim − 1)`, as a
function of the two scalars alone.  That it IS a floor on every eigenvalue is
`detTraceFloor_le_eigenvalue_of_posSemidef`. -/
noncomputable def detTraceFloor (dim : ℕ) (determinant traceValue : ℝ) : ℝ :=
  (((dim - 1 : ℕ)) : ℝ) ^ (dim - 1) * determinant / traceValue ^ (dim - 1)

/-- **C4.**  The determinant–trace floor lies below every eigenvalue of a positive
semidefinite form, with no hypothesis on the trace.  The trace of such a form is
nonnegative, and at trace zero every eigenvalue and the determinant vanish together, so
the floor is `0` there and the statement survives Lean's `x/0 = 0`. -/
theorem detTraceFloor_le_eigenvalue_of_posSemidef {form : Matrix (Fin dim) (Fin dim) ℝ}
    (hpsd : form.PosSemidef) (eigenIndex : Fin dim) :
    detTraceFloor dim form.det (Matrix.trace form) ≤ hpsd.1.eigenvalues eigenIndex := by
  classical
  have hnonneg : ∀ index : Fin dim, 0 ≤ hpsd.1.eigenvalues index := hpsd.eigenvalues_nonneg
  have htrace : Matrix.trace form = ∑ index : Fin dim, hpsd.1.eigenvalues index := by
    simpa using hpsd.1.trace_eq_sum_eigenvalues
  have htraceNonneg : 0 ≤ Matrix.trace form := by
    rw [htrace]
    exact Finset.sum_nonneg fun index _ => hnonneg index
  rcases eq_or_lt_of_le htraceNonneg with htraceZero | htracePos
  · have hallZero : ∀ index ∈ (Finset.univ : Finset (Fin dim)),
        hpsd.1.eigenvalues index = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun index _ => hnonneg index).mp ?_
      rw [← htrace, ← htraceZero]
    have hchosenZero : hpsd.1.eigenvalues eigenIndex = 0 :=
      hallZero eigenIndex (Finset.mem_univ _)
    have hdetZero : form.det = 0 := by
      have hdet : form.det = ∏ index : Fin dim, hpsd.1.eigenvalues index := by
        simpa using hpsd.1.det_eq_prod_eigenvalues
      rw [hdet]
      exact Finset.prod_eq_zero (Finset.mem_univ eigenIndex) hchosenZero
    rw [detTraceFloor, hdetZero, mul_zero, zero_div, hchosenZero]
  · rw [detTraceFloor, div_le_iff₀ (pow_pos htracePos (dim - 1))]
    exact pow_pred_mul_det_le_eigenvalue_mul_trace_pow hpsd eigenIndex

/-- **C4 in Loewner form**, which is how the rest of the repository states floors:
`A ⪰ (detTraceFloor)·1` for every positive semidefinite `A`. -/
theorem posSemidef_sub_detTraceFloor_smul_one {form : Matrix (Fin dim) (Fin dim) ℝ}
    (hpsd : form.PosSemidef) :
    (form - detTraceFloor dim form.det (Matrix.trace form)
      • (1 : Matrix (Fin dim) (Fin dim) ℝ)).PosSemidef :=
  posSemidef_sub_smul_one_of_eigenvalue_ge hpsd.1 _
    fun eigenIndex => detTraceFloor_le_eigenvalue_of_posSemidef hpsd eigenIndex

end DeterminantTrace

/-! ## The ceiling: the `(det, tr)` fibre at rank three does not decide domination

The `(det, tr) = (27/2, 9)` fibre in dimension three carries positive semidefinite
matrices on both sides of the domination threshold.  The two spectra below, `(6, 3/2, 3/2)`
and `(3 − 3√2/2, 3, 3 + 3√2/2)`, are exactly the two realised by the sixteen independent
triples of the `D₃` root design `Gtz.rootKillDesign` — four dominating, twelve not — but
that identification is a separate computation and is NOT asserted here: what is asserted
is only that both spectra occur, which is all the ceiling needs. -/

section FibreCeiling

/-- Shifting a diagonal matrix by a multiple of the identity shifts its diagonal. -/
theorem diagonal_sub_smul_one {dim : ℕ} (entries : Fin dim → ℝ) (level : ℝ) :
    Matrix.diagonal entries - level • (1 : Matrix (Fin dim) (Fin dim) ℝ)
      = Matrix.diagonal fun index => entries index - level := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]

/-- `√2` squares back to `2`. -/
theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `√2 < 2`, which is what keeps the slack spectrum positive. -/
theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [sqrt_two_sq, Real.sqrt_nonneg 2]

/-- `4/3 < √2`, which is what puts the slack spectrum's least value below one. -/
theorem four_div_three_lt_sqrt_two : (4 : ℝ) / 3 < Real.sqrt 2 := by
  nlinarith [sqrt_two_sq, Real.sqrt_nonneg 2]

/-- **The dominating point of the fibre**, spectrum `(6, 3/2, 3/2)`. -/
noncomputable def dominatingFibreForm : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![6, 3 / 2, 3 / 2]

/-- **The slack point of the fibre**, spectrum `(3 − 3√2/2, 3, 3 + 3√2/2)`. -/
noncomputable def slackFibreForm : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![3 - 3 * Real.sqrt 2 / 2, 3, 3 + 3 * Real.sqrt 2 / 2]

theorem posSemidef_dominatingFibreForm : dominatingFibreForm.PosSemidef := by
  rw [dominatingFibreForm, Matrix.posSemidef_diagonal_iff]
  intro index
  fin_cases index <;> norm_num [Matrix.cons_val_two, Matrix.tail_cons]

theorem det_dominatingFibreForm : dominatingFibreForm.det = 27 / 2 := by
  rw [dominatingFibreForm, Matrix.det_diagonal, Fin.prod_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

theorem trace_dominatingFibreForm : Matrix.trace dominatingFibreForm = 9 := by
  rw [dominatingFibreForm, Matrix.trace_diagonal, Fin.sum_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

/-- The dominating point clears the threshold: `A ⪰ 1`. -/
theorem posSemidef_dominatingFibreForm_sub_one :
    (dominatingFibreForm - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  have hshift : dominatingFibreForm - (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = Matrix.diagonal fun index => (![6, 3 / 2, 3 / 2] : Fin 3 → ℝ) index - 1 := by
    rw [dominatingFibreForm, ← diagonal_sub_smul_one, one_smul]
  rw [hshift, Matrix.posSemidef_diagonal_iff]
  intro index
  fin_cases index <;> norm_num [Matrix.cons_val_two, Matrix.tail_cons]

theorem posSemidef_slackFibreForm : slackFibreForm.PosSemidef := by
  rw [slackFibreForm, Matrix.posSemidef_diagonal_iff]
  intro index
  have hupper := sqrt_two_lt_two
  have hlower := Real.sqrt_nonneg 2
  fin_cases index <;> norm_num [Matrix.cons_val_two, Matrix.tail_cons] <;> linarith

theorem det_slackFibreForm : slackFibreForm.det = 27 / 2 := by
  rw [slackFibreForm, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  linear_combination (-(27 : ℝ) / 4) * sqrt_two_sq

theorem trace_slackFibreForm : Matrix.trace slackFibreForm = 9 := by
  rw [slackFibreForm, Matrix.trace_diagonal, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- The slack point's least value sits strictly below the domination threshold. -/
theorem slackFibreLeast_lt_one : 3 - 3 * Real.sqrt 2 / 2 < 1 := by
  linarith [four_div_three_lt_sqrt_two]

/-- The slack point does NOT clear the threshold. -/
theorem not_posSemidef_slackFibreForm_sub_one :
    ¬ (slackFibreForm - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  intro hpsd
  have hshift : slackFibreForm - (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = Matrix.diagonal fun index =>
          (![3 - 3 * Real.sqrt 2 / 2, 3, 3 + 3 * Real.sqrt 2 / 2] : Fin 3 → ℝ) index - 1 := by
    rw [slackFibreForm, ← diagonal_sub_smul_one, one_smul]
  rw [hshift, Matrix.posSemidef_diagonal_iff] at hpsd
  have hleast := hpsd 0
  simp only [Matrix.cons_val_zero] at hleast
  linarith [four_div_three_lt_sqrt_two]

/-- **THE FIBRE DOES NOT DECIDE DOMINATION.**  Two positive semidefinite `3 × 3` forms
with the SAME determinant and the SAME trace, one above the identity and one not. -/
theorem exists_pair_on_detTraceFibre_separated_by_domination :
    ∃ dominatingForm slackForm : Matrix (Fin 3) (Fin 3) ℝ,
      dominatingForm.PosSemidef ∧ slackForm.PosSemidef
        ∧ dominatingForm.det = slackForm.det
        ∧ Matrix.trace dominatingForm = Matrix.trace slackForm
        ∧ (dominatingForm - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef
        ∧ ¬ (slackForm - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef :=
  ⟨dominatingFibreForm, slackFibreForm, posSemidef_dominatingFibreForm, posSemidef_slackFibreForm,
    by rw [det_dominatingFibreForm, det_slackFibreForm],
    by rw [trace_dominatingFibreForm, trace_slackFibreForm],
    posSemidef_dominatingFibreForm_sub_one, not_posSemidef_slackFibreForm_sub_one⟩

/-- **THE CEILING.**  Every function of the determinant and the trace that floors the
spectrum of every positive semidefinite `3 × 3` form is at most `3 − 3√2/2` at the fibre
`(27/2, 9)`.  The slack point supplies the obstruction; nothing about the function is
assumed beyond its being such a floor. -/
theorem detTraceFloorFunction_le_slackFibreLeast (floorFunction : ℝ → ℝ → ℝ)
    (hfloor : ∀ form : Matrix (Fin 3) (Fin 3) ℝ, form.PosSemidef →
      (form - floorFunction form.det (Matrix.trace form)
        • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef) :
    floorFunction (27 / 2) 9 ≤ 3 - 3 * Real.sqrt 2 / 2 := by
  have hshifted := hfloor slackFibreForm posSemidef_slackFibreForm
  rw [det_slackFibreForm, trace_slackFibreForm, slackFibreForm, diagonal_sub_smul_one,
    Matrix.posSemidef_diagonal_iff] at hshifted
  have hleast := hshifted 0
  simp only [Matrix.cons_val_zero] at hleast
  linarith

/-- **No determinant–trace floor certifies domination at rank three.**  At the fibre
`(27/2, 9)` every such floor is strictly below one, so it can never establish
`S_C ⪰ 1` — which is why C4 is landed as matrix analysis and not as a route. -/
theorem detTraceFloorFunction_lt_one (floorFunction : ℝ → ℝ → ℝ)
    (hfloor : ∀ form : Matrix (Fin 3) (Fin 3) ℝ, form.PosSemidef →
      (form - floorFunction form.det (Matrix.trace form)
        • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef) :
    floorFunction (27 / 2) 9 < 1 :=
  lt_of_le_of_lt (detTraceFloorFunction_le_slackFibreLeast floorFunction hfloor)
    slackFibreLeast_lt_one

/-- C4's own value on the fibre: `2²·(27/2)/9² = 2/3`. -/
theorem detTraceFloor_rankThreeFibre : detTraceFloor 3 (27 / 2) 9 = 2 / 3 := by
  rw [detTraceFloor]
  norm_num

/-- **C4 is not sharp for its own method on that fibre**: `2/3` sits strictly below the
ceiling `3 − 3√2/2 ≈ 0.8787`, which is itself strictly below one. -/
theorem detTraceFloor_rankThreeFibre_lt_slackFibreLeast :
    detTraceFloor 3 (27 / 2) 9 < 3 - 3 * Real.sqrt 2 / 2 := by
  rw [detTraceFloor_rankThreeFibre]
  nlinarith [sqrt_two_sq, Real.sqrt_nonneg 2]

end FibreCeiling

/-! ## The C6 companion: the matrix average clears the threshold, and no member need

Concavity of the least eigenvalue is shipped as
`Gtz.posSemidef_expectedSubsetSum_sub_volumeSamplingAverage_smul_one` and is not restated.
What is added is the unconditional matrix average and the gap between averaging matrices
and averaging their floors. -/

section MatrixAverage

variable {size rank : ℕ}

/-- **`E_π[S_C] ⪰ 1`, UNCONDITIONALLY.**  The shipped
`Gtz.posSemidef_leverageWeightedAtomSum_sub_one` puts the leverage-weighted atom sum above
the identity; identifying that sum with the volume-sampling expectation is the one-point
marginal, which is now the theorem `Gtz.isProjectionOnePointMarginal` rather than an
assumed `Prop`.  So the derandomisation question GTZ asks — is SOME `rank`-subset above the
identity? — is exactly the question whether this average can be attained at a point, and
the two witnesses below show that the matrix average alone cannot answer it. -/
theorem posSemidef_expectedSubsetSum_sub_one (design : WeightedDesign size rank) :
    (expectedSubsetSum design - (1 : Matrix (Fin rank) (Fin rank) ℝ)).PosSemidef := by
  rw [expectedSubsetSum_eq_leverageWeightedAtomSum design (isProjectionOnePointMarginal design)]
  exact posSemidef_leverageWeightedAtomSum_sub_one design

/-- The two-member family witnessing the derandomisation gap: member `index` is the
diagonal form vanishing at coordinate `index` and equal to `2` elsewhere. -/
noncomputable def averageGapForm (index : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal fun coordinate => if coordinate = index then 0 else 2

theorem posSemidef_averageGapForm (index : Fin 2) : (averageGapForm index).PosSemidef := by
  rw [averageGapForm, Matrix.posSemidef_diagonal_iff]
  intro coordinate
  by_cases hself : coordinate = index <;> simp [hself]

/-- No member admits a positive Loewner floor: each vanishes at its own coordinate. -/
theorem averageGapForm_floor_nonpos (index : Fin 2) (level : ℝ)
    (hfloor : (averageGapForm index - level • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef) :
    level ≤ 0 := by
  rw [averageGapForm, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub,
    Matrix.posSemidef_diagonal_iff] at hfloor
  have hself := hfloor index
  rw [if_pos rfl] at hself
  linarith

/-- The uniform average of the two members is the identity on the nose. -/
theorem half_smul_averageGapForm_add :
    (1 / 2 : ℝ) • averageGapForm 0 + (1 / 2 : ℝ) • averageGapForm 1
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [averageGapForm, averageGapForm]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [Matrix.diagonal, Matrix.one_apply]

/-- **THE DERANDOMISATION GAP, IN THE KERNEL.**  A positive semidefinite family and a
probability mass whose matrix average is above the identity while EVERY member's largest
Loewner floor is at most zero.  So a floor on the average is not a floor on any member,
and the averaged floors do not inherit the average's.

This is the design-free form of the volume-average law's refutation
(`Gtz.Quantitative.VolumeAverageLaw`, refuted there at an exact rational `(3,2)` design
with margin at least `49/2210`): the matrix average clears the threshold — for designs,
`posSemidef_expectedSubsetSum_sub_one` — while the eigenvalue average need not. -/
theorem exists_family_flooring_average_without_flooring_member :
    ∃ (family : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) (mass : Fin 2 → ℝ),
      (∀ index : Fin 2, (family index).PosSemidef)
        ∧ (∀ index : Fin 2, 0 ≤ mass index)
        ∧ (∑ index : Fin 2, mass index) = 1
        ∧ ((∑ index : Fin 2, mass index • family index)
            - (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef
        ∧ (∀ index : Fin 2, ∀ level : ℝ,
            (family index - level • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef → level ≤ 0) := by
  refine ⟨averageGapForm, fun _ => 1 / 2, posSemidef_averageGapForm, fun _ => by norm_num, ?_, ?_,
    averageGapForm_floor_nonpos⟩
  · rw [Fin.sum_univ_two]
    norm_num
  · rw [Fin.sum_univ_two, half_smul_averageGapForm_add, sub_self]
    exact Matrix.PosSemidef.zero

end MatrixAverage

end Gtz
