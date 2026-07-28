/-
# FLOOR-E2 — the elementary-symmetric floor on the chart value

`Gtz.cauchyBinetValueFloor_le_value_of_isChartArgmaxValue`
(`Gtz/Quantitative/CauchyBinetValueFloor.lean`) bounds a chart block's determinant by
its smallest eigenvalue and counts subsets, giving
`value ≥ -(1/size)(1 - 1/C(size-1, rank-1))`.  This file replaces the eigenvalue
CEILING by an eigenvalue PRODUCT and counts codimension-one minors instead, giving

    `value ≥ -(1/size) (1 - 1/((size - rank)(rank - 1) + rank))` ,

which is `-4/27` at `(6,3)` and `-10/77` at `(7,3)`, against FLOOR-CB's `-3/20` and
`-2/15`.  Both floors are then packaged as one: `combinedValueFloor` uses the count
`N = min (C(size-1, rank-1)) ((size-rank)(rank-1) + rank)`, so the kernel carries a
single floor at least as good as either everywhere and carrying no hypothesis on the
rank at all.

## The one step that changes, and why the hypothesis gets WEAKER

FLOOR-CB reads `det P[C] = lambda_min · (the other eigenvalues)` and bounds the second
factor by `1`, which needs `P[C] ⪯ 1`.  FLOOR-E2 bounds the same factor by
`e_{rank-1}(P[C])` instead — it IS one of that sum's terms, and every term is
nonnegative once `P[C] ⪰ 0`.  So the `⪯ 1` half of the contraction hypothesis is not
used anywhere below: `det_le_dotProduct_mulVec_mul_codimOneMinorSum` assumes ONLY
positive semidefiniteness.  The stronger floor is the cheaper one, and that is why it
is not merely a numerical improvement.

## The chain, in the order the file mechanizes it

1.  **The spectral reading of the minor sums**
    (`sum_det_principalMinors_eq_sum_prod_eigenvalues`): for a Hermitian matrix the
    sum of the `level`-sized principal minors is the `level`-th elementary symmetric
    function of the eigenvalues.  Mathlib's `Matrix.charpoly_coeff_eq_sum_minors` and
    `Matrix.IsHermitian.charpoly_eq` read the same coefficient two ways, and Vieta
    (`Finset.prod_X_add_C_coeff`) turns the second into the symmetric function.  This
    is the minor-side spectral dictionary that `Gtz.Quantitative.ChartHadamard`'s header
    records as absent from this repository, in the only form this argument needs.
2.  **The per-matrix inequality**
    (`det_le_dotProduct_mulVec_mul_codimOneMinorSum`): for `A ⪰ 0` and a unit probe,
    `det A ≤ ⟨u, A u⟩ · e_{n-1}(A)` at size `n`.  Factoring the determinant at the
    eigen-index that minimises gives `det A ≤ lambda_min · e_{n-1}(A)`, and the shipped
    Loewner criterion `Gtz.posSemidef_sub_smul_one_of_eigenvalue_ge` puts `lambda_min`
    below the Rayleigh quotient.
3.  **The block bridge**
    (`sum_shadowDeterminant_powersetCard_eq_sum_det_blockMinors`): a principal minor of
    a principal block is a principal minor of the chart, so `e_{rank-1}(P[C])` is
    `Σ_{B ⊆ C, |B| = rank-1} det P_B` with no `esymm` and no block in the statement.
    `Finset.powersetCard_map` moves the index along the enumeration and
    `Matrix.det_submatrix_equiv_self` moves the determinant.
4.  **E2-A, the per-subset cap**
    (`shadowDeterminant_le_mul_sum_shadowDeterminant_of_isChartArgmaxValue`):
    `det P[C] ≤ (max_{c ∈ C}(t_c + value)) · Σ_{B ⊆ C} det P_B`, stated against an
    arbitrary cap exactly as FLOOR-CB's C1-A is.
5.  **The sum** (`one_le_elementaryCount_mul_one_add_size_mul_value_of_isChartArgmaxValue`):
    Cauchy–Binet `Σ_C det P[C] = 1` against the exchange of summation
    `Σ_C (Σ_{c ∈ C} tau_c) E_C = Σ_c tau_c Σ_{C ∋ c} E_C`, the shipped count
    `Gtz.sum_esym_shadowDeterminant_mem_eq` and the leverage bound `P_cc ≤ 1`.

## THE CROSSOVER, which is a fact about the two counts and not about this file

The two floors are governed by `C(size-1, rank-1)` and `(size-rank)(rank-1) + rank`,
and the smaller count wins.  At `(5,3)` they are `6` and `7`, so the binomial wins
(`choose_lt_elementaryCount_fiveThree`); at `(6,3)` they are `10` and `9`, so E2 wins
(`elementaryCount_lt_choose_sixThree`).  So `(6,3)` is where E2 first beats the binomial
at rank three, and `(6,3)` is also the first open cell: the method's crossover lands on
the first cell that needs it.  Both instances are arithmetic about two numerals and
neither is a theorem about any design; that the two facts coincide is an observation
about where the improvement became available, not an ingredient of anything below.

## The exact hypotheses, so the reach is not overstated

`elementaryValueFloor_le_value_of_isChartArgmaxValue` consumes the design behind the
chart, the shipped admissibility field `Gtz.IsChartArgmaxValue`, the two raw weight
inequalities `-value ≤ t_c` and `Σ t_c = 1`, and `2 ≤ rank`.  The rank hypothesis is
NOT caution about the edges: it is exactly the hypothesis of the count
`Gtz.sum_esym_shadowDeterminant_mem_eq`, whose inner subset size `rank - 1` must be a
positive subset size.  The combined floor
(`combinedValueFloor_le_value_of_isChartArgmaxValue`) carries NO rank hypothesis: at
`rank = 1` the two counts are both `1`, the combined floor is `0`, and the statement is
dispatched to FLOOR-CB, which proves it there; `rank = 0` is unreachable because
admissibility is unsatisfiable at rank zero (`Gtz.rank_pos_of_isChartArgmaxValue`).
No cell is excluded at either edge and no strictness side condition appears anywhere.

Three lemmas below — `dotProduct_self_pick_eq_of_support`,
`dotProduct_mulVec_submatrix_pick_eq_of_support` and
`dotProduct_mulVec_le_of_admissibleProbe` — are the INLINE steps of the shipped
`Gtz.shadowDeterminant_le_dotProduct_mulVec_of_pick` and
`Gtz.shadowDeterminant_le_of_isChartArgmaxValue`, exported.  That file proves them and
does not name them, and it is not this file's to edit; the E2 chain needs the Rayleigh
quotient by itself rather than already multiplied into a determinant bound, so they are
restated here rather than re-derived somewhere else.

## C8-a, the tightened Handelman certificate

`Gtz.twoBlockEliminantCubic` is `E(g) = (6g+1)(3g-1)(6g-5)`, and
`Gtz.twoBlockEliminantCubic_eq_handelmanCombination` decomposes `27 E` positively in
the Bernstein basis of `[-3/20, 0]`.  On the E2 window the same shape gives

    `64 E(g) = 18603(-g)^3 + 196101(g + 4/27)(-g)^2`
              `+ 269001(g + 4/27)^2(-g) + 98415(g + 4/27)^3` ,

again with all four coefficients positive integers, and the left-endpoint margin
improves from `E(-3/20) = 1711/2000` to `E(-4/27) = 689/729`.  `E(-1/6) = 0`
(`twoBlockEliminantCubic_neg_inv_six_eq_zero`) and `-1/6 < -4/27`
(`not_tightenedWindow_neg_inv_six`), so the original `-1/size` window genuinely admits
a root of the eliminant and the floor is load-bearing rather than cosmetic.

## What this does NOT do

* It closes no covering class and makes no theorem unconditional.  A floor is
  class-independent — it constrains every datum equally and excludes no family.
  `Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_negativeValue` still
  carries the undischarged `Gtz.EliminatesChartTwoBlockValue`, and nothing below
  touches it.  The numeric hypothesis of that arc was already discharged by FLOOR-CB;
  the E2 constant would discharge it too, since `-4/27 ≤ value` implies
  `-3/20 ≤ value`, so it supplies margin and not a discharge, and no second discharge
  is stated here.
* It reaches nothing at `value ≥ 0`.  `GTZ(6,3)` and `GTZ(7,3)` are exactly as open
  after this file as before it; the window at `(6,3)` narrows from `(-1/6, 0)` to
  `[-4/27, 0)`, a shrink of exactly one ninth relative to the shipped `-1/size`.
* It is neither proved sharp nor proved improvable.  Outside Lean, three independent
  tightenings of the first-moment family all stop at the same concentrated corner — all
  the weight mass on one atom at leverage one — which satisfies each of them with
  EQUALITY.  That is quoted arithmetic, not a theorem of this development, and nothing
  below depends on it.
-/
import Mathlib
import Gtz.Quantitative.ProjectionOnePointMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The Rayleigh quotient along an enumeration of the support

The shipped `Gtz.shadowDeterminant_le_dotProduct_mulVec_of_pick` proves these two
transports inline on its way to a determinant bound.  FLOOR-E2 needs the quotient
BEFORE it is multiplied into anything, so they are named here. -/

section Transport

variable {size rank : ℕ}

/-- **Transport of the squared length.**  A probe supported on a subset has the same
squared length read along any injective enumeration of that subset. -/
theorem dotProduct_self_pick_eq_of_support {selected : Finset (Fin size)}
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = selected) {probe : Fin size → ℝ}
    (hsupport : ∀ atomIndex : Fin size, atomIndex ∉ selected → probe atomIndex = 0) :
    (fun index : Fin rank => probe (pick index)) ⬝ᵥ (fun index : Fin rank => probe (pick index))
      = probe ⬝ᵥ probe := by
  rw [dotProduct, ← sum_selected_eq_sum_pick pick hinjective himage
      fun atomIndex => probe atomIndex * probe atomIndex,
    ← sum_eq_sum_of_vanishes_offSubset (fun atomIndex => probe atomIndex * probe atomIndex)
      fun atomIndex hnotMem => by rw [hsupport atomIndex hnotMem, mul_zero]]
  rfl

/-- **Transport of the Rayleigh quotient.**  A probe supported on a subset sees the
same quadratic form through the block along the subset as through the whole matrix. -/
theorem dotProduct_mulVec_submatrix_pick_eq_of_support (form : Matrix (Fin size) (Fin size) ℝ)
    {selected : Finset (Fin size)} (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = selected) {probe : Fin size → ℝ}
    (hsupport : ∀ atomIndex : Fin size, atomIndex ∉ selected → probe atomIndex = 0) :
    (fun index : Fin rank => probe (pick index))
        ⬝ᵥ (form.submatrix pick pick *ᵥ fun index : Fin rank => probe (pick index))
      = probe ⬝ᵥ (form *ᵥ probe) := by
  have hrow : ∀ index : Fin rank,
      (form.submatrix pick pick *ᵥ fun otherIndex : Fin rank => probe (pick otherIndex)) index
        = (form *ᵥ probe) (pick index) := by
    intro index
    have hcollapse := (sum_eq_sum_of_vanishes_offSubset
      (fun atomIndex => form (pick index) atomIndex * probe atomIndex)
      fun atomIndex hnotMem => by rw [hsupport atomIndex hnotMem, mul_zero]).trans
      (sum_selected_eq_sum_pick pick hinjective himage _)
    simpa only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] using hcollapse.symm
  rw [dotProduct, Finset.sum_congr rfl fun index _ => by rw [hrow index],
    ← sum_selected_eq_sum_pick pick hinjective himage
      fun atomIndex => probe atomIndex * (form *ᵥ probe) atomIndex,
    ← sum_eq_sum_of_vanishes_offSubset
      (fun atomIndex => probe atomIndex * (form *ᵥ probe) atomIndex)
      fun atomIndex hnotMem => by rw [hsupport atomIndex hnotMem, zero_mul]]
  rfl

/-- **The chart quotient at an admissible probe is capped.**  A unit probe supported on
a subset whose gap quotient is at most `value` has chart quotient at most any upper
bound of `t_c + value` over the subset, because
`⟨u, P u⟩ = ⟨u, W u⟩ + Σ_c t_c u_c²` and the probe's mass is one. -/
theorem dotProduct_mulVec_le_of_admissibleProbe
    {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value capValue : ℝ}
    {selected : Finset (Fin size)} {probe : Fin size → ℝ} (hunit : probe ⬝ᵥ probe = 1)
    (hsupport : ∀ atomIndex : Fin size, atomIndex ∉ selected → probe atomIndex = 0)
    (hquotient : probe ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe) ≤ value)
    (hcap : ∀ atomIndex ∈ selected, weight atomIndex + value ≤ capValue) :
    probe ⬝ᵥ (projection *ᵥ probe) ≤ capValue := by
  have hprobeMass : ∑ atomIndex ∈ selected, probe atomIndex ^ 2 = 1 := by
    rw [← sum_eq_sum_of_vanishes_offSubset (fun atomIndex => probe atomIndex ^ 2)
      fun atomIndex hnotMem => by rw [hsupport atomIndex hnotMem]; ring,
      ← dotProduct_self_eq_sum_sq]
    exact hunit
  have hsplit : probe ⬝ᵥ (projection *ᵥ probe)
      = probe ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe)
        + ∑ atomIndex : Fin size, weight atomIndex * probe atomIndex ^ 2 := by
    have hdiagonal : probe ⬝ᵥ (Matrix.diagonal weight *ᵥ probe)
        = ∑ atomIndex : Fin size, weight atomIndex * probe atomIndex ^ 2 :=
      Finset.sum_congr rfl fun atomIndex _ => by rw [Matrix.mulVec_diagonal]; ring
    rw [chartStationaryGap, Matrix.sub_mulVec, dotProduct_sub, hdiagonal]
    ring
  have hweightMass : ∑ atomIndex : Fin size, weight atomIndex * probe atomIndex ^ 2
      = ∑ atomIndex ∈ selected, weight atomIndex * probe atomIndex ^ 2 :=
    sum_eq_sum_of_vanishes_offSubset _
      fun atomIndex hnotMem => by rw [hsupport atomIndex hnotMem]; ring
  have hweighted : probe ⬝ᵥ (projection *ᵥ probe)
      ≤ ∑ atomIndex ∈ selected, (weight atomIndex + value) * probe atomIndex ^ 2 := by
    have hexpand : ∑ atomIndex ∈ selected, (weight atomIndex + value) * probe atomIndex ^ 2
        = (∑ atomIndex ∈ selected, weight atomIndex * probe atomIndex ^ 2)
          + value * ∑ atomIndex ∈ selected, probe atomIndex ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsplit, hweightMass, hexpand, hprobeMass, mul_one]
    linarith
  have hcapped : ∑ atomIndex ∈ selected, (weight atomIndex + value) * probe atomIndex ^ 2
      ≤ capValue := by
    have hterms : ∑ atomIndex ∈ selected, (weight atomIndex + value) * probe atomIndex ^ 2
        ≤ ∑ atomIndex ∈ selected, capValue * probe atomIndex ^ 2 :=
      Finset.sum_le_sum fun atomIndex hmem =>
        mul_le_mul_of_nonneg_right (hcap atomIndex hmem) (sq_nonneg _)
    rwa [← Finset.mul_sum, hprobeMass, mul_one] at hterms
  linarith

end Transport

/-! ## The spectral reading of the principal-minor sums -/

section Spectral

variable {dimension : ℕ}

/-- **The principal-minor sums are the elementary symmetric functions of the
spectrum.**  Both sides are one coefficient of the characteristic polynomial:
`Matrix.charpoly_coeff_eq_sum_minors` reads it as a signed minor sum, and
`Matrix.IsHermitian.charpoly_eq` together with Vieta's `Finset.prod_X_add_C_coeff`
reads it as a signed symmetric function of the eigenvalues.  The common sign
`(-1)^level` cancels.

The hypothesis `level ≤ dimension` is what Vieta and the minor formula both need; above the
dimension the coefficient is zero on the left and the index arithmetic collapses on
the right. -/
theorem sum_det_principalMinors_eq_sum_prod_eigenvalues
    {form : Matrix (Fin dimension) (Fin dimension) ℝ} (hHermitian : form.IsHermitian)
    (level : ℕ) (hlevel : level ≤ dimension) :
    ∑ selected ∈ (Finset.univ : Finset (Fin dimension)).powersetCard level,
        (form.submatrix (Subtype.val : { index // index ∈ selected } → Fin dimension)
          (Subtype.val : { index // index ∈ selected } → Fin dimension)).det
      = ∑ selected ∈ (Finset.univ : Finset (Fin dimension)).powersetCard level,
          ∏ eigenIndex ∈ selected, hHermitian.eigenvalues eigenIndex := by
  classical
  have hcardFin : Fintype.card (Fin dimension) = dimension := Fintype.card_fin dimension
  have hminors := Matrix.charpoly_coeff_eq_sum_minors form level (by rw [hcardFin]; exact hlevel)
  rw [hcardFin] at hminors
  have hcharpoly : form.charpoly = ∏ eigenIndex : Fin dimension,
      (Polynomial.X + Polynomial.C (-(hHermitian.eigenvalues eigenIndex))) := by
    rw [hHermitian.charpoly_eq]
    refine Finset.prod_congr rfl fun eigenIndex _ => ?_
    rw [map_neg, sub_eq_add_neg]
    norm_cast
  have hvieta := Finset.prod_X_add_C_coeff (Finset.univ : Finset (Fin dimension))
    (fun eigenIndex => -(hHermitian.eigenvalues eigenIndex)) (k := dimension - level)
    (by rw [Finset.card_univ, hcardFin]; omega)
  have hcomplement : dimension - (dimension - level) = level := by omega
  rw [Finset.card_univ, hcardFin, hcomplement] at hvieta
  rw [hcharpoly, hvieta] at hminors
  have hsign : ∀ selected ∈ (Finset.univ : Finset (Fin dimension)).powersetCard level,
      ∏ eigenIndex ∈ selected, (-(hHermitian.eigenvalues eigenIndex))
        = (-1 : ℝ) ^ level * ∏ eigenIndex ∈ selected, hHermitian.eigenvalues eigenIndex := by
    intro selected hmem
    calc ∏ eigenIndex ∈ selected, (-(hHermitian.eigenvalues eigenIndex))
        = ∏ eigenIndex ∈ selected, ((-1 : ℝ) * hHermitian.eigenvalues eigenIndex) :=
          Finset.prod_congr rfl fun eigenIndex _ => (neg_one_mul _).symm
      _ = (∏ _eigenIndex ∈ selected, (-1 : ℝ))
            * ∏ eigenIndex ∈ selected, hHermitian.eigenvalues eigenIndex :=
          Finset.prod_mul_distrib
      _ = (-1 : ℝ) ^ level * ∏ eigenIndex ∈ selected, hHermitian.eigenvalues eigenIndex := by
          rw [Finset.prod_const, (Finset.mem_powersetCard.mp hmem).2]
  rw [Finset.sum_congr rfl hsign, ← Finset.mul_sum] at hminors
  exact mul_left_cancel₀ (pow_ne_zero level (by norm_num : (-1 : ℝ) ≠ 0)) hminors.symm

/-- **The codimension-one principal-minor sum** of a square matrix: the total of its
principal minors one size below the full one.  For a Hermitian matrix this is
`e_{dimension-1}` of the spectrum, which is
`sum_det_principalMinors_eq_sum_prod_eigenvalues` at `level = dimension - 1`. -/
noncomputable def codimOneMinorSum (form : Matrix (Fin dimension) (Fin dimension) ℝ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Fin dimension)).powersetCard (dimension - 1),
    (form.submatrix (Subtype.val : { index // index ∈ selected } → Fin dimension)
      (Subtype.val : { index // index ∈ selected } → Fin dimension)).det

/-- Every principal minor of a positive semidefinite matrix is nonnegative, so the
codimension-one total is. -/
theorem codimOneMinorSum_nonneg {form : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hpsd : form.PosSemidef) : 0 ≤ codimOneMinorSum form :=
  Finset.sum_nonneg fun _selected _ => (hpsd.submatrix _).det_nonneg

/-- **The determinant is below every eigenvalue times the codimension-one total.**
The determinant is the product of the eigenvalues; factoring out any one of them
leaves a product which IS one of the nonnegative terms of the total.  Only positive
semidefiniteness is used — there is no eigenvalue ceiling here, which is exactly where
this parts company with `Gtz.det_le_eigenvalue_of_posSemidef_of_posSemidef_one_sub`. -/
theorem det_le_eigenvalue_mul_codimOneMinorSum {form : Matrix (Fin dimension) (Fin dimension) ℝ}
    (hpsd : form.PosSemidef) (eigenIndex : Fin dimension) :
    form.det ≤ hpsd.1.eigenvalues eigenIndex * codimOneMinorSum form := by
  classical
  have hspectral :=
    sum_det_principalMinors_eq_sum_prod_eigenvalues hpsd.1 (dimension - 1) (by omega)
  have hmem : (Finset.univ : Finset (Fin dimension)).erase eigenIndex
      ∈ (Finset.univ : Finset (Fin dimension)).powersetCard (dimension - 1) := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by
      rw [Finset.card_erase_of_mem (Finset.mem_univ eigenIndex), Finset.card_univ,
        Fintype.card_fin]⟩
  have hsingle : ∏ otherIndex ∈ (Finset.univ : Finset (Fin dimension)).erase eigenIndex,
        hpsd.1.eigenvalues otherIndex
      ≤ ∑ selected ∈ (Finset.univ : Finset (Fin dimension)).powersetCard (dimension - 1),
          ∏ otherIndex ∈ selected, hpsd.1.eigenvalues otherIndex :=
    Finset.single_le_sum
      (f := fun selected => ∏ otherIndex ∈ selected, hpsd.1.eigenvalues otherIndex)
      (fun selected _ => Finset.prod_nonneg fun otherIndex _ => hpsd.eigenvalues_nonneg otherIndex)
      hmem
  have hdet : form.det = hpsd.1.eigenvalues eigenIndex
      * ∏ otherIndex ∈ (Finset.univ : Finset (Fin dimension)).erase eigenIndex,
          hpsd.1.eigenvalues otherIndex := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ eigenIndex)]
    simpa using hpsd.1.det_eq_prod_eigenvalues
  rw [hdet, codimOneMinorSum, hspectral]
  exact mul_le_mul_of_nonneg_left hsingle (hpsd.eigenvalues_nonneg eigenIndex)

/-- **THE E2 SPECTRAL STEP.**  For `A ⪰ 0` and a unit probe,

    `det A ≤ ⟨u, A u⟩ · e_{dimension-1}(A)` .

The previous lemma at the minimising eigen-index gives `det A ≤ lambda_min · e`, the
shipped Loewner criterion `Gtz.posSemidef_sub_smul_one_of_eigenvalue_ge` puts
`lambda_min` below the quotient at a unit probe, and `e ≥ 0` lets the two be
multiplied.  The probe forces the dimension positive, so no side condition is carried.

This assumes strictly less than the FLOOR-CB step
`Gtz.det_le_dotProduct_mulVec_of_posSemidef_of_posSemidef_one_sub`, which also needs
`1 - A ⪰ 0`. -/
theorem det_le_dotProduct_mulVec_mul_codimOneMinorSum
    {form : Matrix (Fin dimension) (Fin dimension) ℝ} (hpsd : form.PosSemidef)
    {probe : Fin dimension → ℝ} (hunit : probe ⬝ᵥ probe = 1) :
    form.det ≤ (probe ⬝ᵥ (form *ᵥ probe)) * codimOneMinorSum form := by
  classical
  have hnonempty : (Finset.univ : Finset (Fin dimension)).Nonempty := by
    rcases Nat.eq_zero_or_pos dimension with hzero | hpos
    · exfalso
      subst hzero
      simp [dotProduct] at hunit
    · exact ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
  obtain ⟨minIndex, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin dimension)) hpsd.1.eigenvalues hnonempty
  have hshift := posSemidef_sub_smul_one_of_eigenvalue_ge hpsd.1
    (hpsd.1.eigenvalues minIndex) fun eigenIndex => hmin eigenIndex (Finset.mem_univ eigenIndex)
  have hquadratic := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hshift).2 probe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, hunit, mul_one] at hquadratic
  have hminorNonneg := codimOneMinorSum_nonneg hpsd
  have hstep := det_le_eigenvalue_mul_codimOneMinorSum hpsd minIndex
  nlinarith [hquadratic, hminorNonneg, hstep]

end Spectral

/-! ## The block bridge: `e_{rank-1}` of a chart block is a chart minor sum -/

section BlockBridge

variable {size rank : ℕ}

/-- The index equivalence between a subset of the enumerating type and its image. -/
noncomputable def mappedSubsetEquiv {domain codomain : Type*} [DecidableEq codomain]
    (embedding : domain ↪ codomain) (chosen : Finset domain) :
    { index // index ∈ chosen } ≃ { element // element ∈ chosen.map embedding } :=
  Equiv.ofBijective
    (fun index => ⟨embedding index.val, Finset.mem_map_of_mem embedding index.2⟩)
    ⟨fun leftIndex rightIndex hpair =>
        Subtype.ext (embedding.injective (congrArg Subtype.val hpair)), by
      rintro ⟨element, hmem⟩
      obtain ⟨index, hindex, himage⟩ := Finset.mem_map.mp hmem
      exact ⟨⟨index, hindex⟩, Subtype.ext himage⟩⟩

/-- **A principal minor of a principal block is a principal minor of the chart.**  Both
are determinants of the same matrix up to simultaneous reindexing along the
enumeration, so `Matrix.det_submatrix_equiv_self` identifies them. -/
theorem shadowDeterminant_map_eq_det_blockMinor (design : WeightedDesign size rank)
    (pick : Fin rank ↪ Fin size) (chosen : Finset (Fin rank)) :
    shadowDeterminant design (chosen.map pick)
      = (((projectionOfDesign design).submatrix pick pick).submatrix
          (Subtype.val : { index // index ∈ chosen } → Fin rank)
          (Subtype.val : { index // index ∈ chosen } → Fin rank)).det := by
  rw [shadowDeterminant,
    ← Matrix.det_submatrix_equiv_self (mappedSubsetEquiv pick chosen)
      ((projectionOfDesign design).submatrix
        (Subtype.val : { element // element ∈ chosen.map pick } → Fin size)
        (Subtype.val : { element // element ∈ chosen.map pick } → Fin size))]
  rfl

/-- **THE BLOCK BRIDGE.**  The chart's minors of a fixed size sitting inside a subset
are exactly the block's principal minors of that size, so the elementary symmetric
function of a block's spectrum never has to be written as an `esymm`.
`Finset.powersetCard_map` moves the index set along the enumeration and the previous
lemma moves each determinant. -/
theorem sum_shadowDeterminant_powersetCard_eq_sum_det_blockMinors
    (design : WeightedDesign size rank) {selected : Finset (Fin size)}
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = selected) (level : ℕ) :
    ∑ subselected ∈ selected.powersetCard level, shadowDeterminant design subselected
      = ∑ chosen ∈ (Finset.univ : Finset (Fin rank)).powersetCard level,
          (((projectionOfDesign design).submatrix pick pick).submatrix
            (Subtype.val : { index // index ∈ chosen } → Fin rank)
            (Subtype.val : { index // index ∈ chosen } → Fin rank)).det := by
  classical
  have hmapImage : Finset.map ⟨pick, hinjective⟩ (Finset.univ : Finset (Fin rank)) = selected := by
    rw [Finset.map_eq_image]
    exact himage
  rw [← hmapImage, Finset.powersetCard_map, Finset.sum_map]
  exact Finset.sum_congr rfl fun chosen _ =>
    shadowDeterminant_map_eq_det_blockMinor design ⟨pick, hinjective⟩ chosen

/-- The block's codimension-one minor total, read on the chart. -/
theorem codimOneMinorSum_submatrix_eq_sum_shadowDeterminant (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = selected) :
    codimOneMinorSum ((projectionOfDesign design).submatrix pick pick)
      = ∑ subselected ∈ selected.powersetCard (rank - 1), shadowDeterminant design subselected :=
  (sum_shadowDeterminant_powersetCard_eq_sum_det_blockMinors design pick hinjective himage
    (rank - 1)).symm

end BlockBridge

/-! ## E2-A: the per-subset cap -/

section PerSubset

variable {size rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
  {value : ℝ}

/-- **E2-A, THE PER-SUBSET CAP.**  At an admissible value, the shadow determinant of
every `rank`-subset is at most any upper bound of `t_c + value` over that subset, times
the total of the chart minors one size below sitting inside it:

    `det P[C] ≤ (max_{c ∈ C} (t_c + value)) · Σ_{B ⊆ C, |B| = rank-1} det P_B` .

Stated against an arbitrary cap, exactly as `Gtz.shadowDeterminant_le_of_isChartArgmaxValue`
is, so that the maximum is not needed as a gadget.  The inputs are the design behind
the chart (through `P[C] ⪰ 0` — and NOT through `P[C] ⪯ 1`, which is where FLOOR-CB
spends more), admissibility, and nothing else: no weight floor and no sign condition
appear.  Everything after this is a sum over it. -/
theorem shadowDeterminant_le_mul_sum_shadowDeterminant_of_isChartArgmaxValue
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) {capValue : ℝ}
    (hcap : ∀ atomIndex ∈ selected, weight atomIndex + value ≤ capValue) :
    shadowDeterminant design selected
      ≤ capValue * ∑ subselected ∈ selected.powersetCard (rank - 1),
          shadowDeterminant design subselected := by
  classical
  obtain ⟨probe, hunit, hsupport, hquotient⟩ := hargmax selected hcard
  have hinjective : Function.Injective (selected.orderEmbOfFin hcard) :=
    (selected.orderEmbOfFin hcard).injective
  have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected :=
    image_orderEmbOfFin hcard
  have hblockPsd : ((projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard)).PosSemidef :=
    (posSemidef_projectionOfDesign design).submatrix _
  have hblockUnit : (fun index : Fin rank => probe (selected.orderEmbOfFin hcard index))
      ⬝ᵥ (fun index : Fin rank => probe (selected.orderEmbOfFin hcard index)) = 1 := by
    rw [dotProduct_self_pick_eq_of_support _ hinjective himage hsupport]
    exact hunit
  have hspectral := det_le_dotProduct_mulVec_mul_codimOneMinorSum hblockPsd hblockUnit
  rw [dotProduct_mulVec_submatrix_pick_eq_of_support (projectionOfDesign design) _ hinjective
      himage hsupport,
    codimOneMinorSum_submatrix_eq_sum_shadowDeterminant design _ hinjective himage] at hspectral
  have hchartQuotient : probe ⬝ᵥ (projectionOfDesign design *ᵥ probe) ≤ capValue := by
    rw [← hchart]
    exact dotProduct_mulVec_le_of_admissibleProbe hunit hsupport hquotient hcap
  have hminorNonneg : 0 ≤ ∑ subselected ∈ selected.powersetCard (rank - 1),
      shadowDeterminant design subselected := by
    rw [← codimOneMinorSum_submatrix_eq_sum_shadowDeterminant design _ hinjective himage]
    exact codimOneMinorSum_nonneg hblockPsd
  rw [shadowDeterminant_eq_det_submatrix design _ hinjective himage]
  exact hspectral.trans (mul_le_mul_of_nonneg_right hchartQuotient hminorNonneg)

end PerSubset

/-! ## The two counts and the floors they define -/

/-- **The E2 count** `(size - rank)(rank - 1) + rank`: the value at leverage one of the
per-atom total `Σ_{C ∋ c} e_{rank-1}(P[C])` proved in
`Gtz.sum_esym_shadowDeterminant_mem_eq`. -/
def elementaryCount (size rank : ℕ) : ℕ := (size - rank) * (rank - 1) + rank

/-- **The combined count**: the smaller of the Cauchy–Binet binomial and the E2 count.
The floor is decreasing in the count, so the smaller count is the better floor. -/
def combinedCount (size rank : ℕ) : ℕ :=
  min ((size - 1).choose (rank - 1)) (elementaryCount size rank)

/-- **The floor a count defines**, `-(1/size)(1 - 1/count)`.  That
`Gtz.cauchyBinetValueFloor` is this at the binomial is `cauchyBinetValueFloor_eq`. -/
noncomputable def valueFloorOfCount (size count : ℕ) : ℝ :=
  -((size : ℝ))⁻¹ * (1 - ((count : ℕ) : ℝ)⁻¹)

/-- **THE ELEMENTARY-SYMMETRIC FLOOR** `-(1/size)(1 - 1/((size-rank)(rank-1) + rank))`,
as a definition of a real number.  That it IS a floor on the chart value is
`elementaryValueFloor_le_value_of_isChartArgmaxValue` below. -/
noncomputable def elementaryValueFloor (size rank : ℕ) : ℝ :=
  valueFloorOfCount size (elementaryCount size rank)

/-- **THE COMBINED FLOOR**, at least as good as both of its parents at every cell. -/
noncomputable def combinedValueFloor (size rank : ℕ) : ℝ :=
  valueFloorOfCount size (combinedCount size rank)

/-- The shipped Cauchy–Binet floor is the count floor at the binomial. -/
theorem cauchyBinetValueFloor_eq (size rank : ℕ) :
    cauchyBinetValueFloor size rank = valueFloorOfCount size ((size - 1).choose (rank - 1)) := rfl

/-- **The count floor is decreasing in the count**: a smaller count is a better floor.
This is what makes `combinedCount` a minimum rather than a maximum. -/
theorem valueFloorOfCount_le_valueFloorOfCount_of_count_le {size smallCount largeCount : ℕ}
    (hsmallPos : 0 < smallCount) (hcountLe : smallCount ≤ largeCount) :
    valueFloorOfCount size largeCount ≤ valueFloorOfCount size smallCount := by
  have hsizeNonneg : (0 : ℝ) ≤ ((size : ℝ))⁻¹ := by positivity
  have hsmallCast : (0 : ℝ) < (smallCount : ℝ) := by exact_mod_cast hsmallPos
  have hlargeCast : (0 : ℝ) < (largeCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hsmallPos hcountLe
  have hinverse : ((largeCount : ℕ) : ℝ)⁻¹ ≤ ((smallCount : ℕ) : ℝ)⁻¹ :=
    one_div (largeCount : ℝ) ▸ one_div (smallCount : ℝ) ▸
      one_div_le_one_div_of_le hsmallCast (by exact_mod_cast hcountLe)
  rw [valueFloorOfCount, valueFloorOfCount, neg_mul, neg_mul, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (by linarith) hsizeNonneg

/-- **The mass inequality solved for the value.**  A positive count whose product with
`1 + size · value` clears one puts the count's floor below the value. -/
theorem valueFloorOfCount_le_value_of_one_le_mul {size count : ℕ} {value : ℝ}
    (hsizePos : 0 < size) (hcountPos : 0 < count)
    (hmass : 1 ≤ ((count : ℕ) : ℝ) * (1 + (size : ℝ) * value)) :
    valueFloorOfCount size count ≤ value := by
  have hsizeCast : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsizePos
  have hcountCast : (0 : ℝ) < ((count : ℕ) : ℝ) := by exact_mod_cast hcountPos
  have hdivideCount : ((count : ℕ) : ℝ)⁻¹ ≤ 1 + (size : ℝ) * value := by
    have hscaled := mul_le_mul_of_nonneg_left hmass (inv_pos.mpr hcountCast).le
    rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hcountCast.ne', one_mul] at hscaled
  have hdivideSize := mul_le_mul_of_nonneg_left
    (show ((count : ℕ) : ℝ)⁻¹ - 1 ≤ (size : ℝ) * value by linarith) (inv_pos.mpr hsizeCast).le
  rw [← mul_assoc, inv_mul_cancel₀ hsizeCast.ne', one_mul] at hdivideSize
  have hrewrite : valueFloorOfCount size count
      = ((size : ℝ))⁻¹ * (((count : ℕ) : ℝ)⁻¹ - 1) := by
    rw [valueFloorOfCount]; ring
  rw [hrewrite]
  exact hdivideSize

/-! ## The double count with a per-atom weight -/

/-- **The weighted exchange of summation.**  Summing a subset-indexed quantity against
the atoms each subset contains is the same as summing per atom over the subsets that
contain it.  The companion of `Gtz.sum_powersetCard_sum_mem_eq_choose_mul_sum`, which
is the case of a constant subset-indexed quantity; unlike that one this needs no
positivity on the rank, because nothing is being counted. -/
theorem sum_powersetCard_sum_mem_mul_eq {size : ℕ} (rank : ℕ) (atomWeight : Fin size → ℝ)
    (subsetValue : Finset (Fin size) → ℝ) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
        (∑ atomIndex ∈ selected, atomWeight atomIndex) * subsetValue selected
      = ∑ atomIndex : Fin size, atomWeight atomIndex
          * ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
              (if atomIndex ∈ selected then subsetValue selected else 0) := by
  classical
  have hrestrict : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      (∑ atomIndex ∈ selected, atomWeight atomIndex) * subsetValue selected
        = ∑ atomIndex : Fin size,
            (if atomIndex ∈ selected then atomWeight atomIndex * subsetValue selected else 0) := by
    intro selected _
    rw [← Finset.sum_filter, Finset.filter_univ_mem, Finset.sum_mul]
  rw [Finset.sum_congr rfl hrestrict, Finset.sum_comm]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun selected _ => by
    by_cases hmem : atomIndex ∈ selected
    · rw [if_pos hmem, if_pos hmem]
    · rw [if_neg hmem, if_neg hmem, mul_zero]

/-! ## The floor -/

section Floor

variable {size rank : ℕ} {activeIndex : Type*} {projection : Matrix (Fin size) (Fin size) ℝ}
  {weight : Fin size → ℝ} {value : ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE E2 MASS INEQUALITY**, which is the floor before it is solved for the value.
Cauchy–Binet against the per-subset cap, the weighted exchange of summation, the
shipped count `Gtz.sum_esym_shadowDeterminant_mem_eq` and the leverage bound
`P_cc = t_c ℓ_c ≤ 1`.

`2 ≤ rank` is the count's hypothesis and nothing more: at `rank = 1` the inner subset
size `rank - 1` is not a positive subset size, and the count is not available in that
form.  The combined floor below carries no rank hypothesis at all. -/
theorem one_le_elementaryCount_mul_one_add_size_mul_value_of_isChartArgmaxValue
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value) (hrank : 2 ≤ rank)
    (hweightFloor : ∀ atomIndex : Fin size, -value ≤ weight atomIndex)
    (hweightSum : ∑ atomIndex : Fin size, weight atomIndex = 1) :
    1 ≤ ((elementaryCount size rank : ℕ) : ℝ) * (1 + (size : ℝ) * value) := by
  classical
  have hperSubset : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      shadowDeterminant design selected
        ≤ (∑ atomIndex ∈ selected, (weight atomIndex + value))
          * ∑ subselected ∈ selected.powersetCard (rank - 1),
              shadowDeterminant design subselected := by
    intro selected hmemFamily
    refine shadowDeterminant_le_mul_sum_shadowDeterminant_of_isChartArgmaxValue design hchart
      hargmax (Finset.mem_powersetCard.mp hmemFamily).2 fun atomIndex hmemSelected => ?_
    exact Finset.single_le_sum (f := fun otherIndex => weight otherIndex + value)
      (fun otherIndex _ => by linarith [hweightFloor otherIndex]) hmemSelected
  have hmass : (1 : ℝ) ≤ ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      (∑ atomIndex ∈ selected, (weight atomIndex + value))
        * ∑ subselected ∈ selected.powersetCard (rank - 1),
            shadowDeterminant design subselected := by
    rw [← sum_shadowDeterminant_eq_one design]
    exact Finset.sum_le_sum hperSubset
  rw [sum_powersetCard_sum_mem_mul_eq rank (fun atomIndex => weight atomIndex + value)
    fun selected => ∑ subselected ∈ selected.powersetCard (rank - 1),
      shadowDeterminant design subselected] at hmass
  have hcount : ∀ atomIndex : Fin size,
      (weight atomIndex + value)
          * ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
              (if atomIndex ∈ selected then
                ∑ subselected ∈ selected.powersetCard (rank - 1),
                  shadowDeterminant design subselected else 0)
        ≤ (weight atomIndex + value) * ((elementaryCount size rank : ℕ) : ℝ) := by
    intro atomIndex
    have hdiagonal : projectionOfDesign design atomIndex atomIndex ≤ 1 := by
      rw [projectionOfDesign_diagonal]
      exact weighted_leverage_le_one design atomIndex
    have hcoefficient : (0 : ℝ) ≤ ((size - rank : ℕ) : ℝ) * ((rank - 1 : ℕ) : ℝ) := by positivity
    have hcast : ((elementaryCount size rank : ℕ) : ℝ)
        = ((size - rank : ℕ) : ℝ) * ((rank - 1 : ℕ) : ℝ) + (rank : ℝ) := by
      simp only [elementaryCount, Nat.cast_add, Nat.cast_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [hweightFloor atomIndex])
    rw [sum_esym_shadowDeterminant_mem_eq design atomIndex hrank, hcast]
    nlinarith [hcoefficient, hdiagonal]
  have hcapped : ∑ atomIndex : Fin size, (weight atomIndex + value)
        * ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
            (if atomIndex ∈ selected then
              ∑ subselected ∈ selected.powersetCard (rank - 1),
                shadowDeterminant design subselected else 0)
      ≤ ∑ atomIndex : Fin size,
          (weight atomIndex + value) * ((elementaryCount size rank : ℕ) : ℝ) :=
    Finset.sum_le_sum fun atomIndex _ => hcount atomIndex
  have htotal : ∑ atomIndex : Fin size,
        (weight atomIndex + value) * ((elementaryCount size rank : ℕ) : ℝ)
      = ((elementaryCount size rank : ℕ) : ℝ) * (1 + (size : ℝ) * value) := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, hweightSum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  linarith [hmass, hcapped, htotal.le, htotal.ge]

/-- The E2 count is positive whenever the rank is. -/
theorem elementaryCount_pos {size rank : ℕ} (hrank : 0 < rank) : 0 < elementaryCount size rank := by
  rw [elementaryCount]
  omega

/-- The Cauchy–Binet count is positive on every cell. -/
theorem cauchyBinetCount_pos {size rank : ℕ} (hrank : 0 < rank) (hrankLe : rank ≤ size) :
    0 < (size - 1).choose (rank - 1) :=
  Nat.choose_pos (by omega)

/-- The combined count is positive on every cell. -/
theorem combinedCount_pos {size rank : ℕ} (hrank : 0 < rank) (hrankLe : rank ≤ size) :
    0 < combinedCount size rank :=
  lt_min (cauchyBinetCount_pos hrank hrankLe) (elementaryCount_pos hrank)

/-- **FLOOR-E2.**  An admissible chart value of rank at least two, whose chart is a
design's and whose weights obey the floor `-value ≤ t_c` and sum to one, satisfies

    `-(1/size)(1 - 1/((size-rank)(rank-1) + rank)) ≤ value` .

The weight floor is exactly what `Gtz.weight_ge_neg_value_of_isChartStationaryData`
supplies; no other field of the stationarity bundle is consumed, no hypothesis on the
size is imposed, and no upper bound on the rank appears. -/
theorem elementaryValueFloor_le_value_of_isChartArgmaxValue
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value) (hrank : 2 ≤ rank)
    (hweightFloor : ∀ atomIndex : Fin size, -value ≤ weight atomIndex)
    (hweightSum : ∑ atomIndex : Fin size, weight atomIndex = 1) :
    elementaryValueFloor size rank ≤ value := by
  have hrankPos := rank_pos_of_isChartArgmaxValue hargmax
  have hsizePos : 0 < size := lt_of_lt_of_le hrankPos (rank_le_of_design design)
  exact valueFloorOfCount_le_value_of_one_le_mul hsizePos (elementaryCount_pos hrankPos)
    (one_le_elementaryCount_mul_one_add_size_mul_value_of_isChartArgmaxValue design hchart hargmax
      hrank hweightFloor hweightSum)

/-- **FLOOR-E2 against the stationarity bundle**, which is how every consumer meets it.
The bundle enters only through the weight floor and the weight sum. -/
theorem elementaryValueFloor_le_value_of_isChartStationaryData
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value) (hrank : 2 ≤ rank)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    elementaryValueFloor size rank ≤ value :=
  elementaryValueFloor_le_value_of_isChartArgmaxValue design hchart hargmax hrank
    (weight_ge_neg_value_of_isChartStationaryData hdata) hdata.weight_sum_one

/-- **THE COMBINED FLOOR**, carrying NO hypothesis on the rank.  At `rank ≥ 2` the
smaller of the two counts is used and the corresponding mass inequality supplies it; at
`rank = 1` the two counts are both one, the floor is `0`, and FLOOR-CB proves it;
`rank = 0` never arises, because admissibility is unsatisfiable there.  So the kernel
carries one floor at least as good as either parent at every cell, with no cell
excluded at either edge. -/
theorem combinedValueFloor_le_value_of_isChartArgmaxValue
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hweightFloor : ∀ atomIndex : Fin size, -value ≤ weight atomIndex)
    (hweightSum : ∑ atomIndex : Fin size, weight atomIndex = 1) :
    combinedValueFloor size rank ≤ value := by
  have hrankPos := rank_pos_of_isChartArgmaxValue hargmax
  have hrankLe := rank_le_of_design design
  have hsizePos : 0 < size := lt_of_lt_of_le hrankPos hrankLe
  have hcauchyBinetMass := one_le_choose_mul_one_add_size_mul_value_of_isChartArgmaxValue design
    hchart hargmax hweightFloor hweightSum
  refine valueFloorOfCount_le_value_of_one_le_mul hsizePos
    (combinedCount_pos hrankPos hrankLe) ?_
  rcases Nat.lt_or_ge rank 2 with hsmall | hbig
  · have hcount : combinedCount size rank = (size - 1).choose (rank - 1) := by
      have hrankOne : rank = 1 := by omega
      simp [combinedCount, elementaryCount, hrankOne]
    rw [hcount]
    exact hcauchyBinetMass
  · have helementaryMass := one_le_elementaryCount_mul_one_add_size_mul_value_of_isChartArgmaxValue
      design hchart hargmax hbig hweightFloor hweightSum
    rcases Nat.le_total ((size - 1).choose (rank - 1)) (elementaryCount size rank) with
      hbinomialLe | helementaryLe
    · rw [combinedCount, Nat.min_eq_left hbinomialLe]
      exact hcauchyBinetMass
    · rw [combinedCount, Nat.min_eq_right helementaryLe]
      exact helementaryMass

/-- **The combined floor against the stationarity bundle.** -/
theorem combinedValueFloor_le_value_of_isChartStationaryData
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    combinedValueFloor size rank ≤ value :=
  combinedValueFloor_le_value_of_isChartArgmaxValue design hchart hargmax
    (weight_ge_neg_value_of_isChartStationaryData hdata) hdata.weight_sum_one

end Floor

/-! ## The supersession, and the crossover between the two counts -/

/-- The combined floor is at least the Cauchy–Binet floor at every cell. -/
theorem cauchyBinetValueFloor_le_combinedValueFloor {size rank : ℕ} (hrank : 0 < rank)
    (hrankLe : rank ≤ size) : cauchyBinetValueFloor size rank ≤ combinedValueFloor size rank :=
  valueFloorOfCount_le_valueFloorOfCount_of_count_le (combinedCount_pos hrank hrankLe)
    (min_le_left _ _)

/-- The combined floor is at least the elementary floor at every cell. -/
theorem elementaryValueFloor_le_combinedValueFloor {size rank : ℕ} (hrank : 0 < rank)
    (hrankLe : rank ≤ size) : elementaryValueFloor size rank ≤ combinedValueFloor size rank :=
  valueFloorOfCount_le_valueFloorOfCount_of_count_le (combinedCount_pos hrank hrankLe)
    (min_le_right _ _)

/-- **THE CROSSOVER, AT `(6,3)`**: the E2 count is `9` and the binomial is `10`, so E2
wins — and `(6,3)` is the first open cell.  Arithmetic about two numerals. -/
theorem elementaryCount_lt_choose_sixThree :
    elementaryCount 6 3 < (6 - 1).choose (3 - 1) := by
  norm_num [elementaryCount, Nat.choose]

/-- **THE CROSSOVER, ONE CELL EARLIER**: at `(5,3)` the E2 count is `7` and the
binomial is `6`, so the binomial still wins.  Together with the previous theorem, the
comparison between the two counts changes sign between `(5,3)` and `(6,3)`; that it
never changes back at rank three is arithmetic not stated here. -/
theorem choose_lt_elementaryCount_fiveThree :
    (5 - 1).choose (3 - 1) < elementaryCount 5 3 := by
  norm_num [elementaryCount, Nat.choose]

/-! ## The floor at the cells where it has been asked for -/

theorem elementaryCount_sixThree : elementaryCount 6 3 = 9 := by norm_num [elementaryCount]

theorem elementaryCount_sevenThree : elementaryCount 7 3 = 11 := by norm_num [elementaryCount]

theorem elementaryValueFloor_sixThree : elementaryValueFloor 6 3 = -(4 / 27) := by
  rw [elementaryValueFloor, valueFloorOfCount, elementaryCount_sixThree]
  norm_num

theorem elementaryValueFloor_sevenThree : elementaryValueFloor 7 3 = -(10 / 77) := by
  rw [elementaryValueFloor, valueFloorOfCount, elementaryCount_sevenThree]
  norm_num

theorem combinedCount_sixThree : combinedCount 6 3 = 9 := by
  norm_num [combinedCount, elementaryCount, Nat.choose]

theorem combinedCount_sevenThree : combinedCount 7 3 = 11 := by
  norm_num [combinedCount, elementaryCount, Nat.choose]

theorem combinedValueFloor_sixThree : combinedValueFloor 6 3 = -(4 / 27) := by
  rw [combinedValueFloor, valueFloorOfCount, combinedCount_sixThree]
  norm_num

theorem combinedValueFloor_sevenThree : combinedValueFloor 7 3 = -(10 / 77) := by
  rw [combinedValueFloor, valueFloorOfCount, combinedCount_sevenThree]
  norm_num

section Cells

variable {size rank : ℕ} {activeIndex : Type*} {projection : Matrix (Fin size) (Fin size) ℝ}
  {weight : Fin size → ℝ} {value : ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin size → ℝ)}

/-- **The floor at `(6,3)`**, the first open cell: `-4/27 ≤ value`, against FLOOR-CB's
`-3/20`.  The window on the negative axis narrows from `(-1/6, 0)` to `[-4/27, 0)`. -/
theorem neg_four_div_twentySeven_le_value_of_isChartStationaryData
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hsize : size = 6) (hrank : rank = 3) :
    -(4 / 27 : ℝ) ≤ value := by
  have hfloor := combinedValueFloor_le_value_of_isChartStationaryData design hchart hargmax hdata
  rwa [hsize, hrank, combinedValueFloor_sixThree] at hfloor

/-- **The floor at `(7,3)`**, the other open cell: `-10/77 ≤ value`, against FLOOR-CB's
`-2/15`. -/
theorem neg_ten_div_seventySeven_le_value_of_isChartStationaryData
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hsize : size = 7) (hrank : rank = 3) :
    -(10 / 77 : ℝ) ≤ value := by
  have hfloor := combinedValueFloor_le_value_of_isChartStationaryData design hchart hargmax hdata
  rwa [hsize, hrank, combinedValueFloor_sevenThree] at hfloor

end Cells

/-! ## C8-a: the two-block eliminant on the tightened window

`Gtz.twoBlockEliminantCubic_eq_handelmanCombination` decomposes `27 E` positively over
`[-3/20, 0]`.  The same shape over `[-4/27, 0]` is below.  Nothing here closes a class:
the class arc's numeric hypothesis was already discharged at `-3/20`, so what follows
is margin on an interval that has already been shown to contain no root, plus the
record of why the ORIGINAL `-1/size` interval does contain one. -/

/-- **THE TIGHTENED HANDELMAN CERTIFICATE** — an exact identity over the rationals,

    `64 E(g) = 18603 (-g)^3 + 196101 (g + 4/27)(-g)^2`
              `+ 269001 (g + 4/27)^2 (-g) + 98415 (g + 4/27)^3` ,

all four coefficients strictly positive integers.  This is the degree-three Handelman
decomposition of `E` in the Bernstein basis of `[-4/27, 0]`, whose two generators are
`-g ≥ 0` and `g + 4/27 ≥ 0`; the Bernstein coefficients are
`(689/729, 269/81, 41/9, 5)` and the factor `19683/64 = (27/4)^3` between them and the
integers above is the cube of the interval's reciprocal length.

Proved by ring normalisation, which is the whole point of a certificate: the
verification is an identity check and does not re-run the search that found it. -/
theorem twoBlockEliminantCubic_eq_tightenedHandelmanCombination (value : ℝ) :
    64 * twoBlockEliminantCubic value
      = 18603 * (-value) ^ 3 + 196101 * (value + 4 / 27) * (-value) ^ 2
        + 269001 * (value + 4 / 27) ^ 2 * (-value) + 98415 * (value + 4 / 27) ^ 3 := by
  unfold twoBlockEliminantCubic
  ring

/-- **The eliminant is nonnegative on the E2 window**, straight off the tightened
certificate: on `-4/27 ≤ g ≤ 0` both generators are nonnegative, so all four terms of
the identity are, and no case analysis is needed anywhere. -/
theorem twoBlockEliminantCubic_nonneg_of_mem_tightenedWindow (value : ℝ)
    (hfloor : -(4 / 27 : ℝ) ≤ value) (hceiling : value ≤ 0) :
    0 ≤ twoBlockEliminantCubic value := by
  have hdescending : (0 : ℝ) ≤ -value := by linarith
  have hascending : (0 : ℝ) ≤ value + 4 / 27 := by linarith
  have hcombination := twoBlockEliminantCubic_eq_tightenedHandelmanCombination value
  have hcube : (0 : ℝ) ≤ (-value) ^ 3 := pow_nonneg hdescending 3
  have hmixedFirst : (0 : ℝ) ≤ (value + 4 / 27) * (-value) ^ 2 :=
    mul_nonneg hascending (pow_nonneg hdescending 2)
  have hmixedSecond : (0 : ℝ) ≤ (value + 4 / 27) ^ 2 * (-value) :=
    mul_nonneg (pow_nonneg hascending 2) hdescending
  have hcubeAscending : (0 : ℝ) ≤ (value + 4 / 27) ^ 3 := pow_nonneg hascending 3
  linarith

/-- **The tightened margin identity**:
`E(g) - 689/729 = (g + 4/27)(108 g^2 - 124 g + 739/27)`.  The right factor is positive
wherever `g ≤ 0` and the left one is nonnegative wherever `g ≥ -4/27`, so `689/729` is
a LOWER BOUND on the window rather than merely a value.  It is also attained, at
`g = -4/27`, which is why no better constant is available from this window. -/
theorem twoBlockEliminantCubic_sub_tightenedMargin_eq_prod (value : ℝ) :
    twoBlockEliminantCubic value - 689 / 729
      = (value + 4 / 27) * (108 * value ^ 2 - 124 * value + 739 / 27) := by
  unfold twoBlockEliminantCubic
  ring

/-- **THE TIGHTENED MARGIN**: `689/729 ≤ E(g)` for `-4/27 ≤ g ≤ 0`.  The left-endpoint
value of the eliminant improves from `E(-3/20) = 1711/2000 = 0.8555` on the
Cauchy–Binet window to `E(-4/27) = 689/729 = 0.94513` on this one. -/
theorem tightenedHandelmanMargin_le_twoBlockEliminantCubic (value : ℝ)
    (hfloor : -(4 / 27 : ℝ) ≤ value) (hceiling : value ≤ 0) :
    (689 / 729 : ℝ) ≤ twoBlockEliminantCubic value := by
  have hascending : (0 : ℝ) ≤ value + 4 / 27 := by linarith
  have hquadratic : (0 : ℝ) ≤ 108 * value ^ 2 - 124 * value + 739 / 27 := by
    nlinarith [sq_nonneg value]
  have hmargin := twoBlockEliminantCubic_sub_tightenedMargin_eq_prod value
  nlinarith [mul_nonneg hascending hquadratic]

/-- **The eliminant is strictly positive on the E2 window.** -/
theorem twoBlockEliminantCubic_pos_of_mem_tightenedWindow (value : ℝ)
    (hfloor : -(4 / 27 : ℝ) ≤ value) (hceiling : value ≤ 0) :
    0 < twoBlockEliminantCubic value := by
  have hmargin := tightenedHandelmanMargin_le_twoBlockEliminantCubic value hfloor hceiling
  linarith

/-- **The E2 window contains no root of the eliminant**, in the form the class arc
consumes it. -/
theorem twoBlockEliminantCubic_ne_zero_of_tightenedNegativeValue (value : ℝ)
    (hfloor : -(4 / 27 : ℝ) ≤ value) (hnegative : value < 0) :
    twoBlockEliminantCubic value ≠ 0 :=
  ne_of_gt (twoBlockEliminantCubic_pos_of_mem_tightenedWindow value hfloor hnegative.le)

/-- **The eliminant VANISHES at `-1/6`.**  Carried forward from
`Gtz.twoBlockEliminantCubic_eq_zero_iff` as the reason the floor is load-bearing: the
shipped `-1/size` window at `size = 6` has a root of the eliminant at its endpoint. -/
theorem twoBlockEliminantCubic_neg_inv_six_eq_zero :
    twoBlockEliminantCubic (-(1 / 6 : ℝ)) = 0 := by
  unfold twoBlockEliminantCubic
  norm_num

/-- **The eliminant's unique negative root is NOT in the E2 window.**  `-1/6 < -4/27`,
so the improvement of the floor from `-1/size` is what makes any interval certificate
possible at all, and the E2 constant clears the root by more than the Cauchy–Binet one
does. -/
theorem not_tightenedWindow_neg_inv_six : ¬ (-(4 / 27 : ℝ) ≤ -(1 / 6 : ℝ)) := by
  norm_num

/-- **The E2 window sits strictly inside the Cauchy–Binet one**, so every statement
proved on the wider window holds on this one and the tightening adds margin rather than
reach. -/
theorem neg_three_div_twenty_lt_neg_four_div_twentySeven :
    -(3 / 20 : ℝ) < -(4 / 27 : ℝ) := by norm_num

end Gtz
