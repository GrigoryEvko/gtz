/-
# V3 — the principal-minor sums of a scaled projection, and the U6 weight identities

`Gtz.sum_det_principalMinors_eq_sum_prod_eigenvalues`
(`Gtz/Quantitative/ElementaryValueFloor.lean`) reads the sum of the `level`-sized
principal minors of a Hermitian matrix as the `level`-th elementary symmetric
function of its spectrum.  This file turns that dictionary into closed numbers on
the objects the `(6,3)` and `(7,3)` frontiers are made of, and then descends to the
scalar identities a covering argument actually pigeonholes on.

## 1.  The dictionary on an arbitrary principal block

`sum_det_principalMinors_compression_eq_sum_prod_eigenvalues` is the shipped
identity read on `Gamma[B]` rather than on `Gamma`: for any selector `pick` the
`level`-subsets of the selected slots contribute their determinants, and the total
is `e_level` of the spectrum of the compression.  No injectivity, no rank, no size
relation — `Matrix.submatrix_submatrix` is the whole proof.

## 2.  The closed form on a scaled projection

The design-side object is not an arbitrary Hermitian matrix.  At a uniform share
`s` the direction Gram satisfies `Gamma * Gamma = s⁻¹ • Gamma`
(`directionGramMatrix_sq_of_uniformShare`), so every eigenvalue is `0` or `s⁻¹`,
the trace `m` forces exactly `m s = k` of them to be `s⁻¹`, and therefore

    `Σ_{|T| = level} det Gamma[T] = C(k, level) · s^(-level)` .

That is `sum_det_principalMinors_directionGramMatrix_of_uniformShare`, and it is
generic in size, rank AND level.  At the equal-share `(6,3)` stratum `s = 1/2` and
the levels `1, 2, 3` read `6`, `12`, `8`; at the equal-share `(7,3)` stratum
`s = 3/7` and the same levels read `7`, `49/3`, `343/27` — the `(7,3)` workflow's own
constants, available from the same theorem rather than from a second derivation
(`sum_det_principalMinors_directionGramMatrix_sixThree` and `…_sevenThree`).  Level `k+1`
returns `C(k, k+1) = 0`, and since every principal minor of a positive
semidefinite matrix is nonnegative, EVERY `(k+1)`-subset determinant vanishes
individually (`det_directionGramMatrix_submatrix_eq_zero_of_uniformShare`).  That
degeneracy is what pins the quartic coefficient of the four-set spectral law below.

The abstract twin runs on `1 + M` for a hollow symmetric involution `M`
(`IsHollowInvolution.sum_det_principalMinors_one_add`), with no design, no
realizability and no `(-1,1)` hypothesis, exactly as U6 does.

## 3.  The two vanishing laws, and why no block algebra is needed

The pen derives the four-set identity from the `4`–`2` block relations and a
spectral count.  Neither is necessary.  Both halves of every instance come from the
row law `Σ_d M_cd² = 1` and the supply chain `Σ_d M_pd M_dq = 0`, which are the
diagonal and off-diagonal entries of `M M = 1`:

* `sum_vertexTripleProduct_eq_zero`: `Σ_{x,y} M_vx M_vy M_xy = 0` at EVERY vertex,
  because the inner sum is the `(v,x)` entry of `M M`.  Unordered, that is
  `Σ_{T ∋ v} P_T = 0`.
* `sum_pairTripleProduct_eq_zero`: `Σ_z M_pq M_pz M_zq = 0` on every pair.
* Summing the first over all vertices gives `Σ_T P_T = 0` over the whole design
  (`sum_tripleProduct_ordered_eq_zero`), at arbitrary size.

Inclusion–exclusion over `{p,q}` then gives the four-set product sum, and the same
inclusion–exclusion on the row law gives the four-set pair mass `1 + w_pq`.  So the
whole V3 layer is elementary: no determinant identity, no characteristic polynomial,
no block relation.  Neither the `3-3` mirror nor either block trace law of
`Gtz.Quantitative.EqualShareSixThreeMargin` is used anywhere below — that module is
imported for two enumeration helpers only (`Gtz.injective_three_of_ne` and
`Gtz.IsHollowInvolution.ne_of_bijective_six`), as `Gtz.Quantitative.MirrorLaw` is
imported for `Gtz.sum_eq_of_bijective_six`.

REACH, stated honestly.  Sections 7 to 11 are `Fin 6` statements and stay there: they
consume `M M = 1`, which holds only at `m = 2k`.  What transports to `(7,3)` is section
2, whose closed form is level-, rank- and size-generic and needs no involution.

## 4.  What the frontier agent gets

Explicit, index-named forms at the three sizes, each with its pigeonhole:

| block | `Σ w` over its pairs | `Σ P` over its triples | `Σ det Gamma[T]` | some triple |
|---|---|---|---|---|
| four-set `F`, complement `{p,q}` | `1 + w_pq` | `0` | `2 (1 - w_pq)` | `≥ (1 - w_pq)/2` |
| five-set | `2` | `0` | `4` | `≥ 2/5` |
| the whole six | `3` | `0` | `8` | `≥ 2/5` |

together with the U6 weight identities `Σ_T sigma_T = 12` over the twenty triples
and `Σ_{T ∋ c} sigma_T = 6` over the ten through any atom.  The per-vertex constant
is `6`, not the `5` an earlier pass recorded: each of the five edges at `c` lies in
FOUR of the ten triples, contributing `4 · 1`, and the ten edges avoiding `c`
contribute their total `3 - 1 = 2`.

## 5.  The four-set spectral law

`IsHollowInvolution.det_smul_one_sub_submatrix_four` states, for every four-set of a
hollow symmetric involution on `Fin 6` with complementary pair `{p,q}`,

    `det (x · 1 - M[F]) = (x² - 1)(x² - M_pq²)` ,

i.e. `spec M[F] = {1, -1, +M_pq, -M_pq}` written without spectra.  The campaign once
recorded a SINGLE `± gamma` here; the icosahedron refutes that reading, and the
corrected law is witnessed in the kernel against `Gtz.icosaDesign` in section 13,
where the four-set `{0,1,2,3}` has characteristic polynomial `(x² - 1)(x² - 1/5)`.

The proof needs no eigenvalues.  Expanding `det (x · 1 - M[F])` at a constant-diagonal
symmetric `4 x 4` gives four coefficients: the cubic one is the vanishing trace, the
quadratic one is the four-set pair mass `1 + w_pq` of section 7, the linear one is
twice the four-set product sum of section 8, already zero, and the constant one is
pinned by evaluating at `x = -1`, where the block is `-(1 + M[F])` and the determinant
is the vanishing four-block minor of `Gamma` from section 4.  (`1 - M` gives the same
vanishing by `IsHollowInvolution.det_one_sub_submatrix_eq_zero`; one of the two
suffices, and only `1 + M` is consumed.)
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.Quantitative.ElementaryValueFloor
import Gtz.Quantitative.EqualShareSixThreeMargin
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.WeightProductFloor

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {size selSize m k : ℕ}

/-! ## 1. The spectral dictionary on an arbitrary principal block -/

/-- **THE MINOR-SUM DICTIONARY ON A BLOCK.**  The shipped
`Gtz.sum_det_principalMinors_eq_sum_prod_eigenvalues` reads the `level`-sized
principal minors of a whole Hermitian matrix; this is the same statement read on the
compression along an arbitrary selector, which is the form a subset argument needs.
`Matrix.submatrix_submatrix` is the entire proof: a principal minor of a principal
block IS a principal minor of the original matrix, indexed through the selector.
Neither injectivity of the selector nor any relation between the two sizes is
assumed. -/
theorem sum_det_principalMinors_compression_eq_sum_prod_eigenvalues
    {form : Matrix (Fin size) (Fin size) ℝ} (pick : Fin selSize → Fin size)
    (hHermitian : (form.submatrix pick pick).IsHermitian)
    (level : ℕ) (hlevel : level ≤ selSize) :
    ∑ selected ∈ (Finset.univ : Finset (Fin selSize)).powersetCard level,
        (form.submatrix (fun slot : { index // index ∈ selected } => pick slot.val)
          (fun slot : { index // index ∈ selected } => pick slot.val)).det
      = ∑ selected ∈ (Finset.univ : Finset (Fin selSize)).powersetCard level,
          ∏ eigenIndex ∈ selected, hHermitian.eigenvalues eigenIndex := by
  rw [← sum_det_principalMinors_eq_sum_prod_eigenvalues hHermitian level hlevel]
  exact Finset.sum_congr rfl fun selected _ => by rw [Matrix.submatrix_submatrix]; rfl

/-- **THE SUBTYPE-TO-TUPLE TRANSFER.**  The principal minors of `sum_det_principalMinors_*`
are indexed by subtypes of a `Finset`; every consumer wants them indexed by an explicit
tuple.  An injective selector enumerates its own image, so the two determinants agree —
`Matrix.det_submatrix_equiv_self` along the enumeration.  This is what lets the closed
form of section 2 be read at named indices. -/
theorem det_submatrix_subtype_image_eq_det_submatrix (form : Matrix (Fin size) (Fin size) ℝ)
    {pick : Fin selSize → Fin size} (hinjective : Function.Injective pick) :
    (form.submatrix
        (Subtype.val : { index // index ∈ Finset.image pick Finset.univ } → Fin size)
        (Subtype.val : { index // index ∈ Finset.image pick Finset.univ } → Fin size)).det
      = (form.submatrix pick pick).det := by
  classical
  have hmember : ∀ slot : Fin selSize, pick slot ∈ Finset.image pick Finset.univ :=
    fun slot => Finset.mem_image_of_mem pick (Finset.mem_univ slot)
  refine (Matrix.det_submatrix_equiv_self
    (Equiv.ofBijective (fun slot : Fin selSize => (⟨pick slot, hmember slot⟩ :
        { index // index ∈ Finset.image pick Finset.univ }))
      ⟨fun leftSlot rightSlot hvalue => hinjective (congrArg Subtype.val hvalue), fun target => by
        obtain ⟨slot, _, hslot⟩ := Finset.mem_image.mp target.2
        exact ⟨slot, Subtype.ext hslot⟩⟩) _).symm.trans ?_
  rw [Matrix.submatrix_submatrix]
  rfl

/-- An injective selector's image has the selector's own cardinality, so it is one of
the `selSize`-subsets the closed form sums over. -/
theorem image_mem_powersetCard_of_injective {pick : Fin selSize → Fin size}
    (hinjective : Function.Injective pick) :
    Finset.image pick Finset.univ
      ∈ (Finset.univ : Finset (Fin size)).powersetCard selSize := by
  classical
  refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
  rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]

/-! ## 2. The closed form on a scaled projection

`form * form = scaleValue • form` is the only structural hypothesis: it says
`form / scaleValue` is an idempotent, so the spectrum is two-valued and the trace
counts the multiplicity. -/

/-- **A SCALED IDEMPOTENT HAS A TWO-VALUED SPECTRUM.**  If `form * form =
scaleValue • form` then every eigenvalue is `0` or `scaleValue`, by applying the
matrix twice to an eigenvector. -/
theorem eigenvalues_eq_zero_or_eq_of_sq_eq_smul {form : Matrix (Fin size) (Fin size) ℝ}
    {scaleValue : ℝ} (hHermitian : form.IsHermitian)
    (hsquare : form * form = scaleValue • form) (index : Fin size) :
    hHermitian.eigenvalues index = 0 ∨ hHermitian.eigenvalues index = scaleValue := by
  classical
  set eigenvector : Fin size → ℝ := ⇑(hHermitian.eigenvectorBasis index) with heigenvector
  have hnonzero : eigenvector ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 <| hHermitian.eigenvectorBasis.orthonormal.ne_zero index
  have hstep : form *ᵥ eigenvector = hHermitian.eigenvalues index • eigenvector :=
    hHermitian.mulVec_eigenvectorBasis index
  have htwice : (hHermitian.eigenvalues index ^ 2) • eigenvector
      = (scaleValue * hHermitian.eigenvalues index) • eigenvector := by
    calc (hHermitian.eigenvalues index ^ 2) • eigenvector
        = form *ᵥ (form *ᵥ eigenvector) := by
          rw [hstep, Matrix.mulVec_smul, hstep, smul_smul, ← pow_two]
      _ = (form * form) *ᵥ eigenvector := by rw [Matrix.mulVec_mulVec]
      _ = (scaleValue • form) *ᵥ eigenvector := by rw [hsquare]
      _ = (scaleValue * hHermitian.eigenvalues index) • eigenvector := by
          rw [Matrix.smul_mulVec, hstep, smul_smul]
  have hscalar : hHermitian.eigenvalues index ^ 2
      - scaleValue * hHermitian.eigenvalues index = 0 := by
    by_contra hcontra
    refine hnonzero ?_
    have hdifference := sub_eq_zero_of_eq htwice
    rw [← sub_smul] at hdifference
    rcases smul_eq_zero.mp hdifference with hcoefficient | hvector
    · exact absurd hcoefficient hcontra
    · exact hvector
  rcases mul_eq_zero.mp (by linear_combination hscalar :
      hHermitian.eigenvalues index * (hHermitian.eigenvalues index - scaleValue) = 0) with
    hzero | hshifted
  · exact Or.inl hzero
  · exact Or.inr (by linarith [sub_eq_zero.mp hshifted])

/-- **THE MULTIPLICITY IS THE TRACE, DIVIDED.**  A scaled idempotent whose trace is
`rankCount * scaleValue` has exactly `rankCount` eigenvalues equal to `scaleValue`;
the rest are zero. -/
theorem card_eigenvalues_eq_of_sq_eq_smul {form : Matrix (Fin size) (Fin size) ℝ}
    {scaleValue : ℝ} (hHermitian : form.IsHermitian)
    (hsquare : form * form = scaleValue • form) (hscaleNonzero : scaleValue ≠ 0)
    {rankCount : ℕ} (htrace : (rankCount : ℝ) * scaleValue = Matrix.trace form) :
    (Finset.univ.filter fun index => hHermitian.eigenvalues index = scaleValue).card
      = rankCount := by
  classical
  have hspectralTrace : Matrix.trace form = ∑ index, hHermitian.eigenvalues index := by
    exact_mod_cast hHermitian.trace_eq_sum_eigenvalues
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin size))
    (fun index => hHermitian.eigenvalues index = scaleValue)
    (fun index => hHermitian.eigenvalues index)
  have hpositivePart : ∑ index ∈ Finset.univ.filter
        (fun index => hHermitian.eigenvalues index = scaleValue),
        hHermitian.eigenvalues index
      = ((Finset.univ.filter
          (fun index => hHermitian.eigenvalues index = scaleValue)).card : ℝ) * scaleValue := by
    rw [Finset.sum_congr rfl fun index hmember => (Finset.mem_filter.mp hmember).2,
      Finset.sum_const, nsmul_eq_mul]
  have hzeroPart : ∑ index ∈ Finset.univ.filter
        (fun index => ¬ hHermitian.eigenvalues index = scaleValue),
        hHermitian.eigenvalues index = 0 := by
    refine Finset.sum_eq_zero fun index hmember => ?_
    exact (eigenvalues_eq_zero_or_eq_of_sq_eq_smul hHermitian hsquare index).resolve_right
      (Finset.mem_filter.mp hmember).2
  rw [hpositivePart, hzeroPart, add_zero, ← hspectralTrace, ← htrace] at hsplit
  exact_mod_cast mul_right_cancel₀ hscaleNonzero hsplit

/-- **THE ELEMENTARY SYMMETRIC FUNCTION OF A TWO-VALUED FAMILY.**  A family taking
only the values `0` and `scaleValue`, with `rankCount` of the latter, has
`e_level = C(rankCount, level) · scaleValue ^ level`: the only surviving subsets are
those inside the level set, and each contributes the same power. -/
theorem sum_prod_of_eigenvalues_two_valued {rankCount : ℕ} {scaleValue : ℝ}
    (values : Fin size → ℝ)
    (htwoValued : ∀ index, values index = 0 ∨ values index = scaleValue)
    (hcard : (Finset.univ.filter fun index => values index = scaleValue).card = rankCount)
    (level : ℕ) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        ∏ index ∈ selected, values index
      = (rankCount.choose level : ℝ) * scaleValue ^ level := by
  classical
  set positiveSet : Finset (Fin size) :=
    Finset.univ.filter fun index => values index = scaleValue with hpositiveSet
  have hsubset : positiveSet.powersetCard level
      ⊆ (Finset.univ : Finset (Fin size)).powersetCard level := by
    intro selected hmember
    rw [Finset.mem_powersetCard] at hmember ⊢
    exact ⟨Finset.subset_univ _, hmember.2⟩
  have hvanish : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
      selected ∉ positiveSet.powersetCard level → ∏ index ∈ selected, values index = 0 := by
    intro selected hmember hnotInside
    rw [Finset.mem_powersetCard] at hmember
    have hnotSubset : ¬ selected ⊆ positiveSet := fun hsubsetOf =>
      hnotInside (Finset.mem_powersetCard.mpr ⟨hsubsetOf, hmember.2⟩)
    obtain ⟨witness, hwitnessMember, hwitnessOutside⟩ := Finset.not_subset.mp hnotSubset
    refine Finset.prod_eq_zero hwitnessMember ?_
    rcases htwoValued witness with hzero | hscale
    · exact hzero
    · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ witness, hscale⟩) hwitnessOutside
  have hconstant : ∀ selected ∈ positiveSet.powersetCard level,
      ∏ index ∈ selected, values index = scaleValue ^ level := by
    intro selected hmember
    rw [Finset.mem_powersetCard] at hmember
    rw [Finset.prod_congr rfl fun index hindex => (Finset.mem_filter.mp (hmember.1 hindex)).2,
      Finset.prod_const, hmember.2]
  rw [← Finset.sum_subset hsubset hvanish, Finset.sum_congr rfl hconstant, Finset.sum_const,
    Finset.card_powersetCard, hcard, nsmul_eq_mul]

/-- **THE PRINCIPAL-MINOR SUMS OF A SCALED PROJECTION.**  For a symmetric `form`
with `form * form = scaleValue • form` and trace `rankCount * scaleValue`, the total
of the `level`-sized principal minors is `C(rankCount, level) · scaleValue ^ level`.
Size, rank and level are all free; the hypothesis is one matrix equation and one
trace equation. -/
theorem sum_det_principalMinors_of_sq_eq_smul {form : Matrix (Fin size) (Fin size) ℝ}
    {scaleValue : ℝ} (hsymmetric : formᵀ = form)
    (hsquare : form * form = scaleValue • form) (hscaleNonzero : scaleValue ≠ 0)
    {rankCount : ℕ} (htrace : (rankCount : ℝ) * scaleValue = Matrix.trace form)
    (level : ℕ) (hlevel : level ≤ size) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        (form.submatrix (Subtype.val : { index // index ∈ selected } → Fin size)
          (Subtype.val : { index // index ∈ selected } → Fin size)).det
      = (rankCount.choose level : ℝ) * scaleValue ^ level := by
  have hHermitian : form.IsHermitian := isHermitian_of_transpose_eq hsymmetric
  rw [sum_det_principalMinors_eq_sum_prod_eigenvalues hHermitian level hlevel]
  exact sum_prod_of_eigenvalues_two_valued _
    (fun index => eigenvalues_eq_zero_or_eq_of_sq_eq_smul hHermitian hsquare index)
    (card_eigenvalues_eq_of_sq_eq_smul hHermitian hsquare hscaleNonzero htrace) level

/-! ## 3. The design instance: uniform share -/

/-- **THE DIRECTION GRAM IS A SCALED PROJECTION AT A UNIFORM SHARE.**  The shipped
`Gtz.directionGramMatrix_mul_diagonal_atomShare_mul_self` says
`Gamma · diag(s) · Gamma = Gamma` unconditionally; when the shares are all
`shareValue` the middle factor is a scalar and the identity becomes
`Gamma * Gamma = shareValue⁻¹ • Gamma`.  Only equality of the shares and positivity
of their common value are used — no uniform weight, no uniform leverage. -/
theorem directionGramMatrix_sq_of_uniformShare (D : WeightedDesign m k) {shareValue : ℝ}
    (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue) (hpositive : 0 < shareValue) :
    directionGramMatrix D * directionGramMatrix D = shareValue⁻¹ • directionGramMatrix D := by
  have hdiagonal : Matrix.diagonal (atomShare D)
      = shareValue • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    ext rowIndex colIndex
    rw [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs with hequal
    · rw [hequal, huniform colIndex, mul_one]
    · rw [mul_zero]
  have hproduct := directionGramMatrix_mul_diagonal_atomShare_mul_self D
  rw [hdiagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hproduct
  calc directionGramMatrix D * directionGramMatrix D
      = (shareValue⁻¹ * shareValue) • (directionGramMatrix D * directionGramMatrix D) := by
        rw [inv_mul_cancel₀ hpositive.ne', one_smul]
    _ = shareValue⁻¹ • (shareValue • (directionGramMatrix D * directionGramMatrix D)) := by
        rw [smul_smul]
    _ = shareValue⁻¹ • directionGramMatrix D := by rw [hproduct]

/-- The trace of the direction Gram is the size: every diagonal entry is `1` once
the atom is nondegenerate, and a positive share forces that. -/
theorem trace_directionGramMatrix_of_uniformShare (D : WeightedDesign m k) {shareValue : ℝ}
    (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue) (hpositive : 0 < shareValue) :
    Matrix.trace (directionGramMatrix D) = (m : ℝ) := by
  rw [Matrix.trace]
  have hdiagonal : ∀ atomIndex : Fin m, (directionGramMatrix D).diag atomIndex = 1 := by
    intro atomIndex
    rw [Matrix.diag_apply]
    exact directionGram_self D
      (leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; exact hpositive))
  rw [Finset.sum_congr rfl fun atomIndex _ => hdiagonal atomIndex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **THE V3 IDENTITY, IN ITS GENERAL FORM.**  On any weighted design whose shares
are all equal, the total of the `level`-sized principal minors of the direction Gram
is `C(k, level) · shareValue^(-level)`.  Generic in size, rank AND level.

At `(6,3)` with `shareValue = 1/2` the levels `1, 2, 3` give `6`, `12`, `8` — the
pen's twenty-triple total is the `level = 3` reading — and every level above the
rank gives `0`.  At the equal-share `(7,3)` stratum `shareValue = 3/7` and level `3`
gives `343/27`, which is the `(7,3)` workflow's analogue of the same constant. -/
theorem sum_det_principalMinors_directionGramMatrix_of_uniformShare (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hpositive : 0 < shareValue) (level : ℕ) (hlevel : level ≤ m) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard level,
        ((directionGramMatrix D).submatrix
          (Subtype.val : { index // index ∈ selected } → Fin m)
          (Subtype.val : { index // index ∈ selected } → Fin m)).det
      = (k.choose level : ℝ) * shareValue⁻¹ ^ level := by
  have hsymmetric : (directionGramMatrix D)ᵀ = directionGramMatrix D := by
    ext rowIndex colIndex
    exact directionGram_comm D colIndex rowIndex
  have hforced := size_mul_atomShare_eq_rank_of_atomShare_eq D huniform
  have htrace : (k : ℝ) * shareValue⁻¹ = Matrix.trace (directionGramMatrix D) := by
    rw [trace_directionGramMatrix_of_uniformShare D huniform hpositive, ← hforced]
    field_simp
  exact sum_det_principalMinors_of_sq_eq_smul hsymmetric
    (directionGramMatrix_sq_of_uniformShare D huniform hpositive)
    (inv_ne_zero hpositive.ne') htrace level hlevel

/-- **ABOVE THE RANK EVERY BLOCK IS SINGULAR.**  At level `k+1` the closed form is
`C(k, k+1) = 0`, and every term of the sum is a principal minor of a positive
semidefinite matrix, hence nonnegative; so each vanishes individually.  This is the
degeneracy that pins the quartic coefficient of the four-set spectral law. -/
theorem det_directionGramMatrix_submatrix_eq_zero_of_uniformShare (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hpositive : 0 < shareValue) {level : ℕ} (hlevel : level ≤ m) (hexceeds : k < level)
    {selected : Finset (Fin m)}
    (hmember : selected ∈ (Finset.univ : Finset (Fin m)).powersetCard level) :
    ((directionGramMatrix D).submatrix
      (Subtype.val : { index // index ∈ selected } → Fin m)
      (Subtype.val : { index // index ∈ selected } → Fin m)).det = 0 := by
  have htotal := sum_det_principalMinors_directionGramMatrix_of_uniformShare D huniform hpositive
    level hlevel
  rw [Nat.choose_eq_zero_of_lt hexceeds] at htotal
  simp only [Nat.cast_zero, zero_mul] at htotal
  refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp htotal selected hmember
  exact fun block _ => ((posSemidef_directionGramMatrix D).submatrix _).det_nonneg

/-! ## 4. The abstract instance: a hollow symmetric involution

`1 + M` is the correlation matrix of the equal-share stratum read abstractly, and it
is a scaled projection at scale `2`.  Nothing below mentions a design, a frame, or
realizability — the same reach the U6 theorem has. -/

namespace IsHollowInvolution

variable {invol : Matrix (Fin size) (Fin size) ℝ}

/-- `1 + M` is a scaled idempotent at scale `2`: `(1 + M)² = 2 + 2M`. -/
theorem sq_one_add (hinvol : IsHollowInvolution invol) :
    ((1 : Matrix (Fin size) (Fin size) ℝ) + invol) * ((1 : Matrix (Fin size) (Fin size) ℝ) + invol)
      = (2 : ℝ) • ((1 : Matrix (Fin size) (Fin size) ℝ) + invol) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hinvol.square_eq_one]
  ext rowIndex colIndex
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> ring

/-- The trace of `1 + M` is the size, because `M` is hollow. -/
theorem trace_one_add (hinvol : IsHollowInvolution invol) :
    Matrix.trace ((1 : Matrix (Fin size) (Fin size) ℝ) + invol) = (size : ℝ) := by
  rw [Matrix.trace_add, Matrix.trace_one, hinvol.trace_eq_zero, add_zero, Fintype.card_fin]

/-- **THE V3 IDENTITY ON THE ABSTRACT OBJECT.**  For a hollow symmetric involution on
`Fin (2 · rankCount)` the total of the `level`-sized principal minors of `1 + M` is
`C(rankCount, level) · 2 ^ level`.  At `size = 6` — so `rankCount = 3` — the levels
`1, 2, 3` read `6`, `12`, `8`; the last is the pen's twenty-triple total
`Σ_T det Gamma[T] = 8`, with no design and no realizability hypothesis. -/
theorem sum_det_principalMinors_one_add (hinvol : IsHollowInvolution invol)
    {rankCount : ℕ} (hsize : size = 2 * rankCount) (level : ℕ) (hlevel : level ≤ size) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        (((1 : Matrix (Fin size) (Fin size) ℝ) + invol).submatrix
          (Subtype.val : { index // index ∈ selected } → Fin size)
          (Subtype.val : { index // index ∈ selected } → Fin size)).det
      = (rankCount.choose level : ℝ) * 2 ^ level := by
  have hsymmetric : ((1 : Matrix (Fin size) (Fin size) ℝ) + invol)ᵀ = 1 + invol := by
    rw [Matrix.transpose_add, Matrix.transpose_one, hinvol.symmetric]
  have htrace : (rankCount : ℝ) * 2
      = Matrix.trace ((1 : Matrix (Fin size) (Fin size) ℝ) + invol) := by
    rw [hinvol.trace_one_add, hsize]
    push_cast
    ring
  exact sum_det_principalMinors_of_sq_eq_smul hsymmetric hinvol.sq_one_add (by norm_num)
    htrace level hlevel

/-- **ABOVE HALF THE SIZE EVERY BLOCK OF `1 + M` IS SINGULAR.**  `1 + M` is positive
semidefinite (`Gtz.IsHollowInvolution.posSemidef_one_add`) and its level-`rankCount+1`
minor total is `C(rankCount, rankCount+1) = 0`, so each such minor vanishes on its own.
Stated at an explicit injective selector rather than at a subtype, which is the form
the four-set spectral law consumes. -/
theorem det_one_add_submatrix_eq_zero (hinvol : IsHollowInvolution invol)
    {rankCount : ℕ} (hsize : size = 2 * rankCount) (hexceeds : rankCount < selSize)
    (hlevel : selSize ≤ size) {pick : Fin selSize → Fin size}
    (hinjective : Function.Injective pick) :
    (((1 : Matrix (Fin size) (Fin size) ℝ) + invol).submatrix pick pick).det = 0 := by
  classical
  have htotal := hinvol.sum_det_principalMinors_one_add hsize selSize hlevel
  rw [Nat.choose_eq_zero_of_lt hexceeds] at htotal
  simp only [Nat.cast_zero, zero_mul] at htotal
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun block _ => (hinvol.posSemidef_one_add.submatrix _).det_nonneg)).mp htotal
    (Finset.image pick Finset.univ) (image_mem_powersetCard_of_injective hinjective)
  rwa [det_submatrix_subtype_image_eq_det_submatrix _ hinjective] at hterm

/-- The same for `1 - M`, since `-M` is a hollow symmetric involution too. -/
theorem det_one_sub_submatrix_eq_zero (hinvol : IsHollowInvolution invol)
    {rankCount : ℕ} (hsize : size = 2 * rankCount) (hexceeds : rankCount < selSize)
    (hlevel : selSize ≤ size) {pick : Fin selSize → Fin size}
    (hinjective : Function.Injective pick) :
    (((1 : Matrix (Fin size) (Fin size) ℝ) - invol).submatrix pick pick).det = 0 := by
  have hnegative := hinvol.neg.det_one_add_submatrix_eq_zero hsize hexceeds hlevel hinjective
  rwa [show (1 : Matrix (Fin size) (Fin size) ℝ) + -invol = 1 - invol
    from (sub_eq_add_neg _ _).symm] at hnegative

end IsHollowInvolution

/-! ## 5. The vanishing laws, in ordered form

Everything the four-, five- and six-set identities need about products of three
entries is already in `M M = 1`.  These three statements are size-generic and carry
no distinctness hypothesis: hollowness makes the degenerate terms vanish by
themselves. -/

namespace IsHollowInvolution

variable {invol : Matrix (Fin size) (Fin size) ℝ}

/-- **THE SUPPLY CHAIN, un-erased.**  `Σ_z M_pz M_zq = 0` for distinct `p, q` — the
off-diagonal entry of `M M = 1` with nothing removed.  The shipped
`Gtz.IsHollowInvolution.sum_sdiff_pair_mul` is this statement with the two hollow
terms deleted; for a triple sum the un-erased form is the convenient one. -/
theorem sum_pair_mul_eq_zero (hinvol : IsHollowInvolution invol) {firstIndex secondIndex : Fin size}
    (hdistinct : firstIndex ≠ secondIndex) :
    ∑ third, invol firstIndex third * invol third secondIndex = 0 := by
  have hentry := congrFun (congrFun hinvol.square_eq_one firstIndex) secondIndex
  rwa [Matrix.mul_apply, Matrix.one_apply_ne hdistinct] at hentry

/-- **THE TRIPLES THROUGH A PAIR CANCEL.**  `Σ_z P_{p q z} = 0` on every pair, because
the inner factor is the supply chain.  Unordered, this is `Σ_{T ⊇ {p,q}} P_T = 0`. -/
theorem sum_pairTripleProduct_eq_zero (hinvol : IsHollowInvolution invol)
    {firstIndex secondIndex : Fin size} (hdistinct : firstIndex ≠ secondIndex) :
    ∑ third, invol firstIndex secondIndex * invol firstIndex third * invol secondIndex third
      = 0 := by
  have hchain := hinvol.sum_pair_mul_eq_zero hdistinct
  rw [← mul_zero (invol firstIndex secondIndex), ← hchain, Finset.mul_sum]
  exact Finset.sum_congr rfl fun third _ => by rw [hinvol.apply_comm third secondIndex]; ring

/-- **THE TRIPLES THROUGH A VERTEX CANCEL.**  `Σ_{x,y} M_vx M_vy M_xy = 0` at every
vertex: summing over `y` first turns the inner factor into the `(v,x)` entry of
`M M = 1`, and the surviving diagonal term is `M_vv = 0`.  Unordered, this is
`Σ_{T ∋ v} P_T = 0`, and it is the whole product side of the V3 layer. -/
theorem sum_vertexTripleProduct_eq_zero (hinvol : IsHollowInvolution invol) (vertex : Fin size) :
    ∑ first, ∑ second, invol vertex first * invol vertex second * invol first second = 0 := by
  have hinner : ∀ first : Fin size,
      ∑ second, invol vertex first * invol vertex second * invol first second
        = invol vertex first * (invol * invol) vertex first := by
    intro first
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun second _ => by rw [hinvol.apply_comm first second]; ring
  rw [Finset.sum_congr rfl fun first _ => hinner first, hinvol.square_eq_one]
  simp only [Matrix.one_apply]
  rw [Finset.sum_eq_single vertex]
  · rw [hinvol.diagonal_eq_zero vertex, if_pos rfl, mul_one]
  · intro other _ hdistinct
    rw [if_neg fun hequal => hdistinct hequal.symm, mul_zero]
  · intro hnotMember
    exact absurd (Finset.mem_univ vertex) hnotMember

/-- **THE WHOLE PRODUCT SUM VANISHES.**  Summing the vertex law over all vertices
gives `Σ_{x,y,z} M_xy M_xz M_yz = 0`, which unordered is `6 · Σ_T P_T = 0` over ALL
triples, at arbitrary size.  The pen reads this at size six as `Σ_T P_T = 0`. -/
theorem sum_tripleProduct_ordered_eq_zero (hinvol : IsHollowInvolution invol) :
    ∑ first, ∑ second, ∑ third, invol first second * invol first third * invol second third = 0 :=
  Finset.sum_eq_zero fun first _ => hinvol.sum_vertexTripleProduct_eq_zero first

end IsHollowInvolution

/-! ## 6. The three scalars of a triple, abstractly

`Gtz.directionTripleSigma` and `Gtz.directionTripleProduct` are the design-level
names; `Gtz.elliptopeBracket` is the determinant of the unit-diagonal correlation
matrix.  The abstract layer had all three only inline, which makes a twenty-term
identity unreadable.  These are the same three quantities read off a bare matrix. -/

/-- `sigma_T`, the squared-entry mass of a triple. -/
noncomputable def hollowTripleSigma (invol : Matrix (Fin size) (Fin size) ℝ)
    (firstIndex secondIndex thirdIndex : Fin size) : ℝ :=
  invol firstIndex secondIndex ^ 2 + invol firstIndex thirdIndex ^ 2
    + invol secondIndex thirdIndex ^ 2

/-- `P_T`, the oriented product of a triple's three entries. -/
noncomputable def hollowTripleProduct (invol : Matrix (Fin size) (Fin size) ℝ)
    (firstIndex secondIndex thirdIndex : Fin size) : ℝ :=
  invol firstIndex secondIndex * invol firstIndex thirdIndex * invol secondIndex thirdIndex

/-- `det Gamma[T]`, the elliptope bracket of a triple's three entries. -/
noncomputable def hollowTripleBracket (invol : Matrix (Fin size) (Fin size) ℝ)
    (firstIndex secondIndex thirdIndex : Fin size) : ℝ :=
  elliptopeBracket (invol firstIndex secondIndex) (invol firstIndex thirdIndex)
    (invol secondIndex thirdIndex)

/-- The bracket in terms of the other two: `det Gamma[T] = 1 - sigma_T + 2 P_T`. -/
theorem hollowTripleBracket_eq_one_sub_sigma_add (invol : Matrix (Fin size) (Fin size) ℝ)
    (firstIndex secondIndex thirdIndex : Fin size) :
    hollowTripleBracket invol firstIndex secondIndex thirdIndex
      = 1 - hollowTripleSigma invol firstIndex secondIndex thirdIndex
        + 2 * hollowTripleProduct invol firstIndex secondIndex thirdIndex := by
  rw [hollowTripleBracket, hollowTripleSigma, hollowTripleProduct, elliptopeBracket]
  ring

/-- **THE BRACKET IS THE BLOCK DETERMINANT.**  For three distinct indices of a hollow
symmetric involution, `hollowTripleBracket` IS `det Gamma[T]` where `Gamma = 1 + M` —
so every identity below is literally a statement about principal minors of the
correlation matrix. -/
theorem IsHollowInvolution.det_one_add_submatrix_three_eq_hollowTripleBracket
    {invol : Matrix (Fin size) (Fin size) ℝ} (hinvol : IsHollowInvolution invol)
    {firstIndex secondIndex thirdIndex : Fin size} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    (((1 : Matrix (Fin size) (Fin size) ℝ) + invol).submatrix
        ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex]).det
      = hollowTripleBracket invol firstIndex secondIndex thirdIndex := by
  have hpick : Function.Injective ![firstIndex, secondIndex, thirdIndex] :=
    injective_three_of_ne hfirstSecond hfirstThird hsecondThird
  have hsplit : ((1 : Matrix (Fin size) (Fin size) ℝ) + invol).submatrix
      ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex]
      = 1 + invol.submatrix ![firstIndex, secondIndex, thirdIndex]
          ![firstIndex, secondIndex, thirdIndex] := by
    rw [show ((1 : Matrix (Fin size) (Fin size) ℝ) + invol).submatrix
        ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex]
        = (1 : Matrix (Fin size) (Fin size) ℝ).submatrix
            ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex]
          + invol.submatrix ![firstIndex, secondIndex, thirdIndex]
            ![firstIndex, secondIndex, thirdIndex] from rfl,
      Matrix.submatrix_one _ hpick]
  rw [hsplit, hinvol.submatrix_three_eq_hollowMatrixThree, one_add_hollowMatrixThree,
    det_correlationMatrixThree, hollowTripleBracket]

/-! ## 7. The pair-mass laws at size six

The row law `Σ_{d ≠ c} w_cd = 1`, summed and then cut down by inclusion–exclusion.
No block algebra, no spectrum.  The convention throughout sections 7 to 10 is one
bijective six-tuple `![first, …, sixth]`: the FOUR-set is `{first, second, third,
fourth}` with complementary pair `{fifth, sixth}`, the FIVE-set is
`{first, …, fifth}`, and the distinguished vertex is `first`.  Since the tuple is
universally quantified, relabelling it recovers every other block of the same size. -/

namespace IsHollowInvolution

variable {invol : Matrix (Fin 6) (Fin 6) ℝ}

/-- The row law expanded along the tuple: each atom's six squared entries total one. -/
theorem sum_sq_row_six (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    (vertex : Fin 6) :
    invol vertex first ^ 2 + invol vertex second ^ 2 + invol vertex third ^ 2
      + invol vertex fourth ^ 2 + invol vertex fifth ^ 2 + invol vertex sixth ^ 2 = 1 := by
  have hentry := hinvol.sum_sq_row vertex
  rwa [sum_eq_of_bijective_six hbijective fun colIndex => invol vertex colIndex ^ 2] at hentry

/-- **THE TOTAL PAIR MASS IS THE RANK.**  The fifteen squared entries of a hollow
symmetric involution on `Fin 6` total `3`: six row laws, each worth one, counted
twice over. -/
theorem sum_pairSquare_six (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    invol first second ^ 2 + invol first third ^ 2 + invol first fourth ^ 2
        + invol first fifth ^ 2 + invol first sixth ^ 2
      + invol second third ^ 2 + invol second fourth ^ 2 + invol second fifth ^ 2
        + invol second sixth ^ 2
      + invol third fourth ^ 2 + invol third fifth ^ 2 + invol third sixth ^ 2
      + invol fourth fifth ^ 2 + invol fourth sixth ^ 2
      + invol fifth sixth ^ 2 = 3 := by
  have hfirst := hinvol.sum_sq_row_six hbijective first
  have hsecond := hinvol.sum_sq_row_six hbijective second
  have hthird := hinvol.sum_sq_row_six hbijective third
  have hfourth := hinvol.sum_sq_row_six hbijective fourth
  have hfifth := hinvol.sum_sq_row_six hbijective fifth
  have hsixth := hinvol.sum_sq_row_six hbijective sixth
  simp only [hinvol.diagonal_eq_zero, hinvol.apply_comm first second,
    hinvol.apply_comm first third, hinvol.apply_comm first fourth, hinvol.apply_comm first fifth,
    hinvol.apply_comm first sixth, hinvol.apply_comm second third,
    hinvol.apply_comm second fourth, hinvol.apply_comm second fifth,
    hinvol.apply_comm second sixth, hinvol.apply_comm third fourth,
    hinvol.apply_comm third fifth, hinvol.apply_comm third sixth,
    hinvol.apply_comm fourth fifth, hinvol.apply_comm fourth sixth,
    hinvol.apply_comm fifth sixth] at hfirst hsecond hthird hfourth hfifth hsixth
  linarith

/-- **THE FIVE-SET PAIR MASS IS TWO.**  Deleting one atom removes exactly its row,
worth one. -/
theorem sum_pairSquare_fiveSet (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    invol first second ^ 2 + invol first third ^ 2 + invol first fourth ^ 2
        + invol first fifth ^ 2
      + invol second third ^ 2 + invol second fourth ^ 2 + invol second fifth ^ 2
      + invol third fourth ^ 2 + invol third fifth ^ 2
      + invol fourth fifth ^ 2 = 2 := by
  have htotal := hinvol.sum_pairSquare_six hbijective
  have hrow := hinvol.sum_sq_row_six hbijective sixth
  simp only [hinvol.diagonal_eq_zero, hinvol.apply_comm first sixth,
    hinvol.apply_comm second sixth, hinvol.apply_comm third sixth,
    hinvol.apply_comm fourth sixth, hinvol.apply_comm fifth sixth] at hrow
  linarith

/-- **THE FOUR-SET PAIR MASS IS `1 + w_pq`.**  Inclusion–exclusion over the
complementary pair: two rows removed, their shared edge restored.  This is the pen's
`Σ_{pairs in F} w = 1 + w_pq`, and it is the quadratic coefficient of the four-set
spectral law. -/
theorem sum_pairSquare_fourSet (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    invol first second ^ 2 + invol first third ^ 2 + invol first fourth ^ 2
      + invol second third ^ 2 + invol second fourth ^ 2
      + invol third fourth ^ 2 = 1 + invol fifth sixth ^ 2 := by
  have htotal := hinvol.sum_pairSquare_six hbijective
  have hfifth := hinvol.sum_sq_row_six hbijective fifth
  have hsixth := hinvol.sum_sq_row_six hbijective sixth
  simp only [hinvol.diagonal_eq_zero, hinvol.apply_comm first fifth,
    hinvol.apply_comm second fifth, hinvol.apply_comm third fifth,
    hinvol.apply_comm fourth fifth, hinvol.apply_comm first sixth,
    hinvol.apply_comm second sixth, hinvol.apply_comm third sixth,
    hinvol.apply_comm fourth sixth, hinvol.apply_comm fifth sixth] at hfifth hsixth
  linarith

/-! ## 8. The product laws at size six

`Σ_T P_T = 0` on every block.  Each instance is the ordered vanishing law of section 5
expanded along the tuple, and the four- and five-set forms are inclusion–exclusion on
top of the total. -/

/-- **THE TRIPLES THROUGH ONE ATOM CANCEL, expanded.**  For any vertex the fifteen
pair-indexed products `P_{vertex, X, Y}` total zero; the five whose pair meets the
vertex vanish term by term, so this is the pen's `Σ_{T ∋ v} P_T = 0` over the
remaining ten. -/
theorem sum_pairTripleProduct_six (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    (vertex : Fin 6) :
    hollowTripleProduct invol vertex first second + hollowTripleProduct invol vertex first third
      + hollowTripleProduct invol vertex first fourth
      + hollowTripleProduct invol vertex first fifth
      + hollowTripleProduct invol vertex first sixth
      + hollowTripleProduct invol vertex second third
      + hollowTripleProduct invol vertex second fourth
      + hollowTripleProduct invol vertex second fifth
      + hollowTripleProduct invol vertex second sixth
      + hollowTripleProduct invol vertex third fourth
      + hollowTripleProduct invol vertex third fifth
      + hollowTripleProduct invol vertex third sixth
      + hollowTripleProduct invol vertex fourth fifth
      + hollowTripleProduct invol vertex fourth sixth
      + hollowTripleProduct invol vertex fifth sixth = 0 := by
  have hzero := hinvol.sum_vertexTripleProduct_eq_zero vertex
  simp only [sum_eq_of_bijective_six hbijective, hollowTripleProduct, hinvol.diagonal_eq_zero,
    mul_zero, add_zero, zero_add, hinvol.apply_comm first second,
    hinvol.apply_comm first third, hinvol.apply_comm first fourth, hinvol.apply_comm first fifth,
    hinvol.apply_comm first sixth, hinvol.apply_comm second third,
    hinvol.apply_comm second fourth, hinvol.apply_comm second fifth,
    hinvol.apply_comm second sixth, hinvol.apply_comm third fourth,
    hinvol.apply_comm third fifth, hinvol.apply_comm third sixth,
    hinvol.apply_comm fourth fifth, hinvol.apply_comm fourth sixth,
    hinvol.apply_comm fifth sixth] at hzero ⊢
  linarith

/-- **THE TRIPLES THROUGH ONE PAIR CANCEL, expanded.**  The supply chain along the
tuple; the two terms whose third index is one of the pair vanish. -/
theorem sum_tripleProduct_throughPair (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    {leftVertex rightVertex : Fin 6} (hdistinct : leftVertex ≠ rightVertex) :
    hollowTripleProduct invol leftVertex rightVertex first
      + hollowTripleProduct invol leftVertex rightVertex second
      + hollowTripleProduct invol leftVertex rightVertex third
      + hollowTripleProduct invol leftVertex rightVertex fourth
      + hollowTripleProduct invol leftVertex rightVertex fifth
      + hollowTripleProduct invol leftVertex rightVertex sixth = 0 := by
  have hzero := hinvol.sum_pairTripleProduct_eq_zero hdistinct
  rwa [sum_eq_of_bijective_six hbijective fun third =>
    invol leftVertex rightVertex * invol leftVertex third * invol rightVertex third] at hzero

/-- **THE TWENTY-TRIPLE PRODUCT SUM VANISHES.**  The pen's `Σ_T P_T = 0` at the
equal-share `(6,3)` stratum, here for every hollow symmetric involution on `Fin 6`. -/
theorem sum_tripleProduct_six (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    hollowTripleProduct invol first second third + hollowTripleProduct invol first second fourth
      + hollowTripleProduct invol first second fifth + hollowTripleProduct invol first second sixth
      + hollowTripleProduct invol first third fourth + hollowTripleProduct invol first third fifth
      + hollowTripleProduct invol first third sixth + hollowTripleProduct invol first fourth fifth
      + hollowTripleProduct invol first fourth sixth + hollowTripleProduct invol first fifth sixth
      + hollowTripleProduct invol second third fourth + hollowTripleProduct invol second third fifth
      + hollowTripleProduct invol second third sixth
      + hollowTripleProduct invol second fourth fifth
      + hollowTripleProduct invol second fourth sixth
      + hollowTripleProduct invol second fifth sixth + hollowTripleProduct invol third fourth fifth
      + hollowTripleProduct invol third fourth sixth + hollowTripleProduct invol third fifth sixth
      + hollowTripleProduct invol fourth fifth sixth = 0 := by
  have hzero := hinvol.sum_tripleProduct_ordered_eq_zero
  simp only [sum_eq_of_bijective_six hbijective, hollowTripleProduct, hinvol.diagonal_eq_zero,
    zero_mul, mul_zero, add_zero, zero_add, hinvol.apply_comm first second,
    hinvol.apply_comm first third, hinvol.apply_comm first fourth, hinvol.apply_comm first fifth,
    hinvol.apply_comm first sixth, hinvol.apply_comm second third,
    hinvol.apply_comm second fourth, hinvol.apply_comm second fifth,
    hinvol.apply_comm second sixth, hinvol.apply_comm third fourth,
    hinvol.apply_comm third fifth, hinvol.apply_comm third sixth,
    hinvol.apply_comm fourth fifth, hinvol.apply_comm fourth sixth,
    hinvol.apply_comm fifth sixth] at hzero ⊢
  linarith

/-- **THE FIVE-SET PRODUCT SUM VANISHES.**  Total minus the ten triples through the
deleted atom. -/
theorem sum_tripleProduct_fiveSet (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    hollowTripleProduct invol first second third + hollowTripleProduct invol first second fourth
      + hollowTripleProduct invol first second fifth + hollowTripleProduct invol first third fourth
      + hollowTripleProduct invol first third fifth + hollowTripleProduct invol first fourth fifth
      + hollowTripleProduct invol second third fourth + hollowTripleProduct invol second third fifth
      + hollowTripleProduct invol second fourth fifth
      + hollowTripleProduct invol third fourth fifth = 0 := by
  have htotal := hinvol.sum_tripleProduct_six hbijective
  have hvertex := hinvol.sum_pairTripleProduct_six hbijective sixth
  simp only [hollowTripleProduct, hinvol.diagonal_eq_zero, zero_mul, mul_zero, add_zero,
    hinvol.apply_comm first sixth, hinvol.apply_comm second sixth,
    hinvol.apply_comm third sixth, hinvol.apply_comm fourth sixth,
    hinvol.apply_comm fifth sixth] at htotal hvertex ⊢
  linarith

/-- **THE FOUR-SET PRODUCT SUM VANISHES.**  Inclusion–exclusion over the complementary
pair: total, minus the triples through each of the two deleted atoms, plus the four
through both.  This is the pen's `Σ_{T ⊆ F} P_T = 0`, i.e. the vanishing of the cubic
coefficient of the four-set spectral law. -/
theorem sum_tripleProduct_fourSet (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    hollowTripleProduct invol first second third + hollowTripleProduct invol first second fourth
      + hollowTripleProduct invol first third fourth
      + hollowTripleProduct invol second third fourth = 0 := by
  have htotal := hinvol.sum_tripleProduct_six hbijective
  have hfifth := hinvol.sum_pairTripleProduct_six hbijective fifth
  have hsixth := hinvol.sum_pairTripleProduct_six hbijective sixth
  have hfifthSixth : fifth ≠ sixth :=
    ne_of_bijective_six hbijective (by decide : (4 : Fin 6) ≠ 5)
  have hpair := hinvol.sum_tripleProduct_throughPair hbijective hfifthSixth
  simp only [hollowTripleProduct, hinvol.diagonal_eq_zero, zero_mul, mul_zero, add_zero,
    hinvol.apply_comm first fifth, hinvol.apply_comm second fifth,
    hinvol.apply_comm third fifth, hinvol.apply_comm fourth fifth,
    hinvol.apply_comm first sixth, hinvol.apply_comm second sixth,
    hinvol.apply_comm third sixth, hinvol.apply_comm fourth sixth,
    hinvol.apply_comm fifth sixth] at htotal hfifth hsixth hpair ⊢
  linarith

/-! ## 9. The `sigma` sums

Pure counting on top of section 7: inside a block of `n` atoms every pair lies in
`n - 2` of the triples.  So `Σ_T sigma_T = (n - 2) · (pair mass)`, which is `12` on the
whole six, `6` on a five-set, and `2(1 + w_pq)` on a four-set.  The per-vertex constant
is the pen's corrected `6`. -/

/-- **THE TWENTY-TRIPLE SIGMA SUM IS TWELVE.**  Each of the fifteen edges lies in four
of the twenty triples, and the total edge mass is `3`. -/
theorem sum_tripleSigma_six (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    hollowTripleSigma invol first second third + hollowTripleSigma invol first second fourth
      + hollowTripleSigma invol first second fifth + hollowTripleSigma invol first second sixth
      + hollowTripleSigma invol first third fourth + hollowTripleSigma invol first third fifth
      + hollowTripleSigma invol first third sixth + hollowTripleSigma invol first fourth fifth
      + hollowTripleSigma invol first fourth sixth + hollowTripleSigma invol first fifth sixth
      + hollowTripleSigma invol second third fourth + hollowTripleSigma invol second third fifth
      + hollowTripleSigma invol second third sixth + hollowTripleSigma invol second fourth fifth
      + hollowTripleSigma invol second fourth sixth + hollowTripleSigma invol second fifth sixth
      + hollowTripleSigma invol third fourth fifth + hollowTripleSigma invol third fourth sixth
      + hollowTripleSigma invol third fifth sixth
      + hollowTripleSigma invol fourth fifth sixth = 12 := by
  have hmass := hinvol.sum_pairSquare_six hbijective
  simp only [hollowTripleSigma]
  linarith

/-- **THE TEN TRIPLES THROUGH ONE ATOM CARRY SIGMA MASS SIX.**  Each of the five edges
at the atom lies in four of them, contributing `4 · 1`; the ten edges avoiding it
contribute their own total `3 - 1 = 2`.  The pen first recorded `5` here and corrected
it to `6`; `6` is what the row law gives. -/
theorem sum_tripleSigma_throughVertex (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    hollowTripleSigma invol first second third + hollowTripleSigma invol first second fourth
      + hollowTripleSigma invol first second fifth + hollowTripleSigma invol first second sixth
      + hollowTripleSigma invol first third fourth + hollowTripleSigma invol first third fifth
      + hollowTripleSigma invol first third sixth + hollowTripleSigma invol first fourth fifth
      + hollowTripleSigma invol first fourth sixth
      + hollowTripleSigma invol first fifth sixth = 6 := by
  have hmass := hinvol.sum_pairSquare_six hbijective
  have hrow := hinvol.sum_sq_row_six hbijective first
  simp only [hinvol.diagonal_eq_zero] at hrow
  simp only [hollowTripleSigma]
  linarith

/-- **THE FIVE-SET SIGMA SUM IS SIX.**  Ten triples, each edge in three of them, edge
mass `2`. -/
theorem sum_tripleSigma_fiveSet (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    hollowTripleSigma invol first second third + hollowTripleSigma invol first second fourth
      + hollowTripleSigma invol first second fifth + hollowTripleSigma invol first third fourth
      + hollowTripleSigma invol first third fifth + hollowTripleSigma invol first fourth fifth
      + hollowTripleSigma invol second third fourth + hollowTripleSigma invol second third fifth
      + hollowTripleSigma invol second fourth fifth
      + hollowTripleSigma invol third fourth fifth = 6 := by
  have hmass := hinvol.sum_pairSquare_fiveSet hbijective
  simp only [hollowTripleSigma]
  linarith

/-- **THE FOUR-SET SIGMA SUM IS `2(1 + w_pq)`.**  Four triples, each edge in two of
them, edge mass `1 + w_pq`. -/
theorem sum_tripleSigma_fourSet (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    hollowTripleSigma invol first second third + hollowTripleSigma invol first second fourth
      + hollowTripleSigma invol first third fourth + hollowTripleSigma invol second third fourth
      = 2 * (1 + invol fifth sixth ^ 2) := by
  have hmass := hinvol.sum_pairSquare_fourSet hbijective
  simp only [hollowTripleSigma]
  linarith

/-! ## 10. The three determinant totals, and their pigeonholes

`det Gamma[T] = 1 - sigma_T + 2 P_T`, so the two previous sections give the totals at
once.  These are the pen's `8`, `4` and `2(1 - w_pq)`, and each one immediately
supplies a triple at or above the average. -/

/-- **THE TWENTY-TRIPLE DETERMINANT TOTAL IS EIGHT.**  The pen's six-set identity.  The
same constant `8` is reached independently by
`IsHollowInvolution.sum_det_principalMinors_one_add` at level three, which knows nothing
about triples and reads it off the spectrum of `1 + M`; the two routes cross-check each
other, and neither is used to prove the other. -/
theorem sum_tripleBracket_six (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    hollowTripleBracket invol first second third + hollowTripleBracket invol first second fourth
      + hollowTripleBracket invol first second fifth + hollowTripleBracket invol first second sixth
      + hollowTripleBracket invol first third fourth + hollowTripleBracket invol first third fifth
      + hollowTripleBracket invol first third sixth + hollowTripleBracket invol first fourth fifth
      + hollowTripleBracket invol first fourth sixth + hollowTripleBracket invol first fifth sixth
      + hollowTripleBracket invol second third fourth + hollowTripleBracket invol second third fifth
      + hollowTripleBracket invol second third sixth
      + hollowTripleBracket invol second fourth fifth
      + hollowTripleBracket invol second fourth sixth
      + hollowTripleBracket invol second fifth sixth + hollowTripleBracket invol third fourth fifth
      + hollowTripleBracket invol third fourth sixth + hollowTripleBracket invol third fifth sixth
      + hollowTripleBracket invol fourth fifth sixth = 8 := by
  have hsigma := hinvol.sum_tripleSigma_six hbijective
  have hproduct := hinvol.sum_tripleProduct_six hbijective
  simp only [hollowTripleBracket_eq_one_sub_sigma_add]
  linarith

/-- **THE FIVE-SET DETERMINANT TOTAL IS FOUR.** -/
theorem sum_tripleBracket_fiveSet (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    hollowTripleBracket invol first second third + hollowTripleBracket invol first second fourth
      + hollowTripleBracket invol first second fifth + hollowTripleBracket invol first third fourth
      + hollowTripleBracket invol first third fifth + hollowTripleBracket invol first fourth fifth
      + hollowTripleBracket invol second third fourth + hollowTripleBracket invol second third fifth
      + hollowTripleBracket invol second fourth fifth
      + hollowTripleBracket invol third fourth fifth = 4 := by
  have hsigma := hinvol.sum_tripleSigma_fiveSet hbijective
  have hproduct := hinvol.sum_tripleProduct_fiveSet hbijective
  simp only [hollowTripleBracket_eq_one_sub_sigma_add]
  linarith

/-- **THE FOUR-SET DETERMINANT TOTAL IS `2(1 - w_pq)`.**  The pen's V4 input: the four
triples of a four-set share exactly twice the deficit of the complementary edge. -/
theorem sum_tripleBracket_fourSet (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    hollowTripleBracket invol first second third + hollowTripleBracket invol first second fourth
      + hollowTripleBracket invol first third fourth + hollowTripleBracket invol second third fourth
      = 2 * (1 - invol fifth sixth ^ 2) := by
  have hsigma := hinvol.sum_tripleSigma_fourSet hbijective
  have hproduct := hinvol.sum_tripleProduct_fourSet hbijective
  simp only [hollowTripleBracket_eq_one_sub_sigma_add]
  linarith

/-- **THE FOUR-SET GATE.**  Some triple of every four-set has
`det Gamma[T] ≥ (1 - w_pq)/2` — the pen's V4 input, stated at named triples so the
consumer can take whichever branch fires. -/
theorem exists_tripleBracket_ge_fourSet (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    (1 - invol fifth sixth ^ 2) / 2 ≤ hollowTripleBracket invol first second third
      ∨ (1 - invol fifth sixth ^ 2) / 2 ≤ hollowTripleBracket invol first second fourth
      ∨ (1 - invol fifth sixth ^ 2) / 2 ≤ hollowTripleBracket invol first third fourth
      ∨ (1 - invol fifth sixth ^ 2) / 2 ≤ hollowTripleBracket invol second third fourth := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hone, htwo, hthree, hfour⟩ := hcontra
  have htotal := hinvol.sum_tripleBracket_fourSet hbijective
  linarith

/-- **THE SIX-SET GATE.**  Twenty triples sharing a total of `8` put one of them at
`det Gamma[T] ≥ 2/5`.  No hypothesis beyond hollowness and the involution law. -/
theorem exists_distinct_tripleBracket_ge_two_fifths (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    ∃ leftIndex middleIndex rightIndex : Fin 6,
      leftIndex ≠ middleIndex ∧ leftIndex ≠ rightIndex ∧ middleIndex ≠ rightIndex
        ∧ 2 / 5 ≤ hollowTripleBracket invol leftIndex middleIndex rightIndex := by
  by_contra hcontra
  push Not at hcontra
  have hab : first ≠ second := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 1)
  have hac : first ≠ third := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 2)
  have had : first ≠ fourth := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 3)
  have hae : first ≠ fifth := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 4)
  have haf : first ≠ sixth := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 5)
  have hbc : second ≠ third := ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 2)
  have hbd : second ≠ fourth := ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 3)
  have hbe : second ≠ fifth := ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 4)
  have hbf : second ≠ sixth := ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 5)
  have hcd : third ≠ fourth := ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 3)
  have hce : third ≠ fifth := ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 4)
  have hcf : third ≠ sixth := ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 5)
  have hde : fourth ≠ fifth := ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 4)
  have hdf : fourth ≠ sixth := ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 5)
  have hef : fifth ≠ sixth := ne_of_bijective_six hbijective (by decide : (4 : Fin 6) ≠ 5)
  have htotal := hinvol.sum_tripleBracket_six hbijective
  linarith [hcontra first second third hab hac hbc, hcontra first second fourth hab had hbd,
    hcontra first second fifth hab hae hbe, hcontra first second sixth hab haf hbf,
    hcontra first third fourth hac had hcd, hcontra first third fifth hac hae hce,
    hcontra first third sixth hac haf hcf, hcontra first fourth fifth had hae hde,
    hcontra first fourth sixth had haf hdf, hcontra first fifth sixth hae haf hef,
    hcontra second third fourth hbc hbd hcd, hcontra second third fifth hbc hbe hce,
    hcontra second third sixth hbc hbf hcf, hcontra second fourth fifth hbd hbe hde,
    hcontra second fourth sixth hbd hbf hdf, hcontra second fifth sixth hbe hbf hef,
    hcontra third fourth fifth hcd hce hde, hcontra third fourth sixth hcd hcf hdf,
    hcontra third fifth sixth hce hcf hef, hcontra fourth fifth sixth hde hdf hef]

/-- **THE FIVE-SET GATE.**  The same constant `2/5` is reached by a triple AVOIDING any
chosen atom: ten triples sharing a total of `4`. -/
theorem exists_distinct_tripleBracket_ge_two_fifths_avoiding (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    ∃ leftIndex middleIndex rightIndex : Fin 6,
      leftIndex ≠ sixth ∧ middleIndex ≠ sixth ∧ rightIndex ≠ sixth
        ∧ leftIndex ≠ middleIndex ∧ leftIndex ≠ rightIndex ∧ middleIndex ≠ rightIndex
        ∧ 2 / 5 ≤ hollowTripleBracket invol leftIndex middleIndex rightIndex := by
  by_contra hcontra
  push Not at hcontra
  have hab : first ≠ second := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 1)
  have hac : first ≠ third := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 2)
  have had : first ≠ fourth := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 3)
  have hae : first ≠ fifth := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 4)
  have haf : first ≠ sixth := ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 5)
  have hbc : second ≠ third := ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 2)
  have hbd : second ≠ fourth := ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 3)
  have hbe : second ≠ fifth := ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 4)
  have hbf : second ≠ sixth := ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 5)
  have hcd : third ≠ fourth := ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 3)
  have hce : third ≠ fifth := ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 4)
  have hcf : third ≠ sixth := ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 5)
  have hde : fourth ≠ fifth := ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 4)
  have hdf : fourth ≠ sixth := ne_of_bijective_six hbijective (by decide : (3 : Fin 6) ≠ 5)
  have hef : fifth ≠ sixth := ne_of_bijective_six hbijective (by decide : (4 : Fin 6) ≠ 5)
  have htotal := hinvol.sum_tripleBracket_fiveSet hbijective
  linarith [hcontra first second third haf hbf hcf hab hac hbc,
    hcontra first second fourth haf hbf hdf hab had hbd,
    hcontra first second fifth haf hbf hef hab hae hbe,
    hcontra first third fourth haf hcf hdf hac had hcd,
    hcontra first third fifth haf hcf hef hac hae hce,
    hcontra first fourth fifth haf hdf hef had hae hde,
    hcontra second third fourth hbf hcf hdf hbc hbd hcd,
    hcontra second third fifth hbf hcf hef hbc hbe hce,
    hcontra second fourth fifth hbf hdf hef hbd hbe hde,
    hcontra third fourth fifth hcf hdf hef hcd hce hde]

end IsHollowInvolution

/-! ## 11. The four-set spectral law

`spec M[F] = {1, -1, +M_pq, -M_pq}` for every four-set of a hollow symmetric involution
on `Fin 6`, written as a determinant identity in a scalar probe.  Three coefficients are
already known: the linear one is the vanishing trace, the quadratic one is the four-set
pair mass `1 + w_pq` (section 7) and the cubic one is the four-set product sum `0`
(section 8).  The quartic one is pinned by the degeneracy `det Gamma[F] = 0` of section
4 — `Gamma` has rank three, so no four of its rows are independent. -/

/-- The symmetric `4 x 4` with a constant diagonal, in the slot convention
`(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)` — the same one `Gtz.hollowMatrixThree` uses
one size down. -/
def symmetricMatrixFour (diagValue edgeOne edgeTwo edgeThree edgeFour edgeFive edgeSix : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![diagValue, edgeOne, edgeTwo, edgeThree;
     edgeOne, diagValue, edgeFour, edgeFive;
     edgeTwo, edgeFour, diagValue, edgeSix;
     edgeThree, edgeFive, edgeSix, diagValue]

/-- Its determinant, expanded.  The coefficient of `diagValue^2` is minus the pair mass,
the coefficient of `diagValue` is twice the product sum, and the constant term is the
determinant of the hollow part. -/
theorem det_symmetricMatrixFour
    (diagValue edgeOne edgeTwo edgeThree edgeFour edgeFive edgeSix : ℝ) :
    (symmetricMatrixFour diagValue edgeOne edgeTwo edgeThree edgeFour edgeFive edgeSix).det
      = diagValue ^ 4
        - diagValue ^ 2 * (edgeOne ^ 2 + edgeTwo ^ 2 + edgeThree ^ 2 + edgeFour ^ 2
            + edgeFive ^ 2 + edgeSix ^ 2)
        + 2 * diagValue * (edgeOne * edgeTwo * edgeFour + edgeOne * edgeThree * edgeFive
            + edgeTwo * edgeThree * edgeSix + edgeFour * edgeFive * edgeSix)
        + (edgeOne ^ 2 * edgeSix ^ 2 + edgeTwo ^ 2 * edgeFive ^ 2 + edgeThree ^ 2 * edgeFour ^ 2
            - 2 * (edgeOne * edgeTwo * edgeFive * edgeSix)
            - 2 * (edgeOne * edgeThree * edgeFour * edgeSix)
            - 2 * (edgeTwo * edgeThree * edgeFour * edgeFive)) := by
  rw [symmetricMatrixFour, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Four pairwise distinct values enumerate injectively — the size-four twin of
`Gtz.injective_three_of_ne`. -/
theorem injective_four_of_ne {carrier : Type*}
    {firstValue secondValue thirdValue fourthValue : carrier}
    (hfirstSecond : firstValue ≠ secondValue) (hfirstThird : firstValue ≠ thirdValue)
    (hfirstFourth : firstValue ≠ fourthValue) (hsecondThird : secondValue ≠ thirdValue)
    (hsecondFourth : secondValue ≠ fourthValue) (hthirdFourth : thirdValue ≠ fourthValue) :
    Function.Injective ![firstValue, secondValue, thirdValue, fourthValue] := by
  intro leftSlot rightSlot hvalue
  fin_cases leftSlot <;> fin_cases rightSlot <;>
    first
      | rfl
      | exact absurd hvalue (by assumption)
      | exact absurd hvalue.symm (by assumption)

namespace IsHollowInvolution

variable {invol : Matrix (Fin 6) (Fin 6) ℝ}

/-- The shifted four-block IS the constant-diagonal symmetric `4 x 4` of the negated
entries: hollowness supplies the diagonal, symmetry the lower triangle. -/
theorem smul_one_sub_submatrix_four_eq (hinvol : IsHollowInvolution invol)
    (firstIndex secondIndex thirdIndex fourthIndex : Fin 6) (probeValue : ℝ) :
    probeValue • (1 : Matrix (Fin 4) (Fin 4) ℝ)
        - invol.submatrix ![firstIndex, secondIndex, thirdIndex, fourthIndex]
          ![firstIndex, secondIndex, thirdIndex, fourthIndex]
      = symmetricMatrixFour probeValue (-invol firstIndex secondIndex)
          (-invol firstIndex thirdIndex) (-invol firstIndex fourthIndex)
          (-invol secondIndex thirdIndex) (-invol secondIndex fourthIndex)
          (-invol thirdIndex fourthIndex) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [symmetricMatrixFour, hinvol.diagonal_eq_zero,
      hinvol.apply_comm firstIndex secondIndex, hinvol.apply_comm firstIndex thirdIndex,
      hinvol.apply_comm firstIndex fourthIndex, hinvol.apply_comm secondIndex thirdIndex,
      hinvol.apply_comm secondIndex fourthIndex, hinvol.apply_comm thirdIndex fourthIndex]

/-- The shifted four-block determinant, before the coefficients are identified. -/
theorem det_smul_one_sub_submatrix_four_expand (hinvol : IsHollowInvolution invol)
    (firstIndex secondIndex thirdIndex fourthIndex : Fin 6) (probeValue : ℝ) :
    (probeValue • (1 : Matrix (Fin 4) (Fin 4) ℝ)
        - invol.submatrix ![firstIndex, secondIndex, thirdIndex, fourthIndex]
          ![firstIndex, secondIndex, thirdIndex, fourthIndex]).det
      = probeValue ^ 4
        - probeValue ^ 2 * (invol firstIndex secondIndex ^ 2 + invol firstIndex thirdIndex ^ 2
            + invol firstIndex fourthIndex ^ 2 + invol secondIndex thirdIndex ^ 2
            + invol secondIndex fourthIndex ^ 2 + invol thirdIndex fourthIndex ^ 2)
        - 2 * probeValue * (hollowTripleProduct invol firstIndex secondIndex thirdIndex
            + hollowTripleProduct invol firstIndex secondIndex fourthIndex
            + hollowTripleProduct invol firstIndex thirdIndex fourthIndex
            + hollowTripleProduct invol secondIndex thirdIndex fourthIndex)
        + (invol firstIndex secondIndex ^ 2 * invol thirdIndex fourthIndex ^ 2
            + invol firstIndex thirdIndex ^ 2 * invol secondIndex fourthIndex ^ 2
            + invol firstIndex fourthIndex ^ 2 * invol secondIndex thirdIndex ^ 2
            - 2 * (invol firstIndex secondIndex * invol firstIndex thirdIndex
                * invol secondIndex fourthIndex * invol thirdIndex fourthIndex)
            - 2 * (invol firstIndex secondIndex * invol firstIndex fourthIndex
                * invol secondIndex thirdIndex * invol thirdIndex fourthIndex)
            - 2 * (invol firstIndex thirdIndex * invol firstIndex fourthIndex
                * invol secondIndex thirdIndex * invol secondIndex fourthIndex)) := by
  rw [hinvol.smul_one_sub_submatrix_four_eq, det_symmetricMatrixFour, hollowTripleProduct,
    hollowTripleProduct, hollowTripleProduct, hollowTripleProduct]
  ring

/-- **THE FOUR-SET SPECTRAL LAW.**  For every four-set of a hollow symmetric involution
on `Fin 6`, with complementary pair `{p,q}`,

    `det (x · 1 - M[F]) = (x² - 1)(x² - M_pq²)` ,

so `spec M[F] = {1, -1, +M_pq, -M_pq}`.  The campaign once recorded a SINGLE `± gamma`
here; the icosahedron refutes that reading and this is the corrected law, witnessed at
`Gtz.icosaDesign` by `Gtz.det_smul_one_sub_submatrix_four_icosaDesign`.

Proof.  Expanding at the constant-diagonal symmetric `4 x 4`, the coefficient of `x³` is
minus the trace, which vanishes by hollowness; the coefficient of `x²` is minus the
four-set pair mass, `-(1 + w_pq)` by `sum_pairSquare_fourSet`; the coefficient of `x` is
minus twice the four-set product sum, `0` by `sum_tripleProduct_fourSet`; and the
constant term is fixed by evaluating the expansion at `x = -1`, where the block is
`-(1 + M[F])` and the determinant is the vanishing four-block minor of `Gamma`
(`det_one_add_submatrix_eq_zero`, rank three against a four-set). -/
theorem det_smul_one_sub_submatrix_four (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    (probeValue : ℝ) :
    (probeValue • (1 : Matrix (Fin 4) (Fin 4) ℝ)
        - invol.submatrix ![first, second, third, fourth] ![first, second, third, fourth]).det
      = (probeValue ^ 2 - 1) * (probeValue ^ 2 - invol fifth sixth ^ 2) := by
  have hinjective : Function.Injective ![first, second, third, fourth] :=
    injective_four_of_ne (ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 1))
      (ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 2))
      (ne_of_bijective_six hbijective (by decide : (0 : Fin 6) ≠ 3))
      (ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 2))
      (ne_of_bijective_six hbijective (by decide : (1 : Fin 6) ≠ 3))
      (ne_of_bijective_six hbijective (by decide : (2 : Fin 6) ≠ 3))
  have hmass := hinvol.sum_pairSquare_fourSet hbijective
  have hproduct := hinvol.sum_tripleProduct_fourSet hbijective
  have hsingular : (((1 : Matrix (Fin 6) (Fin 6) ℝ) + invol).submatrix
      ![first, second, third, fourth] ![first, second, third, fourth]).det = 0 :=
    hinvol.det_one_add_submatrix_eq_zero (rankCount := 3) rfl (by norm_num) (by norm_num)
      hinjective
  have hshift : ((-1 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
      - invol.submatrix ![first, second, third, fourth] ![first, second, third, fourth]).det
      = (((1 : Matrix (Fin 6) (Fin 6) ℝ) + invol).submatrix
          ![first, second, third, fourth] ![first, second, third, fourth]).det := by
    have hblock : ((1 : Matrix (Fin 6) (Fin 6) ℝ) + invol).submatrix
        ![first, second, third, fourth] ![first, second, third, fourth]
        = 1 + invol.submatrix ![first, second, third, fourth] ![first, second, third, fourth] := by
      rw [show ((1 : Matrix (Fin 6) (Fin 6) ℝ) + invol).submatrix
          ![first, second, third, fourth] ![first, second, third, fourth]
          = (1 : Matrix (Fin 6) (Fin 6) ℝ).submatrix
              ![first, second, third, fourth] ![first, second, third, fourth]
            + invol.submatrix ![first, second, third, fourth]
              ![first, second, third, fourth] from rfl,
        Matrix.submatrix_one _ hinjective]
    rw [hblock, show (-1 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
        - invol.submatrix ![first, second, third, fourth] ![first, second, third, fourth]
        = -(1 + invol.submatrix ![first, second, third, fourth]
            ![first, second, third, fourth]) by
      rw [neg_add, neg_smul, one_smul]; abel, Matrix.det_neg]
    norm_num
  rw [hsingular, hinvol.det_smul_one_sub_submatrix_four_expand] at hshift
  rw [hinvol.det_smul_one_sub_submatrix_four_expand]
  simp only [hollowTripleProduct] at hproduct hshift ⊢
  linear_combination (1 - probeValue ^ 2) * hmass + (-2 * probeValue - 2) * hproduct + hshift

/-- **THE FOUR-BLOCK DETERMINANT IS THE COMPLEMENTARY EDGE WEIGHT.**  `det M[F] = w_pq`,
the constant term of the spectral law — the `x = 0` reading, up to the even-size sign. -/
theorem det_submatrix_four_eq_pairSquare (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    (invol.submatrix ![first, second, third, fourth] ![first, second, third, fourth]).det
      = invol fifth sixth ^ 2 := by
  have hprobe := hinvol.det_smul_one_sub_submatrix_four hbijective 0
  rw [show (0 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
      - invol.submatrix ![first, second, third, fourth] ![first, second, third, fourth]
      = -invol.submatrix ![first, second, third, fourth]
          ![first, second, third, fourth] by rw [zero_smul]; abel, Matrix.det_neg,
    Fintype.card_fin, show ((-1 : ℝ)) ^ 4 = 1 by norm_num, one_mul] at hprobe
  linarith [hprobe]

end IsHollowInvolution

/-! ## 12. Back to designs

Two things the frontier agent needs to consume sections 7 to 11 on a design.

First the BRIDGE.  `Gtz.isHollowInvolution_correlationInvolution` is stated at
`Gtz.IsEqualShare`, which demands `weight = 1/m` AND `leverage = k`; its proof consumes
only the uniform SHARE, and the V6 object (free weights, all-heavy leverages, shares all
`1/2`) satisfies the share condition and neither of the other two.  So the version below
is a re-statement at the weaker hypothesis, and with it every identity of sections 7 to
11 applies verbatim to a free-weight `(6,3)` design.  Note that the uniform share is
FORCED to be `k/m = 1/2` — it is not a second hypothesis.

Then the DICTIONARY: on a design the abstract triple scalars are the shipped direction
scalars, so the identities can be read in `Gtz.directionGram` coordinates without
unfolding anything. -/

/-- **THE BRIDGE, at the uniform share alone.**  A design of size `2k` whose shares all
agree has `Gamma - 1` a hollow symmetric involution.  Neither uniform weight nor uniform
leverage is assumed, so this covers the free-weight stratum; the common share is forced
to be `k/m`, hence `1/2`, and positivity of the leverages follows from it. -/
theorem isHollowInvolution_correlationInvolution_of_uniformShare (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hrank : 0 < k) (hdouble : (m : ℝ) = 2 * (k : ℝ)) :
    IsHollowInvolution (correlationInvolution D) := by
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hforced := size_mul_atomShare_eq_rank_of_atomShare_eq D huniform
  have hhalf : shareValue = 1 / 2 := by
    rw [hdouble] at hforced
    field_simp at hforced ⊢
    linarith
  have hpositive : 0 < shareValue := by rw [hhalf]; norm_num
  have hleverage : ∀ atomIndex : Fin m, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; exact hpositive)
  have hsquare := directionGramMatrix_sq_of_uniformShare D huniform hpositive
  rw [hhalf, show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at hsquare
  refine ⟨?_, ?_, fun atomIndex => correlationInvolution_apply_self D (hleverage atomIndex)⟩
  · ext rowIndex colIndex
    show directionGramMatrix D colIndex rowIndex - (1 : Matrix (Fin m) (Fin m) ℝ) colIndex rowIndex
      = directionGramMatrix D rowIndex colIndex - (1 : Matrix (Fin m) (Fin m) ℝ) rowIndex colIndex
    rw [show directionGramMatrix D colIndex rowIndex
        = directionGram D colIndex rowIndex from rfl,
      show directionGramMatrix D rowIndex colIndex
        = directionGram D rowIndex colIndex from rfl,
      directionGram_comm D colIndex rowIndex, Matrix.one_apply, Matrix.one_apply]
    split_ifs with hforward hbackward hbackward
    · rfl
    · exact absurd hforward.symm hbackward
    · exact absurd hbackward.symm hforward
    · rfl
  · rw [correlationInvolution, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, hsquare]
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs <;> ring

/-- The abstract `sigma` of the correlation involution IS the shipped
`Gtz.directionTripleSigma`. -/
theorem hollowTripleSigma_correlationInvolution_eq (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    hollowTripleSigma (correlationInvolution D) firstIndex secondIndex thirdIndex
      = directionTripleSigma D firstIndex secondIndex thirdIndex := by
  rw [hollowTripleSigma, directionTripleSigma,
    correlationInvolution_apply_of_ne D hfirstSecond,
    correlationInvolution_apply_of_ne D hfirstThird,
    correlationInvolution_apply_of_ne D hsecondThird]

/-- The abstract product of the correlation involution IS the shipped
`Gtz.directionTripleProduct`. -/
theorem hollowTripleProduct_correlationInvolution_eq (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    hollowTripleProduct (correlationInvolution D) firstIndex secondIndex thirdIndex
      = directionTripleProduct D firstIndex secondIndex thirdIndex := by
  rw [hollowTripleProduct, directionTripleProduct,
    correlationInvolution_apply_of_ne D hfirstSecond,
    correlationInvolution_apply_of_ne D hfirstThird,
    correlationInvolution_apply_of_ne D hsecondThird]

/-- The abstract bracket of the correlation involution is the elliptope bracket of the
three direction cosines — that is, `det Gamma[T]` in the coordinates every consumer
already uses. -/
theorem hollowTripleBracket_correlationInvolution_eq (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    hollowTripleBracket (correlationInvolution D) firstIndex secondIndex thirdIndex
      = elliptopeBracket (directionGram D firstIndex secondIndex)
          (directionGram D firstIndex thirdIndex) (directionGram D secondIndex thirdIndex) := by
  rw [hollowTripleBracket, correlationInvolution_apply_of_ne D hfirstSecond,
    correlationInvolution_apply_of_ne D hfirstThird,
    correlationInvolution_apply_of_ne D hsecondThird]

/-- **THE `(6,3)` CONSTANT.**  The twenty three-subsets of an equal-share `(6,3)` design
share a determinant total of `8`. -/
theorem sum_det_principalMinors_directionGramMatrix_sixThree (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        ((directionGramMatrix D).submatrix
          (Subtype.val : { index // index ∈ selected } → Fin 6)
          (Subtype.val : { index // index ∈ selected } → Fin 6)).det = 8 := by
  rw [sum_det_principalMinors_directionGramMatrix_of_uniformShare D huniform (by norm_num) 3
    (by norm_num)]
  norm_num

/-- **THE `(7,3)` CONSTANT.**  The same theorem at the equal-share `(7,3)` stratum, where
the share is `3/7`: the thirty-five three-subsets share a determinant total of `343/27`.
This is the `(7,3)` analogue the frontier needs, and it comes from the same closed form
rather than from a second spectral derivation. -/
theorem sum_det_principalMinors_directionGramMatrix_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 7)).powersetCard 3,
        ((directionGramMatrix D).submatrix
          (Subtype.val : { index // index ∈ selected } → Fin 7)
          (Subtype.val : { index // index ∈ selected } → Fin 7)).det = 343 / 27 := by
  rw [sum_det_principalMinors_directionGramMatrix_of_uniformShare D huniform (by norm_num) 3
    (by norm_num)]
  norm_num

/-! ## 13. Non-vacuity: the four-set spectral law at the icosahedron

The campaign once recorded the four-set spectrum as carrying a SINGLE `± gamma`, and the
icosahedron is what refuted that.  Here it is in the kernel: every icosahedral four-set
has characteristic polynomial `(x² - 1)(x² - 1/5)`, so the two square roots BOTH occur,
one with each sign.  This also witnesses that the hypothesis set of sections 4 to 11 is
inhabited. -/

/-- Every distinct pair of icosahedral diagonals has squared direction cosine `1/5`:
leverage `3` against raw squared pairing `9/5`. -/
theorem sq_directionGram_icosaDesign {firstIndex secondIndex : Fin 6}
    (hdistinct : firstIndex ≠ secondIndex) :
    directionGram icosaDesign firstIndex secondIndex ^ 2 = 1 / 5 := by
  have hleverage : ∀ index : Fin 6, leverageOf (icosaDesign.atom index) = 3 := fun index => by
    rw [leverageOf_eq_dotProduct, icosaDesign_atom, icosaAtom_leverage]
  have hsquareRoot : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpair := icosaAtom_dot_sq_of_ne hdistinct
  rw [directionGram_eq_scaled_atomPairing, hleverage, hleverage, icosaDesign_atom,
    show ((Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ * (icosaAtom firstIndex ⬝ᵥ icosaAtom secondIndex)) ^ 2
      = ((Real.sqrt 3) ^ 2)⁻¹ * ((Real.sqrt 3) ^ 2)⁻¹
          * (icosaAtom firstIndex ⬝ᵥ icosaAtom secondIndex) ^ 2 from by ring,
    hsquareRoot, hpair]
  norm_num

/-- **THE FOUR-SET SPECTRAL LAW, WITNESSED.**  At `Gtz.icosaDesign` the four-set
`{0,1,2,3}` has `det (x · 1 - M[F]) = (x² - 1)(x² - 1/5)`, so its spectrum is
`{1, -1, +1/√5, -1/√5}` — two square roots, not one. -/
theorem det_smul_one_sub_submatrix_four_icosaDesign (probeValue : ℝ) :
    (probeValue • (1 : Matrix (Fin 4) (Fin 4) ℝ)
        - (correlationInvolution icosaDesign).submatrix ![0, 1, 2, 3] ![0, 1, 2, 3]).det
      = (probeValue ^ 2 - 1) * (probeValue ^ 2 - 1 / 5) := by
  have hlaw := isHollowInvolution_icosaDesign.det_smul_one_sub_submatrix_four
    (first := 0) (second := 1) (third := 2) (fourth := 3) (fifth := 4) (sixth := 5)
    (by decide) probeValue
  rwa [correlationInvolution_apply_of_ne icosaDesign (by decide : (4 : Fin 6) ≠ 5),
    sq_directionGram_icosaDesign (by decide : (4 : Fin 6) ≠ 5)] at hlaw

/-- The six-set gate, witnessed at the icosahedron. -/
theorem exists_distinct_tripleBracket_ge_two_fifths_icosaDesign :
    ∃ leftIndex middleIndex rightIndex : Fin 6,
      leftIndex ≠ middleIndex ∧ leftIndex ≠ rightIndex ∧ middleIndex ≠ rightIndex
        ∧ 2 / 5 ≤ hollowTripleBracket (correlationInvolution icosaDesign)
            leftIndex middleIndex rightIndex :=
  isHollowInvolution_icosaDesign.exists_distinct_tripleBracket_ge_two_fifths
    (first := 0) (second := 1) (third := 2) (fourth := 3) (fifth := 4) (sixth := 5) (by decide)

end Gtz
