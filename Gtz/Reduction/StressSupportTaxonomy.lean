import Mathlib
import Gtz.Reduction.StressSignSplit
import Gtz.Reduction.StressExistence
import Gtz.Reduction.SplitTransfer
import Gtz.Quantitative.DesignQuadraticFloors

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-
# The strata of a unique-stress `(7,3)` design

`Gtz.gtzWeighted_seven_three_iff_uniqueStress` puts the whole of weighted rank
three on one statement: every `(7,3)` design whose stress space is a LINE has a
dominating triple.  This file classifies those designs by the SUPPORT of that
line, which is the first structural handle on the statement that does not pass
through `GtzWeighted 6 3` (carrying that hypothesis trivialises the cell, so it
is never assumed here).

Two engines do all the work, and both are rank-relative -- the landed split law
reads the sign split only when the family SPANS, and a stress support generally
does not.

* **Lower bound** (`Gtz.twice_finrank_supportSpan_le_card_stressSupport`): the
  support of any stress has at least `2 * r` labels, where `r` is the dimension
  of the span of the supported atoms.  This is the landed transfer law
  `Gtz.neg_side_orthogonal_of_pos_side` run against a probe constrained to the
  support span rather than to all of `R^k` -- the span-relative form of
  `Gtz.rank_le_card_pos_side`.

* **Upper bound** (`Gtz.card_stressSupport_le_succ_finrank_of_unique`): under
  uniqueness the support has at most `d + 1` labels, where `d` is the dimension
  of the span of the supported atom MATRICES.  Rank-nullity on the support-
  restricted stress map; the kernel embeds in the stress line.

Feeding `d <= r(r+1)/2` (the Veronese count, done here by hand at `r <= 2`)
into `2r <= s <= d + 1` leaves exactly

    r = 0 : s = 1  -- a zero atom
    r = 1 : s = 2  -- a parallel pair
    r = 2 : s = 4  -- a coplanar conic-dependent quadruple, split (2,2)
    r = 3 : s = 6  -- spanning, split (3,3), one free atom
    r = 3 : s = 7  -- spanning, split (3,4) up to sign: THE MAIN STRATUM

and NOTHING else: sizes three and five are impossible at every rank, and the
low-rank strata all carry a parallel pair.  Sizes `s = 3` and `s = 5` die from
the two inequalities alone, with no case analysis.

The `s = 1` stratum is a correction to the campaign's earlier taxonomy, which
listed four strata starting at `s = 2`: a design MAY carry a zero atom (nothing
in `Gtz.WeightedDesign` forbids it -- Parseval only constrains the weighted
sum), and then the indicator of that label is a stress of support one.  It is
the `r = 0` corner of the same two inequalities.
-/

namespace Gtz

open Matrix Finset

variable {n k : ℕ}

/-! ## Part 1: the support of a stress and the span of its atoms -/

/-- The support of a coefficient vector: the labels carrying a nonzero entry. -/
noncomputable def stressSupport (stressCoeff : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun c => stressCoeff c ≠ 0

theorem mem_stressSupport_iff {stressCoeff : Fin n → ℝ} {c : Fin n} :
    c ∈ stressSupport stressCoeff ↔ stressCoeff c ≠ 0 := by
  simp [stressSupport]

/-- The linear span of the atoms carried by the support of a stress. -/
noncomputable def supportSpan (atomFamily : Fin n → Fin k → ℝ) (stressCoeff : Fin n → ℝ) :
    Submodule ℝ (Fin k → ℝ) :=
  Submodule.span ℝ (atomFamily '' (↑(stressSupport stressCoeff) : Set (Fin n)))

theorem atom_mem_supportSpan (atomFamily : Fin n → Fin k → ℝ) {stressCoeff : Fin n → ℝ}
    {c : Fin n} (hsupported : stressCoeff c ≠ 0) :
    atomFamily c ∈ supportSpan atomFamily stressCoeff :=
  Submodule.subset_span ⟨c, mem_stressSupport_iff.mpr hsupported, rfl⟩

/-- **A probe inside the support span that annihilates every supported atom is
zero.**  The span sits inside the kernel of the functional `y => y dot probe`,
and the probe sits inside the span, so the probe pairs to zero with itself. -/
theorem eq_zero_of_mem_supportSpan_of_orthogonal (atomFamily : Fin n → Fin k → ℝ)
    (stressCoeff : Fin n → ℝ) {probe : Fin k → ℝ}
    (hmem : probe ∈ supportSpan atomFamily stressCoeff)
    (horthogonal : ∀ c, stressCoeff c ≠ 0 → atomFamily c ⬝ᵥ probe = 0) :
    probe = 0 := by
  have hkills : ∀ vector ∈ supportSpan atomFamily stressCoeff, vector ⬝ᵥ probe = 0 := by
    intro vector hvector
    induction hvector using Submodule.span_induction with
    | mem generator hgenerator =>
        obtain ⟨c, hc, hgen⟩ := hgenerator
        exact hgen ▸ horthogonal c (mem_stressSupport_iff.mp hc)
    | zero => simp
    | add left right _ _ hleft hright => rw [add_dotProduct, hleft, hright, add_zero]
    | smul scalar vector _ hvector => rw [smul_dotProduct, hvector, smul_zero]
  by_contra hne
  exact absurd (hkills probe hmem) (ne_of_gt (selfDotProduct_pos hne))

/-! ## Part 2: the span-relative split law -/

/-- **The split law, span-relative, positive side.**  The positive sign side of
a stress has at least as many labels as the DIMENSION OF THE SPAN of the
supported atoms.  The landed `Gtz.rank_le_card_pos_side` is the case where that
span is everything; here the probe supplied by rank-nullity is constrained to
lie in the span, which is what makes the conclusion available on a support that
fails to span `R^k`. -/
theorem finrank_supportSpan_le_card_positiveSide (atomFamily : Fin n → Fin k → ℝ)
    {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0) :
    Module.finrank ℝ (supportSpan atomFamily stressCoeff)
      ≤ (Finset.univ.filter fun c => 0 < stressCoeff c).card := by
  by_contra hnot
  push Not at hnot
  set positiveSide := Finset.univ.filter fun c => 0 < stressCoeff c with hpositiveSide
  let evalMap : (supportSpan atomFamily stressCoeff) →ₗ[ℝ] (↥positiveSide → ℝ) :=
    { toFun := fun vector label => atomFamily label.1 ⬝ᵥ (vector : Fin k → ℝ)
      map_add' := by
        intro left right
        funext label
        show atomFamily label.1 ⬝ᵥ ((left : Fin k → ℝ) + (right : Fin k → ℝ)) = _
        rw [dotProduct_add]
        rfl
      map_smul' := by
        intro scalar vector
        funext label
        show atomFamily label.1 ⬝ᵥ (scalar • (vector : Fin k → ℝ)) = _
        rw [dotProduct_smul]
        rfl }
  have hnotInjective : ¬ Function.Injective evalMap := by
    intro hinjective
    have hle := LinearMap.finrank_le_finrank_of_injective hinjective
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hle
    omega
  rw [← LinearMap.ker_eq_bot] at hnotInjective
  obtain ⟨kernelVector, hkernelMem, hkernelNe⟩ := (Submodule.ne_bot_iff _).mp hnotInjective
  have hpositiveZero : ∀ c, 0 < stressCoeff c →
      atomFamily c ⬝ᵥ (kernelVector : Fin k → ℝ) = 0 := by
    intro c hc
    have happlied := congrFun (LinearMap.mem_ker.mp hkernelMem)
      ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩⟩
    exact happlied
  have hnegativeZero := neg_side_orthogonal_of_pos_side hstress hpositiveZero
  have hvanish : (kernelVector : Fin k → ℝ) = 0 := by
    refine eq_zero_of_mem_supportSpan_of_orthogonal atomFamily stressCoeff
      kernelVector.2 fun c hc => ?_
    rcases lt_or_lt_iff_ne.mpr hc with hlt | hgt
    · exact hnegativeZero c hlt
    · exact hpositiveZero c hgt
  exact hkernelNe (Subtype.ext hvanish)

/-- The negated stress has the same support, hence the same support span. -/
theorem supportSpan_neg (atomFamily : Fin n → Fin k → ℝ) (stressCoeff : Fin n → ℝ) :
    supportSpan atomFamily (-stressCoeff) = supportSpan atomFamily stressCoeff := by
  have hsupport : stressSupport (-stressCoeff) = stressSupport stressCoeff := by
    ext c
    simp [stressSupport]
  rw [supportSpan, supportSpan, hsupport]

/-- **The split law, span-relative, negative side**, by running the positive
side against the negated stress. -/
theorem finrank_supportSpan_le_card_negativeSide (atomFamily : Fin n → Fin k → ℝ)
    {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0) :
    Module.finrank ℝ (supportSpan atomFamily stressCoeff)
      ≤ (Finset.univ.filter fun c => stressCoeff c < 0).card := by
  have hstressNeg : ∑ c, (-stressCoeff) c • atomMatrix (atomFamily c) = 0 := by
    have hpointwise : ∀ c ∈ Finset.univ,
        (-stressCoeff) c • atomMatrix (atomFamily c)
          = -(stressCoeff c • atomMatrix (atomFamily c)) := by
      intro c _
      rw [Pi.neg_apply, neg_smul]
    rw [Finset.sum_congr rfl hpointwise]
    simp [hstress]
  have hcard := finrank_supportSpan_le_card_positiveSide atomFamily hstressNeg
  rw [supportSpan_neg] at hcard
  have hfilter : (Finset.univ.filter fun c => 0 < (-stressCoeff) c)
      = (Finset.univ.filter fun c => stressCoeff c < 0) := by
    ext c
    simp
  rwa [hfilter] at hcard

/-- The two sign sides partition the support. -/
theorem card_positiveSide_add_card_negativeSide (stressCoeff : Fin n → ℝ) :
    (Finset.univ.filter fun c => 0 < stressCoeff c).card
        + (Finset.univ.filter fun c => stressCoeff c < 0).card
      = (stressSupport stressCoeff).card := by
  have hdisjoint : Disjoint (Finset.univ.filter fun c => 0 < stressCoeff c)
      (Finset.univ.filter fun c => stressCoeff c < 0) := by
    rw [Finset.disjoint_left]
    intro c hcPositive hcNegative
    exact absurd (Finset.mem_filter.mp hcNegative).2
      (asymm (Finset.mem_filter.mp hcPositive).2)
  have hunion : (Finset.univ.filter fun c => 0 < stressCoeff c)
      ∪ (Finset.univ.filter fun c => stressCoeff c < 0) = stressSupport stressCoeff := by
    ext c
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      stressSupport]
    rw [or_comm]
    exact lt_or_lt_iff_ne
  rw [← Finset.card_union_of_disjoint hdisjoint, hunion]

/-- **THE LOWER BOUND.**  The support of a stress carries at least twice the
dimension of the span of its atoms.  Every impossibility in the taxonomy below
is this inequality read against the Veronese upper bound. -/
theorem twice_finrank_supportSpan_le_card_stressSupport (atomFamily : Fin n → Fin k → ℝ)
    {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0) :
    2 * Module.finrank ℝ (supportSpan atomFamily stressCoeff)
      ≤ (stressSupport stressCoeff).card := by
  have hpositive := finrank_supportSpan_le_card_positiveSide atomFamily hstress
  have hnegative := finrank_supportSpan_le_card_negativeSide atomFamily hstress
  have hpartition := card_positiveSide_add_card_negativeSide stressCoeff
  omega

/-! ## Part 3: the combination map and the uniqueness upper bound -/

/-- The combination map of a finite family of matrices: coefficients to the
weighted sum.  Three consumers share it -- the stress map of a whole family, the
stress map restricted to a support, and the span of an explicit generator list --
so all three inherit `Gtz.finrank_range_matrixCombinationMap_le`. -/
noncomputable def matrixCombinationMap {index : Type*} [Fintype index]
    (family : index → Matrix (Fin k) (Fin k) ℝ) :
    (index → ℝ) →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ where
  toFun := fun coeff => ∑ i, coeff i • family i
  map_add' := by
    intro left right
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_smul]
  map_smul' := by
    intro scalar coeff
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]

theorem matrixCombinationMap_apply {index : Type*} [Fintype index]
    (family : index → Matrix (Fin k) (Fin k) ℝ) (coeff : index → ℝ) :
    matrixCombinationMap family coeff = ∑ i, coeff i • family i := rfl

/-- The range of a combination map has dimension at most the number of
generators -- rank-nullity on the coefficient space. -/
theorem finrank_range_matrixCombinationMap_le {index : Type*} [Fintype index]
    (family : index → Matrix (Fin k) (Fin k) ℝ) :
    Module.finrank ℝ (LinearMap.range (matrixCombinationMap family))
      ≤ Fintype.card index := by
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker (matrixCombinationMap family)
  rw [Module.finrank_fintype_fun_eq_card] at hrankNullity
  omega

/-- Every value of a combination map whose generators all lie in a submodule
lies in that submodule. -/
theorem range_matrixCombinationMap_le {index : Type*} [Fintype index]
    (family : index → Matrix (Fin k) (Fin k) ℝ)
    (target : Submodule ℝ (Matrix (Fin k) (Fin k) ℝ))
    (hgenerators : ∀ i, family i ∈ target) :
    LinearMap.range (matrixCombinationMap family) ≤ target := by
  rintro matrixValue ⟨coeff, rfl⟩
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hgenerators i)

/-- The stress map of a family: coefficient vectors to the combination of atom
matrices they weight.  Its kernel is the stress space. -/
noncomputable def stressMap (atomFamily : Fin n → Fin k → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ :=
  matrixCombinationMap fun c => atomMatrix (atomFamily c)

/-- The stress map restricted to a support: the coefficient space shrinks to the
supported labels while the target is unchanged. -/
noncomputable def supportStressMap (atomFamily : Fin n → Fin k → ℝ)
    (support : Finset (Fin n)) :
    (↥support → ℝ) →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ :=
  matrixCombinationMap fun c : ↥support => atomMatrix (atomFamily c.1)

/-- Extension of a coefficient vector on a support by zero off it. -/
noncomputable def extendByZero (support : Finset (Fin n)) :
    (↥support → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := fun coeff c => if hmem : c ∈ support then coeff ⟨c, hmem⟩ else 0
  map_add' := by
    intro left right
    funext c
    by_cases hmem : c ∈ support <;> simp [hmem]
  map_smul' := by
    intro scalar coeff
    funext c
    by_cases hmem : c ∈ support <;> simp [hmem]

theorem extendByZero_injective (support : Finset (Fin n)) :
    Function.Injective (extendByZero support) := by
  intro left right hequal
  funext c
  have hpoint := congrFun hequal c.1
  simpa [extendByZero, c.2] using hpoint

/-- Extending by zero and then applying the whole family's stress map is the
support-restricted stress map. -/
theorem stressMap_extendByZero (atomFamily : Fin n → Fin k → ℝ)
    (support : Finset (Fin n)) (coeff : ↥support → ℝ) :
    stressMap atomFamily (extendByZero support coeff)
      = supportStressMap atomFamily support coeff := by
  rw [stressMap, supportStressMap, matrixCombinationMap_apply, matrixCombinationMap_apply]
  symm
  have hrelabel : ∑ c : ↥support, coeff c • atomMatrix (atomFamily c.1)
      = ∑ c : ↥support, (extendByZero support coeff c.1) • atomMatrix (atomFamily c.1) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = (if hmem : c.1 ∈ support then coeff ⟨c.1, hmem⟩ else 0) • _
    rw [dif_pos c.2]
  rw [hrelabel, Finset.sum_coe_sort support
    fun c => (extendByZero support coeff c) • atomMatrix (atomFamily c)]
  refine Finset.sum_subset (Finset.subset_univ support) ?_
  intro c _ houtside
  show (if hmem : c ∈ support then coeff ⟨c, hmem⟩ else 0) • atomMatrix (atomFamily c) = 0
  rw [dif_neg houtside, zero_smul]

/-- **Uniqueness caps the stress space at a line.**  Every stress is a multiple
of one direction, so the kernel of the stress map sits inside the image of the
line through that direction. -/
theorem finrank_ker_stressMap_le_one (atomFamily : Fin n → Fin k → ℝ)
    {direction : Fin n → ℝ}
    (hunique : ∀ stress : Fin n → ℝ, (∑ c, stress c • atomMatrix (atomFamily c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction) :
    Module.finrank ℝ (LinearMap.ker (stressMap atomFamily)) ≤ 1 := by
  have hline : LinearMap.ker (stressMap atomFamily)
      ≤ LinearMap.range (LinearMap.toSpanSingleton ℝ (Fin n → ℝ) direction) := by
    intro stress hstress
    obtain ⟨ratio, hratio⟩ := hunique stress (LinearMap.mem_ker.mp hstress)
    exact ⟨ratio, hratio.symm⟩
  have hlineRank : Module.finrank ℝ
      (LinearMap.range (LinearMap.toSpanSingleton ℝ (Fin n → ℝ) direction)) ≤ 1 := by
    have hrankNullity := LinearMap.finrank_range_add_finrank_ker
      (LinearMap.toSpanSingleton ℝ (Fin n → ℝ) direction)
    rw [Module.finrank_self] at hrankNullity
    omega
  exact le_trans (Submodule.finrank_mono hline) hlineRank

/-- **THE UPPER BOUND.**  Under uniqueness the support of the stress carries at
most one more label than the dimension of the span of its atom MATRICES.  The
kernel of the support-restricted stress map embeds into the stress line by
extension by zero, so rank-nullity on the support pays for the count. -/
theorem card_stressSupport_le_succ_finrank_range (atomFamily : Fin n → Fin k → ℝ)
    {direction : Fin n → ℝ}
    (hunique : ∀ stress : Fin n → ℝ, (∑ c, stress c • atomMatrix (atomFamily c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction) :
    (stressSupport direction).card
      ≤ Module.finrank ℝ
          (LinearMap.range (supportStressMap atomFamily (stressSupport direction))) + 1 := by
  set support := stressSupport direction with hsupport
  set restricted := supportStressMap atomFamily support with hrestricted
  have hkernelSmall :
      Module.finrank ℝ (LinearMap.ker restricted)
        ≤ Module.finrank ℝ (LinearMap.ker (stressMap atomFamily)) := by
    have hmaps : ∀ coeff : ↥(LinearMap.ker restricted),
        (extendByZero support) (coeff : ↥support → ℝ)
          ∈ LinearMap.ker (stressMap atomFamily) := by
      intro coeff
      rw [LinearMap.mem_ker, stressMap_extendByZero]
      exact LinearMap.mem_ker.mp coeff.2
    let embedding : ↥(LinearMap.ker restricted) →ₗ[ℝ]
        ↥(LinearMap.ker (stressMap atomFamily)) :=
      LinearMap.codRestrict _
        ((extendByZero support).comp (LinearMap.ker restricted).subtype) hmaps
    have hinjective : Function.Injective embedding := by
      intro left right hequal
      have hcoe : (extendByZero support) (left : ↥support → ℝ)
          = (extendByZero support) (right : ↥support → ℝ) :=
        congrArg Subtype.val hequal
      exact Subtype.ext (extendByZero_injective support hcoe)
    exact LinearMap.finrank_le_finrank_of_injective hinjective
  have hunit := finrank_ker_stressMap_le_one atomFamily hunique
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker restricted
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrankNullity
  omega

/-! ## Part 4: the Veronese count, one support rank at a time -/

/-- The generator form of the upper bound: exhibit a finite list of matrices
containing every supported atom matrix in its span, and the support is capped by
its length plus one. -/
theorem card_stressSupport_le_of_generators (atomFamily : Fin n → Fin k → ℝ)
    {direction : Fin n → ℝ}
    (hunique : ∀ stress : Fin n → ℝ, (∑ c, stress c • atomMatrix (atomFamily c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction)
    {generatorCount : ℕ} (generator : Fin generatorCount → Matrix (Fin k) (Fin k) ℝ)
    (hatoms : ∀ c, direction c ≠ 0 →
      atomMatrix (atomFamily c) ∈ LinearMap.range (matrixCombinationMap generator)) :
    (stressSupport direction).card ≤ generatorCount + 1 := by
  have hupper := card_stressSupport_le_succ_finrank_range atomFamily hunique
  have hcontained : LinearMap.range (supportStressMap atomFamily (stressSupport direction))
      ≤ LinearMap.range (matrixCombinationMap generator) :=
    range_matrixCombinationMap_le _ _ fun c => hatoms c.1 (mem_stressSupport_iff.mp c.2)
  have hmono := Submodule.finrank_mono hcontained
  have hgenerators := finrank_range_matrixCombinationMap_le generator
  rw [Fintype.card_fin] at hgenerators
  omega

theorem atomMatrix_zero : atomMatrix (0 : Fin k → ℝ) = 0 := by
  ext row col
  simp [atomMatrix, Matrix.vecMulVec_apply]

/-- A subspace of known dimension has a generating list of that length that
every member is a combination of.  Sole consumer of the basis machinery in this
file; the rank-one and rank-two readings below are its `Fin 1` and `Fin 2`
instances. -/
theorem exists_representation_of_finrank_eq {subspace : Submodule ℝ (Fin k → ℝ)}
    {dimension : ℕ} (hrank : Module.finrank ℝ subspace = dimension) :
    ∃ generator : Fin dimension → Fin k → ℝ, ∀ vector ∈ subspace,
      ∃ coeff : Fin dimension → ℝ, vector = ∑ index, coeff index • generator index := by
  let subspaceBasis := Module.finBasisOfFinrankEq ℝ ↥subspace hrank
  refine ⟨fun index => ((subspaceBasis index : ↥subspace) : Fin k → ℝ),
    fun vector hvector => ⟨fun index => subspaceBasis.repr ⟨vector, hvector⟩ index, ?_⟩⟩
  have hcoe := congrArg subspace.subtype (subspaceBasis.sum_repr ⟨vector, hvector⟩)
  rw [map_sum] at hcoe
  simp only [map_smul, Submodule.subtype_apply] at hcoe
  exact hcoe.symm

/-- A probe orthogonal to a generating list is orthogonal to the whole
subspace. -/
theorem dotProduct_eq_zero_of_generators_orthogonal {subspace : Submodule ℝ (Fin k → ℝ)}
    {dimension : ℕ} {generator : Fin dimension → Fin k → ℝ}
    (hrepresents : ∀ vector ∈ subspace,
      ∃ coeff : Fin dimension → ℝ, vector = ∑ index, coeff index • generator index)
    {probe : Fin k → ℝ} (horthogonal : ∀ index, generator index ⬝ᵥ probe = 0)
    {vector : Fin k → ℝ} (hvector : vector ∈ subspace) :
    vector ⬝ᵥ probe = 0 := by
  obtain ⟨coeff, hcoeff⟩ := hrepresents vector hvector
  rw [hcoeff, sum_dotProduct]
  exact Finset.sum_eq_zero fun index _ => by
    rw [smul_dotProduct, horthogonal index, smul_zero]

/-- A one-dimensional subspace of `R^k` has a generator every member is a
multiple of. -/
theorem exists_generator_of_finrank_eq_one {subspace : Submodule ℝ (Fin k → ℝ)}
    (hrank : Module.finrank ℝ subspace = 1) :
    ∃ generator : Fin k → ℝ, ∀ vector ∈ subspace, ∃ scalar : ℝ, vector = scalar • generator := by
  obtain ⟨generator, hrepresents⟩ := exists_representation_of_finrank_eq hrank
  refine ⟨generator 0, fun vector hvector => ?_⟩
  obtain ⟨coeff, hcoeff⟩ := hrepresents vector hvector
  exact ⟨coeff 0, by rw [hcoeff, Fin.sum_univ_one]⟩

/-- A two-dimensional subspace of `R^k` has a generating pair every member is a
combination of. -/
theorem exists_generating_pair_of_finrank_eq_two {subspace : Submodule ℝ (Fin k → ℝ)}
    (hrank : Module.finrank ℝ subspace = 2) :
    ∃ firstGenerator secondGenerator : Fin k → ℝ, ∀ vector ∈ subspace,
      ∃ alpha beta : ℝ, vector = alpha • firstGenerator + beta • secondGenerator := by
  obtain ⟨generator, hrepresents⟩ := exists_representation_of_finrank_eq hrank
  refine ⟨generator 0, generator 1, fun vector hvector => ?_⟩
  obtain ⟨coeff, hcoeff⟩ := hrepresents vector hvector
  exact ⟨coeff 0, coeff 1, by rw [hcoeff, Fin.sum_univ_two]⟩

/-- **The rank-two Veronese expansion.**  The atom of a combination of two
vectors is a combination of the THREE symmetric products of the pair -- not the
four unsymmetrised ones.  This is the whole content of `dim Sym^2 = 3` at rank
two, and the reason the coplanar stratum is pinned to support four rather than
merely bounded by five. -/
theorem atomMatrix_pair_expansion (firstGenerator secondGenerator : Fin k → ℝ)
    (alpha beta : ℝ) :
    atomMatrix (alpha • firstGenerator + beta • secondGenerator)
      = (alpha ^ 2) • Matrix.vecMulVec firstGenerator firstGenerator
        + ((alpha * beta) • (Matrix.vecMulVec firstGenerator secondGenerator
            + Matrix.vecMulVec secondGenerator firstGenerator)
          + (beta ^ 2) • Matrix.vecMulVec secondGenerator secondGenerator) := by
  ext row col
  simp only [atomMatrix, Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Rank zero: the support is a single zero atom.**  Nothing in
`Gtz.WeightedDesign` forbids a zero atom, and its indicator is a stress. -/
theorem card_stressSupport_eq_one_of_finrank_eq_zero (atomFamily : Fin n → Fin k → ℝ)
    {direction : Fin n → ℝ} (hdirectionNonzero : direction ≠ 0)
    (hunique : ∀ stress : Fin n → ℝ, (∑ c, stress c • atomMatrix (atomFamily c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction)
    (hrank : Module.finrank ℝ (supportSpan atomFamily direction) = 0) :
    (stressSupport direction).card = 1 ∧ ∀ c, direction c ≠ 0 → atomFamily c = 0 := by
  have hbot : supportSpan atomFamily direction = ⊥ := Submodule.finrank_eq_zero.mp hrank
  have hvanish : ∀ c, direction c ≠ 0 → atomFamily c = 0 := fun c hc =>
    (Submodule.eq_bot_iff _).mp hbot _ (atom_mem_supportSpan atomFamily hc)
  have hupper : (stressSupport direction).card ≤ 1 := by
    have hbound := card_stressSupport_le_of_generators atomFamily hunique
      (generatorCount := 0) (fun index => index.elim0) fun c hc => ⟨0, by
        rw [matrixCombinationMap_apply, hvanish c hc, atomMatrix_zero]
        simp⟩
    omega
  obtain ⟨live, hlive⟩ := Function.ne_iff.mp hdirectionNonzero
  have hnonempty : (stressSupport direction).Nonempty :=
    ⟨live, mem_stressSupport_iff.mpr (by simpa using hlive)⟩
  have hlower := Finset.card_pos.mpr hnonempty
  exact ⟨by omega, hvanish⟩

/-- **Rank one: the support is a parallel pair.** -/
theorem card_stressSupport_le_two_of_finrank_eq_one (atomFamily : Fin n → Fin k → ℝ)
    {direction : Fin n → ℝ}
    (hunique : ∀ stress : Fin n → ℝ, (∑ c, stress c • atomMatrix (atomFamily c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction)
    (hrank : Module.finrank ℝ (supportSpan atomFamily direction) = 1) :
    (stressSupport direction).card ≤ 2 := by
  obtain ⟨generator, hgenerator⟩ := exists_generator_of_finrank_eq_one hrank
  refine card_stressSupport_le_of_generators atomFamily hunique
    (generatorCount := 1) (fun _ => atomMatrix generator) fun c hc => ?_
  obtain ⟨scalar, hscalar⟩ := hgenerator (atomFamily c) (atom_mem_supportSpan atomFamily hc)
  exact ⟨fun _ => scalar ^ 2, by
    rw [matrixCombinationMap_apply, hscalar, atomMatrix_smul]
    simp⟩

/-- **Rank two: the support is a coplanar conic-dependent quadruple.**  The three
symmetric products of a generating pair span every supported atom matrix, so the
support is capped at four -- and the span-relative split law floors it at four. -/
theorem card_stressSupport_le_four_of_finrank_eq_two (atomFamily : Fin n → Fin k → ℝ)
    {direction : Fin n → ℝ}
    (hunique : ∀ stress : Fin n → ℝ, (∑ c, stress c • atomMatrix (atomFamily c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction)
    (hrank : Module.finrank ℝ (supportSpan atomFamily direction) = 2) :
    (stressSupport direction).card ≤ 4 := by
  obtain ⟨firstGenerator, secondGenerator, hpair⟩ :=
    exists_generating_pair_of_finrank_eq_two hrank
  refine card_stressSupport_le_of_generators atomFamily hunique (generatorCount := 3)
    ![Matrix.vecMulVec firstGenerator firstGenerator,
      Matrix.vecMulVec firstGenerator secondGenerator
        + Matrix.vecMulVec secondGenerator firstGenerator,
      Matrix.vecMulVec secondGenerator secondGenerator] fun c hc => ?_
  obtain ⟨alpha, beta, hcombination⟩ :=
    hpair (atomFamily c) (atom_mem_supportSpan atomFamily hc)
  refine ⟨![alpha ^ 2, alpha * beta, beta ^ 2], ?_⟩
  rw [matrixCombinationMap_apply, hcombination, atomMatrix_pair_expansion]
  simp [Fin.sum_univ_three, smul_add, add_assoc]

/-! ## Part 5: the strata at `(7,3)` -/

/-- The supported atoms admit a common nonzero orthogonal probe: the support is
confined to a proper subspace. -/
def hasCoplanarSupport (atomFamily : Fin n → Fin k → ℝ) (stressCoeff : Fin n → ℝ) : Prop :=
  ∃ probe : Fin k → ℝ, probe ≠ 0 ∧ ∀ c, stressCoeff c ≠ 0 → atomFamily c ⬝ᵥ probe = 0

/-- The supported atoms span: no nonzero probe annihilates them all. -/
def hasSpanningSupport (atomFamily : Fin n → Fin k → ℝ) (stressCoeff : Fin n → ℝ) : Prop :=
  ∀ probe : Fin k → ℝ, (∀ c, stressCoeff c ≠ 0 → atomFamily c ⬝ᵥ probe = 0) → probe = 0

/-- Two distinct labels carry parallel atoms.  Family-level twin of the shipped
`Gtz.HasParallelPair`, which is this predicate at `atomFamily = design.atom`. -/
def hasParallelAtomPair (atomFamily : Fin n → Fin k → ℝ) : Prop :=
  ∃ (keptLabel dropLabel : Fin n) (ratio : ℝ),
    keptLabel ≠ dropLabel ∧ atomFamily dropLabel = ratio • atomFamily keptLabel

theorem hasParallelPair_iff_hasParallelAtomPair {size rank : ℕ} (design : WeightedDesign size rank) :
    HasParallelPair design ↔ hasParallelAtomPair design.atom := Iff.rfl

/-- **A spanning support has a full-dimensional span.**  Converse of
`Gtz.hasSpanningSupport_of_finrank_eq`: a deficient span would leave a generating
list shorter than the rank, and rank-nullity would hand back the very probe the
spanning hypothesis forbids. -/
theorem finrank_supportSpan_eq_of_hasSpanningSupport (atomFamily : Fin n → Fin k → ℝ)
    (stressCoeff : Fin n → ℝ) (hspanning : hasSpanningSupport atomFamily stressCoeff) :
    Module.finrank ℝ (supportSpan atomFamily stressCoeff) = k := by
  have hle : Module.finrank ℝ (supportSpan atomFamily stressCoeff) ≤ k := by
    have hbound := Submodule.finrank_le (supportSpan atomFamily stressCoeff)
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hbound
  by_contra hne
  have hlt : Module.finrank ℝ (supportSpan atomFamily stressCoeff) < k := by omega
  obtain ⟨generator, hrepresents⟩ :=
    exists_representation_of_finrank_eq (subspace := supportSpan atomFamily stressCoeff) rfl
  obtain ⟨probe, hprobeNonzero, hprobeOrthogonal⟩ :=
    exists_ne_zero_orthogonal_of_card_lt generator Finset.univ (by simpa using hlt)
  exact hprobeNonzero (hspanning probe fun c hc =>
    dotProduct_eq_zero_of_generators_orthogonal hrepresents
      (fun index => hprobeOrthogonal index (Finset.mem_univ index))
      (atom_mem_supportSpan atomFamily hc))

/-- **THE LANDED SPLIT LAW, RECOVERED AND SHARPENED.**  `Gtz.rank_le_card_pos_side`
asks that the WHOLE family span and that the stress have FULL support; the
span-relative law needs only that the SUPPORT spans, and delivers the same
conclusion.  Nothing is lost in the generalisation, and the two discarded
hypotheses are exactly what the coplanar and low-rank strata violate. -/
theorem rank_le_card_positiveSide_of_hasSpanningSupport (atomFamily : Fin n → Fin k → ℝ)
    {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0)
    (hspanning : hasSpanningSupport atomFamily stressCoeff) :
    k ≤ (Finset.univ.filter fun c => 0 < stressCoeff c).card := by
  have hrank := finrank_supportSpan_eq_of_hasSpanningSupport atomFamily stressCoeff hspanning
  have hbound := finrank_supportSpan_le_card_positiveSide atomFamily hstress
  omega

/-- A support span of full dimension is a spanning support. -/
theorem hasSpanningSupport_of_finrank_eq (atomFamily : Fin n → Fin k → ℝ)
    (stressCoeff : Fin n → ℝ)
    (hrank : Module.finrank ℝ (supportSpan atomFamily stressCoeff) = k) :
    hasSpanningSupport atomFamily stressCoeff := by
  have htop : supportSpan atomFamily stressCoeff = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  intro probe horthogonal
  refine eq_zero_of_mem_supportSpan_of_orthogonal atomFamily stressCoeff ?_ horthogonal
  rw [htop]
  exact Submodule.mem_top

/-- A two-dimensional support span inside a rank of at least three is coplanar:
the generating pair leaves an orthogonal probe by rank-nullity, and every
supported atom is a combination of the pair. -/
theorem hasCoplanarSupport_of_finrank_eq_two (atomFamily : Fin n → Fin k → ℝ)
    (stressCoeff : Fin n → ℝ) (hrankLarge : 2 < k)
    (hrank : Module.finrank ℝ (supportSpan atomFamily stressCoeff) = 2) :
    hasCoplanarSupport atomFamily stressCoeff := by
  obtain ⟨firstGenerator, secondGenerator, hpair⟩ :=
    exists_generating_pair_of_finrank_eq_two hrank
  obtain ⟨probe, hprobeNonzero, hprobeOrthogonal⟩ :=
    exists_ne_zero_orthogonal_of_card_lt ![firstGenerator, secondGenerator]
      Finset.univ (by simpa using hrankLarge)
  refine ⟨probe, hprobeNonzero, fun c hc => ?_⟩
  obtain ⟨alpha, beta, hcombination⟩ :=
    hpair (atomFamily c) (atom_mem_supportSpan atomFamily hc)
  have hfirst : firstGenerator ⬝ᵥ probe = 0 := by
    simpa using hprobeOrthogonal 0 (Finset.mem_univ 0)
  have hsecond : secondGenerator ⬝ᵥ probe = 0 := by
    simpa using hprobeOrthogonal 1 (Finset.mem_univ 1)
  rw [hcombination, add_dotProduct, smul_dotProduct, smul_dotProduct, hfirst, hsecond]
  simp

/-- **Rank at most one forces a parallel pair.**  At rank zero the single
supported atom is zero, which is parallel to anything; at rank one the two
supported atoms are multiples of one generator. -/
theorem hasParallelAtomPair_of_finrank_le_one (atomFamily : Fin n → Fin k → ℝ)
    {direction : Fin n → ℝ} (hdirectionNonzero : direction ≠ 0) (hsize : 1 < n)
    (hdirectionStress : ∑ c, direction c • atomMatrix (atomFamily c) = 0)
    (hunique : ∀ stress : Fin n → ℝ, (∑ c, stress c • atomMatrix (atomFamily c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction)
    (hrank : Module.finrank ℝ (supportSpan atomFamily direction) ≤ 1) :
    hasParallelAtomPair atomFamily := by
  have hcases : Module.finrank ℝ (supportSpan atomFamily direction) = 0
      ∨ Module.finrank ℝ (supportSpan atomFamily direction) = 1 := by omega
  rcases hcases with hzero | hone
  · obtain ⟨_, hvanish⟩ :=
      card_stressSupport_eq_one_of_finrank_eq_zero atomFamily hdirectionNonzero hunique hzero
    obtain ⟨live, hlive⟩ := Function.ne_iff.mp hdirectionNonzero
    have hliveNonzero : direction live ≠ 0 := by simpa using hlive
    obtain ⟨other, hother⟩ := Fintype.exists_ne_of_one_lt_card (by simpa using hsize) live
    exact ⟨other, live, 0, hother, by rw [hvanish live hliveNonzero, zero_smul]⟩
  · obtain ⟨generator, hgenerator⟩ := exists_generator_of_finrank_eq_one hone
    have hlower :=
      twice_finrank_supportSpan_le_card_stressSupport atomFamily hdirectionStress
    rw [hone] at hlower
    obtain ⟨first, hfirstMem, second, hsecondMem, hdistinct⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (stressSupport direction).card)
    obtain ⟨alpha, halpha⟩ := hgenerator (atomFamily first)
      (atom_mem_supportSpan atomFamily (mem_stressSupport_iff.mp hfirstMem))
    obtain ⟨beta, hbeta⟩ := hgenerator (atomFamily second)
      (atom_mem_supportSpan atomFamily (mem_stressSupport_iff.mp hsecondMem))
    by_cases halphaZero : alpha = 0
    · exact ⟨second, first, 0, hdistinct.symm, by
        rw [halpha, halphaZero, zero_smul, zero_smul]⟩
    · refine ⟨first, second, beta / alpha, hdistinct, ?_⟩
      rw [hbeta, halpha, smul_smul, div_mul_cancel₀ _ halphaZero]

/-! ## Part 6: the taxonomy and its impossibilities -/

/-- **THE STRATA OF A UNIQUE-STRESS `(7,3)` FAMILY.**  A seven-atom rank-three
family whose stress space is the line through `direction` falls into exactly
five strata, indexed by the support size, and each carries its sign split:

* `s = 1` -- a ZERO ATOM (its indicator is the stress), hence a parallel pair;
* `s = 2` -- a PARALLEL PAIR, split `(1,1)`;
* `s = 4` -- a COPLANAR quadruple, split `(2,2)`, three free atoms;
* `s = 6` -- a SPANNING sextuple, split `(3,3)`, one free atom;
* `s = 7` -- SPANNING, split `(3,4)` up to sign: THE MAIN STRATUM.

Sizes three and five are absent, and this is not a case analysis that happened
to come out empty: they are excluded by the two inequalities
`2r <= s <= (Veronese bound at r) + 1` with no room left at any `r`.

Parseval is never used -- the taxonomy is a statement about the atom family and
its stress line alone, so it applies verbatim to the design-level cell through
`Gtz.uniqueStress_sevenThree_trichotomy`.  Nothing here assumes
`GtzWeighted 6 3`, which would trivialise the `(7,3)` cell outright. -/
theorem uniqueStress_support_taxonomy (atomFamily : Fin 7 → Fin 3 → ℝ)
    {direction : Fin 7 → ℝ} (hdirectionNonzero : direction ≠ 0)
    (hdirectionStress : ∑ c, direction c • atomMatrix (atomFamily c) = 0)
    (hunique : ∀ stress : Fin 7 → ℝ, (∑ c, stress c • atomMatrix (atomFamily c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction) :
    ((stressSupport direction).card = 1
        ∧ (∃ zeroLabel : Fin 7, atomFamily zeroLabel = 0)
        ∧ hasParallelAtomPair atomFamily)
    ∨ ((stressSupport direction).card = 2 ∧ hasParallelAtomPair atomFamily
        ∧ (Finset.univ.filter fun c => 0 < direction c).card = 1
        ∧ (Finset.univ.filter fun c => direction c < 0).card = 1)
    ∨ ((stressSupport direction).card = 4 ∧ hasCoplanarSupport atomFamily direction
        ∧ (Finset.univ.filter fun c => 0 < direction c).card = 2
        ∧ (Finset.univ.filter fun c => direction c < 0).card = 2)
    ∨ ((stressSupport direction).card = 6 ∧ hasSpanningSupport atomFamily direction
        ∧ (Finset.univ.filter fun c => 0 < direction c).card = 3
        ∧ (Finset.univ.filter fun c => direction c < 0).card = 3)
    ∨ ((stressSupport direction).card = 7 ∧ hasSpanningSupport atomFamily direction
        ∧ (((Finset.univ.filter fun c => 0 < direction c).card = 3
              ∧ (Finset.univ.filter fun c => direction c < 0).card = 4)
          ∨ ((Finset.univ.filter fun c => 0 < direction c).card = 4
              ∧ (Finset.univ.filter fun c => direction c < 0).card = 3))) := by
  have hpositive := finrank_supportSpan_le_card_positiveSide atomFamily hdirectionStress
  have hnegative := finrank_supportSpan_le_card_negativeSide atomFamily hdirectionStress
  have hpartition := card_positiveSide_add_card_negativeSide direction
  have hlower := twice_finrank_supportSpan_le_card_stressSupport atomFamily hdirectionStress
  have hrankLe : Module.finrank ℝ (supportSpan atomFamily direction) ≤ 3 := by
    have hle := Submodule.finrank_le (supportSpan atomFamily direction)
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
  have hcardLe : (stressSupport direction).card ≤ 7 := by
    simpa using Finset.card_le_univ (stressSupport direction)
  have hcases : Module.finrank ℝ (supportSpan atomFamily direction) = 0
      ∨ Module.finrank ℝ (supportSpan atomFamily direction) = 1
      ∨ Module.finrank ℝ (supportSpan atomFamily direction) = 2
      ∨ Module.finrank ℝ (supportSpan atomFamily direction) = 3 := by omega
  rcases hcases with hzero | hone | htwo | hthree
  · obtain ⟨hcard, hvanish⟩ :=
      card_stressSupport_eq_one_of_finrank_eq_zero atomFamily hdirectionNonzero hunique hzero
    obtain ⟨live, hlive⟩ := Function.ne_iff.mp hdirectionNonzero
    exact Or.inl ⟨hcard, ⟨live, hvanish live (by simpa using hlive)⟩,
      hasParallelAtomPair_of_finrank_le_one atomFamily hdirectionNonzero (by norm_num)
        hdirectionStress hunique (by omega)⟩
  · have hupper := card_stressSupport_le_two_of_finrank_eq_one atomFamily hunique hone
    rw [hone] at hpositive hnegative hlower
    exact Or.inr (Or.inl ⟨by omega,
      hasParallelAtomPair_of_finrank_le_one atomFamily hdirectionNonzero (by norm_num)
        hdirectionStress hunique (by omega),
      by omega, by omega⟩)
  · have hupper := card_stressSupport_le_four_of_finrank_eq_two atomFamily hunique htwo
    rw [htwo] at hpositive hnegative hlower
    exact Or.inr (Or.inr (Or.inl ⟨by omega,
      hasCoplanarSupport_of_finrank_eq_two atomFamily direction (by norm_num) htwo,
      by omega, by omega⟩))
  · have hspanning := hasSpanningSupport_of_finrank_eq atomFamily direction hthree
    rw [hthree] at hpositive hnegative hlower
    have hsplit : (stressSupport direction).card = 6 ∨ (stressSupport direction).card = 7 := by
      omega
    rcases hsplit with hsix | hseven
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hsix, hspanning, by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hseven, hspanning, by omega⟩)))

/-- **Support three is impossible at every support rank.**  Rank zero and one
cap the support at one and two; rank two already needs four labels by the
span-relative split law. -/
theorem card_stressSupport_ne_three (atomFamily : Fin 7 → Fin 3 → ℝ)
    {direction : Fin 7 → ℝ} (hdirectionNonzero : direction ≠ 0)
    (hdirectionStress : ∑ c, direction c • atomMatrix (atomFamily c) = 0)
    (hunique : ∀ stress : Fin 7 → ℝ, (∑ c, stress c • atomMatrix (atomFamily c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction) :
    (stressSupport direction).card ≠ 3 := by
  rcases uniqueStress_support_taxonomy atomFamily hdirectionNonzero hdirectionStress hunique with
    ⟨hcard, _⟩ | ⟨hcard, _⟩ | ⟨hcard, _⟩ | ⟨hcard, _⟩ | ⟨hcard, _⟩ <;> omega

/-- **Support five is impossible at every support rank.**  Rank two caps it at
four and rank three floors it at six -- the gap the two inequalities leave. -/
theorem card_stressSupport_ne_five (atomFamily : Fin 7 → Fin 3 → ℝ)
    {direction : Fin 7 → ℝ} (hdirectionNonzero : direction ≠ 0)
    (hdirectionStress : ∑ c, direction c • atomMatrix (atomFamily c) = 0)
    (hunique : ∀ stress : Fin 7 → ℝ, (∑ c, stress c • atomMatrix (atomFamily c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction) :
    (stressSupport direction).card ≠ 5 := by
  rcases uniqueStress_support_taxonomy atomFamily hdirectionNonzero hdirectionStress hunique with
    ⟨hcard, _⟩ | ⟨hcard, _⟩ | ⟨hcard, _⟩ | ⟨hcard, _⟩ | ⟨hcard, _⟩ <;> omega

/-- The support size of a unique stress at `(7,3)` takes exactly five values. -/
theorem card_stressSupport_mem_strata (atomFamily : Fin 7 → Fin 3 → ℝ)
    {direction : Fin 7 → ℝ} (hdirectionNonzero : direction ≠ 0)
    (hdirectionStress : ∑ c, direction c • atomMatrix (atomFamily c) = 0)
    (hunique : ∀ stress : Fin 7 → ℝ, (∑ c, stress c • atomMatrix (atomFamily c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction) :
    (stressSupport direction).card = 1 ∨ (stressSupport direction).card = 2
      ∨ (stressSupport direction).card = 4 ∨ (stressSupport direction).card = 6
      ∨ (stressSupport direction).card = 7 := by
  rcases uniqueStress_support_taxonomy atomFamily hdirectionNonzero hdirectionStress hunique with
    ⟨hcard, _⟩ | ⟨hcard, _⟩ | ⟨hcard, _⟩ | ⟨hcard, _⟩ | ⟨hcard, _⟩ <;> omega

/-- **THE `(7,3)` UNIQUE-STRESS TRICHOTOMY, at design level.**  Every design
whose stress space is a line either carries a PARALLEL PAIR -- the two low
strata collapse into one clause -- or has a coplanar support of exactly four
atoms with split `(2,2)`, or a spanning support of six with split `(3,3)`, or
the main stratum: full support with split `(3,4)` up to sign.

This is the `(7,3)` analogue of the `(6,3)` stress trichotomy, and it is the
shape the hinge consumes: everything below the top two strata already has the
parallel pair the hinge asks for, so a unique-stress `(7,3)` TIE that refutes
the hinge must live on the coplanar quadruple or on a spanning support. -/
theorem uniqueStress_sevenThree_trichotomy (design : WeightedDesign 7 3)
    {direction : Fin 7 → ℝ} (hdirectionNonzero : direction ≠ 0)
    (hdirectionStress : ∑ c, direction c • atomMatrix (design.atom c) = 0)
    (hunique : ∀ stress : Fin 7 → ℝ, (∑ c, stress c • atomMatrix (design.atom c)) = 0 →
      ∃ ratio : ℝ, stress = ratio • direction) :
    HasParallelPair design
    ∨ ((stressSupport direction).card = 4 ∧ hasCoplanarSupport design.atom direction
        ∧ (Finset.univ.filter fun c => 0 < direction c).card = 2
        ∧ (Finset.univ.filter fun c => direction c < 0).card = 2)
    ∨ ((stressSupport direction).card = 6 ∧ hasSpanningSupport design.atom direction
        ∧ (Finset.univ.filter fun c => 0 < direction c).card = 3
        ∧ (Finset.univ.filter fun c => direction c < 0).card = 3)
    ∨ ((stressSupport direction).card = 7 ∧ hasSpanningSupport design.atom direction
        ∧ (((Finset.univ.filter fun c => 0 < direction c).card = 3
              ∧ (Finset.univ.filter fun c => direction c < 0).card = 4)
          ∨ ((Finset.univ.filter fun c => 0 < direction c).card = 4
              ∧ (Finset.univ.filter fun c => direction c < 0).card = 3))) := by
  rcases uniqueStress_support_taxonomy design.atom hdirectionNonzero hdirectionStress hunique with
    ⟨_, _, hpair⟩ | ⟨_, hpair, _⟩ | hcoplanar | hsix | hseven
  · exact Or.inl ((hasParallelPair_iff_hasParallelAtomPair design).mpr hpair)
  · exact Or.inl ((hasParallelPair_iff_hasParallelAtomPair design).mpr hpair)
  · exact Or.inr (Or.inl hcoplanar)
  · exact Or.inr (Or.inr (Or.inl hsix))
  · exact Or.inr (Or.inr (Or.inr hseven))

/-! ## Part 7: domination without the middle matrix -/

/-- **DOMINATION IS PARSEVAL SUBSTITUTION.**  `S_C >= I` says exactly that the
selected atoms outweigh the complementary ones once each selected atom is
discounted by its own weight,

    sum_{c in C} (1 - t_c) A_c  >=  sum_{c not in C} t_c A_c,

because `I` IS the weighted atom sum.  No middle matrix, no whitening, no square
root, and no hypothesis beyond `Gtz.WeightedDesign`.

This is the syzygy lane's `X`-free law `(D_C)` at full generality.  The lane
derived it on the `(7,3)` main stratum by congruence through `X^(1/2)` after
whitening the stress sides -- candidate T2 feeding candidate T3.  That route is
UNNECESSARY: the identity holds at every size, every rank and every stratum,
so the whitening normal form is not on the critical path of the domination
criterion, only of the free parametrization used for search. -/
theorem dominates_iff_forall_discountedMoment_ge {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size)) :
    Dominates design selected ↔ ∀ probe : Fin rank → ℝ,
      ∑ c ∈ selectedᶜ, design.weight c * momentCoord design c probe
        ≤ ∑ c ∈ selected, (1 - design.weight c) * momentCoord design c probe := by
  classical
  rw [dominates_iff_forall_moment_ge]
  refine forall_congr' fun probe => ?_
  have hsplit : ∑ c ∈ selected, design.weight c * momentCoord design c probe
      + ∑ c ∈ selectedᶜ, design.weight c * momentCoord design c probe
      = probe ⬝ᵥ probe := by
    rw [Finset.sum_add_sum_compl]
    exact sum_weight_mul_momentCoord design probe
  have hdiscount : ∑ c ∈ selected, (1 - design.weight c) * momentCoord design c probe
      = ∑ c ∈ selected, momentCoord design c probe
        - ∑ c ∈ selected, design.weight c * momentCoord design c probe := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hdiscount]
  constructor
  · intro hdominates
    linarith
  · intro hdiscounted
    linarith
end Gtz
