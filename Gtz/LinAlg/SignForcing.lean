/-
# Sign forcing: the obtuse bound, and the triangle whose product is positive

Two classical facts about REAL vector configurations, mechanised here because the
campaign's certificate layer has run out of room at the sign-blind wall
(`not_signBlindGoodTripleCovering_seven`): every certificate that reads only
`|p_cd|` is refuted, so the only material left is the SIGN of the oriented triple
product `p_ab p_ac p_bc`. This file supplies the first two theorems of the
campaign that produce such a sign.

* **The obtuse bound (T5).** At most `dim + 1` vectors of a `dim`-dimensional
  real coordinate space pair strictly negatively in pairs. Proved by linear
  independence, not by the textbook dimension induction: given one extra vector
  to use as a test functional, a vanishing combination of the rest must have all
  coefficients of one sign (else its positive part is a vector of nonpositive
  square, hence zero) and then pairing that positive part against the test vector
  forces the positive part to be empty. Attributed to Rankin, *The closest packing
  of spherical caps in n dimensions*, Proc. Glasgow Math. Assoc. 2 (1955) 139-144.
  The constant is EXACT at every dimension: `isPairwiseObtuse_obtuseSimplexAtom`
  exhibits `dim + 1` pairwise-obtuse vectors, namely `e_b - 1/(2 dim)` for each
  coordinate `b` together with the constant vector `-1`, with pairings
  `-3/(4 dim)` and `-1/2`. `isPairwiseObtuse_tetraAtom` is the campaign's own
  tetrahedron doing the same at `dim = 3`.

* **Lemma A, sign forcing (T6).** Any `dim + 2` vectors in `R^dim` whose pairings
  are all nonzero carry a triple with `p_ab p_ac p_bc > 0`. Negate each vector by
  the sign that makes its pairing with a fixed base vector negative; the triangle
  hypothesis then makes ALL pairings negative, and the obtuse bound caps the
  family at `dim + 1`. The gauge freedom used is Seidel switching, and
  `triangleProduct_smul` is the statement that the triangle product is its
  invariant -- so this is a statement about the two-graph of the configuration,
  not about the chosen signs. Standard background: van Lint-Seidel, Indag. Math.
  28 (1966) 335-348; Seidel, *A survey of two-graphs*, Atti Convegni Lincei 17
  (1976) 481-511. The threshold `dim + 2` is sharp
  (`not_exists_pos_triangleProduct_tetraAtom`: at `dim = 3` the four tetrahedron
  vertices have all pairings nonzero and every triangle product equal to `-1`),
  and the nonzero hypothesis may be dropped at the cost of one strict inequality
  (`exists_nonneg_triangleProduct_of_card_ge`).

## The field door

Both theorems are stated over an arbitrary finite coordinate index, so they apply
verbatim to `C^dim` viewed as `R^(2 dim)` through `realifyComplexVector`. That is
where the real/complex separation becomes a number: over `R^3` the obtuse bound
is `4` and sign forcing starts at `5` atoms, while over `C^3` the bound is `7` and
sign forcing starts at `8`. Each threshold is exactly one past its bound, because
forcing assumes `dim + 2` atoms over `R` and `2 dim + 2` over `C` -- read the
hypotheses of `exists_pos_triangleProduct_of_card_ge` and
`exists_pos_realTriangleProduct_of_complex_card_ge`, which is where those two
numbers actually live. The complex constant `2 dim + 1` is EXACT, upper
bound by `card_le_two_mul_add_one_of_isPairwiseObtuseComplex` and attainment by
`isPairwiseObtuseComplex_complexifiedSimplex`, which complexifies the real
simplex of `R^(2 dim)`.

So the window in which the real argument has force and the complex one does not is
`m = 5, 6, 7`, and the two campaign counterexamples fall on OPPOSITE sides of it.
`m = 6` (`Gtz.trineDesign`) is inside. `m = 9` (the Hesse SIC) is NOT: nine atoms
is past the complex threshold of eight, so what spares it is the theorem's OTHER
hypothesis -- every pairwise real part nonzero, which a SIC need not satisfy --
and not its size. This docstring read `9` for the threshold and placed both
counterexamples inside the gap; both statements were wrong, while the bound `7`
beside them was right. Either way an argument entering here is not replayable
over `C` at the sizes that matter, and is therefore not touched by
`phaseFree_certificates_cannot_prove_rank_three`. The complex failure
is a remark about the SIZE THRESHOLD, proved here as
`exists_pos_realTriangleProduct_of_complex_card_ge`; no claim is made that Lemma A
itself is false over `C`, because no complex counterexample to it is exhibited.

## What the sign buys, at a rank-three design

`dominates_of_coherentHalfBoxTriangle` is the payoff and it is a genuinely new
certificate cell: a COHERENT triple (nonnegative oriented product) dominates as
soon as `2 p^2 <= u u` on all three edges, where the shipped sign-blind box
`dominates_of_dominantPairings` demands `4 p^2 <= u u`. The threshold `1/2` on
`rho^2` is SHARP (`exists_elliptopeBracket_neg_of_half_lt`), the cell is strictly
larger than the box in the coherent sector, and it is not sign-blind, so the
refutation of `IsSignBlindGoodTriple` does not reach it. Concretely it certifies
the icosahedron's ten coherent triples, where `rho^2 = 9/20 > 1/4`
(`icosaDesign_normalizedPairing_sq_of_ne`) puts every pair outside the box --
`icosaDesign_no_isBoxGoodPair` records that the box graph there is EMPTY.

This is an ENABLING PRIMITIVE, not a closure. Coherence alone certifies nothing:
`(99/100, 99/100, 1/10)` is compatible and coherent with a strictly negative
bracket, and every triple through a repeated atom is coherent while
`not_dominates_of_repeated_atom` forbids it from dominating. Nothing here
lower-bounds the oriented product against the excess gap, and that bound is the
open problem.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Quantitative.GoodTripleGraph

namespace Gtz

open Matrix

/-! ## The dot product over an arbitrary finite coordinate index

`Gtz.dotProduct_self_nonneg` and `Gtz.eq_zero_of_dotProduct_self_eq_zero` in
`Gtz/LinAlg/PsdKit.lean` are stated for `Fin dim -> R`. The obtuse bound has
nothing to do with `Fin`, and stating it over an arbitrary `Fintype` coordinate
index is what lets the complex case reuse it with the coordinate index
`coord + coord`. These two are the only facts about the form that the argument
consumes. -/

/-- The dot square is nonnegative, over any finite coordinate index. -/
theorem dotProduct_self_nonneg_fintype {coord : Type*} [Fintype coord]
    (vector : coord → ℝ) : 0 ≤ vector ⬝ᵥ vector :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- A vanishing dot square forces the zero vector, over any finite coordinate
index: some coordinate would otherwise contribute a strictly positive term to a
sum of nonnegative ones. -/
theorem eq_zero_of_dotProduct_self_eq_zero_fintype {coord : Type*} [Fintype coord]
    {vector : coord → ℝ} (hself : vector ⬝ᵥ vector = 0) : vector = 0 := by
  by_contra hne
  obtain ⟨badCoord, hbadCoord⟩ := Function.ne_iff.mp hne
  simp only [Pi.zero_apply] at hbadCoord
  have hpos : 0 < vector ⬝ᵥ vector :=
    Finset.sum_pos' (fun _ _ => mul_self_nonneg _)
      ⟨badCoord, Finset.mem_univ badCoord, mul_self_pos.mpr hbadCoord⟩
  exact absurd hself (ne_of_gt hpos)

/-! ## T5: pairwise obtuse families and the `dim + 1` bound -/

/-- A family of real coordinate vectors is **pairwise obtuse** when every two
distinct members pair strictly negatively. Note this already forces every member
nonzero as soon as the family has two elements, so no nondegeneracy hypothesis is
ever needed alongside it. -/
def IsPairwiseObtuse {atomIndex coord : Type*} [Fintype coord]
    (vec : atomIndex → (coord → ℝ)) : Prop :=
  ∀ first second : atomIndex, first ≠ second → vec first ⬝ᵥ vec second < 0

/-- **The one-sided relation lemma.** If the family is pairwise obtuse and every
member also pairs negatively against a test vector, then every vanishing real
combination of the family has NONPOSITIVE coefficients.

The pen argument: split the index set on the sign of the coefficient. The
positive part equals the negation of the nonpositive part, so its dot square is
a double sum of terms `(positive) * (nonpositive) * (negative pairing)`, all
nonpositive; being also nonnegative it vanishes, and so does the positive part
itself. Pairing that zero vector against the test vector makes a sum of strictly
negative terms vanish, which forces the positive part to have been empty. -/
theorem forall_coef_nonpos_of_obtuseRelation {atomIndex coord : Type*}
    [Fintype atomIndex] [Fintype coord] {vec : atomIndex → (coord → ℝ)}
    (hobtuse : IsPairwiseObtuse vec) {testVector : coord → ℝ}
    (htest : ∀ index, vec index ⬝ᵥ testVector < 0) {coef : atomIndex → ℝ}
    (hrelation : ∑ index, coef index • vec index = 0) :
    ∀ index, coef index ≤ 0 := by
  classical
  set positiveIndices := Finset.univ.filter (fun index => 0 < coef index) with hpositiveIndices
  set remainingIndices := Finset.univ.filter (fun index => ¬ (0 < coef index)) with hremainingIndices
  set positivePart := ∑ index ∈ positiveIndices, coef index • vec index with hpositivePart
  set remainingPart := ∑ index ∈ remainingIndices, coef index • vec index with hremainingPart
  have hsplit : positivePart + remainingPart = 0 := by
    rw [hpositivePart, hremainingPart, hpositiveIndices, hremainingIndices,
      Finset.sum_filter_add_sum_filter_not]
    exact hrelation
  have hcross : 0 ≤ positivePart ⬝ᵥ remainingPart := by
    rw [hpositivePart, sum_dotProduct]
    refine Finset.sum_nonneg fun leftIndex hleft => ?_
    have hleftPos : 0 < coef leftIndex := by
      have := Finset.mem_filter.mp (hpositiveIndices ▸ hleft)
      exact this.2
    rw [smul_dotProduct, smul_eq_mul, hremainingPart, dotProduct_sum]
    refine mul_nonneg hleftPos.le (Finset.sum_nonneg fun rightIndex hright => ?_)
    have hrightNonpos : coef rightIndex ≤ 0 := by
      have := Finset.mem_filter.mp (hremainingIndices ▸ hright)
      exact not_lt.mp this.2
    have hne : leftIndex ≠ rightIndex := by
      rintro rfl
      exact absurd hleftPos (not_lt.mpr hrightNonpos)
    rw [dotProduct_smul, smul_eq_mul]
    have hbothNegated : 0 ≤ (-(coef rightIndex)) * (-(vec leftIndex ⬝ᵥ vec rightIndex)) :=
      mul_nonneg (neg_nonneg.mpr hrightNonpos) (neg_nonneg.mpr (hobtuse _ _ hne).le)
    have hcancelSigns : (-(coef rightIndex)) * (-(vec leftIndex ⬝ᵥ vec rightIndex))
        = coef rightIndex * (vec leftIndex ⬝ᵥ vec rightIndex) := by ring
    rw [← hcancelSigns]
    exact hbothNegated
  have hexpand : positivePart ⬝ᵥ positivePart + positivePart ⬝ᵥ remainingPart = 0 := by
    rw [← dotProduct_add, hsplit, dotProduct_zero]
  have hpositivePartZero : positivePart = 0 :=
    eq_zero_of_dotProduct_self_eq_zero_fintype
      (le_antisymm (by linarith) (dotProduct_self_nonneg_fintype positivePart))
  intro index
  by_contra hcontra
  have hmem : index ∈ positiveIndices :=
    hpositiveIndices ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ index, not_le.mp hcontra⟩
  have htestZero : positivePart ⬝ᵥ testVector = 0 := by
    rw [hpositivePartZero, zero_dotProduct]
  rw [hpositivePart, sum_dotProduct] at htestZero
  have hstrict : ∑ i ∈ positiveIndices, (coef i • vec i) ⬝ᵥ testVector
      < ∑ _i ∈ positiveIndices, (0 : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty ⟨index, hmem⟩ fun i hi => ?_
    have hiPos : 0 < coef i := by
      have := Finset.mem_filter.mp (hpositiveIndices ▸ hi)
      exact this.2
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hiPos (htest i)
  rw [Finset.sum_const_zero, htestZero] at hstrict
  exact lt_irrefl 0 hstrict

/-- Both signs of the relation lemma: a vanishing combination is trivial. -/
theorem forall_coef_eq_zero_of_obtuseRelation {atomIndex coord : Type*}
    [Fintype atomIndex] [Fintype coord] {vec : atomIndex → (coord → ℝ)}
    (hobtuse : IsPairwiseObtuse vec) {testVector : coord → ℝ}
    (htest : ∀ index, vec index ⬝ᵥ testVector < 0) {coef : atomIndex → ℝ}
    (hrelation : ∑ index, coef index • vec index = 0) :
    ∀ index, coef index = 0 := by
  have hnegRelation : ∑ index, (-coef index) • vec index = 0 := by
    simp only [neg_smul, Finset.sum_neg_distrib, hrelation, neg_zero]
  intro index
  have hupper := forall_coef_nonpos_of_obtuseRelation hobtuse htest hrelation index
  have hlower := forall_coef_nonpos_of_obtuseRelation hobtuse htest hnegRelation index
  simp only [neg_nonpos] at hlower
  linarith

/-- A pairwise-obtuse family admitting a test vector is linearly independent. -/
theorem linearIndependent_of_isPairwiseObtuse_of_testVector {atomIndex coord : Type*}
    [Fintype atomIndex] [Fintype coord] {vec : atomIndex → (coord → ℝ)}
    (hobtuse : IsPairwiseObtuse vec) {testVector : coord → ℝ}
    (htest : ∀ index, vec index ⬝ᵥ testVector < 0) :
    LinearIndependent ℝ vec := by
  rw [Fintype.linearIndependent_iff]
  intro coef hrelation
  exact forall_coef_eq_zero_of_obtuseRelation hobtuse htest hrelation

/-- The dimension count behind the obtuse bound: a pairwise-obtuse family with a
test vector has at most `dim` members. -/
theorem card_le_of_isPairwiseObtuse_of_testVector {atomIndex coord : Type*}
    [Fintype atomIndex] [Fintype coord] {vec : atomIndex → (coord → ℝ)}
    (hobtuse : IsPairwiseObtuse vec) {testVector : coord → ℝ}
    (htest : ∀ index, vec index ⬝ᵥ testVector < 0) :
    Fintype.card atomIndex ≤ Fintype.card coord := by
  have hindependent := linearIndependent_of_isPairwiseObtuse_of_testVector hobtuse htest
  have hcard : Fintype.card atomIndex ≤ Module.finrank ℝ (coord → ℝ) :=
    hindependent.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card ℝ] at hcard

/-- **T5, THE OBTUSE BOUND.** At most `dim + 1` vectors of a real coordinate space
of dimension `dim` are pairwise obtuse. Sharp at every dimension; the case
`dim = 3` is `isPairwiseObtuse_tetraAtom`. -/
theorem card_le_succ_of_isPairwiseObtuse {atomIndex coord : Type*}
    [Fintype atomIndex] [Fintype coord] {vec : atomIndex → (coord → ℝ)}
    (hobtuse : IsPairwiseObtuse vec) :
    Fintype.card atomIndex ≤ Fintype.card coord + 1 := by
  classical
  rcases isEmpty_or_nonempty atomIndex with hempty | hnonempty
  · simp [Fintype.card_eq_zero]
  · obtain ⟨baseIndex⟩ := hnonempty
    have hrestObtuse : IsPairwiseObtuse (fun index : {i : atomIndex // i ≠ baseIndex} => vec index.val) := by
      intro first second hne
      exact hobtuse _ _ fun hval => hne (Subtype.ext hval)
    have hrestTest : ∀ index : {i : atomIndex // i ≠ baseIndex},
        vec index.val ⬝ᵥ vec baseIndex < 0 := fun index => hobtuse _ _ index.property
    have hrestCard := card_le_of_isPairwiseObtuse_of_testVector hrestObtuse hrestTest
    have hcomplement : Fintype.card {i : atomIndex // i ≠ baseIndex}
        = Fintype.card atomIndex - Fintype.card {i : atomIndex // i = baseIndex} :=
      Fintype.card_subtype_compl (fun i => i = baseIndex)
    have hsingleton : Fintype.card {i : atomIndex // i = baseIndex} = 1 :=
      Fintype.card_subtype_eq baseIndex
    have hbasePos : 0 < Fintype.card atomIndex := Fintype.card_pos_iff.mpr ⟨baseIndex⟩
    rw [hcomplement, hsingleton] at hrestCard
    omega

/-- The obtuse bound for a `Finset` of a possibly infinite index type: the same
theorem, with only the members of the `Finset` required to pair negatively. This
is the form a design-level consumer wants, since there the family is a subset of
the atom indices. -/
theorem card_le_succ_of_isPairwiseObtuse_on {atomIndex coord : Type*} [Fintype coord]
    {vec : atomIndex → (coord → ℝ)} (family : Finset atomIndex)
    (hobtuse : ∀ first ∈ family, ∀ second ∈ family, first ≠ second →
      vec first ⬝ᵥ vec second < 0) :
    family.card ≤ Fintype.card coord + 1 := by
  classical
  have hsubObtuse : IsPairwiseObtuse (fun index : {i // i ∈ family} => vec index.val) := by
    intro first second hne
    exact hobtuse _ first.property _ second.property fun hval => hne (Subtype.ext hval)
  have hcard := card_le_succ_of_isPairwiseObtuse hsubObtuse
  rwa [Fintype.card_coe] at hcard

/-! ### Sharpness of the obtuse bound at dimension three

The campaign's own regular tetrahedron is four pairwise-obtuse vectors of `R^3`,
so `dim + 1` cannot be lowered — and, since all four of its triangle products are
`-1`, Lemma A's threshold of `dim + 2 = 5` atoms cannot be lowered either. -/

/-- Distinct tetrahedron vertices pair to `-1`, signs included. The shipped
`tetraAtom_dot_sq_of_ne` records only the square. -/
theorem tetraAtom_dotProduct_eq_neg_one_of_ne {first second : Fin 4} (hne : first ≠ second) :
    tetraAtom first ⬝ᵥ tetraAtom second = -1 := by
  fin_cases first <;> fin_cases second <;>
    simp_all [tetraAtom, dotProduct, Fin.sum_univ_three]

/-- **The obtuse bound is attained at dimension three**: the four tetrahedron
vertices are pairwise obtuse in `R^3`, matching `card_le_succ_of_isPairwiseObtuse`
with equality. -/
theorem isPairwiseObtuse_tetraAtom : IsPairwiseObtuse tetraAtom := by
  intro first second hne
  rw [tetraAtom_dotProduct_eq_neg_one_of_ne hne]
  norm_num

/-! ### Sharpness at EVERY dimension: the regular simplex

The tetrahedron settles `dim = 3`. For a general finite coordinate index the
witness is `e_b - (1/2 dim) * 1` for each coordinate `b`, together with the single
extra vector `-1`. The two constants are forced by the two inequalities the
construction must satisfy — `d a^2 < 2 a` for the `some/some` edges and `a d < 1`
for the edges to the extra vector — and `a = 1/(2 dim)` satisfies both with room
to spare, giving pairings `-3/(4 dim)` and `-1/2`. -/

/-- The dot product of two constant vectors is the dimension times the product. -/
theorem dotProduct_constant {coord : Type*} [Fintype coord] (leftValue rightValue : ℝ) :
    (fun _ : coord => leftValue) ⬝ᵥ (fun _ : coord => rightValue)
      = (Fintype.card coord : ℝ) * (leftValue * rightValue) := by
  rw [dotProduct, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The regular simplex realising the obtuse bound: `dim` vectors `e_b - a * 1`
with `a = 1/(2 dim)`, plus the single vector `-1`. Indexed by `Option coord`, whose
cardinality is `dim + 1` on the nose. -/
noncomputable def obtuseSimplexAtom {coord : Type*} [Fintype coord] [DecidableEq coord] :
    Option coord → (coord → ℝ)
  | none => fun _ => -1
  | some base => Pi.single base 1 - fun _ => 1 / (2 * (Fintype.card coord : ℝ))

/-- Two simplex vectors at distinct coordinates pair to `-3/(4 dim)`. -/
theorem obtuseSimplexAtom_dotProduct_some_some {coord : Type*} [Fintype coord] [DecidableEq coord]
    {baseFirst baseSecond : coord} (hne : baseFirst ≠ baseSecond) :
    obtuseSimplexAtom (some baseFirst) ⬝ᵥ obtuseSimplexAtom (some baseSecond)
      = -3 / (4 * (Fintype.card coord : ℝ)) := by
  have hcardPos : 0 < Fintype.card coord := Fintype.card_pos_iff.mpr ⟨baseFirst⟩
  have hcardNe : ((Fintype.card coord : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hcardPos.ne'
  simp only [obtuseSimplexAtom, sub_dotProduct, dotProduct_sub, single_dotProduct,
    dotProduct_single, dotProduct_constant, Pi.sub_apply,
    Pi.single_eq_of_ne (Ne.symm hne)]
  field_simp
  ring

/-- A simplex vector pairs to `-1/2` with the extra vector. -/
theorem obtuseSimplexAtom_dotProduct_some_none {coord : Type*} [Fintype coord] [DecidableEq coord]
    (base : coord) :
    obtuseSimplexAtom (some base) ⬝ᵥ obtuseSimplexAtom none = -(1 / 2) := by
  have hcardPos : 0 < Fintype.card coord := Fintype.card_pos_iff.mpr ⟨base⟩
  have hcardNe : ((Fintype.card coord : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hcardPos.ne'
  simp only [obtuseSimplexAtom, sub_dotProduct, single_dotProduct, dotProduct_constant]
  field_simp
  norm_num

/-- **THE OBTUSE BOUND IS ATTAINED AT EVERY DIMENSION.** The simplex family is
pairwise obtuse and is indexed by a type of cardinality exactly `dim + 1`, so
`card_le_succ_of_isPairwiseObtuse` is an equality on it and the constant cannot be
lowered. The hypothesis `1 <= dim` is only needed because at `dim = 0` there is no
`some` vector at all — and there the bound `card (Option Empty) = 1 = 0 + 1` is
still attained, vacuously. -/
theorem isPairwiseObtuse_obtuseSimplexAtom {coord : Type*} [Fintype coord] [DecidableEq coord] :
    IsPairwiseObtuse (obtuseSimplexAtom (coord := coord))
      ∧ Fintype.card (Option coord) = Fintype.card coord + 1 := by
  refine ⟨?_, Fintype.card_option⟩
  intro first second hne
  match first, second with
  | none, none => exact absurd rfl hne
  | none, some baseSecond =>
      rw [dotProduct_comm, obtuseSimplexAtom_dotProduct_some_none baseSecond]
      norm_num
  | some baseFirst, none =>
      rw [obtuseSimplexAtom_dotProduct_some_none baseFirst]
      norm_num
  | some baseFirst, some baseSecond =>
      have hbaseNe : baseFirst ≠ baseSecond := fun heq => hne (by rw [heq])
      have hcardPos : 0 < Fintype.card coord := Fintype.card_pos_iff.mpr ⟨baseFirst⟩
      have hcardPosReal : (0 : ℝ) < (Fintype.card coord : ℝ) := Nat.cast_pos.mpr hcardPos
      rw [obtuseSimplexAtom_dotProduct_some_some hbaseNe]
      apply div_neg_of_neg_of_pos <;> linarith

/-! ## Switching invariance of the triangle product -/

/-- The **triangle product** `<a,b> <a,c> <b,c>` of three vectors: the invariant of
the underlying two-graph, and the only sign the sign-blind certificate families
cannot see. -/
def triangleProduct {coord : Type*} [Fintype coord]
    (first second third : coord → ℝ) : ℝ :=
  (first ⬝ᵥ second) * (first ⬝ᵥ third) * (second ⬝ᵥ third)

theorem triangleProduct_comm_left {coord : Type*} [Fintype coord]
    (first second third : coord → ℝ) :
    triangleProduct first second third = triangleProduct second first third := by
  simp only [triangleProduct, dotProduct_comm first second, dotProduct_comm first third,
    dotProduct_comm second third]
  ring

/-- **SWITCHING INVARIANCE, in its strongest form.** Rescaling the three vectors by
ARBITRARY real scalars multiplies the triangle product by the SQUARE of the product
of the scalars. Each scalar occurs in exactly two of the three pairings, which is
the whole content: no odd power survives. Consequently the sign of the triangle
product depends only on the rescaling class of the configuration, and in
particular is untouched by negating any subset of the vectors — Seidel switching.
This is why Lemma A is a statement about the two-graph and not about a choice of
representative vectors. -/
theorem triangleProduct_smul {coord : Type*} [Fintype coord]
    (scaleFirst scaleSecond scaleThird : ℝ) (first second third : coord → ℝ) :
    triangleProduct (scaleFirst • first) (scaleSecond • second) (scaleThird • third)
      = (scaleFirst * scaleSecond * scaleThird) ^ 2 * triangleProduct first second third := by
  simp only [triangleProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Rescaling by signs leaves the triangle product FIXED, not merely
sign-preserved: `(+-1 * +-1 * +-1)^2 = 1`. -/
theorem triangleProduct_smul_of_sq_eq_one {coord : Type*} [Fintype coord]
    {scaleFirst scaleSecond scaleThird : ℝ} (hfirst : scaleFirst ^ 2 = 1)
    (hsecond : scaleSecond ^ 2 = 1) (hthird : scaleThird ^ 2 = 1)
    (first second third : coord → ℝ) :
    triangleProduct (scaleFirst • first) (scaleSecond • second) (scaleThird • third)
      = triangleProduct first second third := by
  rw [triangleProduct_smul]
  have hunit : (scaleFirst * scaleSecond * scaleThird) ^ 2 = 1 := by
    rw [mul_pow, mul_pow, hfirst, hsecond, hthird]
    ring
  rw [hunit, one_mul]

/-- The sign of the triangle product is invariant under any rescaling by nonzero
scalars. -/
theorem triangleProduct_smul_pos_iff {coord : Type*} [Fintype coord]
    {scaleFirst scaleSecond scaleThird : ℝ} (hfirst : scaleFirst ≠ 0)
    (hsecond : scaleSecond ≠ 0) (hthird : scaleThird ≠ 0)
    (first second third : coord → ℝ) :
    0 < triangleProduct (scaleFirst • first) (scaleSecond • second) (scaleThird • third)
      ↔ 0 < triangleProduct first second third := by
  rw [triangleProduct_smul]
  have hscaleNe : scaleFirst * scaleSecond * scaleThird ≠ 0 :=
    mul_ne_zero (mul_ne_zero hfirst hsecond) hthird
  have hscalePos : 0 < (scaleFirst * scaleSecond * scaleThird) ^ 2 := by positivity
  constructor
  · intro hpos
    by_contra hnonpos
    push Not at hnonpos
    have hopposite : 0 ≤ (scaleFirst * scaleSecond * scaleThird) ^ 2
        * (-triangleProduct first second third) :=
      mul_nonneg hscalePos.le (neg_nonneg.mpr hnonpos)
    nlinarith [hopposite, hpos]
  · intro hpos
    exact mul_pos hscalePos hpos

/-! ## T6: Lemma A, sign forcing -/

/-- The **switching sign** relative to a base atom: `+1` at the base, and elsewhere
the sign that makes the pairing with the base atom negative. -/
noncomputable def switchSign {atomIndex coord : Type*} [Fintype coord] [DecidableEq atomIndex]
    (vec : atomIndex → (coord → ℝ)) (baseIndex index : atomIndex) : ℝ :=
  if index = baseIndex then 1 else if vec baseIndex ⬝ᵥ vec index < 0 then 1 else -1

theorem switchSign_sq_eq_one {atomIndex coord : Type*} [Fintype coord] [DecidableEq atomIndex]
    (vec : atomIndex → (coord → ℝ)) (baseIndex index : atomIndex) :
    switchSign vec baseIndex index ^ 2 = 1 := by
  rw [switchSign]
  split
  · norm_num
  · split <;> norm_num

theorem switchSign_ne_zero {atomIndex coord : Type*} [Fintype coord] [DecidableEq atomIndex]
    (vec : atomIndex → (coord → ℝ)) (baseIndex index : atomIndex) :
    switchSign vec baseIndex index ≠ 0 := by
  intro hzero
  have hsq := switchSign_sq_eq_one vec baseIndex index
  rw [hzero] at hsq
  norm_num at hsq

theorem switchSign_base {atomIndex coord : Type*} [Fintype coord] [DecidableEq atomIndex]
    (vec : atomIndex → (coord → ℝ)) (baseIndex : atomIndex) :
    switchSign vec baseIndex baseIndex = 1 := by
  rw [switchSign, if_pos rfl]

/-- After switching, every off-base pairing with the base atom is strictly
negative — provided it was nonzero to begin with. -/
theorem switchSign_mul_basePairing_neg {atomIndex coord : Type*} [Fintype coord]
    [DecidableEq atomIndex] {vec : atomIndex → (coord → ℝ)} {baseIndex index : atomIndex}
    (hnonzero : vec baseIndex ⬝ᵥ vec index ≠ 0) (hne : index ≠ baseIndex) :
    switchSign vec baseIndex index * (vec baseIndex ⬝ᵥ vec index) < 0 := by
  rw [switchSign, if_neg hne]
  rcases lt_or_gt_of_ne hnonzero with hneg | hpos
  · rw [if_pos hneg]; linarith
  · rw [if_neg (not_lt.mpr hpos.le)]; linarith

/-- **T6, LEMMA A (SIGN FORCING).** Any family of at least `dim + 2` vectors in a
real coordinate space of dimension `dim`, all of whose pairwise pairings are
nonzero, carries a triple with strictly positive triangle product.

The pen argument: assume every triple has nonpositive triangle product. Switch by
`switchSign` relative to a base atom. Edges at the base become negative by
construction. For an edge `{i,j}` off the base, write `u` for the product of the
two switching signs; then `u^2 = 1`, the switched base pairings multiply to
`u * <b,i> <b,j> > 0`, and `(u <i,j>) * (u <b,i><b,j>) = <b,i><b,j><i,j> <= 0`
forces `u <i,j> <= 0`, strictly since `<i,j> /= 0`. So the whole switched family
is pairwise obtuse, and the obtuse bound caps it at `dim + 1`. -/
theorem exists_pos_triangleProduct_of_card_ge {atomIndex coord : Type*}
    [Fintype atomIndex] [DecidableEq atomIndex] [Fintype coord]
    (vec : atomIndex → (coord → ℝ))
    (hnonzero : ∀ first second : atomIndex, first ≠ second → vec first ⬝ᵥ vec second ≠ 0)
    (hcard : Fintype.card coord + 2 ≤ Fintype.card atomIndex) :
    ∃ first second third : atomIndex, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 < triangleProduct (vec first) (vec second) (vec third) := by
  by_contra hall
  push Not at hall
  have hcardPos : 0 < Fintype.card atomIndex := by omega
  obtain ⟨baseIndex⟩ := Fintype.card_pos_iff.mp hcardPos
  -- The switched pairing of any two distinct atoms is strictly negative.
  have hswitchedNeg : ∀ first second : atomIndex, first ≠ second →
      switchSign vec baseIndex first * switchSign vec baseIndex second
          * (vec first ⬝ᵥ vec second) < 0 := by
    intro first second hne
    rcases eq_or_ne first baseIndex with hfirstBase | hfirstNe
    · subst hfirstBase
      have hsecondNe : second ≠ first := Ne.symm hne
      have hbaseSign : switchSign vec first first = 1 := switchSign_base vec first
      have hkey : switchSign vec first second * (vec first ⬝ᵥ vec second) < 0 :=
        switchSign_mul_basePairing_neg (baseIndex := first) (index := second)
          (hnonzero first second hne) hsecondNe
      rw [hbaseSign, one_mul]
      exact hkey
    · rcases eq_or_ne second baseIndex with hsecondBase | hsecondNe
      · subst hsecondBase
        have hbaseSign : switchSign vec second second = 1 := switchSign_base vec second
        have hkey : switchSign vec second first * (vec second ⬝ᵥ vec first) < 0 :=
          switchSign_mul_basePairing_neg (baseIndex := second) (index := first)
            (hnonzero second first (Ne.symm hne)) hfirstNe
        rw [hbaseSign, mul_one, dotProduct_comm]
        exact hkey
      · -- Both off the base: consume the triangle `{base, first, second}`.
        have htriangle : triangleProduct (vec baseIndex) (vec first) (vec second) ≤ 0 :=
          hall baseIndex first second (Ne.symm hfirstNe) (Ne.symm hsecondNe) hne
        rw [triangleProduct] at htriangle
        have hfirstBaseNeg : switchSign vec baseIndex first * (vec baseIndex ⬝ᵥ vec first) < 0 :=
          switchSign_mul_basePairing_neg (baseIndex := baseIndex) (index := first)
            (hnonzero baseIndex first (Ne.symm hfirstNe)) hfirstNe
        have hsecondBaseNeg : switchSign vec baseIndex second * (vec baseIndex ⬝ᵥ vec second) < 0 :=
          switchSign_mul_basePairing_neg (baseIndex := baseIndex) (index := second)
            (hnonzero baseIndex second (Ne.symm hsecondNe)) hsecondNe
        have hcrossNe : vec first ⬝ᵥ vec second ≠ 0 := hnonzero first second hne
        have hfirstSq := switchSign_sq_eq_one vec baseIndex first
        have hsecondSq := switchSign_sq_eq_one vec baseIndex second
        -- The two switched base pairings multiply to a strictly positive number.
        have hbaseProdPos : 0 < switchSign vec baseIndex first * switchSign vec baseIndex second
            * ((vec baseIndex ⬝ᵥ vec first) * (vec baseIndex ⬝ᵥ vec second)) := by
          have hproduct := mul_pos_of_neg_of_neg hfirstBaseNeg hsecondBaseNeg
          have hregroup : switchSign vec baseIndex first * switchSign vec baseIndex second
              * ((vec baseIndex ⬝ᵥ vec first) * (vec baseIndex ⬝ᵥ vec second))
              = (switchSign vec baseIndex first * (vec baseIndex ⬝ᵥ vec first))
                * (switchSign vec baseIndex second * (vec baseIndex ⬝ᵥ vec second)) := by
            ring
          rw [hregroup]
          exact hproduct
        -- Multiplying the goal by that positive number returns the triangle product.
        have hgaugeCancel :
            (switchSign vec baseIndex first * switchSign vec baseIndex second
                * (vec first ⬝ᵥ vec second))
              * (switchSign vec baseIndex first * switchSign vec baseIndex second
                  * ((vec baseIndex ⬝ᵥ vec first) * (vec baseIndex ⬝ᵥ vec second)))
            = (vec baseIndex ⬝ᵥ vec first) * (vec baseIndex ⬝ᵥ vec second)
                * (vec first ⬝ᵥ vec second) := by
          linear_combination ((vec baseIndex ⬝ᵥ vec first) * (vec baseIndex ⬝ᵥ vec second)
              * (vec first ⬝ᵥ vec second) * switchSign vec baseIndex second ^ 2) * hfirstSq
            + ((vec baseIndex ⬝ᵥ vec first) * (vec baseIndex ⬝ᵥ vec second)
              * (vec first ⬝ᵥ vec second)) * hsecondSq
        have hswitchedNonpos : switchSign vec baseIndex first * switchSign vec baseIndex second
            * (vec first ⬝ᵥ vec second) ≤ 0 := by
          by_contra hpositive
          push Not at hpositive
          have hcontradiction := mul_pos hpositive hbaseProdPos
          rw [hgaugeCancel] at hcontradiction
          linarith
        have hswitchedNe : switchSign vec baseIndex first * switchSign vec baseIndex second
            * (vec first ⬝ᵥ vec second) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (switchSign_ne_zero vec baseIndex first)
            (switchSign_ne_zero vec baseIndex second)) hcrossNe
        exact lt_of_le_of_ne hswitchedNonpos hswitchedNe
  have hswitchedObtuse :
      IsPairwiseObtuse (fun index => switchSign vec baseIndex index • vec index) := by
    intro first second hne
    show (switchSign vec baseIndex first • vec first)
      ⬝ᵥ (switchSign vec baseIndex second • vec second) < 0
    have hexpand : (switchSign vec baseIndex first • vec first)
        ⬝ᵥ (switchSign vec baseIndex second • vec second)
        = switchSign vec baseIndex first * switchSign vec baseIndex second
            * (vec first ⬝ᵥ vec second) := by
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [hexpand]
    exact hswitchedNeg first second hne
  have hbound := card_le_succ_of_isPairwiseObtuse hswitchedObtuse
  omega

/-- **The hypothesis-free strengthening.** Drop the nonzero-pairing hypothesis and
the conclusion weakens by exactly one strict inequality: `dim + 2` vectors always
carry a triple of NONNEGATIVE triangle product, because a vanishing pairing gives
a vanishing product through any third member. The only extra input is that a
third member exists. -/
theorem exists_nonneg_triangleProduct_of_card_ge {atomIndex coord : Type*}
    [Fintype atomIndex] [DecidableEq atomIndex] [Fintype coord]
    (vec : atomIndex → (coord → ℝ))
    (hcard : Fintype.card coord + 2 ≤ Fintype.card atomIndex)
    (hthree : 3 ≤ Fintype.card atomIndex) :
    ∃ first second third : atomIndex, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 ≤ triangleProduct (vec first) (vec second) (vec third) := by
  classical
  by_cases hnonzero : ∀ first second : atomIndex, first ≠ second → vec first ⬝ᵥ vec second ≠ 0
  · obtain ⟨first, second, third, hfs, hft, hst, hpos⟩ :=
      exists_pos_triangleProduct_of_card_ge vec hnonzero hcard
    exact ⟨first, second, third, hfs, hft, hst, hpos.le⟩
  · push Not at hnonzero
    obtain ⟨first, second, hfs, hzero⟩ := hnonzero
    have hthird : ∃ third : atomIndex, third ≠ first ∧ third ≠ second := by
      by_contra hnone
      push Not at hnone
      have hsubset : (Finset.univ : Finset atomIndex) ⊆ {first, second} := by
        intro index _
        rcases eq_or_ne index first with rfl | hne
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (hnone index hne))
      have hpairCard : ({first, second} : Finset atomIndex).card ≤ 2 := by
        refine (Finset.card_insert_le _ _).trans ?_
        simp
      have hcardLe : Fintype.card atomIndex ≤ 2 := by
        have huniv := Finset.card_le_card hsubset
        rw [Finset.card_univ] at huniv
        omega
      omega
    obtain ⟨third, hthirdFirst, hthirdSecond⟩ := hthird
    refine ⟨first, second, third, hfs, Ne.symm hthirdFirst, Ne.symm hthirdSecond, ?_⟩
    rw [triangleProduct, hzero]
    simp

/-- **LEMMA A'S THRESHOLD IS SHARP.** At `dim + 1` vectors the conclusion fails:
the four tetrahedron vertices of `R^3` have all six pairings equal to `-1`, hence
every one of their four triangle products is `-1 < 0`, while every pairing is
nonzero. So `dim + 2` cannot be lowered to `dim + 1`. -/
theorem triangleProduct_tetraAtom_eq_neg_one {first second third : Fin 4}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    triangleProduct (tetraAtom first) (tetraAtom second) (tetraAtom third) = -1 := by
  rw [triangleProduct, tetraAtom_dotProduct_eq_neg_one_of_ne hfirstSecond,
    tetraAtom_dotProduct_eq_neg_one_of_ne hfirstThird,
    tetraAtom_dotProduct_eq_neg_one_of_ne hsecondThird]
  norm_num

/-- The same, as the negative statement Lemma A's sharpness actually asserts. -/
theorem not_exists_pos_triangleProduct_tetraAtom :
    ¬ ∃ first second third : Fin 4, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 < triangleProduct (tetraAtom first) (tetraAtom second) (tetraAtom third) := by
  rintro ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hpos⟩
  rw [triangleProduct_tetraAtom_eq_neg_one hfirstSecond hfirstThird hsecondThird] at hpos
  norm_num at hpos

/-! ## The complex coordinate space, viewed as a real one

`C^dim` is `R^(2 dim)` and the real part of the Hermitian pairing IS the real dot
product of the realifications. Both theorems above therefore transfer with the
constant doubled, which is the precise arithmetic of the field door. -/

/-- Realification of a complex coordinate vector: real parts on the left summand,
imaginary parts on the right. The coordinate index doubles. -/
def realifyComplexVector {coord : Type*} (vector : coord → ℂ) : (coord ⊕ coord) → ℝ :=
  Sum.elim (fun index => (vector index).re) (fun index => (vector index).im)

/-- **Realification is an isometry for the real part of the Hermitian form.** -/
theorem dotProduct_realifyComplexVector {coord : Type*} [Fintype coord]
    (left right : coord → ℂ) :
    realifyComplexVector left ⬝ᵥ realifyComplexVector right = (star left ⬝ᵥ right).re := by
  rw [dotProduct, Fintype.sum_sum_type, dotProduct, Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun index _ => ?_
  simp only [realifyComplexVector, Sum.elim_inl, Sum.elim_inr, Pi.star_apply,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- A complex family is **pairwise obtuse** when the real part of every Hermitian
pairing of distinct members is strictly negative. -/
def IsPairwiseObtuseComplex {atomIndex coord : Type*} [Fintype coord]
    (vec : atomIndex → (coord → ℂ)) : Prop :=
  ∀ first second : atomIndex, first ≠ second → (star (vec first) ⬝ᵥ vec second).re < 0

/-- **THE OBTUSE BOUND OVER `C`.** At most `2 dim + 1` vectors of `C^dim` are
pairwise obtuse for the real part of the Hermitian pairing — twice the real bound
plus one, because `C^dim` is `R^(2 dim)`. This is the exact form of the field
door: at `dim = 3` the real bound is `4` and the complex bound is `7`. -/
theorem card_le_two_mul_add_one_of_isPairwiseObtuseComplex {atomIndex coord : Type*}
    [Fintype atomIndex] [Fintype coord] {vec : atomIndex → (coord → ℂ)}
    (hobtuse : IsPairwiseObtuseComplex vec) :
    Fintype.card atomIndex ≤ 2 * Fintype.card coord + 1 := by
  have hrealObtuse : IsPairwiseObtuse (fun index => realifyComplexVector (vec index)) := by
    intro first second hne
    rw [dotProduct_realifyComplexVector]
    exact hobtuse first second hne
  have hbound := card_le_succ_of_isPairwiseObtuse hrealObtuse
  rwa [Fintype.card_sum, ← two_mul] at hbound

/-- Complexification, inverse to `realifyComplexVector`: read the left summand as
real parts and the right summand as imaginary parts. -/
def complexifyRealVector {coord : Type*} (vector : (coord ⊕ coord) → ℝ) : coord → ℂ :=
  fun index => ⟨vector (Sum.inl index), vector (Sum.inr index)⟩

theorem realifyComplexVector_complexifyRealVector {coord : Type*}
    (vector : (coord ⊕ coord) → ℝ) :
    realifyComplexVector (complexifyRealVector vector) = vector := by
  funext index
  cases index <;> rfl

/-- **THE COMPLEX OBTUSE BOUND IS ATTAINED, SO `2 dim + 1` IS EXACT.** Complexify
the real simplex of `R^(2 dim)`: since realification is an isometry for the real
part of the Hermitian form and inverts complexification, the resulting `2 dim + 1`
vectors of `C^dim` are pairwise obtuse. Together with
`card_le_two_mul_add_one_of_isPairwiseObtuseComplex` this pins the complex constant
exactly, which is the precise measure of the field door: `4` over `R^3` against
`7` over `C^3`. -/
theorem isPairwiseObtuseComplex_complexifiedSimplex {coord : Type*} [Fintype coord]
    [DecidableEq coord] :
    IsPairwiseObtuseComplex (fun index : Option (coord ⊕ coord) =>
        complexifyRealVector (obtuseSimplexAtom index))
      ∧ Fintype.card (Option (coord ⊕ coord)) = 2 * Fintype.card coord + 1 := by
  refine ⟨?_, ?_⟩
  · intro first second hne
    have hrealNeg := (isPairwiseObtuse_obtuseSimplexAtom
      (coord := coord ⊕ coord)).1 first second hne
    rw [← dotProduct_realifyComplexVector, realifyComplexVector_complexifyRealVector,
      realifyComplexVector_complexifyRealVector]
    exact hrealNeg
  · rw [Fintype.card_option, Fintype.card_sum, ← two_mul]

/-- **Sign forcing over `C`, and the size threshold it moves.** Any `2 dim + 2`
vectors of `C^dim` whose Hermitian pairings all have nonzero real part carry a
triple whose triangle product OF REAL PARTS is strictly positive.

Read this as the honest statement of where the real argument dies over `C`: at
`dim = 3` the threshold moves from `5` atoms to `8` -- the hypothesis below is
`2 dim + 2 <= card`, so at `dim = 3` it reads `8 <= card` -- leaving `m = 5, 6, 7`
as the window where the real argument forces and the complex one does not. Of the
campaign's complex counterexamples `m = 6` (`trineDesign`) lies in that window;
`m = 9` (the Hesse SIC) lies ABOVE it, and escapes this theorem only through the
nonzero-real-part hypothesis, not through its size. No claim is made here that
Lemma A itself fails over `C`; what fails is the obtuse bound that powers it, and
it fails by the doubling of the real dimension. -/
theorem exists_pos_realTriangleProduct_of_complex_card_ge {atomIndex coord : Type*}
    [Fintype atomIndex] [DecidableEq atomIndex] [Fintype coord]
    (vec : atomIndex → (coord → ℂ))
    (hnonzero : ∀ first second : atomIndex, first ≠ second →
      (star (vec first) ⬝ᵥ vec second).re ≠ 0)
    (hcard : 2 * Fintype.card coord + 2 ≤ Fintype.card atomIndex) :
    ∃ first second third : atomIndex, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 < (star (vec first) ⬝ᵥ vec second).re * (star (vec first) ⬝ᵥ vec third).re
            * (star (vec second) ⬝ᵥ vec third).re := by
  have hrealNonzero : ∀ first second : atomIndex, first ≠ second →
      realifyComplexVector (vec first) ⬝ᵥ realifyComplexVector (vec second) ≠ 0 := by
    intro first second hne
    rw [dotProduct_realifyComplexVector]
    exact hnonzero first second hne
  have hcardReal : Fintype.card (coord ⊕ coord) + 2 ≤ Fintype.card atomIndex := by
    rwa [Fintype.card_sum, ← two_mul]
  obtain ⟨first, second, third, hfs, hft, hst, hpos⟩ :=
    exists_pos_triangleProduct_of_card_ge
      (fun index => realifyComplexVector (vec index)) hrealNonzero hcardReal
  refine ⟨first, second, third, hfs, hft, hst, ?_⟩
  rw [triangleProduct, dotProduct_realifyComplexVector, dotProduct_realifyComplexVector,
    dotProduct_realifyComplexVector] at hpos
  exact hpos

/-! ## What a positive triangle buys at a rank-three design

The scalar cell first, in the three normalized pairings, then its design reading,
then the failure consequence Lemma A feeds. -/

/-- **THE COHERENT HALF-BOX CELL, in `rho` coordinates.** A coherent triple —
nonnegative oriented product — has nonnegative elliptope bracket as soon as every
correlation satisfies `rho^2 <= 1/2`. The sign-blind box needs `rho^2 <= 1/4`, so
in the coherent sector this doubles the admissible squared correlation.

The pen argument is a multilinear certificate. Writing `x = rho_1^2` and so on,
`4xyz - x - y - z + 1` is multilinear in each variable, hence a convex combination
of its eight vertex values on `[0,1/2]^3`, which are `1, 1/2, 0` and `0`; the
explicit positive combination is `8 XYZ + 4(xYZ + XyZ + XYz)` with `X = 1/2 - x`.
That gives `x + y + z - 1 <= 4 (rho_1 rho_2 rho_3)^2`. If `x + y + z <= 1` the
bracket is nonnegative outright; otherwise the excess `s = x + y + z - 1` lies in
`(0, 1/2]`, and `(2 rho_1 rho_2 rho_3)^2 >= s` together with `s^2 <= s` forces
`2 rho_1 rho_2 rho_3 >= s`, which is the bracket again. -/
theorem elliptopeBracket_nonneg_of_coherent_of_sq_le_half
    {rhoFirst rhoSecond rhoThird : ℝ}
    (hcoherent : 0 ≤ rhoFirst * rhoSecond * rhoThird)
    (hfirst : rhoFirst ^ 2 ≤ 1 / 2) (hsecond : rhoSecond ^ 2 ≤ 1 / 2)
    (hthird : rhoThird ^ 2 ≤ 1 / 2) :
    0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird := by
  have hslackFirst : 0 ≤ 1 / 2 - rhoFirst ^ 2 := by linarith
  have hslackSecond : 0 ≤ 1 / 2 - rhoSecond ^ 2 := by linarith
  have hslackThird : 0 ≤ 1 / 2 - rhoThird ^ 2 := by linarith
  have hmultilinear : rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2 - 1
      ≤ 4 * (rhoFirst * rhoSecond * rhoThird) ^ 2 := by
    have hcertificate : 4 * (rhoFirst * rhoSecond * rhoThird) ^ 2
          - (rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2 - 1)
        = 8 * ((1 / 2 - rhoFirst ^ 2) * (1 / 2 - rhoSecond ^ 2) * (1 / 2 - rhoThird ^ 2))
          + 4 * (rhoFirst ^ 2 * ((1 / 2 - rhoSecond ^ 2) * (1 / 2 - rhoThird ^ 2)))
          + 4 * ((1 / 2 - rhoFirst ^ 2) * (rhoSecond ^ 2 * (1 / 2 - rhoThird ^ 2)))
          + 4 * ((1 / 2 - rhoFirst ^ 2) * ((1 / 2 - rhoSecond ^ 2) * rhoThird ^ 2)) := by
      ring
    have hvertexAll : 0 ≤ (1 / 2 - rhoFirst ^ 2) * (1 / 2 - rhoSecond ^ 2) * (1 / 2 - rhoThird ^ 2) :=
      mul_nonneg (mul_nonneg hslackFirst hslackSecond) hslackThird
    have hvertexFirst : 0 ≤ rhoFirst ^ 2 * ((1 / 2 - rhoSecond ^ 2) * (1 / 2 - rhoThird ^ 2)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg hslackSecond hslackThird)
    have hvertexSecond : 0 ≤ (1 / 2 - rhoFirst ^ 2) * (rhoSecond ^ 2 * (1 / 2 - rhoThird ^ 2)) :=
      mul_nonneg hslackFirst (mul_nonneg (sq_nonneg _) hslackThird)
    have hvertexThird : 0 ≤ (1 / 2 - rhoFirst ^ 2) * ((1 / 2 - rhoSecond ^ 2) * rhoThird ^ 2) :=
      mul_nonneg hslackFirst (mul_nonneg hslackSecond (sq_nonneg _))
    linarith
  rcases le_or_gt (rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2 - 1) 0 with hsmall | hlarge
  · rw [elliptopeBracket]; linarith
  · have hexcessLe : rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2 - 1 ≤ 1 / 2 := by linarith
    have hproductBound : rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2 - 1
        ≤ 2 * (rhoFirst * rhoSecond * rhoThird) := by
      by_contra hcontra
      push Not at hcontra
      nlinarith [hcoherent, hmultilinear, hlarge, hexcessLe, hcontra]
    rw [elliptopeBracket]; linarith

/-- **The threshold `1/2` is SHARP.** Above it the cell is false, witnessed by
`rho = (0, s, s)` with `s^2` just past one half: the oriented product is `0`, so
the triple is coherent, every square is at most the threshold, and the bracket is
`1 - 2 s^2 < 0`. Equality at `s^2 = 1/2` gives bracket exactly `0`, so the cell is
attained on its boundary and the non-strict form is the correct one. -/
theorem exists_elliptopeBracket_neg_of_half_lt {threshold : ℝ} (hthreshold : 1 / 2 < threshold) :
    ∃ rhoFirst rhoSecond rhoThird : ℝ,
      0 ≤ rhoFirst * rhoSecond * rhoThird ∧ rhoFirst ^ 2 ≤ threshold
        ∧ rhoSecond ^ 2 ≤ threshold ∧ rhoThird ^ 2 ≤ threshold
        ∧ elliptopeBracket rhoFirst rhoSecond rhoThird < 0 := by
  set level := min threshold 1 with hlevel
  have hlevelPos : 1 / 2 < level := by
    rw [hlevel]
    exact lt_min hthreshold (by norm_num)
  have hlevelNonneg : (0 : ℝ) ≤ level := by linarith
  have hsqrtSq : Real.sqrt level ^ 2 = level := Real.sq_sqrt hlevelNonneg
  have hlevelLe : level ≤ threshold := by rw [hlevel]; exact min_le_left _ _
  refine ⟨0, Real.sqrt level, Real.sqrt level, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · have hzeroSq : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [hzeroSq]; linarith
  · rw [hsqrtSq]; exact hlevelLe
  · rw [hsqrtSq]; exact hlevelLe
  · rw [elliptopeBracket, hsqrtSq]
    linarith

/-- The half-box edge condition in raw scalars is exactly `rho^2 <= 1/2`. -/
theorem normalizedPairing_sq_le_half_iff {m : ℕ} (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirstPos : 0 < heavyExcess D atomFirst)
    (hsecondPos : 0 < heavyExcess D atomSecond) :
    normalizedPairing D atomFirst atomSecond ^ 2 ≤ 1 / 2
      ↔ 2 * atomPairing D atomFirst atomSecond ^ 2
          ≤ heavyExcess D atomFirst * heavyExcess D atomSecond := by
  rw [normalizedPairing_sq D hfirstPos hsecondPos, div_le_iff₀ (mul_pos hfirstPos hsecondPos)]
  constructor <;> intro hbound <;> linarith

/-- **THE COHERENT HALF-BOX CERTIFICATE.** A triple of distinct atoms of an
all-heavy rank-three design dominates as soon as its oriented pairing product is
nonnegative and every edge satisfies `2 p^2 <= u u`.

Compare `dominates_of_dominantPairings`, which demands `4 p^2 <= u u` and reads no
sign: in the coherent sector this cell is strictly larger, and it is not
sign-blind, so `not_signBlindGoodTripleCovering_seven` does not reach it. It
certifies the icosahedron's coherent triples, whose every pair has
`rho^2 = 9/20` and so lies outside the box graph entirely
(`icosaDesign_no_isBoxGoodPair`). It does NOT give a covering: coherence at every
triple is not available, and nothing here bounds the oriented product from below
against the excess gap. -/
theorem dominates_of_coherentHalfBoxTriangle {m : ℕ} {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hcoherent : 0 ≤ atomPairing D first second * atomPairing D first third
      * atomPairing D second third)
    (hedgeFirstSecond : 2 * atomPairing D first second ^ 2
      ≤ heavyExcess D first * heavyExcess D second)
    (hedgeFirstThird : 2 * atomPairing D first third ^ 2
      ≤ heavyExcess D first * heavyExcess D third)
    (hedgeSecondThird : 2 * atomPairing D second third ^ 2
      ≤ heavyExcess D second * heavyExcess D third) :
    Dominates D {first, second, third} := by
  have hfirstPos := allHeavy_heavyExcess_pos hheavy first
  have hsecondPos := allHeavy_heavyExcess_pos hheavy second
  have hthirdPos := allHeavy_heavyExcess_pos hheavy third
  have hrhoFirstSecond : normalizedPairing D first second ^ 2 ≤ 1 / 2 :=
    (normalizedPairing_sq_le_half_iff D hfirstPos hsecondPos).mpr hedgeFirstSecond
  have hrhoFirstThird : normalizedPairing D first third ^ 2 ≤ 1 / 2 :=
    (normalizedPairing_sq_le_half_iff D hfirstPos hthirdPos).mpr hedgeFirstThird
  have hrhoSecondThird : normalizedPairing D second third ^ 2 ≤ 1 / 2 :=
    (normalizedPairing_sq_le_half_iff D hsecondPos hthirdPos).mpr hedgeSecondThird
  have hrhoCoherent : 0 ≤ normalizedPairing D first second * normalizedPairing D first third
      * normalizedPairing D second third := by
    rw [normalizedPairing_product D hfirstPos hsecondPos hthirdPos]
    exact div_nonneg hcoherent (by positivity)
  have hbracket : 0 ≤ elliptopeBracket (normalizedPairing D first second)
      (normalizedPairing D first third) (normalizedPairing D second third) :=
    elliptopeBracket_nonneg_of_coherent_of_sq_le_half hrhoCoherent hrhoFirstSecond
      hrhoFirstThird hrhoSecondThird
  refine (dominates_triple_iff_isElliptopeGoodTriangle hheavy hfirstSecond hfirstThird
    hsecondThird).mpr ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [IsCompatiblePair, pairMinor]
    linarith [sq_nonneg (atomPairing D first second)]
  · rw [IsCompatiblePair, pairMinor]
    linarith [sq_nonneg (atomPairing D first third)]
  · rw [IsCompatiblePair, pairMinor]
    linarith [sq_nonneg (atomPairing D second third)]
  · exact (discriminantTie_nonneg_iff_elliptopeBracket_nonneg D hfirstPos hsecondPos
      hthirdPos).mpr hbracket

/-- **THE NEW CELL IS NONEMPTY EXACTLY WHERE THE BOX IS EMPTY.** Every distinct
icosahedral triple with nonnegative oriented pairing product dominates, by the
half-box certificate alone — even though the box graph of `icosaDesign` is EMPTY
(`icosaDesign_no_isBoxGoodPair`), each of its fifteen pairs sitting at
`rho^2 = 9/20` (`icosaDesign_normalizedPairing_sq_of_ne`), comfortably outside the
box threshold `1/4` and comfortably inside the half-box threshold `1/2`. In raw
scalars: `2 p^2 = 18/5` against `u u = 4`.

That the icosahedron's coherent triples dominate is independently known from
`icosaDesign_dominates_iff_pairingProduct`; what is new here is that it follows
from a GENERAL cell rather than from the icosahedron's own arithmetic, which is
the concrete evidence that reading the oriented sign strictly enlarges the
certified region beyond every sign-blind family. -/
theorem icosaDesign_dominates_of_coherentPairings {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hcoherent : 0 ≤ atomPairing icosaDesign first second
      * atomPairing icosaDesign first third * atomPairing icosaDesign second third) :
    Dominates icosaDesign {first, second, third} := by
  have hedge : ∀ atomFirst atomSecond : Fin 6, atomFirst ≠ atomSecond →
      2 * atomPairing icosaDesign atomFirst atomSecond ^ 2
        ≤ heavyExcess icosaDesign atomFirst * heavyExcess icosaDesign atomSecond := by
    intro atomFirst atomSecond hne
    rw [icosaDesign_atomPairing_sq_of_ne hne, icosaDesign_heavyExcess, icosaDesign_heavyExcess]
    norm_num
  exact dominates_of_coherentHalfBoxTriangle icosaDesign_allHeavy_goodTriple hfirstSecond hfirstThird
    hsecondThird hcoherent (hedge _ _ hfirstSecond) (hedge _ _ hfirstThird)
    (hedge _ _ hsecondThird)

/-- **THE FAILURE CONSEQUENCE.** A coherent triple of an all-heavy rank-three
design that does NOT dominate carries an edge of squared correlation above one
half — that is, `|rho| > 1/sqrt 2`. This is the exact contrapositive of the
half-box cell, and by its sharpness the constant cannot be raised. -/
theorem exists_normalizedPairing_sq_gt_half_of_not_dominates {m : ℕ} {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hcoherent : 0 ≤ atomPairing D first second * atomPairing D first third
      * atomPairing D second third)
    (hfail : ¬ Dominates D {first, second, third}) :
    1 / 2 < normalizedPairing D first second ^ 2
      ∨ 1 / 2 < normalizedPairing D first third ^ 2
      ∨ 1 / 2 < normalizedPairing D second third ^ 2 := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hfirstSecondBound, hfirstThirdBound, hsecondThirdBound⟩ := hcontra
  have hfirstPos := allHeavy_heavyExcess_pos hheavy first
  have hsecondPos := allHeavy_heavyExcess_pos hheavy second
  have hthirdPos := allHeavy_heavyExcess_pos hheavy third
  exact hfail (dominates_of_coherentHalfBoxTriangle hheavy hfirstSecond hfirstThird hsecondThird
    hcoherent
    ((normalizedPairing_sq_le_half_iff D hfirstPos hsecondPos).mp hfirstSecondBound)
    ((normalizedPairing_sq_le_half_iff D hfirstPos hthirdPos).mp hfirstThirdBound)
    ((normalizedPairing_sq_le_half_iff D hsecondPos hthirdPos).mp hsecondThirdBound))

/-- **LEMMA A AT A RANK-THREE DESIGN.** Five atoms carrying pairwise nonzero
pairings contain a coherent triple: `3 + 2 = 5` is exactly Lemma A's threshold in
`R^3`. No injectivity of `pick` is needed: two indices carrying the same atom pair
to a leverage, which is nonzero, so the hypothesis already covers that case. -/
theorem exists_pos_atomPairingProduct_of_five_atoms {m : ℕ} (D : WeightedDesign m 3)
    (pick : Fin 5 → Fin m)
    (hnonzero : ∀ first second : Fin 5, first ≠ second →
      atomPairing D (pick first) (pick second) ≠ 0) :
    ∃ first second third : Fin 5, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 < atomPairing D (pick first) (pick second)
          * atomPairing D (pick first) (pick third)
          * atomPairing D (pick second) (pick third) := by
  have hcard : Fintype.card (Fin 3) + 2 ≤ Fintype.card (Fin 5) := by simp
  obtain ⟨first, second, third, hfs, hft, hst, hpos⟩ :=
    exists_pos_triangleProduct_of_card_ge (fun index => D.atom (pick index))
      (fun first second hne => hnonzero first second hne) hcard
  refine ⟨first, second, third, hfs, hft, hst, ?_⟩
  simpa only [triangleProduct, atomPairing] using hpos

/-- **THE SIGN-FORCING CONSEQUENCE FOR A COUNTEREXAMPLE.** In an all-heavy
rank-three design in which no triple dominates, ANY five atoms with pairwise
nonzero pairings carry a coherent triple, and that triple must fail either by
incompatibility or by a negative bracket — either way it carries an edge of
squared correlation above one half.

This is the shape a counterexample analysis wants: a strong edge is forced inside
every five-atom window, at a threshold `1/sqrt 2` that no sign-blind certificate
can reach, since the sign-blind closure is refuted
(`not_signBlindGoodTripleCovering_seven`) while this reads the oriented product.

HONESTY: the hypothesis `hnoTriple` is exactly the negation of weighted GTZ at
rank three for this design, which is the campaign's open problem. If that problem
resolves in the positive direction the hypothesis is unsatisfiable and the
statement below is vacuous. It is offered as a CONSTRAINT ON A HYPOTHETICAL
COUNTEREXAMPLE, not as progress toward a covering: nothing here produces a
dominating triple, and nothing here bounds the oriented product from below. -/
theorem exists_normalizedPairing_sq_gt_half_of_five_atoms {m : ℕ} {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) (pick : Fin 5 → Fin m) (hinjective : Function.Injective pick)
    (hnonzero : ∀ first second : Fin 5, first ≠ second →
      atomPairing D (pick first) (pick second) ≠ 0)
    (hnoTriple : ∀ first second third : Fin m, first ≠ second → first ≠ third →
      second ≠ third → ¬ Dominates D {first, second, third}) :
    ∃ first second : Fin 5, first ≠ second
      ∧ 1 / 2 < normalizedPairing D (pick first) (pick second) ^ 2 := by
  obtain ⟨first, second, third, hfs, hft, hst, hpos⟩ :=
    exists_pos_atomPairingProduct_of_five_atoms D pick hnonzero
  have hpickFs : pick first ≠ pick second := fun heq => hfs (hinjective heq)
  have hpickFt : pick first ≠ pick third := fun heq => hft (hinjective heq)
  have hpickSt : pick second ≠ pick third := fun heq => hst (hinjective heq)
  rcases exists_normalizedPairing_sq_gt_half_of_not_dominates hheavy hpickFs hpickFt hpickSt
    hpos.le (hnoTriple _ _ _ hpickFs hpickFt hpickSt) with hedge | hedge | hedge
  · exact ⟨first, second, hfs, hedge⟩
  · exact ⟨first, third, hft, hedge⟩
  · exact ⟨second, third, hst, hedge⟩

/-- The radical reading of the failure consequence: the forced edge has
`|rho| > 1/sqrt 2 = sqrt 2 / 2`. Stated separately because the squared form is the
one the campaign's exact-rational sign tests consume. -/
theorem exists_abs_normalizedPairing_gt_of_five_atoms {m : ℕ} {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) (pick : Fin 5 → Fin m) (hinjective : Function.Injective pick)
    (hnonzero : ∀ first second : Fin 5, first ≠ second →
      atomPairing D (pick first) (pick second) ≠ 0)
    (hnoTriple : ∀ first second third : Fin m, first ≠ second → first ≠ third →
      second ≠ third → ¬ Dominates D {first, second, third}) :
    ∃ first second : Fin 5, first ≠ second
      ∧ Real.sqrt 2 / 2 < |normalizedPairing D (pick first) (pick second)| := by
  obtain ⟨first, second, hne, hsquare⟩ :=
    exists_normalizedPairing_sq_gt_half_of_five_atoms hheavy pick hinjective hnonzero hnoTriple
  refine ⟨first, second, hne, ?_⟩
  have hsqrtTwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [abs_nonneg (normalizedPairing D (pick first) (pick second)),
    sq_abs (normalizedPairing D (pick first) (pick second)), hsquare, hsqrtTwo, hsqrtPos]

end Gtz
