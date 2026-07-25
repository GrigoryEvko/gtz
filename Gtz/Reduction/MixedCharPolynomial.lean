/-
# The volume-sampling mixed characteristic polynomial, and the refutation of its root bound

The shadow determinants `det P_T` of the `k`-subsets are nonnegative and sum to
one (`Gtz.shadowDeterminant_nonneg`, `Gtz.sum_shadowDeterminant_eq_one`), so they
are a probability measure on `k`-subsets — volume sampling, the projection
determinantal measure.  Mixing the characteristic polynomials of the subset atom
sums against it gives

    mixedCharPoly D  :=  ∑_{|T| = k} det P_T · charpoly(S_T),

monic of degree `k` (`mixedCharPoly_monic`, `mixedCharPoly_natDegree`).  The route
this file was built to test:

  (i)   for a homogeneous STRONGLY RAYLEIGH measure the polynomials
        `charpoly(∑_{c ∈ T} g_c g_cᵀ)` form an INTERLACING FAMILY;
  (ii)  an interlacing family has a leaf whose SMALLEST root is at least the
        mixture's smallest root;
  (iii) the mixture's smallest root is at least `1` on every all-heavy design.

Then (iii) + (ii) + (i) give a `k`-subset with `λ_min(S_T) ≥ 1`, i.e. domination,
i.e. GTZ on the all-heavy stratum — which is exactly what
`Gtz.rank_three_of_heavy_residuals` consumes.

**Step (iii) is FALSE at BOTH residual sizes.**  It is refuted here at `(6,3)` and
at `(7,3)`, by exact designs.  Steps (i) and (ii) are, on the contrary, backed by
published theorems (see the citation ledger below) — the route dies on its own
analytic half, not on the borrowed one.

## The ledger

**PROVED — the general kit.**

  * `mixedCharPoly`, `mixedCharPoly_monic`, `mixedCharPoly_natDegree`,
    `mixedCharPoly_eval` — the mixture, its monicity and degree, and its value at
    a level as the shadow-weighted average of `det(level·I − S_T)`.
  * `shadowDeterminant_eq_weightProduct_mul_detSubsetSum` — the enumeration-free
    evaluation `det P_T = (∏_{c ∈ T} t_c) · det S_T`.  At selection size exactly
    the rank the selected-row matrix is square, so the squared determinant of
    `Gtz.shadowDeterminant_eq_weightProduct_mul_detSq` becomes the determinant of
    `MᵀM = S_T` and the chosen enumeration disappears.  This is what makes every
    numerical claim below a function of the SUBSET, never of an ordering.
  * `mixedCharPoly_eval_zero` — **the value at zero, closed form, every design**:
    `eval 0 = (−1)^k · ∑_T (∏_{c ∈ T} t_c) · (det S_T)²`.  Every term is a
    weight-product times a SQUARE, so at odd rank the mixture is nonpositive at
    zero for structural reasons (`mixedCharPoly_eval_zero_nonpos_of_odd`) and
    strictly negative as soon as one `k`-subset is nonsingular
    (`mixedCharPoly_eval_zero_neg_of_odd`).  Both refutations below use this and
    therefore need only ONE decided aggregate each — the level-one one.
  * `shadowDeterminant_eq_zero_of_atom_eq` — a repeated atom kills the score.
  * `mixedCharPoly_eq_of_classes` — the constant-mixture lemma: if every subset
    either has zero shadow mass or carries the same characteristic polynomial,
    the mixture IS that polynomial.  No enumeration of the `C(m,k)` subsets
    anywhere; `sum_shadowDeterminant_eq_one` does the aggregation.

**PROVED — the extremal tightness, exactly.**  `mixedCharPoly_splitSevenDesign`:
at the split tetrahedron (`Gtz.splitSevenDesign`, the `(7,3)` design that is the
regular tetrahedron with three directions halved) the mixture is `(X − 1)(X − 4)²`
ON THE NOSE.  Its smallest root is exactly `1`
(`mixedCharPoly_splitSevenDesign_isRoot_one`,
`mixedCharPoly_splitSevenDesign_noRoot_below_one`): the conjectured bound holds
there with ZERO slack.  Mechanism: fifteen of the thirty-five triples repeat a
tetrahedron direction and carry shadow mass zero; the other twenty have atom sum
`4·I − d_j d_jᵀ` for the missing direction `j`, spectrum `(1,4,4)` regardless of
`j`.  This is why the refutations had to be searched for rather than stumbled on.

**PROVED — the two refutations.**

  * `(6,3)`, `rootKillDesign`: the **D₃ root system**.  Atoms `√(3/2)·v_c` along
    the six vectors `±e_i ± e_j`, written `(0,1,−1), (0,1,1), (1,−1,0), (1,0,−1),
    (1,0,1), (1,1,0)`, at uniform weight `1/6`.  Parseval is the integer identity
    `∑_c v_c v_cᵀ = 4·I₃`; every leverage is exactly `3` (`leverageOf_rootKillAtom`),
    so the design sits on the SAME constant-leverage slice as the split
    tetrahedron.  Sixteen of the twenty triples carry shadow mass exactly `1/16`
    and four — the linearly dependent ones — carry zero; ON THOSE SIXTEEN
    `det(I − S_T)` takes only two values, `−5/4` on the four dominating triples
    and `+1` on the other twelve.  Hence
    `mixedCharPoly_rootKillDesign_eval_one = 7/16 > 0`, while
    `mixedCharPoly_rootKillDesign_eval_zero_neg` is negative for free, so there is
    a root strictly inside `(0,1)` (`exists_root_rootKillDesign_lt_one`) and
    `not_mixedRootAtLeastOne_sixThree`.
  * `(7,3)`, `axisKillDesign`: the four tetrahedron directions — the sign vectors
    `(±1,±1,±1)` with an EVEN number of minus signs — plus the three DOUBLED axes
    `(2,0,0), (0,2,0), (0,0,2)`, at uniform weight `1/7`, atoms `√(7/8)·v_c`.
    Parseval is `∑_c v_c v_cᵀ = 8·I₃`.  Leverages are `21/8` and `7/2` — this
    design is OFF the constant-leverage slice, so it is an independent point of
    the stratum and NOT a padding of the `(6,3)` witness.
    `mixedCharPoly_axisKillDesign_eval_one = 11/256 > 0`, root in `(0,1)`,
    `not_mixedRootAtLeastOne_sevenThree`.
  * `not_mixedRootAtLeastOne_rankThreeResiduals` — the conjunction of negations,
    so the route fails at each residual size separately, not merely jointly.
  * `rootKillDesign_hasDominatingSubset`, `axisKillDesign_hasDominatingSubset` —
    **GTZ HOLDS at both witnesses.**  At `rootKillDesign` the triple `{0,2,4}` has
    `S_T − I = (1/2)·I + (3/2)·u uᵀ` for `u = (1,−1,1)`; at `axisKillDesign` the
    three doubled axes `{4,5,6}` give `S_T − I = (5/2)·I` outright.  So what is
    refuted is the BOUND, not the conjecture.

**CONDITIONAL on named `Prop`s.**  `gtzWeightedHeavy_of_mixtureInterlacesAt` is
the route assembled: `MixtureInterlacesAt m k 1` (steps (i)+(ii), stated
root-free so no existence-of-a-real-root claim is smuggled in) plus
`MixedRootAtLeastOne m k` (step (iii)) give `GtzWeightedHeavy m k`.  Both
hypotheses are consumed explicitly and nothing else is used.  Since the second is
false at both residual sizes, the implication is sound but unusable at rank three.

**CITED — and what the citations actually say.**  `MixtureInterlacesAt` is not
mechanized here, but it is NOT an open question either; calling it "neither proved
nor refuted" would undersell it.  Both halves are published:

  * step (i) — Anari and Oveis Gharan, *The Kadison–Singer Problem for Strongly
    Rayleigh Measures and Applications to Asymmetric TSP*, arXiv:1412.1143,
    Theorem 3.3 (with Corollary 3.2): for a homogeneous strongly Rayleigh measure
    the polynomials `q_S(x) = μ(S)·χ[∑_{i ∈ S} 2 v_i v_iᵀ](x²)` form an
    interlacing family, the vectors being arbitrary and decoupled from `μ`.  Their
    §2 defines exactly the measure used here — `μ(T) ∝ det(∑_{i ∈ T} λ_i v_i v_iᵀ)`,
    determinantal with respect to the projection Gram, hence strongly Rayleigh by
    Borcea–Brändén–Liggett.
  * step (ii) — Marcus, Spielman and Srivastava, *Interlacing Families III:
    Sharper Restricted Invertibility Estimates*, arXiv:1712.07766, Theorem 2.7:
    for an interlacing family and EVERY index `j` there are leaves `a`, `b` with
    `λ_j(f_a) ≥ λ_j(f_∅) ≥ λ_j(f_b)`, where `f_∅` is the convex combination and
    `λ_j` is the `j`-th largest zero.  NOTE the paper's headline result —
    restricted invertibility — is on this campaign's dead-routes list; Theorem 2.7
    is not that result but the generic interlacing-family bound, which is why it is
    quoted here.  Taking `j = k` gives the SMALLEST root directly: no reflection
    `x ↦ −x` is needed, and an earlier version of this header wrongly flagged one
    as an open check.

  Provenance of those two quotations, precisely: MSS Theorem 2.7 was read verbatim
  by two independent reviewers.  The AOG statement was read verbatim by one; a
  second could not retrieve that paper's source and confirmed only its title,
  authors and subject, so AOG's THEOREM NUMBERING rests on a single reading.
  Neither paper's PROOF was checked, and Borcea–Brändén–Liggett — the step that
  makes a determinantal measure strongly Rayleigh — is asserted by AOG and taken on
  trust here.

  The one genuine assembly step is the change of variable between them: AOG's
  family is even in `x` (their polynomials are `χ(x²)`), MSS's bound is in the
  eigenvalue variable.  Because every `S_T` is positive semidefinite the mixture's
  roots are all `≥ 0`, so `x ↦ x²` is an order isomorphism between the `k` largest
  zeros of the even degree-`2k` family and the `k` zeros in the eigenvalue
  variable, and the composite goes through.  That reindexing is DERIVED BY HAND,
  not quoted, and nothing in this file depends on it.

  Independently: at level one the hypothesis is a CONSEQUENCE of the conjecture
  (`mixtureInterlacesAtOne_of_gtzWeighted`), because `MixtureInterlacesAt m k 1`'s
  conclusion is literally GTZ's.  So `MixtureInterlacesAt m k 1` cannot be refuted
  without refuting GTZ, and only levels strictly below one carry independent
  content.  The salvage interface
  (`exists_leastEigenvalue_ge_of_mixtureInterlacesAt`) is level-parametric for
  exactly that reason.

**MEASURED, not mechanized.**  All numbers below were found and cross-checked in
exact rational arithmetic outside Lean; only what this file states is mechanized.

  * `rootKillDesign`'s mixture is `X³ − 9X² + (351/16)X − 27/2`, smallest root
    `0.94007381475321202413…`, `eval 0 = −27/2`.  Only `eval 1 = 7/16`, the sign
    of `eval 0`, and the resulting sign change are proved here.
  * `axisKillDesign`'s mixture is `X³ − (147/16)X² + (735/32)X − 3773/256`,
    smallest root `0.99436743793369736147…`, `eval 0 = −3773/256`.  Same caveat.
  * Four of `rootKillDesign`'s twenty triples dominate, and thirteen of
    `axisKillDesign`'s thirty-five; one of each is exhibited.
  * An earlier `(6,3)` witness with a DEEPER root is on record and was dropped for
    a simpler one: atoms `√(3/5)·v_c` along `(0,1,2), (0,1,−2), (1,2,0), (1,−2,0),
    (2,0,1), (−2,0,1)`, Parseval `10·I₃`, all leverages `3`, mixture
    `X³ − 9X² + (2727/125)X − 41823/3125`, `eval 1 = 1352/3125`, smallest root
    `0.93975305783565639473…`, ten of twenty triples dominating.  It refutes the
    same statement with larger integers (aggregates `54080` and `61960` against
    `224`), so it buys nothing and is not mechanized.
  * Splitting any atom of a witness into parallel copies at ANY ratio leaves the
    mixture EXACTLY unchanged, so witnesses exist at every `m ≥ 6`.  Not needed
    and not mechanized: `axisKillDesign` covers `(7,3)` on its own merits.
  * A separate search reports the infimum of the mixture's smallest root over
    all-heavy `(m,3)` designs to be `0.910432248406…` for every `m ≥ 6`, attained
    on the equal-leverage stratum by an icosahedral design, and to be exactly `1`
    at `m = 4, 5` and at rank two.  Not proved, not used; if true it means the
    route WOULD prove GTZ at rank two and misses at rank three by about nine per
    cent.

**The danger zone, confirmed.**  The route's own stated risk was designs where
failing triples carry large determinants and out-mass the dominating ones.  That
is exactly the mechanism at `rootKillDesign`: the four dominating triples carry
`det(I − S_T) = −5/4` each but the twelve failing ones carry `+1` each, and
`4·(−5/4) + 12·(+1) = 7 > 0` pushes `mixedCharPoly(1)` positive.  The tetrahedron
avoids it only because its failing triples are linearly DEPENDENT and therefore
weightless.

## What survives for a future interlacing attempt

The enumeration-free shadow evaluation, the closed form at zero, the
constant-mixture lemma, the exact extremal computation, and the two named `Prop`s
with their honest implication.  The interlacing half is untouched by the
refutations; a bound weaker than `1` — the numerics suggest `0.9104…` is the true
infimum at rank three — would still be a theorem about `max_T λ_min`, just not one
strong enough for GTZ.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm
import Gtz.Quantitative.DecisionAtlasSevenThree
import Gtz.Reduction.ExchangeInvariant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The mixture -/

/-- **The mixed characteristic polynomial** of a weighted design: the
volume-sampling mixture of the characteristic polynomials of its `k`-subset atom
sums, each weighted by the shadow determinant `det P_T` of that subset.  Since
the shadow determinants are nonnegative (`shadowDeterminant_nonneg`) and sum to
one (`sum_shadowDeterminant_eq_one`) this is a genuine convex combination of
monic degree-`k` polynomials, hence itself monic of degree `k`. -/
noncomputable def mixedCharPoly (D : WeightedDesign m k) : Polynomial ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
    shadowDeterminant D selected • (subsetSum D selected).charpoly

/-- The coefficient of the mixture at the top degree is the total shadow mass,
which is one. -/
theorem mixedCharPoly_coeff_rank (D : WeightedDesign m k) :
    (mixedCharPoly D).coeff k = 1 := by
  rw [mixedCharPoly, Polynomial.finsetSum_coeff]
  rw [← sum_shadowDeterminant_eq_one D]
  refine Finset.sum_congr rfl fun selected _ => ?_
  rw [Polynomial.coeff_smul, smul_eq_mul]
  have hleading : (subsetSum D selected).charpoly.coeff k = 1 := by
    have hmonic := (Matrix.charpoly_monic (subsetSum D selected)).leadingCoeff
    have hdegree : (subsetSum D selected).charpoly.natDegree = k := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    rwa [Polynomial.leadingCoeff, hdegree] at hmonic
  rw [hleading, mul_one]

/-- Every summand of the mixture has degree at most the rank, so the mixture
does. -/
theorem mixedCharPoly_natDegree_le (D : WeightedDesign m k) :
    (mixedCharPoly D).natDegree ≤ k := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun selected _ => ?_
  refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- **The mixture is monic.**  A convex combination of monic degree-`k`
polynomials has leading coefficient `∑ w_T = 1` at degree `k` and nothing
above. -/
theorem mixedCharPoly_monic (D : WeightedDesign m k) : (mixedCharPoly D).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one k (mixedCharPoly_natDegree_le D)
    (mixedCharPoly_coeff_rank D)

/-- **The mixture has degree exactly the rank.** -/
theorem mixedCharPoly_natDegree (D : WeightedDesign m k) :
    (mixedCharPoly D).natDegree = k := by
  refine le_antisymm (mixedCharPoly_natDegree_le D) ?_
  refine Polynomial.le_natDegree_of_ne_zero ?_
  rw [mixedCharPoly_coeff_rank D]
  exact one_ne_zero

/-- The mixture is not the zero polynomial. -/
theorem mixedCharPoly_ne_zero (D : WeightedDesign m k) : mixedCharPoly D ≠ 0 :=
  (mixedCharPoly_monic D).ne_zero_of_ne (by norm_num : (0 : ℝ) ≠ 1)

/-- **Evaluating the mixture**: at every level the value is the shadow-weighted
average of the shifted determinants `det(level·I − S_T)`.  This is the only form
in which the mixture is ever computed below. -/
theorem mixedCharPoly_eval (D : WeightedDesign m k) (level : ℝ) :
    (mixedCharPoly D).eval level
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          shadowDeterminant D selected
            * (Matrix.scalar (Fin k) level - subsetSum D selected).det := by
  rw [mixedCharPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun selected _ => ?_
  rw [Polynomial.eval_smul, smul_eq_mul, Matrix.eval_charpoly]

/-! ## Reading the shadow determinant off the subset, with no enumeration

`Gtz.shadowDeterminant_eq_weightProduct_mul_detSq` evaluates the score along a
chosen enumeration of the subset.  At selection size exactly the rank the
selected-row matrix is SQUARE, so its squared determinant is the determinant of
`MᵀM = S_T` itself, and the enumeration disappears: both factors below are
manifestly functions of the subset alone.  Every numerical claim about the
mixture goes through this form. -/

/-- **The enumeration-free evaluation**: `det P_T = (∏_{c ∈ T} t_c) · det S_T`. -/
theorem shadowDeterminant_eq_weightProduct_mul_detSubsetSum (D : WeightedDesign m k)
    {selected : Finset (Fin m)} (hcard : selected.card = k) :
    shadowDeterminant D selected
      = (∏ atomIndex ∈ selected, D.weight atomIndex) * (subsetSum D selected).det := by
  have hgram : (selectedAtomRows D (selected.orderEmbOfFin hcard))ᵀ
      * selectedAtomRows D (selected.orderEmbOfFin hcard) = subsetSum D selected := by
    rw [transpose_mul_selectedAtomRows D _ (selected.orderEmbOfFin hcard).injective,
      image_orderEmbOfFin hcard]
  have hdet : (selectedAtomRows D (selected.orderEmbOfFin hcard)).det ^ 2
      = (subsetSum D selected).det := by
    rw [← hgram, Matrix.det_mul, Matrix.det_transpose, ← pow_two]
  have hweights : (∏ selectedIndex, D.weight (selected.orderEmbOfFin hcard selectedIndex))
      = ∏ atomIndex ∈ selected, D.weight atomIndex := by
    conv_rhs => rw [← image_orderEmbOfFin hcard]
    exact (Finset.prod_image fun left _ right _ hpair =>
      (selected.orderEmbOfFin hcard).injective hpair).symm
  rw [shadowDeterminant_eq_orderEmb D hcard, hdet, hweights]

/-- **A repeated atom kills the shadow determinant.**  Two distinct selected
indices carrying the same vector give the selected-row matrix two equal rows, so
its determinant — and with it the score — vanishes.  This is the mechanism by
which a subset repeating a direction contributes nothing to the mixture. -/
theorem shadowDeterminant_eq_zero_of_atom_eq (D : WeightedDesign m k)
    {selected : Finset (Fin m)} (hcard : selected.card = k)
    {firstAtom secondAtom : Fin m} (hfirstMem : firstAtom ∈ selected)
    (hsecondMem : secondAtom ∈ selected) (hne : firstAtom ≠ secondAtom)
    (hsameVector : D.atom firstAtom = D.atom secondAtom) :
    shadowDeterminant D selected = 0 := by
  have himage := image_orderEmbOfFin (selected := selected) hcard
  obtain ⟨firstIndex, -, hfirstIndex⟩ : ∃ index ∈ (Finset.univ : Finset (Fin k)),
      selected.orderEmbOfFin hcard index = firstAtom :=
    Finset.mem_image.mp (by rw [himage]; exact hfirstMem)
  obtain ⟨secondIndex, -, hsecondIndex⟩ : ∃ index ∈ (Finset.univ : Finset (Fin k)),
      selected.orderEmbOfFin hcard index = secondAtom :=
    Finset.mem_image.mp (by rw [himage]; exact hsecondMem)
  have hindexNe : firstIndex ≠ secondIndex := by
    intro hsame
    exact hne (by rw [← hfirstIndex, ← hsecondIndex, hsame])
  have hrowEq : selectedAtomRows D (selected.orderEmbOfFin hcard) firstIndex
      = selectedAtomRows D (selected.orderEmbOfFin hcard) secondIndex := by
    funext coord
    simp only [selectedAtomRows, Matrix.of_apply, hfirstIndex, hsecondIndex]
    exact congrFun hsameVector coord
  rw [shadowDeterminant_eq_orderEmb D hcard,
    Matrix.det_zero_of_row_eq hindexNe hrowEq]
  ring

/-! ## The mixture at zero, in closed form

Substituting `level = 0` turns `det(level·I − S_T)` into `(−1)^k det S_T`, and the
enumeration-free shadow evaluation contributes another `det S_T`.  So every term
of the mixture at zero is a positive weight product times a SQUARE, and the sign
of `eval 0` is decided by the parity of the rank alone — no arithmetic over the
`C(m,k)` subsets is needed.  Both refutations below get their negative endpoint
from this and therefore each decide only ONE aggregate, at level one. -/

/-- **The mixture at zero, closed form, for every design.** -/
theorem mixedCharPoly_eval_zero (D : WeightedDesign m k) :
    (mixedCharPoly D).eval 0
      = (-1 : ℝ) ^ k * ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (∏ atomIndex ∈ selected, D.weight atomIndex) * (subsetSum D selected).det ^ 2 := by
  rw [mixedCharPoly_eval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun selected hmem => ?_
  have hcard : selected.card = k := (Finset.mem_powersetCard.mp hmem).2
  have hneg : Matrix.scalar (Fin k) (0 : ℝ) - subsetSum D selected
      = -subsetSum D selected := by
    rw [map_zero, zero_sub]
  rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum D hcard, hneg, Matrix.det_neg,
    Fintype.card_fin]
  ring

/-- The sum of squares appearing in `mixedCharPoly_eval_zero` is nonnegative:
weights are positive and determinants are squared. -/
theorem sum_weightProduct_mul_detSubsetSum_sq_nonneg (D : WeightedDesign m k) :
    0 ≤ ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (∏ atomIndex ∈ selected, D.weight atomIndex) * (subsetSum D selected).det ^ 2 :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Finset.prod_nonneg fun atomIndex _ => (D.weight_pos atomIndex).le) (sq_nonneg _)

/-- **At odd rank the mixture is nonpositive at zero, for every design.**  Nothing
about the design enters beyond positivity of the weights. -/
theorem mixedCharPoly_eval_zero_nonpos_of_odd (D : WeightedDesign m k) (hodd : Odd k) :
    (mixedCharPoly D).eval 0 ≤ 0 := by
  rw [mixedCharPoly_eval_zero, hodd.neg_one_pow, neg_one_mul, neg_nonpos]
  exact sum_weightProduct_mul_detSubsetSum_sq_nonneg D

/-- **At odd rank one nonsingular `k`-subset makes the mixture strictly negative
at zero.**  This replaces a decided aggregate at level zero in every refutation
below: only the level-one endpoint has to be computed. -/
theorem mixedCharPoly_eval_zero_neg_of_odd (D : WeightedDesign m k) (hodd : Odd k)
    {witness : Finset (Fin m)} (hcard : witness.card = k)
    (hdet : (subsetSum D witness).det ≠ 0) :
    (mixedCharPoly D).eval 0 < 0 := by
  have hmem : witness ∈ (Finset.univ : Finset (Fin m)).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  have hpos : 0 < (∏ atomIndex ∈ witness, D.weight atomIndex)
      * (subsetSum D witness).det ^ 2 :=
    mul_pos (Finset.prod_pos fun atomIndex _ => D.weight_pos atomIndex)
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hdet)))
  have hsum : 0 < ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      (∏ atomIndex ∈ selected, D.weight atomIndex) * (subsetSum D selected).det ^ 2 :=
    Finset.sum_pos' (fun selected _ =>
      mul_nonneg (Finset.prod_nonneg fun atomIndex _ => (D.weight_pos atomIndex).le)
        (sq_nonneg _)) ⟨witness, hmem, hpos⟩
  rw [mixedCharPoly_eval_zero, hodd.neg_one_pow, neg_one_mul, neg_neg_iff_pos]
  exact hsum

/-! ## The mixture collapses when every weighted subset carries one polynomial -/

/-- **The constant-mixture lemma.**  If every `k`-subset either has shadow mass
zero or has the SAME characteristic polynomial `target`, then the mixture IS
`target` — because the shadow determinants sum to one.  No enumeration of the
`C(m,k)` subsets is performed anywhere; the identity
`Gtz.sum_shadowDeterminant_eq_one` does the whole aggregation. -/
theorem mixedCharPoly_eq_of_classes (D : WeightedDesign m k) (target : Polynomial ℝ)
    (hclass : ∀ selected : Finset (Fin m), selected.card = k →
      shadowDeterminant D selected = 0 ∨ (subsetSum D selected).charpoly = target) :
    mixedCharPoly D = target := by
  have hcollapse : mixedCharPoly D
      = (∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          shadowDeterminant D selected) • target := by
    rw [mixedCharPoly, Finset.sum_smul]
    refine Finset.sum_congr rfl fun selected hmem => ?_
    rcases hclass selected (Finset.mem_powersetCard.mp hmem).2 with hzero | hsame
    · rw [hzero, zero_smul, zero_smul]
    · rw [hsame]
  rw [hcollapse, sum_shadowDeterminant_eq_one D, one_smul]

/-! ## The characteristic polynomial of a `3 × 3` matrix, expanded -/

/-- The characteristic polynomial of a `3 × 3` real matrix in coefficient form:
`X³ − tr·X² + e₂·X − det`, with every coefficient written out in the entries.
The only reason this is here is that the split tetrahedron's subset sums are
explicit `3 × 3` matrices and their characteristic polynomials have to be
evaluated. -/
theorem charpoly_fin_three_expand (target : Matrix (Fin 3) (Fin 3) ℝ) :
    target.charpoly = Polynomial.X ^ 3
      - Polynomial.C (target 0 0 + target 1 1 + target 2 2) * Polynomial.X ^ 2
      + Polynomial.C (target 0 0 * target 1 1 - target 0 1 * target 1 0
          + target 0 0 * target 2 2 - target 0 2 * target 2 0
          + target 1 1 * target 2 2 - target 1 2 * target 2 1) * Polynomial.X
      - Polynomial.C (target 0 0 * target 1 1 * target 2 2
          - target 0 0 * target 1 2 * target 2 1
          - target 0 1 * target 1 0 * target 2 2
          + target 0 1 * target 1 2 * target 2 0
          + target 0 2 * target 1 0 * target 2 1
          - target 0 2 * target 1 1 * target 2 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.reduceEq, if_false,
    if_true, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, zero_sub]
  ring

/-! ## The extremal fibre: the split tetrahedron at `(7,3)`

`Gtz.splitSevenDesign` is the regular tetrahedron with three of its four
directions halved (`Gtz.tripleSplitTetraDesign_eq_splitSevenDesign`).  Its
thirty-five triples split into exactly two classes: those repeating a direction,
which are linearly dependent and carry shadow mass ZERO, and the twenty carrying
three distinct directions, whose atom sum is `4·I − d_j d_jᵀ` for the missing
direction `j` and whose spectrum is therefore `(1, 4, 4)` regardless of `j`.  So
the mixture is a single polynomial and equals it exactly. -/

/-- The four tetrahedron atoms resolve `4·I` — the identity that makes a
three-distinct-direction triple a rank-one deficit of `4·I`.

`Gtz.Ties.StratumFirstOrder` proves the same fact as
`sum_atomMatrix_tetraAtom_eq_four_smul_one`.  It is restated rather than imported
because that file lives in the `Ties` layer and this one in `Reduction`, and a
`Reduction → Ties` dependency would invert the layering; the duplication is
deliberate and the two names are kept apart so that no import order can decide
which declaration a `#print axioms` reaches. -/
theorem sum_tetraAtomMatrix_eq_fourSmulOne :
    ∑ dirIndex : Fin 4, atomMatrix (tetraAtom dirIndex)
      = (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowCoord colCoord
  fin_cases rowCoord <;> fin_cases colCoord <;>
    simp only [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply, Fin.sum_univ_four,
      tetraAtom, Matrix.cons_val, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] <;>
    norm_num

/-- The spectrum `(1, 4, 4)` recognised from the three coefficients. -/
theorem charpoly_eq_oneFourFour_of_coefficients (target : Matrix (Fin 3) (Fin 3) ℝ)
    (htrace : target 0 0 + target 1 1 + target 2 2 = 9)
    (hsecond : target 0 0 * target 1 1 - target 0 1 * target 1 0
        + target 0 0 * target 2 2 - target 0 2 * target 2 0
        + target 1 1 * target 2 2 - target 1 2 * target 2 1 = 24)
    (hdeterminant : target 0 0 * target 1 1 * target 2 2 - target 0 0 * target 1 2 * target 2 1
        - target 0 1 * target 1 0 * target 2 2 + target 0 1 * target 1 2 * target 2 0
        + target 0 2 * target 1 0 * target 2 1 - target 0 2 * target 1 1 * target 2 0 = 16) :
    target.charpoly = (Polynomial.X - 1) * (Polynomial.X - 4) ^ 2 := by
  rw [charpoly_fin_three_expand, htrace, hsecond, hdeterminant]
  simp only [map_ofNat]
  ring

/-- **The spectrum of a three-direction triple.**  Whichever tetrahedron
direction is missing, the atom sum `4·I − d_j d_jᵀ` has characteristic
polynomial `(X − 1)(X − 4)²` — eigenvalue `1` along `d_j` and `4` on its
orthogonal complement, because `|d_j|² = 3`. -/
theorem charpoly_four_smul_sub_tetraAtom (missingDirection : Fin 4) :
    ((4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (tetraAtom missingDirection)).charpoly
      = (Polynomial.X - 1) * (Polynomial.X - 4) ^ 2 := by
  refine charpoly_eq_oneFourFour_of_coefficients _ ?_ ?_ ?_ <;>
    fin_cases missingDirection <;>
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, atomMatrix,
      Matrix.vecMulVec_apply, smul_eq_mul, tetraAtom, Fin.reduceEq, if_false, if_true] <;>
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- **A triple of distinct directions is a rank-one deficit of `4·I`.**  The
atom sum reindexes along the injective direction map onto the three carried
directions, and the fourth is subtracted from the resolution
`∑ d_i d_iᵀ = 4·I`. -/
theorem subsetSum_splitSevenDesign_of_distinctDirections {selected : Finset (Fin 7)}
    (hcard : selected.card = 3)
    (hdistinct : ∀ firstAtom ∈ selected, ∀ secondAtom ∈ selected,
      splitSevenDirection firstAtom = splitSevenDirection secondAtom → firstAtom = secondAtom) :
    ∃ missingDirection : Fin 4, subsetSum splitSevenDesign selected
      = (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (tetraAtom missingDirection) := by
  have hreindex : subsetSum splitSevenDesign selected
      = ∑ dirIndex ∈ selected.image splitSevenDirection, atomMatrix (tetraAtom dirIndex) := by
    rw [Finset.sum_image hdistinct]
    rfl
  have himageCard : (selected.image splitSevenDirection).card = 3 := by
    rw [Finset.card_image_of_injOn hdistinct, hcard]
  have hcomplCard : (selected.image splitSevenDirection)ᶜ.card = 1 := by
    rw [Finset.card_compl, himageCard, Fintype.card_fin]
  obtain ⟨missingDirection, hmissing⟩ := Finset.card_eq_one.mp hcomplCard
  refine ⟨missingDirection, ?_⟩
  have hsplit := Finset.sum_add_sum_compl (selected.image splitSevenDirection)
    (fun dirIndex => atomMatrix (tetraAtom dirIndex))
  rw [hmissing, Finset.sum_singleton, sum_tetraAtomMatrix_eq_fourSmulOne] at hsplit
  exact hreindex.trans (eq_sub_of_add_eq hsplit)

/-- **THE EXTREMAL TIGHTNESS, EXACTLY.**  At the split tetrahedron the mixed
characteristic polynomial is `(X − 1)(X − 4)²` on the nose: its smallest root is
exactly `1`, with no slack whatsoever.  The proof performs no enumeration — every
triple either repeats a direction (shadow mass zero,
`shadowDeterminant_eq_zero_of_atom_eq`) or carries three (characteristic
polynomial `(X − 1)(X − 4)²`), and `mixedCharPoly_eq_of_classes` aggregates. -/
theorem mixedCharPoly_splitSevenDesign :
    mixedCharPoly splitSevenDesign = (Polynomial.X - 1) * (Polynomial.X - 4) ^ 2 := by
  refine mixedCharPoly_eq_of_classes splitSevenDesign _ fun selected hcard => ?_
  by_cases hdistinct : ∀ firstAtom ∈ selected, ∀ secondAtom ∈ selected,
      splitSevenDirection firstAtom = splitSevenDirection secondAtom → firstAtom = secondAtom
  · obtain ⟨missingDirection, hsum⟩ :=
      subsetSum_splitSevenDesign_of_distinctDirections hcard hdistinct
    exact Or.inr (by rw [hsum, charpoly_four_smul_sub_tetraAtom])
  · push Not at hdistinct
    obtain ⟨firstAtom, hfirstMem, secondAtom, hsecondMem, hsameDirection, hne⟩ := hdistinct
    refine Or.inl (shadowDeterminant_eq_zero_of_atom_eq splitSevenDesign hcard hfirstMem
      hsecondMem hne ?_)
    rw [splitSevenDesign_atom, splitSevenDesign_atom, hsameDirection]

/-- The extremal mixture has `1` as a root and nothing below it: `(X − 1)(X − 4)²`
vanishes at `1`, and below `1` all three factors are negative, so the value is
strictly negative.  This is the exact boundary the conjecture below asks every
design to respect. -/
theorem mixedCharPoly_splitSevenDesign_eval_lt_zero {level : ℝ} (hlevel : level < 1) :
    (mixedCharPoly splitSevenDesign).eval level < 0 := by
  rw [mixedCharPoly_splitSevenDesign]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  have hfirst : level - 1 < 0 := by linarith
  have hsquare : 0 < (level - 4) ^ 2 := by nlinarith
  exact mul_neg_of_neg_of_pos hfirst hsquare

/-- The extremal mixture is rooted exactly at `1`. -/
theorem mixedCharPoly_splitSevenDesign_isRoot_one :
    (mixedCharPoly splitSevenDesign).IsRoot 1 := by
  rw [Polynomial.IsRoot, mixedCharPoly_splitSevenDesign]
  simp

/-! ## The conditional route, stated so that neither half can be overread

The route runs: (i) for a strongly Rayleigh measure the characteristic
polynomials of the sampled atom sums form an INTERLACING FAMILY; (ii) an
interlacing family has a leaf whose smallest root is at least the mixture's
smallest root; (iii) the mixture's smallest root is at least one on every
all-heavy design, so that leaf dominates.  Steps (i) and (ii) are exactly what
`MixtureInterlacesAt` packages — root-free, so that no separate existence-of-a-
real-root lemma is smuggled in — and step (iii) is `MixedRootAtLeastOne`.  The
implication below is the whole of the route, and it is honest: it consumes both
named hypotheses and nothing else.

Step (iii) is REFUTED at `(6,3)` and at `(7,3)` in the next sections, so the chain
cannot close at rank three.  Steps (i) and (ii) are untouched by that refutation;
both are published theorems, cited in the file header. -/

/-- **The interlacing conclusion, at a level.**  If the mixture has no root
strictly below `level`, some `k`-subset's least eigenvalue is at least `level`.
This is the composite of the two literature steps — Anari–Oveis Gharan's
interlacing family for a homogeneous strongly Rayleigh measure and the
Marcus–Spielman–Srivastava leaf bound at the smallest root — stated without
reference to roots so that it carries no hidden existence claim. -/
def MixtureInterlacesAt (m k : ℕ) [Nonempty (Fin k)] (level : ℝ) : Prop :=
  ∀ D : WeightedDesign m k,
    (∀ below : ℝ, below < level → (mixedCharPoly D).eval below ≠ 0) →
      ∃ selected : Finset (Fin m), selected.card = k ∧
        level ≤ lambdaMinMat (subsetSum D selected)

/-- **The analytic conjecture the route needed**: on every all-heavy design the
mixture has no real root strictly below one.  At the split tetrahedron this holds
with equality — the smallest root is exactly `1`
(`mixedCharPoly_splitSevenDesign`) — which is what made the conjecture look
plausible.  It is FALSE at both residual sizes:
`not_mixedRootAtLeastOne_sixThree`, `not_mixedRootAtLeastOne_sevenThree`. -/
def MixedRootAtLeastOne (m k : ℕ) : Prop :=
  ∀ D : WeightedDesign m k, AllHeavy D →
    ∀ level : ℝ, level < 1 → (mixedCharPoly D).eval level ≠ 0

/-- **THE ROUTE, assembled.**  The interlacing conclusion at level one plus the
root bound gives weighted GTZ on the all-heavy stratum — which is the stratum
`Gtz.rank_three_of_heavy_residuals` consumes.  Both hypotheses are named
`Prop`s; nothing else is used. -/
theorem gtzWeightedHeavy_of_mixtureInterlacesAt [Nonempty (Fin k)]
    (hinterlace : MixtureInterlacesAt m k 1)
    (hroot : MixedRootAtLeastOne m k) : GtzWeightedHeavy m k := by
  intro D hheavy
  obtain ⟨selected, hcard, hlevel⟩ := hinterlace D (hroot D hheavy)
  exact ⟨selected, hcard, (dominates_iff_one_le_lambdaMinMat D selected).mpr hlevel⟩

/-- **At level one the interlacing half is a CONSEQUENCE of the conjecture**, so
it cannot be refuted without refuting GTZ itself: `MixtureInterlacesAt m k 1`
asks for a `k`-subset with `1 ≤ λ_min(S_T)`, which
`dominates_iff_one_le_lambdaMinMat` says is exactly domination — and the
hypothesis about roots is simply discarded.  Consequence for the ledger: all the
independent content of `MixtureInterlacesAt` sits at levels strictly below one,
which is why the salvage interface below is level-parametric.  It also means the
refutations in this file could not have gone the other way: only the analytic
half was ever refutable at level one. -/
theorem mixtureInterlacesAtOne_of_gtzWeighted [Nonempty (Fin k)] (hgtz : GtzWeighted m k) :
    MixtureInterlacesAt m k 1 := by
  intro D _
  obtain ⟨selected, hcard, hdominates⟩ := hgtz D
  exact ⟨selected, hcard, (dominates_iff_one_le_lambdaMinMat D selected).mp hdominates⟩

/-! ## The integer scaffolding shared by both refutations

Both witnesses are integer direction systems rescaled by one square root, so that
every Gram matrix, every determinant and every aggregate below is an INTEGER
computation, and each real-valued step is a rescaling of one integer identity by
an explicit rational.  The single aggregate each witness decides is at level one;
level zero comes from `mixedCharPoly_eval_zero_neg_of_odd` with no arithmetic. -/

/-- The determinant of a `3 × 3` integer matrix, laid out exactly as
`Matrix.det_fin_three`. -/
def detThreeInt (entry : Fin 3 → Fin 3 → ℤ) : ℤ :=
  entry 0 0 * entry 1 1 * entry 2 2 - entry 0 0 * entry 1 2 * entry 2 1
    - entry 0 1 * entry 1 0 * entry 2 2 + entry 0 1 * entry 1 2 * entry 2 0
    + entry 0 2 * entry 1 0 * entry 2 1 - entry 0 2 * entry 1 1 * entry 2 0

/-! ## THE REFUTATION at `(6,3)`: the `D₃` root system

The six vectors `±e_i ± e_j` in `ℝ³`, uniformly weighted.  The integer identity
`∑_c v_c v_cᵀ = 4·I₃` makes `√(3/2)·v_c` an exact Parseval frame at weight `1/6`,
every leverage is exactly `3`, and the design is therefore strictly all-heavy and
sits on the constant-leverage slice the split tetrahedron also occupies.  Its
mixture is

    X³ − 9X² + (351/16)X − 27/2,

whose value at `1` is `+7/16 > 0` while at `0` it is negative for structural
reasons: a root in `(0,1)`, so `MixedRootAtLeastOne 6 3` is FALSE.  GTZ is
untouched — four of the twenty triples dominate and `{0,2,4}` is exhibited below
with an explicit positive-semidefinite decomposition.

Sixteen triples carry shadow mass exactly `1/16` and four (the linearly dependent
ones) carry zero; `det(I − S_T)` is `−5/4` on the four dominating triples and
`+1` on the other twelve, so the level-one aggregate is
`(1/16)·(4·(−5/4) + 12·(+1)) = 7/16` — the whole mechanism in one line. -/

/-- The six `D₃` roots `±e_i ± e_j`. -/
def rootKillVector : Fin 6 → Fin 3 → ℤ :=
  ![![0, 1, -1], ![0, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, 1], ![1, 1, 0]]

/-- **The integer Parseval identity** `∑_c v_c v_cᵀ = 4·I₃`. -/
theorem rootKillVector_parseval (rowCoord colCoord : Fin 3) :
    ∑ atomIndex : Fin 6, rootKillVector atomIndex rowCoord * rootKillVector atomIndex colCoord
      = if rowCoord = colCoord then 4 else 0 := by
  revert rowCoord colCoord
  decide

/-- Every root has squared length `2`. -/
theorem rootKillVector_lengthSq (atomIndex : Fin 6) :
    ∑ coord : Fin 3, rootKillVector atomIndex coord * rootKillVector atomIndex coord = 2 := by
  revert atomIndex
  decide

/-- The common scale `√(3/2)`: it turns the integer frame into a Parseval frame
at uniform weight `1/6`, since `(1/6)·(3/2)·4 = 1`. -/
noncomputable def rootKillScale : ℝ := Real.sqrt (3 / 2)

theorem rootKillScale_mul_self : rootKillScale * rootKillScale = 3 / 2 :=
  Real.mul_self_sqrt (by norm_num)

/-- The six real atoms. -/
noncomputable def rootKillAtom (atomIndex : Fin 6) : Fin 3 → ℝ :=
  fun coord => rootKillScale * (rootKillVector atomIndex coord : ℝ)

/-- **The `(6,3)` refuting design**: uniform weight `1/6`, exact Parseval. -/
noncomputable def rootKillDesign : WeightedDesign 6 3 where
  atom := rootKillAtom
  weight := fun _ => 1 / 6
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  isParseval := by
    ext rowCoord colCoord
    have hterm : ∀ atomIndex : Fin 6,
        (((1 : ℝ) / 6) • atomMatrix (rootKillAtom atomIndex)) rowCoord colCoord
          = (1 / 4 : ℝ)
            * ((rootKillVector atomIndex rowCoord * rootKillVector atomIndex colCoord : ℤ) : ℝ) := by
      intro atomIndex
      simp only [Matrix.smul_apply, smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply, rootKillAtom]
      push_cast
      linear_combination ((rootKillVector atomIndex rowCoord : ℝ)
        * (rootKillVector atomIndex colCoord : ℝ) / 6) * rootKillScale_mul_self
    rw [Matrix.sum_apply, Finset.sum_congr rfl (fun atomIndex _ => hterm atomIndex),
      ← Finset.mul_sum, ← Int.cast_sum, rootKillVector_parseval, Matrix.one_apply]
    by_cases hdiagonal : rowCoord = colCoord
    · rw [if_pos hdiagonal, if_pos hdiagonal]
      norm_num
    · rw [if_neg hdiagonal, if_neg hdiagonal]
      norm_num

@[simp] theorem rootKillDesign_atom (atomIndex : Fin 6) :
    rootKillDesign.atom atomIndex = rootKillAtom atomIndex := rfl

@[simp] theorem rootKillDesign_weight (atomIndex : Fin 6) :
    rootKillDesign.weight atomIndex = 1 / 6 := rfl

/-- **Every leverage is exactly `3`** — the design lies on the constant-leverage
slice, and is strictly all-heavy. -/
theorem leverageOf_rootKillAtom (atomIndex : Fin 6) : leverageOf (rootKillAtom atomIndex) = 3 := by
  have hinteger : ∑ coord : Fin 3,
      (rootKillVector atomIndex coord : ℝ) * (rootKillVector atomIndex coord : ℝ) = 2 := by
    have hcast := congrArg (fun value : ℤ => (value : ℝ)) (rootKillVector_lengthSq atomIndex)
    push_cast at hcast
    exact hcast
  have hterm : ∀ coord : Fin 3, rootKillAtom atomIndex coord ^ 2
      = (3 / 2 : ℝ) * ((rootKillVector atomIndex coord : ℝ)
          * (rootKillVector atomIndex coord : ℝ)) := by
    intro coord
    simp only [rootKillAtom]
    linear_combination ((rootKillVector atomIndex coord : ℝ)
      * (rootKillVector atomIndex coord : ℝ)) * rootKillScale_mul_self
  rw [leverageOf, Finset.sum_congr rfl (fun coord _ => hterm coord), ← Finset.mul_sum, hinteger]
  norm_num

theorem rootKillDesign_allHeavy : AllHeavy rootKillDesign := by
  intro atomIndex
  rw [rootKillDesign_atom, leverageOf_rootKillAtom]
  norm_num

/-- The integer Gram of a selected set of roots: `2/3` times the real atom sum,
entrywise. -/
def rootKillGram (selected : Finset (Fin 6)) (rowCoord colCoord : Fin 3) : ℤ :=
  ∑ atomIndex ∈ selected,
    rootKillVector atomIndex rowCoord * rootKillVector atomIndex colCoord

/-- The shadow determinant's integer numerator: `det P_T = (this)/64`. -/
def rootKillShadowNumerator (selected : Finset (Fin 6)) : ℤ :=
  detThreeInt (rootKillGram selected)

/-- The domination-gap numerator: `det(I − S_T) = (this)/8`. -/
def rootKillGapNumerator (selected : Finset (Fin 6)) : ℤ :=
  detThreeInt fun rowCoord colCoord =>
    2 * (if rowCoord = colCoord then 1 else 0) - 3 * rootKillGram selected rowCoord colCoord

/-- **The aggregate at level one**, over all twenty triples — one integer, decided.
It is `4 · (4·(−10) + 12·(+8)) = 224`: sixteen triples have Gram determinant `4`,
of which the four dominating ones carry gap numerator `−10` and the twelve failing
ones `+8`; the remaining four triples are linearly dependent and drop out. -/
theorem rootKillNumeratorSum_one :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      rootKillShadowNumerator selected * rootKillGapNumerator selected = 224 := by decide

theorem subsetSum_rootKillDesign_apply (selected : Finset (Fin 6)) (rowCoord colCoord : Fin 3) :
    subsetSum rootKillDesign selected rowCoord colCoord
      = (3 / 2 : ℝ) * ((rootKillGram selected rowCoord colCoord : ℤ) : ℝ) := by
  rw [subsetSum_apply, rootKillGram]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  show rootKillScale * (rootKillVector atomIndex rowCoord : ℝ)
      * (rootKillScale * (rootKillVector atomIndex colCoord : ℝ)) = _
  linear_combination ((rootKillVector atomIndex rowCoord : ℝ)
    * (rootKillVector atomIndex colCoord : ℝ)) * rootKillScale_mul_self

theorem det_subsetSum_rootKillDesign (selected : Finset (Fin 6)) :
    (subsetSum rootKillDesign selected).det
      = (27 / 8 : ℝ) * ((rootKillShadowNumerator selected : ℤ) : ℝ) := by
  rw [Matrix.det_fin_three]
  simp only [subsetSum_rootKillDesign_apply, rootKillShadowNumerator, detThreeInt]
  push_cast
  ring

theorem shadowDeterminant_rootKillDesign {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    shadowDeterminant rootKillDesign selected
      = ((rootKillShadowNumerator selected : ℤ) : ℝ) / 64 := by
  have hweights : (∏ atomIndex ∈ selected, rootKillDesign.weight atomIndex) = (1 / 6 : ℝ) ^ 3 := by
    rw [Finset.prod_congr rfl (fun atomIndex _ => rootKillDesign_weight atomIndex),
      Finset.prod_const, hcard]
  rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum rootKillDesign hcard, hweights,
    det_subsetSum_rootKillDesign]
  ring

theorem det_scalarOne_sub_subsetSum_rootKillDesign (selected : Finset (Fin 6)) :
    (Matrix.scalar (Fin 3) (1 : ℝ) - subsetSum rootKillDesign selected).det
      = ((rootKillGapNumerator selected : ℤ) : ℝ) / 8 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    subsetSum_rootKillDesign_apply, rootKillGapNumerator, detThreeInt, Fin.reduceEq, if_false,
    if_true]
  push_cast
  ring

/-- **The mixture is strictly positive at one**: `7/16`. -/
theorem mixedCharPoly_rootKillDesign_eval_one :
    (mixedCharPoly rootKillDesign).eval 1 = 7 / 16 := by
  rw [mixedCharPoly_eval]
  have hterm : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      shadowDeterminant rootKillDesign selected
          * (Matrix.scalar (Fin 3) (1 : ℝ) - subsetSum rootKillDesign selected).det
        = ((rootKillShadowNumerator selected * rootKillGapNumerator selected : ℤ) : ℝ)
            / 512 := by
    intro selected hmem
    rw [shadowDeterminant_rootKillDesign (Finset.mem_powersetCard.mp hmem).2,
      det_scalarOne_sub_subsetSum_rootKillDesign]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Int.cast_sum, rootKillNumeratorSum_one]
  norm_num

/-- The triple `{0,2,4}` is nonsingular: its integer Gram determinant is `4`. -/
theorem rootKillShadowNumerator_zeroTwoFour : rootKillShadowNumerator {0, 2, 4} = 4 := by decide

theorem det_subsetSum_rootKillDesign_zeroTwoFour_ne_zero :
    (subsetSum rootKillDesign {0, 2, 4}).det ≠ 0 := by
  rw [det_subsetSum_rootKillDesign, rootKillShadowNumerator_zeroTwoFour]
  norm_num

/-- **The mixture is strictly negative at zero** — no arithmetic over the twenty
triples: `mixedCharPoly_eval_zero_neg_of_odd` needs only the one nonsingular
triple. -/
theorem mixedCharPoly_rootKillDesign_eval_zero_neg :
    (mixedCharPoly rootKillDesign).eval 0 < 0 :=
  mixedCharPoly_eval_zero_neg_of_odd rootKillDesign (by decide) (by decide)
    det_subsetSum_rootKillDesign_zeroTwoFour_ne_zero

/-- **THE ROOT BELOW ONE at `(6,3)`.**  The mixture changes sign strictly inside
`(0,1)`, so by the intermediate value theorem it has a real root there. -/
theorem exists_root_rootKillDesign_lt_one :
    ∃ level : ℝ, 0 < level ∧ level < 1 ∧ (mixedCharPoly rootKillDesign).eval level = 0 := by
  have hcontinuous : ContinuousOn (fun level : ℝ => (mixedCharPoly rootKillDesign).eval level)
      (Set.Icc 0 1) := (mixedCharPoly rootKillDesign).continuous_aeval.continuousOn
  have hbelow : (mixedCharPoly rootKillDesign).eval 0 < 0 :=
    mixedCharPoly_rootKillDesign_eval_zero_neg
  have habove : 0 < (mixedCharPoly rootKillDesign).eval 1 := by
    rw [mixedCharPoly_rootKillDesign_eval_one]; norm_num
  have hmember : (0 : ℝ) ∈ Set.Icc ((mixedCharPoly rootKillDesign).eval 0)
      ((mixedCharPoly rootKillDesign).eval 1) := ⟨hbelow.le, habove.le⟩
  obtain ⟨level, hlevelMem, hlevelValue⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcontinuous hmember
  have hvalue : (mixedCharPoly rootKillDesign).eval level = 0 := hlevelValue
  refine ⟨level, ?_, ?_, hvalue⟩
  · rcases hlevelMem.1.lt_or_eq with hstrict | hzero
    · exact hstrict
    · rw [← hzero] at hvalue
      rw [hvalue] at hbelow
      exact absurd hbelow (lt_irrefl 0)
  · rcases hlevelMem.2.lt_or_eq with hstrict | hone
    · exact hstrict
    · rw [hone] at hvalue
      rw [hvalue] at habove
      exact absurd habove (lt_irrefl 0)

/-- **STEP (iii) IS FALSE at `(6,3)`.**  The witness is all-heavy and its mixture
has a root strictly between zero and one. -/
theorem not_mixedRootAtLeastOne_sixThree : ¬ MixedRootAtLeastOne 6 3 := by
  intro hroot
  obtain ⟨level, -, hlevelLt, hlevelRoot⟩ := exists_root_rootKillDesign_lt_one
  exact hroot rootKillDesign rootKillDesign_allHeavy level hlevelLt hlevelRoot

/-- The vector `u = (1, −1, 1)`: the triple `{0,2,4}`'s integer Gram is exactly
`I + u uᵀ`, which is what turns its atom sum into a domination certificate. -/
def rootKillWitnessVector : Fin 3 → ℤ := ![1, -1, 1]

/-- The real image of `u`, the rank-one direction of the certificate. -/
noncomputable def rootKillWitnessAtom : Fin 3 → ℝ :=
  fun coord => ((rootKillWitnessVector coord : ℤ) : ℝ)

theorem rootKillGram_zeroTwoFour (rowCoord colCoord : Fin 3) :
    rootKillGram {0, 2, 4} rowCoord colCoord
      = (if rowCoord = colCoord then 1 else 0)
        + rootKillWitnessVector rowCoord * rootKillWitnessVector colCoord := by
  revert rowCoord colCoord
  decide

/-- **GTZ holds at the `(6,3)` witness** — the triple `{0,2,4}`, whose atom sum
minus the identity is `(1/2)·I + (3/2)·u uᵀ` for `u = (1,−1,1)`, an explicit sum
of positive semidefinite matrices.  So the refutation is a refutation of the
BOUND, not of the conjecture. -/
theorem rootKillDesign_hasDominatingSubset :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates rootKillDesign selected := by
  refine ⟨{0, 2, 4}, by decide, ?_⟩
  have hdecomposition : subsetSum rootKillDesign {0, 2, 4} - 1
      = (1 / 2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + (3 / 2 : ℝ) • atomMatrix rootKillWitnessAtom := by
    ext rowCoord colCoord
    by_cases hdiagonal : rowCoord = colCoord
    · subst hdiagonal
      simp only [Matrix.sub_apply, subsetSum_rootKillDesign_apply, rootKillGram_zeroTwoFour,
        Matrix.one_apply_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        atomMatrix, Matrix.vecMulVec_apply, rootKillWitnessAtom]
      push_cast
      ring
    · simp only [Matrix.sub_apply, subsetSum_rootKillDesign_apply, rootKillGram_zeroTwoFour,
        if_neg hdiagonal, Matrix.one_apply_ne hdiagonal, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply, rootKillWitnessAtom]
      push_cast
      ring
  show (subsetSum rootKillDesign {0, 2, 4} - 1).PosSemidef
  rw [hdecomposition]
  exact (Matrix.PosSemidef.one.smul (by norm_num)).add
    ((posSemidef_atomMatrix _).smul (by norm_num))

/-! ## THE REFUTATION at `(7,3)`: tetrahedron plus doubled axes

The `(6,3)` witness could be padded to `(7,3)` by splitting one atom into two
parallel copies — the new triples are linearly dependent, carry shadow mass zero,
and the mixture is unchanged.  That padding is deliberately NOT what happens here.
The `(7,3)` witness below is an independent point of the stratum: the four
tetrahedron directions together with the three DOUBLED coordinate axes, at uniform
weight `1/7` and scale `√(7/8)`, with `∑_c v_c v_cᵀ = 8·I₃`.  Its leverages are
`21/8` on the tetrahedron atoms and `7/2` on the axes — it is OFF the
constant-leverage slice that both the split tetrahedron and the `(6,3)` witness
occupy, so it tests the conjecture somewhere genuinely different.  Its mixture is

    X³ − (147/16)X² + (735/32)X − 3773/256,

with `eval 1 = +11/256 > 0` and `eval 0` negative for structural reasons. -/

/-- The four tetrahedron directions followed by the three doubled coordinate
axes. -/
def axisKillVector : Fin 7 → Fin 3 → ℤ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1],
    ![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]

/-- **The integer Parseval identity** `∑_c v_c v_cᵀ = 8·I₃` — the tetrahedron
contributes `4·I₃` and the doubled axes another `4·I₃`. -/
theorem axisKillVector_parseval (rowCoord colCoord : Fin 3) :
    ∑ atomIndex : Fin 7, axisKillVector atomIndex rowCoord * axisKillVector atomIndex colCoord
      = if rowCoord = colCoord then 8 else 0 := by
  revert rowCoord colCoord
  decide

/-- Squared lengths are `3` on the tetrahedron and `4` on the axes; all that is
needed below is the lower bound. -/
theorem axisKillVector_lengthSq_ge (atomIndex : Fin 7) :
    3 ≤ ∑ coord : Fin 3, axisKillVector atomIndex coord * axisKillVector atomIndex coord := by
  revert atomIndex
  decide

/-- The common scale `√(7/8)`: it turns the integer frame into a Parseval frame at
uniform weight `1/7`, since `(1/7)·(7/8)·8 = 1`. -/
noncomputable def axisKillScale : ℝ := Real.sqrt (7 / 8)

theorem axisKillScale_mul_self : axisKillScale * axisKillScale = 7 / 8 :=
  Real.mul_self_sqrt (by norm_num)

/-- The seven real atoms. -/
noncomputable def axisKillAtom (atomIndex : Fin 7) : Fin 3 → ℝ :=
  fun coord => axisKillScale * (axisKillVector atomIndex coord : ℝ)

/-- **The `(7,3)` refuting design**: uniform weight `1/7`, exact Parseval. -/
noncomputable def axisKillDesign : WeightedDesign 7 3 where
  atom := axisKillAtom
  weight := fun _ => 1 / 7
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  isParseval := by
    ext rowCoord colCoord
    have hterm : ∀ atomIndex : Fin 7,
        (((1 : ℝ) / 7) • atomMatrix (axisKillAtom atomIndex)) rowCoord colCoord
          = (1 / 8 : ℝ)
            * ((axisKillVector atomIndex rowCoord * axisKillVector atomIndex colCoord : ℤ) : ℝ) := by
      intro atomIndex
      simp only [Matrix.smul_apply, smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply, axisKillAtom]
      push_cast
      linear_combination ((axisKillVector atomIndex rowCoord : ℝ)
        * (axisKillVector atomIndex colCoord : ℝ) / 7) * axisKillScale_mul_self
    rw [Matrix.sum_apply, Finset.sum_congr rfl (fun atomIndex _ => hterm atomIndex),
      ← Finset.mul_sum, ← Int.cast_sum, axisKillVector_parseval, Matrix.one_apply]
    by_cases hdiagonal : rowCoord = colCoord
    · rw [if_pos hdiagonal, if_pos hdiagonal]
      norm_num
    · rw [if_neg hdiagonal, if_neg hdiagonal]
      norm_num

@[simp] theorem axisKillDesign_atom (atomIndex : Fin 7) :
    axisKillDesign.atom atomIndex = axisKillAtom atomIndex := rfl

@[simp] theorem axisKillDesign_weight (atomIndex : Fin 7) :
    axisKillDesign.weight atomIndex = 1 / 7 := rfl

/-- The leverage is `7/8` times the integer squared length — `21/8` on the
tetrahedron atoms, `7/2` on the axes.  The design is therefore NOT on the
constant-leverage slice. -/
theorem leverageOf_axisKillAtom (atomIndex : Fin 7) :
    leverageOf (axisKillAtom atomIndex)
      = (7 / 8 : ℝ) * ((∑ coord : Fin 3,
          axisKillVector atomIndex coord * axisKillVector atomIndex coord : ℤ) : ℝ) := by
  have hterm : ∀ coord : Fin 3, axisKillAtom atomIndex coord ^ 2
      = (7 / 8 : ℝ) * ((axisKillVector atomIndex coord : ℝ)
          * (axisKillVector atomIndex coord : ℝ)) := by
    intro coord
    simp only [axisKillAtom]
    linear_combination ((axisKillVector atomIndex coord : ℝ)
      * (axisKillVector atomIndex coord : ℝ)) * axisKillScale_mul_self
  rw [leverageOf, Finset.sum_congr rfl (fun coord _ => hterm coord), ← Finset.mul_sum]
  push_cast
  ring

theorem axisKillDesign_allHeavy : AllHeavy axisKillDesign := by
  intro atomIndex
  rw [axisKillDesign_atom, leverageOf_axisKillAtom]
  have hlength : (3 : ℝ) ≤ ((∑ coord : Fin 3,
      axisKillVector atomIndex coord * axisKillVector atomIndex coord : ℤ) : ℝ) := by
    exact_mod_cast axisKillVector_lengthSq_ge atomIndex
  linarith

/-- The integer Gram of a selected set of directions: `8/7` times the real atom
sum, entrywise. -/
def axisKillGram (selected : Finset (Fin 7)) (rowCoord colCoord : Fin 3) : ℤ :=
  ∑ atomIndex ∈ selected,
    axisKillVector atomIndex rowCoord * axisKillVector atomIndex colCoord

/-- The shadow determinant's integer numerator: `det P_T = (this)/512`. -/
def axisKillShadowNumerator (selected : Finset (Fin 7)) : ℤ :=
  detThreeInt (axisKillGram selected)

/-- The domination-gap numerator: `det(I − S_T) = (this)/512`. -/
def axisKillGapNumerator (selected : Finset (Fin 7)) : ℤ :=
  detThreeInt fun rowCoord colCoord =>
    8 * (if rowCoord = colCoord then 1 else 0) - 7 * axisKillGram selected rowCoord colCoord

/-- **The aggregate at level one**, over all thirty-five triples — one integer,
decided. -/
theorem axisKillNumeratorSum_one :
    ∑ selected ∈ (Finset.univ : Finset (Fin 7)).powersetCard 3,
      axisKillShadowNumerator selected * axisKillGapNumerator selected = 11264 := by decide

theorem subsetSum_axisKillDesign_apply (selected : Finset (Fin 7)) (rowCoord colCoord : Fin 3) :
    subsetSum axisKillDesign selected rowCoord colCoord
      = (7 / 8 : ℝ) * ((axisKillGram selected rowCoord colCoord : ℤ) : ℝ) := by
  rw [subsetSum_apply, axisKillGram]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  show axisKillScale * (axisKillVector atomIndex rowCoord : ℝ)
      * (axisKillScale * (axisKillVector atomIndex colCoord : ℝ)) = _
  linear_combination ((axisKillVector atomIndex rowCoord : ℝ)
    * (axisKillVector atomIndex colCoord : ℝ)) * axisKillScale_mul_self

theorem det_subsetSum_axisKillDesign (selected : Finset (Fin 7)) :
    (subsetSum axisKillDesign selected).det
      = (343 / 512 : ℝ) * ((axisKillShadowNumerator selected : ℤ) : ℝ) := by
  rw [Matrix.det_fin_three]
  simp only [subsetSum_axisKillDesign_apply, axisKillShadowNumerator, detThreeInt]
  push_cast
  ring

theorem shadowDeterminant_axisKillDesign {selected : Finset (Fin 7)} (hcard : selected.card = 3) :
    shadowDeterminant axisKillDesign selected
      = ((axisKillShadowNumerator selected : ℤ) : ℝ) / 512 := by
  have hweights : (∏ atomIndex ∈ selected, axisKillDesign.weight atomIndex) = (1 / 7 : ℝ) ^ 3 := by
    rw [Finset.prod_congr rfl (fun atomIndex _ => axisKillDesign_weight atomIndex),
      Finset.prod_const, hcard]
  rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum axisKillDesign hcard, hweights,
    det_subsetSum_axisKillDesign]
  ring

theorem det_scalarOne_sub_subsetSum_axisKillDesign (selected : Finset (Fin 7)) :
    (Matrix.scalar (Fin 3) (1 : ℝ) - subsetSum axisKillDesign selected).det
      = ((axisKillGapNumerator selected : ℤ) : ℝ) / 512 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    subsetSum_axisKillDesign_apply, axisKillGapNumerator, detThreeInt, Fin.reduceEq, if_false,
    if_true]
  push_cast
  ring

/-- **The mixture is strictly positive at one**: `11/256`. -/
theorem mixedCharPoly_axisKillDesign_eval_one :
    (mixedCharPoly axisKillDesign).eval 1 = 11 / 256 := by
  rw [mixedCharPoly_eval]
  have hterm : ∀ selected ∈ (Finset.univ : Finset (Fin 7)).powersetCard 3,
      shadowDeterminant axisKillDesign selected
          * (Matrix.scalar (Fin 3) (1 : ℝ) - subsetSum axisKillDesign selected).det
        = ((axisKillShadowNumerator selected * axisKillGapNumerator selected : ℤ) : ℝ)
            / 262144 := by
    intro selected hmem
    rw [shadowDeterminant_axisKillDesign (Finset.mem_powersetCard.mp hmem).2,
      det_scalarOne_sub_subsetSum_axisKillDesign]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Int.cast_sum, axisKillNumeratorSum_one]
  norm_num

/-- The three doubled axes have integer Gram `4·I₃`. -/
theorem axisKillGram_fourFiveSix (rowCoord colCoord : Fin 3) :
    axisKillGram {4, 5, 6} rowCoord colCoord = if rowCoord = colCoord then 4 else 0 := by
  revert rowCoord colCoord
  decide

theorem axisKillShadowNumerator_fourFiveSix : axisKillShadowNumerator {4, 5, 6} = 64 := by decide

theorem det_subsetSum_axisKillDesign_fourFiveSix_ne_zero :
    (subsetSum axisKillDesign {4, 5, 6}).det ≠ 0 := by
  rw [det_subsetSum_axisKillDesign, axisKillShadowNumerator_fourFiveSix]
  norm_num

/-- **The mixture is strictly negative at zero** — again with no arithmetic over
the thirty-five triples. -/
theorem mixedCharPoly_axisKillDesign_eval_zero_neg :
    (mixedCharPoly axisKillDesign).eval 0 < 0 :=
  mixedCharPoly_eval_zero_neg_of_odd axisKillDesign (by decide) (by decide)
    det_subsetSum_axisKillDesign_fourFiveSix_ne_zero

/-- **THE ROOT BELOW ONE at `(7,3)`.** -/
theorem exists_root_axisKillDesign_lt_one :
    ∃ level : ℝ, 0 < level ∧ level < 1 ∧ (mixedCharPoly axisKillDesign).eval level = 0 := by
  have hcontinuous : ContinuousOn (fun level : ℝ => (mixedCharPoly axisKillDesign).eval level)
      (Set.Icc 0 1) := (mixedCharPoly axisKillDesign).continuous_aeval.continuousOn
  have hbelow : (mixedCharPoly axisKillDesign).eval 0 < 0 :=
    mixedCharPoly_axisKillDesign_eval_zero_neg
  have habove : 0 < (mixedCharPoly axisKillDesign).eval 1 := by
    rw [mixedCharPoly_axisKillDesign_eval_one]; norm_num
  have hmember : (0 : ℝ) ∈ Set.Icc ((mixedCharPoly axisKillDesign).eval 0)
      ((mixedCharPoly axisKillDesign).eval 1) := ⟨hbelow.le, habove.le⟩
  obtain ⟨level, hlevelMem, hlevelValue⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcontinuous hmember
  have hvalue : (mixedCharPoly axisKillDesign).eval level = 0 := hlevelValue
  refine ⟨level, ?_, ?_, hvalue⟩
  · rcases hlevelMem.1.lt_or_eq with hstrict | hzero
    · exact hstrict
    · rw [← hzero] at hvalue
      rw [hvalue] at hbelow
      exact absurd hbelow (lt_irrefl 0)
  · rcases hlevelMem.2.lt_or_eq with hstrict | hone
    · exact hstrict
    · rw [hone] at hvalue
      rw [hvalue] at habove
      exact absurd habove (lt_irrefl 0)

/-- **STEP (iii) IS FALSE at `(7,3)` TOO**, and not by padding the `(6,3)`
witness: `axisKillDesign` has two distinct leverages and so lies off the
constant-leverage slice. -/
theorem not_mixedRootAtLeastOne_sevenThree : ¬ MixedRootAtLeastOne 7 3 := by
  intro hroot
  obtain ⟨level, -, hlevelLt, hlevelRoot⟩ := exists_root_axisKillDesign_lt_one
  exact hroot axisKillDesign axisKillDesign_allHeavy level hlevelLt hlevelRoot

/-- **GTZ holds at the `(7,3)` witness** — the three doubled axes `{4,5,6}` have
atom sum `(7/2)·I`, so the gap is `(5/2)·I`, positive definite outright. -/
theorem axisKillDesign_hasDominatingSubset :
    ∃ selected : Finset (Fin 7), selected.card = 3 ∧ Dominates axisKillDesign selected := by
  refine ⟨{4, 5, 6}, by decide, ?_⟩
  have hdecomposition : subsetSum axisKillDesign {4, 5, 6} - 1
      = (5 / 2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext rowCoord colCoord
    by_cases hdiagonal : rowCoord = colCoord
    · subst hdiagonal
      simp only [Matrix.sub_apply, subsetSum_axisKillDesign_apply, axisKillGram_fourFiveSix,
        Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul]
      norm_num
    · simp only [Matrix.sub_apply, subsetSum_axisKillDesign_apply, axisKillGram_fourFiveSix,
        if_neg hdiagonal, Matrix.one_apply_ne hdiagonal, Matrix.smul_apply, smul_eq_mul]
      norm_num
  show (subsetSum axisKillDesign {4, 5, 6} - 1).PosSemidef
  rw [hdecomposition]
  exact Matrix.PosSemidef.one.smul (by norm_num)

/-! ## The ledger, as theorems -/

/-- **The extremal design DOES satisfy the conjecture, with zero slack.**  Below
one the split tetrahedron's mixture is strictly negative, so it has no root
there — and it has a root exactly AT one
(`mixedCharPoly_splitSevenDesign_isRoot_one`).  The conjecture is therefore tight
where it holds, which is why the refutations had to be searched for rather than
stumbled on. -/
theorem mixedCharPoly_splitSevenDesign_noRoot_below_one {level : ℝ} (hlevel : level < 1) :
    (mixedCharPoly splitSevenDesign).eval level ≠ 0 :=
  ne_of_lt (mixedCharPoly_splitSevenDesign_eval_lt_zero hlevel)

/-- **THE ROUTE IS DEAD AT RANK THREE, AT EACH RESIDUAL SIZE SEPARATELY.**
`Gtz.rank_three_of_heavy_residuals` consumes `GtzWeightedHeavy 6 3` AND
`GtzWeightedHeavy 7 3`, so the mixture route would have to supply both; it can
supply neither, because its analytic half is false at `(6,3)` and independently
false at `(7,3)`.  Nothing here bears on the conjecture: both witnesses satisfy
GTZ (`rootKillDesign_hasDominatingSubset`,
`axisKillDesign_hasDominatingSubset`). -/
theorem not_mixedRootAtLeastOne_rankThreeResiduals :
    ¬ MixedRootAtLeastOne 6 3 ∧ ¬ MixedRootAtLeastOne 7 3 :=
  ⟨not_mixedRootAtLeastOne_sixThree, not_mixedRootAtLeastOne_sevenThree⟩

/-- The conjunction the rank-three reduction would need is therefore
unavailable. -/
theorem not_mixedRootAtLeastOne_rankThreeConjunction :
    ¬ (MixedRootAtLeastOne 6 3 ∧ MixedRootAtLeastOne 7 3) :=
  fun hboth => not_mixedRootAtLeastOne_sixThree hboth.1

/-- **What the refutations do NOT touch, and the salvage interface.**  The route
runs at EVERY level, not just at one: interlacing at `level` plus "no root below
`level`" delivers a `k`-subset whose least eigenvalue is at least `level`.  Only
`level = 1` is strong enough for domination, and only `level = 1` is refuted.
`MixtureInterlacesAt` itself is neither proved nor refuted anywhere here — its
literature backing is in the file header, and at level one it is anyway implied by
GTZ (`mixtureInterlacesAtOne_of_gtzWeighted`).  A future attempt would replace the
refuted half by a bound at some level below one and would get a genuine — merely
insufficient — theorem about `max_T λ_min`. -/
theorem exists_leastEigenvalue_ge_of_mixtureInterlacesAt [Nonempty (Fin k)] {level : ℝ}
    (hinterlace : MixtureInterlacesAt m k level)
    (hbound : ∀ D : WeightedDesign m k, AllHeavy D →
      ∀ below : ℝ, below < level → (mixedCharPoly D).eval below ≠ 0)
    (D : WeightedDesign m k) (hheavy : AllHeavy D) :
    ∃ selected : Finset (Fin m), selected.card = k ∧
      level ≤ lambdaMinMat (subsetSum D selected) :=
  hinterlace D (hbound D hheavy)

end Gtz
