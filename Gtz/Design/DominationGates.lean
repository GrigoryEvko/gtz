/-
# Domination gates: orthogonal frames, saturated atoms, and the two counting laws

Four gates that all say "here is a structural reason a `k`-subset dominates" or
"here is a structural reason the counting attack has no purchase".  They are the
foundations layer the (7,3) squeeze workflows consume, so every statement here
is proved at the widest hypothesis the argument actually needs, and where the
repository already owns a narrower version the relationship is recorded.

## T7(a) — a pairwise-orthogonal frame dominates, at EVERY rank

`k` pairwise-orthogonal atoms of a rank-`k` design, each of leverage at least
one, dominate.  Normalizing gives `k` orthonormal vectors in `ℝᵏ`, so the row
matrix `U` satisfies `U Uᵀ = 1`; being SQUARE it also satisfies `Uᵀ U = 1`, which
IS `Σ_c u_c u_cᵀ = I_k`.  Then `S_C − I = Σ_c (ℓ_c − 1) u_c u_cᵀ ⪰ 0`.  No
eigenvalues, no dimension induction, no basis extension — one application of
`mul_eq_one_comm` and `Gtz.transpose_mul_self_eq_sum_rows`.

The repository already owns the rank-three instance
(`Gtz.dominates_of_orthogonalTriple`, `Gtz/Quantitative/DiscriminantSystem.lean`)
with STRICT heaviness `1 < ℓ`.  `dominates_of_orthogonalTriple_of_one_le` below
is that statement with the heaviness relaxed to `1 ≤ ℓ`, and it is a corollary of
the general-rank theorem rather than a second proof.  With STRICT heaviness the
same decomposition gives a POSITIVE DEFINITE gap
(`posDef_of_pairwiseOrthogonalPick`).

The normalization needs the unit direction `u = g/|g|`, which was in the
repository nowhere — `unitAtom`, `directionOf` and `normalizeAtom` are all free
names — so `unitDirection` and its four identities are landed here as well.  The
direction-coordinate workflows can consume them directly.

## T7(b) — the saturated atom, and its collar

The share of an atom is `s_c = t_c ℓ_c`, and `s_c ≤ 1` always
(`Gtz.weighted_leverage_le_one`).  The boundary case `s_a = 1` is EXACTLY
orthogonality of every other atom to `g_a`:

    t_a ℓ_a = 1   ⟺   ∀ c ≠ a, ⟨g_c, g_a⟩ = 0        (given g_a ≠ 0)

Both directions are the row law `Σ_e t_e ⟨g_a, g_e⟩² = ℓ_a`
(`Gtz.sum_weight_mul_sq_atomPairing`) read at the atom itself: the `e = a` term is
`t_a ℓ_a²  = s_a ℓ_a`, so the remaining terms sum to `ℓ_a (1 − s_a)`, a sum of
NONNEGATIVE terms with strictly positive weights.  This is stated at every rank.

At rank three the saturated atom then produces a dominating triple THROUGH IT, by
composition with `Gtz.gtz_rank_two`: the other atoms live in the plane `g_a^⊥`,
`gtz_rank_two` supplies a pair there, and the assembly is block diagonal.  What is
proved here is strictly more, and it is what the collar workflow needs: the exact
orthogonality may be replaced by a QUANTITATIVE bound.  Writing `t` for the pole's
weight and `L` for its leverage, if every other atom obeys

    ⟨g_c, g_a⟩² · ℓ_c  ≤  collarBound          and   4 (1 − t) · collarBound  <  L (L − 1) t

then some triple containing `a` has a POSITIVE DEFINITE gap.  At exact saturation
`collarBound = 0` and the budget reads `0 < L(L−1)t`, true because `L = 1/t > 1`;
so the collar is an honest neighbourhood of the saturated locus, not a
reformulation of it.

The mechanism, in one line: the pole's weight is dead mass on the plane, so
reallocating a fraction `eps ∈ (0, t)` of it sharpens `gtz_rank_two`'s weak planar
floor `1` to `(1 − eps)/(1 − t) > 1` (`exists_planar_pair_explicitFloor`, the
named-floor strengthening of `Gtz.exists_planar_pair_strictFloor`, which exports
only `1 < floor`).  That strict floor is the budget the off-plane components of
the two planar atoms are paid out of, and the exchange rate is exactly the
`4 (1 − t) · collarBound < L (L − 1) t` above.

Three honest limitations of the collar.  (i) The budget is STRICT, because the
split `eps` has to be chosen strictly positive and it eats a strictly positive
slice; the boundary case `4(1 − t) collarBound = L(L − 1)t` is not covered.
(ii) `collarBound` is a UNIFORM bound over every non-pole atom, not over the two
atoms the transport happens to select — the pair is produced BY the transport, so
it cannot be named in advance.  (iii) The constant `4` comes from `(x + y)² ≤
2(x² + y²)` on the two-element pair together with the completed square; it is
sufficient, and nothing here claims it is sharp.

Non-vacuity is controlled at a shipped witness rather than asserted:
`Gtz.nearPencilSixDesign` has a saturated pole (`t = 1/4`, `ℓ = 4`), T7(b) fires
there, and `nearPencilSixDesign_collarBudget_of_lt_one` shows the collar's budget
at that design admits every `collarBound < 1` — a positive radius, so the collar
really is a neighbourhood and not saturation in disguise.

T7(b) and the collar are RANK THREE only, because the transport goes through
`Gtz.gtz_rank_two` and a `2 × 3` orthonormal plane.  The saturation-equals-
orthogonality equivalence above is the part that holds at every rank.

## T7(c) — Mantel on the box-good graph, and why it decides nothing

If no triple of an all-heavy rank-three design dominates then no triangle of the
box-good graph exists (`Gtz.dominates_of_isBoxGoodTriangle`), so Mantel's theorem
caps its edges at `⌊m²/4⌋` — nine at `m = 6`, twelve at `m = 7`, leaving at least
six and at least nine box-BAD pairs respectively.  This is a true theorem and a
DEAD route, and the file records both: `boxGoodGraph_icosaDesign_eq_bot` says the
box-good graph of the maximal real equiangular design is EMPTY, so all fifteen of
its pairs are box-bad against the six the counting asked for — and the design
dominates strictly anyway.  The refutations
`Gtz.not_boxGoodTriangleCovering_six/_seven` and the stronger sign-blind
`Gtz.not_signBlindGoodTripleCovering_seven` are already kernel-checked upstream.
Mantel is landed here as infrastructure for the Ramsey squeeze, NOT as progress
on rank three.

## T7(d) — R(3,3) = 6, both halves

From any two-colouring of the ordered pairs of six points, three of them carry the
same colour on all three of their pairs.  Proved by pigeonhole, not by a
`2¹⁵`-case `decide`: five booleans `colour 0 ·` contain three equal ones (a
thirty-two case `decide`), and then a single boolean trichotomy on the three
induced pairs closes it.  SYMMETRY OF THE COLOURING IS NOT NEEDED — every pair is
read in one fixed orientation throughout — so the theorem applies to arbitrary
`colour : V → V → Bool`, and the symmetric case is the corollary.  Mathlib has no
Ramsey numbers at all (`Combinatorics/Hindman.lean` and `HalesJewett.lean` are
unrelated infinitary results), so this is from scratch.

The matching lower bound is here too: the pentagon `i ~ i ± 1 (mod 5)` and its
complement the pentagram `i ~ i ± 2` are both five-cycles, hence both
triangle-free (`exists_cliqueFree_three_and_compl_cliqueFree_three_five`).  So the
Ramsey number is exactly six, not merely at most six.

The consumable form is `exists_monochromaticTriple_of_pairPredicate`: any pair
predicate on any type, evaluated at six points, has a monochromatic triple.  Fed
the box-good predicate it gives `exists_dominating_triple_or_boxBadTriple` — every
rank-three design on at least six atoms either dominates on some triple or owns a
totally box-bad triple.  The second disjunct is where every known witness sits.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.Compression
import Gtz.Reduction.Reductions
import Gtz.Reduction.RealVolumeFloor
import Gtz.Ties.TotalTieCorankOne
import Gtz.Quantitative.ChartHadamard
import Gtz.Quantitative.GoodTripleGraph
import Gtz.Design.NearPencilTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## T7(a): a pairwise-orthogonal frame dominates, at every rank -/

/-- **`k` orthonormal vectors in `ℝᵏ` resolve the identity.**  The row matrix `U`
of the family has `U Uᵀ = 1` by orthonormality; it is SQUARE, so `Uᵀ U = 1` as
well, and `Uᵀ U` is the sum of the rows' rank-one atoms.  This is the only place
the argument uses that the family is as large as the dimension. -/
theorem sum_atomMatrix_eq_one_of_orthonormalFrame {rank : ℕ}
    (frame : Fin rank → (Fin rank → ℝ))
    (hunit : ∀ index, frame index ⬝ᵥ frame index = 1)
    (horthogonal : ∀ leftIndex rightIndex, leftIndex ≠ rightIndex →
      frame leftIndex ⬝ᵥ frame rightIndex = 0) :
    ∑ index, atomMatrix (frame index) = 1 := by
  set frameRows : Matrix (Fin rank) (Fin rank) ℝ := Matrix.of frame with hframeRows
  have hentry : ∀ leftIndex rightIndex, (frameRows * frameRowsᵀ) leftIndex rightIndex
      = frame leftIndex ⬝ᵥ frame rightIndex := by
    intro leftIndex rightIndex
    simp only [hframeRows, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct]
  have hgram : frameRows * frameRowsᵀ = 1 := by
    ext leftIndex rightIndex
    rw [hentry]
    rcases eq_or_ne leftIndex rightIndex with rfl | hne
    · rw [hunit, Matrix.one_apply_eq]
    · rw [horthogonal leftIndex rightIndex hne, Matrix.one_apply_ne hne]
  have hother : frameRowsᵀ * frameRows = 1 := mul_eq_one_comm.mp hgram
  rw [← hother, transpose_mul_self_eq_sum_rows]
  rfl

/-- The selected labels of an injective pick form a subset of the right size. -/
theorem card_image_of_injective_pick {size rank : ℕ} (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick) :
    (Finset.image pick Finset.univ).card = rank := by
  rw [Finset.card_image_of_injective Finset.univ hinjective, Finset.card_univ,
    Fintype.card_fin]

/-! ### The unit direction of an atom

`u_c = g_c/|g_c|` is not in the repository anywhere — `unitAtom`, `directionOf`
and `normalizeAtom` are all free names — so it is introduced here together with
the two identities every direction-coordinate argument needs: the direction is a
unit vector, and the atom is the direction's rank-one projector scaled by the
leverage. -/

/-- **The unit direction `g/|g|` of a nonzero atom.**  Written with `√ℓ` rather
than a norm so that `atomMatrix_smul` applies directly and no `Real.norm` API is
dragged in. -/
noncomputable def unitDirection {rank : ℕ} (vec : Fin rank → ℝ) : Fin rank → ℝ :=
  (Real.sqrt (leverageOf vec))⁻¹ • vec

/-- The pairing of two unit directions is the pairing of the atoms divided by the
two lengths. -/
theorem unitDirection_dotProduct {rank : ℕ} (leftVec rightVec : Fin rank → ℝ) :
    unitDirection leftVec ⬝ᵥ unitDirection rightVec
      = ((Real.sqrt (leverageOf leftVec))⁻¹ * (Real.sqrt (leverageOf rightVec))⁻¹)
        * (leftVec ⬝ᵥ rightVec) := by
  rw [unitDirection, unitDirection, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The unit direction is a unit vector** when the atom has positive leverage. -/
theorem unitDirection_dotProduct_self {rank : ℕ} {vec : Fin rank → ℝ}
    (hpositive : 0 < leverageOf vec) : unitDirection vec ⬝ᵥ unitDirection vec = 1 := by
  rw [unitDirection_dotProduct, ← leverageOf_eq_dotProduct_self, ← pow_two, inv_pow,
    Real.sq_sqrt hpositive.le, inv_mul_cancel₀ (ne_of_gt hpositive)]

/-- Orthogonal atoms have orthogonal directions. -/
theorem unitDirection_dotProduct_eq_zero {rank : ℕ} {leftVec rightVec : Fin rank → ℝ}
    (hzero : leftVec ⬝ᵥ rightVec = 0) :
    unitDirection leftVec ⬝ᵥ unitDirection rightVec = 0 := by
  rw [unitDirection_dotProduct, hzero, mul_zero]

/-- **The atom is its direction's projector scaled by the leverage**:
`g gᵀ = ℓ · u uᵀ`. -/
theorem leverage_smul_atomMatrix_unitDirection {rank : ℕ} {vec : Fin rank → ℝ}
    (hpositive : 0 < leverageOf vec) :
    leverageOf vec • atomMatrix (unitDirection vec) = atomMatrix vec := by
  rw [unitDirection, atomMatrix_smul, inv_pow, Real.sq_sqrt hpositive.le, smul_smul,
    mul_inv_cancel₀ (ne_of_gt hpositive), one_smul]

/-- **The gap of a pairwise-orthogonal frame, decomposed.**  `rank` pairwise
orthogonal atoms of positive leverage give
`S_C − I = Σ_c (ℓ_c − 1) u_c u_cᵀ`, the identity both the semidefinite and the
definite readings of T7(a) come from. -/
theorem subsetSum_image_sub_one_eq_sum_excess_smul {size rank : ℕ}
    (D : WeightedDesign size rank) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (horthogonal : ∀ leftIndex rightIndex, leftIndex ≠ rightIndex →
      D.atom (pick leftIndex) ⬝ᵥ D.atom (pick rightIndex) = 0)
    (hpositive : ∀ index, 0 < leverageOf (D.atom (pick index))) :
    subsetSum D (Finset.image pick Finset.univ) - 1
      = ∑ index, (leverageOf (D.atom (pick index)) - 1)
          • atomMatrix (unitDirection (D.atom (pick index))) := by
  classical
  have hresolve : ∑ index, atomMatrix (unitDirection (D.atom (pick index))) = 1 :=
    sum_atomMatrix_eq_one_of_orthonormalFrame _
      (fun index => unitDirection_dotProduct_self (hpositive index))
      (fun leftIndex rightIndex hne =>
        unitDirection_dotProduct_eq_zero (horthogonal leftIndex rightIndex hne))
  have hsubsetSum : subsetSum D (Finset.image pick Finset.univ)
      = ∑ index, leverageOf (D.atom (pick index))
          • atomMatrix (unitDirection (D.atom (pick index))) := by
    rw [subsetSum, Finset.sum_image (fun leftIndex _ rightIndex _ hequal =>
      hinjective hequal)]
    exact Finset.sum_congr rfl fun index _ =>
      (leverage_smul_atomMatrix_unitDirection (hpositive index)).symm
  rw [hsubsetSum, ← hresolve, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun index _ => by rw [sub_smul, one_smul]

/-- **T7(a), at every rank**: `rank` pairwise-orthogonal atoms of a rank-`rank`
design, each of leverage AT LEAST ONE, dominate.

Pen argument: normalize to `u_c = g_c/|g_c|` — legitimate because leverage `≥ 1`
forbids the zero vector.  The `u_c` are `rank` orthonormal vectors in `ℝ^rank`,
hence `Σ_c u_c u_cᵀ = I` (`sum_atomMatrix_eq_one_of_orthonormalFrame`), so

    S_C − I  =  Σ_c ℓ_c u_c u_cᵀ − Σ_c u_c u_cᵀ  =  Σ_c (ℓ_c − 1) u_c u_cᵀ  ⪰  0,

each summand being `(√(ℓ_c − 1) u_c)(√(ℓ_c − 1) u_c)ᵀ`.  The heaviness hypothesis
is NON-STRICT: with `ℓ_c = 1` at every atom the subset sum is exactly `I` and the
gap is exactly zero, which is the boundary case a strict hypothesis would lose. -/
theorem dominates_of_pairwiseOrthogonalPick {size rank : ℕ} (D : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (horthogonal : ∀ leftIndex rightIndex, leftIndex ≠ rightIndex →
      D.atom (pick leftIndex) ⬝ᵥ D.atom (pick rightIndex) = 0)
    (hheavy : ∀ index, 1 ≤ leverageOf (D.atom (pick index))) :
    Dominates D (Finset.image pick Finset.univ) := by
  classical
  have hpositive : ∀ index, 0 < leverageOf (D.atom (pick index)) :=
    fun index => lt_of_lt_of_le zero_lt_one (hheavy index)
  rw [Dominates, subsetSum_image_sub_one_eq_sum_excess_smul D pick hinjective horthogonal
    hpositive]
  refine Matrix.posSemidef_sum Finset.univ fun index _ => ?_
  have hshift : (leverageOf (D.atom (pick index)) - 1)
        • atomMatrix (unitDirection (D.atom (pick index)))
      = atomMatrix (Real.sqrt (leverageOf (D.atom (pick index)) - 1)
          • unitDirection (D.atom (pick index))) := by
    rw [atomMatrix_smul, Real.sq_sqrt (by linarith [hheavy index])]
  rw [hshift]
  exact posSemidef_atomMatrix _

/-- **T7(a), the definite reading**: with every leverage STRICTLY above one the
gap of a pairwise-orthogonal frame is positive definite.  Along a probe `w` the
gap is `Σ_c (ℓ_c − 1) ⟨u_c, w⟩²`, and `Σ_c ⟨u_c, w⟩² = |w|² > 0` forces one
overlap to be nonzero. -/
theorem posDef_of_pairwiseOrthogonalPick {size rank : ℕ} (D : WeightedDesign size rank)
    (pick : Fin rank → Fin size) (hinjective : Function.Injective pick)
    (horthogonal : ∀ leftIndex rightIndex, leftIndex ≠ rightIndex →
      D.atom (pick leftIndex) ⬝ᵥ D.atom (pick rightIndex) = 0)
    (hheavy : ∀ index, 1 < leverageOf (D.atom (pick index))) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef := by
  classical
  have hpositive : ∀ index, 0 < leverageOf (D.atom (pick index)) :=
    fun index => lt_trans zero_lt_one (hheavy index)
  have hgap := subsetSum_image_sub_one_eq_sum_excess_smul D pick hinjective horthogonal hpositive
  have hresolve : ∑ index, atomMatrix (unitDirection (D.atom (pick index))) = 1 :=
    sum_atomMatrix_eq_one_of_orthonormalFrame _
      (fun index => unitDirection_dotProduct_self (hpositive index))
      (fun leftIndex rightIndex hne =>
        unitDirection_dotProduct_eq_zero (horthogonal leftIndex rightIndex hne))
  have hsemidefinite : (subsetSum D (Finset.image pick Finset.univ) - 1).PosSemidef :=
    dominates_of_pairwiseOrthogonalPick D pick hinjective horthogonal
      (fun index => (hheavy index).le)
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hsemidefinite.isHermitian, fun probe hprobeNe => ?_⟩
  rw [star_trivial, hgap]
  have hoverlapSum : ∑ index, (unitDirection (D.atom (pick index)) ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ probe := by
    have hstep := congrArg (fun gram => probe ⬝ᵥ (gram *ᵥ probe)) hresolve
    simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.one_mulVec] at hstep
    rw [← hstep]
    exact Finset.sum_congr rfl fun index _ => (dotProduct_atomMatrix_mulVec_self _ _).symm
  have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
  have hexistsOverlap : ∃ index, 0 < (unitDirection (D.atom (pick index)) ⬝ᵥ probe) ^ 2 := by
    by_contra hcontra
    have hcontraAll : ∀ index, (unitDirection (D.atom (pick index)) ⬝ᵥ probe) ^ 2 ≤ 0 :=
      fun index => not_lt.mp fun hpos => hcontra ⟨index, hpos⟩
    have hallZero : ∀ index ∈ (Finset.univ : Finset (Fin rank)),
        (unitDirection (D.atom (pick index)) ⬝ᵥ probe) ^ 2 = 0 :=
      fun index _ => le_antisymm (hcontraAll index) (sq_nonneg _)
    rw [Finset.sum_congr rfl hallZero, Finset.sum_const_zero] at hoverlapSum
    linarith
  obtain ⟨witnessIndex, hwitness⟩ := hexistsOverlap
  have hform : probe ⬝ᵥ ((∑ index, (leverageOf (D.atom (pick index)) - 1)
        • atomMatrix (unitDirection (D.atom (pick index)))) *ᵥ probe)
      = ∑ index, (leverageOf (D.atom (pick index)) - 1)
          * (unitDirection (D.atom (pick index)) ⬝ᵥ probe) ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun index _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        dotProduct_atomMatrix_mulVec_self]
  rw [hform]
  refine Finset.sum_pos' (fun index _ => ?_)
    ⟨witnessIndex, Finset.mem_univ witnessIndex, ?_⟩
  · exact mul_nonneg (by linarith [hheavy index]) (sq_nonneg _)
  · exact mul_pos (by linarith [hheavy witnessIndex]) hwitness

/-- The existential reading of T7(a): a pairwise-orthogonal frame of `rank` atoms
IS a dominating subset of the required size. -/
theorem exists_dominating_of_pairwiseOrthogonalPick {size rank : ℕ}
    (D : WeightedDesign size rank) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (horthogonal : ∀ leftIndex rightIndex, leftIndex ≠ rightIndex →
      D.atom (pick leftIndex) ⬝ᵥ D.atom (pick rightIndex) = 0)
    (hheavy : ∀ index, 1 ≤ leverageOf (D.atom (pick index))) :
    ∃ selected : Finset (Fin size), selected.card = rank ∧ Dominates D selected :=
  ⟨Finset.image pick Finset.univ, card_image_of_injective_pick pick hinjective,
    dominates_of_pairwiseOrthogonalPick D pick hinjective horthogonal hheavy⟩

/-- **T7(a) at rank three, with NON-STRICT heaviness.**  The repository's
`Gtz.dominates_of_orthogonalTriple` asks `1 < ℓ` at all three atoms; the orthogonal
corner does not need it, and the boundary `ℓ = 1` is exactly the orthonormal-basis
triple whose gap is zero.  Corollary of the general-rank theorem, not a reproof. -/
theorem dominates_of_orthogonalTriple_of_one_le {size : ℕ} (D : WeightedDesign size 3)
    {pivot pairFirst pairSecond : Fin size} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 ≤ leverageOf (D.atom pivot))
    (hfirstHeavy : 1 ≤ leverageOf (D.atom pairFirst))
    (hsecondHeavy : 1 ≤ leverageOf (D.atom pairSecond))
    (hpivotFirstZero : atomPairing D pivot pairFirst = 0)
    (hpivotSecondZero : atomPairing D pivot pairSecond = 0)
    (hpairZero : atomPairing D pairFirst pairSecond = 0) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  classical
  have hcases : ∀ index : Fin 3, index = 0 ∨ index = 1 ∨ index = 2 := by decide
  have hzeroFirst : D.atom pivot ⬝ᵥ D.atom pairFirst = 0 := hpivotFirstZero
  have hzeroSecond : D.atom pivot ⬝ᵥ D.atom pairSecond = 0 := hpivotSecondZero
  have hzeroPair : D.atom pairFirst ⬝ᵥ D.atom pairSecond = 0 := hpairZero
  have hzeroFirstFlip : D.atom pairFirst ⬝ᵥ D.atom pivot = 0 := by
    rw [dotProduct_comm]; exact hzeroFirst
  have hzeroSecondFlip : D.atom pairSecond ⬝ᵥ D.atom pivot = 0 := by
    rw [dotProduct_comm]; exact hzeroSecond
  have hzeroPairFlip : D.atom pairSecond ⬝ᵥ D.atom pairFirst = 0 := by
    rw [dotProduct_comm]; exact hzeroPair
  have hinjective :
      Function.Injective (![pivot, pairFirst, pairSecond] : Fin 3 → Fin size) := by
    intro leftIndex rightIndex hequal
    rcases hcases leftIndex with rfl | rfl | rfl <;>
      rcases hcases rightIndex with rfl | rfl | rfl <;> simp_all
  have himage : Finset.image (![pivot, pairFirst, pairSecond] : Fin 3 → Fin size) Finset.univ
      = {pivot, pairFirst, pairSecond} := by
    ext label
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨index, rfl⟩
      rcases hcases index with rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
  rw [← himage]
  refine dominates_of_pairwiseOrthogonalPick D _ hinjective ?_ ?_
  · intro leftIndex rightIndex hne
    rcases hcases leftIndex with rfl | rfl | rfl <;>
      rcases hcases rightIndex with rfl | rfl | rfl <;> simp_all
  · intro index
    rcases hcases index with rfl | rfl | rfl
    · simpa using hpivotHeavy
    · simpa using hfirstHeavy
    · simpa using hsecondHeavy

/-! ## T7(b), part one: saturation IS orthogonality -/

/-- **A saturated atom is orthogonal to every other atom.**  The row law
`Σ_e t_e ⟨g_a, g_e⟩² = ℓ_a` (`Gtz.sum_weight_mul_sq_atomPairing`) has `e = a` term
`t_a ℓ_a² = (t_a ℓ_a) ℓ_a = ℓ_a`, so the remaining terms — all nonnegative, all
with strictly positive weight — sum to zero and each vanishes.  Stated at every
rank; no heaviness and no size hypothesis. -/
theorem dotProduct_eq_zero_of_weightedLeverage_eq_one {size rank : ℕ}
    (D : WeightedDesign size rank) {saturated : Fin size}
    (hshare : D.weight saturated * leverageOf (D.atom saturated) = 1)
    {other : Fin size} (hother : other ≠ saturated) :
    D.atom other ⬝ᵥ D.atom saturated = 0 := by
  classical
  have hrowLaw := sum_weight_mul_sq_atomPairing D saturated
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun otherIndex => D.weight otherIndex
      * (D.atom saturated ⬝ᵥ D.atom otherIndex) ^ 2) (Finset.mem_univ saturated)
  have hdiagonal : D.weight saturated * (D.atom saturated ⬝ᵥ D.atom saturated) ^ 2
      = leverageOf (D.atom saturated) := by
    rw [← leverageOf_eq_dotProduct_self]
    calc D.weight saturated * leverageOf (D.atom saturated) ^ 2
        = (D.weight saturated * leverageOf (D.atom saturated))
          * leverageOf (D.atom saturated) := by ring
      _ = leverageOf (D.atom saturated) := by rw [hshare, one_mul]
  have htailZero : ∑ otherIndex ∈ Finset.univ.erase saturated,
      D.weight otherIndex * (D.atom saturated ⬝ᵥ D.atom otherIndex) ^ 2 = 0 := by
    rw [hrowLaw] at hsplit
    rw [hdiagonal] at hsplit
    linarith
  have hnonneg : ∀ otherIndex ∈ Finset.univ.erase saturated,
      0 ≤ D.weight otherIndex * (D.atom saturated ⬝ᵥ D.atom otherIndex) ^ 2 :=
    fun otherIndex _ => mul_nonneg (D.weight_pos otherIndex).le (sq_nonneg _)
  have hterm : D.weight other * (D.atom saturated ⬝ᵥ D.atom other) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp htailZero other
      (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)
  have hsquare : (D.atom saturated ⬝ᵥ D.atom other) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hterm with hweightZero | hgood
    · exact absurd hweightZero (ne_of_gt (D.weight_pos other))
    · exact hgood
  rw [dotProduct_comm]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsquare

/-- **The converse: total orthogonality forces saturation.**  With every other
atom orthogonal to `g_a` the row law collapses to `t_a ℓ_a² = ℓ_a`, and `ℓ_a > 0`
cancels.  Together with the previous theorem this pins the boundary case of the
landed share ceiling `Gtz.weighted_leverage_le_one`. -/
theorem weightedLeverage_eq_one_of_forall_dotProduct_eq_zero {size rank : ℕ}
    (D : WeightedDesign size rank) {saturated : Fin size}
    (hnonzero : D.atom saturated ≠ 0)
    (horthogonal : ∀ other, other ≠ saturated → D.atom other ⬝ᵥ D.atom saturated = 0) :
    D.weight saturated * leverageOf (D.atom saturated) = 1 := by
  classical
  have hleveragePos : 0 < leverageOf (D.atom saturated) := by
    rw [leverageOf_eq_dotProduct_self]
    exact dotProduct_self_pos hnonzero
  have hrowLaw := sum_weight_mul_sq_atomPairing D saturated
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun otherIndex => D.weight otherIndex
      * (D.atom saturated ⬝ᵥ D.atom otherIndex) ^ 2) (Finset.mem_univ saturated)
  have htailZero : ∑ otherIndex ∈ Finset.univ.erase saturated,
      D.weight otherIndex * (D.atom saturated ⬝ᵥ D.atom otherIndex) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun otherIndex hmember => ?_
    have hne : otherIndex ≠ saturated := (Finset.mem_erase.mp hmember).1
    have hzero : D.atom saturated ⬝ᵥ D.atom otherIndex = 0 := by
      rw [dotProduct_comm]
      exact horthogonal otherIndex hne
    rw [hzero]
    ring
  have hdiagonal : D.weight saturated * leverageOf (D.atom saturated) ^ 2
      = leverageOf (D.atom saturated) := by
    rw [hrowLaw, htailZero, ← leverageOf_eq_dotProduct_self] at hsplit
    linarith
  have hfactor : (D.weight saturated * leverageOf (D.atom saturated) - 1)
      * leverageOf (D.atom saturated) = 0 := by nlinarith [hdiagonal]
  rcases mul_eq_zero.mp hfactor with hgood | hbad
  · linarith
  · exact absurd hbad (ne_of_gt hleveragePos)

/-- **Saturation IS orthogonality**, as an equivalence at every rank.  The share
`s_a = t_a ℓ_a` sits at its ceiling exactly when the atom is orthogonal to the
whole rest of the design — so the saturated stratum is the orthogonal-splitting
stratum, and nothing else. -/
theorem weightedLeverage_eq_one_iff_forall_dotProduct_eq_zero {size rank : ℕ}
    (D : WeightedDesign size rank) {saturated : Fin size}
    (hnonzero : D.atom saturated ≠ 0) :
    D.weight saturated * leverageOf (D.atom saturated) = 1
      ↔ ∀ other, other ≠ saturated → D.atom other ⬝ᵥ D.atom saturated = 0 :=
  ⟨fun hshare _ hother => dotProduct_eq_zero_of_weightedLeverage_eq_one D hshare hother,
    weightedLeverage_eq_one_of_forall_dotProduct_eq_zero D hnonzero⟩

/-- A saturated atom of a design with at least two atoms is strictly heavy:
`ℓ_a = 1/t_a` and `t_a < 1`. -/
theorem one_lt_leverage_of_weightedLeverage_eq_one {size rank : ℕ} (hsize : 2 ≤ size)
    (D : WeightedDesign size rank) {saturated : Fin size}
    (hshare : D.weight saturated * leverageOf (D.atom saturated) = 1) :
    1 < leverageOf (D.atom saturated) := by
  have hweightPos : 0 < D.weight saturated := D.weight_pos saturated
  have hweightLtOne : D.weight saturated < 1 := weight_lt_one D hsize saturated
  nlinarith [hshare]

/-! ## T7(b), part two: the sharpened planar floor with a NAMED constant

`Gtz.exists_planar_pair_strictFloor` exports only `1 < planarFloor`, which cannot
pay for anything quantitative.  The same transport with the split fraction left
free names the floor exactly, and that is what the collar consumes. -/

/-- **The planar pair with an explicit floor.**  Reallocating a fraction
`splitFraction` of the pole's dead planar mass and rescaling the atoms by
`√((1 − t)/(1 − splitFraction))` is again a rank-two design, so `Gtz.gtz_rank_two`
supplies a pair — necessarily avoiding the pole, whose transported atom is zero —
that beats the floor `(1 − splitFraction)/(1 − t)` on every planar probe.  The
floor exceeds one exactly when `splitFraction < t`; the statement itself needs
only `0 < splitFraction < 1`, so the caller chooses how much of the pole's mass to
spend.  The rank-two input is a repository theorem, so this is unconditional. -/
theorem exists_planar_pair_explicitFloor {size : ℕ} (hsize : 2 ≤ size)
    (D : WeightedDesign size 3) (poleLabel : Fin size) (plane : Matrix (Fin 2) (Fin 3) ℝ)
    (hOrthonormal : plane * planeᵀ = 1)
    (hPoleKilled : plane *ᵥ D.atom poleLabel = 0)
    (splitFraction : ℝ) (hsplitPos : 0 < splitFraction) (hsplitLtOne : splitFraction < 1) :
    ∃ pair : Finset (Fin size), pair.card = 2 ∧ poleLabel ∉ pair ∧
      ∀ probe : Fin 2 → ℝ,
        (1 - splitFraction) / (1 - D.weight poleLabel) * (probe ⬝ᵥ probe)
          ≤ ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2 := by
  classical
  have hpoleWeightLtOne : D.weight poleLabel < 1 := weight_lt_one D hsize poleLabel
  have hpoleSharePos : (0 : ℝ) < 1 - D.weight poleLabel := by linarith
  have hretainedPos : (0 : ℝ) < 1 - splitFraction := by linarith
  set scaleSquared : ℝ := (1 - D.weight poleLabel) / (1 - splitFraction) with hscaleSquared
  have hscaleSquaredPos : 0 < scaleSquared := div_pos hpoleSharePos hretainedPos
  have hscaleSq : Real.sqrt scaleSquared ^ 2 = scaleSquared := Real.sq_sqrt hscaleSquaredPos.le
  set planarFloor : ℝ := (1 - splitFraction) / (1 - D.weight poleLabel) with hplanarFloor
  have hfloorNonneg : 0 ≤ planarFloor := (div_pos hretainedPos hpoleSharePos).le
  have hfloorScale : planarFloor * scaleSquared = 1 := by
    rw [hplanarFloor, hscaleSquared, div_mul_div_comm,
      mul_comm (1 - D.weight poleLabel) (1 - splitFraction)]
    exact div_self (mul_ne_zero (ne_of_gt hretainedPos) (ne_of_gt hpoleSharePos))
  set transported := rescaledPlanarDesign D poleLabel plane hOrthonormal hPoleKilled
    splitFraction hsplitPos hsplitLtOne hpoleSharePos with htransported
  obtain ⟨pair, hcard, hdominates⟩ := gtz_rank_two size transported
  have hpoleAtomZero : transported.atom poleLabel = 0 := by
    rw [htransported, rescaledPlanarDesign_atom, hPoleKilled, smul_zero]
  have hpoleOut : poleLabel ∉ pair := fun hmember =>
    not_dominates_of_zero_atom_planar transported pair hcard poleLabel hmember hpoleAtomZero
      hdominates
  refine ⟨pair, hcard, hpoleOut, fun probe => ?_⟩
  have hform : 0 ≤ probe ⬝ᵥ ((subsetSum transported pair - 1) *ᵥ probe) := by
    have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    rwa [star_trivial] at hnonneg
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    dotProduct_subsetSum_mulVec_of_finset] at hform
  have hscaled : ∑ label ∈ pair, (transported.atom label ⬝ᵥ probe) ^ 2
      = scaleSquared * ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [htransported, rescaledPlanarDesign_atom, smul_dotProduct, smul_eq_mul, mul_pow, hscaleSq]
  rw [hscaled] at hform
  have hbound : probe ⬝ᵥ probe
      ≤ scaleSquared * ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2 := by linarith
  calc planarFloor * (probe ⬝ᵥ probe)
      ≤ planarFloor * (scaleSquared * ∑ label ∈ pair,
          ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2) := mul_le_mul_of_nonneg_left hbound hfloorNonneg
    _ = ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2 := by
        rw [← mul_assoc, hfloorScale, one_mul]

/-! ## T7(b), part three: the collar

Every other atom's component ALONG the pole is paid for out of the sharpened
planar floor.  The exchange rate is exact and it is the whole content of the
theorem. -/

/-- **The collar exchange, as pure real algebra.**  This is the whole analytic
content of the collar, isolated from the design: the gap of the assembled triple
along a probe, written in the pole/plane coordinates, is positive as soon as the
two planar atoms' components ALONG the pole are small enough relative to the
sharpened planar floor.

The variables are the probe's pole coordinate `axisValue`, its squared planar
shadow `shadowNormSq`, the two atoms' planar overlaps with the shadow, their
pairings with the pole, the reciprocal leverage `poleLevInv = 1/L`, the planar
floor and the collar bound.  Multiplying the lower bound

    (1 − p) axis² + (F − 1) |shadow|² + 2 p axis (q₁ Y₁ + q₂ Y₂)

by `1 − p` completes a square, leaving `((1 − p)(F − 1) − 4 p² collarBound)
|shadow|²`, and `hexchange` is exactly the positivity of that coefficient.  The
degenerate shadow is handled separately: there the gap is `(1 − p) axis²` plus two
squares, and `hprobeNonzero` forces `axis ≠ 0`. -/
theorem pos_of_collarExchange {axisValue shadowNormSq shadowFirst shadowSecond
    crossFirst crossSecond poleLevInv planarFloor collarBound : ℝ}
    (hpoleLevInvPos : 0 < poleLevInv) (hpoleLevInvLtOne : poleLevInv < 1)
    (hshadowNonneg : 0 ≤ shadowNormSq)
    (hfloor : planarFloor * shadowNormSq ≤ shadowFirst ^ 2 + shadowSecond ^ 2)
    (hcrossFirst : crossFirst ^ 2 * shadowFirst ^ 2 ≤ collarBound * shadowNormSq)
    (hcrossSecond : crossSecond ^ 2 * shadowSecond ^ 2 ≤ collarBound * shadowNormSq)
    (hexchange : 4 * poleLevInv ^ 2 * collarBound < (1 - poleLevInv) * (planarFloor - 1))
    (hprobeNonzero : 0 < shadowNormSq + poleLevInv * axisValue ^ 2) :
    0 < axisValue ^ 2 + (shadowFirst + poleLevInv * (crossFirst * axisValue)) ^ 2
      + (shadowSecond + poleLevInv * (crossSecond * axisValue)) ^ 2
      - (shadowNormSq + poleLevInv * axisValue ^ 2) := by
  have hcrossTotalBound :
      (crossFirst * shadowFirst + crossSecond * shadowSecond) ^ 2
        ≤ 4 * collarBound * shadowNormSq := by
    nlinarith [sq_nonneg (crossFirst * shadowFirst - crossSecond * shadowSecond),
      hcrossFirst, hcrossSecond]
  rcases eq_or_lt_of_le hshadowNonneg with hshadowZero | hshadowPos
  · have haxisSqPos : 0 < axisValue ^ 2 := by
      rw [← hshadowZero] at hprobeNonzero
      nlinarith [hprobeNonzero, hpoleLevInvPos]
    rw [← hshadowZero]
    nlinarith [sq_nonneg (shadowFirst + poleLevInv * (crossFirst * axisValue)),
      sq_nonneg (shadowSecond + poleLevInv * (crossSecond * axisValue)),
      haxisSqPos, hpoleLevInvLtOne]
  · have hmainPos : 0 < (1 - poleLevInv) * axisValue ^ 2
        + (planarFloor - 1) * shadowNormSq
        + 2 * poleLevInv * (axisValue * (crossFirst * shadowFirst
          + crossSecond * shadowSecond)) := by
      have hexcessPos : 0 < 1 - poleLevInv := by linarith
      have hproduct : 4 * poleLevInv ^ 2 * collarBound * shadowNormSq
          < (1 - poleLevInv) * (planarFloor - 1) * shadowNormSq :=
        mul_lt_mul_of_pos_right hexchange hshadowPos
      have hsquared : poleLevInv ^ 2
            * (crossFirst * shadowFirst + crossSecond * shadowSecond) ^ 2
          ≤ poleLevInv ^ 2 * (4 * collarBound * shadowNormSq) :=
        mul_le_mul_of_nonneg_left hcrossTotalBound (sq_nonneg _)
      have hscaled : 0 < (1 - poleLevInv)
          * ((1 - poleLevInv) * axisValue ^ 2 + (planarFloor - 1) * shadowNormSq
            + 2 * poleLevInv * (axisValue * (crossFirst * shadowFirst
              + crossSecond * shadowSecond))) := by
        have hidentity : (1 - poleLevInv)
            * ((1 - poleLevInv) * axisValue ^ 2 + (planarFloor - 1) * shadowNormSq
              + 2 * poleLevInv * (axisValue * (crossFirst * shadowFirst
                + crossSecond * shadowSecond)))
            = ((1 - poleLevInv) * axisValue
                + poleLevInv * (crossFirst * shadowFirst + crossSecond * shadowSecond)) ^ 2
              - poleLevInv ^ 2
                * (crossFirst * shadowFirst + crossSecond * shadowSecond) ^ 2
              + (1 - poleLevInv) * (planarFloor - 1) * shadowNormSq := by ring
        rw [hidentity]
        nlinarith [sq_nonneg ((1 - poleLevInv) * axisValue
          + poleLevInv * (crossFirst * shadowFirst + crossSecond * shadowSecond)),
          hsquared, hproduct]
      nlinarith [hscaled, hexcessPos]
    nlinarith [hmainPos, hfloor, sq_nonneg (poleLevInv * axisValue * crossFirst),
      sq_nonneg (poleLevInv * axisValue * crossSecond)]

/-- **The collar around the saturated stratum.**  Let `a` be a strictly heavy atom
of a rank-three design of size at least two, `t` its weight, `L` its leverage.  If
every other atom obeys `⟨g_c, g_a⟩² ℓ_c ≤ collarBound` and the budget

    4 (1 − t) · collarBound  <  L (L − 1) t

holds, then some triple CONTAINING `a` has a positive definite gap.  In particular
the design dominates on that triple.

Pen argument.  Build the plane `P = g_a^⊥` and take the sharpened planar pair
`{x, y}` at split `eps`, with floor `F = (1 − eps)/(1 − t)`.  Decompose a probe
through the completeness identity `PᵀP + L⁻¹ g_a g_aᵀ = I₃`: writing
`axis = ⟨g_a, w⟩`, `shadow = P w`, `Y_c = ⟨P g_c, shadow⟩`, `q_c = ⟨g_c, g_a⟩`,

    ⟨w,(S − I)w⟩ = (1 − L⁻¹) axis² + (Σ Y_c² − |shadow|²) + 2 L⁻¹ axis Σ q_c Y_c
                     + L⁻² axis² Σ q_c²
                 ≥ E axis² + G |shadow|² + 2 L⁻¹ axis · crossTotal,

with `E = (L−1)/L`, `G = F − 1`.  Cauchy–Schwarz gives `Y_c² ≤ |P g_c|² |shadow|²`
and completeness gives `|P g_c|² = ℓ_c − L⁻¹ q_c²`, so
`q_c² Y_c² ≤ q_c² ℓ_c |shadow|² ≤ collarBound |shadow|²` and hence
`crossTotal² ≤ 4 collarBound |shadow|²` over the two-element pair.  Multiplying the
bound by `E` completes a square:

    E · bound = (E axis + L⁻¹ crossTotal)² − L⁻² crossTotal² + E G |shadow|²
              ≥ (E G − 4 L⁻² collarBound) |shadow|²,

and `E G − 4 L⁻² collarBound = (L(L−1)G − 4 collarBound)/L² > 0` is precisely the
budget after clearing `(1 − t)`.  The split `eps` is chosen small enough that the
strict budget survives, which is why the hypothesis is strict.  When
`|shadow| = 0` the shadow vanishes outright, the cross term with it, and the bound
is `E axis² > 0` for a nonzero probe. -/
theorem exists_posDef_triple_of_collar {size : ℕ} (hsize : 2 ≤ size)
    (D : WeightedDesign size 3) (poleLabel : Fin size)
    (hpoleHeavy : 1 < leverageOf (D.atom poleLabel)) (collarBound : ℝ)
    (hcollar : ∀ label, label ≠ poleLabel →
      (D.atom label ⬝ᵥ D.atom poleLabel) ^ 2 * leverageOf (D.atom label) ≤ collarBound)
    (hbudget : 4 * (1 - D.weight poleLabel) * collarBound
      < leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)
          * D.weight poleLabel) :
    ∃ triple : Finset (Fin size), triple.card = 3 ∧ poleLabel ∈ triple
      ∧ (subsetSum D triple - 1).PosDef := by
  classical
  have hpoleNonzero : D.atom poleLabel ≠ 0 := by
    intro hzero
    rw [leverageOf_eq_dotProduct_self, hzero, zero_dotProduct] at hpoleHeavy
    linarith
  have hweightPos : 0 < D.weight poleLabel := D.weight_pos poleLabel
  have hweightLtOne : D.weight poleLabel < 1 := weight_lt_one D hsize poleLabel
  have hshareRoom : (0 : ℝ) < 1 - D.weight poleLabel := by linarith
  have hleveragePos : 0 < leverageOf (D.atom poleLabel) := by linarith
  have hleverageNe : leverageOf (D.atom poleLabel) ≠ 0 := ne_of_gt hleveragePos
  have hexcessPos : (0 : ℝ) < leverageOf (D.atom poleLabel) - 1 := by linarith
  have hexcessNe : leverageOf (D.atom poleLabel) - 1 ≠ 0 := ne_of_gt hexcessPos
  have hproductPos : 0 < leverageOf (D.atom poleLabel)
      * (leverageOf (D.atom poleLabel) - 1) := mul_pos hleveragePos hexcessPos
  -- choose the split so the strict budget survives the transport
  set slack : ℝ := leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)
      * D.weight poleLabel - 4 * (1 - D.weight poleLabel) * collarBound with hslack
  have hslackPos : 0 < slack := by rw [hslack]; linarith
  set splitFraction : ℝ := min (D.weight poleLabel / 2)
      (slack / (2 * (leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1))))
    with hsplitFraction
  have hsplitPos : 0 < splitFraction := by
    rw [hsplitFraction]
    exact lt_min (by linarith) (div_pos hslackPos (by linarith))
  have hsplitLtWeight : splitFraction < D.weight poleLabel :=
    lt_of_le_of_lt (hsplitFraction ▸ min_le_left _ _) (by linarith)
  have hsplitLtOne : splitFraction < 1 := by linarith
  have hsplitSmall : (leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1))
      * splitFraction ≤ slack / 2 := by
    have hle : splitFraction
        ≤ slack / (2 * (leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1))) :=
      hsplitFraction ▸ min_le_right _ _
    calc (leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)) * splitFraction
        ≤ (leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1))
          * (slack / (2 * (leverageOf (D.atom poleLabel)
            * (leverageOf (D.atom poleLabel) - 1)))) := mul_le_mul_of_nonneg_left hle hproductPos.le
      _ = slack / 2 := by field_simp
  have hgapBudget : 4 * (1 - D.weight poleLabel) * collarBound
      < leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)
          * (D.weight poleLabel - splitFraction) := by
    have hexpand : leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)
        * (D.weight poleLabel - splitFraction)
        = leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)
            * D.weight poleLabel
          - (leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1))
            * splitFraction := by ring
    rw [hexpand]
    linarith [hsplitSmall, hslack, hslackPos]
  -- the plane, the sharpened pair, and the exchange rate
  obtain ⟨plane, hOrthonormal, hPoleKilled, hcomplete⟩ :=
    exists_orthonormalPlane_of_ne_zero (D.atom poleLabel) hpoleNonzero
  obtain ⟨pair, hpairCard, hpoleOut, hfloorBound⟩ :=
    exists_planar_pair_explicitFloor hsize D poleLabel plane hOrthonormal hPoleKilled
      splitFraction hsplitPos hsplitLtOne
  have hfloorGap : (1 - splitFraction) / (1 - D.weight poleLabel) - 1
      = (D.weight poleLabel - splitFraction) / (1 - D.weight poleLabel) := by
    field_simp
    ring
  have hcondition : 4 * collarBound
      < leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)
          * ((1 - splitFraction) / (1 - D.weight poleLabel) - 1) := by
    have hrewrite : leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)
        * ((1 - splitFraction) / (1 - D.weight poleLabel) - 1)
        = leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)
            * (D.weight poleLabel - splitFraction) / (1 - D.weight poleLabel) := by
      rw [hfloorGap]; ring
    rw [hrewrite, lt_div_iff₀ hshareRoom]
    nlinarith [hgapBudget]
  have hexchange : 4 * ((leverageOf (D.atom poleLabel))⁻¹) ^ 2 * collarBound
      < (1 - (leverageOf (D.atom poleLabel))⁻¹)
        * ((1 - splitFraction) / (1 - D.weight poleLabel) - 1) := by
    have hdifference : (1 - (leverageOf (D.atom poleLabel))⁻¹)
          * ((1 - splitFraction) / (1 - D.weight poleLabel) - 1)
          - 4 * ((leverageOf (D.atom poleLabel))⁻¹) ^ 2 * collarBound
        = (leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)
            * ((1 - splitFraction) / (1 - D.weight poleLabel) - 1) - 4 * collarBound)
          / leverageOf (D.atom poleLabel) ^ 2 := by
      field_simp
    have hpositive : 0 < (1 - (leverageOf (D.atom poleLabel))⁻¹)
        * ((1 - splitFraction) / (1 - D.weight poleLabel) - 1)
        - 4 * ((leverageOf (D.atom poleLabel))⁻¹) ^ 2 * collarBound := by
      rw [hdifference]
      exact div_pos (by linarith) (by positivity)
    linarith
  -- name the two planar atoms
  obtain ⟨firstLabel, secondLabel, hlabelNe, hpairEq⟩ := Finset.card_eq_two.mp hpairCard
  have hfirstNe : firstLabel ≠ poleLabel := by
    intro hequal
    exact hpoleOut (by rw [hpairEq, ← hequal]; exact Finset.mem_insert_self _ _)
  have hsecondNe : secondLabel ≠ poleLabel := by
    intro hequal
    exact hpoleOut (by rw [hpairEq, ← hequal]; simp)
  refine ⟨insert poleLabel pair, ?_, Finset.mem_insert_self _ _, ?_⟩
  · rw [Finset.card_insert_of_notMem hpoleOut, hpairCard]
  -- the completeness identity, as a bilinear decomposition
  have hpoleNormSq : D.atom poleLabel ⬝ᵥ D.atom poleLabel = leverageOf (D.atom poleLabel) :=
    (leverageOf_eq_dotProduct_self (D.atom poleLabel)).symm
  have hbilinear : ∀ leftVec rightVec : Fin 3 → ℝ, leftVec ⬝ᵥ rightVec
      = (plane *ᵥ leftVec) ⬝ᵥ (plane *ᵥ rightVec)
        + (leverageOf (D.atom poleLabel))⁻¹
          * ((leftVec ⬝ᵥ D.atom poleLabel) * (D.atom poleLabel ⬝ᵥ rightVec)) := by
    intro leftVec rightVec
    have happlied := congrArg (fun gram => leftVec ⬝ᵥ (gram *ᵥ rightVec)) hcomplete
    simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, Matrix.one_mulVec, hpoleNormSq] at happlied
    rw [atomMatrix_mulVec_eq_smul, dotProduct_smul, smul_eq_mul] at happlied
    have hplaneBlock : leftVec ⬝ᵥ ((planeᵀ * plane) *ᵥ rightVec)
        = (plane *ᵥ leftVec) ⬝ᵥ (plane *ᵥ rightVec) := by
      rw [← Matrix.mulVec_mulVec, dotProduct_comm,
        dotProduct_mulVec_transpose plane (plane *ᵥ rightVec) leftVec, dotProduct_comm]
    rw [hplaneBlock] at happlied
    rw [← happlied]
    ring
  have hplanarLeverage : ∀ label : Fin size,
      (plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ D.atom label) ≤ leverageOf (D.atom label) := by
    intro label
    have hstep := hbilinear (D.atom label) (D.atom label)
    rw [dotProduct_comm (D.atom poleLabel) (D.atom label),
      ← leverageOf_eq_dotProduct_self] at hstep
    have hnonneg : 0 ≤ (leverageOf (D.atom poleLabel))⁻¹
        * ((D.atom label ⬝ᵥ D.atom poleLabel) * (D.atom label ⬝ᵥ D.atom poleLabel)) :=
      mul_nonneg (inv_pos.mpr hleveragePos).le (mul_self_nonneg _)
    linarith [hstep]
  have hhermitian : (subsetSum D (insert poleLabel pair) - 1).IsHermitian :=
    Matrix.IsHermitian.sub
      (Matrix.posSemidef_sum (insert poleLabel pair)
        (fun label _ => posSemidef_atomMatrix (D.atom label))).isHermitian
      Matrix.isHermitian_one
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hhermitian, fun probe hprobeNe => ?_⟩
  rw [star_trivial]
  have hform : probe ⬝ᵥ ((subsetSum D (insert poleLabel pair) - 1) *ᵥ probe)
      = (D.atom poleLabel ⬝ᵥ probe) ^ 2 + (D.atom firstLabel ⬝ᵥ probe) ^ 2
        + (D.atom secondLabel ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      dotProduct_subsetSum_mulVec_of_finset, Finset.sum_insert hpoleOut, hpairEq,
      Finset.sum_pair hlabelNe]
    ring
  have hprobeSplit : probe ⬝ᵥ probe
      = (plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe)
        + (leverageOf (D.atom poleLabel))⁻¹ * (D.atom poleLabel ⬝ᵥ probe) ^ 2 := by
    have hstep := hbilinear probe probe
    rw [dotProduct_comm probe (D.atom poleLabel)] at hstep
    rw [hstep]
    ring
  have hfirstForm : D.atom firstLabel ⬝ᵥ probe
      = (plane *ᵥ D.atom firstLabel) ⬝ᵥ (plane *ᵥ probe)
        + (leverageOf (D.atom poleLabel))⁻¹
          * ((D.atom firstLabel ⬝ᵥ D.atom poleLabel) * (D.atom poleLabel ⬝ᵥ probe)) :=
    hbilinear _ _
  have hsecondForm : D.atom secondLabel ⬝ᵥ probe
      = (plane *ᵥ D.atom secondLabel) ⬝ᵥ (plane *ᵥ probe)
        + (leverageOf (D.atom poleLabel))⁻¹
          * ((D.atom secondLabel ⬝ᵥ D.atom poleLabel) * (D.atom poleLabel ⬝ᵥ probe)) :=
    hbilinear _ _
  have hshadowNonneg : 0 ≤ (plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe) := dotProduct_self_nonneg _
  have hcrossBound : ∀ label : Fin size, label ≠ poleLabel →
      (D.atom label ⬝ᵥ D.atom poleLabel) ^ 2
          * ((plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ probe)) ^ 2
        ≤ collarBound * ((plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe)) := by
    intro label hlabel
    have hcauchy : ((plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ probe)) ^ 2
        ≤ ((plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ D.atom label))
          * ((plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe)) := dotProduct_sq_le_mul _ _
    have hstep : (D.atom label ⬝ᵥ D.atom poleLabel) ^ 2
        * ((plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ probe)) ^ 2
        ≤ (D.atom label ⬝ᵥ D.atom poleLabel) ^ 2
          * (((plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ D.atom label))
            * ((plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe))) :=
      mul_le_mul_of_nonneg_left hcauchy (sq_nonneg _)
    have hplanar : (D.atom label ⬝ᵥ D.atom poleLabel) ^ 2
          * (((plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ D.atom label))
            * ((plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe)))
        ≤ (D.atom label ⬝ᵥ D.atom poleLabel) ^ 2
          * (leverageOf (D.atom label) * ((plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hplanarLeverage label) hshadowNonneg) (sq_nonneg _)
    have hfinal : (D.atom label ⬝ᵥ D.atom poleLabel) ^ 2 * leverageOf (D.atom label)
          * ((plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe))
        ≤ collarBound * ((plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe)) :=
      mul_le_mul_of_nonneg_right (hcollar label hlabel) hshadowNonneg
    nlinarith [hstep, hplanar, hfinal]
  have hfloorAtProbe : (1 - splitFraction) / (1 - D.weight poleLabel)
        * ((plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe))
      ≤ ((plane *ᵥ D.atom firstLabel) ⬝ᵥ (plane *ᵥ probe)) ^ 2
        + ((plane *ᵥ D.atom secondLabel) ⬝ᵥ (plane *ᵥ probe)) ^ 2 := by
    have hstep := hfloorBound (plane *ᵥ probe)
    rw [hpairEq, Finset.sum_pair hlabelNe] at hstep
    exact hstep
  have hprobeNonzero : 0 < (plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe)
      + (leverageOf (D.atom poleLabel))⁻¹ * (D.atom poleLabel ⬝ᵥ probe) ^ 2 := by
    rw [← hprobeSplit]
    exact dotProduct_self_pos hprobeNe
  rw [hform, hfirstForm, hsecondForm, hprobeSplit]
  exact pos_of_collarExchange (inv_pos.mpr hleveragePos)
    (inv_lt_one_of_one_lt₀ hpoleHeavy) hshadowNonneg hfloorAtProbe
    (hcrossBound firstLabel hfirstNe) (hcrossBound secondLabel hsecondNe) hexchange hprobeNonzero

/-- The collar, in the form the ladder consumes: a dominating triple through the
near-saturated atom. -/
theorem exists_dominating_triple_of_collar {size : ℕ} (hsize : 2 ≤ size)
    (D : WeightedDesign size 3) (poleLabel : Fin size)
    (hpoleHeavy : 1 < leverageOf (D.atom poleLabel)) (collarBound : ℝ)
    (hcollar : ∀ label, label ≠ poleLabel →
      (D.atom label ⬝ᵥ D.atom poleLabel) ^ 2 * leverageOf (D.atom label) ≤ collarBound)
    (hbudget : 4 * (1 - D.weight poleLabel) * collarBound
      < leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)
          * D.weight poleLabel) :
    ∃ triple : Finset (Fin size), triple.card = 3 ∧ poleLabel ∈ triple ∧ Dominates D triple := by
  obtain ⟨triple, hcard, hmember, hposDef⟩ :=
    exists_posDef_triple_of_collar hsize D poleLabel hpoleHeavy collarBound hcollar hbudget
  exact ⟨triple, hcard, hmember, hposDef.posSemidef⟩

/-- **The collar in radius form**, the shape a perturbation argument supplies: if
every other atom's pairing with the pole is at most `pairingRadius` in absolute
value and every other leverage is at most `leverageCap`, then `pairingRadius² ·
leverageCap` is a legitimate collar bound.  At exact saturation `pairingRadius = 0`
and the budget reads `0 < L(L − 1) t`, so the radius statement inherits the whole
saturated locus and a genuine neighbourhood of it. -/
theorem exists_dominating_triple_of_collarRadius {size : ℕ} (hsize : 2 ≤ size)
    (D : WeightedDesign size 3) (poleLabel : Fin size)
    (hpoleHeavy : 1 < leverageOf (D.atom poleLabel)) (pairingRadius leverageCap : ℝ)
    (hradius : ∀ label, label ≠ poleLabel →
      |D.atom label ⬝ᵥ D.atom poleLabel| ≤ pairingRadius)
    (hcap : ∀ label, label ≠ poleLabel → leverageOf (D.atom label) ≤ leverageCap)
    (hbudget : 4 * (1 - D.weight poleLabel) * (pairingRadius ^ 2 * leverageCap)
      < leverageOf (D.atom poleLabel) * (leverageOf (D.atom poleLabel) - 1)
          * D.weight poleLabel) :
    ∃ triple : Finset (Fin size), triple.card = 3 ∧ poleLabel ∈ triple ∧ Dominates D triple := by
  refine exists_dominating_triple_of_collar hsize D poleLabel hpoleHeavy
    (pairingRadius ^ 2 * leverageCap) ?_ hbudget
  intro label hlabel
  have hpairing := hradius label hlabel
  have hleverage := hcap label hlabel
  have hleverageNonneg : 0 ≤ leverageOf (D.atom label) := by
    rw [leverageOf_eq_dotProduct_self]
    exact dotProduct_self_nonneg _
  have hbounds := abs_le.mp hpairing
  have hsquare : (D.atom label ⬝ᵥ D.atom poleLabel) ^ 2 ≤ pairingRadius ^ 2 :=
    sq_le_sq' hbounds.1 hbounds.2
  nlinarith [hsquare, hleverage, hleverageNonneg, sq_nonneg (D.atom label ⬝ᵥ D.atom poleLabel),
    sq_nonneg pairingRadius]

/-- **T7(b): a saturated atom sits inside a strictly dominating triple.**  The
collar at `collarBound = 0`: saturation gives exact orthogonality
(`dotProduct_eq_zero_of_weightedLeverage_eq_one`), so the collar hypothesis is an
equality, and the budget `0 < L(L−1)t` holds because `L = 1/t > 1`.

This is `Gtz.exists_posDef_triple_of_solePole` with two changes: the hypothesis is
the SHARE reaching its ceiling rather than a shared normal, and the conclusion
records that the saturated atom is IN the triple. -/
theorem exists_posDef_triple_of_weightedLeverage_eq_one {size : ℕ} (hsize : 2 ≤ size)
    (D : WeightedDesign size 3) (saturated : Fin size)
    (hshare : D.weight saturated * leverageOf (D.atom saturated) = 1) :
    ∃ triple : Finset (Fin size), triple.card = 3 ∧ saturated ∈ triple
      ∧ (subsetSum D triple - 1).PosDef := by
  have hheavy : 1 < leverageOf (D.atom saturated) :=
    one_lt_leverage_of_weightedLeverage_eq_one hsize D hshare
  have hweightPos : 0 < D.weight saturated := D.weight_pos saturated
  refine exists_posDef_triple_of_collar hsize D saturated hheavy 0 ?_ ?_
  · intro label hlabel
    rw [dotProduct_eq_zero_of_weightedLeverage_eq_one D hshare hlabel]
    simp
  · have hexcessPos : 0 < leverageOf (D.atom saturated) * (leverageOf (D.atom saturated) - 1) := by
      nlinarith
    have hproductPos : 0 < leverageOf (D.atom saturated) * (leverageOf (D.atom saturated) - 1)
        * D.weight saturated := mul_pos hexcessPos hweightPos
    linarith

/-- The domination reading of T7(b). -/
theorem exists_dominating_triple_of_weightedLeverage_eq_one {size : ℕ} (hsize : 2 ≤ size)
    (D : WeightedDesign size 3) (saturated : Fin size)
    (hshare : D.weight saturated * leverageOf (D.atom saturated) = 1) :
    ∃ triple : Finset (Fin size), triple.card = 3 ∧ saturated ∈ triple ∧ Dominates D triple := by
  obtain ⟨triple, hcard, hmember, hposDef⟩ :=
    exists_posDef_triple_of_weightedLeverage_eq_one hsize D saturated hshare
  exact ⟨triple, hcard, hmember, hposDef.posSemidef⟩

/-! ## T7(c): Mantel on the box-good graph -/

/-- The **box-good graph** of a rank-three design: distinct atoms joined when
`4 p² ≤ u u`, i.e. `|rho| ≤ 1/2`.  Its triangles dominate
(`Gtz.dominates_of_isBoxGoodTriangle`), so a design with no dominating triple has a
triangle-free box-good graph. -/
def boxGoodGraph {size : ℕ} (D : WeightedDesign size 3) : SimpleGraph (Fin size) :=
  SimpleGraph.fromRel (IsBoxGoodPair D)

@[simp] theorem boxGoodGraph_adj {size : ℕ} (D : WeightedDesign size 3)
    (atomFirst atomSecond : Fin size) :
    (boxGoodGraph D).Adj atomFirst atomSecond
      ↔ atomFirst ≠ atomSecond ∧ IsBoxGoodPair D atomFirst atomSecond := by
  rw [boxGoodGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hgood | hgood⟩
    · exact ⟨hne, hgood⟩
    · exact ⟨hne, (isBoxGoodPair_comm D atomSecond atomFirst).mp hgood⟩
  · rintro ⟨hne, hgood⟩
    exact ⟨hne, Or.inl hgood⟩

/-- **A design with no dominating triple has a triangle-free box-good graph.**
Contrapositive of `Gtz.dominates_of_isBoxGoodTriangle`. -/
theorem cliqueFree_boxGoodGraph_of_forall_not_dominates {size : ℕ} {D : WeightedDesign size 3}
    (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin size), triple.card = 3 → ¬ Dominates D triple) :
    (boxGoodGraph D).CliqueFree 3 := by
  intro triple hclique
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, htripleEq⟩ :=
    Finset.card_eq_three.mp hclique.2
  have hcliqueTriple : (boxGoodGraph D).IsNClique 3 {first, second, third} := htripleEq ▸ hclique
  obtain ⟨hadjFirstSecond, hadjFirstThird, hadjSecondThird⟩ :=
    SimpleGraph.is3Clique_triple_iff.mp hcliqueTriple
  refine hnone {first, second, third} hcliqueTriple.2 ?_
  exact dominates_of_isBoxGoodTriangle hheavy hfirstSecond hfirstThird hsecondThird
    ⟨((boxGoodGraph_adj D first second).mp hadjFirstSecond).2,
      ((boxGoodGraph_adj D first third).mp hadjFirstThird).2,
      ((boxGoodGraph_adj D second third).mp hadjSecondThird).2⟩

/-- **Mantel's bound on the box-good graph.**  If no triple of an all-heavy
rank-three design dominates then its box-good graph has at most `⌊m²/4⌋` edges: at
most nine at `m = 6`, at most twelve at `m = 7`, so at least six and at least nine
of the pairs are box-BAD.

READ THE NEXT THEOREM BEFORE USING THIS.  The counting is true and it decides
nothing: at `Gtz.icosaDesign` the box-good graph is EMPTY, so the conclusion
"at least six box-bad pairs" is satisfied with fifteen to spare while the design
dominates strictly.  The certificate family this would have bounded is refuted
upstream (`Gtz.not_boxGoodTriangleCovering_six`, and the stronger sign-blind
`Gtz.not_signBlindGoodTripleCovering_seven`).  Mantel is landed here as
infrastructure for the Ramsey squeeze, not as progress. -/
theorem card_edgeFinset_boxGoodGraph_le {size : ℕ} (D : WeightedDesign size 3)
    [DecidableRel (boxGoodGraph D).Adj] (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin size), triple.card = 3 → ¬ Dominates D triple) :
    (boxGoodGraph D).edgeFinset.card ≤ size ^ 2 / 4 := by
  have hfree : (boxGoodGraph D).CliqueFree 3 :=
    cliqueFree_boxGoodGraph_of_forall_not_dominates hheavy hnone
  have hbound := hfree.card_edgeFinset_le (r := 2)
  simp only [Fintype.card_fin] at hbound
  have hchoose : (size % 2).choose 2 = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  have hmonotone : (size ^ 2 - (size % 2) ^ 2) * (2 - 1) / (2 * 2) ≤ size ^ 2 / 4 := by
    have hsub : (size ^ 2 - (size % 2) ^ 2) * (2 - 1) ≤ size ^ 2 := by
      norm_num
    calc (size ^ 2 - (size % 2) ^ 2) * (2 - 1) / (2 * 2)
        ≤ size ^ 2 / (2 * 2) := Nat.div_le_div_right hsub
      _ = size ^ 2 / 4 := by norm_num
  omega

/-- Mantel at the two sizes the squeeze uses: nine edges at six atoms. -/
theorem card_edgeFinset_boxGoodGraph_le_six (D : WeightedDesign 6 3)
    [DecidableRel (boxGoodGraph D).Adj] (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin 6), triple.card = 3 → ¬ Dominates D triple) :
    (boxGoodGraph D).edgeFinset.card ≤ 9 := by
  have hbound := card_edgeFinset_boxGoodGraph_le D hheavy hnone
  norm_num at hbound
  exact hbound

/-- Mantel at the frontier size: twelve edges at seven atoms, so at least nine of
the twenty-one pairs are box-bad. -/
theorem card_edgeFinset_boxGoodGraph_le_seven (D : WeightedDesign 7 3)
    [DecidableRel (boxGoodGraph D).Adj] (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin 7), triple.card = 3 → ¬ Dominates D triple) :
    (boxGoodGraph D).edgeFinset.card ≤ 12 := by
  have hbound := card_edgeFinset_boxGoodGraph_le D hheavy hnone
  norm_num at hbound
  exact hbound

/-- **The complementary count**: the box-BAD pairs number at least
`C(m,2) − ⌊m²/4⌋`, so at least six at `m = 6` and at least nine at `m = 7`.  This
is the form the pen argument states the pressure in, and it is the form the
refutation contradicts: at `Gtz.icosaSevenDesign` ALL twenty-one pairs are box-bad
and the design dominates. -/
theorem card_edgeFinset_compl_boxGoodGraph_ge {size : ℕ} (D : WeightedDesign size 3)
    [DecidableRel (boxGoodGraph D).Adj] [DecidableRel (boxGoodGraph D)ᶜ.Adj]
    (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin size), triple.card = 3 → ¬ Dominates D triple) :
    size.choose 2 - size ^ 2 / 4 ≤ (boxGoodGraph D)ᶜ.edgeFinset.card := by
  classical
  have hbound := card_edgeFinset_boxGoodGraph_le D hheavy hnone
  have hdisjoint : Disjoint (boxGoodGraph D).edgeFinset (boxGoodGraph D)ᶜ.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
  have hunion : (boxGoodGraph D).edgeFinset ∪ (boxGoodGraph D)ᶜ.edgeFinset
      = (⊤ : SimpleGraph (Fin size)).edgeFinset := by
    ext edge
    simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset]
    induction edge using Sym2.ind with
    | _ leftVertex rightVertex =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj, SimpleGraph.top_adj]
      constructor
      · rintro (hadjacent | ⟨hne, _⟩)
        · exact (boxGoodGraph D).ne_of_adj hadjacent
        · exact hne
      · intro hne
        by_cases hadjacent : (boxGoodGraph D).Adj leftVertex rightVertex
        · exact Or.inl hadjacent
        · exact Or.inr ⟨hne, hadjacent⟩
  have htotal : (boxGoodGraph D).edgeFinset.card + (boxGoodGraph D)ᶜ.edgeFinset.card
      = size.choose 2 := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  omega

/-- **WHY THE MANTEL ROUTE IS DEAD**, in graph form: the box-good graph of the
maximal real equiangular design is the EMPTY graph.  All fifteen pairs fail the box
test by exactly `−16/5` (`Gtz.icosaDesign_no_isBoxGoodPair`), against the six
box-bad pairs Mantel's count asked for — and `Gtz.icosaDesign_strictly_dominates`
says the design dominates anyway.  The counting has no purchase at any size. -/
theorem boxGoodGraph_icosaDesign_eq_bot : boxGoodGraph icosaDesign = ⊥ := by
  ext atomFirst atomSecond
  simp only [boxGoodGraph_adj, SimpleGraph.bot_adj, iff_false, not_and]
  intro _ hbox
  exact icosaDesign_no_isBoxGoodPair atomFirst atomSecond hbox

/-! ## T7(d): R(3,3) ≤ 6 -/

/-- Two booleans differing from a common third are equal. -/
theorem eq_of_ne_of_ne_bool {leftValue rightValue pivotValue : Bool}
    (hleft : leftValue ≠ pivotValue) (hright : rightValue ≠ pivotValue) :
    leftValue = rightValue := by
  cases leftValue <;> cases rightValue <;> cases pivotValue <;> simp_all

/-- **The pigeonhole step**: five booleans contain three equal ones.  Thirty-two
cases, decided in the kernel. -/
theorem exists_equalTriple_of_five (colourAt : Fin 5 → Bool) :
    ∃ firstIndex secondIndex thirdIndex : Fin 5,
      firstIndex ≠ secondIndex ∧ firstIndex ≠ thirdIndex ∧ secondIndex ≠ thirdIndex ∧
        colourAt firstIndex = colourAt secondIndex ∧ colourAt firstIndex = colourAt thirdIndex := by
  revert colourAt
  decide

/-- **R(3,3) ≤ 6.**  Every two-colouring of the ordered pairs of six points admits
three points carrying one colour on all three of their pairs.

The colouring is NOT assumed symmetric: the proof reads each pair in a single
fixed orientation (the pivot first, then increasing index), so the statement holds
for arbitrary `colour : Fin 6 → Fin 6 → Bool` and the symmetric case is a special
case.  Proof: the five edges at `0` contain three of one colour `v`
(`exists_equalTriple_of_five`); if any of the three induced pairs is also `v`, that
pair with `0` is monochromatic; otherwise all three induced pairs differ from `v`,
hence agree with each other (`eq_of_ne_of_ne_bool`), and the three points are
monochromatic in the other colour.

Mathlib has no Ramsey numbers, so this is proved from scratch. -/
theorem exists_monochromaticTriangle_six (colour : Fin 6 → Fin 6 → Bool) :
    ∃ firstPoint secondPoint thirdPoint : Fin 6,
      firstPoint ≠ secondPoint ∧ firstPoint ≠ thirdPoint ∧ secondPoint ≠ thirdPoint ∧
        colour firstPoint secondPoint = colour firstPoint thirdPoint ∧
        colour firstPoint secondPoint = colour secondPoint thirdPoint := by
  obtain ⟨firstIndex, secondIndex, thirdIndex, hfirstSecond, hfirstThird, hsecondThird,
    hcolourSecond, hcolourThird⟩ :=
    exists_equalTriple_of_five (fun index => colour 0 index.succ)
  have hfirstNeZero : (0 : Fin 6) ≠ firstIndex.succ := (Fin.succ_ne_zero firstIndex).symm
  have hsecondNeZero : (0 : Fin 6) ≠ secondIndex.succ := (Fin.succ_ne_zero secondIndex).symm
  have hthirdNeZero : (0 : Fin 6) ≠ thirdIndex.succ := (Fin.succ_ne_zero thirdIndex).symm
  have hsuccFirstSecond : firstIndex.succ ≠ secondIndex.succ := fun hequal =>
    hfirstSecond (Fin.succ_injective 5 hequal)
  have hsuccFirstThird : firstIndex.succ ≠ thirdIndex.succ := fun hequal =>
    hfirstThird (Fin.succ_injective 5 hequal)
  have hsuccSecondThird : secondIndex.succ ≠ thirdIndex.succ := fun hequal =>
    hsecondThird (Fin.succ_injective 5 hequal)
  by_cases hpairSecond : colour firstIndex.succ secondIndex.succ = colour 0 firstIndex.succ
  · exact ⟨0, firstIndex.succ, secondIndex.succ, hfirstNeZero, hsecondNeZero,
      hsuccFirstSecond, hcolourSecond, hpairSecond.symm⟩
  by_cases hpairThird : colour firstIndex.succ thirdIndex.succ = colour 0 firstIndex.succ
  · exact ⟨0, firstIndex.succ, thirdIndex.succ, hfirstNeZero, hthirdNeZero,
      hsuccFirstThird, hcolourThird, hpairThird.symm⟩
  by_cases hpairMixed : colour secondIndex.succ thirdIndex.succ = colour 0 secondIndex.succ
  · refine ⟨0, secondIndex.succ, thirdIndex.succ, hsecondNeZero, hthirdNeZero,
      hsuccSecondThird, ?_, ?_⟩
    · rw [← hcolourSecond, hcolourThird]
    · rw [← hcolourSecond, hpairMixed, hcolourSecond]
  · have hmixedNe : colour secondIndex.succ thirdIndex.succ ≠ colour 0 firstIndex.succ := by
      rw [hcolourSecond]
      exact hpairMixed
    exact ⟨firstIndex.succ, secondIndex.succ, thirdIndex.succ, hsuccFirstSecond,
      hsuccFirstThird, hsuccSecondThird,
      eq_of_ne_of_ne_bool hpairSecond hpairThird,
      eq_of_ne_of_ne_bool hpairSecond hmixedNe⟩

/-- R(3,3) ≤ 6 transported along any six points of any type. -/
theorem exists_monochromaticTriangle_of_pick {vertex : Type*} (colour : vertex → vertex → Bool)
    (pick : Fin 6 → vertex) :
    ∃ firstIndex secondIndex thirdIndex : Fin 6,
      firstIndex ≠ secondIndex ∧ firstIndex ≠ thirdIndex ∧ secondIndex ≠ thirdIndex ∧
        colour (pick firstIndex) (pick secondIndex) = colour (pick firstIndex) (pick thirdIndex) ∧
        colour (pick firstIndex) (pick secondIndex)
          = colour (pick secondIndex) (pick thirdIndex) :=
  exists_monochromaticTriangle_six (fun leftIndex rightIndex => colour (pick leftIndex)
    (pick rightIndex))

/-- **The consumable form of R(3,3) ≤ 6**: ANY pair predicate on ANY type,
evaluated at six points, has a monochromatic triple — three of the six indices on
which the predicate holds at all three pairs, or fails at all three.  No
decidability, no symmetry, no injectivity of the six points is required. -/
theorem exists_monochromaticTriple_of_pairPredicate {vertex : Type*}
    (pairPredicate : vertex → vertex → Prop) (pick : Fin 6 → vertex) :
    ∃ firstIndex secondIndex thirdIndex : Fin 6,
      firstIndex ≠ secondIndex ∧ firstIndex ≠ thirdIndex ∧ secondIndex ≠ thirdIndex ∧
        ((pairPredicate (pick firstIndex) (pick secondIndex)
            ∧ pairPredicate (pick firstIndex) (pick thirdIndex)
            ∧ pairPredicate (pick secondIndex) (pick thirdIndex))
          ∨ (¬ pairPredicate (pick firstIndex) (pick secondIndex)
            ∧ ¬ pairPredicate (pick firstIndex) (pick thirdIndex)
            ∧ ¬ pairPredicate (pick secondIndex) (pick thirdIndex))) := by
  classical
  obtain ⟨firstIndex, secondIndex, thirdIndex, hfirstSecond, hfirstThird, hsecondThird,
    hagreeThird, hagreeMixed⟩ :=
    exists_monochromaticTriangle_of_pick
      (fun leftVertex rightVertex => decide (pairPredicate leftVertex rightVertex)) pick
  refine ⟨firstIndex, secondIndex, thirdIndex, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  have hthirdIff : pairPredicate (pick firstIndex) (pick secondIndex)
      ↔ pairPredicate (pick firstIndex) (pick thirdIndex) := decide_eq_decide.mp hagreeThird
  have hmixedIff : pairPredicate (pick firstIndex) (pick secondIndex)
      ↔ pairPredicate (pick secondIndex) (pick thirdIndex) := decide_eq_decide.mp hagreeMixed
  by_cases hbase : pairPredicate (pick firstIndex) (pick secondIndex)
  · exact Or.inl ⟨hbase, hthirdIff.mp hbase, hmixedIff.mp hbase⟩
  · exact Or.inr ⟨hbase, fun hcontra => hbase (hthirdIff.mpr hcontra),
      fun hcontra => hbase (hmixedIff.mpr hcontra)⟩

/-- The graph form the squeeze quotes: no graph on six vertices has both itself
and its complement triangle-free. -/
theorem not_cliqueFree_three_and_compl_cliqueFree_three (graph : SimpleGraph (Fin 6)) :
    ¬ (graph.CliqueFree 3 ∧ graphᶜ.CliqueFree 3) := by
  classical
  rintro ⟨hgraphFree, hcomplFree⟩
  obtain ⟨firstIndex, secondIndex, thirdIndex, hfirstSecond, hfirstThird, hsecondThird,
    hmonochromatic⟩ := exists_monochromaticTriple_of_pairPredicate graph.Adj id
  rcases hmonochromatic with ⟨hadjFirstSecond, hadjFirstThird, hadjSecondThird⟩
    | ⟨hnonFirstSecond, hnonFirstThird, hnonSecondThird⟩
  · exact hgraphFree {firstIndex, secondIndex, thirdIndex}
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨hadjFirstSecond, hadjFirstThird, hadjSecondThird⟩)
  · refine hcomplFree {firstIndex, secondIndex, thirdIndex}
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨?_, ?_, ?_⟩)
    · exact ⟨hfirstSecond, hnonFirstSecond⟩
    · exact ⟨hfirstThird, hnonFirstThird⟩
    · exact ⟨hsecondThird, hnonSecondThird⟩

/-! ### The matching lower bound: five vertices are not enough

The pentagon `i ~ i ± 1 (mod 5)` and its complement, the pentagram `i ~ i ± 2`,
are both five-cycles and hence both triangle-free, so `R(3,3) > 5`.  Together with
`not_cliqueFree_three_and_compl_cliqueFree_three` this is `R(3,3) = 6` on the nose,
not merely the upper bound the squeeze consumes. -/

/-- **The pentagon** `i ~ i ± 1 (mod 5)`. -/
def pentagonGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun leftVertex rightVertex => leftVertex - rightVertex = 1)

theorem pentagonGraph_adj (leftVertex rightVertex : Fin 5) :
    pentagonGraph.Adj leftVertex rightVertex
      ↔ leftVertex ≠ rightVertex
        ∧ (leftVertex - rightVertex = 1 ∨ rightVertex - leftVertex = 1) :=
  SimpleGraph.fromRel_adj _ _ _

/-- **Neither the pentagon nor the pentagram carries a triangle**, checked over
all one hundred and twenty-five index triples in the kernel. -/
theorem pentagon_no_monochromaticTriple (first second third : Fin 5)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    ¬ ((first - second = 1 ∨ second - first = 1)
        ∧ (first - third = 1 ∨ third - first = 1)
        ∧ (second - third = 1 ∨ third - second = 1))
      ∧ ¬ (¬ (first - second = 1 ∨ second - first = 1)
        ∧ ¬ (first - third = 1 ∨ third - first = 1)
        ∧ ¬ (second - third = 1 ∨ third - second = 1)) := by
  revert first second third
  decide

/-- The pentagon is triangle-free. -/
theorem cliqueFree_three_pentagonGraph : pentagonGraph.CliqueFree 3 := by
  intro clique hclique
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcliqueEq⟩ :=
    Finset.card_eq_three.mp hclique.2
  have htriple : pentagonGraph.IsNClique 3 {first, second, third} := hcliqueEq ▸ hclique
  obtain ⟨hadjFirstSecond, hadjFirstThird, hadjSecondThird⟩ :=
    SimpleGraph.is3Clique_triple_iff.mp htriple
  exact (pentagon_no_monochromaticTriple first second third hfirstSecond hfirstThird
    hsecondThird).1
    ⟨((pentagonGraph_adj first second).mp hadjFirstSecond).2,
      ((pentagonGraph_adj first third).mp hadjFirstThird).2,
      ((pentagonGraph_adj second third).mp hadjSecondThird).2⟩

/-- The pentagram — the pentagon's complement — is triangle-free. -/
theorem cliqueFree_three_compl_pentagonGraph : pentagonGraphᶜ.CliqueFree 3 := by
  intro clique hclique
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcliqueEq⟩ :=
    Finset.card_eq_three.mp hclique.2
  have htriple : pentagonGraphᶜ.IsNClique 3 {first, second, third} := hcliqueEq ▸ hclique
  obtain ⟨hadjFirstSecond, hadjFirstThird, hadjSecondThird⟩ :=
    SimpleGraph.is3Clique_triple_iff.mp htriple
  refine (pentagon_no_monochromaticTriple first second third hfirstSecond hfirstThird
    hsecondThird).2 ⟨?_, ?_, ?_⟩
  · exact fun hrelation =>
      ((SimpleGraph.compl_adj pentagonGraph first second).mp hadjFirstSecond).2
        ((pentagonGraph_adj first second).mpr ⟨hfirstSecond, hrelation⟩)
  · exact fun hrelation =>
      ((SimpleGraph.compl_adj pentagonGraph first third).mp hadjFirstThird).2
        ((pentagonGraph_adj first third).mpr ⟨hfirstThird, hrelation⟩)
  · exact fun hrelation =>
      ((SimpleGraph.compl_adj pentagonGraph second third).mp hadjSecondThird).2
        ((pentagonGraph_adj second third).mpr ⟨hsecondThird, hrelation⟩)

/-- **`R(3,3) > 5`**: a graph on five vertices with both it and its complement
triangle-free EXISTS.  With `not_cliqueFree_three_and_compl_cliqueFree_three` this
pins the Ramsey number at exactly six. -/
theorem exists_cliqueFree_three_and_compl_cliqueFree_three_five :
    ∃ graph : SimpleGraph (Fin 5), graph.CliqueFree 3 ∧ graphᶜ.CliqueFree 3 :=
  ⟨pentagonGraph, cliqueFree_three_pentagonGraph, cliqueFree_three_compl_pentagonGraph⟩

/-! ## The squeeze: Ramsey applied to the box-good graph -/

/-- **The Ramsey squeeze at rank three.**  Every design on at least six atoms
either dominates on some triple, or owns a triple ALL THREE of whose pairs are
box-bad.  Ramsey supplies the dichotomy; `Gtz.dominates_of_isBoxGoodTriangle` turns
the box-good side into domination.

The second disjunct is where every known witness sits: at `Gtz.icosaDesign` ALL
fifteen pairs are box-bad and the design still dominates, so this dichotomy
constrains a certificate family, not the conjecture.  The value of the statement is
that the box-bad side is now a NAMED object with three specific atoms attached, and
`Gtz.dominates_of_isBoxGoodTriangle` is the only escape from it. -/
theorem exists_dominating_triple_or_boxBadTriple {size : ℕ} (hsize : 6 ≤ size)
    (D : WeightedDesign size 3) (hheavy : AllHeavy D) :
    (∃ triple : Finset (Fin size), triple.card = 3 ∧ Dominates D triple)
      ∨ ∃ first second third : Fin size, first ≠ second ∧ first ≠ third ∧ second ≠ third
          ∧ ¬ IsBoxGoodPair D first second ∧ ¬ IsBoxGoodPair D first third
          ∧ ¬ IsBoxGoodPair D second third := by
  classical
  obtain ⟨firstIndex, secondIndex, thirdIndex, hfirstSecond, hfirstThird, hsecondThird,
    hmonochromatic⟩ :=
    exists_monochromaticTriple_of_pairPredicate (IsBoxGoodPair D) (Fin.castLE hsize)
  have hcastFirstSecond : Fin.castLE hsize firstIndex ≠ Fin.castLE hsize secondIndex :=
    fun hequal => hfirstSecond (Fin.castLE_injective hsize hequal)
  have hcastFirstThird : Fin.castLE hsize firstIndex ≠ Fin.castLE hsize thirdIndex :=
    fun hequal => hfirstThird (Fin.castLE_injective hsize hequal)
  have hcastSecondThird : Fin.castLE hsize secondIndex ≠ Fin.castLE hsize thirdIndex :=
    fun hequal => hsecondThird (Fin.castLE_injective hsize hequal)
  rcases hmonochromatic with hgood | hbad
  · refine Or.inl ⟨{Fin.castLE hsize firstIndex, Fin.castLE hsize secondIndex,
      Fin.castLE hsize thirdIndex}, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simp [hcastFirstSecond, hcastFirstThird]),
        Finset.card_insert_of_notMem (by simp [hcastSecondThird]), Finset.card_singleton]
    · exact dominates_of_isBoxGoodTriangle hheavy hcastFirstSecond hcastFirstThird
        hcastSecondThird ⟨hgood.1, hgood.2.1, hgood.2.2⟩
  · exact Or.inr ⟨Fin.castLE hsize firstIndex, Fin.castLE hsize secondIndex,
      Fin.castLE hsize thirdIndex, hcastFirstSecond, hcastFirstThird, hcastSecondThird,
      hbad.1, hbad.2.1, hbad.2.2⟩

/-! ## Non-vacuity controls at a shipped witness

`Gtz.nearPencilSixDesign` (`Gtz.Design.NearPencilTransport`) carries a saturated
atom on the nose — pole `![0,0,2]` of leverage `4` at weight `1/4` — and three of
its atoms are pairwise orthogonal, so both gates of this file fire on a design
already in the repository, and the collar's budget there is a strictly positive
number rather than an equality in disguise. -/

/-- The near-pencil pole has leverage four. -/
theorem nearPencilSixDesign_pole_leverage : leverageOf (nearPencilSixDesign.atom 5) = 4 := by
  have hatom : nearPencilSixDesign.atom 5 = ![0, 0, 2] := rfl
  rw [hatom, leverageOf, Fin.sum_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- The near-pencil pole carries weight one quarter. -/
theorem nearPencilSixDesign_pole_weight : nearPencilSixDesign.weight 5 = 1 / 4 := rfl

/-- **The near-pencil pole is saturated**: `t . l = (1/4) . 4 = 1`, exactly the
boundary case of the landed share ceiling `Gtz.weighted_leverage_le_one`. -/
theorem nearPencilSixDesign_pole_share :
    nearPencilSixDesign.weight 5 * leverageOf (nearPencilSixDesign.atom 5) = 1 := by
  rw [nearPencilSixDesign_pole_weight, nearPencilSixDesign_pole_leverage]
  norm_num

/-- **T7(b) fires at a shipped witness**: the near-pencil design has a triple
through its saturated pole whose gap is positive definite. -/
theorem exists_posDef_triple_nearPencilSixDesign :
    ∃ triple : Finset (Fin 6), triple.card = 3 ∧ (5 : Fin 6) ∈ triple
      ∧ (subsetSum nearPencilSixDesign triple - 1).PosDef :=
  exists_posDef_triple_of_weightedLeverage_eq_one (by norm_num) nearPencilSixDesign 5
    nearPencilSixDesign_pole_share

/-- **The collar's budget at the near-pencil witness is a positive radius**: every
`collarBound < 1` satisfies it, since `4(1 - t) = 3` and `L(L - 1)t = 3`.  So the
collar is a genuine neighbourhood of the saturated locus and not a restatement of
saturation. -/
theorem nearPencilSixDesign_collarBudget_of_lt_one {collarBound : ℝ}
    (hsmall : collarBound < 1) :
    4 * (1 - nearPencilSixDesign.weight 5) * collarBound
      < leverageOf (nearPencilSixDesign.atom 5)
          * (leverageOf (nearPencilSixDesign.atom 5) - 1) * nearPencilSixDesign.weight 5 := by
  rw [nearPencilSixDesign_pole_weight, nearPencilSixDesign_pole_leverage]
  linarith

/-- **T7(a) fires at a shipped witness**: `![2,0,0]`, `![0,2,0]` and `![0,0,2]` are
pairwise orthogonal atoms of leverage four, so the triple they span dominates. -/
theorem dominates_nearPencilSixDesign_orthogonalTriple :
    Dominates nearPencilSixDesign {0, 1, 5} := by
  have hfirstAtom : nearPencilSixDesign.atom 0 = ![2, 0, 0] := rfl
  have hsecondAtom : nearPencilSixDesign.atom 1 = ![0, 2, 0] := rfl
  have hpoleAtom : nearPencilSixDesign.atom 5 = ![0, 0, 2] := rfl
  refine dominates_of_orthogonalTriple_of_one_le nearPencilSixDesign (by decide) (by decide)
    (by decide) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hfirstAtom, leverageOf, Fin.sum_univ_three]
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  · rw [hsecondAtom, leverageOf, Fin.sum_univ_three]
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  · rw [nearPencilSixDesign_pole_leverage]
    norm_num
  · rw [atomPairing, hfirstAtom, hsecondAtom, dotProduct, Fin.sum_univ_three]
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  · rw [atomPairing, hfirstAtom, hpoleAtom, dotProduct, Fin.sum_univ_three]
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  · rw [atomPairing, hsecondAtom, hpoleAtom, dotProduct, Fin.sum_univ_three]
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

end Gtz
