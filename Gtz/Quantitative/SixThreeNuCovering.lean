/-
# The `nu`-covering of the `(6,3)` hypersimplex

The campaign's `(6,3)` residual in the coordinate it calls `nu`:

    `nu_c = 1 / ell_c`      (the INVARIANT LEVERAGE, `ell_c = |g_c|^2`),

together with the two facts that make it a covering problem — on a uniform-share
design `sum_c nu_c = m/k`, which at `(6,3)` is `2` over six atoms so the mean is
`1/3`, and domination of a triple `T` is exactly `Gamma[T] ⪰ diag(nu)|_T`.

## LOUD HONESTY FIRST: the reformulation was already shipped, reflected

`Gtz/Quantitative/WeightedTripleCriterion.lean` already carries the entire
covering reformulation, in the CAPACITY coordinate `tau_c = 1 - 1/ell_c`
(`Gtz.weightSlack`, and the same function again as `Gtz.atomCapacity`).  Since

    `nu_c = 1 - tau_c`      (`Gtz.inv_leverage_eq_one_sub_weightSlack`),

`Gtz.slackSimplex` IS the `nu`-hypersimplex `Delta = {nu in [0,1]^6 : sum nu = 2}`,
`Gtz.heavySlackSimplex` IS the open design region, `Gtz.tripleSlackCell` IS the
cell `K_T`, and `Gtz.gtzUniformShareSixThree_iff_forall_coversHeavySlackSimplex` IS
the covering equivalence.  Convexity, closedness, 3-locality and monotonicity of
the cells are shipped; so is the budget `sum_c 1/ell_c = m/k`
(`Gtz.sum_inv_leverage_of_uniformShare`).

This file therefore does NOT re-derive them and mints NO new coordinate: `nu` is
the function `fun c => (leverageOf (D.atom c))⁻¹`, and `weightSlack`,
`atomCapacity`, `atomWeightSlack` are already three live names for that axis.
What it lands instead is (a) the reflection dictionary, (b) the
`Gamma[T] ⪰ diag(nu)|_T` form, which is the `nu`-side statement that was genuinely
absent, (c) the concavity the shipped file gets around, and (d) new mathematics:
the quarter refutation, the boundary identification, and two walls.

## PROVED

1. **The `nu` dictionary, unconditional.**
   `Gtz.dominates_triple_iff_posSemidef_gramSubmatrix_sub_diagonal`: for a
   rank-three design with three distinct nondegenerate atoms,

       `Dominates D {a,b,c}  <->  Gamma[{a,b,c}] - diag(nu_a, nu_b, nu_c) ⪰ 0`.

   No share hypothesis, no heaviness.

2. **The covering equivalence in `nu` coordinates.**
   `Gtz.gtzUniformShareSixThree_iff_forall_coversInvariantLeverageDesignRegion`:
   every uniform-share all-heavy weighted `(6,3)` design has a dominating triple
   iff for every unit-norm tight frame of six directions in `R^3` the twenty cells
   cover `{nu in (0,1)^6 : sum nu = 2}`.  Both directions unconditional, obtained
   from the shipped slack equivalence by the reflection.

3. **The margin is CONCAVE, and the cells are convex.**  `Gtz.concave_lambdaMinMat`
   — the least eigenvalue is concave in the matrix, proved from the Rayleigh
   characterisation alone, with no appeal to the ORDER structure on the spectrum,
   which this pinned mathlib does not have — and `Gtz.concave_tripleSlackMargin`,
   `Gtz.concave_invariantLeverageMargin`.  The cell is the margin's nonnegativity
   set (`Gtz.mem_tripleSlackCell_iff_zero_le_tripleSlackMargin`).  Note that
   `Gtz.convex_invariantLeverageCell` is proved INDEPENDENTLY of all of this, by
   splitting the shifted block directly; no declaration in this file derives
   convexity from the concavity, and the shipped `Gtz.convex_tripleSlackCell` is
   the same fact in the reflected coordinate.

4. **THE QUARTER CONJECTURE IS FALSE, by an exact rational witness.**
   `Gtz.not_quarterConjectureSixThree`.  The witness `Gtz.quarterFrame` is the
   three-orthogonal-pair frame

       `u_0 = (0, 20/29, 21/29)`,   `u_1 = (0, -21/29, 20/29)`,
       `u_2 = (21/29, 0, 20/29)`,   `u_3 = (20/29, 0, -21/29)`,
       `u_4 = (4/5, 3/5, 0)`,       `u_5 = (-3/5, 4/5, 0)`,

   verified unit (`20^2 + 21^2 = 29^2`, `3-4-5`) and verified tight EXACTLY,
   `quarterFrame^T quarterFrame = 2 . 1` — hence `sum_c u_c u_c^T = 2 I` — and
   every one of the twenty triples fails `lambda_min(Gamma[T]) >= 1/2`
   (`Gtz.not_mem_tripleSlackCell_quarterGram_half`), all twenty at the SAME clause:
   the determinant clause of `Gtz.posSemidef_slackHollowThree_iff` at capacity
   `1/2`, which reads `sigma_T - 4 P_T <= 1/4` on the squared correlations.  The
   binding triple is `{1,3,4}` with `sigma - 4 P = 4663129/17682025`, exceeding
   `1/4` by `970491/70728100`.  A float scan reports the largest least eigenvalue
   as `0.43610` at that same triple; nothing proved here depends on that number.

5. **And V6 survives on the witness**, so the refutation is of the threshold `1/2`
   and not of the covering: `Gtz.quarterDesign` is a genuine point of the
   equal-share stratum (`Gtz.isEqualShare_quarterDesign`) and U6 fires on it
   (`Gtz.exists_dominating_triple_quarterDesign`).  Its max-min edge weight is at
   least `3969/21025 > 1/8` (`Gtz.one_eighth_lt_maxMinWeight_quarterDesign`), so
   the closed branch `m <= 1/8` of the quarter THEOREM does not reach it.

6. **And the quarter conjecture was never equivalent to V6.**
   `Gtz.constantHalf_notMem_invariantLeverageHypersimplex`: the constant `nu == 1/2`
   sums to `3`, not `2`, so it is not a point of the polytope at all; the
   admissible uniform point is `nu == 1/3`
   (`Gtz.constantThird_mem_invariantLeverageHypersimplex`).

7. **The boundary where the campaign's joint descent found margin exactly zero is
   COVERED, not a failure.**  `Gtz.mem_invariantLeverageCell_of_vanishing`: whenever
   three coordinates of `nu` vanish, the triple carrying them lies in the cell,
   because the block is then the Gram block and a Gram is positive semidefinite —
   no hypothesis on the frame at all.  And
   `Gtz.tripleSlackMargin_unitComplement_eq_lambdaMinMat_of_vanishing` identifies
   the margin there as `lambda_min(Gamma[T])`, which is `0` exactly when the three
   directions are linearly dependent.  So the reported infimum `0` at
   `nu = [0, *, 0, *, *, 0]` is a covering with a SINGULAR certificate.

8. **Two exact walls on the interior-margin route.**
   `Gtz.exists_third_le_of_sum_eq_two` and
   `Gtz.eq_third_of_le_third_of_sum_eq_two`: on the polytope `max_c nu_c >= 1/3`,
   with equality only at the uniform point.  Feeding the frame-only U6 constant
   `1/3` through the only cheap sufficient condition
   (`Gtz.mem_invariantLeverageCell_of_le_lambdaMinMat`: spectral dominance) therefore
   certifies a triple only where that triple's own three coordinates are at most
   `1/3` — never all of `Delta`.  And
   `Gtz.gram_eq_zero_of_mem_invariantLeverageCell_of_eq_one`: at a point with
   `nu_a = 1` a cell containing `a` forces `a`'s two correlations inside the triple
   to VANISH, so on that face only triples avoiding `a`, or triples in which `a` is
   orthogonal to both partners, can cover.

9. **KKM and KKMS are the wrong tool.**  The decisive reason is the DIRECTION of
   the implication: KKM and Shapley's subset-indexed KKMS both derive a nonempty
   intersection FROM a covering-type hypothesis on the faces, whereas V6 asks us to
   PROVE the covering; only the contrapositive is ever available, and it could only
   refute a covering.  `Gtz.zero_mem_iInter_invariantLeverageCell` separately
   records that the origin lies in EVERY cell — but see NOT PROVED below: that does
   NOT establish that the KKMS conclusion is vacuous here.

## HYPOTHESIS

Nothing in this file is conditional.  Every declaration is unconditional in its
stated hypotheses; the hypotheses used are exactly nondegeneracy of atoms
(`0 < leverageOf`), distinctness of indices, unit diagonal and symmetry of the
Gram, `IsUnitTightFrameSix` for the frame statements, and uniform share plus
`AllHeavy` where the shipped equivalence needs them.

## NOT PROVED

**The interior margin itself, which was this lane's target 3.**  The exact
remaining gap: the shipped band gate
`Gtz.exists_dominates_of_sixteen_twentyfifths_le_weightSlack` covers every
uniform-share all-heavy design with `min_c tau_c >= 16/25`, i.e. every `nu` with
`max_c nu_c <= 9/25` (`Gtz.exists_dominates_of_inv_leverage_le_nine_twentyfifths`),
and the polytope reaches `max_c nu_c = 1`.  The gap `9/25 -> 1` is untouched.
No epsilon-dependent floor is proved: the plateau value `0.028` the campaign's
descent reports under `nu >= epsilon` is NOT established here, and item 8 is the
record of exactly why the two cheap routes cannot reach it.  No statement in this
file asserts V6, `GtzUniformShareSixThree`, or `GtzWeighted 6 3`.

**The vacuity leg of item 9 is WITHDRAWN, and the correction is recorded here
rather than deleted.**  `Gtz.zero_mem_iInter_invariantLeverageCell` does not make
the KKMS conclusion information-free, because the origin is not a point of `Delta`
— its coordinates sum to `0`, not `2` — and KKMS asserts a common point INSIDE the
simplex.  On the witness frame of §6 the twenty cells in fact have EMPTY
intersection with `Delta`: membership in `K_T` with `nu >= 0` forces
`sum_{i in T} nu_i w_i^2 <= lambda_min(Gamma[T])` at the least-eigenvalue
direction `w`, and the four near-singular triples `{1,3,5}`, `{1,2,4}`, `{0,3,4}`,
`{0,2,5}` (least eigenvalues about `0.0019`, `0.0045`, `0.0045`, `0.0081`) between
them touch all six atoms, capping every coordinate below `0.015` and so
`sum_c nu_c` below `0.06`, against the required `2`.  Those four figures are
floating point and nothing is proved from them; they are reported as the reason the
vacuity claim is withdrawn, not as a result.  Item 9's FIRST reason — the direction
of the implication — is unaffected and is on its own decisive.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Design.FrameConservation
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.TauOrderStatistics
import Gtz.Quantitative.WeightedTripleCriterion
import Gtz.Quantitative.EqualShareSixThree

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {m k size : ℕ}

/-! ## 1. The reflection `nu = 1 - tau` -/

/-- The pointwise complement `v |-> 1 - v`, the affine involution carrying the
campaign's invariant leverage `nu` to the shipped capacity `tau` and back. -/
def unitComplement (values : Fin size → ℝ) : Fin size → ℝ := fun index => 1 - values index

theorem unitComplement_apply (values : Fin size → ℝ) (index : Fin size) :
    unitComplement values index = 1 - values index := rfl

theorem unitComplement_unitComplement (values : Fin size → ℝ) :
    unitComplement (unitComplement values) = values := by
  funext index
  rw [unitComplement_apply, unitComplement_apply]
  ring

/-- **THE REFLECTION.**  The invariant leverage is one minus the shipped
capacity, so `nu` is not a new coordinate. -/
theorem inv_leverage_eq_one_sub_weightSlack (D : WeightedDesign m k) (atomIndex : Fin m) :
    (leverageOf (D.atom atomIndex))⁻¹ = 1 - weightSlack D atomIndex := by
  rw [weightSlack]
  ring

/-- **THE BUDGET in `nu` coordinates at `(6,3)`**: the six invariant leverages of
a uniform-share design sum to `2`, so their mean is `1/3`. -/
theorem sum_inv_leverage_eq_two_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    ∑ atomIndex, (leverageOf (D.atom atomIndex))⁻¹ = 2 := by
  have hshare : ∀ atomIndex : Fin 6, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) :=
    fun atomIndex => by rw [huniform atomIndex]; norm_num
  have hlaw := sum_inv_leverage_of_uniformShare D (by norm_num) hshare
  rw [hlaw]
  norm_num

/-! ## 2. `Gamma[T] ⪰ diag(nu)|_T` -/

/-- **THE IDENTITY.**  Subtracting `diag(nu)` from a `3 x 3` principal block whose
diagonal entries are one and whose relevant off-diagonal pairs agree produces
exactly the shipped slack-shifted hollow block at capacities `1 - nu`. -/
theorem submatrix_sub_diagonal_eq_slackHollowThree
    (gram : Matrix (Fin size) (Fin size) ℝ) {first second third : Fin size}
    (hunitFirst : gram first first = 1) (hunitSecond : gram second second = 1)
    (hunitThird : gram third third = 1)
    (hcommFirstSecond : gram second first = gram first second)
    (hcommFirstThird : gram third first = gram first third)
    (hcommSecondThird : gram third second = gram second third)
    (invariantLeverage : Fin size → ℝ) :
    gram.submatrix ![first, second, third] ![first, second, third]
        - Matrix.diagonal (fun slot => invariantLeverage (![first, second, third] slot))
      = slackHollowThree (1 - invariantLeverage first) (1 - invariantLeverage second)
          (1 - invariantLeverage third) (gram first second) (gram first third)
          (gram second third) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [slackHollowThree, Matrix.sub_apply, hunitFirst, hunitSecond, hunitThird,
      hcommFirstSecond, hcommFirstThird, hcommSecondThird]

/-- **THE `nu` DICTIONARY.**  A triple of distinct nondegenerate atoms of a
rank-three design dominates exactly when the direction Gram's block dominates the
diagonal of the invariant leverages: `Gamma[T] ⪰ diag(nu)|_T`.  No share
hypothesis, no heaviness. -/
theorem dominates_triple_iff_posSemidef_gramSubmatrix_sub_diagonal (D : WeightedDesign m 3)
    {first second third : Fin m} (hfirstPos : 0 < leverageOf (D.atom first))
    (hsecondPos : 0 < leverageOf (D.atom second)) (hthirdPos : 0 < leverageOf (D.atom third))
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Dominates D {first, second, third}
      ↔ ((directionGramMatrix D).submatrix ![first, second, third] ![first, second, third]
          - Matrix.diagonal
              (fun slot =>
                (leverageOf (D.atom (![first, second, third] slot)))⁻¹)).PosSemidef := by
  rw [submatrix_sub_diagonal_eq_slackHollowThree (directionGramMatrix D)
    (directionGram_self D hfirstPos) (directionGram_self D hsecondPos)
    (directionGram_self D hthirdPos) (directionGram_comm D second first)
    (directionGram_comm D third first) (directionGram_comm D third second)
    (fun atomIndex => (leverageOf (D.atom atomIndex))⁻¹)]
  exact dominates_triple_iff_posSemidef_slackHollowThree D hfirstPos hsecondPos hthirdPos
    hfirstSecond hfirstThird hsecondThird

/-! ## 3. The cell, in `nu` coordinates -/

/-- **THE CELL `K_T` in `nu` coordinates**: those invariant-leverage vectors whose
diagonal is dominated by the triple's Gram block. -/
def invariantLeverageCell (gram : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) : Set (Fin size → ℝ) :=
  {invariantLeverage |
    (gram.submatrix ![first, second, third] ![first, second, third]
      - Matrix.diagonal
          (fun slot => invariantLeverage (![first, second, third] slot))).PosSemidef}

theorem mem_invariantLeverageCell_iff {gram : Matrix (Fin size) (Fin size) ℝ}
    {first second third : Fin size} {invariantLeverage : Fin size → ℝ} :
    invariantLeverage ∈ invariantLeverageCell gram first second third
      ↔ (gram.submatrix ![first, second, third] ![first, second, third]
          - Matrix.diagonal
              (fun slot => invariantLeverage (![first, second, third] slot))).PosSemidef :=
  Iff.rfl

/-- **THE CELL IS THE SHIPPED CELL, REFLECTED.**  `K_T` in `nu` coordinates is
`Gtz.tripleSlackCell` at the complementary vector, so convexity, closedness,
3-locality and monotonicity all transfer from the shipped layer. -/
theorem mem_invariantLeverageCell_iff_unitComplement_mem_tripleSlackCell
    (gram : Matrix (Fin size) (Fin size) ℝ) {first second third : Fin size}
    (hunitFirst : gram first first = 1) (hunitSecond : gram second second = 1)
    (hunitThird : gram third third = 1)
    (hcommFirstSecond : gram second first = gram first second)
    (hcommFirstThird : gram third first = gram first third)
    (hcommSecondThird : gram third second = gram second third)
    (invariantLeverage : Fin size → ℝ) :
    invariantLeverage ∈ invariantLeverageCell gram first second third
      ↔ unitComplement invariantLeverage ∈ tripleSlackCell gram first second third := by
  rw [mem_invariantLeverageCell_iff, submatrix_sub_diagonal_eq_slackHollowThree gram hunitFirst
    hunitSecond hunitThird hcommFirstSecond hcommFirstThird hcommSecondThird,
    mem_tripleSlackCell_iff]
  simp only [unitComplement_apply]

/-- The shipped cell reads only the three off-diagonal correlations, so replacing
the involution by any matrix that agrees there leaves it unchanged.  This is what
lets `Gtz.frameCorrelationInvolution` and the frame's own Gram be used
interchangeably. -/
theorem tripleSlackCell_congr_offDiagonal
    {leftMatrix rightMatrix : Matrix (Fin size) (Fin size) ℝ} {first second third : Fin size}
    (hfirstSecond : leftMatrix first second = rightMatrix first second)
    (hfirstThird : leftMatrix first third = rightMatrix first third)
    (hsecondThird : leftMatrix second third = rightMatrix second third) :
    tripleSlackCell leftMatrix first second third
      = tripleSlackCell rightMatrix first second third := by
  ext slack
  rw [mem_tripleSlackCell_iff, mem_tripleSlackCell_iff, hfirstSecond, hfirstThird, hsecondThird]

/-- **THE CELL IS CONVEX**, in `nu` coordinates.  Proved directly, by splitting the
shifted block into a convex combination of two positive semidefinite blocks.  It is
NOT transported from the shipped `Gtz.convex_tripleSlackCell`, and it is NOT derived
from the §4 concavity — that is a strictly stronger statement which this file proves
but does not route convexity through. -/
theorem convex_invariantLeverageCell (gram : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    Convex ℝ (invariantLeverageCell gram first second third) := by
  intro leftPoint hleftMember rightPoint hrightMember leftShare rightShare hleftShare
    hrightShare hshares
  obtain rfl : rightShare = 1 - leftShare := by linarith
  rw [mem_invariantLeverageCell_iff] at hleftMember hrightMember ⊢
  have hsplit : gram.submatrix ![first, second, third] ![first, second, third]
        - Matrix.diagonal
            (fun slot => (leftShare • leftPoint + (1 - leftShare) • rightPoint)
              (![first, second, third] slot))
      = leftShare • (gram.submatrix ![first, second, third] ![first, second, third]
            - Matrix.diagonal (fun slot => leftPoint (![first, second, third] slot)))
        + (1 - leftShare) • (gram.submatrix ![first, second, third] ![first, second, third]
            - Matrix.diagonal (fun slot => rightPoint (![first, second, third] slot))) := by
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [hsplit]
  exact (hleftMember.smul hleftShare).add (hrightMember.smul hrightShare)

/-- **THE CELL IS ANTITONE in `nu`**: lowering the invariant leverages preserves
domination, since the difference is a nonnegative diagonal.  The `nu`-reading of
the shipped `Gtz.mem_tripleSlackCell_of_le`. -/
theorem mem_invariantLeverageCell_of_le {gram : Matrix (Fin size) (Fin size) ℝ}
    {first second third : Fin size} {upperPoint lowerPoint : Fin size → ℝ}
    (hmember : upperPoint ∈ invariantLeverageCell gram first second third)
    (hfirst : lowerPoint first ≤ upperPoint first)
    (hsecond : lowerPoint second ≤ upperPoint second)
    (hthird : lowerPoint third ≤ upperPoint third) :
    lowerPoint ∈ invariantLeverageCell gram first second third := by
  rw [mem_invariantLeverageCell_iff] at hmember ⊢
  have hsplit : gram.submatrix ![first, second, third] ![first, second, third]
        - Matrix.diagonal (fun slot => lowerPoint (![first, second, third] slot))
      = (gram.submatrix ![first, second, third] ![first, second, third]
          - Matrix.diagonal (fun slot => upperPoint (![first, second, third] slot)))
        + Matrix.diagonal (fun slot =>
            upperPoint (![first, second, third] slot) - lowerPoint (![first, second, third] slot)) := by
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply]
    split_ifs <;> ring
  rw [hsplit]
  refine hmember.add (Matrix.PosSemidef.diagonal ?_)
  intro slot
  fin_cases slot <;> simp <;> linarith

/-- **THE ORIGIN LIES IN EVERY CELL.**  At `nu = 0` the block is the Gram itself,
which is positive semidefinite for any Gram.  Stated for an arbitrary matrix of
the form `frame * frame^T`, which is what a Gram is. -/
theorem zero_mem_invariantLeverageCell {rank : ℕ} (frame : Matrix (Fin size) (Fin rank) ℝ)
    (first second third : Fin size) :
    (0 : Fin size → ℝ) ∈ invariantLeverageCell (frame * frameᵀ) first second third := by
  rw [mem_invariantLeverageCell_iff]
  have hzero : Matrix.diagonal (fun slot => (0 : Fin size → ℝ) (![first, second, third] slot))
      = 0 := by
    ext rowIndex colIndex
    simp [Matrix.diagonal_apply]
  rw [hzero, sub_zero]
  refine Matrix.PosSemidef.submatrix ?_ _
  simpa using Matrix.posSemidef_conjTranspose_mul_self (frameᵀ)

/-! ## 4. The margin, and its concavity -/

/-- **THE MARGIN of a triple**, in the shipped capacity coordinate: the least
eigenvalue of the slack-shifted hollow block. -/
noncomputable def tripleSlackMargin (invol : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) (slack : Fin size → ℝ) : ℝ :=
  lambdaMinMat (slackHollowThree (slack first) (slack second) (slack third)
    (invol first second) (invol first third) (invol second third))

/-- **THE CELL IS THE MARGIN'S NONNEGATIVITY SET**, so `K_T = {h_T >= 0}`
literally. -/
theorem mem_tripleSlackCell_iff_zero_le_tripleSlackMargin
    (invol : Matrix (Fin size) (Fin size) ℝ) (first second third : Fin size)
    (slack : Fin size → ℝ) :
    slack ∈ tripleSlackCell invol first second third
      ↔ 0 ≤ tripleSlackMargin invol first second third slack := by
  rw [mem_tripleSlackCell_iff, tripleSlackMargin,
    le_lambdaMinMat_iff_posSemidef_sub_smul_one _ (slackHollowThree_transpose _ _ _ _ _ _) 0,
    zero_smul, sub_zero]

/-- **THE LEAST EIGENVALUE IS CONCAVE IN THE MATRIX**, from the Rayleigh
characterisation alone — no eigenvectors, no diagonalisation, no ordering of the
spectrum.  Of those three it is only the ORDERING that is genuinely absent from this
pinned mathlib: `Matrix.IsHermitian.spectral_theorem` and `.eigenvalues` do exist,
but there is no sorted-eigenvalue API, which is why the Rayleigh route is the one
taken. -/
theorem concave_lambdaMinMat {dim : ℕ} [Nonempty (Fin dim)]
    (leftBlock rightBlock : Matrix (Fin dim) (Fin dim) ℝ) {leftShare rightShare : ℝ}
    (hleftShare : 0 ≤ leftShare) (hrightShare : 0 ≤ rightShare) :
    leftShare * lambdaMinMat leftBlock + rightShare * lambdaMinMat rightBlock
      ≤ lambdaMinMat (leftShare • leftBlock + rightShare • rightBlock) := by
  rw [le_lambdaMinMat_iff_forall_dotProduct]
  intro direction
  have hleft := (le_lambdaMinMat_iff_forall_dotProduct leftBlock
    (lambdaMinMat leftBlock)).mp le_rfl direction
  have hright := (le_lambdaMinMat_iff_forall_dotProduct rightBlock
    (lambdaMinMat rightBlock)).mp le_rfl direction
  have hexpand : direction ⬝ᵥ (leftShare • leftBlock + rightShare • rightBlock) *ᵥ direction
      = leftShare * (direction ⬝ᵥ leftBlock *ᵥ direction)
        + rightShare * (direction ⬝ᵥ rightBlock *ᵥ direction) := by
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
  rw [hexpand]
  nlinarith [hleft, hright, hleftShare, hrightShare]

/-- **THE MARGIN IS CONCAVE in the capacity vector.**  The block is affine in the
capacities, so the concavity of the least eigenvalue transports verbatim. -/
theorem concave_tripleSlackMargin (invol : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) (leftSlack rightSlack : Fin size → ℝ)
    {leftShare rightShare : ℝ} (hleftShare : 0 ≤ leftShare) (hrightShare : 0 ≤ rightShare)
    (hshares : leftShare + rightShare = 1) :
    leftShare * tripleSlackMargin invol first second third leftSlack
        + rightShare * tripleSlackMargin invol first second third rightSlack
      ≤ tripleSlackMargin invol first second third
          (leftShare • leftSlack + rightShare • rightSlack) := by
  obtain rfl : rightShare = 1 - leftShare := by linarith
  have hsplit : slackHollowThree ((leftShare • leftSlack + (1 - leftShare) • rightSlack) first)
        ((leftShare • leftSlack + (1 - leftShare) • rightSlack) second)
        ((leftShare • leftSlack + (1 - leftShare) • rightSlack) third)
        (invol first second) (invol first third) (invol second third)
      = leftShare • slackHollowThree (leftSlack first) (leftSlack second) (leftSlack third)
            (invol first second) (invol first third) (invol second third)
        + (1 - leftShare) • slackHollowThree (rightSlack first) (rightSlack second)
            (rightSlack third) (invol first second) (invol first third) (invol second third) := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [slackHollowThree, Pi.add_apply, Pi.smul_apply] <;> ring
  simp only [tripleSlackMargin]
  rw [hsplit]
  exact concave_lambdaMinMat _ _ hleftShare hrightShare

/-- **THE MARGIN IS CONCAVE in `nu`** as well: the change of variables is affine
and a convex combination of complements is the complement of the combination. -/
theorem concave_invariantLeverageMargin (invol : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) (leftPoint rightPoint : Fin size → ℝ)
    {leftShare rightShare : ℝ} (hleftShare : 0 ≤ leftShare) (hrightShare : 0 ≤ rightShare)
    (hshares : leftShare + rightShare = 1) :
    leftShare * tripleSlackMargin invol first second third (unitComplement leftPoint)
        + rightShare * tripleSlackMargin invol first second third (unitComplement rightPoint)
      ≤ tripleSlackMargin invol first second third
          (unitComplement (leftShare • leftPoint + rightShare • rightPoint)) := by
  obtain rfl : rightShare = 1 - leftShare := by linarith
  have haffine : unitComplement (leftShare • leftPoint + (1 - leftShare) • rightPoint)
      = leftShare • unitComplement leftPoint + (1 - leftShare) • unitComplement rightPoint := by
    funext index
    simp only [unitComplement_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [haffine]
  exact concave_tripleSlackMargin invol first second third _ _ hleftShare hrightShare hshares

/-! ## 5. The polytope and the covering sentence, in `nu` coordinates

The polytope is the hypersimplex `Delta(6,2) = {nu in [0,1]^6 : sum nu = 2}`,
whose fifteen vertices are the indicator vectors of the two-element subsets, and
the design locus is its relative interior in the cube.  Both are the shipped
`Gtz.slackSimplex` and `Gtz.heavySlackSimplex` reflected. -/

/-- The frame's own Gram, entrywise. -/
theorem frameGram_apply (frame : Matrix (Fin size) (Fin k) ℝ) (leftIndex rightIndex : Fin size) :
    (frame * frameᵀ) leftIndex rightIndex = frame leftIndex ⬝ᵥ frame rightIndex := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, dotProduct]

/-- Unit rows give the frame Gram a unit diagonal. -/
theorem frameGram_diagonal (frame : Matrix (Fin size) (Fin k) ℝ)
    (hunit : ∀ index, leverageOf (frame index) = 1) (index : Fin size) :
    (frame * frameᵀ) index index = 1 := by
  rw [frameGram_apply, dotProduct_self_eq_sum_sq]
  exact hunit index

theorem frameGram_comm (frame : Matrix (Fin size) (Fin k) ℝ) (leftIndex rightIndex : Fin size) :
    (frame * frameᵀ) leftIndex rightIndex = (frame * frameᵀ) rightIndex leftIndex := by
  rw [frameGram_apply, frameGram_apply, dotProduct_comm]

/-- **THE POLYTOPE `Delta`**: the hypersimplex `{nu in [0,1]^6 : sum nu = 2}`.  It
is `Gtz.slackSimplex` reflected. -/
def invariantLeverageHypersimplex : Set (Fin 6 → ℝ) :=
  {invariantLeverage | (∀ index, invariantLeverage index ∈ Set.Icc (0 : ℝ) 1)
    ∧ ∑ index, invariantLeverage index = 2}

/-- **THE DESIGN LOCUS**: the open part `{nu in (0,1)^6 : sum nu = 2}`.  `nu_c = 0`
is an atom of infinite leverage — a weight-zero limit no design occupies, matching
`Gtz.not_exists_design_of_weight_eq_zero` — and `nu_c = 1` is the light boundary
`ell_c = 1`, off which `Gtz.AllHeavy` holds and below which the shipped light-atom
deflation deletes the atom.  It is `Gtz.heavySlackSimplex` reflected. -/
def invariantLeverageDesignRegion : Set (Fin 6 → ℝ) :=
  {invariantLeverage | (∀ index, 0 < invariantLeverage index ∧ invariantLeverage index < 1)
    ∧ ∑ index, invariantLeverage index = 2}

theorem sum_unitComplement_six (values : Fin 6 → ℝ) :
    ∑ index, unitComplement values index = 6 - ∑ index, values index := by
  simp only [unitComplement_apply]
  rw [Fin.sum_univ_six, Fin.sum_univ_six]
  ring

/-- **THE POLYTOPES CORRESPOND.**  `Delta` is the shipped slack simplex reflected,
so the shipped convexity and compactness of the latter are the `nu`-side facts. -/
theorem unitComplement_mem_slackSimplex_iff (invariantLeverage : Fin 6 → ℝ) :
    unitComplement invariantLeverage ∈ slackSimplex
      ↔ invariantLeverage ∈ invariantLeverageHypersimplex := by
  simp only [slackSimplex, invariantLeverageHypersimplex, Set.mem_setOf_eq, Set.mem_Icc,
    unitComplement_apply, Fin.sum_univ_six]
  constructor
  · rintro ⟨hbounds, hsum⟩
    exact ⟨fun index => ⟨by linarith [(hbounds index).2], by linarith [(hbounds index).1]⟩,
      by linarith⟩
  · rintro ⟨hbounds, hsum⟩
    exact ⟨fun index => ⟨by linarith [(hbounds index).2], by linarith [(hbounds index).1]⟩,
      by linarith⟩

/-- **THE DESIGN LOCI CORRESPOND.** -/
theorem unitComplement_mem_heavySlackSimplex_iff (invariantLeverage : Fin 6 → ℝ) :
    unitComplement invariantLeverage ∈ heavySlackSimplex
      ↔ invariantLeverage ∈ invariantLeverageDesignRegion := by
  simp only [heavySlackSimplex, invariantLeverageDesignRegion, Set.mem_setOf_eq,
    unitComplement_apply, Fin.sum_univ_six]
  constructor
  · rintro ⟨hbounds, hsum⟩
    exact ⟨fun index => ⟨by linarith [(hbounds index).2], by linarith [(hbounds index).1]⟩,
      by linarith⟩
  · rintro ⟨hbounds, hsum⟩
    exact ⟨fun index => ⟨by linarith [(hbounds index).2], by linarith [(hbounds index).1]⟩,
      by linarith⟩

/-- The admissible uniform point is `nu == 1/3`, the mean. -/
theorem constantThird_mem_invariantLeverageHypersimplex :
    (fun _ : Fin 6 => (1 : ℝ) / 3) ∈ invariantLeverageHypersimplex := by
  refine ⟨fun _ => ⟨by norm_num, by norm_num⟩, ?_⟩
  rw [Fin.sum_univ_six]
  norm_num

/-- **AND `nu == 1/2` IS NOT A POINT OF THE POLYTOPE AT ALL**: its coordinates sum
to `3`, not `2`.  This is the structural reason the quarter conjecture refuted in
§6 was never equivalent to V6 — it asks for domination at an inadmissible
point. -/
theorem constantHalf_notMem_invariantLeverageHypersimplex :
    (fun _ : Fin 6 => (1 : ℝ) / 2) ∉ invariantLeverageHypersimplex := by
  rintro ⟨-, hsum⟩
  rw [Fin.sum_univ_six] at hsum
  norm_num at hsum

/-- **THE COVERING PREDICATE in `nu` coordinates**: the twenty cells of a Gram
cover a region. -/
def CoversInvariantLeverageRegion (gram : Matrix (Fin 6) (Fin 6) ℝ)
    (region : Set (Fin 6 → ℝ)) : Prop :=
  ∀ invariantLeverage ∈ region, ∃ first second third : Fin 6,
    first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ invariantLeverage ∈ invariantLeverageCell gram first second third

/-- The cell of a unit-norm tight frame's Gram is the shipped cell of its
correlation involution, reflected. -/
theorem mem_invariantLeverageCell_frameGram_iff (frame : Matrix (Fin 6) (Fin 3) ℝ)
    (hframe : IsUnitTightFrameSix frame) {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) (invariantLeverage : Fin 6 → ℝ) :
    invariantLeverage ∈ invariantLeverageCell (frame * frameᵀ) first second third
      ↔ unitComplement invariantLeverage
          ∈ tripleSlackCell (frameCorrelationInvolution frame) first second third := by
  rw [mem_invariantLeverageCell_iff_unitComplement_mem_tripleSlackCell (frame * frameᵀ)
    (frameGram_diagonal frame hframe.unit first) (frameGram_diagonal frame hframe.unit second)
    (frameGram_diagonal frame hframe.unit third) (frameGram_comm frame second first)
    (frameGram_comm frame third first) (frameGram_comm frame third second),
    tripleSlackCell_congr_offDiagonal
      (leftMatrix := frame * frameᵀ) (rightMatrix := frameCorrelationInvolution frame)
      (by rw [frameCorrelationInvolution_apply_of_ne frame hfirstSecond, frameGram_apply])
      (by rw [frameCorrelationInvolution_apply_of_ne frame hfirstThird, frameGram_apply])
      (by rw [frameCorrelationInvolution_apply_of_ne frame hsecondThird, frameGram_apply])]

/-- **THE TWO COVERING SENTENCES ARE ONE.** -/
theorem coversInvariantLeverageDesignRegion_iff_coversHeavySlackSimplex
    (frame : Matrix (Fin 6) (Fin 3) ℝ) (hframe : IsUnitTightFrameSix frame) :
    CoversInvariantLeverageRegion (frame * frameᵀ) invariantLeverageDesignRegion
      ↔ CoversSlackRegion (frameCorrelationInvolution frame) heavySlackSimplex := by
  constructor
  · intro hcovers slack hmember
    obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcell⟩ :=
      hcovers (unitComplement slack)
        ((unitComplement_mem_heavySlackSimplex_iff (unitComplement slack)).mp
          (by rw [unitComplement_unitComplement]; exact hmember))
    refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
    have hreflected := (mem_invariantLeverageCell_frameGram_iff frame hframe hfirstSecond
      hfirstThird hsecondThird (unitComplement slack)).mp hcell
    rwa [unitComplement_unitComplement] at hreflected
  · intro hcovers invariantLeverage hmember
    obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcell⟩ :=
      hcovers (unitComplement invariantLeverage)
        ((unitComplement_mem_heavySlackSimplex_iff invariantLeverage).mpr hmember)
    exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
      (mem_invariantLeverageCell_frameGram_iff frame hframe hfirstSecond hfirstThird
        hsecondThird invariantLeverage).mpr hcell⟩

/-- **THE COVERING EQUIVALENCE, in `nu` coordinates.**  Every uniform-share
all-heavy weighted `(6,3)` design has a dominating triple **iff** for every
unit-norm tight frame of six directions in `R^3` the twenty cells cover
`{nu in (0,1)^6 : sum nu = 2}`.  Both directions unconditional; obtained from the
shipped slack-coordinate equivalence by the reflection. -/
theorem gtzUniformShareSixThree_iff_forall_coversInvariantLeverageDesignRegion :
    GtzUniformShareSixThree ↔ ∀ frame : Matrix (Fin 6) (Fin 3) ℝ, IsUnitTightFrameSix frame →
      CoversInvariantLeverageRegion (frame * frameᵀ) invariantLeverageDesignRegion := by
  rw [gtzUniformShareSixThree_iff_forall_coversHeavySlackSimplex]
  constructor
  · intro hcovers frame hframe
    exact (coversInvariantLeverageDesignRegion_iff_coversHeavySlackSimplex frame hframe).mpr
      (hcovers frame hframe)
  · intro hcovers frame hframe
    exact (coversInvariantLeverageDesignRegion_iff_coversHeavySlackSimplex frame hframe).mp
      (hcovers frame hframe)

/-! ## 6. THE QUARTER CONJECTURE IS FALSE

The witness is the three-orthogonal-pair frame

  `u_0 = (0, 20/29, 21/29)`,   `u_1 = (0, -21/29, 20/29)`,
  `u_2 = (21/29, 0, 20/29)`,   `u_3 = (20/29, 0, -21/29)`,
  `u_4 = (4/5, 3/5, 0)`,       `u_5 = (-3/5, 4/5, 0)`,

with `u_0 ⟂ u_1`, `u_2 ⟂ u_3`, `u_4 ⟂ u_5` and the three plane normals
orthonormal, which is exactly what forces `sum_c u_c u_c^T = 2 I` — verified below
as an exact rational matrix identity, not a numeric estimate.

Every one of the twenty triples fails at the SAME clause: the determinant clause
of `Gtz.posSemidef_slackHollowThree_iff` at capacity `1/2`, which reads
`sigma_T - 4 P_T <= 1/4` on the squared correlations.  The tightest triple is
`{1,3,4}`, where `sigma - 4 P = 4663129/17682025`, exceeding `1/4` by
`970491/70728100`.  A float scan reports its least eigenvalue as `0.43610`; nothing
here depends on that number. -/

/-- **THE QUARTER WITNESS**, as a unit-row tight frame. -/
noncomputable def quarterFrame : Matrix (Fin 6) (Fin 3) ℝ :=
  Matrix.of ![![0, 20 / 29, 21 / 29], ![0, -21 / 29, 20 / 29], ![21 / 29, 0, 20 / 29],
    ![20 / 29, 0, -21 / 29], ![4 / 5, 3 / 5, 0], ![-3 / 5, 4 / 5, 0]]

/-- Every row is a unit vector: `20^2 + 21^2 = 29^2` and `3-4-5`. -/
theorem quarterFrame_unit (index : Fin 6) : leverageOf (quarterFrame index) = 1 := by
  fin_cases index <;> simp [quarterFrame, leverageOf, Fin.sum_univ_three] <;> norm_num

/-- **AND THE FRAME IS TIGHT AT LEVEL TWO, EXACTLY**: `sum_c u_c u_c^T = 2 I_3`. -/
theorem quarterFrame_tight :
    quarterFrameᵀ * quarterFrame = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [quarterFrame, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

theorem isUnitTightFrameSix_quarterFrame : IsUnitTightFrameSix quarterFrame where
  unit := quarterFrame_unit
  tight := quarterFrame_tight

/-- The witness's Gram, exactly.  Every entry is a rational with denominator
dividing `841 = 29^2` or `145 = 5 . 29`. -/
noncomputable def quarterGram : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of ![
    ![1, 0, 420 / 841, -441 / 841, 12 / 29, 16 / 29],
    ![0, 1, 400 / 841, -420 / 841, -63 / 145, -84 / 145],
    ![420 / 841, 400 / 841, 1, 0, 84 / 145, -63 / 145],
    ![-441 / 841, -420 / 841, 0, 1, 16 / 29, -12 / 29],
    ![12 / 29, -63 / 145, 84 / 145, 16 / 29, 1, 0],
    ![16 / 29, -84 / 145, -63 / 145, -12 / 29, 0, 1]]

theorem quarterFrame_mul_transpose : quarterFrame * quarterFrameᵀ = quarterGram := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [quarterFrame, quarterGram, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem quarterGram_comm (first second : Fin 6) :
    quarterGram first second = quarterGram second first := by
  rw [← quarterFrame_mul_transpose]
  exact frameGram_comm quarterFrame first second

theorem quarterGram_diagonal (index : Fin 6) : quarterGram index index = 1 := by
  rw [← quarterFrame_mul_transpose]
  exact frameGram_diagonal quarterFrame quarterFrame_unit index

theorem transpose_submatrix_quarterGram (first second third : Fin 6) :
    (quarterGram.submatrix ![first, second, third] ![first, second, third])ᵀ
      = quarterGram.submatrix ![first, second, third] ![first, second, third] := by
  ext rowIndex colIndex
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
  exact quarterGram_comm _ _

/-- The determinant clause at capacity `1/2` reads `sigma - 4 P <= 1/4`; violating
it kills the block. -/
private theorem notPosSemidef_half_of_sigma {edgeFirst edgeSecond edgeThird : ℝ}
    (hbig : 1 / 4 < edgeFirst ^ 2 + edgeSecond ^ 2 + edgeThird ^ 2
      - 4 * (edgeFirst * edgeSecond * edgeThird)) :
    ¬ (slackHollowThree (1 / 2) (1 / 2) (1 / 2) edgeFirst edgeSecond edgeThird).PosSemidef := by
  rw [posSemidef_slackHollowThree_iff]
  rintro ⟨-, -, -, -, -, -, hdet⟩
  rw [slackDeterminantThree] at hdet
  nlinarith [hdet, hbig]

/-- **ALL TWENTY TRIPLES OF THE WITNESS FAIL AT CAPACITY `1/2`.**  Twenty exact
rational determinant certificates, no floating point anywhere. -/
theorem not_mem_tripleSlackCell_quarterGram_half {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (fun _ => (1 : ℝ) / 2) ∉ tripleSlackCell quarterGram first second third := by
  rw [mem_tripleSlackCell_iff]
  fin_cases first <;> fin_cases second <;> fin_cases third <;>
    first
      | exact absurd rfl hfirstSecond
      | exact absurd rfl hfirstThird
      | exact absurd rfl hsecondThird
      | (refine notPosSemidef_half_of_sigma ?_; norm_num [quarterGram])

theorem diagonal_const_eq_smul_one (level : ℝ) :
    Matrix.diagonal (fun _ : Fin 3 => level) = level • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- **THE CONSTANT `nu == 1/2` IS IN NO CELL of the witness.** -/
theorem constantHalf_notMem_invariantLeverageCell_quarterGram {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (fun _ => (1 : ℝ) / 2) ∉ invariantLeverageCell quarterGram first second third := by
  rw [mem_invariantLeverageCell_iff_unitComplement_mem_tripleSlackCell quarterGram
    (quarterGram_diagonal first) (quarterGram_diagonal second) (quarterGram_diagonal third)
    (quarterGram_comm second first) (quarterGram_comm third first) (quarterGram_comm third second),
    show unitComplement (fun _ : Fin 6 => (1 : ℝ) / 2) = (fun _ : Fin 6 => (1 : ℝ) / 2) from by
      funext index; rw [unitComplement_apply]; norm_num]
  exact not_mem_tripleSlackCell_quarterGram_half hfirstSecond hfirstThird hsecondThird

/-- **NO TRIPLE OF THE WITNESS HAS LEAST EIGENVALUE AT LEAST `1/2`.** -/
theorem not_two_inv_le_lambdaMinMat_quarterGram {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    ¬ (1 : ℝ) / 2 ≤ lambdaMinMat (quarterGram.submatrix ![first, second, third]
        ![first, second, third]) := by
  intro hlambda
  refine constantHalf_notMem_invariantLeverageCell_quarterGram hfirstSecond hfirstThird
    hsecondThird ?_
  rw [mem_invariantLeverageCell_iff]
  have hpsd := (le_lambdaMinMat_iff_posSemidef_sub_smul_one _
    (transpose_submatrix_quarterGram first second third) (1 / 2)).mp hlambda
  have hshape : Matrix.diagonal
        (fun slot : Fin 3 => (fun _ : Fin 6 => (1 : ℝ) / 2) (![first, second, third] slot))
      = ((1 : ℝ) / 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := diagonal_const_eq_smul_one _
  rw [hshape]
  exact hpsd

theorem quarterFrame_tight_cast :
    quarterFrameᵀ * quarterFrame
      = (((6 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [show (((6 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = (2 : ℝ) from by norm_num]
  exact quarterFrame_tight

/-- **THE QUARTER WITNESS AS A DESIGN**: a genuine point of the equal-share
`(6,3)` stratum. -/
noncomputable def quarterDesign : WeightedDesign 6 3 :=
  tightFrameDesign quarterFrame (by norm_num) (by norm_num) quarterFrame_tight_cast

theorem isEqualShare_quarterDesign : IsEqualShare quarterDesign :=
  isEqualShare_tightFrameDesign quarterFrame (by norm_num) (by norm_num) quarterFrame_tight_cast
    quarterFrame_unit

theorem directionGram_quarterDesign (first second : Fin 6) :
    directionGram quarterDesign first second = quarterGram first second := by
  rw [quarterDesign, directionGram_tightFrameDesign quarterFrame (by norm_num) (by norm_num)
    quarterFrame_tight_cast quarterFrame_unit, ← quarterFrame_mul_transpose, frameGram_apply]

/-- **THE QUARTER CONJECTURE**: every equal-share `(6,3)` design has a triple of
distinct atoms whose direction Gram has least eigenvalue at least `1/2`. -/
def QuarterConjectureSixThree : Prop :=
  ∀ D : WeightedDesign 6 3, IsEqualShare D →
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ (1 : ℝ) / 2 ≤ lambdaMinMat ((directionGramMatrix D).submatrix
          ![first, second, third] ![first, second, third])

/-- **THE REFUTATION.**  `Gtz.quarterDesign` is on the equal-share stratum and no
triple of it reaches `1/2`. -/
theorem not_quarterConjectureSixThree : ¬ QuarterConjectureSixThree := by
  intro hclaim
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hlambda⟩ :=
    hclaim quarterDesign isEqualShare_quarterDesign
  refine not_two_inv_le_lambdaMinMat_quarterGram hfirstSecond hfirstThird hsecondThird ?_
  have hblock : (directionGramMatrix quarterDesign).submatrix ![first, second, third]
        ![first, second, third]
      = quarterGram.submatrix ![first, second, third] ![first, second, third] := by
    ext rowIndex colIndex
    simp only [Matrix.submatrix_apply]
    exact directionGram_quarterDesign _ _
  rwa [hblock] at hlambda

/-- **AND V6 SURVIVES ON THE WITNESS.**  U6 fires: the equal-share design built on
the quarter frame does have a dominating triple.  So the refutation is of the
QUARTER threshold `1/2`, not of the `(6,3)` covering. -/
theorem exists_dominating_triple_quarterDesign :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      Dominates quarterDesign {first, second, third} :=
  exists_dominating_triple_of_isEqualShare quarterDesign isEqualShare_quarterDesign

/-- **THE WITNESS SITS STRICTLY ABOVE THE QUARTER THEOREM'S LOWER REGION.**  The
triple `{0,2,5}` has all three edge weights at least `3969/21025`, so the
max-min edge weight of the witness exceeds `1/8` and the closed branch `m <= 1/8`
of the quarter theorem does not reach it.  (Exactly `3969/21025` is the max-min
value; only the lower bound is proved here, and it is the half that matters.) -/
theorem quarterGram_zero_two : quarterGram 0 2 = 420 / 841 := by simp [quarterGram]

theorem quarterGram_zero_five : quarterGram 0 5 = 16 / 29 := by simp [quarterGram]

theorem quarterGram_two_five : quarterGram 2 5 = -(63 / 145) := by
  simp [quarterGram]
  norm_num

theorem edgeWeightFloor_le_maxMinWeight_quarterDesign :
    3969 / 21025 ≤ maxMinWeight (edgeWeight quarterDesign) := by
  refine le_trans ?_
    (minTripleWeight_le_maxMinWeight (edgeWeight quarterDesign)
      (mem_distinctTriples (by decide) (by decide) (by decide) :
        ((0 : Fin 6), (2 : Fin 6), (5 : Fin 6)) ∈ distinctTriples))
  rw [minTripleWeight]
  refine le_min (le_min ?_ ?_) ?_
  · rw [edgeWeight, directionGram_quarterDesign, quarterGram_zero_two]; norm_num
  · rw [edgeWeight, directionGram_quarterDesign, quarterGram_zero_five]; norm_num
  · rw [edgeWeight, directionGram_quarterDesign, quarterGram_two_five]; norm_num

theorem one_eighth_lt_maxMinWeight_quarterDesign :
    1 / 8 < maxMinWeight (edgeWeight quarterDesign) :=
  lt_of_lt_of_le (by norm_num) edgeWeightFloor_le_maxMinWeight_quarterDesign

/-! ## 7. The boundary where the descent found margin exactly zero

The campaign's joint descent over (frame, `nu`) drove the V6 margin to `0` at a
point with three vanishing coordinates and the corresponding three directions
linearly dependent.  That point is COVERED, and this section says why: on
`nu|_T = 0` the block IS the Gram block, whose least eigenvalue is `>= 0` always
and `= 0` exactly when the three directions are dependent.  So the zero is a
covering with a singular certificate, not a counterexample. -/

/-- The cell reads exactly the three coordinates of its triple. -/
theorem invariantLeverageCell_congr {gram : Matrix (Fin size) (Fin size) ℝ}
    {first second third : Fin size} {leftPoint rightPoint : Fin size → ℝ}
    (hfirst : leftPoint first = rightPoint first)
    (hsecond : leftPoint second = rightPoint second)
    (hthird : leftPoint third = rightPoint third) :
    leftPoint ∈ invariantLeverageCell gram first second third
      ↔ rightPoint ∈ invariantLeverageCell gram first second third := by
  rw [mem_invariantLeverageCell_iff, mem_invariantLeverageCell_iff]
  have hdiag : Matrix.diagonal (fun slot => leftPoint (![first, second, third] slot))
      = Matrix.diagonal (fun slot => rightPoint (![first, second, third] slot)) := by
    congr 1
    funext slot
    fin_cases slot <;> simp [hfirst, hsecond, hthird]
  rw [hdiag]

/-- **A VANISHING TRIPLE IS ALWAYS COVERED.**  No hypothesis on the frame at all:
the block is the Gram block, and a Gram is positive semidefinite. -/
theorem mem_invariantLeverageCell_of_vanishing {rank : ℕ} (frame : Matrix (Fin size) (Fin rank) ℝ)
    {first second third : Fin size} {invariantLeverage : Fin size → ℝ}
    (hfirst : invariantLeverage first = 0) (hsecond : invariantLeverage second = 0)
    (hthird : invariantLeverage third = 0) :
    invariantLeverage ∈ invariantLeverageCell (frame * frameᵀ) first second third :=
  (invariantLeverageCell_congr (gram := frame * frameᵀ) (first := first) (second := second)
    (third := third) (leftPoint := (0 : Fin size → ℝ)) (rightPoint := invariantLeverage)
    hfirst.symm hsecond.symm hthird.symm).mp
    (zero_mem_invariantLeverageCell frame first second third)

/-- **AND ITS MARGIN IS THE GRAM'S LEAST EIGENVALUE**, hence zero exactly when the
three directions are linearly dependent.  This is the exact identification of the
campaign's reported infimum `0`. -/
theorem tripleSlackMargin_unitComplement_eq_lambdaMinMat_of_vanishing
    (gram : Matrix (Fin size) (Fin size) ℝ) {first second third : Fin size}
    (hunitFirst : gram first first = 1) (hunitSecond : gram second second = 1)
    (hunitThird : gram third third = 1)
    (hcommFirstSecond : gram second first = gram first second)
    (hcommFirstThird : gram third first = gram first third)
    (hcommSecondThird : gram third second = gram second third)
    {invariantLeverage : Fin size → ℝ} (hfirst : invariantLeverage first = 0)
    (hsecond : invariantLeverage second = 0) (hthird : invariantLeverage third = 0) :
    tripleSlackMargin gram first second third (unitComplement invariantLeverage)
      = lambdaMinMat (gram.submatrix ![first, second, third] ![first, second, third]) := by
  have hshape : slackHollowThree (unitComplement invariantLeverage first)
        (unitComplement invariantLeverage second) (unitComplement invariantLeverage third)
        (gram first second) (gram first third) (gram second third)
      = gram.submatrix ![first, second, third] ![first, second, third] := by
    rw [unitComplement_apply, unitComplement_apply, unitComplement_apply, hfirst, hsecond, hthird]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [slackHollowThree, hunitFirst, hunitSecond, hunitThird, hcommFirstSecond,
        hcommFirstThird, hcommSecondThird]
  rw [tripleSlackMargin, hshape]

/-! ## 8. Two exact walls on the interior-margin route -/

/-- **THE MEAN PINS THE MAXIMUM.**  Every point of the polytope has a coordinate
at least `1/3`. -/
theorem exists_third_le_of_sum_eq_two {invariantLeverage : Fin 6 → ℝ}
    (hsum : ∑ index, invariantLeverage index = 2) :
    ∃ index, 1 / 3 ≤ invariantLeverage index := by
  by_contra hsmall
  push Not at hsmall
  rw [Fin.sum_univ_six] at hsum
  linarith [hsmall 0, hsmall 1, hsmall 2, hsmall 3, hsmall 4, hsmall 5]

/-- **AND EQUALITY ONLY AT THE UNIFORM POINT.**  So `nu == 1/3` is the unique point
of the polytope whose maximum coordinate is `1/3`. -/
theorem eq_third_of_le_third_of_sum_eq_two {invariantLeverage : Fin 6 → ℝ}
    (hsum : ∑ index, invariantLeverage index = 2)
    (hcap : ∀ index, invariantLeverage index ≤ 1 / 3) (index : Fin 6) :
    invariantLeverage index = 1 / 3 := by
  rw [Fin.sum_univ_six] at hsum
  have hzero : invariantLeverage 0 = 1 / 3 := by
    linarith [hcap 0, hcap 1, hcap 2, hcap 3, hcap 4, hcap 5]
  have hone : invariantLeverage 1 = 1 / 3 := by
    linarith [hcap 0, hcap 1, hcap 2, hcap 3, hcap 4, hcap 5]
  have htwo : invariantLeverage 2 = 1 / 3 := by
    linarith [hcap 0, hcap 1, hcap 2, hcap 3, hcap 4, hcap 5]
  have hthree : invariantLeverage 3 = 1 / 3 := by
    linarith [hcap 0, hcap 1, hcap 2, hcap 3, hcap 4, hcap 5]
  have hfour : invariantLeverage 4 = 1 / 3 := by
    linarith [hcap 0, hcap 1, hcap 2, hcap 3, hcap 4, hcap 5]
  have hfive : invariantLeverage 5 = 1 / 3 := by
    linarith [hcap 0, hcap 1, hcap 2, hcap 3, hcap 4, hcap 5]
  fin_cases index <;>
    first
      | exact hzero
      | exact hone
      | exact htwo
      | exact hthree
      | exact hfour
      | exact hfive

/-- **SPECTRAL DOMINANCE IS SUFFICIENT.**  If the triple's Gram block has least
eigenvalue at least `level` and all three of ITS coordinates are at most `level`,
the point is in the cell.  This is the only cheap route from a
least-eigenvalue bound to a covering statement.

THE WALL: the frame-only bound available for every unit-norm tight frame of six
directions is exactly `1/3` (U6, `Gtz.exists_inv_three_le_lambdaMinMat_of_isEqualShare`,
attained at the tetrahedral tripod tie), and by
`Gtz.eq_third_of_le_third_of_sum_eq_two` the only point of the polytope all of
whose coordinates are at most `1/3` is the uniform one.  So this route with the
frame-only constant certifies a covering only where the triple's own three
coordinates happen to be small — never all of `Delta`, and never by a
frame-independent argument. -/
theorem mem_invariantLeverageCell_of_le_lambdaMinMat
    (gram : Matrix (Fin size) (Fin size) ℝ) {first second third : Fin size}
    (hsymmetric : (gram.submatrix ![first, second, third] ![first, second, third])ᵀ
      = gram.submatrix ![first, second, third] ![first, second, third]) {level : ℝ}
    (hlevel : level
      ≤ lambdaMinMat (gram.submatrix ![first, second, third] ![first, second, third]))
    {invariantLeverage : Fin size → ℝ} (hfirst : invariantLeverage first ≤ level)
    (hsecond : invariantLeverage second ≤ level) (hthird : invariantLeverage third ≤ level) :
    invariantLeverage ∈ invariantLeverageCell gram first second third := by
  rw [mem_invariantLeverageCell_iff]
  have hgap := (le_lambdaMinMat_iff_posSemidef_sub_smul_one _ hsymmetric level).mp hlevel
  have hsplit : gram.submatrix ![first, second, third] ![first, second, third]
        - Matrix.diagonal (fun slot => invariantLeverage (![first, second, third] slot))
      = (gram.submatrix ![first, second, third] ![first, second, third]
          - level • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        + Matrix.diagonal
            (fun slot => level - invariantLeverage (![first, second, third] slot)) := by
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [hsplit]
  refine hgap.add (Matrix.PosSemidef.diagonal ?_)
  intro slot
  fin_cases slot <;> simp <;> linarith

/-- **THE WALL ON THE `nu_a = 1` FACE.**  If a cell containing `a` covers a point
with `nu_a = 1` then `a`'s two correlations inside the triple VANISH.  So on that
face of the polytope only the four triples avoiding `a`, or triples in which `a` is
orthogonal to both partners, can cover — and by the shipped row law
`Gtz.sum_sq_directionGram_erase_six` an atom cannot be orthogonal to everything.
Any interior-margin argument must therefore be non-uniform in `nu` near that
face. -/
theorem gram_eq_zero_of_mem_invariantLeverageCell_of_eq_one
    (gram : Matrix (Fin size) (Fin size) ℝ) {first second third : Fin size}
    (hunitFirst : gram first first = 1) (hunitSecond : gram second second = 1)
    (hunitThird : gram third third = 1)
    (hcommFirstSecond : gram second first = gram first second)
    (hcommFirstThird : gram third first = gram first third)
    (hcommSecondThird : gram third second = gram second third)
    {invariantLeverage : Fin size → ℝ}
    (hmember : invariantLeverage ∈ invariantLeverageCell gram first second third)
    (hone : invariantLeverage first = 1) :
    gram first second = 0 ∧ gram first third = 0 := by
  rw [mem_invariantLeverageCell_iff_unitComplement_mem_tripleSlackCell gram hunitFirst hunitSecond
    hunitThird hcommFirstSecond hcommFirstThird hcommSecondThird, mem_tripleSlackCell_iff,
    posSemidef_slackHollowThree_iff] at hmember
  obtain ⟨-, -, -, hpairFirstSecond, hpairFirstThird, -, -⟩ := hmember
  rw [unitComplement_apply, unitComplement_apply, hone] at hpairFirstSecond
  rw [unitComplement_apply, unitComplement_apply, hone] at hpairFirstThird
  refine ⟨?_, ?_⟩
  · have hzero : gram first second * gram first second = 0 :=
      le_antisymm (by nlinarith [hpairFirstSecond]) (mul_self_nonneg _)
    rcases mul_eq_zero.mp hzero with hvanishes | hvanishes <;> exact hvanishes
  · have hzero : gram first third * gram first third = 0 :=
      le_antisymm (by nlinarith [hpairFirstThird]) (mul_self_nonneg _)
    rcases mul_eq_zero.mp hzero with hvanishes | hvanishes <;> exact hvanishes

/-- **THE EXACT REMAINING GAP**, in `nu` coordinates: the shipped band gate covers
every uniform-share all-heavy design whose invariant leverages are all at most
`9/25`, that being `1 - 16/25`.  The polytope reaches `nu_c = 1`, so the gap this
lane does not close is `9/25 -> 1`. -/
theorem exists_dominates_of_inv_leverage_le_nine_twentyfifths (D : WeightedDesign 6 3)
    (hshare : ∀ atomIndex, atomShare D atomIndex = 1 / 2) (hheavy : AllHeavy D)
    (hcap : ∀ atomIndex, (leverageOf (D.atom atomIndex))⁻¹ ≤ 9 / 25) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C := by
  refine exists_dominates_of_sixteen_twentyfifths_le_weightSlack D hshare hheavy
    fun atomIndex => ?_
  have hbound := hcap atomIndex
  rw [inv_leverage_eq_one_sub_weightSlack] at hbound
  linarith

/-! ## 9. KKM and KKMS are the wrong tool

The reason is the DIRECTION of the implication.  Knaster–Kuratowski–Mazurkiewicz
and Shapley's subset-indexed KKMS both DERIVE a nonempty intersection FROM a
covering-type hypothesis on the faces.  V6 asks us to PROVE the covering, so a KKM
theorem is not an available step; its contrapositive would only ever refute a
covering.  Secondarily, the domain is not the standard simplex: `Delta` is the
hypersimplex `Delta(6,2)`, which contains none of the standard simplex's vertices,
so the KKMS face hypothesis is not expressible in its standard form.

A SECOND ARGUMENT WAS TRIED AND IS WITHDRAWN.  The theorem below — the origin lies
in every cell — was offered as showing the KKMS conclusion vacuous.  It does not:
the origin has coordinate sum `0`, so it is not a point of `Delta`, and KKMS
asserts a common point INSIDE the simplex.  The header's NOT PROVED section records
the correction, including the observation that on the §6 witness the twenty cells
have empty intersection with `Delta`. -/

/-- **THE WHOLE FAMILY HAS A COMMON POINT IN THE `nu` CONE**, at the origin.  This
is NOT a vacuity argument against KKMS: the origin's coordinates sum to `0`, so it
is not a point of `Delta`, and the KKMS conclusion concerns a common point inside
the simplex.  See the header's NOT PROVED section. -/
theorem zero_mem_iInter_invariantLeverageCell {rank : ℕ}
    (frame : Matrix (Fin size) (Fin rank) ℝ) :
    (0 : Fin size → ℝ) ∈ ⋂ triple : Fin size × Fin size × Fin size,
      invariantLeverageCell (frame * frameᵀ) triple.1 triple.2.1 triple.2.2 := by
  simp only [Set.mem_iInter]
  intro triple
  exact zero_mem_invariantLeverageCell frame triple.1 triple.2.1 triple.2.2

end Gtz
