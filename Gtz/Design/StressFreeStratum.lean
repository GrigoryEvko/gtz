/-
# Branch (i) of the `(6,3)` stress trichotomy: the stress-free stratum

`Gtz.sixThree_stress_trichotomy` splits every `(6,3)` design by its stress
structure and its first branch is the STRESS-FREE stratum, where the six atom
matrices are linearly independent.  Since the space of symmetric `3x3` matrices
has dimension exactly six, on that stratum the atoms are a BASIS of it, and the
whole stratum is one six-by-six linear algebra problem.  This file lands four
things about it and one unconditional fact that all three branches share.

## The geometric identification of the branch

`stressFree_iff_no_conic_sixThree`: the six atom matrices are independent
exactly when NO nonzero quadratic form vanishes at all six directions — the six
points of the projective plane lie on no conic.  The bridge is the six-by-six
VERONESE GRID whose rows are the quadratic monomials of the atoms
(`veroneseGrid`); a stress is a left kernel vector of that grid and a conic is a
right kernel vector, so both conditions are `det /= 0`
(`stressFree_iff_veroneseGrid_det_ne_zero`).  That determinant is the criterion
an exact-rational sampler of the stratum checks, and it is why K4 — which is
never on a conic — lies in this branch.

## The stratum's gaps never vanish

On the stress-free stratum the gap matrix of a proper subset has coordinate
vector `(1 - t_c on C, -t_c off C)` in the atom basis, which is never zero
because the weights are strictly positive: `gap_ne_zero_of_stressFree`.  Hence a
weakly dominating subset of a stress-free design has STRICTLY positive trace
(`trace_gap_pos_of_dominates_of_stressFree`), a positive-semidefinite matrix of
zero trace being zero (`trace_pos_of_posSemidef_of_ne_zero`).

## The leverage-sum floor, and the trace lever it powers

`sq_rank_le_sum_leverage`: EVERY weighted design satisfies
`rank^2 <= sum_c |g_c|^2`, unconditionally and at every size.  It is Sedrakyan's
inequality against the shipped share ceiling `t_c |g_c|^2 <= 1` and the shipped
trace identity `sum_c t_c |g_c|^2 = rank`, and it is sharp — the scaled
orthonormal basis attains it.  Feeding it to the shipped subset double count
`Gtz.sum_powersetCard_sum_mem_eq_choose_mul_sum` gives the averaged trace of the
gap over the whole `rank`-subset layer, hence a subset whose gap has trace at
least `rank * (rank^2 - size) / size`.  That is POSITIVE exactly below
`size = rank^2`, so it bites at both open cells of the campaign — `3/2` at
`(6,3)` (`sixThree_exists_triple_three_halves_le_trace_gap`) and `6/7` at
`(7,3)` — and expires at `size = 9`.

The floor also settles the weaker leverage statement that the tie's own leverage
floor produces: at a tie every leverage is at least one and they cannot all be
one, since that would read the trace identity as `1 = rank`
(`size_lt_sum_leverage_of_leverage_floor`).  At `(6,3)` that says `> 6` where
the unconditional floor already says `>= 9`, so the tie hypothesis buys nothing
here; the statement is landed at general size because there the two are
incomparable.

## The isotropy criterion, and what it says about every tie

`posDef_three_of_trace_nonneg_of_two_mul_frobeniusNormSq_lt`: a symmetric `3x3`
matrix with nonnegative trace and `2 |M|_F^2 < (tr M)^2` is positive definite.
The proof is Cauchy-Schwarz in the Frobenius pairing against `u u^T - (|u|^2/3)
I`, whose squared norm is `(2/3) |u|^4` — no spectral theorem, no square root.
The criterion is sufficient and NOT necessary: it is exactly the contrapositive
of "least eigenvalue at most zero forces `(tr M)^2 <= 2 |M|_F^2` once the trace
is nonnegative", so it discharges the ISOTROPIC gaps and misses the strongly
anisotropic ones.  K4's star gap has spectrum `(5, 1/2, 1/2)` and fails it,
which is the honest measure of the region.

Against a `(6,3)` tie the criterion needs no trace hypothesis at all, because
the tie's leverage floor already gives every triple's gap a nonnegative trace.
So `two_mul_frobeniusNormSq_gap_of_isTie_sixThree` holds in ALL THREE branches:
EVERY gap matrix of a `(6,3)` tie is anisotropic, `(tr G_C)^2 <= 2 |G_C|_F^2`,
for all twenty triples.  Combined with the trace lever, some triple of a
`(6,3)` tie carries `tr G_C >= 3/2` and therefore `|G_C|_F^2 >= 9/8`.

## The third invariant

A `3x3` spectrum has three invariants and the two-moment chart reads two, so the
chart is incomplete by construction.  Against the shipped exact criterion
`Gtz.posDef_three_of_elementarySymmetric` the isotropy test is revealed to be a
pure SECOND-INVARIANT test: `|M|_F^2 = (tr M)^2 - 2 e2`, so its inequality is
`(tr M)^2 < 4 e2` and it never reads the determinant.  Two consequences land
here.  At a `(6,3)` tie leaf one is free on all twenty triples, so domination
collapses to `0 <= e2` and `0 < e3`, whence every triple of a tie has `e2 < 0`
or `e3 <= 0`.  And `no_two_invariant_domination_test` exhibits two gaps of ONE
stress-free primitive design with equal trace and equal second invariant whose
determinants are `5/4` and `-49/4`: the two-invariant chart is not lossy on K4,
it is BLIND there.

## The branch-(i) capstone and its residual

`NoStressResidual` names exactly what is left: a primitive stress-free tie ALL
of whose twenty gaps are anisotropic.  The isotropic region is discharged by
construction, so the residual is strictly smaller than the branch.
`sixThree_hasParallelPair_of_isTie_of_stressFree` is the capstone in the
campaign's shape.
-/
import Mathlib
import Gtz.Reduction.NoStressRigidity
import Gtz.Design.StratumEmptinessLedger
import Gtz.Design.PrimitiveTightClassification
import Gtz.Quantitative.CauchyBinetValueFloor
import Gtz.Quantitative.ExpectedCharPolynomial
import Gtz.Quantitative.SevenThreeMetricBound
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Reduction.HeavyTraceFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Part 1: the leverage-sum floor -/

/-- **THE LEVERAGE-SUM FLOOR.**  Every weighted design carries total raw leverage
at least the SQUARE of its rank, at every size and with no further hypothesis.

Two shipped facts drive it: the share ceiling `t_c |g_c|^2 <= 1`
(`Gtz.weighted_leverage_le_one`) and the trace identity
`sum_c t_c |g_c|^2 = rank` (`Gtz.sum_weighted_leverage`).  Writing `s_c` for the
share, `|g_c|^2 = s_c / t_c >= s_c^2 / t_c` because `s_c <= 1`, and Sedrakyan's
inequality sends `sum_c s_c^2 / t_c` below `(sum_c s_c)^2 / sum_c t_c = rank^2`.

The bound is SHARP: `rank` orthogonal atoms of squared length `rank` carrying
weight `1/rank` each attain it. -/
theorem sq_rank_le_sum_leverage (design : WeightedDesign size rank) :
    ((rank : ℝ)) ^ 2 ≤ ∑ atomIndex, leverageOf (design.atom atomIndex) := by
  classical
  have hweightPos : ∀ atomIndex, 0 < design.weight atomIndex := design.weight_pos
  have hshareSum : ∑ atomIndex, design.weight atomIndex * leverageOf (design.atom atomIndex)
      = (rank : ℝ) := sum_weighted_leverage design
  have hsedrakyan := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin size))
    (fun atomIndex => design.weight atomIndex * leverageOf (design.atom atomIndex))
    (fun atomIndex _ => hweightPos atomIndex)
  rw [hshareSum, design.weight_sum_one, div_one] at hsedrakyan
  refine hsedrakyan.trans (Finset.sum_le_sum fun atomIndex _ => ?_)
  have hpos := hweightPos atomIndex
  have hceiling := weighted_leverage_le_one design atomIndex
  have hleverage := leverageOf_nonneg (design.atom atomIndex)
  have hshareNonneg : 0 ≤ design.weight atomIndex * leverageOf (design.atom atomIndex) :=
    mul_nonneg hpos.le hleverage
  rw [div_le_iff₀ hpos]
  nlinarith [mul_nonneg hshareNonneg (sub_nonneg.mpr hceiling)]

/-- The floor at the hinge's own cell: nine, against six atoms. -/
theorem sixThree_nine_le_sum_leverage (design : WeightedDesign 6 3) :
    (9 : ℝ) ≤ ∑ atomIndex, leverageOf (design.atom atomIndex) := by
  have hfloor := sq_rank_le_sum_leverage design
  norm_num at hfloor
  exact hfloor

/-- **The tie's own leverage statement.**  Where a leverage FLOOR of one is
available per atom — at `(6,3)` this is the unconditional
`Gtz.leverage_one_le_of_isTie_sixThree` — the leverages cannot all equal one,
because the trace identity would then read `1 = rank`.  So the total leverage
strictly exceeds the SIZE.  At `(6,3)` this says `> 6`, which
`sixThree_nine_le_sum_leverage` already beats; at larger sizes the two bounds
are incomparable, which is why this is stated at general size. -/
theorem size_lt_sum_leverage_of_leverage_floor (design : WeightedDesign size rank)
    (hrank : 2 ≤ rank) (hfloor : ∀ atomIndex, 1 ≤ leverageOf (design.atom atomIndex)) :
    (size : ℝ) < ∑ atomIndex, leverageOf (design.atom atomIndex) := by
  classical
  have hheavyExists : ∃ atomIndex : Fin size, 1 < leverageOf (design.atom atomIndex) := by
    by_contra hallOne
    push Not at hallOne
    have hunit : ∀ atomIndex : Fin size, leverageOf (design.atom atomIndex) = 1 := fun atomIndex =>
      le_antisymm (hallOne atomIndex) (hfloor atomIndex)
    have hcollapse : ∑ atomIndex, design.weight atomIndex * leverageOf (design.atom atomIndex)
        = ∑ atomIndex, design.weight atomIndex :=
      Finset.sum_congr rfl fun atomIndex _ => by rw [hunit atomIndex, mul_one]
    rw [sum_weighted_leverage design, design.weight_sum_one] at hcollapse
    have hcast : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
    linarith
  obtain ⟨heavyIndex, hheavy⟩ := hheavyExists
  have hstrict : ∑ _atomIndex : Fin size, (1 : ℝ)
      < ∑ atomIndex, leverageOf (design.atom atomIndex) :=
    Finset.sum_lt_sum (fun atomIndex _ => hfloor atomIndex)
      ⟨heavyIndex, Finset.mem_univ heavyIndex, hheavy⟩
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hstrict

/-! ## Part 2: the trace lever on the subset layer -/

/-- **The averaged gap trace over the whole `rank`-subset layer.**  Every atom
lies in `C(size - 1, rank - 1)` of the `C(size, rank)` subsets, so the layer sum
of the gap traces reads off the total leverage.  Proved by consuming the shipped
double count `Gtz.sum_powersetCard_sum_mem_eq_choose_mul_sum`. -/
theorem sum_powersetCard_trace_gap (design : WeightedDesign size rank) (hrankPos : 0 < rank) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
        Matrix.trace (subsetSum design selected - 1)
      = (((size - 1).choose (rank - 1) : ℕ) : ℝ)
            * ∑ atomIndex, leverageOf (design.atom atomIndex)
          - ((size.choose rank : ℕ) : ℝ) * rank := by
  classical
  have hterm : ∀ selected : Finset (Fin size),
      Matrix.trace (subsetSum design selected - (1 : Matrix (Fin rank) (Fin rank) ℝ))
        = (∑ atomIndex ∈ selected, leverageOf (design.atom atomIndex)) - (rank : ℝ) := by
    intro selected
    rw [Matrix.trace_sub, trace_subsetSum, Matrix.trace_one, Fintype.card_fin]
  simp only [hterm]
  rw [Finset.sum_sub_distrib,
    sum_powersetCard_sum_mem_eq_choose_mul_sum rank hrankPos
      (fun atomIndex => leverageOf (design.atom atomIndex)),
    Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- **THE TRACE LEVER.**  Some `rank`-subset carries at least the layer-average
gap trace.  Stated multiplied through by the layer size so no division appears. -/
theorem exists_powersetCard_choose_mul_trace_gap_ge (design : WeightedDesign size rank)
    (hrankPos : 0 < rank) (hrankLe : rank ≤ size) :
    ∃ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      (((size - 1).choose (rank - 1) : ℕ) : ℝ)
            * (∑ atomIndex, leverageOf (design.atom atomIndex))
          - ((size.choose rank : ℕ) : ℝ) * rank
        ≤ ((size.choose rank : ℕ) : ℝ)
            * Matrix.trace (subsetSum design selected - 1) := by
  classical
  have hnonempty : ((Finset.univ : Finset (Fin size)).powersetCard rank).Nonempty := by
    refine Finset.powersetCard_nonempty.mpr ?_
    rw [Finset.card_univ, Fintype.card_fin]
    exact hrankLe
  have hlayerSum := sum_powersetCard_trace_gap design hrankPos
  refine Finset.exists_le_of_sum_le hnonempty ?_
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, hlayerSum]

/-- **The trace lever at the hinge.**  At `(6,3)` the layer has twenty triples,
each atom lies in ten of them, and the leverage floor is nine, so the averaged
gap trace is at least `(10 * 9 - 20 * 3) / 20 = 3/2`.  Unconditional: no tie, no
primitivity, no stress hypothesis. -/
theorem sixThree_exists_triple_three_halves_le_trace_gap (design : WeightedDesign 6 3) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (3 : ℝ) / 2 ≤ Matrix.trace (subsetSum design selected - 1) := by
  obtain ⟨selected, hmem, hbound⟩ :=
    exists_powersetCard_choose_mul_trace_gap_ge design (by norm_num) (by norm_num)
  refine ⟨selected, (Finset.mem_powersetCard.mp hmem).2, ?_⟩
  have hfloor := sixThree_nine_le_sum_leverage design
  have hthrough : (10 : ℝ) * (∑ atomIndex, leverageOf (design.atom atomIndex)) - 20 * 3
      ≤ 20 * Matrix.trace (subsetSum design selected - 1) := by
    have hleft : ((6 - 1 : ℕ).choose (3 - 1)) = 10 := by decide
    have hright : ((6 : ℕ).choose 3) = 20 := by decide
    rw [hleft, hright] at hbound
    push_cast at hbound
    linarith
  linarith

/-! ## Part 3: gaps of the stress-free stratum never vanish -/

/-- **The gap in atom coordinates.**  Parseval turns the identity into the
weight combination of the atoms, so the gap of a subset is the atom combination
with coefficient `1 - t_c` inside the subset and `-t_c` outside it. -/
theorem gap_eq_sum_indicator_sub_weight_smul (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    subsetSum design selected - 1
      = ∑ atomIndex,
          ((if atomIndex ∈ selected then (1 : ℝ) else 0) - design.weight atomIndex)
            • atomMatrix (design.atom atomIndex) := by
  classical
  have hsplit : ∀ atomIndex : Fin size,
      ((if atomIndex ∈ selected then (1 : ℝ) else 0) - design.weight atomIndex)
          • atomMatrix (design.atom atomIndex)
        = (if atomIndex ∈ selected then (1 : ℝ) else 0)
              • atomMatrix (design.atom atomIndex)
            - design.weight atomIndex • atomMatrix (design.atom atomIndex) :=
    fun atomIndex => sub_smul _ _ _
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, design.isParseval]
  congr 1
  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, subsetSum]

/-- **No gap vanishes on the stress-free stratum.**  A subset missing at least
one atom has a strictly negative coordinate there, and independence of the atom
matrices forbids the coordinate vector from being zero. -/
theorem gap_ne_zero_of_stressFree (design : WeightedDesign size rank)
    (hstressFree : ∀ stressCoeff : Fin size → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0)
    {selected : Finset (Fin size)} {outsideLabel : Fin size}
    (houtside : outsideLabel ∉ selected) :
    subsetSum design selected - 1 ≠ 0 := by
  classical
  intro hvanishes
  have hcoefficientZero := hstressFree
    (fun atomIndex => (if atomIndex ∈ selected then (1 : ℝ) else 0) - design.weight atomIndex)
    (by rw [← gap_eq_sum_indicator_sub_weight_smul]; exact hvanishes)
  have houtsideCoordinate := congrFun hcoefficientZero outsideLabel
  rw [if_neg houtside, zero_sub, Pi.zero_apply, neg_eq_zero] at houtsideCoordinate
  exact absurd houtsideCoordinate (design.weight_pos outsideLabel).ne'

/-- **A positive-semidefinite matrix of zero trace is zero**, so a nonzero one
has strictly positive trace.  The diagonal is nonnegative and sums to the trace,
so a vanishing trace kills it; the off-diagonal entries then die against the
two-support probes `e_i + s e_j`. -/
theorem trace_pos_of_posSemidef_of_ne_zero {dim : ℕ}
    {target : Matrix (Fin dim) (Fin dim) ℝ}
    (hposSemidef : target.PosSemidef) (hnonzero : target ≠ 0) :
    0 < Matrix.trace target := by
  classical
  rcases hposSemidef.trace_nonneg.lt_or_eq with hstrict | hvanishing
  · exact hstrict
  refine absurd ?_ hnonzero
  have hquadratic := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposSemidef).2
  have hdiagonalNonneg : ∀ rowIndex : Fin dim, 0 ≤ target rowIndex rowIndex := fun rowIndex =>
    hposSemidef.diag_nonneg (i := rowIndex)
  have hdiagonalZero : ∀ rowIndex : Fin dim, target rowIndex rowIndex = 0 := by
    intro rowIndex
    have htraceSum : ∑ index : Fin dim, target index index = 0 := hvanishing.symm
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun index _ => hdiagonalNonneg index)).mp htraceSum rowIndex (Finset.mem_univ rowIndex)
    exact this
  have hoffDiagonalZero : ∀ rowIndex colIndex : Fin dim, target rowIndex colIndex = 0 := by
    intro rowIndex colIndex
    by_cases hsame : rowIndex = colIndex
    · rw [hsame]; exact hdiagonalZero colIndex
    have hsymmetric : target colIndex rowIndex = target rowIndex colIndex := by
      have hentry := congrFun (congrFun hposSemidef.1 colIndex) rowIndex
      simpa using hentry.symm
    have hminor := hposSemidef.submatrix ![rowIndex, colIndex]
    have hdet := hminor.det_nonneg
    rw [Matrix.det_fin_two] at hdet
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
    rw [hdiagonalZero rowIndex, hdiagonalZero colIndex, hsymmetric] at hdet
    have hsquareZero : target rowIndex colIndex ^ 2 = 0 :=
      le_antisymm (by nlinarith [hdet]) (sq_nonneg _)
    exact pow_eq_zero_iff two_ne_zero |>.mp hsquareZero
  ext rowIndex colIndex
  rw [hoffDiagonalZero rowIndex colIndex, Matrix.zero_apply]

/-- **A weakly dominating subset of a stress-free design has strictly positive
gap trace.**  Its gap is positive semidefinite by domination and nonzero by
`gap_ne_zero_of_stressFree`. -/
theorem trace_gap_pos_of_dominates_of_stressFree (design : WeightedDesign size rank)
    (hstressFree : ∀ stressCoeff : Fin size → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0)
    {selected : Finset (Fin size)} {outsideLabel : Fin size}
    (houtside : outsideLabel ∉ selected) (hdominates : Dominates design selected) :
    0 < Matrix.trace (subsetSum design selected - 1) :=
  trace_pos_of_posSemidef_of_ne_zero hdominates
    (gap_ne_zero_of_stressFree design hstressFree houtside)

/-- **The dominating triple of a stress-free `(6,3)` design is strictly heavy**:
its three leverages sum above three.  A triple of six atoms always misses one. -/
theorem sixThree_three_lt_sum_leverage_of_dominates_of_stressFree
    (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hdominates : Dominates design selected) :
    (3 : ℝ) < ∑ atomLabel ∈ selected, leverageOf (design.atom atomLabel) := by
  classical
  have hproper : ∃ outsideLabel : Fin 6, outsideLabel ∉ selected := by
    by_contra hcovers
    push Not at hcovers
    have huniv : (Finset.univ : Finset (Fin 6)) ⊆ selected := fun label _ => hcovers label
    have hcount := Finset.card_le_card huniv
    rw [Finset.card_univ, Fintype.card_fin, hcard] at hcount
    omega
  obtain ⟨outsideLabel, houtside⟩ := hproper
  have htrace := trace_gap_pos_of_dominates_of_stressFree design hstressFree houtside hdominates
  rwa [Matrix.trace_sub, trace_subsetSum, Matrix.trace_one, Fintype.card_fin,
    sub_pos] at htrace

/-! ## Part 4: the Veronese grid and the conic identification of the branch -/

/-- The six quadratic monomials of a direction in three-space, in the order
`(x^2, y^2, z^2, xy, xz, yz)`: the affine Veronese coordinates that turn a
quadratic form's value into a dot product. -/
def veroneseCoords (direction : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![direction 0 * direction 0, direction 1 * direction 1, direction 2 * direction 2,
    direction 0 * direction 1, direction 0 * direction 2, direction 1 * direction 2]

/-- The six-by-six VERONESE GRID of a six-atom rank-three family: row `c` is the
Veronese coordinate vector of atom `c`.  Its LEFT kernel is the stress space and
its RIGHT kernel is the space of conics through the six directions, so both
sides of the stratum's identification are governed by one determinant. -/
def veroneseGrid (atomFamily : Fin 6 → Fin 3 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun atomIndex coordIndex => veroneseCoords (atomFamily atomIndex) coordIndex

/-- The six independent entries of a symmetric `3x3` matrix, weighted so that
pairing them against `veroneseCoords` evaluates the quadratic form. -/
def conicCoords (conic : Matrix (Fin 3) (Fin 3) ℝ) : Fin 6 → ℝ :=
  ![conic 0 0, conic 1 1, conic 2 2, 2 * conic 0 1, 2 * conic 0 2, 2 * conic 1 2]

/-- An entry of an atom combination is the coefficient-weighted sum of the
corresponding coordinate products. -/
theorem sum_smul_atomMatrix_apply (atomFamily : Fin 6 → Fin 3 → ℝ)
    (stressCoeff : Fin 6 → ℝ) (rowIndex colIndex : Fin 3) :
    (∑ atomIndex, stressCoeff atomIndex • atomMatrix (atomFamily atomIndex))
        rowIndex colIndex
      = ∑ atomIndex, stressCoeff atomIndex
          * (atomFamily atomIndex rowIndex * atomFamily atomIndex colIndex) := by
  simp [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply]

/-- A coordinate of a left multiplication by the Veronese grid. -/
theorem vecMul_veroneseGrid_apply (atomFamily : Fin 6 → Fin 3 → ℝ)
    (stressCoeff : Fin 6 → ℝ) (coordIndex : Fin 6) :
    (stressCoeff ᵥ* veroneseGrid atomFamily) coordIndex
      = ∑ atomIndex, stressCoeff atomIndex
          * veroneseCoords (atomFamily atomIndex) coordIndex := by
  simp [Matrix.vecMul, dotProduct, veroneseGrid]

/-- An atom combination vanishes exactly when its six Veronese coordinates do:
the entries `(0,0)`, `(1,1)`, `(2,2)`, `(0,1)`, `(0,2)`, `(1,2)` determine a
symmetric matrix. -/
theorem sum_smul_atomMatrix_eq_zero_iff_veronese (atomFamily : Fin 6 → Fin 3 → ℝ)
    (stressCoeff : Fin 6 → ℝ) :
    (∑ atomIndex, stressCoeff atomIndex • atomMatrix (atomFamily atomIndex)) = 0
      ↔ stressCoeff ᵥ* veroneseGrid atomFamily = 0 := by
  have hentry := sum_smul_atomMatrix_apply atomFamily stressCoeff
  have hcoord := vecMul_veroneseGrid_apply atomFamily stressCoeff
  constructor
  · intro hvanishes
    funext coordIndex
    have hzero : ∀ rowIndex colIndex : Fin 3,
        ∑ atomIndex, stressCoeff atomIndex
            * (atomFamily atomIndex rowIndex * atomFamily atomIndex colIndex) = 0 := by
      intro rowIndex colIndex
      rw [← hentry rowIndex colIndex, hvanishes, Matrix.zero_apply]
    rw [hcoord coordIndex, Pi.zero_apply]
    fin_cases coordIndex
    · simpa [veroneseCoords] using hzero 0 0
    · simpa [veroneseCoords] using hzero 1 1
    · simpa [veroneseCoords] using hzero 2 2
    · simpa [veroneseCoords] using hzero 0 1
    · simpa [veroneseCoords] using hzero 0 2
    · simpa [veroneseCoords] using hzero 1 2
  · intro hvanishes
    have hzero : ∀ coordIndex : Fin 6,
        ∑ atomIndex, stressCoeff atomIndex
            * veroneseCoords (atomFamily atomIndex) coordIndex = 0 := by
      intro coordIndex
      rw [← hcoord coordIndex, hvanishes, Pi.zero_apply]
    have hswap : ∀ rowIndex colIndex : Fin 3,
        ∑ atomIndex, stressCoeff atomIndex
            * (atomFamily atomIndex rowIndex * atomFamily atomIndex colIndex)
          = ∑ atomIndex, stressCoeff atomIndex
            * (atomFamily atomIndex colIndex * atomFamily atomIndex rowIndex) :=
      fun rowIndex colIndex => Finset.sum_congr rfl fun _ _ => by ring
    ext rowIndex colIndex
    rw [hentry rowIndex colIndex, Matrix.zero_apply]
    fin_cases rowIndex <;> fin_cases colIndex
    · simpa [veroneseCoords] using hzero 0
    · simpa [veroneseCoords] using hzero 3
    · simpa [veroneseCoords] using hzero 4
    · rw [hswap]; simpa [veroneseCoords] using hzero 3
    · simpa [veroneseCoords] using hzero 1
    · simpa [veroneseCoords] using hzero 5
    · rw [hswap]; simpa [veroneseCoords] using hzero 4
    · rw [hswap]; simpa [veroneseCoords] using hzero 5
    · simpa [veroneseCoords] using hzero 2

/-- The three transposition identities a symmetric conic supplies. -/
theorem conic_transposed_entries {conic : Matrix (Fin 3) (Fin 3) ℝ} (hsymm : conicᵀ = conic) :
    conic 1 0 = conic 0 1 ∧ conic 2 0 = conic 0 2 ∧ conic 2 1 = conic 1 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using (congrFun (congrFun hsymm 1) 0).symm
  · simpa using (congrFun (congrFun hsymm 2) 0).symm
  · simpa using (congrFun (congrFun hsymm 2) 1).symm

/-- A symmetric conic's value at a direction is the Veronese pairing. -/
theorem conic_form_eq_veronese_dotProduct {conic : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : conicᵀ = conic) (direction : Fin 3 → ℝ) :
    direction ⬝ᵥ (conic *ᵥ direction)
      = veroneseCoords direction ⬝ᵥ conicCoords conic := by
  obtain ⟨hten, htwenty, htwentyone⟩ := conic_transposed_entries hsymm
  have hleft : direction ⬝ᵥ (conic *ᵥ direction)
      = ∑ rowIndex : Fin 3, ∑ colIndex : Fin 3,
          conic rowIndex colIndex * direction rowIndex * direction colIndex := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hright : veroneseCoords direction ⬝ᵥ conicCoords conic
      = direction 0 * direction 0 * conic 0 0 + direction 1 * direction 1 * conic 1 1
        + direction 2 * direction 2 * conic 2 2 + 2 * direction 0 * direction 1 * conic 0 1
        + 2 * direction 0 * direction 2 * conic 0 2
        + 2 * direction 1 * direction 2 * conic 1 2 := by
    simp [veroneseCoords, conicCoords, dotProduct, Fin.sum_univ_six]
    ring
  rw [hleft, hright]
  simp only [Fin.sum_univ_three]
  rw [hten, htwenty, htwentyone]
  ring

/-- A symmetric conic vanishes exactly when its coordinate vector does. -/
theorem conicCoords_eq_zero_iff {conic : Matrix (Fin 3) (Fin 3) ℝ} (hsymm : conicᵀ = conic) :
    conicCoords conic = 0 ↔ conic = 0 := by
  obtain ⟨hten, htwenty, htwentyone⟩ := conic_transposed_entries hsymm
  constructor
  · intro hcoords
    have hentry : ∀ coordIndex : Fin 6, conicCoords conic coordIndex = 0 := fun coordIndex =>
      congrFun hcoords coordIndex
    have hzeroZero : conic 0 0 = 0 := by simpa [conicCoords] using hentry 0
    have honeOne : conic 1 1 = 0 := by simpa [conicCoords] using hentry 1
    have htwoTwo : conic 2 2 = 0 := by simpa [conicCoords] using hentry 2
    have hzeroOne : conic 0 1 = 0 := by
      have := hentry 3
      simp only [conicCoords] at this
      simp at this
      linarith
    have hzeroTwo : conic 0 2 = 0 := by
      have := hentry 4
      simp only [conicCoords] at this
      simp at this
      linarith
    have honeTwo : conic 1 2 = 0 := by
      have := hentry 5
      simp only [conicCoords] at this
      simp at this
      linarith
    have honeZero : conic 1 0 = 0 := by rw [hten, hzeroOne]
    have htwoZero : conic 2 0 = 0 := by rw [htwenty, hzeroTwo]
    have htwoOne : conic 2 1 = 0 := by rw [htwentyone, honeTwo]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp_all
  · intro hzero
    funext coordIndex
    rw [hzero]
    fin_cases coordIndex <;> simp [conicCoords]

/-- **The stress-free stratum is the nonvanishing of the Veronese
determinant.**  Branch (i)'s hypothesis is exactly triviality of the grid's left
kernel, which for a square matrix over a field is `det /= 0`. -/
theorem stressFree_iff_veroneseGrid_det_ne_zero (atomFamily : Fin 6 → Fin 3 → ℝ) :
    (∀ stressCoeff : Fin 6 → ℝ,
        (∑ atomIndex, stressCoeff atomIndex • atomMatrix (atomFamily atomIndex)) = 0 →
          stressCoeff = 0)
      ↔ (veroneseGrid atomFamily).det ≠ 0 := by
  constructor
  · intro hstressFree hdetZero
    obtain ⟨witness, hwitnessNe, hwitnessKernel⟩ :=
      Matrix.exists_vecMul_eq_zero_iff.mpr hdetZero
    exact hwitnessNe
      (hstressFree witness
        ((sum_smul_atomMatrix_eq_zero_iff_veronese atomFamily witness).mpr hwitnessKernel))
  · intro hdetNe stressCoeff hstress
    by_contra hstressNe
    exact hdetNe (Matrix.exists_vecMul_eq_zero_iff.mp
      ⟨stressCoeff, hstressNe,
        (sum_smul_atomMatrix_eq_zero_iff_veronese atomFamily stressCoeff).mp hstress⟩)

/-- **BRANCH (i) IS "THE SIX DIRECTIONS LIE ON NO CONIC".**  A stress is a
linear dependence among the atom matrices; a conic through the six directions is
a symmetric matrix orthogonal to all of them under the trace pairing.  The two
are the left and right kernels of one square Veronese grid, so each is trivial
exactly when the other is.  This is why K4, which is never on a conic, is a
branch-(i) design. -/
theorem stressFree_iff_no_conic_sixThree (atomFamily : Fin 6 → Fin 3 → ℝ) :
    (∀ stressCoeff : Fin 6 → ℝ,
        (∑ atomIndex, stressCoeff atomIndex • atomMatrix (atomFamily atomIndex)) = 0 →
          stressCoeff = 0)
      ↔ ∀ conic : Matrix (Fin 3) (Fin 3) ℝ, conicᵀ = conic →
          (∀ atomIndex, atomFamily atomIndex ⬝ᵥ (conic *ᵥ atomFamily atomIndex) = 0) →
            conic = 0 := by
  rw [stressFree_iff_veroneseGrid_det_ne_zero]
  have hbridge : ∀ conic : Matrix (Fin 3) (Fin 3) ℝ, conicᵀ = conic →
      ((∀ atomIndex, atomFamily atomIndex ⬝ᵥ (conic *ᵥ atomFamily atomIndex) = 0)
        ↔ veroneseGrid atomFamily *ᵥ conicCoords conic = 0) := by
    intro conic hsymm
    have hrow : ∀ atomIndex : Fin 6,
        (veroneseGrid atomFamily *ᵥ conicCoords conic) atomIndex
          = veroneseCoords (atomFamily atomIndex) ⬝ᵥ conicCoords conic := fun _ => rfl
    constructor
    · intro hvanishes
      funext atomIndex
      rw [Pi.zero_apply, hrow atomIndex, ← conic_form_eq_veronese_dotProduct hsymm]
      exact hvanishes atomIndex
    · intro hkernel atomIndex
      rw [conic_form_eq_veronese_dotProduct hsymm]
      have hentry := congrFun hkernel atomIndex
      rwa [hrow atomIndex, Pi.zero_apply] at hentry
  constructor
  · intro hdetNe conic hsymm hvanishes
    by_contra hconicNe
    have hcoordsNe : conicCoords conic ≠ 0 := fun hzero =>
      hconicNe ((conicCoords_eq_zero_iff hsymm).mp hzero)
    exact hdetNe (Matrix.exists_mulVec_eq_zero_iff.mp
      ⟨conicCoords conic, hcoordsNe, (hbridge conic hsymm).mp hvanishes⟩)
  · intro hnoConic hdetZero
    obtain ⟨witness, hwitnessNe, hwitnessKernel⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hdetZero
    refine hwitnessNe ?_
    set recovered : Matrix (Fin 3) (Fin 3) ℝ :=
      Matrix.of ![![witness 0, witness 3 / 2, witness 4 / 2],
                  ![witness 3 / 2, witness 1, witness 5 / 2],
                  ![witness 4 / 2, witness 5 / 2, witness 2]] with hrecovered
    have hsymm : recoveredᵀ = recovered := by
      ext rowIndex colIndex
      fin_cases rowIndex <;> fin_cases colIndex <;> simp [hrecovered]
    have hcoords : conicCoords recovered = witness := by
      funext coordIndex
      fin_cases coordIndex <;> simp [conicCoords, hrecovered] <;> ring
    have hzero : recovered = 0 :=
      hnoConic recovered hsymm ((hbridge recovered hsymm).mpr (by rw [hcoords]; exact hwitnessKernel))
    rw [← hcoords, hzero]
    funext coordIndex
    fin_cases coordIndex <;> simp [conicCoords]

/-! ## Part 4b: the weights of a stress-free design, explicitly -/

/-- **Parseval in Veronese coordinates.**  The weight vector left-multiplies the
Veronese grid to the coordinate vector of the identity. -/
theorem weight_vecMul_veroneseGrid (design : WeightedDesign 6 3) :
    design.weight ᵥ* veroneseGrid design.atom = ![1, 1, 1, 0, 0, 0] := by
  have hentry : ∀ rowIndex colIndex : Fin 3,
      (∑ atomIndex, design.weight atomIndex
          * (design.atom atomIndex rowIndex * design.atom atomIndex colIndex))
        = (1 : Matrix (Fin 3) (Fin 3) ℝ) rowIndex colIndex := by
    intro rowIndex colIndex
    rw [← sum_smul_atomMatrix_apply design.atom design.weight rowIndex colIndex,
      design.isParseval]
  funext coordIndex
  rw [vecMul_veroneseGrid_apply]
  fin_cases coordIndex
  · simpa [veroneseCoords, Matrix.one_apply] using hentry 0 0
  · simpa [veroneseCoords, Matrix.one_apply] using hentry 1 1
  · simpa [veroneseCoords, Matrix.one_apply] using hentry 2 2
  · simpa [veroneseCoords, Matrix.one_apply] using hentry 0 1
  · simpa [veroneseCoords, Matrix.one_apply] using hentry 0 2
  · simpa [veroneseCoords, Matrix.one_apply] using hentry 1 2

/-- **The weights of a stress-free design, in closed form.**  Branch (i)'s
rigidity is not merely uniqueness (`Gtz.sixThree_noStress_weights_determined`):
the weight vector IS the coordinate vector of the identity in the atom basis,
obtained from the six directions by ONE six-by-six inversion.  This is the
formula an exact-rational sampler of the stratum evaluates, and its positivity
is the only remaining design condition on the directions. -/
theorem weight_eq_veroneseGrid_inv_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) :
    design.weight = ![1, 1, 1, 0, 0, 0] ᵥ* (veroneseGrid design.atom)⁻¹ := by
  have hdetNe : (veroneseGrid design.atom).det ≠ 0 :=
    (stressFree_iff_veroneseGrid_det_ne_zero design.atom).mp hstressFree
  have hunit : IsUnit (veroneseGrid design.atom).det := isUnit_iff_ne_zero.mpr hdetNe
  have hcancel : (design.weight ᵥ* veroneseGrid design.atom)
        ᵥ* (veroneseGrid design.atom)⁻¹ = design.weight := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hunit, Matrix.vecMul_one]
  rw [← hcancel, weight_vecMul_veroneseGrid]

/-! ## Part 5: the isotropy domination criterion -/

/-- **The Frobenius Cauchy-Schwarz bound on a quadratic form.**  Pairing the
traceless part of a symmetric matrix against the traceless part of `u u^T` and
applying Cauchy-Schwarz in the nine entrywise coordinates: the deviation of the
Rayleigh numerator from its isotropic value is controlled by the matrix's
deviation from a multiple of the identity.  No spectral theorem, no square root
— the whole spectral content is the constant `2`, which is
`3 * |u u^T - (|u|^2/3) I|_F^2 / |u|^4`. -/
theorem sq_sum_entrywise_mul_le (leftEntry rightEntry : Fin 3 → Fin 3 → ℝ) :
    (∑ rowIndex : Fin 3, ∑ colIndex : Fin 3,
        leftEntry rowIndex colIndex * rightEntry rowIndex colIndex) ^ 2
      ≤ (∑ rowIndex : Fin 3, ∑ colIndex : Fin 3, leftEntry rowIndex colIndex ^ 2)
        * ∑ rowIndex : Fin 3, ∑ colIndex : Fin 3, rightEntry rowIndex colIndex ^ 2 := by
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun entry => leftEntry entry.1 entry.2) (fun entry => rightEntry entry.1 entry.2)
  simpa [Fintype.sum_prod_type] using hcauchy

set_option maxHeartbeats 1600000 in
theorem sq_three_mul_form_sub_trace_mul_normSq_le (target : Matrix (Fin 3) (Fin 3) ℝ)
    (probe : Fin 3 → ℝ) :
    (3 * (probe ⬝ᵥ (target *ᵥ probe)) - Matrix.trace target * (probe ⬝ᵥ probe)) ^ 2
      ≤ 2 * (3 * frobeniusNormSq target - Matrix.trace target ^ 2) * (probe ⬝ᵥ probe) ^ 2 := by
  classical
  have hform : probe ⬝ᵥ (target *ᵥ probe)
      = target 0 0 * probe 0 * probe 0 + target 0 1 * probe 0 * probe 1
        + target 0 2 * probe 0 * probe 2 + target 1 0 * probe 1 * probe 0
        + target 1 1 * probe 1 * probe 1 + target 1 2 * probe 1 * probe 2
        + target 2 0 * probe 2 * probe 0 + target 2 1 * probe 2 * probe 1
        + target 2 2 * probe 2 * probe 2 := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  have hnorm : probe ⬝ᵥ probe = probe 0 * probe 0 + probe 1 * probe 1 + probe 2 * probe 2 := by
    simp [dotProduct, Fin.sum_univ_three]
  have htrace : Matrix.trace target
      = target 0 0 + target 1 1 + target 2 2 := Matrix.trace_fin_three target
  have hfrobenius : frobeniusNormSq target
      = target 0 0 ^ 2 + target 0 1 ^ 2 + target 0 2 ^ 2
        + target 1 0 ^ 2 + target 1 1 ^ 2 + target 1 2 ^ 2
        + target 2 0 ^ 2 + target 2 1 ^ 2 + target 2 2 ^ 2 := by
    simp [frobeniusNormSq, frobeniusInner, Fin.sum_univ_three, sq]
    ring
  have hcauchy := sq_sum_entrywise_mul_le
    (fun rowIndex colIndex => 3 * target rowIndex colIndex
      - (Matrix.trace target) * (if rowIndex = colIndex then (1 : ℝ) else 0))
    (fun rowIndex colIndex => 3 * probe rowIndex * probe colIndex
      - (probe ⬝ᵥ probe) * (if rowIndex = colIndex then (1 : ℝ) else 0))
  simp only [Fin.sum_univ_three] at hcauchy
  norm_num [Fin.ext_iff] at hcauchy
  rw [hnorm, htrace] at hcauchy
  rw [hform, hnorm, htrace, hfrobenius]
  nlinarith [hcauchy]

/-- **THE ISOTROPY DOMINATION CRITERION.**  A symmetric `3x3` matrix with
nonnegative trace whose squared Frobenius norm is under half the squared trace
is POSITIVE DEFINITE.

Sufficient and not necessary, exactly: the converse statement is that a least
eigenvalue at most zero forces `(tr M)^2 <= 2 |M|_F^2` once the trace is
nonnegative, so the criterion is precisely blind to the anisotropic
positive-definite matrices.  K4's star gap, of spectrum `(5, 1/2, 1/2)`, has
`(tr)^2 = 36` against `2 |M|_F^2 = 51` and is missed. -/
theorem posDef_three_of_trace_nonneg_of_two_mul_frobeniusNormSq_lt
    {target : Matrix (Fin 3) (Fin 3) ℝ} (hsymm : targetᵀ = target)
    (htraceNonneg : 0 ≤ Matrix.trace target)
    (hisotropy : 2 * frobeniusNormSq target < Matrix.trace target ^ 2) :
    target.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq hsymm, ?_⟩
  intro probe hprobeNe
  rw [star_trivial]
  have hnormPos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
  have hkey := sq_three_mul_form_sub_trace_mul_normSq_le target probe
  by_contra hnotPos
  push Not at hnotPos
  have hdominates : (Matrix.trace target * (probe ⬝ᵥ probe)) ^ 2
      ≤ (3 * (probe ⬝ᵥ (target *ᵥ probe))
          - Matrix.trace target * (probe ⬝ᵥ probe)) ^ 2 := by
    nlinarith [hnotPos, htraceNonneg, hnormPos.le,
      mul_nonneg htraceNonneg hnormPos.le,
      sq_nonneg (probe ⬝ᵥ (target *ᵥ probe))]
  have hsqueeze : (Matrix.trace target * (probe ⬝ᵥ probe)) ^ 2
      ≤ 2 * (3 * frobeniusNormSq target - Matrix.trace target ^ 2)
          * (probe ⬝ᵥ probe) ^ 2 := hdominates.trans hkey
  nlinarith [hsqueeze, hnormPos, hisotropy, mul_pos hnormPos hnormPos]

/-- **THE THRESHOLD TWO IS SHARP, AND THE CHART IS EXHAUSTED.**  The diagonal
matrix `diag(1,1,0)` has trace two and squared Frobenius norm two, so it sits
exactly on the criterion's boundary `(tr M)^2 = 2 |M|_F^2` — and it is not
positive definite.  Hence the strict inequality cannot be relaxed and no larger
threshold is admissible.

More: among symmetric `3x3` matrices with a given trace and a given Frobenius
norm the least eigenvalue is smallest when the two LARGER eigenvalues coincide,
and this witness is that extremal shape at least eigenvalue zero.  So
`posDef_three_of_trace_nonneg_of_two_mul_frobeniusNormSq_lt` is the OPTIMAL
domination test readable from the trace and the Frobenius norm alone; any
sharper criterion must read a third invariant, and the determinant already makes
the test equivalent to domination itself. -/
theorem sq_trace_eq_two_mul_frobeniusNormSq_of_notPosDef_witness :
    Matrix.trace (Matrix.diagonal ![(1 : ℝ), 1, 0]) ^ 2
        = 2 * frobeniusNormSq (Matrix.diagonal ![(1 : ℝ), 1, 0])
      ∧ ¬ (Matrix.diagonal ![(1 : ℝ), 1, 0]).PosDef := by
  refine ⟨?_, ?_⟩
  · simp [frobeniusNormSq, frobeniusInner, Fin.sum_univ_three, Matrix.diagonal_apply]
    norm_num
  · intro hposDef
    have hprobeNe : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hentry := congrFun hzero 2
      simp at hentry
    have hprobe := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
    rw [star_trivial] at hprobe
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.diagonal_apply] at hprobe

/-! ## Part 6: what the criterion says about every `(6,3)` tie -/

/-- The gap matrix of a subset is symmetric. -/
theorem transpose_gap_eq (design : WeightedDesign size rank) (selected : Finset (Fin size)) :
    (subsetSum design selected - 1)ᵀ = subsetSum design selected - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun atomIndex _ =>
    transpose_eq_of_isHermitian (posSemidef_atomMatrix (design.atom atomIndex)).1

/-- **The tie's gaps all have nonnegative trace.**  The unconditional `(6,3)`
leverage floor puts every atom at leverage at least one, so a triple's leverages
sum to at least three. -/
theorem sixThree_trace_gap_nonneg_of_isTie (design : WeightedDesign 6 3) (htie : IsTie design)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    0 ≤ Matrix.trace (subsetSum design selected - 1) := by
  have hfloor := leverage_one_le_of_isTie_sixThree design htie
  have hsum : (3 : ℝ) ≤ ∑ atomLabel ∈ selected, leverageOf (design.atom atomLabel) := by
    have hconst : ∑ _atomLabel ∈ selected, (1 : ℝ) = 3 := by
      rw [Finset.sum_const, hcard]; norm_num
    rw [← hconst]
    exact Finset.sum_le_sum fun atomLabel _ => hfloor atomLabel
  rw [Matrix.trace_sub, trace_subsetSum, Matrix.trace_one, Fintype.card_fin]
  push_cast
  linarith

/-- **An isotropic gap at a `(6,3)` tie is positive definite**, with no trace
hypothesis: the tie's leverage floor supplies it. -/
theorem posDef_gap_of_isotropy_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hisotropy : 2 * frobeniusNormSq (subsetSum design selected - 1)
      < Matrix.trace (subsetSum design selected - 1) ^ 2) :
    (subsetSum design selected - 1).PosDef :=
  posDef_three_of_trace_nonneg_of_two_mul_frobeniusNormSq_lt
    (transpose_gap_eq design selected)
    (sixThree_trace_gap_nonneg_of_isTie design htie hcard) hisotropy

/-- **EVERY GAP MATRIX OF A `(6,3)` TIE IS ANISOTROPIC.**  All twenty triples, in
all three branches of the stress trichotomy, unconditionally: an isotropic gap
would dominate strictly, which a tie forbids. -/
theorem two_mul_frobeniusNormSq_gap_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    Matrix.trace (subsetSum design selected - 1) ^ 2
      ≤ 2 * frobeniusNormSq (subsetSum design selected - 1) := by
  by_contra hisotropy
  push Not at hisotropy
  exact htie.2 selected hcard
    (posDef_gap_of_isotropy_of_isTie_sixThree design htie hcard hisotropy)

/-- **The trace lever against the anisotropy law.**  Some triple of a `(6,3)` tie
carries gap trace at least `3/2`, hence squared Frobenius norm at least `9/8`. -/
theorem sixThree_exists_triple_frobenius_floor_of_isTie (design : WeightedDesign 6 3)
    (htie : IsTie design) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (3 : ℝ) / 2 ≤ Matrix.trace (subsetSum design selected - 1)
      ∧ (9 : ℝ) / 8 ≤ frobeniusNormSq (subsetSum design selected - 1) := by
  obtain ⟨selected, hcard, htrace⟩ := sixThree_exists_triple_three_halves_le_trace_gap design
  refine ⟨selected, hcard, htrace, ?_⟩
  have haniso := two_mul_frobeniusNormSq_gap_of_isTie_sixThree design htie hcard
  nlinarith [htrace, haniso]

/-! ## Part 6b: the third invariant, and what the two-moment chart really was

A `3x3` spectrum has three invariants and the trace-and-Frobenius chart reads
only two, so the chart cannot be complete.  The exact criterion in all three is
`Gtz.posDef_three_of_elementarySymmetric` (`Gtz/Quantitative/TripleCubicCriterion.lean`),
already in the tree and consumed here rather than rebuilt: a symmetric `3x3`
form with `0 <= e1`, `0 <= e2` and `0 < e3` is positive definite, proved from
the scalar cubic core with no leading-minor ordering.

Read against it, the two-moment criterion of Part 5 is exactly a SECOND-INVARIANT
test with the determinant traded away: for a symmetric form
`|M|_F^2 = (tr M)^2 - 2 e2`, so `2 |M|_F^2 < (tr M)^2` is literally
`(tr M)^2 < 4 e2`.  That is why it is sharp in its chart and why it misses K4 —
K4's star gap has `e1 = 6`, `e2 = 21/4`, `e3 = 5/4`, so `4 e2 = 21 < 36 = e1^2`
and the two-moment test fails, while all three invariants are positive and the
three-invariant test FIRES.  The third invariant is the whole gap. -/

/-- The second invariant of a `3x3` form: the sum of its three `2x2` principal
minors, the middle coefficient of the characteristic polynomial. -/
def secondInvariantThree (form : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (form 0 0 * form 1 1 - form 0 1 * form 1 0)
    + (form 0 0 * form 2 2 - form 0 2 * form 2 0)
    + (form 1 1 * form 2 2 - form 1 2 * form 2 1)

/-- **The Frobenius norm is the first two invariants.**  For a symmetric `3x3`
form, `|M|_F^2 = (tr M)^2 - 2 e2` — the Frobenius chart carries no information
beyond `e1` and `e2`. -/
theorem frobeniusNormSq_eq_sq_trace_sub_two_mul_secondInvariant
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymm : formᵀ = form) :
    frobeniusNormSq form = Matrix.trace form ^ 2 - 2 * secondInvariantThree form := by
  have hone : form 1 0 = form 0 1 := by simpa using (congrFun (congrFun hsymm 1) 0).symm
  have htwo : form 2 0 = form 0 2 := by simpa using (congrFun (congrFun hsymm 2) 0).symm
  have hthree : form 2 1 = form 1 2 := by simpa using (congrFun (congrFun hsymm 2) 1).symm
  rw [Matrix.trace_fin_three, secondInvariantThree]
  simp only [frobeniusNormSq, frobeniusInner, Fin.sum_univ_three]
  rw [hone, htwo, hthree]
  ring

/-- **The two-moment test IS the second-invariant test.**  Its inequality is
`(tr M)^2 < 4 e2`, so it never reads the determinant. -/
theorem two_mul_frobeniusNormSq_lt_sq_trace_iff {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : formᵀ = form) :
    2 * frobeniusNormSq form < Matrix.trace form ^ 2
      ↔ Matrix.trace form ^ 2 < 4 * secondInvariantThree form := by
  rw [frobeniusNormSq_eq_sq_trace_sub_two_mul_secondInvariant hsymm]
  constructor <;> intro hside <;> linarith

/-- **THE THREE-INVARIANT DOMINATION CRITERION**, at a gap matrix.  Consumes the
shipped `Gtz.posDef_three_of_elementarySymmetric`; the only work here is that the
gap is symmetric and that its trace is the sum of its diagonal. -/
theorem posDef_gap_of_positiveInvariants (design : WeightedDesign size 3)
    (selected : Finset (Fin size))
    (hfirst : 0 ≤ Matrix.trace (subsetSum design selected - 1))
    (hsecond : 0 ≤ secondInvariantThree (subsetSum design selected - 1))
    (hthird : 0 < (subsetSum design selected - 1).det) :
    (subsetSum design selected - 1).PosDef := by
  refine posDef_three_of_elementarySymmetric (transpose_gap_eq design selected) ?_ ?_ hthird
  · rwa [← Matrix.trace_fin_three]
  · exact hsecond

/-- **At a `(6,3)` tie the FIRST leaf is free, on all twenty triples.**  The tie's
leverage floor already gives every gap a nonnegative trace, so domination of a
triple collapses from three sign conditions to TWO: `0 <= e2` and `0 < e3`. -/
theorem posDef_gap_of_secondInvariant_of_det_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hsecond : 0 ≤ secondInvariantThree (subsetSum design selected - 1))
    (hthird : 0 < (subsetSum design selected - 1).det) :
    (subsetSum design selected - 1).PosDef :=
  posDef_gap_of_positiveInvariants design selected
    (sixThree_trace_gap_nonneg_of_isTie design htie hcard) hsecond hthird

/-- **EVERY TRIPLE OF A `(6,3)` TIE FAILS ONE OF THE TWO REMAINING LEAVES.**
Unconditional, in all three branches of the stress trichotomy: at a tie each of
the twenty gaps has a strictly negative second invariant or a nonpositive
determinant.  This supersedes the two-moment anisotropy law of Part 6, which in
the invariant chart says only `4 e2 <= e1^2`; the two combine to say that a
triple with `0 <= e2` has `e2 <= e1^2 / 4` AND nonpositive determinant. -/
theorem secondInvariant_neg_or_det_nonpos_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design) {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    secondInvariantThree (subsetSum design selected - 1) < 0
      ∨ (subsetSum design selected - 1).det ≤ 0 := by
  by_contra hboth
  push Not at hboth
  exact htie.2 selected hcard
    (posDef_gap_of_secondInvariant_of_det_of_isTie_sixThree design htie hcard
      hboth.1 hboth.2)

/-- The gap matrix of a dominating triple of the six-root design. -/
noncomputable def rootStarGap : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, 3 / 2, 3 / 2; 3 / 2, 2, 3 / 2; 3 / 2, 3 / 2, 2]

/-- The gap matrix of a NON-dominating triple of the same design, carrying the
same first two invariants as `rootStarGap`. -/
noncomputable def rootTwinGap : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, 3 / 2, 3 / 2; 3 / 2, 2, -(3 / 2); 3 / 2, -(3 / 2), 2]

/-- The matrix-literal entries, once. -/
theorem rootStarGap_symm : rootStarGapᵀ = rootStarGap := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [rootStarGap, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]

/-- **NO TWO-INVARIANT CRITERION CAN DECIDE DOMINATION.**  The two displayed
forms are the gap matrices of two triples of ONE design -- the six root
directions `(1,1,0), (1,-1,0), (1,0,1), (1,0,-1), (0,1,1), (0,1,-1)` scaled to
Parseval, which is K4's graphic design and is stress-free and primitive.  They
have the SAME trace, the SAME second invariant and therefore the same Frobenius
norm, and their determinants are `5/4` against `-49/4`: the first dominates
strictly, the second does not.

So the failure of the trace-and-Frobenius chart on K4 is not lossiness, it is
BLINDNESS -- any test reading only the first two invariants must return the same
verdict on a dominating triple and a non-dominating one of the same design.  The
sharpness witness of Part 5 shows the threshold cannot be raised; this shows no
threshold whatever would help. -/
theorem no_two_invariant_domination_test :
    Matrix.trace rootStarGap = Matrix.trace rootTwinGap
      ∧ secondInvariantThree rootStarGap = secondInvariantThree rootTwinGap
      ∧ frobeniusNormSq rootStarGap = frobeniusNormSq rootTwinGap
      ∧ rootStarGap.det = 5 / 4 ∧ rootTwinGap.det = -(49 / 4)
      ∧ rootStarGap.PosDef ∧ ¬ rootTwinGap.PosDef := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [rootStarGap, rootTwinGap, Matrix.trace_fin_three, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  · simp [secondInvariantThree, rootStarGap, rootTwinGap, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
    try norm_num
  · simp [frobeniusNormSq, frobeniusInner, Fin.sum_univ_three, rootStarGap, rootTwinGap,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
    try norm_num
  · simp [Matrix.det_fin_three, rootStarGap, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
    try norm_num
  · simp [Matrix.det_fin_three, rootTwinGap, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
    try norm_num
  · refine posDef_three_of_elementarySymmetric rootStarGap_symm ?_ ?_ ?_ <;>
      simp [Matrix.det_fin_three, rootStarGap, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.of_apply] <;>
      try norm_num
  · intro hposDef
    have hdet := hposDef.det_pos
    simp [Matrix.det_fin_three, rootTwinGap, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply] at hdet
    try norm_num at hdet

/-! ## Part 7: the branch-(i) capstone, modulo the named residual

A residual must never be phrased as `... -> IsTie design -> False`.  A tie has NO
strictly dominating subset, so it already implies the negation of every
strict-domination certificate; an obligation carrying `IsTie` alongside "no
certificate fires" therefore carries a hypothesis it gets for free and collapses
back onto the whole branch.  Everything below is phrased as a POSITIVE
domination claim that never mentions tightness, in the shape of
`Gtz.TwoPoleStratumSelection`; the tie form is a corollary.

Note the structural ceiling this exposes, which is not special to this branch:
every certificate of this kind concludes STRICT domination and a tie has none,
so at a tie every certificate fails and any certificate-shaped residual contains
the entire tie locus.  Closing branch (i) will need a selection argument or an
emptiness proof, not a sharper relaxation. -/

/-- **The isotropy certificate as a predicate on a triple.**  Its two clauses are
exactly the hypotheses of
`posDef_three_of_trace_nonneg_of_two_mul_frobeniusNormSq_lt`. -/
def HasIsotropicGap (design : WeightedDesign size 3) (selected : Finset (Fin size)) : Prop :=
  0 ≤ Matrix.trace (subsetSum design selected - 1)
    ∧ 2 * frobeniusNormSq (subsetSum design selected - 1)
        < Matrix.trace (subsetSum design selected - 1) ^ 2

/-- A triple carrying the isotropy certificate dominates STRICTLY.  No tie, no
stress, no primitivity — the design hypothesis is not used at all. -/
theorem posDef_gap_of_hasIsotropicGap (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hisotropic : HasIsotropicGap design selected) :
    (subsetSum design selected - 1).PosDef :=
  posDef_three_of_trace_nonneg_of_two_mul_frobeniusNormSq_lt
    (transpose_gap_eq design selected) hisotropic.1 hisotropic.2

/-- **The free-mass budget certificate**, verbatim the conclusion of
`Gtz.posDef_gap_of_freeMassBudget`: a certificate of strict domination for an
arbitrary subset of an arbitrary weighted design, proved by Cauchy-Schwarz in
the free-mass metric.  It mentions no stress, so it applies to the stress-free
stratum directly.  It stands here as a named hypothesis so that this module
carries no duplicate of it; every use below is discharged by that theorem. -/
def FreeMassBudgetCertificate (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (selected : Finset (Fin size)),
    (∑ c ∈ selected, (1 - design.weight c) • atomMatrix (design.atom c)).PosDef →
    (∑ c ∈ selectedᶜ, design.weight c
        * (design.atom c ⬝ᵥ ((∑ d ∈ selected,
            (1 - design.weight d) • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c))
      < 1) →
    (subsetSum design selected - 1).PosDef

/-- **A triple carries a certificate** when either the isotropy test above or
the free-mass budget of `Gtz.posDef_gap_of_freeMassBudget` fires on it. -/
def HasStrictCertificate (design : WeightedDesign size 3) (selected : Finset (Fin size)) :
    Prop :=
  HasIsotropicGap design selected
    ∨ ((∑ c ∈ selected, (1 - design.weight c) • atomMatrix (design.atom c)).PosDef
      ∧ ∑ c ∈ selectedᶜ, design.weight c
          * (design.atom c ⬝ᵥ ((∑ d ∈ selected,
              (1 - design.weight d) • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c))
        < 1)

/-- Either certificate produces a strictly dominating subset. -/
theorem posDef_gap_of_hasStrictCertificate (hbudget : FreeMassBudgetCertificate size 3)
    (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (hcertificate : HasStrictCertificate design selected) :
    (subsetSum design selected - 1).PosDef := by
  rcases hcertificate with hisotropic | ⟨hfreePosDef, hspend⟩
  · exact posDef_gap_of_hasIsotropicGap design selected hisotropic
  · exact hbudget design selected hfreePosDef hspend

/-- **THE NAMED RESIDUAL OF BRANCH (i): the CERTIFICATE-FREE region only.**  A
primitive stress-free design NONE of whose twenty triples carries either
certificate still has a strictly dominating triple.  A positive claim: `IsTie`
does not appear, so the obligation is not the branch goal in disguise.  The
certificate-carrying region is discharged unconditionally by
`posDef_gap_of_hasStrictCertificate`, so only its complement is assumed.

Measured in exact rationals on this stratum.  Across five adversarial samplers
of integer directions with rational rescalings, 145 admissible stress-free
`(6,3)` designs, every one strictly dominating; the isotropy test alone fired on
108 of them.  It does NOT reach the frontier: a float-guided descent with exact
re-derivation of its endpoints reached margin
`max_C lambda_min(S_C) - 1 = 0.0052373265088` at a stress-free primitive design
whose twenty gaps ALL failed the isotropy test, the best ratio
`(tr G_C)^2 / (2 |G_C|_F^2)` there being `0.99414` — approaching the threshold
one from below, exactly as the sharpness witness predicts, since the extremal
shape at ratio one is a gap of spectrum `(lambda, lambda, 0)`.  The isotropy
half therefore cannot be sharpened inside the trace-and-Frobenius chart.

The free-mass budget DOES reach that frontier: at the same two descent endpoints
it fires on four and on two triples respectively — including in both cases the
maximum-margin triple, at budget value `0.99189` at the tighter one — while the
isotropy test fires on none, and no triple carries both.  On this stratum the
two certificates are disjoint in the measured range, so the union is a strictly
larger discharged region than either.

BOTH certificates miss K4, the branch's calibration object.  Its four stars
dominate strictly with margin exactly `1/2`; the isotropy test reads
`(tr G)^2 = 36` against `2 |G|_F^2 = 51`, and the free-mass budget reads exactly
`6/5` on each star (and `7/5` on each of the other sixteen triples).  The two
failures have ONE cause: each certificate is a trace relaxation of an
operator-norm condition, and K4's pencils carry a doubled eigenvalue, so each
relaxation loses exactly the multiplicity factor two — the star's gap has
spectrum `(5, 1/2, 1/2)` and the star's free-mass-to-bound-mass pencil has
spectrum `(0, 3/5, 3/5)`, whose true maximum `3/5` is under the threshold while
its trace `6/5` is over.  Any certificate that is to catch K4 must read the
spectrum, not its first two moments — and `no_two_invariant_domination_test`
makes that unavoidable, not merely advisable.

WHY THE RESIDUAL IS NOT UPGRADED TO THE THREE-INVARIANT TEST.  That test is an
EQUIVALENCE, so "no triple carries it" is literally "no triple dominates
strictly" and the obligation would collapse onto the branch goal.  Its value is
not as a certificate but as a LEAF DECOMPOSITION, and the three leaves are
measured, exactly, on K4:

* leaf one, the trace, is FREE at a tie on all twenty triples
  (`posDef_gap_of_secondInvariant_of_det_of_isTie_sixThree`) and carries no
  selection power at K4 at all, where all twenty gaps have trace exactly six;
* leaf two, the second invariant, is MAXIMISED BY NON-DOMINATING TRIPLES at K4 —
  the four stars sit at `21/4` and twelve non-stars at `15/2` — so no maximise-
  or-average argument on it can select a dominating triple;
* leaf three, the determinant, is the only discriminating invariant there
  (`5/4` on a star against `-1` and `-49/4` off it) and its AVERAGE over the
  twenty triples is `-14/5`, strictly negative, so no averaging argument can
  supply it either.  The average obeys the exact identity
  `sum_C det G_C = det (sum_c A_c) - 4 sum_{c<d} (l_c l_d - g_cd^2) + 10 L - 20`,
  which at K4 reads `216 - 432 + 180 - 20 = -56`.

So all three averaging levers are refuted at the branch's own calibration point,
and the selection must be made by the determinant against a negative mean. -/
def NoStressResidual (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3,
    IsPrimitiveDesign design →
    (∀ stressCoeff : Fin size → ℝ,
        (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
          stressCoeff = 0) →
    (∀ selected : Finset (Fin size), selected.card = 3 →
        ¬ HasStrictCertificate design selected) →
    ∃ dominatingTriple : Finset (Fin size), dominatingTriple.card = 3
      ∧ (subsetSum design dominatingTriple - 1).PosDef

/-- **OB(i) AS A POSITIVE CLAIM: every primitive stress-free `(6,3)` design has a
strictly dominating triple**, given the residual.  The certificate arm is
unconditional; the certificate-free arm is the residual.  Nothing here assumes
tightness. -/
theorem sixThree_exists_posDef_triple_of_stressFree
    (hbudget : FreeMassBudgetCertificate 6 3) (hresidual : NoStressResidual 6)
    (design : WeightedDesign 6 3) (hprimitive : IsPrimitiveDesign design)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) :
    ∃ dominatingTriple : Finset (Fin 6), dominatingTriple.card = 3
      ∧ (subsetSum design dominatingTriple - 1).PosDef := by
  classical
  by_cases hcertified : ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ HasStrictCertificate design selected
  · obtain ⟨selected, hcard, hcertificate⟩ := hcertified
    exact ⟨selected, hcard, posDef_gap_of_hasStrictCertificate hbudget design selected
      hcertificate⟩
  · refine hresidual design hprimitive hstressFree fun selected hcard hcertificate => ?_
    exact hcertified ⟨selected, hcard, hcertificate⟩

/-- **No primitive stress-free `(6,3)` design is a tie**, given the residual: it
has a strictly dominating triple and a tie has none. -/
theorem sixThree_not_isTie_of_stressFree_of_primitive
    (hbudget : FreeMassBudgetCertificate 6 3) (hresidual : NoStressResidual 6)
    (design : WeightedDesign 6 3) (hprimitive : IsPrimitiveDesign design)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) :
    ¬ IsTie design := by
  intro htie
  obtain ⟨dominatingTriple, hcard, hposDef⟩ :=
    sixThree_exists_posDef_triple_of_stressFree hbudget hresidual design hprimitive
      hstressFree
  exact htie.2 dominatingTriple hcard hposDef

/-- **OB(i) in the hinge's vocabulary: a stress-free `(6,3)` tie carries a
parallel pair.**  Plugs directly into
`Gtz.hingeHoldsAtSize_six_three_iff_no_parallelFree_tie`. -/
theorem sixThree_hasParallelPair_of_isTie_of_stressFree
    (hbudget : FreeMassBudgetCertificate 6 3) (hresidual : NoStressResidual 6)
    (design : WeightedDesign 6 3) (htie : IsTie design)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) :
    HasParallelPair design := by
  by_contra hnoPair
  exact sixThree_not_isTie_of_stressFree_of_primitive hbudget hresidual design
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair) hstressFree htie

end Gtz
