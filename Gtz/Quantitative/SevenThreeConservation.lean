/-
# The `(7,3)` conservation laws: products, determinants, and the weighted aggregate

At a uniform share `s = 3/7` the direction Gram of a `(7,3)` design satisfies the
landed square law `Gamma * Gamma = (7/3) • Gamma`
(`Gtz.directionGramMatrix_sq_of_uniformShare`), so the hollow correlation matrix
`M = Gamma - 1` obeys the QUADRATIC LAW

  `M^2 = (1/3) M + (4/3) 1`,     hence     `M^3 = (13/9) M + (4/9) 1`.

Where the `(6,3)` stratum has an involution (`M^2 = 1`, supply chain ZERO), the
`(7,3)` stratum has a POSITIVE supply chain `sum_{c /= a,b} M_ac M_cb = (1/3) M_ab`
— and that single sign difference is the whole content of this file.  Reading the
quadratic law entrywise gives the row law `sum_d M_ad^2 = 4/3` and the supply
chain, and from those two the six conservation laws of the July 2026 pen campaign
follow by pure algebra, every constant exact:

| law | statement | value |
|---|---|---|
| C-P1 | `sum_{T ⊇ {a,b}} P_T` | `w_ab / 3 ≥ 0` |
| C-P2 | `sum_{T ∋ a} P_T` | `2/9` |
| C-P3 | `sum_T P_T` | `14/27` |
| C-D1 | `sum_{T ⊇ {e,f}} det Gamma[T]` | `(7/3)(1 - w_ef)` |
| C-D2 | `sum_{T ∋ a} det Gamma[T]` | `49/9` |
| C-5SET | `sum_{T ⊆ B_5} P_T` | `2/27 + w_ef / 3 > 0` |

with `w = gamma^2`, `P_T` the oriented triple product and `det Gamma[T] =
1 - sigma_T + 2 P_T`.  The 35-triple determinant total `343/27` is re-derived here
from the per-edge law (C-D1 summed over the 21 edges) and CROSS-CHECKS the landed
spectral route `Gtz.sum_det_principalMinors_directionGramMatrix_sevenThree`, which
knows nothing about triples; neither proof uses the other.

## The centerpiece: the weighted aggregate identity (C-AGG)

For EVERY uniform-share `(7,3)` design and EVERY slack vector `tau : Fin 7 → ℝ`,

  `sum_{|T| = 3} det(diag(tau_T) + M[T]) = e_3(tau) - (10/3) sum_c tau_c + 28/27`.

The right-hand side is frame-independent: the thirty-five determinant clauses of
the weighted triple criterion have a CONSTANT total on the whole stratum.  At
`tau ≡ 1` the identity returns the minor total `343/27`; at the criterion point
`tau ≡ 2/3` (the capacity of a leverage-3 atom) it returns `-112/27 < 0`; and on
the whole capacity polytope `{0 ≤ tau ≤ 1, sum tau = 14/3}` the total stays below
`-308/81`.  So the mean determinant clause is negative EVERYWHERE on the polytope:
no unweighted aggregation of determinant clauses can certify the `(7,3)` covering,
exactly as `Gtz.sum_involSlackDeterminant_six` kills it at `(6,3)`.  Unlike
`(6,3)`, the `+28/27` coherent residue of the positive supply chain SURVIVES in
the constant term, and its localisations (C-P1, C-5SET) are where the selection
information lives: EVERY five-set carries strictly positive coherent product mass.

The gradient reading (the GO-BEYOND of the brief): the aggregate's derivative
along `tau_c` is `e_2(tau off c) - 10/3`, whose `-10/3` is the six-set pair mass
`sum_{pairs off c} w = 14/3 - 4/3` (`Gtz.sum_pairSquare_sixSet_sevenThree`).  At a
constant slack `t` the aggregate is `35 t^3 - (70/3) t + 28/27`, stationary exactly
at `9 t^2 = 2` (`Gtz.constantSlackAggregate_stationary_iff_sevenThree`) — the
criterion point `2/3` is NOT the stationary point; the aggregate is already
climbing there.

## The starve-feed gate (C-PAIR)

The five determinant clauses through a pair total `Gtz.pairSumValueSeven`, which
at the criterion point reads `-8/27 - (4/3) w_ab < 0` — the pair-sum gate is as
vacuous at `(7,3)` as `Gtz.pairSumValue_nonpos` makes it at `(6,3)`, POSITIVE
SUPPLY NOTWITHSTANDING.  What survives is the reading relative to a failing hub:
a hub triple starved below the pair value feeds a nonnegative determinant clause
to one of the four other completions of its pair, and with the pairwise clauses
in hand that is a dominating triple (`Gtz.exists_dominates_of_starvedHub_sevenThree`,
the `(7,3)` twin of the landed `(6,3)` gate).

Everything below is stated on a design `D : WeightedDesign 7 3` under the single
hypothesis `huniform : ∀ c, atomShare D c = 3/7`; positivity of every leverage is
forced by it.  Non-vacuity of the hypothesis set is this workflow's module 1 (the
basis-plus-tetrapod witness); every statement here is an implication and does not
wait for it.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.MinorSumIdentities
import Gtz.Quantitative.WeightedTripleCriterion
import Gtz.Quantitative.WeightedBandCovering

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {m k size : ℕ}

/-! ## 0. Seven-slot enumeration helpers

The `Fin 7` twins of `Gtz.sum_eq_of_bijective_six` and `Gtz.ne_of_bijective_six`:
a bijective seven-tuple expands any sum over `Fin 7` into seven named terms and
carries all twenty-one pairwise distinctness facts. -/

/-- The seven-index expansion supplied by a bijective tuple. -/
theorem sum_eq_of_bijective_seven {valueType : Type*} [AddCommMonoid valueType]
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh])
    (summand : Fin 7 → valueType) :
    ∑ atomIndex, summand atomIndex
      = summand first + summand second + summand third + summand fourth + summand fifth
        + summand sixth + summand seventh := by
  rw [← Equiv.sum_comp (Equiv.ofBijective _ hbijective) summand, Fin.sum_univ_seven]
  simp only [Equiv.ofBijective_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four]
  rfl

/-- The pairwise distinctness facts a bijective seven-tuple carries. -/
theorem ne_of_bijective_seven {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh])
    {leftSlot rightSlot : Fin 7} (hslot : leftSlot ≠ rightSlot) :
    ![first, second, third, fourth, fifth, sixth, seventh] leftSlot
      ≠ ![first, second, third, fourth, fifth, sixth, seventh] rightSlot :=
  fun hvalue => hslot (hbijective.1 hvalue)

/-! ## 1. The correlation matrix of the `(7,3)`-uniform stratum

`Gtz.correlationInvolution` is `Gamma - 1` at every size; only at `m = 2k` is it
an involution.  Here it obeys the quadratic law instead. -/

/-- The correlation matrix is symmetric — no hypothesis, any size, any rank. -/
theorem correlationInvolution_comm (D : WeightedDesign m k) (rowIndex colIndex : Fin m) :
    correlationInvolution D colIndex rowIndex = correlationInvolution D rowIndex colIndex := by
  rw [correlationInvolution, Matrix.sub_apply, Matrix.sub_apply,
    show directionGramMatrix D colIndex rowIndex = directionGram D colIndex rowIndex from rfl,
    show directionGramMatrix D rowIndex colIndex = directionGram D rowIndex colIndex from rfl,
    directionGram_comm D colIndex rowIndex]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs with hforward hbackward hbackward
  · rfl
  · exact absurd hforward.symm hbackward
  · exact absurd hbackward.symm hforward
  · rfl

/-- At the constant slack `1` the determinant clause of a triple IS its elliptope
bracket `det Gamma[T]` — the scalar identity that makes the `tau ≡ 1` reading of
the aggregate the minor total. -/
theorem involSlackDeterminant_one_eq_hollowTripleBracket
    (invol : Matrix (Fin size) (Fin size) ℝ) {slack : Fin size → ℝ}
    (hone : ∀ index, slack index = 1) (first second third : Fin size) :
    involSlackDeterminant invol slack first second third
      = hollowTripleBracket invol first second third := by
  rw [involSlackDeterminant, slackDeterminantThree, hone first, hone second, hone third,
    hollowTripleBracket, elliptopeBracket]
  ring

/-- **THE QUADRATIC LAW.**  On the `(7,3)`-uniform stratum the hollow correlation
matrix satisfies `M^2 = (1/3) M + (4/3) 1` — the `(7,3)` replacement for the
`(6,3)` involution law `M^2 = 1`, read off the landed square law
`Gamma^2 = (7/3) Gamma`. -/
theorem correlationInvolution_sq_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    correlationInvolution D * correlationInvolution D
      = ((1 : ℝ) / 3) • correlationInvolution D
        + ((4 : ℝ) / 3) • (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
  have hsquare := directionGramMatrix_sq_of_uniformShare D huniform (by norm_num)
  rw [show ((3 : ℝ) / 7)⁻¹ = 7 / 3 by norm_num] at hsquare
  rw [correlationInvolution, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, hsquare]
  ext rowIndex colIndex
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  split_ifs <;> ring

/-- **THE CUBE LAW** `M^3 = (13/9) M + (4/9) 1`, one multiplication later.  Its
trace `28/9` is the total oriented product mass — see `sum_tripleProduct_sevenThree`. -/
theorem correlationInvolution_cube_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    correlationInvolution D * correlationInvolution D * correlationInvolution D
      = ((13 : ℝ) / 9) • correlationInvolution D
        + ((4 : ℝ) / 9) • (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
  rw [correlationInvolution_sq_sevenThree D huniform, Matrix.add_mul, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.one_mul, correlationInvolution_sq_sevenThree D huniform]
  ext rowIndex colIndex
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> ring

/-- The correlation matrix is hollow on the stratum, so its trace vanishes. -/
theorem trace_correlationInvolution_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    Matrix.trace (correlationInvolution D) = 0 := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  rw [Matrix.trace]
  exact Finset.sum_eq_zero fun atomIndex _ =>
    correlationInvolution_apply_self D (hpositive atomIndex)

/-- **THE FIRST TRACE LAW**: `tr M^2 = 28/3`, i.e. the twenty-one edge weights
total `14/3`. -/
theorem trace_sq_correlationInvolution_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    Matrix.trace (correlationInvolution D * correlationInvolution D) = 28 / 3 := by
  rw [correlationInvolution_sq_sevenThree D huniform, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, trace_correlationInvolution_sevenThree D huniform, Matrix.trace_one]
  simp only [smul_eq_mul, mul_zero, zero_add, Fintype.card_fin]
  norm_num

/-- **THE SECOND TRACE LAW**: `tr M^3 = 28/9` — six times the total oriented
product mass `14/27` of C-P3. -/
theorem trace_cube_correlationInvolution_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    Matrix.trace (correlationInvolution D * correlationInvolution D * correlationInvolution D)
      = 28 / 9 := by
  rw [correlationInvolution_cube_sevenThree D huniform, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, trace_correlationInvolution_sevenThree D huniform, Matrix.trace_one]
  simp only [smul_eq_mul, mul_zero, zero_add, Fintype.card_fin]
  norm_num

/-! ## 2. The row law and the supply chain, locally derived

The two entrywise readings of the quadratic law.  These are the file's own copies,
derived from the landed square law as the brief directs; the landed
`Gtz.sum_erase_edgeWeight_eq_of_atomShare_eq` is the same row law in
`Gtz.edgeWeight` coordinates. -/

/-- **THE ROW LAW**: `sum_d M_ad^2 = 4/3` at every atom — the diagonal of the
quadratic law.  The diagonal term of the sum is itself zero, so erased and
un-erased forms agree. -/
theorem sum_sq_correlationInvolution_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (vertex : Fin 7) :
    ∑ colIndex, correlationInvolution D vertex colIndex ^ 2 = 4 / 3 := by
  have hpositive : 0 < leverageOf (D.atom vertex) :=
    leverageOf_pos_of_atomShare_pos D (by rw [huniform vertex]; norm_num)
  have hentry := congrFun (congrFun (correlationInvolution_sq_sevenThree D huniform) vertex)
    vertex
  rw [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, correlationInvolution_apply_self D hpositive] at hentry
  have hsquares : ∑ colIndex, correlationInvolution D vertex colIndex
        * correlationInvolution D colIndex vertex
      = ∑ colIndex, correlationInvolution D vertex colIndex ^ 2 :=
    Finset.sum_congr rfl fun colIndex _ => by
      rw [correlationInvolution_comm D vertex colIndex, pow_two]
  rw [hsquares] at hentry
  rw [hentry]
  simp only [smul_eq_mul]
  norm_num

/-- **THE SUPPLY CHAIN**: `sum_c M_ac M_cb = (1/3) M_ab` for distinct `a, b` — the
off-diagonal of the quadratic law.  POSITIVE supply, where the `(6,3)` involution
has zero: this surviving third is the coherent residue behind every `(7,3)`
constant below. -/
theorem sum_correlationInvolution_chain_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {leftIndex rightIndex : Fin 7} (hdistinct : leftIndex ≠ rightIndex) :
    ∑ colIndex, correlationInvolution D leftIndex colIndex
        * correlationInvolution D colIndex rightIndex
      = (1 / 3 : ℝ) * correlationInvolution D leftIndex rightIndex := by
  have hentry := congrFun (congrFun (correlationInvolution_sq_sevenThree D huniform) leftIndex)
    rightIndex
  rw [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.one_apply_ne hdistinct] at hentry
  rw [hentry]
  simp only [smul_eq_mul, mul_zero, add_zero]

/-! ## 3. Product conservation: C-P1, C-P2, C-P3

The oriented triple products `P_T = M_ab M_ac M_bc`.  Every law is the supply
chain read one multiplication deeper; the localisation chain per-edge → per-atom
→ total carries the constants `w/3 → 2/9 → 14/27`. -/

/-- **(C-P1), un-erased**: the products through a pair total `w_ab / 3`, summed
over ALL seven third slots — the two degenerate terms vanish by hollowness. -/
theorem sum_tripleProduct_pair_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {leftIndex rightIndex : Fin 7} (hdistinct : leftIndex ≠ rightIndex) :
    ∑ colIndex, hollowTripleProduct (correlationInvolution D) leftIndex rightIndex colIndex
      = correlationInvolution D leftIndex rightIndex ^ 2 / 3 := by
  have hchain := sum_correlationInvolution_chain_sevenThree D huniform hdistinct
  have hpull : ∑ colIndex,
        hollowTripleProduct (correlationInvolution D) leftIndex rightIndex colIndex
      = correlationInvolution D leftIndex rightIndex
        * ∑ colIndex, correlationInvolution D leftIndex colIndex
            * correlationInvolution D colIndex rightIndex := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun colIndex _ => ?_
    rw [hollowTripleProduct, correlationInvolution_comm D colIndex rightIndex]
    ring
  rw [hpull, hchain]
  ring

/-- **(C-P1) PER-EDGE PRODUCT SUPPLY.**  The five triples through a pair carry
oriented product mass exactly `w_ab / 3` — positive supply, where the `(6,3)`
involution stratum has zero (`Gtz.IsHollowInvolution.sum_pairTripleProduct_eq_zero`). -/
theorem sum_sdiff_tripleProduct_pair_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {leftIndex rightIndex : Fin 7} (hdistinct : leftIndex ≠ rightIndex) :
    ∑ colIndex ∈ Finset.univ \ ({leftIndex, rightIndex} : Finset (Fin 7)),
        hollowTripleProduct (correlationInvolution D) leftIndex rightIndex colIndex
      = correlationInvolution D leftIndex rightIndex ^ 2 / 3 := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hsplit := Finset.sum_sdiff (f := fun colIndex =>
      hollowTripleProduct (correlationInvolution D) leftIndex rightIndex colIndex)
    (Finset.subset_univ ({leftIndex, rightIndex} : Finset (Fin 7)))
  have hpair : ∑ colIndex ∈ ({leftIndex, rightIndex} : Finset (Fin 7)),
      hollowTripleProduct (correlationInvolution D) leftIndex rightIndex colIndex = 0 := by
    rw [Finset.sum_pair hdistinct, hollowTripleProduct, hollowTripleProduct,
      correlationInvolution_apply_self D (hpositive leftIndex),
      correlationInvolution_apply_self D (hpositive rightIndex)]
    ring
  have hmaster := sum_tripleProduct_pair_sevenThree D huniform hdistinct
  linarith [hsplit, hpair, hmaster]

/-- The per-edge product supply is nonnegative — the sign half of (C-P1). -/
theorem sum_sdiff_tripleProduct_pair_nonneg_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {leftIndex rightIndex : Fin 7} (hdistinct : leftIndex ≠ rightIndex) :
    0 ≤ ∑ colIndex ∈ Finset.univ \ ({leftIndex, rightIndex} : Finset (Fin 7)),
        hollowTripleProduct (correlationInvolution D) leftIndex rightIndex colIndex := by
  rw [sum_sdiff_tripleProduct_pair_sevenThree D huniform hdistinct]
  positivity

/-- **(C-P2), ordered form**: `sum_{b,c} M_vb M_vc M_bc = 4/9` at every atom —
each unordered triple through the atom counted twice, so the unordered reading is
`2/9`.  The proof is one multiplication on the quadratic law: the inner sum is an
entry of `M^2`. -/
theorem sum_ordered_tripleProduct_vertex_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (vertex : Fin 7) :
    ∑ leftIndex, ∑ rightIndex,
        correlationInvolution D vertex leftIndex * correlationInvolution D vertex rightIndex
          * correlationInvolution D leftIndex rightIndex
      = 4 / 9 := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hrow := sum_sq_correlationInvolution_sevenThree D huniform vertex
  have hdiagSum : (∑ leftIndex, correlationInvolution D vertex leftIndex
      * (1 : Matrix (Fin 7) (Fin 7) ℝ) vertex leftIndex) = 0 := by
    refine Finset.sum_eq_zero fun leftIndex _ => ?_
    rcases eq_or_ne vertex leftIndex with hsame | hdiffer
    · rw [← hsame, correlationInvolution_apply_self D (hpositive vertex), zero_mul]
    · rw [Matrix.one_apply_ne hdiffer, mul_zero]
  have hinner : ∀ leftIndex : Fin 7,
      (∑ rightIndex, correlationInvolution D vertex leftIndex
        * correlationInvolution D vertex rightIndex
        * correlationInvolution D leftIndex rightIndex)
      = correlationInvolution D vertex leftIndex
        * (correlationInvolution D * correlationInvolution D) vertex leftIndex := by
    intro leftIndex
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun rightIndex _ => ?_
    rw [correlationInvolution_comm D rightIndex leftIndex]
    ring
  have hsplit : ∀ leftIndex : Fin 7,
      correlationInvolution D vertex leftIndex
        * (((1 : ℝ) / 3) • correlationInvolution D
            + ((4 : ℝ) / 3) • (1 : Matrix (Fin 7) (Fin 7) ℝ)) vertex leftIndex
      = (1 / 3 : ℝ) * correlationInvolution D vertex leftIndex ^ 2
        + (4 / 3 : ℝ) * (correlationInvolution D vertex leftIndex
            * (1 : Matrix (Fin 7) (Fin 7) ℝ) vertex leftIndex) := by
    intro leftIndex
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun leftIndex _ => hinner leftIndex,
    correlationInvolution_sq_sevenThree D huniform,
    Finset.sum_congr rfl fun leftIndex _ => hsplit leftIndex, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hrow, hdiagSum, mul_zero, add_zero]
  norm_num

/-- The row law expanded along a bijective tuple: seven squared correlations out
of any atom total `4/3`. -/
theorem sum_sq_row_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh])
    (vertex : Fin 7) :
    correlationInvolution D vertex first ^ 2 + correlationInvolution D vertex second ^ 2
      + correlationInvolution D vertex third ^ 2 + correlationInvolution D vertex fourth ^ 2
      + correlationInvolution D vertex fifth ^ 2 + correlationInvolution D vertex sixth ^ 2
      + correlationInvolution D vertex seventh ^ 2 = 4 / 3 := by
  have hrow := sum_sq_correlationInvolution_sevenThree D huniform vertex
  rwa [sum_eq_of_bijective_seven hbijective
    (fun colIndex => correlationInvolution D vertex colIndex ^ 2)] at hrow

/-- **(C-P1) expanded along a tuple**: the products through any distinct pair,
listed over the seven slots, total `w / 3`. -/
theorem sum_tripleProduct_throughPair_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh])
    {leftVertex rightVertex : Fin 7} (hdistinct : leftVertex ≠ rightVertex) :
    hollowTripleProduct (correlationInvolution D) leftVertex rightVertex first
      + hollowTripleProduct (correlationInvolution D) leftVertex rightVertex second
      + hollowTripleProduct (correlationInvolution D) leftVertex rightVertex third
      + hollowTripleProduct (correlationInvolution D) leftVertex rightVertex fourth
      + hollowTripleProduct (correlationInvolution D) leftVertex rightVertex fifth
      + hollowTripleProduct (correlationInvolution D) leftVertex rightVertex sixth
      + hollowTripleProduct (correlationInvolution D) leftVertex rightVertex seventh
      = correlationInvolution D leftVertex rightVertex ^ 2 / 3 := by
  have hmaster := sum_tripleProduct_pair_sevenThree D huniform hdistinct
  rwa [sum_eq_of_bijective_seven hbijective (fun colIndex =>
    hollowTripleProduct (correlationInvolution D) leftVertex rightVertex colIndex)] at hmaster

/-- **(C-P2) PER-ATOM PRODUCT MASS.**  The triples through any atom carry oriented
product mass `2/9`: the twenty-one pair-indexed products at a vertex, of which the
six meeting the vertex vanish, leaving the fifteen genuine triples.  The `(6,3)`
analogue is zero (`Gtz.IsHollowInvolution.sum_pairTripleProduct_six`). -/
theorem sum_pairTripleProduct_vertex_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh])
    (vertex : Fin 7) :
    hollowTripleProduct (correlationInvolution D) vertex first second
      + hollowTripleProduct (correlationInvolution D) vertex first third
      + hollowTripleProduct (correlationInvolution D) vertex first fourth
      + hollowTripleProduct (correlationInvolution D) vertex first fifth
      + hollowTripleProduct (correlationInvolution D) vertex first sixth
      + hollowTripleProduct (correlationInvolution D) vertex first seventh
      + hollowTripleProduct (correlationInvolution D) vertex second third
      + hollowTripleProduct (correlationInvolution D) vertex second fourth
      + hollowTripleProduct (correlationInvolution D) vertex second fifth
      + hollowTripleProduct (correlationInvolution D) vertex second sixth
      + hollowTripleProduct (correlationInvolution D) vertex second seventh
      + hollowTripleProduct (correlationInvolution D) vertex third fourth
      + hollowTripleProduct (correlationInvolution D) vertex third fifth
      + hollowTripleProduct (correlationInvolution D) vertex third sixth
      + hollowTripleProduct (correlationInvolution D) vertex third seventh
      + hollowTripleProduct (correlationInvolution D) vertex fourth fifth
      + hollowTripleProduct (correlationInvolution D) vertex fourth sixth
      + hollowTripleProduct (correlationInvolution D) vertex fourth seventh
      + hollowTripleProduct (correlationInvolution D) vertex fifth sixth
      + hollowTripleProduct (correlationInvolution D) vertex fifth seventh
      + hollowTripleProduct (correlationInvolution D) vertex sixth seventh
      = 2 / 9 := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hordered := sum_ordered_tripleProduct_vertex_sevenThree D huniform vertex
  have hdiag0 : correlationInvolution D first first = 0 :=
    correlationInvolution_apply_self D (hpositive first)
  have hdiag1 : correlationInvolution D second second = 0 :=
    correlationInvolution_apply_self D (hpositive second)
  have hdiag2 : correlationInvolution D third third = 0 :=
    correlationInvolution_apply_self D (hpositive third)
  have hdiag3 : correlationInvolution D fourth fourth = 0 :=
    correlationInvolution_apply_self D (hpositive fourth)
  have hdiag4 : correlationInvolution D fifth fifth = 0 :=
    correlationInvolution_apply_self D (hpositive fifth)
  have hdiag5 : correlationInvolution D sixth sixth = 0 :=
    correlationInvolution_apply_self D (hpositive sixth)
  have hdiag6 : correlationInvolution D seventh seventh = 0 :=
    correlationInvolution_apply_self D (hpositive seventh)
  have hcomm01 : correlationInvolution D second first = correlationInvolution D first second :=
    correlationInvolution_comm D first second
  have hcomm02 : correlationInvolution D third first = correlationInvolution D first third :=
    correlationInvolution_comm D first third
  have hcomm03 : correlationInvolution D fourth first = correlationInvolution D first fourth :=
    correlationInvolution_comm D first fourth
  have hcomm04 : correlationInvolution D fifth first = correlationInvolution D first fifth :=
    correlationInvolution_comm D first fifth
  have hcomm05 : correlationInvolution D sixth first = correlationInvolution D first sixth :=
    correlationInvolution_comm D first sixth
  have hcomm06 : correlationInvolution D seventh first = correlationInvolution D first seventh :=
    correlationInvolution_comm D first seventh
  have hcomm12 : correlationInvolution D third second = correlationInvolution D second third :=
    correlationInvolution_comm D second third
  have hcomm13 : correlationInvolution D fourth second = correlationInvolution D second fourth :=
    correlationInvolution_comm D second fourth
  have hcomm14 : correlationInvolution D fifth second = correlationInvolution D second fifth :=
    correlationInvolution_comm D second fifth
  have hcomm15 : correlationInvolution D sixth second = correlationInvolution D second sixth :=
    correlationInvolution_comm D second sixth
  have hcomm16 : correlationInvolution D seventh second = correlationInvolution D second seventh :=
    correlationInvolution_comm D second seventh
  have hcomm23 : correlationInvolution D fourth third = correlationInvolution D third fourth :=
    correlationInvolution_comm D third fourth
  have hcomm24 : correlationInvolution D fifth third = correlationInvolution D third fifth :=
    correlationInvolution_comm D third fifth
  have hcomm25 : correlationInvolution D sixth third = correlationInvolution D third sixth :=
    correlationInvolution_comm D third sixth
  have hcomm26 : correlationInvolution D seventh third = correlationInvolution D third seventh :=
    correlationInvolution_comm D third seventh
  have hcomm34 : correlationInvolution D fifth fourth = correlationInvolution D fourth fifth :=
    correlationInvolution_comm D fourth fifth
  have hcomm35 : correlationInvolution D sixth fourth = correlationInvolution D fourth sixth :=
    correlationInvolution_comm D fourth sixth
  have hcomm36 : correlationInvolution D seventh fourth = correlationInvolution D fourth seventh :=
    correlationInvolution_comm D fourth seventh
  have hcomm45 : correlationInvolution D sixth fifth = correlationInvolution D fifth sixth :=
    correlationInvolution_comm D fifth sixth
  have hcomm46 : correlationInvolution D seventh fifth = correlationInvolution D fifth seventh :=
    correlationInvolution_comm D fifth seventh
  have hcomm56 : correlationInvolution D seventh sixth = correlationInvolution D sixth seventh :=
    correlationInvolution_comm D sixth seventh
  simp only [sum_eq_of_bijective_seven hbijective, hdiag0, hdiag1, hdiag2, hdiag3, hdiag4,
    hdiag5, hdiag6, hcomm01, hcomm02, hcomm03, hcomm04, hcomm05, hcomm06, hcomm12, hcomm13,
    hcomm14, hcomm15, hcomm16, hcomm23, hcomm24, hcomm25, hcomm26, hcomm34, hcomm35, hcomm36,
    hcomm45, hcomm46, hcomm56, mul_zero, add_zero, zero_add] at hordered
  simp only [hollowTripleProduct]
  linarith [hordered]

/-- **(C-P3) THE TOTAL PRODUCT MASS.**  The thirty-five oriented triple products
of a uniform-share `(7,3)` design total `14/27` — one sixth of `tr M^3 = 28/9`,
and the constant that survives as the `+28/27` of the aggregate identity.  The
`(6,3)` total is zero (`Gtz.IsHollowInvolution.sum_tripleProduct_six`); the
`(7,3)` stratum is globally coherent. -/
theorem sum_tripleProduct_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh]) :
    hollowTripleProduct (correlationInvolution D) first second third
      + hollowTripleProduct (correlationInvolution D) first second fourth
      + hollowTripleProduct (correlationInvolution D) first second fifth
      + hollowTripleProduct (correlationInvolution D) first second sixth
      + hollowTripleProduct (correlationInvolution D) first second seventh
      + hollowTripleProduct (correlationInvolution D) first third fourth
      + hollowTripleProduct (correlationInvolution D) first third fifth
      + hollowTripleProduct (correlationInvolution D) first third sixth
      + hollowTripleProduct (correlationInvolution D) first third seventh
      + hollowTripleProduct (correlationInvolution D) first fourth fifth
      + hollowTripleProduct (correlationInvolution D) first fourth sixth
      + hollowTripleProduct (correlationInvolution D) first fourth seventh
      + hollowTripleProduct (correlationInvolution D) first fifth sixth
      + hollowTripleProduct (correlationInvolution D) first fifth seventh
      + hollowTripleProduct (correlationInvolution D) first sixth seventh
      + hollowTripleProduct (correlationInvolution D) second third fourth
      + hollowTripleProduct (correlationInvolution D) second third fifth
      + hollowTripleProduct (correlationInvolution D) second third sixth
      + hollowTripleProduct (correlationInvolution D) second third seventh
      + hollowTripleProduct (correlationInvolution D) second fourth fifth
      + hollowTripleProduct (correlationInvolution D) second fourth sixth
      + hollowTripleProduct (correlationInvolution D) second fourth seventh
      + hollowTripleProduct (correlationInvolution D) second fifth sixth
      + hollowTripleProduct (correlationInvolution D) second fifth seventh
      + hollowTripleProduct (correlationInvolution D) second sixth seventh
      + hollowTripleProduct (correlationInvolution D) third fourth fifth
      + hollowTripleProduct (correlationInvolution D) third fourth sixth
      + hollowTripleProduct (correlationInvolution D) third fourth seventh
      + hollowTripleProduct (correlationInvolution D) third fifth sixth
      + hollowTripleProduct (correlationInvolution D) third fifth seventh
      + hollowTripleProduct (correlationInvolution D) third sixth seventh
      + hollowTripleProduct (correlationInvolution D) fourth fifth sixth
      + hollowTripleProduct (correlationInvolution D) fourth fifth seventh
      + hollowTripleProduct (correlationInvolution D) fourth sixth seventh
      + hollowTripleProduct (correlationInvolution D) fifth sixth seventh
      = 14 / 27 := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hdiagAll : ∀ atomIndex : Fin 7, correlationInvolution D atomIndex atomIndex = 0 :=
    fun atomIndex => correlationInvolution_apply_self D (hpositive atomIndex)
  have hcommAll : ∀ rowIndex colIndex : Fin 7,
      correlationInvolution D colIndex rowIndex = correlationInvolution D rowIndex colIndex :=
    correlationInvolution_comm D
  have hvertex0 := sum_pairTripleProduct_vertex_sevenThree D huniform hbijective first
  have hvertex1 := sum_pairTripleProduct_vertex_sevenThree D huniform hbijective second
  have hvertex2 := sum_pairTripleProduct_vertex_sevenThree D huniform hbijective third
  have hvertex3 := sum_pairTripleProduct_vertex_sevenThree D huniform hbijective fourth
  have hvertex4 := sum_pairTripleProduct_vertex_sevenThree D huniform hbijective fifth
  have hvertex5 := sum_pairTripleProduct_vertex_sevenThree D huniform hbijective sixth
  have hvertex6 := sum_pairTripleProduct_vertex_sevenThree D huniform hbijective seventh
  simp only [hollowTripleProduct, hdiagAll, hcommAll first second, hcommAll first third,
    hcommAll first fourth, hcommAll first fifth, hcommAll first sixth, hcommAll first seventh,
    hcommAll second third, hcommAll second fourth, hcommAll second fifth,
    hcommAll second sixth, hcommAll second seventh, hcommAll third fourth,
    hcommAll third fifth, hcommAll third sixth, hcommAll third seventh,
    hcommAll fourth fifth, hcommAll fourth sixth, hcommAll fourth seventh,
    hcommAll fifth sixth, hcommAll fifth seventh, hcommAll sixth seventh, mul_zero, zero_mul,
    add_zero, zero_add]
    at hvertex0 hvertex1 hvertex2 hvertex3 hvertex4 hvertex5 hvertex6 ⊢
  linarith [hvertex0, hvertex1, hvertex2, hvertex3, hvertex4, hvertex5, hvertex6]

/-! ## 4. The pair-mass laws: the sigma side of the ledger

Inclusion–exclusion on the row law.  The six-set mass `10/3` is exactly the
`-10/3` of the aggregate's gradient `e_2(tau off c) - 10/3`, and the five-set
mass `2 + w` is the trace half of the pen's five-block law
`tr M[B_5]^2 = 4 + 2 w_ef`. -/

/-- **THE TOTAL PAIR MASS IS `14/3`**: the twenty-one edge weights of the
`(7,3)`-uniform stratum, seven row laws counted twice over.  This is the
entrywise reading of `tr M^2 = 28/3`. -/
theorem sum_pairSquare_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh]) :
    correlationInvolution D first second ^ 2 + correlationInvolution D first third ^ 2
      + correlationInvolution D first fourth ^ 2 + correlationInvolution D first fifth ^ 2
      + correlationInvolution D first sixth ^ 2 + correlationInvolution D first seventh ^ 2
      + correlationInvolution D second third ^ 2 + correlationInvolution D second fourth ^ 2
      + correlationInvolution D second fifth ^ 2 + correlationInvolution D second sixth ^ 2
      + correlationInvolution D second seventh ^ 2 + correlationInvolution D third fourth ^ 2
      + correlationInvolution D third fifth ^ 2 + correlationInvolution D third sixth ^ 2
      + correlationInvolution D third seventh ^ 2 + correlationInvolution D fourth fifth ^ 2
      + correlationInvolution D fourth sixth ^ 2 + correlationInvolution D fourth seventh ^ 2
      + correlationInvolution D fifth sixth ^ 2 + correlationInvolution D fifth seventh ^ 2
      + correlationInvolution D sixth seventh ^ 2 = 14 / 3 := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hdiagAll : ∀ atomIndex : Fin 7, correlationInvolution D atomIndex atomIndex = 0 :=
    fun atomIndex => correlationInvolution_apply_self D (hpositive atomIndex)
  have hcommAll : ∀ rowIndex colIndex : Fin 7,
      correlationInvolution D colIndex rowIndex = correlationInvolution D rowIndex colIndex :=
    correlationInvolution_comm D
  have hrow0 := sum_sq_row_sevenThree D huniform hbijective first
  have hrow1 := sum_sq_row_sevenThree D huniform hbijective second
  have hrow2 := sum_sq_row_sevenThree D huniform hbijective third
  have hrow3 := sum_sq_row_sevenThree D huniform hbijective fourth
  have hrow4 := sum_sq_row_sevenThree D huniform hbijective fifth
  have hrow5 := sum_sq_row_sevenThree D huniform hbijective sixth
  have hrow6 := sum_sq_row_sevenThree D huniform hbijective seventh
  simp only [hdiagAll, hcommAll first second, hcommAll first third, hcommAll first fourth,
    hcommAll first fifth, hcommAll first sixth, hcommAll first seventh, hcommAll second third,
    hcommAll second fourth, hcommAll second fifth, hcommAll second sixth,
    hcommAll second seventh, hcommAll third fourth, hcommAll third fifth,
    hcommAll third sixth, hcommAll third seventh, hcommAll fourth fifth,
    hcommAll fourth sixth, hcommAll fourth seventh, hcommAll fifth sixth,
    hcommAll fifth seventh, hcommAll sixth seventh, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero, zero_add]
    at hrow0 hrow1 hrow2 hrow3 hrow4 hrow5 hrow6
  linarith [hrow0, hrow1, hrow2, hrow3, hrow4, hrow5, hrow6]

/-- **THE SIX-SET PAIR MASS IS `10/3`**: deleting one atom removes exactly its
row, worth `4/3`.  This constant is the `-10/3` in the aggregate's gradient
`e_2(tau off c) - 10/3`, and twice it is the pen's frozen six-block trace
`tr M[B_6]^2 = 20/3`. -/
theorem sum_pairSquare_sixSet_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh]) :
    correlationInvolution D second third ^ 2 + correlationInvolution D second fourth ^ 2
      + correlationInvolution D second fifth ^ 2 + correlationInvolution D second sixth ^ 2
      + correlationInvolution D second seventh ^ 2 + correlationInvolution D third fourth ^ 2
      + correlationInvolution D third fifth ^ 2 + correlationInvolution D third sixth ^ 2
      + correlationInvolution D third seventh ^ 2 + correlationInvolution D fourth fifth ^ 2
      + correlationInvolution D fourth sixth ^ 2 + correlationInvolution D fourth seventh ^ 2
      + correlationInvolution D fifth sixth ^ 2 + correlationInvolution D fifth seventh ^ 2
      + correlationInvolution D sixth seventh ^ 2 = 10 / 3 := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hdiagAll : ∀ atomIndex : Fin 7, correlationInvolution D atomIndex atomIndex = 0 :=
    fun atomIndex => correlationInvolution_apply_self D (hpositive atomIndex)
  have hcommAll : ∀ rowIndex colIndex : Fin 7,
      correlationInvolution D colIndex rowIndex = correlationInvolution D rowIndex colIndex :=
    correlationInvolution_comm D
  have htotal := sum_pairSquare_sevenThree D huniform hbijective
  have hrow0 := sum_sq_row_sevenThree D huniform hbijective first
  simp only [hdiagAll, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_add] at hrow0
  linarith [htotal, hrow0]

/-- **THE FIVE-SET PAIR MASS IS `2 + w_ef`**: deleting a pair removes two rows and
restores their shared edge.  The pen's five-block trace law `tr M[B_5]^2 = 4 + 2w`
is twice this. -/
theorem sum_pairSquare_fiveSet_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh]) :
    correlationInvolution D first second ^ 2 + correlationInvolution D first third ^ 2
      + correlationInvolution D first fourth ^ 2 + correlationInvolution D first fifth ^ 2
      + correlationInvolution D second third ^ 2 + correlationInvolution D second fourth ^ 2
      + correlationInvolution D second fifth ^ 2 + correlationInvolution D third fourth ^ 2
      + correlationInvolution D third fifth ^ 2 + correlationInvolution D fourth fifth ^ 2
      = 2 + correlationInvolution D sixth seventh ^ 2 := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hdiagAll : ∀ atomIndex : Fin 7, correlationInvolution D atomIndex atomIndex = 0 :=
    fun atomIndex => correlationInvolution_apply_self D (hpositive atomIndex)
  have hcommAll : ∀ rowIndex colIndex : Fin 7,
      correlationInvolution D colIndex rowIndex = correlationInvolution D rowIndex colIndex :=
    correlationInvolution_comm D
  have htotal := sum_pairSquare_sevenThree D huniform hbijective
  have hrow5 := sum_sq_row_sevenThree D huniform hbijective sixth
  have hrow6 := sum_sq_row_sevenThree D huniform hbijective seventh
  simp only [hdiagAll, hcommAll first sixth, hcommAll second sixth, hcommAll third sixth,
    hcommAll fourth sixth, hcommAll fifth sixth, hcommAll first seventh,
    hcommAll second seventh, hcommAll third seventh, hcommAll fourth seventh,
    hcommAll fifth seventh, hcommAll sixth seventh, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero] at hrow5 hrow6
  linarith [htotal, hrow5, hrow6]

/-! ## 5. Determinant conservation: C-D1, C-D2, C-D3

`det Gamma[T] = 1 - sigma_T + 2 P_T`, so the sigma and product ledgers combine
into the determinant ledger.  The 35-triple total `343/27` re-derived here is the
same constant the landed spectral route
`Gtz.sum_det_principalMinors_directionGramMatrix_sevenThree` reads off the
two-valued spectrum of `Gamma`; the two proofs share nothing, and their agreement
is the file's consistency check with the shipped kernel. -/

/-- **(C-D1) THE PER-EDGE DETERMINANT LAW.**  The five triples through a pair
carry determinant mass `(7/3)(1 - w_ef)` — the sharper the pair, the poorer its
completions.  At `w_ef = 1` (a doubled atom) the five completions carry nothing:
a parallel pair starves every triple through it. -/
theorem sum_sdiff_tripleBracket_pair_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {leftIndex rightIndex : Fin 7} (hdistinct : leftIndex ≠ rightIndex) :
    ∑ colIndex ∈ Finset.univ \ ({leftIndex, rightIndex} : Finset (Fin 7)),
        hollowTripleBracket (correlationInvolution D) leftIndex rightIndex colIndex
      = 7 / 3 * (1 - correlationInvolution D leftIndex rightIndex ^ 2) := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hexpand : ∀ colIndex : Fin 7,
      hollowTripleBracket (correlationInvolution D) leftIndex rightIndex colIndex
      = 1 - correlationInvolution D leftIndex rightIndex ^ 2
        - correlationInvolution D leftIndex colIndex ^ 2
        - correlationInvolution D rightIndex colIndex ^ 2
        + 2 * hollowTripleProduct (correlationInvolution D) leftIndex rightIndex colIndex := by
    intro colIndex
    rw [hollowTripleBracket, elliptopeBracket, hollowTripleProduct]
  have hrowLeft : ∑ colIndex ∈ Finset.univ \ ({leftIndex, rightIndex} : Finset (Fin 7)),
      correlationInvolution D leftIndex colIndex ^ 2
      = 4 / 3 - correlationInvolution D leftIndex rightIndex ^ 2 := by
    have hsplit := Finset.sum_sdiff (f := fun colIndex =>
        correlationInvolution D leftIndex colIndex ^ 2)
      (Finset.subset_univ ({leftIndex, rightIndex} : Finset (Fin 7)))
    have hpairSum : ∑ colIndex ∈ ({leftIndex, rightIndex} : Finset (Fin 7)),
        correlationInvolution D leftIndex colIndex ^ 2
        = correlationInvolution D leftIndex rightIndex ^ 2 := by
      rw [Finset.sum_pair hdistinct,
        correlationInvolution_apply_self D (hpositive leftIndex)]
      norm_num
    have hrow := sum_sq_correlationInvolution_sevenThree D huniform leftIndex
    linarith [hsplit, hpairSum, hrow]
  have hrowRight : ∑ colIndex ∈ Finset.univ \ ({leftIndex, rightIndex} : Finset (Fin 7)),
      correlationInvolution D rightIndex colIndex ^ 2
      = 4 / 3 - correlationInvolution D leftIndex rightIndex ^ 2 := by
    have hsplit := Finset.sum_sdiff (f := fun colIndex =>
        correlationInvolution D rightIndex colIndex ^ 2)
      (Finset.subset_univ ({leftIndex, rightIndex} : Finset (Fin 7)))
    have hpairSum : ∑ colIndex ∈ ({leftIndex, rightIndex} : Finset (Fin 7)),
        correlationInvolution D rightIndex colIndex ^ 2
        = correlationInvolution D leftIndex rightIndex ^ 2 := by
      rw [Finset.sum_pair hdistinct,
        correlationInvolution_apply_self D (hpositive rightIndex),
        correlationInvolution_comm D leftIndex rightIndex]
      norm_num
    have hrow := sum_sq_correlationInvolution_sevenThree D huniform rightIndex
    linarith [hsplit, hpairSum, hrow]
  have hproducts := sum_sdiff_tripleProduct_pair_sevenThree D huniform hdistinct
  have hcard : (Finset.univ \ ({leftIndex, rightIndex} : Finset (Fin 7))).card = 5 := by
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
      Finset.card_pair hdistinct]
  rw [Finset.sum_congr rfl fun colIndex _ => hexpand colIndex, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, hcard, hrowLeft,
    hrowRight, ← Finset.mul_sum, hproducts]
  ring

/-- The fifteen sigma masses of the triples through an atom total `10`: each of
the six edges at the atom sits in five of them (`5 * 4/3`), and the fifteen edges
avoiding it each sit in one (`10/3`). -/
theorem sum_tripleSigma_vertex_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh]) :
    hollowTripleSigma (correlationInvolution D) first second third
      + hollowTripleSigma (correlationInvolution D) first second fourth
      + hollowTripleSigma (correlationInvolution D) first second fifth
      + hollowTripleSigma (correlationInvolution D) first second sixth
      + hollowTripleSigma (correlationInvolution D) first second seventh
      + hollowTripleSigma (correlationInvolution D) first third fourth
      + hollowTripleSigma (correlationInvolution D) first third fifth
      + hollowTripleSigma (correlationInvolution D) first third sixth
      + hollowTripleSigma (correlationInvolution D) first third seventh
      + hollowTripleSigma (correlationInvolution D) first fourth fifth
      + hollowTripleSigma (correlationInvolution D) first fourth sixth
      + hollowTripleSigma (correlationInvolution D) first fourth seventh
      + hollowTripleSigma (correlationInvolution D) first fifth sixth
      + hollowTripleSigma (correlationInvolution D) first fifth seventh
      + hollowTripleSigma (correlationInvolution D) first sixth seventh = 10 := by
  have hrow0 := sum_sq_row_sevenThree D huniform hbijective first
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hdiagAll : ∀ atomIndex : Fin 7, correlationInvolution D atomIndex atomIndex = 0 :=
    fun atomIndex => correlationInvolution_apply_self D (hpositive atomIndex)
  have hsixSet := sum_pairSquare_sixSet_sevenThree D huniform hbijective
  simp only [hdiagAll, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_add] at hrow0
  simp only [hollowTripleSigma]
  linarith [hrow0, hsixSet]

/-- **(C-D2) THE PER-ATOM DETERMINANT LAW.**  The fifteen triples through any
atom carry determinant mass `49/9`, so some triple through EVERY atom has
`det Gamma[T] ≥ 49/135`. -/
theorem sum_tripleBracket_vertex_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh]) :
    hollowTripleBracket (correlationInvolution D) first second third
      + hollowTripleBracket (correlationInvolution D) first second fourth
      + hollowTripleBracket (correlationInvolution D) first second fifth
      + hollowTripleBracket (correlationInvolution D) first second sixth
      + hollowTripleBracket (correlationInvolution D) first second seventh
      + hollowTripleBracket (correlationInvolution D) first third fourth
      + hollowTripleBracket (correlationInvolution D) first third fifth
      + hollowTripleBracket (correlationInvolution D) first third sixth
      + hollowTripleBracket (correlationInvolution D) first third seventh
      + hollowTripleBracket (correlationInvolution D) first fourth fifth
      + hollowTripleBracket (correlationInvolution D) first fourth sixth
      + hollowTripleBracket (correlationInvolution D) first fourth seventh
      + hollowTripleBracket (correlationInvolution D) first fifth sixth
      + hollowTripleBracket (correlationInvolution D) first fifth seventh
      + hollowTripleBracket (correlationInvolution D) first sixth seventh = 49 / 9 := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hdiagAll : ∀ atomIndex : Fin 7, correlationInvolution D atomIndex atomIndex = 0 :=
    fun atomIndex => correlationInvolution_apply_self D (hpositive atomIndex)
  have hsigma := sum_tripleSigma_vertex_sevenThree D huniform hbijective
  have hproducts := sum_pairTripleProduct_vertex_sevenThree D huniform hbijective first
  simp only [hollowTripleProduct, hdiagAll, zero_mul, add_zero, zero_add]
    at hproducts
  simp only [hollowTripleBracket_eq_one_sub_sigma_add, hollowTripleProduct]
  linarith [hsigma, hproducts]

/-- The thirty-five sigma masses total `70/3`: every edge lies in five triples. -/
theorem sum_tripleSigma_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh]) :
    hollowTripleSigma (correlationInvolution D) first second third
      + hollowTripleSigma (correlationInvolution D) first second fourth
      + hollowTripleSigma (correlationInvolution D) first second fifth
      + hollowTripleSigma (correlationInvolution D) first second sixth
      + hollowTripleSigma (correlationInvolution D) first second seventh
      + hollowTripleSigma (correlationInvolution D) first third fourth
      + hollowTripleSigma (correlationInvolution D) first third fifth
      + hollowTripleSigma (correlationInvolution D) first third sixth
      + hollowTripleSigma (correlationInvolution D) first third seventh
      + hollowTripleSigma (correlationInvolution D) first fourth fifth
      + hollowTripleSigma (correlationInvolution D) first fourth sixth
      + hollowTripleSigma (correlationInvolution D) first fourth seventh
      + hollowTripleSigma (correlationInvolution D) first fifth sixth
      + hollowTripleSigma (correlationInvolution D) first fifth seventh
      + hollowTripleSigma (correlationInvolution D) first sixth seventh
      + hollowTripleSigma (correlationInvolution D) second third fourth
      + hollowTripleSigma (correlationInvolution D) second third fifth
      + hollowTripleSigma (correlationInvolution D) second third sixth
      + hollowTripleSigma (correlationInvolution D) second third seventh
      + hollowTripleSigma (correlationInvolution D) second fourth fifth
      + hollowTripleSigma (correlationInvolution D) second fourth sixth
      + hollowTripleSigma (correlationInvolution D) second fourth seventh
      + hollowTripleSigma (correlationInvolution D) second fifth sixth
      + hollowTripleSigma (correlationInvolution D) second fifth seventh
      + hollowTripleSigma (correlationInvolution D) second sixth seventh
      + hollowTripleSigma (correlationInvolution D) third fourth fifth
      + hollowTripleSigma (correlationInvolution D) third fourth sixth
      + hollowTripleSigma (correlationInvolution D) third fourth seventh
      + hollowTripleSigma (correlationInvolution D) third fifth sixth
      + hollowTripleSigma (correlationInvolution D) third fifth seventh
      + hollowTripleSigma (correlationInvolution D) third sixth seventh
      + hollowTripleSigma (correlationInvolution D) fourth fifth sixth
      + hollowTripleSigma (correlationInvolution D) fourth fifth seventh
      + hollowTripleSigma (correlationInvolution D) fourth sixth seventh
      + hollowTripleSigma (correlationInvolution D) fifth sixth seventh = 70 / 3 := by
  have hmass := sum_pairSquare_sevenThree D huniform hbijective
  simp only [hollowTripleSigma]
  linarith [hmass]

/-- **(C-D3) THE TOTAL, RE-DERIVED.**  The thirty-five triple determinants total
`343/27 = (7/3)^3` — here from the sigma and product ledgers
(`35 - 70/3 + 28/27`), in the kernel already from the two-valued spectrum of
`Gamma` (`Gtz.sum_det_principalMinors_directionGramMatrix_sevenThree`).  The two
routes share no lemma; their agreement on `343/27` is the cross-check the brief
demands. -/
theorem sum_tripleBracket_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh]) :
    hollowTripleBracket (correlationInvolution D) first second third
      + hollowTripleBracket (correlationInvolution D) first second fourth
      + hollowTripleBracket (correlationInvolution D) first second fifth
      + hollowTripleBracket (correlationInvolution D) first second sixth
      + hollowTripleBracket (correlationInvolution D) first second seventh
      + hollowTripleBracket (correlationInvolution D) first third fourth
      + hollowTripleBracket (correlationInvolution D) first third fifth
      + hollowTripleBracket (correlationInvolution D) first third sixth
      + hollowTripleBracket (correlationInvolution D) first third seventh
      + hollowTripleBracket (correlationInvolution D) first fourth fifth
      + hollowTripleBracket (correlationInvolution D) first fourth sixth
      + hollowTripleBracket (correlationInvolution D) first fourth seventh
      + hollowTripleBracket (correlationInvolution D) first fifth sixth
      + hollowTripleBracket (correlationInvolution D) first fifth seventh
      + hollowTripleBracket (correlationInvolution D) first sixth seventh
      + hollowTripleBracket (correlationInvolution D) second third fourth
      + hollowTripleBracket (correlationInvolution D) second third fifth
      + hollowTripleBracket (correlationInvolution D) second third sixth
      + hollowTripleBracket (correlationInvolution D) second third seventh
      + hollowTripleBracket (correlationInvolution D) second fourth fifth
      + hollowTripleBracket (correlationInvolution D) second fourth sixth
      + hollowTripleBracket (correlationInvolution D) second fourth seventh
      + hollowTripleBracket (correlationInvolution D) second fifth sixth
      + hollowTripleBracket (correlationInvolution D) second fifth seventh
      + hollowTripleBracket (correlationInvolution D) second sixth seventh
      + hollowTripleBracket (correlationInvolution D) third fourth fifth
      + hollowTripleBracket (correlationInvolution D) third fourth sixth
      + hollowTripleBracket (correlationInvolution D) third fourth seventh
      + hollowTripleBracket (correlationInvolution D) third fifth sixth
      + hollowTripleBracket (correlationInvolution D) third fifth seventh
      + hollowTripleBracket (correlationInvolution D) third sixth seventh
      + hollowTripleBracket (correlationInvolution D) fourth fifth sixth
      + hollowTripleBracket (correlationInvolution D) fourth fifth seventh
      + hollowTripleBracket (correlationInvolution D) fourth sixth seventh
      + hollowTripleBracket (correlationInvolution D) fifth sixth seventh = 343 / 27 := by
  have hsigma := sum_tripleSigma_sevenThree D huniform hbijective
  have hproducts := sum_tripleProduct_sevenThree D huniform hbijective
  simp only [hollowTripleBracket_eq_one_sub_sigma_add]
  linarith [hsigma, hproducts]

/-! ## 6. Five-set coherence: C-5SET

Inclusion–exclusion over a deleted pair.  This is the sharpest sign law of the
`(7,3)` stratum: EVERY five-set carries strictly positive oriented product mass
— where the `(6,3)` analogue vanishes identically
(`Gtz.IsHollowInvolution.sum_tripleProduct_fiveSet`). -/

/-- **(C-5SET) THE FIVE-SET COHERENCE LAW.**  The ten triples avoiding a pair
carry product mass `2/27 + w_ef / 3 > 0`. -/
theorem sum_tripleProduct_fiveSet_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh]) :
    hollowTripleProduct (correlationInvolution D) first second third
      + hollowTripleProduct (correlationInvolution D) first second fourth
      + hollowTripleProduct (correlationInvolution D) first second fifth
      + hollowTripleProduct (correlationInvolution D) first third fourth
      + hollowTripleProduct (correlationInvolution D) first third fifth
      + hollowTripleProduct (correlationInvolution D) first fourth fifth
      + hollowTripleProduct (correlationInvolution D) second third fourth
      + hollowTripleProduct (correlationInvolution D) second third fifth
      + hollowTripleProduct (correlationInvolution D) second fourth fifth
      + hollowTripleProduct (correlationInvolution D) third fourth fifth
      = 2 / 27 + correlationInvolution D sixth seventh ^ 2 / 3 := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hdiagAll : ∀ atomIndex : Fin 7, correlationInvolution D atomIndex atomIndex = 0 :=
    fun atomIndex => correlationInvolution_apply_self D (hpositive atomIndex)
  have hcommAll : ∀ rowIndex colIndex : Fin 7,
      correlationInvolution D colIndex rowIndex = correlationInvolution D rowIndex colIndex :=
    correlationInvolution_comm D
  have hne56 : sixth ≠ seventh :=
    ne_of_bijective_seven hbijective (by decide : (5 : Fin 7) ≠ 6)
  have htotal := sum_tripleProduct_sevenThree D huniform hbijective
  have hvertex5 := sum_pairTripleProduct_vertex_sevenThree D huniform hbijective sixth
  have hvertex6 := sum_pairTripleProduct_vertex_sevenThree D huniform hbijective seventh
  have hpair := sum_tripleProduct_throughPair_sevenThree D huniform hbijective hne56
  simp only [hollowTripleProduct, hdiagAll, hcommAll first sixth, hcommAll first seventh,
    hcommAll second sixth, hcommAll second seventh, hcommAll third sixth,
    hcommAll third seventh, hcommAll fourth sixth, hcommAll fourth seventh,
    hcommAll fifth sixth, hcommAll fifth seventh, hcommAll sixth seventh, mul_zero, zero_mul,
    add_zero] at htotal hvertex5 hvertex6 hpair ⊢
  linarith [htotal, hvertex5, hvertex6, hpair]

/-- **EVERY FIVE-SET CARRIES STRICTLY POSITIVE COHERENT MASS** — the headline
sign law of the `(7,3)` stratum, and exactly what the `(6,3)` cell provably
lacks (there the ten products sum to zero). -/
theorem sum_tripleProduct_fiveSet_pos_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh]) :
    0 < hollowTripleProduct (correlationInvolution D) first second third
      + hollowTripleProduct (correlationInvolution D) first second fourth
      + hollowTripleProduct (correlationInvolution D) first second fifth
      + hollowTripleProduct (correlationInvolution D) first third fourth
      + hollowTripleProduct (correlationInvolution D) first third fifth
      + hollowTripleProduct (correlationInvolution D) first fourth fifth
      + hollowTripleProduct (correlationInvolution D) second third fourth
      + hollowTripleProduct (correlationInvolution D) second third fifth
      + hollowTripleProduct (correlationInvolution D) second fourth fifth
      + hollowTripleProduct (correlationInvolution D) third fourth fifth := by
  rw [sum_tripleProduct_fiveSet_sevenThree D huniform hbijective]
  positivity

/-- **EVERY FIVE-SET CONTAINS A COHERENT TRIPLE**: some triple avoiding the
deleted pair has oriented product at least `(2/27 + w/3)/10 ≥ 1/135 > 0` — the
pigeonhole reading of C-5SET, and the quantitative sign law the `(6,3)` cell
provably lacks. -/
theorem exists_distinct_tripleProduct_ge_avoiding_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh]) :
    ∃ leftIndex middleIndex rightIndex : Fin 7,
      leftIndex ≠ sixth ∧ leftIndex ≠ seventh ∧ middleIndex ≠ sixth ∧ middleIndex ≠ seventh
        ∧ rightIndex ≠ sixth ∧ rightIndex ≠ seventh
        ∧ leftIndex ≠ middleIndex ∧ leftIndex ≠ rightIndex ∧ middleIndex ≠ rightIndex
        ∧ (2 / 27 + correlationInvolution D sixth seventh ^ 2 / 3) / 10
            ≤ hollowTripleProduct (correlationInvolution D) leftIndex middleIndex rightIndex := by
  by_contra hcontra
  simp only [not_exists, not_and, not_le] at hcontra
  have hneOf : ∀ leftSlot rightSlot : Fin 7, leftSlot ≠ rightSlot →
      ![first, second, third, fourth, fifth, sixth, seventh] leftSlot
        ≠ ![first, second, third, fourth, fifth, sixth, seventh] rightSlot :=
    fun _ _ hslot => ne_of_bijective_seven hbijective hslot
  have hfive := sum_tripleProduct_fiveSet_sevenThree D huniform hbijective
  have hbound : ∀ leftIndex middleIndex rightIndex : Fin 7,
      leftIndex ≠ sixth → leftIndex ≠ seventh → middleIndex ≠ sixth → middleIndex ≠ seventh →
      rightIndex ≠ sixth → rightIndex ≠ seventh →
      leftIndex ≠ middleIndex → leftIndex ≠ rightIndex → middleIndex ≠ rightIndex →
      hollowTripleProduct (correlationInvolution D) leftIndex middleIndex rightIndex
        < (2 / 27 + correlationInvolution D sixth seventh ^ 2 / 3) / 10 :=
    fun leftIndex middleIndex rightIndex h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      hcontra leftIndex middleIndex rightIndex h1 h2 h3 h4 h5 h6 h7 h8 h9
  linarith [hfive,
    hbound first second third (hneOf 0 5 (by decide)) (hneOf 0 6 (by decide))
      (hneOf 1 5 (by decide)) (hneOf 1 6 (by decide)) (hneOf 2 5 (by decide))
      (hneOf 2 6 (by decide)) (hneOf 0 1 (by decide)) (hneOf 0 2 (by decide))
      (hneOf 1 2 (by decide)),
    hbound first second fourth (hneOf 0 5 (by decide)) (hneOf 0 6 (by decide))
      (hneOf 1 5 (by decide)) (hneOf 1 6 (by decide)) (hneOf 3 5 (by decide))
      (hneOf 3 6 (by decide)) (hneOf 0 1 (by decide)) (hneOf 0 3 (by decide))
      (hneOf 1 3 (by decide)),
    hbound first second fifth (hneOf 0 5 (by decide)) (hneOf 0 6 (by decide))
      (hneOf 1 5 (by decide)) (hneOf 1 6 (by decide)) (hneOf 4 5 (by decide))
      (hneOf 4 6 (by decide)) (hneOf 0 1 (by decide)) (hneOf 0 4 (by decide))
      (hneOf 1 4 (by decide)),
    hbound first third fourth (hneOf 0 5 (by decide)) (hneOf 0 6 (by decide))
      (hneOf 2 5 (by decide)) (hneOf 2 6 (by decide)) (hneOf 3 5 (by decide))
      (hneOf 3 6 (by decide)) (hneOf 0 2 (by decide)) (hneOf 0 3 (by decide))
      (hneOf 2 3 (by decide)),
    hbound first third fifth (hneOf 0 5 (by decide)) (hneOf 0 6 (by decide))
      (hneOf 2 5 (by decide)) (hneOf 2 6 (by decide)) (hneOf 4 5 (by decide))
      (hneOf 4 6 (by decide)) (hneOf 0 2 (by decide)) (hneOf 0 4 (by decide))
      (hneOf 2 4 (by decide)),
    hbound first fourth fifth (hneOf 0 5 (by decide)) (hneOf 0 6 (by decide))
      (hneOf 3 5 (by decide)) (hneOf 3 6 (by decide)) (hneOf 4 5 (by decide))
      (hneOf 4 6 (by decide)) (hneOf 0 3 (by decide)) (hneOf 0 4 (by decide))
      (hneOf 3 4 (by decide)),
    hbound second third fourth (hneOf 1 5 (by decide)) (hneOf 1 6 (by decide))
      (hneOf 2 5 (by decide)) (hneOf 2 6 (by decide)) (hneOf 3 5 (by decide))
      (hneOf 3 6 (by decide)) (hneOf 1 2 (by decide)) (hneOf 1 3 (by decide))
      (hneOf 2 3 (by decide)),
    hbound second third fifth (hneOf 1 5 (by decide)) (hneOf 1 6 (by decide))
      (hneOf 2 5 (by decide)) (hneOf 2 6 (by decide)) (hneOf 4 5 (by decide))
      (hneOf 4 6 (by decide)) (hneOf 1 2 (by decide)) (hneOf 1 4 (by decide))
      (hneOf 2 4 (by decide)),
    hbound second fourth fifth (hneOf 1 5 (by decide)) (hneOf 1 6 (by decide))
      (hneOf 3 5 (by decide)) (hneOf 3 6 (by decide)) (hneOf 4 5 (by decide))
      (hneOf 4 6 (by decide)) (hneOf 1 3 (by decide)) (hneOf 1 4 (by decide))
      (hneOf 3 4 (by decide)),
    hbound third fourth fifth (hneOf 2 5 (by decide)) (hneOf 2 6 (by decide))
      (hneOf 3 5 (by decide)) (hneOf 3 6 (by decide)) (hneOf 4 5 (by decide))
      (hneOf 4 6 (by decide)) (hneOf 2 3 (by decide)) (hneOf 2 4 (by decide))
      (hneOf 3 4 (by decide))]

/-! ## 7. The weighted aggregate identity: C-AGG

The file's centerpiece.  The thirty-five determinant clauses
`Delta_tau(T) = det(diag(tau_T) + M[T])` of the weighted triple criterion have a
frame-independent total on the whole `(7,3)`-uniform stratum:

  `sum_T Delta_tau(T) = e_3(tau) - (10/3) sum tau + 28/27` ,

with `e_3` written in power sums.  Seven row laws and the product total C-P3 are
the entire proof.  The `(6,3)` twin is `Gtz.sum_involSlackDeterminant_six`
(`e_3(tau) - 2 sum tau`, no residue); the `+28/27` here is the coherent residue
of the positive supply chain, and it does NOT rescue averaging: on the capacity
polytope the total is still bounded below `-308/81`. -/

/-- **(C-AGG) THE WEIGHTED AGGREGATE IDENTITY.**  For every uniform-share
`(7,3)` design and EVERY slack vector, the thirty-five determinant clauses total
`e_3(tau) - (10/3) sum tau + 28/27`. -/
theorem sum_involSlackDeterminant_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh])
    (slack : Fin 7 → ℝ) :
    involSlackDeterminant (correlationInvolution D) slack first second third
      + involSlackDeterminant (correlationInvolution D) slack first second fourth
      + involSlackDeterminant (correlationInvolution D) slack first second fifth
      + involSlackDeterminant (correlationInvolution D) slack first second sixth
      + involSlackDeterminant (correlationInvolution D) slack first second seventh
      + involSlackDeterminant (correlationInvolution D) slack first third fourth
      + involSlackDeterminant (correlationInvolution D) slack first third fifth
      + involSlackDeterminant (correlationInvolution D) slack first third sixth
      + involSlackDeterminant (correlationInvolution D) slack first third seventh
      + involSlackDeterminant (correlationInvolution D) slack first fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack first fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack first fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack first fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack first fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack first sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack second third fourth
      + involSlackDeterminant (correlationInvolution D) slack second third fifth
      + involSlackDeterminant (correlationInvolution D) slack second third sixth
      + involSlackDeterminant (correlationInvolution D) slack second third seventh
      + involSlackDeterminant (correlationInvolution D) slack second fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack second fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack second fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack second fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack second fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack second sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack third fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack third fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack third fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack third fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack third fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack third sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack fourth fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack fourth fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack fourth sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack fifth sixth seventh
      = ((∑ index, slack index) ^ 3
            - 3 * (∑ index, slack index) * (∑ index, slack index ^ 2)
            + 2 * ∑ index, slack index ^ 3) / 6
        - 10 / 3 * (∑ index, slack index) + 28 / 27 := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hdiagAll : ∀ atomIndex : Fin 7, correlationInvolution D atomIndex atomIndex = 0 :=
    fun atomIndex => correlationInvolution_apply_self D (hpositive atomIndex)
  have hcommAll : ∀ rowIndex colIndex : Fin 7,
      correlationInvolution D colIndex rowIndex = correlationInvolution D rowIndex colIndex :=
    correlationInvolution_comm D
  have hproduct := sum_tripleProduct_sevenThree D huniform hbijective
  have hrow0 := sum_sq_row_sevenThree D huniform hbijective first
  have hrow1 := sum_sq_row_sevenThree D huniform hbijective second
  have hrow2 := sum_sq_row_sevenThree D huniform hbijective third
  have hrow3 := sum_sq_row_sevenThree D huniform hbijective fourth
  have hrow4 := sum_sq_row_sevenThree D huniform hbijective fifth
  have hrow5 := sum_sq_row_sevenThree D huniform hbijective sixth
  have hrow6 := sum_sq_row_sevenThree D huniform hbijective seventh
  simp only [hdiagAll, hcommAll first second, hcommAll first third, hcommAll first fourth,
    hcommAll first fifth, hcommAll first sixth, hcommAll first seventh, hcommAll second third,
    hcommAll second fourth, hcommAll second fifth, hcommAll second sixth,
    hcommAll second seventh, hcommAll third fourth, hcommAll third fifth,
    hcommAll third sixth, hcommAll third seventh, hcommAll fourth fifth,
    hcommAll fourth sixth, hcommAll fourth seventh, hcommAll fifth sixth,
    hcommAll fifth seventh, hcommAll sixth seventh, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero, zero_add]
    at hrow0 hrow1 hrow2 hrow3 hrow4 hrow5 hrow6
  simp only [hollowTripleProduct] at hproduct
  rw [sum_eq_of_bijective_seven hbijective slack,
    sum_eq_of_bijective_seven hbijective fun index => slack index ^ 2,
    sum_eq_of_bijective_seven hbijective fun index => slack index ^ 3]
  simp only [involSlackDeterminant, slackDeterminantThree]
  linear_combination
    (slack first - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth + slack seventh) / 2) * hrow0
      + (slack second - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth + slack seventh) / 2) * hrow1
      + (slack third - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth + slack seventh) / 2) * hrow2
      + (slack fourth - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth + slack seventh) / 2) * hrow3
      + (slack fifth - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth + slack seventh) / 2) * hrow4
      + (slack sixth - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth + slack seventh) / 2) * hrow5
      + (slack seventh - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth + slack seventh) / 2) * hrow6
      + 2 * hproduct

/-- **THE CONSTANT-SLACK AGGREGATE** is `35 t^3 - (70/3) t + 28/27`.  Its three
markers: `t = 1` gives the minor total `343/27`; `t = 2/3` gives `-112/27`; the
stationary point is `9 t^2 = 2`, strictly below the criterion point. -/
theorem sum_involSlackDeterminant_eq_of_constant_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh])
    {slack : Fin 7 → ℝ} {level : ℝ} (hconstant : ∀ index, slack index = level) :
    involSlackDeterminant (correlationInvolution D) slack first second third
      + involSlackDeterminant (correlationInvolution D) slack first second fourth
      + involSlackDeterminant (correlationInvolution D) slack first second fifth
      + involSlackDeterminant (correlationInvolution D) slack first second sixth
      + involSlackDeterminant (correlationInvolution D) slack first second seventh
      + involSlackDeterminant (correlationInvolution D) slack first third fourth
      + involSlackDeterminant (correlationInvolution D) slack first third fifth
      + involSlackDeterminant (correlationInvolution D) slack first third sixth
      + involSlackDeterminant (correlationInvolution D) slack first third seventh
      + involSlackDeterminant (correlationInvolution D) slack first fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack first fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack first fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack first fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack first fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack first sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack second third fourth
      + involSlackDeterminant (correlationInvolution D) slack second third fifth
      + involSlackDeterminant (correlationInvolution D) slack second third sixth
      + involSlackDeterminant (correlationInvolution D) slack second third seventh
      + involSlackDeterminant (correlationInvolution D) slack second fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack second fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack second fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack second fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack second fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack second sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack third fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack third fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack third fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack third fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack third fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack third sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack fourth fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack fourth fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack fourth sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack fifth sixth seventh
      = 35 * level ^ 3 - 70 / 3 * level + 28 / 27 := by
  have hmain := sum_involSlackDeterminant_sevenThree D huniform hbijective slack
  have hsumOne : ∑ index, slack index = 7 * level := by
    rw [Finset.sum_congr rfl fun index _ => hconstant index, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hsumSq : ∑ index, slack index ^ 2 = 7 * level ^ 2 := by
    rw [Finset.sum_congr rfl fun index _ => by rw [hconstant index], Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hsumCube : ∑ index, slack index ^ 3 = 7 * level ^ 3 := by
    rw [Finset.sum_congr rfl fun index _ => by rw [hconstant index], Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [hmain, hsumOne, hsumSq, hsumCube]
  ring

/-- **THE `tau ≡ 1` EVALUATION IS THE MINOR TOTAL**: the aggregate at slack one
returns `343/27`, matching `Gtz.sum_tripleBracket_sevenThree` — and through it
the landed spectral total
`Gtz.sum_det_principalMinors_directionGramMatrix_sevenThree`.  Three independent
routes, one constant. -/
theorem sum_involSlackDeterminant_slack_one_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh])
    {slack : Fin 7 → ℝ} (hconstant : ∀ index, slack index = 1) :
    involSlackDeterminant (correlationInvolution D) slack first second third
      + involSlackDeterminant (correlationInvolution D) slack first second fourth
      + involSlackDeterminant (correlationInvolution D) slack first second fifth
      + involSlackDeterminant (correlationInvolution D) slack first second sixth
      + involSlackDeterminant (correlationInvolution D) slack first second seventh
      + involSlackDeterminant (correlationInvolution D) slack first third fourth
      + involSlackDeterminant (correlationInvolution D) slack first third fifth
      + involSlackDeterminant (correlationInvolution D) slack first third sixth
      + involSlackDeterminant (correlationInvolution D) slack first third seventh
      + involSlackDeterminant (correlationInvolution D) slack first fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack first fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack first fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack first fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack first fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack first sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack second third fourth
      + involSlackDeterminant (correlationInvolution D) slack second third fifth
      + involSlackDeterminant (correlationInvolution D) slack second third sixth
      + involSlackDeterminant (correlationInvolution D) slack second third seventh
      + involSlackDeterminant (correlationInvolution D) slack second fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack second fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack second fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack second fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack second fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack second sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack third fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack third fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack third fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack third fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack third fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack third sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack fourth fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack fourth fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack fourth sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack fifth sixth seventh
      = 343 / 27 := by
  rw [sum_involSlackDeterminant_eq_of_constant_sevenThree D huniform hbijective hconstant]
  norm_num

/-- **THE CRITERION-POINT EVALUATION: NO AVERAGING SELECTOR AT `(7,3)`.**  At the
capacity slack `tau ≡ 2/3` of a leverage-3 atom the thirty-five determinant
clauses total exactly `-112/27`, so their mean is `-16/135 < 0`: no unweighted
aggregation of determinant clauses can certify coverage on the uniform stratum,
positive supply notwithstanding.  The covering must be carried by the SPREAD of
the thirty-five values; the localisations C-P1 and C-5SET say where the positive
part lives. -/
theorem sum_involSlackDeterminant_criterion_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh])
    {slack : Fin 7 → ℝ} (hconstant : ∀ index, slack index = 2 / 3) :
    involSlackDeterminant (correlationInvolution D) slack first second third
      + involSlackDeterminant (correlationInvolution D) slack first second fourth
      + involSlackDeterminant (correlationInvolution D) slack first second fifth
      + involSlackDeterminant (correlationInvolution D) slack first second sixth
      + involSlackDeterminant (correlationInvolution D) slack first second seventh
      + involSlackDeterminant (correlationInvolution D) slack first third fourth
      + involSlackDeterminant (correlationInvolution D) slack first third fifth
      + involSlackDeterminant (correlationInvolution D) slack first third sixth
      + involSlackDeterminant (correlationInvolution D) slack first third seventh
      + involSlackDeterminant (correlationInvolution D) slack first fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack first fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack first fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack first fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack first fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack first sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack second third fourth
      + involSlackDeterminant (correlationInvolution D) slack second third fifth
      + involSlackDeterminant (correlationInvolution D) slack second third sixth
      + involSlackDeterminant (correlationInvolution D) slack second third seventh
      + involSlackDeterminant (correlationInvolution D) slack second fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack second fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack second fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack second fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack second fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack second sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack third fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack third fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack third fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack third fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack third fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack third sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack fourth fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack fourth fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack fourth sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack fifth sixth seventh
      = -(112 / 27) := by
  rw [sum_involSlackDeterminant_eq_of_constant_sevenThree D huniform hbijective hconstant]
  norm_num

/-- **THE `(7,3)` CAPACITY POLYTOPE** `{tau in [0,1]^7 : sum tau = 14/3}` — the
image of the uniform-share stratum's capacities, `14/3` being the slack
normalisation `Gtz.sum_weightSlack_of_uniformShare` at `(7,3)`. -/
def slackSimplexSeven : Set (Fin 7 → ℝ) :=
  {slack | (∀ index, slack index ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ index, slack index = 14 / 3}

/-- **THE AGGREGATE IS BOUNDED AWAY FROM ZERO ON THE WHOLE POLYTOPE**: at every
point of `Gtz.slackSimplexSeven` the thirty-five clauses total at most
`-308/81`, so their mean is at most `-44/405` everywhere.  The `(6,3)` twin is
`Gtz.sum_involSlackDeterminant_le_of_mem_slackSimplex` at `-4/3`. -/
theorem sum_involSlackDeterminant_le_of_mem_slackSimplexSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third fourth fifth sixth seventh : Fin 7}
    (hbijective : Function.Bijective
      ![first, second, third, fourth, fifth, sixth, seventh])
    {slack : Fin 7 → ℝ} (hmember : slack ∈ slackSimplexSeven) :
    involSlackDeterminant (correlationInvolution D) slack first second third
      + involSlackDeterminant (correlationInvolution D) slack first second fourth
      + involSlackDeterminant (correlationInvolution D) slack first second fifth
      + involSlackDeterminant (correlationInvolution D) slack first second sixth
      + involSlackDeterminant (correlationInvolution D) slack first second seventh
      + involSlackDeterminant (correlationInvolution D) slack first third fourth
      + involSlackDeterminant (correlationInvolution D) slack first third fifth
      + involSlackDeterminant (correlationInvolution D) slack first third sixth
      + involSlackDeterminant (correlationInvolution D) slack first third seventh
      + involSlackDeterminant (correlationInvolution D) slack first fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack first fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack first fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack first fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack first fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack first sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack second third fourth
      + involSlackDeterminant (correlationInvolution D) slack second third fifth
      + involSlackDeterminant (correlationInvolution D) slack second third sixth
      + involSlackDeterminant (correlationInvolution D) slack second third seventh
      + involSlackDeterminant (correlationInvolution D) slack second fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack second fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack second fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack second fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack second fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack second sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack third fourth fifth
      + involSlackDeterminant (correlationInvolution D) slack third fourth sixth
      + involSlackDeterminant (correlationInvolution D) slack third fourth seventh
      + involSlackDeterminant (correlationInvolution D) slack third fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack third fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack third sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack fourth fifth sixth
      + involSlackDeterminant (correlationInvolution D) slack fourth fifth seventh
      + involSlackDeterminant (correlationInvolution D) slack fourth sixth seventh
      + involSlackDeterminant (correlationInvolution D) slack fifth sixth seventh
      ≤ -(308 / 81) := by
  obtain ⟨hbounds, hsum⟩ := hmember
  have hidentity := sum_involSlackDeterminant_sevenThree D huniform hbijective slack
  rw [hidentity, hsum]
  have hcube : ∀ index : Fin 7, slack index ^ 3 ≤ slack index ^ 2 := by
    intro index
    nlinarith [(hbounds index).1, (hbounds index).2, sq_nonneg (slack index)]
  have hcubeTotal : ∑ index, slack index ^ 3 ≤ ∑ index, slack index ^ 2 :=
    Finset.sum_le_sum fun index _ => hcube index
  have hsquareLower : ∀ index : Fin 7, (4 / 3) * slack index - 4 / 9 ≤ slack index ^ 2 := by
    intro index
    nlinarith [sq_nonneg (slack index - 2 / 3)]
  have hsquareFloor : (28 : ℝ) / 9 ≤ ∑ index, slack index ^ 2 := by
    have hbound : ∑ index : Fin 7, ((4 / 3) * slack index - 4 / 9)
        ≤ ∑ index : Fin 7, slack index ^ 2 :=
      Finset.sum_le_sum fun index _ => hsquareLower index
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hbound
    norm_num at hbound
    linarith
  nlinarith [hcubeTotal, hsquareFloor]

/-- **THE GRADIENT FACTORISATION.**  Between two constant slacks the aggregate
moves by `(s - t) (35 (s^2 + st + t^2) - 70/3)` — the discrete form of
`d/dt [35 t^3 - (70/3) t + 28/27] = 105 t^2 - 70/3`. -/
theorem constantSlackAggregate_sub_factor_sevenThree (leftLevel rightLevel : ℝ) :
    (35 * leftLevel ^ 3 - 70 / 3 * leftLevel + 28 / 27)
        - (35 * rightLevel ^ 3 - 70 / 3 * rightLevel + 28 / 27)
      = (leftLevel - rightLevel)
        * (35 * (leftLevel ^ 2 + leftLevel * rightLevel + rightLevel ^ 2) - 70 / 3) := by
  ring

/-- **THE STATIONARY POINT OF THE CONSTANT-SLACK AGGREGATE IS `9 t^2 = 2`** —
`t = sqrt 2 / 3 ≈ 0.4714`, strictly below the criterion point `2/3`: at the
criterion slack the aggregate is already CLIMBING (derivative `+10/3`), which is
the exact sense in which the `-112/27` deficit sits on the recovering side of the
well. -/
theorem constantSlackAggregate_stationary_iff_sevenThree (level : ℝ) :
    35 * (level ^ 2 + level * level + level ^ 2) - 70 / 3 = 0 ↔ 9 * level ^ 2 = 2 := by
  constructor <;> intro hvalue <;> nlinarith [hvalue]

/-! ## 8. The pair sum and the starve-feed gate: C-PAIR

The five-term shadow of the aggregate.  `Gtz.pairSumValueSeven` is the exact
value of the five determinant clauses through a pair; it is nonpositive on the
whole capacity box, so the pair-sum gate is as vacuous at `(7,3)` as
`Gtz.pairSumValue_nonpos` makes it at `(6,3)` — the positive supply chain does
NOT rescue it.  What survives is the starve-feed reading: a hub starved below
the pair value feeds one of the four other completions. -/

/-- **THE `(7,3)` PAIR-SUM FUNCTIONAL**: the exact total of the five determinant
clauses through a pair, as a function of the pair's two slacks and its edge
weight.  Against the `(6,3)` `Gtz.pairSumValue` the slack total moves from `4`
to `14/3`, the row constant from `1` to `4/3`, and the supply chain contributes
the new `+2w/3`. -/
noncomputable def pairSumValueSeven (firstSlack secondSlack pairWeight : ℝ) : ℝ :=
  (firstSlack * secondSlack - pairWeight) * (14 / 3 - firstSlack - secondSlack)
    - (firstSlack + secondSlack) * (4 / 3 - pairWeight) + 2 / 3 * pairWeight

/-- The pair functional at equal slacks, factored: the deficit is
`(2/3)(1 - level)` times the negative quantity `3 level^2 - 4 level - 6 w`. -/
theorem pairSumValueSeven_self (level pairWeight : ℝ) :
    pairSumValueSeven level level pairWeight
      = 2 / 3 * (1 - level) * (3 * level ^ 2 - 4 * level - 6 * pairWeight) := by
  rw [pairSumValueSeven]
  ring

/-- **THE CRITERION-POINT PAIR VALUE `-8/27 - (4/3) w`** — strictly negative for
every edge, so through EVERY pair of the uniform stratum at the criterion slack
at least one of the five completions fails its determinant clause. -/
theorem pairSumValueSeven_criterionPoint (pairWeight : ℝ) :
    pairSumValueSeven (2 / 3) (2 / 3) pairWeight = -(8 / 27) - 4 / 3 * pairWeight := by
  rw [pairSumValueSeven]
  ring

/-- The deletion corner is a zero of the pair functional for every edge weight —
the same corner structure as `(6,3)`. -/
theorem pairSumValueSeven_one_one (pairWeight : ℝ) :
    pairSumValueSeven 1 1 pairWeight = 0 := by
  rw [pairSumValueSeven]
  ring

/-- **THE EXACT CAP**: `pairSumValueSeven ≤ -s(2-s)(8-3s)/12 - 2w(2-s)` with
`s` the slack total; the slack of the bound is `(x-y)^2 (14-3s)/12`, so the cap
is attained exactly at equal slacks. -/
theorem pairSumValueSeven_le (firstSlack secondSlack pairWeight : ℝ)
    (hfirst : firstSlack ≤ 1) (hsecond : secondSlack ≤ 1) :
    pairSumValueSeven firstSlack secondSlack pairWeight
      ≤ -(firstSlack + secondSlack) * (2 - firstSlack - secondSlack)
            * (8 - 3 * (firstSlack + secondSlack)) / 12
        - 2 * pairWeight * (2 - firstSlack - secondSlack) := by
  have hroom : (0 : ℝ) ≤ 14 - 3 * (firstSlack + secondSlack) := by linarith
  rw [pairSumValueSeven]
  nlinarith [mul_nonneg (sq_nonneg (firstSlack - secondSlack)) hroom]

/-- **THE PAIR-SUM GATE IS VACUOUS AT `(7,3)` TOO.**  On the whole capacity box
the functional is at most zero — positive supply notwithstanding.  Only the
starve-feed reading below survives. -/
theorem pairSumValueSeven_nonpos (firstSlack secondSlack pairWeight : ℝ)
    (hfirst : firstSlack ≤ 1) (hsecond : secondSlack ≤ 1) (hweight : 0 ≤ pairWeight)
    (hsum : 0 ≤ firstSlack + secondSlack) :
    pairSumValueSeven firstSlack secondSlack pairWeight ≤ 0 := by
  have hcap := pairSumValueSeven_le firstSlack secondSlack pairWeight hfirst hsecond
  have hgap : (0 : ℝ) ≤ 2 - firstSlack - secondSlack := by linarith
  have height : (0 : ℝ) ≤ 8 - 3 * (firstSlack + secondSlack) := by linarith
  nlinarith [hcap, mul_nonneg (mul_nonneg hsum hgap) height, mul_nonneg hweight hgap]

/-- **(C-PAIR) THE PAIR IDENTITY.**  At any slack vector of total `14/3`, the
five determinant clauses through a pair sum to `Gtz.pairSumValueSeven` of the
pair's two slacks and its edge weight.  Two row laws, the supply chain, and the
slack normalisation are the whole proof. -/
theorem sum_involSlackDeterminant_through_pair_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {outerFirst outerSecond outerThird outerFourth hubThird pairFirst pairSecond : Fin 7}
    (hbijective : Function.Bijective ![outerFirst, outerSecond, outerThird, outerFourth,
      hubThird, pairFirst, pairSecond])
    (slack : Fin 7 → ℝ) (hslackSum : ∑ index, slack index = 14 / 3) :
    involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerFirst
      + involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerSecond
      + involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerThird
      + involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerFourth
      + involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond hubThird
      = pairSumValueSeven (slack pairFirst) (slack pairSecond)
          (correlationInvolution D pairFirst pairSecond ^ 2) := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hdiagAll : ∀ atomIndex : Fin 7, correlationInvolution D atomIndex atomIndex = 0 :=
    fun atomIndex => correlationInvolution_apply_self D (hpositive atomIndex)
  have hcommAll : ∀ rowIndex colIndex : Fin 7,
      correlationInvolution D colIndex rowIndex = correlationInvolution D rowIndex colIndex :=
    correlationInvolution_comm D
  have hdistinct : pairFirst ≠ pairSecond := fun hvalue =>
    (by decide : ¬(5 : Fin 7) = 6) (hbijective.1 (by simpa using hvalue))
  rw [sum_eq_of_bijective_seven hbijective slack] at hslackSum
  have hrowFirst := sum_sq_row_sevenThree D huniform hbijective pairFirst
  have hrowSecond := sum_sq_row_sevenThree D huniform hbijective pairSecond
  simp only [hdiagAll, hcommAll pairFirst pairSecond, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero] at hrowFirst hrowSecond
  have hchain := congrFun (congrFun (correlationInvolution_sq_sevenThree D huniform)
    pairFirst) pairSecond
  rw [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.one_apply_ne hdistinct, sum_eq_of_bijective_seven hbijective
      (fun colIndex => correlationInvolution D pairFirst colIndex
        * correlationInvolution D colIndex pairSecond)] at hchain
  simp only [hdiagAll, hcommAll pairSecond outerFirst, hcommAll pairSecond outerSecond,
    hcommAll pairSecond outerThird, hcommAll pairSecond outerFourth,
    hcommAll pairSecond hubThird, smul_eq_mul, mul_zero, zero_mul, add_zero]
    at hchain
  simp only [involSlackDeterminant, slackDeterminantThree, pairSumValueSeven]
  linear_combination
    (slack pairFirst * slack pairSecond - correlationInvolution D pairFirst pairSecond ^ 2)
        * hslackSum
      - slack pairSecond * hrowFirst - slack pairFirst * hrowSecond
      + 2 * correlationInvolution D pairFirst pairSecond * hchain

/-- **(C-PAIR) AT THE CRITERION POINT**: at the constant slack `2/3` the five
determinant clauses through a pair total exactly `-8/27 - (4/3) w` — strictly
negative for every edge, so through every pair at least one completion fails.
The pair-sum gate is vacuous at `(7,3)`; only its starve-feed reading survives. -/
theorem sum_involSlackDeterminant_through_pair_criterion_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {outerFirst outerSecond outerThird outerFourth hubThird pairFirst pairSecond : Fin 7}
    (hbijective : Function.Bijective ![outerFirst, outerSecond, outerThird, outerFourth,
      hubThird, pairFirst, pairSecond])
    {slack : Fin 7 → ℝ} (hconstant : ∀ index, slack index = 2 / 3) :
    involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerFirst
      + involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerSecond
      + involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerThird
      + involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerFourth
      + involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond hubThird
      = -(8 / 27) - 4 / 3 * correlationInvolution D pairFirst pairSecond ^ 2 := by
  have hslackSum : ∑ index, slack index = 14 / 3 := by
    rw [Finset.sum_congr rfl fun index _ => hconstant index, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [sum_involSlackDeterminant_through_pair_sevenThree D huniform hbijective slack hslackSum,
    hconstant pairFirst, hconstant pairSecond, pairSumValueSeven_criterionPoint]

/-- **THE STARVE-FEED IDENTITY**: the four determinant clauses through a pair and
off a chosen hub sum to the pair functional minus the hub's own clause. -/
theorem sum_involSlackDeterminant_off_hub_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {outerFirst outerSecond outerThird outerFourth hubThird pairFirst pairSecond : Fin 7}
    (hbijective : Function.Bijective ![outerFirst, outerSecond, outerThird, outerFourth,
      hubThird, pairFirst, pairSecond])
    (slack : Fin 7 → ℝ) (hslackSum : ∑ index, slack index = 14 / 3) :
    involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerFirst
      + involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerSecond
      + involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerThird
      + involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerFourth
      = pairSumValueSeven (slack pairFirst) (slack pairSecond)
          (correlationInvolution D pairFirst pairSecond ^ 2)
        - involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond
            hubThird := by
  have hpair := sum_involSlackDeterminant_through_pair_sevenThree D huniform hbijective
    slack hslackSum
  linarith [hpair]

/-- **THE STARVE-FEED GATE.**  If the hub triple `{pairFirst, pairSecond,
hubThird}` is starved — its own determinant clause at most the pair functional —
then one of the FOUR triples through the pair and off the hub has a nonnegative
determinant clause.  Since the functional is nonpositive on the box, starvation
asks the hub to fail by a definite margin; the deficit is the mixed triples'
budget. -/
theorem exists_nonneg_involSlackDeterminant_of_starvedHub_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {outerFirst outerSecond outerThird outerFourth hubThird pairFirst pairSecond : Fin 7}
    (hbijective : Function.Bijective ![outerFirst, outerSecond, outerThird, outerFourth,
      hubThird, pairFirst, pairSecond])
    (slack : Fin 7 → ℝ) (hslackSum : ∑ index, slack index = 14 / 3)
    (hstarved : involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond
        hubThird
      ≤ pairSumValueSeven (slack pairFirst) (slack pairSecond)
          (correlationInvolution D pairFirst pairSecond ^ 2)) :
    0 ≤ involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond outerFirst
      ∨ 0 ≤ involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond
          outerSecond
      ∨ 0 ≤ involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond
          outerThird
      ∨ 0 ≤ involSlackDeterminant (correlationInvolution D) slack pairFirst pairSecond
          outerFourth := by
  by_contra hcontra
  simp only [not_or, not_le] at hcontra
  obtain ⟨hfirst, hsecond, hthird, hfourth⟩ := hcontra
  have hsplit := sum_involSlackDeterminant_off_hub_sevenThree D huniform hbijective
    slack hslackSum
  linarith [hsplit, hstarved, hfirst, hsecond, hthird, hfourth]

/-- **THE STARVE-FEED GATE, ON THE DESIGN**: on an all-heavy uniform-share
`(7,3)` design, a starved hub delivers a DOMINATING triple through its pair,
provided the pair carries its pairwise clauses.  The `(7,3)` twin of the landed
`Gtz.exists_dominates_of_starvedHub`, with `Gtz.pairSumValueSeven` replacing
`Gtz.pairSumValue` and five completions replacing four. -/
theorem exists_dominates_of_starvedHub_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (hheavy : AllHeavy D)
    {outerFirst outerSecond outerThird outerFourth hubThird pairFirst pairSecond : Fin 7}
    (hbijective : Function.Bijective ![outerFirst, outerSecond, outerThird, outerFourth,
      hubThird, pairFirst, pairSecond])
    (hpair : correlationInvolution D pairFirst pairSecond ^ 2
      ≤ weightSlack D pairFirst * weightSlack D pairSecond)
    (hcrossFirst : ∀ outer : Fin 7, correlationInvolution D pairFirst outer ^ 2
      ≤ weightSlack D pairFirst * weightSlack D outer)
    (hcrossSecond : ∀ outer : Fin 7, correlationInvolution D pairSecond outer ^ 2
      ≤ weightSlack D pairSecond * weightSlack D outer)
    (hstarved : involSlackDeterminant (correlationInvolution D) (weightSlack D)
        pairFirst pairSecond hubThird
      ≤ pairSumValueSeven (weightSlack D pairFirst) (weightSlack D pairSecond)
          (correlationInvolution D pairFirst pairSecond ^ 2)) :
    ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) :=
    fun atomIndex => lt_trans zero_lt_one (hheavy atomIndex)
  have hslackSum : ∑ atomIndex, weightSlack D atomIndex = 14 / 3 := by
    have hnormalised := sum_weightSlack_of_uniformShare D (by norm_num) (by
      intro atomIndex
      rw [huniform atomIndex]
      norm_num)
    rw [hnormalised]
    norm_num
  have houter : ∀ leftSlot rightSlot : Fin 7, leftSlot ≠ rightSlot →
      ![outerFirst, outerSecond, outerThird, outerFourth, hubThird, pairFirst, pairSecond]
          leftSlot
        ≠ ![outerFirst, outerSecond, outerThird, outerFourth, hubThird, pairFirst, pairSecond]
          rightSlot :=
    fun _ _ hslot hvalue => hslot (hbijective.1 hvalue)
  have hpairDistinct : pairFirst ≠ pairSecond := houter 5 6 (by decide)
  have hbuild : ∀ outer : Fin 7, pairFirst ≠ outer → pairSecond ≠ outer →
      0 ≤ involSlackDeterminant (correlationInvolution D) (weightSlack D)
          pairFirst pairSecond outer →
      Dominates D {pairFirst, pairSecond, outer} := by
    intro outer hfirstOuter hsecondOuter hdeterminant
    refine (dominates_triple_iff_posSemidef_slackHollowThree D (hpositive pairFirst)
      (hpositive pairSecond) (hpositive outer) hpairDistinct hfirstOuter hsecondOuter).mpr ?_
    rw [← correlationInvolution_apply_of_ne D hpairDistinct,
      ← correlationInvolution_apply_of_ne D hfirstOuter,
      ← correlationInvolution_apply_of_ne D hsecondOuter,
      posSemidef_slackHollowThree_iff]
    exact ⟨(weightSlack_pos D hheavy pairFirst).le, (weightSlack_pos D hheavy pairSecond).le,
      (weightSlack_pos D hheavy outer).le, hpair, hcrossFirst outer, hcrossSecond outer,
      hdeterminant⟩
  have hcard : ∀ outer : Fin 7, pairFirst ≠ outer → pairSecond ≠ outer →
      ({pairFirst, pairSecond, outer} : Finset (Fin 7)).card = 3 := by
    intro outer hfirstOuter hsecondOuter
    rw [Finset.card_insert_of_notMem (by simp [hpairDistinct, hfirstOuter]),
      Finset.card_insert_of_notMem (by simp [hsecondOuter]), Finset.card_singleton]
  rcases exists_nonneg_involSlackDeterminant_of_starvedHub_sevenThree D huniform hbijective
    (weightSlack D) hslackSum hstarved with hfirst | hsecond | hthird | hfourth
  · exact ⟨{pairFirst, pairSecond, outerFirst},
      hcard outerFirst (houter 5 0 (by decide)) (houter 6 0 (by decide)),
      hbuild outerFirst (houter 5 0 (by decide)) (houter 6 0 (by decide)) hfirst⟩
  · exact ⟨{pairFirst, pairSecond, outerSecond},
      hcard outerSecond (houter 5 1 (by decide)) (houter 6 1 (by decide)),
      hbuild outerSecond (houter 5 1 (by decide)) (houter 6 1 (by decide)) hsecond⟩
  · exact ⟨{pairFirst, pairSecond, outerThird},
      hcard outerThird (houter 5 2 (by decide)) (houter 6 2 (by decide)),
      hbuild outerThird (houter 5 2 (by decide)) (houter 6 2 (by decide)) hthird⟩
  · exact ⟨{pairFirst, pairSecond, outerFourth},
      hcard outerFourth (houter 5 3 (by decide)) (houter 6 3 (by decide)),
      hbuild outerFourth (houter 5 3 (by decide)) (houter 6 3 (by decide)) hfourth⟩

/-! ## 9. The cross-check with the landed spectral ledger

The brief's consistency demand, as a kernel theorem: the landed minor total
(`powersetCard` form, proved from the two-valued spectrum of `Gamma`) EQUALS
this file's thirty-five-bracket total (proved from the row law and supply
chain).  Each side is evaluated by its own route — the spectral one through
`Gtz.sum_det_principalMinors_directionGramMatrix_sevenThree`, the entrywise one
through `Gtz.sum_tripleBracket_sevenThree` at the identity tuple — and the two
meet at `343/27`. -/

/-- **THE TWO DETERMINANT LEDGERS AGREE.**  The spectral principal-minor total
and the conservation-law bracket total are the same number, each proved
independently to be `343/27`. -/
theorem sum_det_principalMinors_eq_sum_tripleBracket_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 7)).powersetCard 3,
        ((directionGramMatrix D).submatrix
          (Subtype.val : { index // index ∈ selected } → Fin 7)
          (Subtype.val : { index // index ∈ selected } → Fin 7)).det
      = hollowTripleBracket (correlationInvolution D) 0 1 2
        + hollowTripleBracket (correlationInvolution D) 0 1 3
        + hollowTripleBracket (correlationInvolution D) 0 1 4
        + hollowTripleBracket (correlationInvolution D) 0 1 5
        + hollowTripleBracket (correlationInvolution D) 0 1 6
        + hollowTripleBracket (correlationInvolution D) 0 2 3
        + hollowTripleBracket (correlationInvolution D) 0 2 4
        + hollowTripleBracket (correlationInvolution D) 0 2 5
        + hollowTripleBracket (correlationInvolution D) 0 2 6
        + hollowTripleBracket (correlationInvolution D) 0 3 4
        + hollowTripleBracket (correlationInvolution D) 0 3 5
        + hollowTripleBracket (correlationInvolution D) 0 3 6
        + hollowTripleBracket (correlationInvolution D) 0 4 5
        + hollowTripleBracket (correlationInvolution D) 0 4 6
        + hollowTripleBracket (correlationInvolution D) 0 5 6
        + hollowTripleBracket (correlationInvolution D) 1 2 3
        + hollowTripleBracket (correlationInvolution D) 1 2 4
        + hollowTripleBracket (correlationInvolution D) 1 2 5
        + hollowTripleBracket (correlationInvolution D) 1 2 6
        + hollowTripleBracket (correlationInvolution D) 1 3 4
        + hollowTripleBracket (correlationInvolution D) 1 3 5
        + hollowTripleBracket (correlationInvolution D) 1 3 6
        + hollowTripleBracket (correlationInvolution D) 1 4 5
        + hollowTripleBracket (correlationInvolution D) 1 4 6
        + hollowTripleBracket (correlationInvolution D) 1 5 6
        + hollowTripleBracket (correlationInvolution D) 2 3 4
        + hollowTripleBracket (correlationInvolution D) 2 3 5
        + hollowTripleBracket (correlationInvolution D) 2 3 6
        + hollowTripleBracket (correlationInvolution D) 2 4 5
        + hollowTripleBracket (correlationInvolution D) 2 4 6
        + hollowTripleBracket (correlationInvolution D) 2 5 6
        + hollowTripleBracket (correlationInvolution D) 3 4 5
        + hollowTripleBracket (correlationInvolution D) 3 4 6
        + hollowTripleBracket (correlationInvolution D) 3 5 6
        + hollowTripleBracket (correlationInvolution D) 4 5 6 := by
  rw [sum_det_principalMinors_directionGramMatrix_sevenThree D huniform,
    sum_tripleBracket_sevenThree D huniform
      (first := 0) (second := 1) (third := 2) (fourth := 3) (fifth := 4) (sixth := 5)
      (seventh := 6) (by decide)]

end Gtz
