/-
# The residual `(6,3)` pen ledger: the determinant form of the criterion, the
# transfer law at every share, the linearized gate, and two closed routes

Five independent pen items, landed exactly, plus an honest census of which of
them the repository already carried under other names.

## PROVED here, unconditionally

**1.  The criterion is a single level set of `det + P`.**  Substituting
`det Gamma[T] = 1 - sigma_T + 2 P_T` into the shipped oriented criterion
`sigma_T - 3 P_T <= 4/9` gives

    T dominates   <->   det Gamma[T] + P_T >= 5/9,

as `Gtz.dominates_triple_iff_five_ninths_le_determinant_add_product_of_uniformShare`
(size-generic, share at least `3/7`) with the two residual cells instantiated.
The identity behind it is `ring`, and it is exact:
`directionTripleDeterminant + directionTripleProduct = 1 - orientedTripleResidual`.
BOTH tie configurations sit ON that one surface — `gamma == -1/3` gives
`16/27 - 1/27 = 5/9` and `gamma == 2/3` gives `7/27 + 8/27 = 5/9` — so the light
and heavy gate endpoints are ONE level set, not two.  Sharper still: on the
equilateral line the criterion cubic factors as

    27 t^3 - 27 t^2 + 4 = (3 t + 1) (3 t - 2)^2,

a SIMPLE root at the light tie and a DOUBLE root at the heavy tie, mirroring the
shipped `Gtz.bandGateCubic_factorisation` on the edge-weight axis.  As a
by-product the shipped name `Gtz.directionTripleDeterminant` is justified for the
first time: it really is `Matrix.det` of the `3 x 3` Gram compression
(`Gtz.det_directionGramMatrix_submatrix_three_eq_directionTripleDeterminant`).

**2.  The transfer law, at EVERY share.**  For any design of uniform share `s`
and any pair `{p,q}`,

    sum over ALL atoms l of P_{p q l}  =  s^{-1} w_pq ,
    sum over l outside {p,q} of P_{p q l}  =  (s^{-1} - 2) w_pq .

At `(6,3)` the share is `1/2` and the coefficient is `0` — that is why the pen's
`(6,3)` conservation laws hold.  At `(7,3)` the share is `3/7` and the
coefficient is `1/3`, so the SAME law reads `(1/3) w_pq`, not `0`: the vanishing
is a coincidence of the share, not a structural fact, and the one-line proof
exhibits exactly where six is special.  Read inside a `3 heavy + 3 light` split
with heavy side `{p, q, h}` the `(6,3)` case gives
`P_H = - (P_{pql1} + P_{pql2} + P_{pql3})`, hence a heavy triple of frustration
`pi` forces one mixed triple to carry `P >= pi/3` — an exact general-frame
product floor, no estimate.  SHARPENING OF THE PEN: the frustration hypothesis
`P_H <= 0` is NOT needed for the pigeonhole, only for reading the floor as
nonnegative, so `Gtz.exists_mixed_directionTripleProduct_ge_third_of_heavyTriple`
carries no sign hypothesis at all.  The cancellation is genuine and not termwise:
at the icosahedron every oriented triple product has square exactly `1/125`, and
the four products off any pair still sum to zero.

**3.  The linearized gate, eigenvalue-free.**  For EVERY unit-diagonal `3 x 3`
correlation matrix `R` on the elliptope,

    R  -  (4/9) (det R) . 1   is positive semidefinite,

i.e. `lambda_min(R) >= (4/9) det R` with no eigenvalue, no interlacing and no
matrix square root.  The proof is an exact factorisation,

    det(R - (4/9) B . 1) = (4/9) B (1/4 + (1/3) B - (16/81) B^2 + 2 P),   B = det R,

whose bracket is nonnegative because `B` lies in `[0,1]` and `P >= -1/8` on the
elliptope.  That product floor `P >= -1/8` is itself new here in its general
form (the tree carried it only inside the box `gamma^2 <= 1/4`).  Its equality set
is NOT the single point `gamma == -1/2`: it is the FOUR Mercedes points — the sign
patterns of `(1/2, 1/2, 1/2)` with an ODD number of minus signs, one geometric
configuration (the `M(K4)` heavy triangle) up to vector sign flips — enumerated by
the shipped `Gtz.elliptopeBracket_eq_zero_iff_mercedesPoint`.  Attainment at those
four points is arithmetic, but NO theorem here states it, so read `sharp` as a
claim about the constant, not as a landed result.  Composing the
gate with the shipped determinant-mass identities gives the pen's two constants:
`8/45` from a five-set (`det >= 2/5`) and `(2/9)(1 - w_pq)` from a four-set
(`det >= (1 - w_pq)/2`).  The five-set constant is wired all the way to designs:
on an equal-share `(6,3)` design some triple avoiding any prescribed atom has its
Gram compression above `(8/45) . 1`
(`Gtz.exists_gateTriple_avoiding_sixThree`).

**4.  The Radon step, in its dimension-free form, at THREE and at FIVE.**  Three
unit vectors carrying a strictly positive vanishing combination have a pair at
inner product at most `-1/2` — 120 degrees, sharp at the Mercedes frame, and true
in every ambient dimension, no plane and no angle.  Five such vectors have a pair
at most `-1/4`, by the same norm certificate against Cauchy-Schwarz.  Five is the
count the pen's `(6,3)` application needs, and `-1/4` is exactly as far as the
certificate reaches — see the wall below.

**5.  Two closed routes, with their exact miss constants.**  The deletion
averaging floor `7/18 - (1/6) s` equals `1/3` exactly on the cone boundary
`s = 1/3` and falls to `2/9` at the pole, a deficit of exactly `1/9`; after
averaging the four deletions the collapse `(23/24) x = 7/24` pins `x = 7/23`,
and `1/3 - 7/23 = 2/69 > 0`.  So deletion-averaging misses `(7,3)` by exactly
`2/69` even granting `(6,3)` in full.

## HYPOTHESIS in every statement that carries one

Item 1's criterion inherits the shipped hypotheses verbatim: rank three, uniform
share at least `3/7`, and leverage exactly three at the three atoms of the
triple.  Item 2's transfer law needs only uniform positive share; the `(6,3)`
reading additionally needs the six-tuple bijection.  Item 3 needs only that the
three correlations form an elliptope point.  Item 5 is pure arithmetic on the
pen's constants.

## NOT PROVED, stated so silence is not read as closure

* Item 5 mechanizes the pen's CONSTANTS and their collapse, not the geometric
  derivation that produces `S_T >= (7/18) 1 - (1/6) u_d u_d^T` from a deletion.
  The conclusion landed is therefore "the arithmetic of this route closes at
  `7/23`, missing `1/3` by `2/69`", not "the route is the best possible".
* Item 4's `(6,3)` APPLICATION is WALLED, and both sides of the wall are theorems.
  The pen reads the Radon step on FIVE planar projections at doubled angles and
  claims two lines at least 60 degrees apart, i.e. a doubled-angle correlation at
  most `-1/2`.  The norm certificate at count five is proved here and delivers
  `-1/4`, NOT `-1/2`
  (`Gtz.exists_dotProduct_le_neg_quarter_of_fiveTermVanishingCombination`) —
  lines at least about 52.2 degrees apart, not 60.  Sharpness of `-1/4` is NOT
  landed here, only evidenced: `Gtz.posSemidef_equalCorrelationFiveGram` and
  `Gtz.equalCorrelationFiveGram_mulVec_ones_eq_zero` exhibit a GRAM MATRIX — unit
  diagonal, every off-diagonal `-1/4`, all-ones vector in the kernel — not five
  vectors.  The passage from that Gram to an actual five-vector family, the
  statement that every pair sits at `-1/4`, and the rank-four claim below are all
  UNMECHANIZED; `Gtz.fiveTermCertificate_symmetricValue` is a bare `ring` identity
  whose link to the certificate is prose.  Granting those (they are true: the
  spectrum is `{0, 5/4, 5/4, 5/4, 5/4}`), the configuration has Gram rank four and
  so is not planar, and the pen's
  `-1/2` is not a sharpening of the dimension-free argument, it strictly consumes
  the rank-two hypothesis the norm certificate never touches.  Closing the pen's
  constant needs the largest-angular-gap argument, a cyclic sort of the five
  doubled arguments, which is not mechanized anywhere in this repository.  The
  residue is exactly the interval from `-1/4` to `-1/2`
  (`Gtz.radonFiveDirectionGap`).  Also NOT proved here: that the five planar
  projections of a `(6,3)` design with a parallel pair actually satisfy a
  positive-weight vanishing combination at doubled angles.  That is the geometric
  input the lemma consumes, and it is a hypothesis, not a conclusion.
* The four-set constant `(2/9)(1 - w_pq)` is landed only at the level of the
  correlation matrix of a triple whose determinant is bounded.  Its design-side
  wiring would need the shipped
  `Gtz.IsHollowInvolution.exists_tripleBracket_ge_fourSet` branch selection, which
  returns a four-fold disjunction rather than an existential and is therefore not
  a one-line composition; it is not performed here.  The five-set constant `8/45`
  IS wired (`Gtz.exists_gateTriple_avoiding_sixThree`).
* Nothing here says the `8/45` floor suffices for domination.  The domination
  threshold in this coordinate is `det + P >= 5/9` (item 1), and a spectral floor
  of `8/45` does not by itself reach it.  The gate is an input to a covering
  argument, not a covering argument.

## ALREADY IN THE TREE — reported, not duplicated

The pen's `(6,3)` COHERENCE CONSERVATION half is landed, and this file does not
restate it.  The vanishing laws are
`Gtz.IsHollowInvolution.sum_pairTripleProduct_eq_zero` (triples through a pair),
`…sum_vertexTripleProduct_eq_zero` (triples through an atom),
`…sum_tripleProduct_ordered_eq_zero` (all triples), with the six-tuple readings
`Gtz.IsHollowInvolution.sum_tripleProduct_throughPair`, `…_six`, `…_fiveSet`,
`…_fourSet`, and the design-side twins
`Gtz.sum_directionGram_chain_through_pair` and
`Gtz.sum_directionTripleProduct_within_quadruple_eq_zero`.  What was missing is
only the share-generic form and the heavy-pair pigeonhole, which is what item 2
adds.  Item 4's `V5` planar rigidity is landed and STRICTLY STRONGER than the
pen's version in `Gtz/Quantitative/PlanarTightFrameRigidity.lean`
(`Gtz.exists_orthogonalMatching_of_unitTightFamily`, no distinctness, any rank);
nothing here weakens it.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.RhoNormalForm
import Gtz.LinAlg.ElliptopeInterval
import Gtz.Reduction.PrincipalMinorsThree
import Gtz.Quantitative.CheapAtomGate
import Gtz.Quantitative.SevenThreeCapsGates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1.  The criterion as one level set of `det + P` -/

/-- **THE SUBSTITUTION, IN SCALARS.**  `det + P = 1 - (sigma - 3P)`: the elliptope
bracket plus the oriented product is one minus the oriented criterion value.  Pure
`ring`; it is the whole of item 1. -/
theorem elliptopeBracket_add_product_eq_one_sub_orientedResidual
    (rhoFirst rhoSecond rhoThird : ℝ) :
    elliptopeBracket rhoFirst rhoSecond rhoThird + rhoFirst * rhoSecond * rhoThird
      = 1 - (rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2
          - 3 * (rhoFirst * rhoSecond * rhoThird)) := by
  rw [elliptopeBracket]
  ring

/-- **THE SUBSTITUTION, AT A DESIGN TRIPLE.**  The shipped Gram determinant plus the
shipped oriented product is one minus the shipped oriented criterion value. -/
theorem directionTripleDeterminant_add_product_eq_one_sub_orientedTripleResidual
    (D : WeightedDesign m k) (first second third : Fin m) :
    directionTripleDeterminant D first second third
        + directionTripleProduct D first second third
      = 1 - orientedTripleResidual D first second third := by
  rw [directionTripleDeterminant, directionTripleSigma, orientedTripleResidual, edgeWeight,
    edgeWeight, edgeWeight, directionTripleProduct]
  ring

/-- The criterion threshold `4/9` on the oriented residual IS the threshold `5/9` on
`det + P`. -/
theorem orientedTripleResidual_le_four_ninths_iff_five_ninths_le_determinant_add_product
    (D : WeightedDesign m k) (first second third : Fin m) :
    orientedTripleResidual D first second third ≤ 4 / 9
      ↔ 5 / 9 ≤ directionTripleDeterminant D first second third
          + directionTripleProduct D first second third := by
  rw [directionTripleDeterminant_add_product_eq_one_sub_orientedTripleResidual]
  constructor <;> intro hbound <;> linarith

/-- **(C1-IFF) IN DETERMINANT FORM, the master statement.**  On a rank-three design of
uniform share at least `3/7`, a triple of distinct leverage-three atoms dominates if
and only if its Gram determinant plus its oriented product reaches `5/9`.  Same
hypotheses as the shipped
`Gtz.dominates_triple_iff_orientedTripleResidual_le_four_ninths_of_uniformShare`; only
the coordinate changes, and it changes to the one in which both tie configurations
coincide. -/
theorem dominates_triple_iff_five_ninths_le_determinant_add_product_of_uniformShare
    (D : WeightedDesign m 3) {shareValue : ℝ}
    (hshare : ∀ atomIndex, atomShare D atomIndex = shareValue) (hfloor : 3 / 7 ≤ shareValue)
    {first second third : Fin m} (hlevFirst : leverageOf (D.atom first) = 3)
    (hlevSecond : leverageOf (D.atom second) = 3) (hlevThird : leverageOf (D.atom third) = 3)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Dominates D {first, second, third}
      ↔ 5 / 9 ≤ directionTripleDeterminant D first second third
          + directionTripleProduct D first second third := by
  rw [dominates_triple_iff_orientedTripleResidual_le_four_ninths_of_uniformShare D hshare hfloor
      hlevFirst hlevSecond hlevThird hfirstSecond hfirstThird hsecondThird,
    orientedTripleResidual_le_four_ninths_iff_five_ninths_le_determinant_add_product]

/-- **(C1-IFF) IN DETERMINANT FORM AT `(6,3)`**, the equal-share cell of this lane. -/
theorem dominates_triple_iff_five_ninths_le_determinant_add_product_sixThree
    (D : WeightedDesign 6 3) (hshare : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {first second third : Fin 6} (hlevFirst : leverageOf (D.atom first) = 3)
    (hlevSecond : leverageOf (D.atom second) = 3) (hlevThird : leverageOf (D.atom third) = 3)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Dominates D {first, second, third}
      ↔ 5 / 9 ≤ directionTripleDeterminant D first second third
          + directionTripleProduct D first second third :=
  dominates_triple_iff_five_ninths_le_determinant_add_product_of_uniformShare D hshare
    (by norm_num) hlevFirst hlevSecond hlevThird hfirstSecond hfirstThird hsecondThird

/-- **(C1-IFF) IN DETERMINANT FORM AT `(7,3)`**, the global frontier cell. -/
theorem dominates_triple_iff_five_ninths_le_determinant_add_product_sevenThree
    (D : WeightedDesign 7 3) (hshare : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third : Fin 7} (hlevFirst : leverageOf (D.atom first) = 3)
    (hlevSecond : leverageOf (D.atom second) = 3) (hlevThird : leverageOf (D.atom third) = 3)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Dominates D {first, second, third}
      ↔ 5 / 9 ≤ directionTripleDeterminant D first second third
          + directionTripleProduct D first second third :=
  dominates_triple_iff_five_ninths_le_determinant_add_product_of_uniformShare D hshare
    (le_refl _) hlevFirst hlevSecond hlevThird hfirstSecond hfirstThird hsecondThird

/-! ### The shipped determinant name, justified

`Gtz.directionTripleDeterminant` is DEFINED as `1 - sigma + 2P`.  Nothing in the tree
identified it with `Matrix.det` of anything.  It is the determinant of the `3 x 3`
principal compression of the direction Gram, which is what makes item 1 a statement
about a determinant rather than about a polynomial that happens to be named one. -/

/-- **THE NAME IS EARNED.**  The shipped `directionTripleDeterminant` is `Matrix.det`
of the direction Gram's principal `3 x 3` compression at the triple.  Triple-local
nondegeneracy only. -/
theorem det_directionGramMatrix_submatrix_three_eq_directionTripleDeterminant
    (D : WeightedDesign m k) {first second third : Fin m}
    (hfirst : 0 < leverageOf (D.atom first)) (hsecond : 0 < leverageOf (D.atom second))
    (hthird : 0 < leverageOf (D.atom third)) :
    ((directionGramMatrix D).submatrix ![first, second, third] ![first, second, third]).det
      = directionTripleDeterminant D first second third := by
  rw [directionGramMatrix_submatrix_three_eq_correlationMatrixThree D hfirst hsecond hthird,
    det_correlationMatrixThree, elliptopeBracket, directionTripleDeterminant,
    directionTripleSigma, directionTripleProduct]
  ring

/-- The compression's determinant is nonnegative: it is a principal minor of a Gram
matrix. -/
theorem directionTripleDeterminant_nonneg (D : WeightedDesign m k) {first second third : Fin m}
    (hfirst : 0 < leverageOf (D.atom first)) (hsecond : 0 < leverageOf (D.atom second))
    (hthird : 0 < leverageOf (D.atom third)) :
    0 ≤ directionTripleDeterminant D first second third := by
  rw [← det_directionGramMatrix_submatrix_three_eq_directionTripleDeterminant D hfirst hsecond
    hthird]
  exact ((posSemidef_directionGramMatrix D).submatrix ![first, second, third]).det_nonneg

/-! ### Both ties sit on the one surface -/

/-- **THE TETRAHEDRAL TIE IS ON THE `5/9` SURFACE.**  `gamma == -1/3` gives
`det = 16/27` and `P = -1/27`, and `16/27 - 1/27 = 5/9`. -/
theorem elliptopeBracket_add_product_at_tetrahedralTie :
    elliptopeBracket (-(1 / 3) : ℝ) (-(1 / 3)) (-(1 / 3))
        + (-(1 / 3) : ℝ) * (-(1 / 3)) * (-(1 / 3)) = 5 / 9 := by
  rw [elliptopeBracket]
  norm_num

/-- **THE HEAVY TIE IS ON THE SAME SURFACE.**  `gamma == 2/3` gives `det = 7/27` and
`P = 8/27`, and `7/27 + 8/27 = 5/9`.  The light and heavy gate endpoints are ONE level
set of `det + P`, not two thresholds. -/
theorem elliptopeBracket_add_product_at_heavyTie :
    elliptopeBracket ((2 : ℝ) / 3) (2 / 3) (2 / 3) + ((2 : ℝ) / 3) * (2 / 3) * (2 / 3)
      = 5 / 9 := by
  rw [elliptopeBracket]
  norm_num

/-- **ONE SURFACE, BOTH ENDPOINTS**, as a single statement: the two tie
configurations of the `(6,3)`/`(7,3)` gates evaluate the criterion coordinate to the
SAME number. -/
theorem elliptopeBracket_add_product_tetrahedralTie_eq_heavyTie :
    elliptopeBracket (-(1 / 3) : ℝ) (-(1 / 3)) (-(1 / 3))
        + (-(1 / 3) : ℝ) * (-(1 / 3)) * (-(1 / 3))
      = elliptopeBracket ((2 : ℝ) / 3) (2 / 3) (2 / 3)
          + ((2 : ℝ) / 3) * (2 / 3) * (2 / 3) := by
  rw [elliptopeBracket_add_product_at_tetrahedralTie, elliptopeBracket_add_product_at_heavyTie]

/-- **THE EQUILATERAL CRITERION CUBIC FACTORS.**  On the line `gamma == t` the
criterion `det + P >= 5/9` reads `27 t^3 - 27 t^2 + 4 >= 0`, and that cubic is
`(3t + 1)(3t - 2)^2`: a SIMPLE root at the light tie `-1/3` and a DOUBLE root at the
heavy tie `2/3`.  The same simple/double pattern the shipped
`Gtz.bandGateCubic_factorisation` exhibits on the edge-weight axis, now on the
correlation axis. -/
theorem equilateralCriterionCubic_factorisation (edgeCosine : ℝ) :
    27 * edgeCosine ^ 3 - 27 * edgeCosine ^ 2 + 4
      = (3 * edgeCosine + 1) * (3 * edgeCosine - 2) ^ 2 := by
  ring

/-- The equilateral criterion coordinate, in closed form: `det + P - 5/9` is
`(1/9)(3t + 1)(3t - 2)^2`.  Nonnegative exactly for `t >= -1/3`, so on the
equilateral line the criterion is an interval condition with the heavy tie an
isolated tangency. -/
theorem elliptopeBracket_add_product_equilateral_sub_five_ninths (edgeCosine : ℝ) :
    elliptopeBracket edgeCosine edgeCosine edgeCosine
        + edgeCosine * edgeCosine * edgeCosine - 5 / 9
      = (1 / 9) * ((3 * edgeCosine + 1) * (3 * edgeCosine - 2) ^ 2) := by
  rw [elliptopeBracket]
  ring

/-! ## 2.  The transfer law, at every share

The frame law `sum_c s_c gamma_{pc} gamma_{cq} = gamma_{pq}` multiplied through by
`gamma_{pq}` IS the pen's coherence transfer law, and it holds at every share.  The
tree's `(6,3)` versions run through the hollow-involution square `M M = 1`, which
exists only at share one half; this route does not, so it also produces the `(7,3)`
value and exhibits what makes six special. -/

/-- **THE TRANSFER LAW, MASTER FORM.**  Summed over ALL atoms, the oriented products
through a pair total `s^{-1}` times the pair's edge weight.  No distinctness, no
nondegeneracy, any size, any rank, any positive uniform share. -/
theorem sum_directionTripleProduct_eq_inv_share_mul_edgeWeight (D : WeightedDesign m k)
    {shareValue : ℝ} (hshare : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hpositive : 0 < shareValue) (pairFirst pairSecond : Fin m) :
    ∑ otherIndex, directionTripleProduct D pairFirst pairSecond otherIndex
      = shareValue⁻¹ * edgeWeight D pairFirst pairSecond := by
  have hmaster := sum_atomShare_mul_directionGram_mul_directionGram D pairFirst pairSecond
  rw [Finset.sum_congr rfl fun otherIndex _ => by rw [hshare otherIndex], ← Finset.mul_sum]
    at hmaster
  have hchain : ∑ otherIndex, directionGram D pairFirst otherIndex
        * directionGram D otherIndex pairSecond
      = shareValue⁻¹ * directionGram D pairFirst pairSecond := by
    rw [← hmaster, inv_mul_cancel_left₀ (ne_of_gt hpositive)]
  calc ∑ otherIndex, directionTripleProduct D pairFirst pairSecond otherIndex
      = directionGram D pairFirst pairSecond
          * ∑ otherIndex, directionGram D pairFirst otherIndex
              * directionGram D otherIndex pairSecond := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun otherIndex _ => by
          rw [directionTripleProduct, directionGram_comm D pairSecond otherIndex]; ring
    _ = directionGram D pairFirst pairSecond
          * (shareValue⁻¹ * directionGram D pairFirst pairSecond) := by rw [hchain]
    _ = shareValue⁻¹ * edgeWeight D pairFirst pairSecond := by rw [edgeWeight]; ring

/-- **THE TRANSFER LAW, OFF-PAIR FORM.**  Deleting the two degenerate terms, the
oriented products through a DISTINCT pair total `(s^{-1} - 2) w_pq`.  This is the
coefficient the pen's conservation half depends on. -/
theorem sum_directionTripleProduct_off_pair_eq (D : WeightedDesign m k)
    {shareValue : ℝ} (hshare : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hpositive : 0 < shareValue) {pairFirst pairSecond : Fin m}
    (hdistinct : pairFirst ≠ pairSecond) :
    ∑ otherIndex ∈ (Finset.univ.erase pairFirst).erase pairSecond,
        directionTripleProduct D pairFirst pairSecond otherIndex
      = (shareValue⁻¹ - 2) * edgeWeight D pairFirst pairSecond := by
  have hleverageFirst : 0 < leverageOf (D.atom pairFirst) :=
    leverageOf_pos_of_atomShare_pos D (by rw [hshare pairFirst]; exact hpositive)
  have hleverageSecond : 0 < leverageOf (D.atom pairSecond) :=
    leverageOf_pos_of_atomShare_pos D (by rw [hshare pairSecond]; exact hpositive)
  have htotal := sum_directionTripleProduct_eq_inv_share_mul_edgeWeight D hshare hpositive
    pairFirst pairSecond
  have hatFirst : directionTripleProduct D pairFirst pairSecond pairFirst
      = edgeWeight D pairFirst pairSecond := by
    rw [directionTripleProduct, directionGram_self D hleverageFirst,
      directionGram_comm D pairSecond pairFirst, edgeWeight]
    ring
  have hatSecond : directionTripleProduct D pairFirst pairSecond pairSecond
      = edgeWeight D pairFirst pairSecond := by
    rw [directionTripleProduct, directionGram_self D hleverageSecond, edgeWeight]
    ring
  have hsplitSecond : ∑ otherIndex ∈ Finset.univ.erase pairFirst,
        directionTripleProduct D pairFirst pairSecond otherIndex
      = ∑ otherIndex ∈ (Finset.univ.erase pairFirst).erase pairSecond,
          directionTripleProduct D pairFirst pairSecond otherIndex
        + directionTripleProduct D pairFirst pairSecond pairSecond :=
    (Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hdistinct.symm, Finset.mem_univ _⟩)).symm
  have hsplitFirst : ∑ otherIndex, directionTripleProduct D pairFirst pairSecond otherIndex
      = ∑ otherIndex ∈ Finset.univ.erase pairFirst,
          directionTripleProduct D pairFirst pairSecond otherIndex
        + directionTripleProduct D pairFirst pairSecond pairFirst :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
  rw [hsplitFirst, hsplitSecond, hatFirst, hatSecond] at htotal
  linarith [htotal]

/-- **AT `(6,3)` THE COEFFICIENT IS ZERO.**  Share one half gives `s^{-1} - 2 = 0`, so
the oriented products through any distinct pair cancel exactly.  This is the
share-generic explanation of the pen's `(6,3)` conservation laws — the tree proves the
same vanishing through the hollow involution `M M = 1`, which exists only here. -/
theorem sum_directionTripleProduct_off_pair_eq_zero_sixThree (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {pairFirst pairSecond : Fin 6} (hdistinct : pairFirst ≠ pairSecond) :
    ∑ otherIndex ∈ (Finset.univ.erase pairFirst).erase pairSecond,
        directionTripleProduct D pairFirst pairSecond otherIndex = 0 := by
  rw [sum_directionTripleProduct_off_pair_eq D huniform (by norm_num) hdistinct]
  norm_num

/-- **AT `(7,3)` THE COEFFICIENT IS ONE THIRD, NOT ZERO.**  Share `3/7` gives
`s^{-1} - 2 = 1/3`, so the same law reads `(1/3) w_pq`.  The `(6,3)` vanishing is a
coincidence of the share; nothing structural transports. -/
theorem sum_directionTripleProduct_off_pair_eq_third_mul_edgeWeight_sevenThree
    (D : WeightedDesign 7 3) (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pairFirst pairSecond : Fin 7} (hdistinct : pairFirst ≠ pairSecond) :
    ∑ otherIndex ∈ (Finset.univ.erase pairFirst).erase pairSecond,
        directionTripleProduct D pairFirst pairSecond otherIndex
      = (1 / 3) * edgeWeight D pairFirst pairSecond := by
  rw [sum_directionTripleProduct_off_pair_eq D huniform (by norm_num) hdistinct]
  norm_num

/-! ### The transfer law is genuine cancellation: the icosahedral fibre

Every icosahedral edge weight is `1/5`, so every oriented triple product has square
`1/125` — no term vanishes.  Yet the four terms off any pair sum to zero exactly.  The
`(6,3)` vanishing is therefore a real cancellation, not a termwise triviality, and the
hypothesis set of the transfer law is inhabited. -/

/-- Every icosahedral triple has oriented product of square `1/125`: three edge weights
of `1/5` each.  Nothing vanishes. -/
theorem sq_directionTripleProduct_icosaDesign {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    directionTripleProduct icosaDesign first second third ^ 2 = 1 / 125 := by
  rw [directionTripleProduct,
    show (directionGram icosaDesign first second * directionGram icosaDesign first third
          * directionGram icosaDesign second third) ^ 2
        = directionGram icosaDesign first second ^ 2 * directionGram icosaDesign first third ^ 2
          * directionGram icosaDesign second third ^ 2 from by ring,
    sq_directionGram_icosaDesign hfirstSecond, sq_directionGram_icosaDesign hfirstThird,
    sq_directionGram_icosaDesign hsecondThird]
  norm_num

/-- **THE CANCELLATION, WITNESSED.**  At the icosahedron the four oriented products off
any pair sum to zero while each has square `1/125`. -/
theorem sum_directionTripleProduct_off_pair_eq_zero_icosaDesign
    {pairFirst pairSecond : Fin 6} (hdistinct : pairFirst ≠ pairSecond) :
    ∑ otherIndex ∈ (Finset.univ.erase pairFirst).erase pairSecond,
        directionTripleProduct icosaDesign pairFirst pairSecond otherIndex = 0 :=
  sum_directionTripleProduct_off_pair_eq_zero_sixThree icosaDesign atomShare_icosaDesign hdistinct

/-- The master transfer law at the icosahedron: summed over ALL six atoms the products
through a pair total `2 w_pq = 2/5`, of which the two degenerate terms supply everything
and the four live terms supply nothing. -/
theorem sum_directionTripleProduct_eq_two_fifths_icosaDesign (pairFirst pairSecond : Fin 6)
    (hdistinct : pairFirst ≠ pairSecond) :
    ∑ otherIndex, directionTripleProduct icosaDesign pairFirst pairSecond otherIndex = 2 / 5 := by
  rw [sum_directionTripleProduct_eq_inv_share_mul_edgeWeight icosaDesign atomShare_icosaDesign
      (by norm_num) pairFirst pairSecond, edgeWeight, sq_directionGram_icosaDesign hdistinct]
  norm_num

/-! ### The heavy-pair reading and the exact product floor -/

/-- **THE HEAVY TRIPLE IS MINUS THE MIXED MASS.**  At `(6,3)` equal share, for a heavy
side `{p, q, h}` and light side `{l1, l2, l3}`, the oriented product of the heavy
triple is the negative of the three mixed products over the heavy pair `{p, q}`.  Exact
identity, no estimate. -/
theorem directionTripleProduct_heavy_eq_neg_sum_mixed (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {heavyThird lightFirst lightSecond lightThird pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![heavyThird, lightFirst, lightSecond, lightThird, pairFirst, pairSecond]) :
    directionTripleProduct D pairFirst pairSecond heavyThird
      = -(directionTripleProduct D pairFirst pairSecond lightFirst
          + directionTripleProduct D pairFirst pairSecond lightSecond
          + directionTripleProduct D pairFirst pairSecond lightThird) := by
  have hchain := sum_directionGram_chain_through_pair D huniform hbijective
  simp only [directionTripleProduct]
  rw [directionGram_comm D pairSecond heavyThird, directionGram_comm D pairSecond lightFirst,
    directionGram_comm D pairSecond lightSecond, directionGram_comm D pairSecond lightThird]
  linear_combination directionGram D pairFirst pairSecond * hchain

/-- **THE EXACT PRODUCT FLOOR, WITHOUT THE FRUSTRATION HYPOTHESIS.**  One of the three
mixed triples over a heavy pair carries at least a third of the heavy triple's
frustration.  The pen states this for a FRUSTRATED heavy triple; the hypothesis is not
needed — the pigeonhole runs on the identity alone and holds at every sign of `P_H`.
An identity plus a pigeonhole, not an estimate. -/
theorem exists_mixed_directionTripleProduct_ge_third_of_heavyTriple
    (D : WeightedDesign 6 3) (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {heavyThird lightFirst lightSecond lightThird pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![heavyThird, lightFirst, lightSecond, lightThird, pairFirst, pairSecond]) :
    -directionTripleProduct D pairFirst pairSecond heavyThird / 3
        ≤ directionTripleProduct D pairFirst pairSecond lightFirst
      ∨ -directionTripleProduct D pairFirst pairSecond heavyThird / 3
        ≤ directionTripleProduct D pairFirst pairSecond lightSecond
      ∨ -directionTripleProduct D pairFirst pairSecond heavyThird / 3
        ≤ directionTripleProduct D pairFirst pairSecond lightThird := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hfirstLow, hsecondLow, hthirdLow⟩ := hcontra
  have htransfer := directionTripleProduct_heavy_eq_neg_sum_mixed D huniform hbijective
  linarith [hfirstLow, hsecondLow, hthirdLow, htransfer]

/-- **THE PEN'S FORM.**  When the heavy triple is frustrated with `|P_H| = pi`, the
carrier the pigeonhole selects has a NONNEGATIVE product of magnitude at least `pi/3`,
so the mixed coherent mass over each heavy pair is genuinely there.  Immediate from the
unconditional statement plus the sign hypothesis. -/
theorem exists_mixed_directionTripleProduct_ge_third_nonneg_of_frustratedHeavy
    (D : WeightedDesign 6 3) (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {heavyThird lightFirst lightSecond lightThird pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![heavyThird, lightFirst, lightSecond, lightThird, pairFirst, pairSecond])
    (hfrustrated : directionTripleProduct D pairFirst pairSecond heavyThird ≤ 0) :
    ∃ carrier : Fin 6, (carrier = lightFirst ∨ carrier = lightSecond ∨ carrier = lightThird)
      ∧ 0 ≤ directionTripleProduct D pairFirst pairSecond carrier
      ∧ -directionTripleProduct D pairFirst pairSecond heavyThird / 3
        ≤ directionTripleProduct D pairFirst pairSecond carrier := by
  have hfloorNonneg : 0 ≤ -directionTripleProduct D pairFirst pairSecond heavyThird / 3 := by
    linarith
  rcases exists_mixed_directionTripleProduct_ge_third_of_heavyTriple D huniform hbijective with
    hfirst | hsecond | hthird
  · exact ⟨lightFirst, Or.inl rfl, le_trans hfloorNonneg hfirst, hfirst⟩
  · exact ⟨lightSecond, Or.inr (Or.inl rfl), le_trans hfloorNonneg hsecond, hsecond⟩
  · exact ⟨lightThird, Or.inr (Or.inr rfl), le_trans hfloorNonneg hthird, hthird⟩

/-! ## 3.  The linearized gate: `lambda_min(R) >= (4/9) det R`, eigenvalue-free

Mathlib at this revision has no sorted spectrum, no interlacing and no positive
semidefinite square root, so a `lambda_min` bound must be stated as a positive
semidefinite shift.  That is what is proved, and the certificate is an exact
factorisation of the shifted determinant. -/

/-- The three-variable arithmetic-geometric mean in polynomial form, with the exact
Schur-style certificate rather than a search. -/
private theorem twentySeven_mul_prod_le_cube {firstValue secondValue thirdValue : ℝ}
    (hfirst : 0 ≤ firstValue) (hsecond : 0 ≤ secondValue) (hthird : 0 ≤ thirdValue) :
    27 * (firstValue * secondValue * thirdValue)
      ≤ (firstValue + secondValue + thirdValue) ^ 3 := by
  have hspread : 0 ≤ (firstValue + secondValue + thirdValue)
      * ((firstValue - secondValue) ^ 2 + (secondValue - thirdValue) ^ 2
        + (thirdValue - firstValue) ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  have hfirstTerm : 0 ≤ firstValue * (secondValue - thirdValue) ^ 2 :=
    mul_nonneg hfirst (sq_nonneg _)
  have hsecondTerm : 0 ≤ secondValue * (thirdValue - firstValue) ^ 2 :=
    mul_nonneg hsecond (sq_nonneg _)
  have hthirdTerm : 0 ≤ thirdValue * (firstValue - secondValue) ^ 2 :=
    mul_nonneg hthird (sq_nonneg _)
  nlinarith [hspread, hfirstTerm, hsecondTerm, hthirdTerm]

/-- **THE ORIENTED PRODUCT FLOOR.**  Every triple of nonnegative bracket has
`gamma_1 gamma_2 gamma_3 >= -1/8`.  The hypothesis is `0 <= elliptopeBracket` ALONE —
compatibility is not needed, so this is strictly larger than the elliptope.  The tree
carried the constant only inside the box `gamma^2 <= 1/4`
(`Gtz.elliptopeBracket_eq_zero_iff_mercedes`).

Equality is NOT confined to `gamma == -1/2`.  Forcing equality in both certificate
steps pins `sigma = 3/4` and `gamma_i^2 = 1/4`, so the equality set is the FOUR
Mercedes points (odd number of minus signs among `+-1/2`), which the shipped
`Gtz.elliptopeBracket_eq_zero_iff_mercedesPoint` enumerates; they are one geometric
configuration, the `M(K4)` heavy triangle, up to vector sign flips.  Attainment is
not landed as a theorem here.

Certificate: the bracket gives `sigma <= 1 + 2P`, arithmetic-geometric mean gives
`27 P^2 <= sigma^3`, and `(1 + 2P)^3 - 27 P^2 = (8P + 1)(P - 1)^2`. -/
theorem elliptopeBracket_product_ge_neg_eighth {rhoFirst rhoSecond rhoThird : ℝ}
    (hbracket : 0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird) :
    -(1 / 8 : ℝ) ≤ rhoFirst * rhoSecond * rhoThird := by
  rcases le_or_gt 0 (rhoFirst * rhoSecond * rhoThird) with hcoherent | hfrustrated
  · linarith
  · have hmassNonneg : 0 ≤ rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2 := by positivity
    have hmass : rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2
        ≤ 1 + 2 * (rhoFirst * rhoSecond * rhoThird) := by
      rw [elliptopeBracket] at hbracket
      linarith
    have hcapNonneg : 0 ≤ 1 + 2 * (rhoFirst * rhoSecond * rhoThird) :=
      le_trans hmassNonneg hmass
    have hamgm : 27 * (rhoFirst ^ 2 * rhoSecond ^ 2 * rhoThird ^ 2)
        ≤ (rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2) ^ 3 :=
      twentySeven_mul_prod_le_cube (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
    have hcube : (rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2) ^ 3
        ≤ (1 + 2 * (rhoFirst * rhoSecond * rhoThird)) ^ 3 :=
      pow_le_pow_left₀ hmassNonneg hmass 3
    have hfactor : 0 ≤ (8 * (rhoFirst * rhoSecond * rhoThird) + 1)
        * (rhoFirst * rhoSecond * rhoThird - 1) ^ 2 := by
      nlinarith [hamgm, hcube]
    have hsquarePos : 0 < (rhoFirst * rhoSecond * rhoThird - 1) ^ 2 := by
      nlinarith [hfrustrated, sq_nonneg (rhoFirst * rhoSecond * rhoThird)]
    nlinarith [hfactor, hsquarePos]

/-- The bracket never exceeds the deficit of any one edge — the `3 x 3` Fischer bound in
scalars.  Exact certificate `B - (1 - r^2) = -(s - r t)^2 - t^2 (1 - r^2)`. -/
private theorem elliptopeBracket_le_one_sub_sq {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1) :
    elliptopeBracket rhoFirst rhoSecond rhoThird ≤ 1 - rhoFirst ^ 2 := by
  rw [elliptopeBracket]
  nlinarith [sq_nonneg (rhoSecond - rhoFirst * rhoThird),
    mul_nonneg (sq_nonneg rhoThird) (sub_nonneg.mpr hfirst)]

/-- The unit-diagonal correlation matrix shifted by a scalar, entry by entry. -/
private theorem correlationMatrixThree_sub_smul_one_eq
    (rhoFirst rhoSecond rhoThird shiftValue : ℝ) :
    correlationMatrixThree rhoFirst rhoSecond rhoThird
        - shiftValue • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = !![1 - shiftValue, rhoFirst, rhoSecond;
           rhoFirst, 1 - shiftValue, rhoThird;
           rhoSecond, rhoThird, 1 - shiftValue] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [correlationMatrixThree]

/-- The shifted correlation matrix is symmetric. -/
private theorem shiftedCorrelationMatrix_transpose
    (rhoFirst rhoSecond rhoThird diagValue : ℝ) :
    (!![diagValue, rhoFirst, rhoSecond;
        rhoFirst, diagValue, rhoThird;
        rhoSecond, rhoThird, diagValue] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ
      = !![diagValue, rhoFirst, rhoSecond;
           rhoFirst, diagValue, rhoThird;
           rhoSecond, rhoThird, diagValue] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> rfl

/-- The determinant of a symmetric `3 x 3` with constant diagonal. -/
private theorem det_shiftedCorrelationMatrix
    (rhoFirst rhoSecond rhoThird diagValue : ℝ) :
    (!![diagValue, rhoFirst, rhoSecond;
        rhoFirst, diagValue, rhoThird;
        rhoSecond, rhoThird, diagValue] : Matrix (Fin 3) (Fin 3) ℝ).det
      = diagValue ^ 3 - diagValue * (rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2)
        + 2 * (rhoFirst * rhoSecond * rhoThird) := by
  rw [Matrix.det_fin_three]
  simp
  ring

/-- **THE SHIFTED DETERMINANT FACTORISES.**  With `B` the bracket and `P` the product,
`det(R - (4/9) B . 1) = (4/9) B (1/4 + (1/3) B - (16/81) B^2 + 2 P)`.  The whole gate is
this `ring` identity: the shifted determinant carries `B` as a factor because at `B = 0`
the shift vanishes and the determinant is `B` itself. -/
theorem shiftedCorrelationDeterminant_factorisation (sigmaValue productValue : ℝ) :
    (1 - (4 / 9) * (1 - sigmaValue + 2 * productValue)) ^ 3
        - (1 - (4 / 9) * (1 - sigmaValue + 2 * productValue)) * sigmaValue + 2 * productValue
      = (4 / 9) * (1 - sigmaValue + 2 * productValue)
        * (1 / 4 + (1 / 3) * (1 - sigmaValue + 2 * productValue)
            - (16 / 81) * (1 - sigmaValue + 2 * productValue) ^ 2 + 2 * productValue) := by
  ring

/-- **THE LINEARIZED GATE.**  For every unit-diagonal `3 x 3` correlation matrix on the
elliptope, `R - (4/9)(det R) . 1` is positive semidefinite: `lambda_min(R) >= (4/9) det R`
with no eigenvalue, no interlacing, no square root.

Three principal-minor clauses, each with its own exact certificate.  The diagonal and
the `2 x 2` minors come from the Fischer bound `B <= 1 - r^2`; the determinant comes from
the factorisation above together with the sharp product floor `P >= -1/8`.

On the constant `4/9`: it is the reciprocal of `(3/2)^2 = 9/4`, the maximum of the
product of the two largest eigenvalues of a trace-three positive semidefinite `3 x 3`,
so no larger constant can work — but that OPTIMALITY IS NOT PROVED HERE, only the
inequality.  At `gamma == -1/2` both sides vanish (`B = 0`), which is the degenerate
equality case `0 >= 0`, not a certificate of optimality. -/
theorem posSemidef_correlationMatrixThree_sub_four_ninths_bracket_smul_one
    {rhoFirst rhoSecond rhoThird : ℝ}
    (hcompat : IsCompatibleTriple rhoFirst rhoSecond rhoThird)
    (hbracket : 0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird) :
    (correlationMatrixThree rhoFirst rhoSecond rhoThird
        - ((4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird)
          • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  obtain ⟨hfirstCap, hsecondCap, hthirdCap⟩ := hcompat
  have hcapFirst := elliptopeBracket_le_one_sub_sq (rhoSecond := rhoSecond)
    (rhoThird := rhoThird) hfirstCap
  have hcapSecond : elliptopeBracket rhoFirst rhoSecond rhoThird ≤ 1 - rhoSecond ^ 2 := by
    have hswap : elliptopeBracket rhoSecond rhoFirst rhoThird
        = elliptopeBracket rhoFirst rhoSecond rhoThird := by
      rw [elliptopeBracket, elliptopeBracket]; ring
    rw [← hswap]
    exact elliptopeBracket_le_one_sub_sq hsecondCap
  have hcapThird : elliptopeBracket rhoFirst rhoSecond rhoThird ≤ 1 - rhoThird ^ 2 := by
    have hswap : elliptopeBracket rhoThird rhoSecond rhoFirst
        = elliptopeBracket rhoFirst rhoSecond rhoThird := by
      rw [elliptopeBracket, elliptopeBracket]; ring
    rw [← hswap]
    exact elliptopeBracket_le_one_sub_sq hthirdCap
  have hproduct := elliptopeBracket_product_ge_neg_eighth hbracket
  have hbracketLeOne : elliptopeBracket rhoFirst rhoSecond rhoThird ≤ 1 := by
    nlinarith [hcapFirst, sq_nonneg rhoFirst]
  rw [correlationMatrixThree_sub_smul_one_eq]
  refine posSemidef_three_of_principalMinors
    (shiftedCorrelationMatrix_transpose rhoFirst rhoSecond rhoThird
      (1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show (0 : ℝ) ≤ 1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird
    linarith
  · show (0 : ℝ) ≤ 1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird
    linarith
  · show (0 : ℝ) ≤ 1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird
    linarith
  · show (0 : ℝ) ≤ (1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird)
        * (1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird) - rhoFirst ^ 2
    nlinarith [hcapFirst, hbracket, sq_nonneg (elliptopeBracket rhoFirst rhoSecond rhoThird),
      hfirstCap]
  · show (0 : ℝ) ≤ (1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird)
        * (1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird) - rhoSecond ^ 2
    nlinarith [hcapSecond, hbracket, sq_nonneg (elliptopeBracket rhoFirst rhoSecond rhoThird),
      hsecondCap]
  · show (0 : ℝ) ≤ (1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird)
        * (1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird) - rhoThird ^ 2
    nlinarith [hcapThird, hbracket, sq_nonneg (elliptopeBracket rhoFirst rhoSecond rhoThird),
      hthirdCap]
  · rw [det_shiftedCorrelationMatrix]
    have hexpand : (1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird) ^ 3
          - (1 - (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird)
            * (rhoFirst ^ 2 + rhoSecond ^ 2 + rhoThird ^ 2)
          + 2 * (rhoFirst * rhoSecond * rhoThird)
        = (4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird
          * (1 / 4 + (1 / 3) * elliptopeBracket rhoFirst rhoSecond rhoThird
              - (16 / 81) * elliptopeBracket rhoFirst rhoSecond rhoThird ^ 2
              + 2 * (rhoFirst * rhoSecond * rhoThird)) := by
      rw [elliptopeBracket]
      ring
    have hinner : 0 ≤ 1 / 4 + (1 / 3) * elliptopeBracket rhoFirst rhoSecond rhoThird
        - (16 / 81) * elliptopeBracket rhoFirst rhoSecond rhoThird ^ 2
        + 2 * (rhoFirst * rhoSecond * rhoThird) := by
      have hshrink : 0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird
          * (1 / 3 - (16 / 81) * elliptopeBracket rhoFirst rhoSecond rhoThird) :=
        mul_nonneg hbracket (by linarith)
      nlinarith [hshrink, hproduct]
    nlinarith [hexpand, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 9) hbracket) hinner]

/-- **THE LINEARIZED GATE AT A DESIGN TRIPLE.**  The `3 x 3` Gram compression of a
triple of nondegenerate atoms dominates `(4/9)` of its own determinant.  All the
hypotheses are triple-local; no share, no size, no rank relation. -/
theorem posSemidef_directionGramMatrix_submatrix_three_sub_gate (D : WeightedDesign m k)
    {first second third : Fin m} (hfirst : 0 < leverageOf (D.atom first))
    (hsecond : 0 < leverageOf (D.atom second)) (hthird : 0 < leverageOf (D.atom third)) :
    ((directionGramMatrix D).submatrix ![first, second, third] ![first, second, third]
        - ((4 / 9) * directionTripleDeterminant D first second third)
          • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  have hbridge : directionTripleDeterminant D first second third
      = elliptopeBracket (directionGram D first second) (directionGram D first third)
          (directionGram D second third) := by
    rw [directionTripleDeterminant, directionTripleSigma, directionTripleProduct,
      elliptopeBracket]
    ring
  have hsq : ∀ leftIndex rightIndex : Fin m, directionGram D leftIndex rightIndex ^ 2 ≤ 1 := by
    intro leftIndex rightIndex
    have habs := abs_directionGram_le_one D leftIndex rightIndex
    nlinarith [sq_abs (directionGram D leftIndex rightIndex),
      abs_nonneg (directionGram D leftIndex rightIndex)]
  have hbracketNonneg : 0 ≤ elliptopeBracket (directionGram D first second)
      (directionGram D first third) (directionGram D second third) := by
    rw [← hbridge]
    exact directionTripleDeterminant_nonneg D hfirst hsecond hthird
  rw [directionGramMatrix_submatrix_three_eq_correlationMatrixThree D hfirst hsecond hthird,
    hbridge]
  exact posSemidef_correlationMatrixThree_sub_four_ninths_bracket_smul_one
    ⟨hsq first second, hsq first third, hsq second third⟩ hbracketNonneg

/-- **THE FIVE-SET CONSTANT `8/45`.**  A triple whose Gram determinant reaches `2/5`
has `lambda_min >= (4/9)(2/5) = 8/45`.  Composed with the shipped
`Gtz.IsHollowInvolution.exists_distinct_tripleBracket_ge_two_fifths_avoiding` this is the
pen's five-set floor. -/
theorem posSemidef_correlationMatrixThree_sub_eight_forty_fifths_smul_one
    {rhoFirst rhoSecond rhoThird : ℝ}
    (hcompat : IsCompatibleTriple rhoFirst rhoSecond rhoThird)
    (hbracket : 2 / 5 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird) :
    (correlationMatrixThree rhoFirst rhoSecond rhoThird
        - (8 / 45 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  have hgate := posSemidef_correlationMatrixThree_sub_four_ninths_bracket_smul_one hcompat
    (by linarith)
  have hshift : correlationMatrixThree rhoFirst rhoSecond rhoThird
        - (8 / 45 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = (correlationMatrixThree rhoFirst rhoSecond rhoThird
          - ((4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird)
            • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        + ((4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird - 8 / 45)
          • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [sub_smul]
    abel
  rw [hshift]
  exact hgate.add ((Matrix.PosSemidef.one).smul (by linarith))

/-- **THE FOUR-SET CONSTANT `(2/9)(1 - w_pq)`.**  A triple whose Gram determinant reaches
`(1 - w)/2` has `lambda_min >= (4/9)(1 - w)/2 = (2/9)(1 - w)`.  Composed with the shipped
`Gtz.IsHollowInvolution.exists_tripleBracket_ge_fourSet` this is the pen's four-set
floor. -/
theorem posSemidef_correlationMatrixThree_sub_two_ninths_deficit_smul_one
    {rhoFirst rhoSecond rhoThird complementEdge : ℝ}
    (hcompat : IsCompatibleTriple rhoFirst rhoSecond rhoThird)
    (hdeficitNonneg : 0 ≤ 1 - complementEdge)
    (hbracket : (1 - complementEdge) / 2 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird) :
    (correlationMatrixThree rhoFirst rhoSecond rhoThird
        - ((2 / 9) * (1 - complementEdge)) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  have hgate := posSemidef_correlationMatrixThree_sub_four_ninths_bracket_smul_one hcompat
    (by linarith)
  have hshift : correlationMatrixThree rhoFirst rhoSecond rhoThird
        - ((2 / 9) * (1 - complementEdge)) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = (correlationMatrixThree rhoFirst rhoSecond rhoThird
          - ((4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird)
            • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        + ((4 / 9) * elliptopeBracket rhoFirst rhoSecond rhoThird
            - (2 / 9) * (1 - complementEdge)) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [sub_smul]
    abel
  rw [hshift]
  exact hgate.add ((Matrix.PosSemidef.one).smul (by linarith))

/-! ### The gate, wired to the shipped `(6,3)` determinant masses

The shipped five- and six-set gates deliver a triple with `det Gamma[T] >= 2/5`; the
linearized gate turns that determinant into a spectral floor.  Both are stated in the
six-tuple interface the shipped lemmas already use, so no permutation gymnastics enter. -/

/-- **THE `(6,3)` FIVE-SET SPECTRAL FLOOR, `8/45`.**  On an equal-share `(6,3)` design,
some triple AVOIDING any prescribed atom has its Gram compression above `(8/45) . 1`.
Ten triples share a determinant total of `4`, so one reaches `2/5`; the linearized gate
converts `2/5` into `8/45`.  No eigenvalue anywhere. -/
theorem exists_gateTriple_avoiding_sixThree (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    ∃ leftIndex middleIndex rightIndex : Fin 6,
      leftIndex ≠ sixth ∧ middleIndex ≠ sixth ∧ rightIndex ≠ sixth
        ∧ leftIndex ≠ middleIndex ∧ leftIndex ≠ rightIndex ∧ middleIndex ≠ rightIndex
        ∧ ((directionGramMatrix D).submatrix ![leftIndex, middleIndex, rightIndex]
              ![leftIndex, middleIndex, rightIndex]
            - (8 / 45 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  have hleverage : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hinvol := isHollowInvolution_correlationInvolution_of_uniformShare D huniform
    (by norm_num) (by norm_num)
  obtain ⟨leftIndex, middleIndex, rightIndex, hleftSixth, hmiddleSixth, hrightSixth,
    hleftMiddle, hleftRight, hmiddleRight, hbracketBound⟩ :=
    hinvol.exists_distinct_tripleBracket_ge_two_fifths_avoiding hbijective
  rw [hollowTripleBracket_correlationInvolution_eq D hleftMiddle hleftRight hmiddleRight]
    at hbracketBound
  have hsq : ∀ leftSlot rightSlot : Fin 6, directionGram D leftSlot rightSlot ^ 2 ≤ 1 := by
    intro leftSlot rightSlot
    have habs := abs_directionGram_le_one D leftSlot rightSlot
    nlinarith [sq_abs (directionGram D leftSlot rightSlot),
      abs_nonneg (directionGram D leftSlot rightSlot)]
  refine ⟨leftIndex, middleIndex, rightIndex, hleftSixth, hmiddleSixth, hrightSixth,
    hleftMiddle, hleftRight, hmiddleRight, ?_⟩
  rw [directionGramMatrix_submatrix_three_eq_correlationMatrixThree D (hleverage leftIndex)
    (hleverage middleIndex) (hleverage rightIndex)]
  exact posSemidef_correlationMatrixThree_sub_eight_forty_fifths_smul_one
    ⟨hsq leftIndex middleIndex, hsq leftIndex rightIndex, hsq middleIndex rightIndex⟩
    hbracketBound

/-- **THE `(6,3)` SIX-SET SPECTRAL FLOOR, `8/45`.**  The same constant without the
avoidance clause: twenty triples share a determinant total of `8`. -/
theorem exists_gateTriple_sixThree (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth]) :
    ∃ leftIndex middleIndex rightIndex : Fin 6,
      leftIndex ≠ middleIndex ∧ leftIndex ≠ rightIndex ∧ middleIndex ≠ rightIndex
        ∧ ((directionGramMatrix D).submatrix ![leftIndex, middleIndex, rightIndex]
              ![leftIndex, middleIndex, rightIndex]
            - (8 / 45 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  obtain ⟨leftIndex, middleIndex, rightIndex, _, _, _, hleftMiddle, hleftRight, hmiddleRight,
    hgate⟩ := exists_gateTriple_avoiding_sixThree D huniform hbijective
  exact ⟨leftIndex, middleIndex, rightIndex, hleftMiddle, hleftRight, hmiddleRight, hgate⟩

/-! ## 4.  The Radon step, dimension-free

The pen's planar Radon lemma at THREE directions, with the angle removed.  The
certificate is the vanishing of the squared norm of the combination; the plane, the
circle and the doubled angles are all unnecessary at count three.  The pen's FIVE-term
application is walled — see the header. -/

/-- **THE RADON STEP AT THREE DIRECTIONS, sharp.**  Three unit vectors carrying a
strictly positive vanishing combination have a pair at inner product at most `-1/2`:
two of them are at least 120 degrees apart.  True in EVERY ambient dimension — no
plane, no angle, no doubling.  Sharp at the Mercedes frame, where all three pairs
achieve `-1/2` exactly. -/
theorem exists_dotProduct_le_neg_half_of_vanishingCombination {coord : Type*} [Fintype coord]
    {firstVec secondVec thirdVec : coord → ℝ} {firstWeight secondWeight thirdWeight : ℝ}
    (hfirstUnit : firstVec ⬝ᵥ firstVec = 1) (hsecondUnit : secondVec ⬝ᵥ secondVec = 1)
    (hthirdUnit : thirdVec ⬝ᵥ thirdVec = 1) (hfirstPos : 0 < firstWeight)
    (hsecondPos : 0 < secondWeight) (hthirdPos : 0 < thirdWeight)
    (hvanish : firstWeight • firstVec + secondWeight • secondVec + thirdWeight • thirdVec = 0) :
    firstVec ⬝ᵥ secondVec ≤ -(1 / 2) ∨ firstVec ⬝ᵥ thirdVec ≤ -(1 / 2)
      ∨ secondVec ⬝ᵥ thirdVec ≤ -(1 / 2) := by
  have hcombination : firstWeight • firstVec + secondWeight • secondVec + thirdWeight • thirdVec
      = 0 := hvanish
  have hnormZero : (firstWeight • firstVec + secondWeight • secondVec + thirdWeight • thirdVec)
      ⬝ᵥ (firstWeight • firstVec + secondWeight • secondVec + thirdWeight • thirdVec) = 0 := by
    rw [hcombination, dotProduct_zero]
  have hexpand : (firstWeight • firstVec + secondWeight • secondVec + thirdWeight • thirdVec)
        ⬝ᵥ (firstWeight • firstVec + secondWeight • secondVec + thirdWeight • thirdVec)
      = firstWeight ^ 2 * (firstVec ⬝ᵥ firstVec) + secondWeight ^ 2 * (secondVec ⬝ᵥ secondVec)
        + thirdWeight ^ 2 * (thirdVec ⬝ᵥ thirdVec)
        + 2 * (firstWeight * secondWeight) * (firstVec ⬝ᵥ secondVec)
        + 2 * (firstWeight * thirdWeight) * (firstVec ⬝ᵥ thirdVec)
        + 2 * (secondWeight * thirdWeight) * (secondVec ⬝ᵥ thirdVec) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm secondVec firstVec, dotProduct_comm thirdVec firstVec,
      dotProduct_comm thirdVec secondVec]
    ring
  rw [hexpand, hfirstUnit, hsecondUnit, hthirdUnit] at hnormZero
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hfirstSecond, hfirstThird, hsecondThird⟩ := hcontra
  nlinarith [hnormZero, hfirstSecond, hfirstThird, hsecondThird,
    mul_pos hfirstPos hsecondPos, mul_pos hfirstPos hthirdPos, mul_pos hsecondPos hthirdPos,
    sq_nonneg (firstWeight - secondWeight), sq_nonneg (firstWeight - thirdWeight),
    sq_nonneg (secondWeight - thirdWeight)]

/-- The squared norm of a five-term combination, in the fifteen scalars of the family. -/
private theorem dotProduct_self_fiveTermCombination {coord : Type*} [Fintype coord]
    (firstVec secondVec thirdVec fourthVec fifthVec : coord → ℝ)
    (firstWeight secondWeight thirdWeight fourthWeight fifthWeight : ℝ) :
    (firstWeight • firstVec + secondWeight • secondVec + thirdWeight • thirdVec
          + fourthWeight • fourthVec + fifthWeight • fifthVec)
        ⬝ᵥ (firstWeight • firstVec + secondWeight • secondVec + thirdWeight • thirdVec
          + fourthWeight • fourthVec + fifthWeight • fifthVec)
      = firstWeight ^ 2 * (firstVec ⬝ᵥ firstVec) + secondWeight ^ 2 * (secondVec ⬝ᵥ secondVec)
          + thirdWeight ^ 2 * (thirdVec ⬝ᵥ thirdVec)
          + fourthWeight ^ 2 * (fourthVec ⬝ᵥ fourthVec)
          + fifthWeight ^ 2 * (fifthVec ⬝ᵥ fifthVec)
        + 2 * (firstWeight * secondWeight) * (firstVec ⬝ᵥ secondVec)
        + 2 * (firstWeight * thirdWeight) * (firstVec ⬝ᵥ thirdVec)
        + 2 * (firstWeight * fourthWeight) * (firstVec ⬝ᵥ fourthVec)
        + 2 * (firstWeight * fifthWeight) * (firstVec ⬝ᵥ fifthVec)
        + 2 * (secondWeight * thirdWeight) * (secondVec ⬝ᵥ thirdVec)
        + 2 * (secondWeight * fourthWeight) * (secondVec ⬝ᵥ fourthVec)
        + 2 * (secondWeight * fifthWeight) * (secondVec ⬝ᵥ fifthVec)
        + 2 * (thirdWeight * fourthWeight) * (thirdVec ⬝ᵥ fourthVec)
        + 2 * (thirdWeight * fifthWeight) * (thirdVec ⬝ᵥ fifthVec)
        + 2 * (fourthWeight * fifthWeight) * (fourthVec ⬝ᵥ fifthVec) := by
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm secondVec firstVec, dotProduct_comm thirdVec firstVec,
    dotProduct_comm fourthVec firstVec, dotProduct_comm fifthVec firstVec,
    dotProduct_comm thirdVec secondVec, dotProduct_comm fourthVec secondVec,
    dotProduct_comm fifthVec secondVec, dotProduct_comm fourthVec thirdVec,
    dotProduct_comm fifthVec thirdVec, dotProduct_comm fifthVec fourthVec]
  ring

/-- **THE RADON STEP AT FIVE DIRECTIONS, and this is the WALL.**  Five unit vectors
carrying a strictly positive vanishing combination have a pair at inner product at most
`-1/4`.  The certificate is the same one as at three directions — the squared norm of the
combination against the Cauchy-Schwarz bound `(sum w)^2 <= 5 sum w^2` — and the constant
it produces is `-1/(count - 1)`, so at count five it is `-1/4`.

THE PEN NEEDS `-1/2` (two lines 60 degrees apart after angle doubling).  `-1/4`
corresponds to about 52.2 degrees.  This theorem is therefore the exact boundary of what
the norm certificate can give, and the residue is the interval from `-1/4` down to
`-1/2`, which requires the largest-angular-gap argument on a cyclic sort of the five
doubled arguments.  That argument is not mechanized anywhere in this repository. -/
theorem exists_dotProduct_le_neg_quarter_of_fiveTermVanishingCombination {coord : Type*}
    [Fintype coord] {firstVec secondVec thirdVec fourthVec fifthVec : coord → ℝ}
    {firstWeight secondWeight thirdWeight fourthWeight fifthWeight : ℝ}
    (hfirstUnit : firstVec ⬝ᵥ firstVec = 1) (hsecondUnit : secondVec ⬝ᵥ secondVec = 1)
    (hthirdUnit : thirdVec ⬝ᵥ thirdVec = 1) (hfourthUnit : fourthVec ⬝ᵥ fourthVec = 1)
    (hfifthUnit : fifthVec ⬝ᵥ fifthVec = 1) (hfirstPos : 0 < firstWeight)
    (hsecondPos : 0 < secondWeight) (hthirdPos : 0 < thirdWeight)
    (hfourthPos : 0 < fourthWeight) (hfifthPos : 0 < fifthWeight)
    (hvanish : firstWeight • firstVec + secondWeight • secondVec + thirdWeight • thirdVec
      + fourthWeight • fourthVec + fifthWeight • fifthVec = 0) :
    firstVec ⬝ᵥ secondVec ≤ -(1 / 4) ∨ firstVec ⬝ᵥ thirdVec ≤ -(1 / 4)
      ∨ firstVec ⬝ᵥ fourthVec ≤ -(1 / 4) ∨ firstVec ⬝ᵥ fifthVec ≤ -(1 / 4)
      ∨ secondVec ⬝ᵥ thirdVec ≤ -(1 / 4) ∨ secondVec ⬝ᵥ fourthVec ≤ -(1 / 4)
      ∨ secondVec ⬝ᵥ fifthVec ≤ -(1 / 4) ∨ thirdVec ⬝ᵥ fourthVec ≤ -(1 / 4)
      ∨ thirdVec ⬝ᵥ fifthVec ≤ -(1 / 4) ∨ fourthVec ⬝ᵥ fifthVec ≤ -(1 / 4) := by
  have hnormZero : (firstWeight • firstVec + secondWeight • secondVec + thirdWeight • thirdVec
        + fourthWeight • fourthVec + fifthWeight • fifthVec)
      ⬝ᵥ (firstWeight • firstVec + secondWeight • secondVec + thirdWeight • thirdVec
        + fourthWeight • fourthVec + fifthWeight • fifthVec) = 0 := by
    rw [hvanish, dotProduct_zero]
  rw [dotProduct_self_fiveTermCombination, hfirstUnit, hsecondUnit, hthirdUnit, hfourthUnit,
    hfifthUnit] at hnormZero
  have hcauchySchwarz : (firstWeight + secondWeight + thirdWeight + fourthWeight + fifthWeight) ^ 2
      ≤ 5 * (firstWeight ^ 2 + secondWeight ^ 2 + thirdWeight ^ 2 + fourthWeight ^ 2
        + fifthWeight ^ 2) := by
    nlinarith [sq_nonneg (firstWeight - secondWeight), sq_nonneg (firstWeight - thirdWeight),
      sq_nonneg (firstWeight - fourthWeight), sq_nonneg (firstWeight - fifthWeight),
      sq_nonneg (secondWeight - thirdWeight), sq_nonneg (secondWeight - fourthWeight),
      sq_nonneg (secondWeight - fifthWeight), sq_nonneg (thirdWeight - fourthWeight),
      sq_nonneg (thirdWeight - fifthWeight), sq_nonneg (fourthWeight - fifthWeight)]
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hfirstSecond, hfirstThird, hfirstFourth, hfirstFifth, hsecondThird, hsecondFourth,
    hsecondFifth, hthirdFourth, hthirdFifth, hfourthFifth⟩ := hcontra
  have hslackFirstSecond : 0 < firstWeight * secondWeight * (firstVec ⬝ᵥ secondVec + 1 / 4) :=
    mul_pos (mul_pos hfirstPos hsecondPos) (by linarith)
  have hslackFirstThird : 0 < firstWeight * thirdWeight * (firstVec ⬝ᵥ thirdVec + 1 / 4) :=
    mul_pos (mul_pos hfirstPos hthirdPos) (by linarith)
  have hslackFirstFourth : 0 < firstWeight * fourthWeight * (firstVec ⬝ᵥ fourthVec + 1 / 4) :=
    mul_pos (mul_pos hfirstPos hfourthPos) (by linarith)
  have hslackFirstFifth : 0 < firstWeight * fifthWeight * (firstVec ⬝ᵥ fifthVec + 1 / 4) :=
    mul_pos (mul_pos hfirstPos hfifthPos) (by linarith)
  have hslackSecondThird : 0 < secondWeight * thirdWeight * (secondVec ⬝ᵥ thirdVec + 1 / 4) :=
    mul_pos (mul_pos hsecondPos hthirdPos) (by linarith)
  have hslackSecondFourth : 0 < secondWeight * fourthWeight * (secondVec ⬝ᵥ fourthVec + 1 / 4) :=
    mul_pos (mul_pos hsecondPos hfourthPos) (by linarith)
  have hslackSecondFifth : 0 < secondWeight * fifthWeight * (secondVec ⬝ᵥ fifthVec + 1 / 4) :=
    mul_pos (mul_pos hsecondPos hfifthPos) (by linarith)
  have hslackThirdFourth : 0 < thirdWeight * fourthWeight * (thirdVec ⬝ᵥ fourthVec + 1 / 4) :=
    mul_pos (mul_pos hthirdPos hfourthPos) (by linarith)
  have hslackThirdFifth : 0 < thirdWeight * fifthWeight * (thirdVec ⬝ᵥ fifthVec + 1 / 4) :=
    mul_pos (mul_pos hthirdPos hfifthPos) (by linarith)
  have hslackFourthFifth : 0 < fourthWeight * fifthWeight * (fourthVec ⬝ᵥ fifthVec + 1 / 4) :=
    mul_pos (mul_pos hfourthPos hfifthPos) (by linarith)
  linarith [hnormZero, hcauchySchwarz, hslackFirstSecond, hslackFirstThird, hslackFirstFourth,
    hslackFirstFifth, hslackSecondThird, hslackSecondFourth, hslackSecondFifth,
    hslackThirdFourth, hslackThirdFifth, hslackFourthFifth]

/-- **THE COUNT-FIVE CERTIFICATE HAS ZERO SLACK AT `-1/4`.**  At equal weights and a
common correlation, the quadratic form the certificate bounds is
`5 w^2 (1 + 4 g)`: it vanishes exactly at `g = -1/4` and is negative below.  So `-1/4` is
where the norm certificate is exhausted, and no rearrangement of the same argument can
produce `-1/2`. -/
theorem fiveTermCertificate_symmetricValue (commonWeight commonCorrelation : ℝ) :
    5 * commonWeight ^ 2 + 2 * (10 * commonWeight ^ 2) * commonCorrelation
      = 5 * commonWeight ^ 2 * (1 + 4 * commonCorrelation) := by
  ring

/-- The Gram matrix of five unit directions at the common correlation `-1/4`: unit
diagonal, every off-diagonal entry `-1/4`. -/
noncomputable def equalCorrelationFiveGram : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun rowIndex colIndex => if rowIndex = colIndex then 1 else -(1 / 4)

/-- **`-1/4` IS ATTAINED, so the count-five bound is SHARP as stated.**  The unit-diagonal
`5 x 5` matrix with every off-diagonal entry `-1/4` is positive semidefinite and kills the
all-ones vector.  It is therefore the Gram matrix of five unit vectors whose equal-weight
combination vanishes and every pair of which sits exactly at `-1/4` — the regular
`4`-simplex.  Since that configuration is NOT planar, the pen's `-1/2` is not a
sharpening of the dimension-free argument: it strictly consumes the rank-two hypothesis,
which the norm certificate never touches.  That is the precise content of the wall. -/
theorem posSemidef_equalCorrelationFiveGram : equalCorrelationFiveGram.PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun testVector => ?_⟩
  · ext rowIndex colIndex
    show (if colIndex = rowIndex then (1 : ℝ) else -(1 / 4))
      = if rowIndex = colIndex then (1 : ℝ) else -(1 / 4)
    split_ifs with hforward hbackward hbackward
    · rfl
    · exact absurd hforward.symm hbackward
    · exact absurd hbackward.symm hforward
    · rfl
  · have hquadForm : testVector ⬝ᵥ (equalCorrelationFiveGram *ᵥ testVector)
        = (5 / 4) * (testVector 0 ^ 2 + testVector 1 ^ 2 + testVector 2 ^ 2 + testVector 3 ^ 2
            + testVector 4 ^ 2)
          - (1 / 4) * (testVector 0 + testVector 1 + testVector 2 + testVector 3
            + testVector 4) ^ 2 := by
      simp [equalCorrelationFiveGram, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      ring
    rw [star_trivial, hquadForm]
    nlinarith [sq_nonneg (testVector 0 - testVector 1), sq_nonneg (testVector 0 - testVector 2),
      sq_nonneg (testVector 0 - testVector 3), sq_nonneg (testVector 0 - testVector 4),
      sq_nonneg (testVector 1 - testVector 2), sq_nonneg (testVector 1 - testVector 3),
      sq_nonneg (testVector 1 - testVector 4), sq_nonneg (testVector 2 - testVector 3),
      sq_nonneg (testVector 2 - testVector 4), sq_nonneg (testVector 3 - testVector 4)]

/-- The all-ones vector is in the kernel: the equal-weight combination of the five
directions vanishes. -/
theorem equalCorrelationFiveGram_mulVec_ones_eq_zero :
    equalCorrelationFiveGram *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  funext rowIndex
  fin_cases rowIndex <;>
    simp [equalCorrelationFiveGram, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;>
    norm_num

/-! ## 5.  Two closed routes, with exact miss constants

Nothing here is a geometric derivation.  What is mechanized is the ARITHMETIC of the
pen's deletion-averaging route, with every constant exact, and the conclusion that the
route closes strictly short of the target.  The geometric step producing the deletion
floor is NOT proved here; see the header. -/

/-- **THE DELETION FLOOR IS EXACT ON THE CONE BOUNDARY.**  The pen's deletion bound
`7/18 - (1/6) s` reaches the target `1/3` exactly when the squared cosine `s` is at
most `1/3`, with equality at `s = 1/3`. -/
theorem deletionFloor_ge_third_iff_le_third (squaredCosine : ℝ) :
    (1 : ℝ) / 3 ≤ 7 / 18 - (1 / 6) * squaredCosine ↔ squaredCosine ≤ 1 / 3 := by
  constructor <;> intro hbound <;> linarith

/-- **THE DELETION DEFICIT AT THE POLE IS EXACTLY `1/9`.**  At `s = 1` the deletion floor
is `2/9`, and `1/3 - 2/9 = 1/9`. -/
theorem deletionFloor_at_pole :
    (7 : ℝ) / 18 - (1 / 6) * 1 = 2 / 9 ∧ (1 : ℝ) / 3 - 2 / 9 = 1 / 9 := by
  constructor <;> norm_num

/-- **THE AVERAGING COLLAPSE PINS `7/23`.**  The pen's four-deletion average produces
`(23/24) x >= 7/24`; the best floor that yields is exactly `7/23`. -/
theorem deletionAveraging_collapse (floorValue : ℝ) :
    (23 / 24 : ℝ) * floorValue = 7 / 24 ↔ floorValue = 7 / 23 := by
  constructor <;> intro hvalue <;> linarith

/-- **THE ROUTE IS CLOSED, AND THE MISS IS EXACTLY `2/69`.**  Even granting `(6,3)` in
full, deletion-averaging bottoms out at `7/23`, strictly below the `(7,3)` target `1/3`,
with deficit exactly `2/69`.  A closed route with an exact constant. -/
theorem deletionAveraging_misses_third_by_two_sixty_ninths :
    (1 : ℝ) / 3 - 7 / 23 = 2 / 69 ∧ (7 : ℝ) / 23 < 1 / 3 ∧ (0 : ℝ) < 2 / 69 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **THE WALLED CONSTANT AT FIVE DIRECTIONS, as arithmetic.**  The count-five Radon step
proved in section 4 delivers `-1/4`; the pen's 60-degree claim needs `-1/2`.  `-1/4` is
strictly above `-1/2` and the residue is exactly `1/4`.  This is the wall, in numbers. -/
theorem radonFiveDirectionGap :
    -(1 / 4 : ℝ) > -(1 / 2) ∧ -(1 / 4 : ℝ) - (-(1 / 2)) = 1 / 4 := by
  refine ⟨by norm_num, by norm_num⟩

end Gtz
