/-
# Planar tight-frame rigidity: four unit vectors in a plane are two orthogonal pairs

The pen's item V5, landed, sharpened, and given its exact boundary.

## What the pen asked for

> Every 4-vector equal-norm tight frame of `ℝ²` with pairwise distinct directions
> is a union of TWO ORTHOGONAL PAIRS.

with a proof running through `z_c = exp(2 i θ_c)` on the unit circle, the
identity `Σ z_c = 0`, and the parametrisation of the unit-modulus pairs with a
prescribed sum.  That proof has a genuine hole at `Σ_{c ∈ first pair} z_c = 0`
(where the parametrisation has no axis) and it needs the distinctness hypothesis
throughout.

## What is landed here instead, and why it is strictly stronger

The whole statement is an identity about the GRAM matrix, so it needs neither
the plane, nor the circle, nor distinctness.  Write `G` for the `4 × 4` Gram of
the four unit vectors.  The tight-frame equation `Σ_c u_c u_cᵀ = 2 P` with `P`
acting as the identity on each `u_c` gives, by sandwiching against `u_i` and
`u_j`, exactly `G² = 2 G`; with `G_ii = 1` that says

    H := G − 1   is a HOLLOW SYMMETRIC INVOLUTION on `Fin 4`,

the repository's own `Gtz.IsHollowInvolution` at size four.  And every such `H`
has a perfect matching both of whose edges vanish
(`IsHollowInvolution.exists_zeroMatching_four`) — a six-line polynomial
consequence of `H² = 1`, with NO non-degeneracy hypothesis anywhere.  So:

* the theorem holds in EVERY ambient dimension, not just the plane — which is
  what the merge boundary needs, where the four residue vectors sit in a plane
  inside `ℝ³` and normalising a basis of that plane is exactly the step one
  wants to avoid;
* the pen's "pairwise non-parallel" hypothesis is dropped.  That matters: the
  campaign has already recorded (workflow 2) that carrying a non-parallel
  hypothesis on this stratum is not merely unnecessary but harmful, the
  octahedron being a landed member with three antipodal pairs.  The degenerate
  frame `u, u, v, v` with `u ⊥ v` is a genuine tight frame — its Gram shift has
  `H 0 1 = H 2 3 = 1` — and it satisfies the conclusion through its other two
  matchings.

## The moduli, exactly

Given a vanishing matching the classification is complete and one-dimensional:
the `2 × 2` CROSS BLOCK of `H` between the two pairs has orthonormal rows
(`crossBlock_isOrthonormal_of_zeroEdge`), and sharply,

    (H 1 2, H 1 3) = (−H 0 3, H 0 2)   or   (H 1 2, H 1 3) = (H 0 3, −H 0 2)

with `H 0 2 ^ 2 + H 0 3 ^ 2 = 1` (`crossBlock_quarterTurn_of_zeroEdge`).
That is precisely "two orthogonal pairs at a relative angle", the two branches
being the rotation and the reflection.  Every such datum is realised
(`isHollowInvolution_orthogonalPairInvolution`), so the moduli space of
`4 × 4` hollow symmetric involutions is, up to relabelling, `O(2)`.

Neither statement needs the matching, only one vanishing edge: a single zero
entry drags its complement to zero as well
(`complementaryEdge_eq_zero_of_zeroEdge_four`), so the pairing-up of the
vanishing entries is structural rather than an artefact of the proof above.

## The sharpness census: the rigidity holds at `m = 2` and `m = 4`, NOWHERE ELSE

The pen asked whether the `(m, 2)` generalisation is true.  It is FALSE, and
this file carries the witnesses rather than the assertion.

* `m = 2`: TRUE, and trivially — `dotProduct_eq_zero_of_planarTightFrame_two`.
* `m = 4`: TRUE — the theorem above.
* `m = 3`: FALSE — `exists_planarTightFrame_three_without_orthogonalPair`.  The
  Mercedes frame is a unit-norm tight frame with pairwise distinct directions in
  which no two atoms are orthogonal at all.
* `m = 6`: FALSE — `exists_planarTightFrame_six_without_orthogonalPair`.  Two
  Mercedes frames at the rational relative rotation `(3/5, 4/5)`.  All fifteen
  pairings are nonzero, so the frame contains no orthogonal pair whatsoever;
  even-`m` is therefore not saved by a parity argument.

In the Bloch picture (`Gtz.blochSquare`) the reason is transparent: a unit-norm
tight frame is a family of points on the circle summing to zero, an orthogonal
pair is an antipodal pair, and "sum zero forces antipodal pairing" is a fact
about FOUR points and no other count.

## The merge boundary

The pen's use of V5 is the collar where a near-parallel pair of a `(6,3)` design
merges: the merged atom is saturated, so every other atom is orthogonal to it,
and the four residue directions form a planar tight frame.  V5 hands over an
orthogonal pair inside that residue, and axis-plus-pair is three pairwise
orthogonal atoms, which dominate at EVERY weight vector by the shipped
`Gtz.dominates_of_orthogonalTriple_of_one_le` — `Gtz.Dominates` is weight-free.
That is `exists_dominating_triple_of_axisTightResidue`, and its tightness
hypothesis is discharged on the stratum by
`sum_atomMatrix_unitDirection_erase_of_saturatedAxis`: share one at the axis and
share one half everywhere else is exactly `Σ_c u_c u_cᵀ = 2 (1 − u_a u_aᵀ)`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.HollowInvolution
import Gtz.Design.DominationGates

namespace Gtz

open Matrix

variable {count rank size : ℕ}

/-! ## The algebraic core: a vanishing matching in every `4 × 4` hollow involution -/

namespace IsHollowInvolution

/-- **The rigidity theorem, in its dimension-free form.**  Every `4 × 4` hollow
symmetric involution has a perfect matching of `Fin 4` both of whose edges are
zero entries.  No non-degeneracy hypothesis: the degenerate involution with
`H 0 1 = H 2 3 = 1` and all other entries zero — the Gram shift of the doubled
orthogonal pair `u, u, v, v` — satisfies the conclusion through its other two
matchings.

Pen argument, rewritten as polynomial algebra.  Abbreviate the six independent
entries `a = H 0 1`, `b = H 0 2`, `c = H 0 3`, `d = H 1 2`, `e = H 1 3`,
`f = H 2 3`.  The off-diagonal entries of `H² = 1` are the six relations

    b d + c e = 0,  a d + c f = 0,  a e + b f = 0,
    a b + e f = 0,  a c + d f = 0,  b c + d e = 0,

and from them each of `b c`, `b d`, `c e`, `d e` annihilates `a² + f²` (three
relations apiece).  Multiplying the four back in gives

    (a² + f²) (b² + e²) (c² + d²) = 0,

a product of three sums of squares, so one factor vanishes identically — and
each factor vanishing is exactly one matching's two edges vanishing. -/
theorem exists_zeroMatching_four {invol : Matrix (Fin 4) (Fin 4) ℝ}
    (hinvol : IsHollowInvolution invol) :
    (invol 0 1 = 0 ∧ invol 2 3 = 0) ∨ (invol 0 2 = 0 ∧ invol 1 3 = 0)
      ∨ (invol 0 3 = 0 ∧ invol 1 2 = 0) := by
  have hoffDiagonal : ∀ leftIndex rightIndex : Fin 4, leftIndex ≠ rightIndex →
      ∑ midIndex, invol leftIndex midIndex * invol midIndex rightIndex = 0 := by
    intro leftIndex rightIndex hdistinct
    have hentry := congrFun (congrFun hinvol.square_eq_one leftIndex) rightIndex
    rwa [Matrix.mul_apply, Matrix.one_apply_ne hdistinct] at hentry
  have hhollow := hinvol.diagonal_eq_zero
  have hmirror := hinvol.apply_comm
  set firstEdge := invol 0 1 with hfirstEdge
  set secondEdge := invol 0 2 with hsecondEdge
  set thirdEdge := invol 0 3 with hthirdEdge
  set fourthEdge := invol 1 2 with hfourthEdge
  set fifthEdge := invol 1 3 with hfifthEdge
  set sixthEdge := invol 2 3 with hsixthEdge
  have relOneTwo : secondEdge * fourthEdge + thirdEdge * fifthEdge = 0 := by
    have hsum := hoffDiagonal 0 1 (by decide)
    rw [Fin.sum_univ_four, hhollow 0, hhollow 1, hmirror 1 2, hmirror 1 3] at hsum
    linarith [hsum]
  have relOneThree : firstEdge * fourthEdge + thirdEdge * sixthEdge = 0 := by
    have hsum := hoffDiagonal 0 2 (by decide)
    rw [Fin.sum_univ_four, hhollow 0, hhollow 2, hmirror 2 3] at hsum
    linarith [hsum]
  have relOneFour : firstEdge * fifthEdge + secondEdge * sixthEdge = 0 := by
    have hsum := hoffDiagonal 0 3 (by decide)
    rw [Fin.sum_univ_four, hhollow 0, hhollow 3] at hsum
    linarith [hsum]
  have relTwoThree : firstEdge * secondEdge + fifthEdge * sixthEdge = 0 := by
    have hsum := hoffDiagonal 1 2 (by decide)
    rw [Fin.sum_univ_four, hhollow 1, hhollow 2, hmirror 0 1, hmirror 2 3] at hsum
    linarith [hsum]
  have relTwoFour : firstEdge * thirdEdge + fourthEdge * sixthEdge = 0 := by
    have hsum := hoffDiagonal 1 3 (by decide)
    rw [Fin.sum_univ_four, hhollow 1, hhollow 3, hmirror 0 1] at hsum
    linarith [hsum]
  have relThreeFour : secondEdge * thirdEdge + fourthEdge * fifthEdge = 0 := by
    have hsum := hoffDiagonal 2 3 (by decide)
    rw [Fin.sum_univ_four, hhollow 2, hhollow 3, hmirror 0 2, hmirror 1 2] at hsum
    linarith [hsum]
  have crossOne : secondEdge * thirdEdge * (firstEdge ^ 2 + sixthEdge ^ 2) = 0 := by
    linear_combination (sixthEdge * secondEdge) * relOneThree
      - (sixthEdge * firstEdge) * relOneTwo + (thirdEdge * firstEdge) * relTwoThree
  have crossTwo : secondEdge * fourthEdge * (firstEdge ^ 2 + sixthEdge ^ 2) = 0 := by
    linear_combination (firstEdge * fourthEdge) * relTwoThree
      - (firstEdge * sixthEdge) * relThreeFour + (secondEdge * sixthEdge) * relTwoFour
  have crossThree : thirdEdge * fifthEdge * (firstEdge ^ 2 + sixthEdge ^ 2) = 0 := by
    linear_combination (firstEdge * fifthEdge) * relTwoFour
      - (firstEdge * sixthEdge) * relThreeFour + (thirdEdge * sixthEdge) * relTwoThree
  have crossFour : fourthEdge * fifthEdge * (firstEdge ^ 2 + sixthEdge ^ 2) = 0 := by
    linear_combination (sixthEdge * fifthEdge) * relTwoFour
      - (sixthEdge * firstEdge) * relOneTwo + (fourthEdge * firstEdge) * relOneFour
  have hmatchingProduct : (firstEdge ^ 2 + sixthEdge ^ 2)
      * ((secondEdge ^ 2 + fifthEdge ^ 2) * (thirdEdge ^ 2 + fourthEdge ^ 2)) = 0 := by
    linear_combination (secondEdge * thirdEdge) * crossOne
      + (secondEdge * fourthEdge) * crossTwo + (thirdEdge * fifthEdge) * crossThree
      + (fourthEdge * fifthEdge) * crossFour
  have hbothVanish : ∀ leftValue rightValue : ℝ, leftValue ^ 2 + rightValue ^ 2 = 0 →
      leftValue = 0 ∧ rightValue = 0 := by
    intro leftValue rightValue hsumSquares
    exact ⟨sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg rightValue]) (sq_nonneg _)),
      sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg leftValue]) (sq_nonneg _))⟩
  rcases mul_eq_zero.mp hmatchingProduct with hfirstMatching | hremaining
  · exact Or.inl (hbothVanish _ _ hfirstMatching)
  · rcases mul_eq_zero.mp hremaining with hsecondMatching | hthirdMatching
    · exact Or.inr (Or.inl (hbothVanish _ _ hsecondMatching))
    · exact Or.inr (Or.inr (hbothVanish _ _ hthirdMatching))

/-- The convenient consumer form of `exists_zeroMatching_four`: SOME off-diagonal
entry of a `4 × 4` hollow symmetric involution vanishes. -/
theorem exists_zeroEntry_four {invol : Matrix (Fin 4) (Fin 4) ℝ}
    (hinvol : IsHollowInvolution invol) :
    ∃ leftIndex rightIndex : Fin 4, leftIndex ≠ rightIndex ∧ invol leftIndex rightIndex = 0 := by
  rcases hinvol.exists_zeroMatching_four with ⟨hzero, _⟩ | ⟨hzero, _⟩ | ⟨hzero, _⟩
  · exact ⟨0, 1, by decide, hzero⟩
  · exact ⟨0, 2, by decide, hzero⟩
  · exact ⟨0, 3, by decide, hzero⟩

/-! ### The moduli of a `4 × 4` hollow involution with a prescribed zero matching -/

/-- **The cross block has orthonormal rows.**  Given a single vanishing edge
`H 0 1 = 0`, the two rows `(H 0 2, H 0 3)` and `(H 1 2, H 1 3)` of the `2 × 2`
block between the pairs are unit vectors and are orthogonal — the block is an
orthogonal matrix, which is the "relative angle" of the pen's moduli description.

Note the complementary edge `H 2 3 = 0` is NOT a hypothesis: it is a consequence
(`complementaryEdge_eq_zero_of_zeroEdge_four`).  Both unit statements are the
diagonal of `H² = 1` at rows `0` and `1` with the vanishing entry deleted; the
orthogonality is the `(0,1)` entry of `H² = 1`. -/
theorem crossBlock_isOrthonormal_of_zeroEdge {invol : Matrix (Fin 4) (Fin 4) ℝ}
    (hinvol : IsHollowInvolution invol) (hfirstEdge : invol 0 1 = 0) :
    invol 0 2 ^ 2 + invol 0 3 ^ 2 = 1 ∧ invol 1 2 ^ 2 + invol 1 3 ^ 2 = 1
      ∧ invol 0 2 * invol 1 2 + invol 0 3 * invol 1 3 = 0 := by
  have hdiagonal : ∀ rowIndex : Fin 4,
      ∑ midIndex, invol rowIndex midIndex * invol midIndex rowIndex = 1 := by
    intro rowIndex
    have hentry := congrFun (congrFun hinvol.square_eq_one rowIndex) rowIndex
    rwa [Matrix.mul_apply, Matrix.one_apply_eq] at hentry
  have hoffDiagonal : ∀ leftIndex rightIndex : Fin 4, leftIndex ≠ rightIndex →
      ∑ midIndex, invol leftIndex midIndex * invol midIndex rightIndex = 0 := by
    intro leftIndex rightIndex hdistinct
    have hentry := congrFun (congrFun hinvol.square_eq_one leftIndex) rightIndex
    rwa [Matrix.mul_apply, Matrix.one_apply_ne hdistinct] at hentry
  have hhollow := hinvol.diagonal_eq_zero
  have hmirror := hinvol.apply_comm
  refine ⟨?_, ?_, ?_⟩
  · have hrow := hdiagonal 0
    rw [Fin.sum_univ_four, hhollow 0, hmirror 0 1, hmirror 0 2, hmirror 0 3,
      hfirstEdge] at hrow
    nlinarith [hrow]
  · have hrow := hdiagonal 1
    rw [Fin.sum_univ_four, hhollow 1, hmirror 1 0, hmirror 1 2, hmirror 1 3,
      hinvol.apply_comm 0 1, hfirstEdge] at hrow
    nlinarith [hrow]
  · have hrow := hoffDiagonal 0 1 (by decide)
    rw [Fin.sum_univ_four, hhollow 0, hhollow 1, hmirror 1 2, hmirror 1 3] at hrow
    linarith [hrow]

/-- **A vanishing edge drags its complement to zero.**  In a `4 × 4` hollow
symmetric involution `H 0 1 = 0` already forces `H 2 3 = 0`, so the "matching" of
`exists_zeroMatching_four` is not a coincidence of that proof but a structural
fact: the vanishing entries of such a matrix always come in complementary pairs.
By relabelling the same holds for the other two matchings.

Pen argument: rows two and three of `H² = 1` read `H 0 2 ² + H 1 2 ² + H 2 3 ² = 1`
and `H 0 3 ² + H 1 3 ² + H 2 3 ² = 1`; adding them and substituting the two
cross-block unit relations gives `2 + 2 · H 2 3 ² = 2`. -/
theorem complementaryEdge_eq_zero_of_zeroEdge_four {invol : Matrix (Fin 4) (Fin 4) ℝ}
    (hinvol : IsHollowInvolution invol) (hfirstEdge : invol 0 1 = 0) :
    invol 2 3 = 0 := by
  obtain ⟨hfirstRow, hsecondRow, _⟩ := hinvol.crossBlock_isOrthonormal_of_zeroEdge hfirstEdge
  have hdiagonal : ∀ rowIndex : Fin 4,
      ∑ midIndex, invol rowIndex midIndex * invol midIndex rowIndex = 1 := by
    intro rowIndex
    have hentry := congrFun (congrFun hinvol.square_eq_one rowIndex) rowIndex
    rwa [Matrix.mul_apply, Matrix.one_apply_eq] at hentry
  have hhollow := hinvol.diagonal_eq_zero
  have hmirror := hinvol.apply_comm
  have hthirdRow := hdiagonal 2
  rw [Fin.sum_univ_four, hhollow 2, hmirror 0 2, hmirror 1 2, hmirror 2 3] at hthirdRow
  have hfourthRow := hdiagonal 3
  rw [Fin.sum_univ_four, hhollow 3, hmirror 0 3, hmirror 1 3, hmirror 2 3] at hfourthRow
  have hsquare : invol 2 3 ^ 2 = 0 := by nlinarith [hthirdRow, hfourthRow, hfirstRow, hsecondRow]
  exact sq_eq_zero_iff.mp hsquare

/-- **The moduli, sharply.**  With the edge `H 0 1` vanishing — hence, by
`complementaryEdge_eq_zero_of_zeroEdge_four`, the whole matching `{0,1} | {2,3}` —
the second row of the cross block is a quarter turn of the first, in one of the
two orientations.  Writing `H 0 2 = cos φ` and `H 0 3 = sin φ` (legitimate by the
unit relation), the frame is two orthonormal pairs at relative angle `φ`, the two
branches being the rotation and the reflection.  Together with
`isHollowInvolution_orthogonalPairInvolution` this pins the moduli exactly.

Pen argument: Lagrange's identity turns the three cross-block relations into
`(H 0 2 · H 1 3 − H 0 3 · H 1 2)² = 1`, and each sign completes a sum of two
squares to zero. -/
theorem crossBlock_quarterTurn_of_zeroEdge {invol : Matrix (Fin 4) (Fin 4) ℝ}
    (hinvol : IsHollowInvolution invol) (hfirstEdge : invol 0 1 = 0) :
    invol 0 2 ^ 2 + invol 0 3 ^ 2 = 1
      ∧ ((invol 1 2 = -invol 0 3 ∧ invol 1 3 = invol 0 2)
        ∨ (invol 1 2 = invol 0 3 ∧ invol 1 3 = -invol 0 2)) := by
  obtain ⟨hfirstRow, hsecondRow, hrowsOrthogonal⟩ :=
    hinvol.crossBlock_isOrthonormal_of_zeroEdge hfirstEdge
  refine ⟨hfirstRow, ?_⟩
  have hdeterminant : (invol 0 2 * invol 1 3 - invol 0 3 * invol 1 2 - 1)
      * (invol 0 2 * invol 1 3 - invol 0 3 * invol 1 2 + 1) = 0 := by
    nlinarith [hfirstRow, hsecondRow, hrowsOrthogonal]
  rcases mul_eq_zero.mp hdeterminant with hrotation | hreflection
  · left
    have hcollapse : (invol 1 2 + invol 0 3) ^ 2 + (invol 1 3 - invol 0 2) ^ 2 = 0 := by
      nlinarith [hfirstRow, hsecondRow, hrotation]
    constructor
    · have hsquare : (invol 1 2 + invol 0 3) ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg (invol 1 3 - invol 0 2)]) (sq_nonneg _)
      have hvanishes := sq_eq_zero_iff.mp hsquare
      linarith
    · have hsquare : (invol 1 3 - invol 0 2) ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg (invol 1 2 + invol 0 3)]) (sq_nonneg _)
      have hvanishes := sq_eq_zero_iff.mp hsquare
      linarith
  · right
    have hcollapse : (invol 1 2 - invol 0 3) ^ 2 + (invol 1 3 + invol 0 2) ^ 2 = 0 := by
      nlinarith [hfirstRow, hsecondRow, hreflection]
    constructor
    · have hsquare : (invol 1 2 - invol 0 3) ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg (invol 1 3 + invol 0 2)]) (sq_nonneg _)
      have hvanishes := sq_eq_zero_iff.mp hsquare
      linarith
    · have hsquare : (invol 1 3 + invol 0 2) ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg (invol 1 2 - invol 0 3)]) (sq_nonneg _)
      have hvanishes := sq_eq_zero_iff.mp hsquare
      linarith

end IsHollowInvolution

/-! ### Realising the moduli: every relative angle occurs -/

/-- The `4 × 4` hollow matrix of two orthogonal pairs at the relative angle
whose cosine and sine are the two arguments. -/
def orthogonalPairInvolution (angleCos angleSin : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, angleCos, angleSin;
     0, 0, -angleSin, angleCos;
     angleCos, -angleSin, 0, 0;
     angleSin, angleCos, 0, 0]

/-- **The moduli are inhabited at every angle**, so the classification of
`IsHollowInvolution.crossBlock_quarterTurn_of_zeroEdge` is exact: up to
relabelling, the `4 × 4` hollow symmetric involutions are a copy of `O(2)`. -/
theorem isHollowInvolution_orthogonalPairInvolution {angleCos angleSin : ℝ}
    (hunitCircle : angleCos ^ 2 + angleSin ^ 2 = 1) :
    IsHollowInvolution (orthogonalPairInvolution angleCos angleSin) where
  symmetric := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [orthogonalPairInvolution]
  square_eq_one := by
    ext rowIndex colIndex
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp only [orthogonalPairInvolution, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_fin_const, Matrix.one_apply, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.cons_val_three, Matrix.head_fin_const] <;>
      norm_num <;> nlinarith [hunitCircle]
  diagonal_eq_zero := by
    intro index
    fin_cases index <;> simp [orthogonalPairInvolution]

/-! ## The Gram bridge: a tight family of unit vectors is a hollow involution -/

/-- The Gram matrix of an arbitrary family of vectors. -/
def familyGramMatrix (family : Fin count → Fin rank → ℝ) : Matrix (Fin count) (Fin count) ℝ :=
  Matrix.of fun leftIndex rightIndex => family leftIndex ⬝ᵥ family rightIndex

theorem familyGramMatrix_apply (family : Fin count → Fin rank → ℝ)
    (leftIndex rightIndex : Fin count) :
    familyGramMatrix family leftIndex rightIndex = family leftIndex ⬝ᵥ family rightIndex := rfl

/-- **The Gram square law.**  If the family's atoms resolve `level` times a matrix
that fixes every member of the family, then the Gram matrix satisfies
`G² = level · G`.  Sandwich the frame equation between two members: the left side
is the `(i,j)` entry of `G²` because `(u u ᵀ) v = ⟨u,v⟩ u`, and the right side
collapses because the plane fixes `u_j`. -/
theorem gramSquare_of_tightOnPlane (level : ℝ) (family : Fin count → Fin rank → ℝ)
    (plane : Matrix (Fin rank) (Fin rank) ℝ)
    (hframe : ∑ index, atomMatrix (family index) = level • plane)
    (hfixed : ∀ index, plane *ᵥ family index = family index)
    (leftIndex rightIndex : Fin count) :
    ∑ midIndex, (family leftIndex ⬝ᵥ family midIndex) * (family midIndex ⬝ᵥ family rightIndex)
      = level * (family leftIndex ⬝ᵥ family rightIndex) := by
  have hsandwich := congrArg (fun gram => family leftIndex ⬝ᵥ (gram *ᵥ family rightIndex)) hframe
  simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, hfixed, dotProduct_smul,
    smul_eq_mul] at hsandwich
  rw [← hsandwich]
  refine Finset.sum_congr rfl fun midIndex _ => ?_
  rw [atomMatrix_mulVec_eq_smul, dotProduct_smul, smul_eq_mul]
  ring

/-- **The bridge.**  A family of unit vectors whose Gram matrix squares to twice
itself has `G − 1` a hollow symmetric involution.  This is where the ambient
dimension disappears. -/
theorem isHollowInvolution_familyGramMatrix_sub_one (family : Fin count → Fin rank → ℝ)
    (hunit : ∀ index, family index ⬝ᵥ family index = 1)
    (hgramSquare : ∀ leftIndex rightIndex : Fin count,
      ∑ midIndex, (family leftIndex ⬝ᵥ family midIndex) * (family midIndex ⬝ᵥ family rightIndex)
        = 2 * (family leftIndex ⬝ᵥ family rightIndex)) :
    IsHollowInvolution (familyGramMatrix family - 1) where
  symmetric := by
    ext leftIndex rightIndex
    simp only [Matrix.transpose_apply, Matrix.sub_apply, familyGramMatrix, Matrix.of_apply,
      Matrix.one_apply, dotProduct_comm (family rightIndex) (family leftIndex)]
    rcases eq_or_ne leftIndex rightIndex with rfl | hdistinct
    · rfl
    · rw [if_neg hdistinct, if_neg (Ne.symm hdistinct)]
  square_eq_one := by
    have hdouble : familyGramMatrix family * familyGramMatrix family
        = familyGramMatrix family + familyGramMatrix family := by
      ext leftIndex rightIndex
      rw [Matrix.mul_apply, Matrix.add_apply]
      simpa only [familyGramMatrix, Matrix.of_apply] using
        (hgramSquare leftIndex rightIndex).trans (by ring)
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
      Matrix.one_mul, hdouble]
    abel
  diagonal_eq_zero := by
    intro index
    simp only [Matrix.sub_apply, familyGramMatrix, Matrix.of_apply, Matrix.one_apply_eq,
      hunit index, sub_self]

/-! ## V5 proper, in three readings -/

/-- **V5, ambient form.**  Four unit vectors whose atoms resolve twice a matrix
fixing all four split into two orthogonal pairs.  Any rank, no distinctness
hypothesis. -/
theorem exists_orthogonalMatching_of_unitTightFamily (family : Fin 4 → Fin rank → ℝ)
    (plane : Matrix (Fin rank) (Fin rank) ℝ)
    (hunit : ∀ index, family index ⬝ᵥ family index = 1)
    (hframe : ∑ index, atomMatrix (family index) = (2 : ℝ) • plane)
    (hfixed : ∀ index, plane *ᵥ family index = family index) :
    (family 0 ⬝ᵥ family 1 = 0 ∧ family 2 ⬝ᵥ family 3 = 0)
      ∨ (family 0 ⬝ᵥ family 2 = 0 ∧ family 1 ⬝ᵥ family 3 = 0)
      ∨ (family 0 ⬝ᵥ family 3 = 0 ∧ family 1 ⬝ᵥ family 2 = 0) := by
  have hinvolution := isHollowInvolution_familyGramMatrix_sub_one family hunit
    (gramSquare_of_tightOnPlane 2 family plane hframe hfixed)
  have hentry : ∀ leftIndex rightIndex : Fin 4, leftIndex ≠ rightIndex →
      (familyGramMatrix family - 1) leftIndex rightIndex = family leftIndex ⬝ᵥ family rightIndex := by
    intro leftIndex rightIndex hdistinct
    rw [Matrix.sub_apply, familyGramMatrix_apply, Matrix.one_apply_ne hdistinct, sub_zero]
  rcases hinvolution.exists_zeroMatching_four with
    ⟨hleft, hright⟩ | ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact Or.inl ⟨(hentry 0 1 (by decide)) ▸ hleft, (hentry 2 3 (by decide)) ▸ hright⟩
  · exact Or.inr (Or.inl ⟨(hentry 0 2 (by decide)) ▸ hleft, (hentry 1 3 (by decide)) ▸ hright⟩)
  · exact Or.inr (Or.inr ⟨(hentry 0 3 (by decide)) ▸ hleft, (hentry 1 2 (by decide)) ▸ hright⟩)

/-- The convenient consumer form: a tight four-family of unit vectors contains an
orthogonal pair. -/
theorem exists_orthogonalPair_of_unitTightFamily (family : Fin 4 → Fin rank → ℝ)
    (plane : Matrix (Fin rank) (Fin rank) ℝ)
    (hunit : ∀ index, family index ⬝ᵥ family index = 1)
    (hframe : ∑ index, atomMatrix (family index) = (2 : ℝ) • plane)
    (hfixed : ∀ index, plane *ᵥ family index = family index) :
    ∃ leftIndex rightIndex : Fin 4, leftIndex ≠ rightIndex ∧
      family leftIndex ⬝ᵥ family rightIndex = 0 := by
  rcases exists_orthogonalMatching_of_unitTightFamily family plane hunit hframe hfixed with
    ⟨hleft, _⟩ | ⟨hleft, _⟩ | ⟨hleft, _⟩
  · exact ⟨0, 1, by decide, hleft⟩
  · exact ⟨0, 2, by decide, hleft⟩
  · exact ⟨0, 3, by decide, hleft⟩

/-- **V5, the pen's planar form.**  Four unit vectors of `ℝ²` forming a tight
frame split into two orthogonal pairs.  The pen assumed pairwise distinct
directions; the hypothesis is not needed. -/
theorem exists_orthogonalMatching_of_planarTightFrame (family : Fin 4 → Fin 2 → ℝ)
    (hunit : ∀ index, family index ⬝ᵥ family index = 1)
    (hframe : ∑ index, atomMatrix (family index) = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    (family 0 ⬝ᵥ family 1 = 0 ∧ family 2 ⬝ᵥ family 3 = 0)
      ∨ (family 0 ⬝ᵥ family 2 = 0 ∧ family 1 ⬝ᵥ family 3 = 0)
      ∨ (family 0 ⬝ᵥ family 3 = 0 ∧ family 1 ⬝ᵥ family 2 = 0) :=
  exists_orthogonalMatching_of_unitTightFamily family 1 hunit hframe
    fun index => Matrix.one_mulVec (family index)

/-- **V5, the merge-boundary form.**  Four unit vectors orthogonal to a unit axis
whose atoms resolve twice the axis's orthogonal projector split into two
orthogonal pairs.  This is the reading the collar consumes: the residue of a
merged near-parallel pair lives in the plane orthogonal to the saturated axis,
and no basis of that plane ever has to be chosen. -/
theorem exists_orthogonalMatching_of_axisTightResidue {axis : Fin rank → ℝ}
    (family : Fin 4 → Fin rank → ℝ)
    (hunit : ∀ index, family index ⬝ᵥ family index = 1)
    (haxisOrthogonal : ∀ index, axis ⬝ᵥ family index = 0)
    (hframe : ∑ index, atomMatrix (family index)
      = (2 : ℝ) • ((1 : Matrix (Fin rank) (Fin rank) ℝ) - atomMatrix axis)) :
    (family 0 ⬝ᵥ family 1 = 0 ∧ family 2 ⬝ᵥ family 3 = 0)
      ∨ (family 0 ⬝ᵥ family 2 = 0 ∧ family 1 ⬝ᵥ family 3 = 0)
      ∨ (family 0 ⬝ᵥ family 3 = 0 ∧ family 1 ⬝ᵥ family 2 = 0) := by
  refine exists_orthogonalMatching_of_unitTightFamily family _ hunit hframe fun index => ?_
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, atomMatrix_mulVec_eq_smul, haxisOrthogonal index,
    zero_smul, sub_zero]

/-! ## The converse, and the classification as an equivalence -/

/-- Two orthonormal planar vectors resolve the identity. -/
theorem add_atomMatrix_eq_one_of_planarOrthonormalPair {leftVec rightVec : Fin 2 → ℝ}
    (hleft : leftVec ⬝ᵥ leftVec = 1) (hright : rightVec ⬝ᵥ rightVec = 1)
    (horthogonal : leftVec ⬝ᵥ rightVec = 0) :
    atomMatrix leftVec + atomMatrix rightVec = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hunitFrame : ∀ index : Fin 2,
      (![leftVec, rightVec] : Fin 2 → Fin 2 → ℝ) index ⬝ᵥ
        (![leftVec, rightVec] : Fin 2 → Fin 2 → ℝ) index = 1 := by
    intro index
    fin_cases index
    · exact hleft
    · exact hright
  have horthogonalFrame : ∀ leftIndex rightIndex : Fin 2, leftIndex ≠ rightIndex →
      (![leftVec, rightVec] : Fin 2 → Fin 2 → ℝ) leftIndex ⬝ᵥ
        (![leftVec, rightVec] : Fin 2 → Fin 2 → ℝ) rightIndex = 0 := by
    intro leftIndex rightIndex
    fin_cases leftIndex <;> fin_cases rightIndex <;> intro hdistinct
    · exact absurd rfl hdistinct
    · exact horthogonal
    · rw [dotProduct_comm]; exact horthogonal
    · exact absurd rfl hdistinct
  have hframe := sum_atomMatrix_eq_one_of_orthonormalFrame _ hunitFrame horthogonalFrame
  rw [Fin.sum_univ_two] at hframe
  exact hframe

/-- **The converse of V5.**  Any planar four-family that splits into two
orthonormal pairs — in any of the three matchings — is a tight frame. -/
theorem sum_atomMatrix_eq_two_smul_one_of_orthogonalMatching (family : Fin 4 → Fin 2 → ℝ)
    (hunit : ∀ index, family index ⬝ᵥ family index = 1)
    (hmatching : (family 0 ⬝ᵥ family 1 = 0 ∧ family 2 ⬝ᵥ family 3 = 0)
      ∨ (family 0 ⬝ᵥ family 2 = 0 ∧ family 1 ⬝ᵥ family 3 = 0)
      ∨ (family 0 ⬝ᵥ family 3 = 0 ∧ family 1 ⬝ᵥ family 2 = 0)) :
    ∑ index, atomMatrix (family index) = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Fin.sum_univ_four, two_smul]
  rcases hmatching with ⟨hleft, hright⟩ | ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · rw [show atomMatrix (family 0) + atomMatrix (family 1) + atomMatrix (family 2)
        + atomMatrix (family 3)
      = (atomMatrix (family 0) + atomMatrix (family 1))
        + (atomMatrix (family 2) + atomMatrix (family 3)) from by abel,
      add_atomMatrix_eq_one_of_planarOrthonormalPair (hunit 0) (hunit 1) hleft,
      add_atomMatrix_eq_one_of_planarOrthonormalPair (hunit 2) (hunit 3) hright]
  · rw [show atomMatrix (family 0) + atomMatrix (family 1) + atomMatrix (family 2)
        + atomMatrix (family 3)
      = (atomMatrix (family 0) + atomMatrix (family 2))
        + (atomMatrix (family 1) + atomMatrix (family 3)) from by abel,
      add_atomMatrix_eq_one_of_planarOrthonormalPair (hunit 0) (hunit 2) hleft,
      add_atomMatrix_eq_one_of_planarOrthonormalPair (hunit 1) (hunit 3) hright]
  · rw [show atomMatrix (family 0) + atomMatrix (family 1) + atomMatrix (family 2)
        + atomMatrix (family 3)
      = (atomMatrix (family 0) + atomMatrix (family 3))
        + (atomMatrix (family 1) + atomMatrix (family 2)) from by abel,
      add_atomMatrix_eq_one_of_planarOrthonormalPair (hunit 0) (hunit 3) hleft,
      add_atomMatrix_eq_one_of_planarOrthonormalPair (hunit 1) (hunit 2) hright]

/-- **The classification of planar four-frames, as an equivalence.**  For four
unit vectors of `ℝ²`, being a tight frame IS being a union of two orthogonal
pairs.  Combined with `IsHollowInvolution.crossBlock_quarterTurn_of_zeroEdge`
this is the pen's moduli statement in full: the frames are the pairs of
orthogonal pairs, parameterised by their relative angle. -/
theorem planarTightFrame_iff_exists_orthogonalMatching (family : Fin 4 → Fin 2 → ℝ)
    (hunit : ∀ index, family index ⬝ᵥ family index = 1) :
    (∑ index, atomMatrix (family index) = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      ↔ ((family 0 ⬝ᵥ family 1 = 0 ∧ family 2 ⬝ᵥ family 3 = 0)
        ∨ (family 0 ⬝ᵥ family 2 = 0 ∧ family 1 ⬝ᵥ family 3 = 0)
        ∨ (family 0 ⬝ᵥ family 3 = 0 ∧ family 1 ⬝ᵥ family 2 = 0)) :=
  ⟨exists_orthogonalMatching_of_planarTightFrame family hunit,
    sum_atomMatrix_eq_two_smul_one_of_orthogonalMatching family hunit⟩

/-! ## The sharpness census: the rigidity holds at `m = 2` and `m = 4`, and nowhere else -/

/-- **`m = 2` is rigid, trivially.**  Two unit planar vectors whose atoms resolve
the identity are orthogonal: the Gram square law at level one reads
`1 + ⟨u,v⟩² = 1`. -/
theorem dotProduct_eq_zero_of_planarTightFrame_two (family : Fin 2 → Fin 2 → ℝ)
    (hunit : ∀ index, family index ⬝ᵥ family index = 1)
    (hframe : ∑ index, atomMatrix (family index) = (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    family 0 ⬝ᵥ family 1 = 0 := by
  have hgramSquare := gramSquare_of_tightOnPlane 1 family 1 hframe
    (fun index => Matrix.one_mulVec (family index)) 0 0
  rw [Fin.sum_univ_two, hunit 0] at hgramSquare
  have hsquare : (family 0 ⬝ᵥ family 1) ^ 2 = 0 := by
    rw [dotProduct_comm (family 1) (family 0)] at hgramSquare
    nlinarith [hgramSquare]
  exact sq_eq_zero_iff.mp hsquare

private theorem sqrtThree_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private theorem sqrtThree_lower : 1 < Real.sqrt 3 := by
  nlinarith [sqrtThree_sq, Real.sqrt_nonneg 3]

private theorem sqrtThree_upper : Real.sqrt 3 < 7 / 4 := by
  nlinarith [sqrtThree_sq, Real.sqrt_nonneg 3]

/-- The Mercedes frame: three unit planar vectors at `120` degrees. -/
noncomputable def mercedesPlanarFrame : Fin 3 → Fin 2 → ℝ :=
  ![![1, 0], ![-(1 / 2), Real.sqrt 3 / 2], ![-(1 / 2), -(Real.sqrt 3 / 2)]]

private theorem mercedesPlanarFrame_zero : mercedesPlanarFrame 0 = ![1, 0] := rfl
private theorem mercedesPlanarFrame_one :
    mercedesPlanarFrame 1 = ![-(1 / 2), Real.sqrt 3 / 2] := rfl
private theorem mercedesPlanarFrame_two :
    mercedesPlanarFrame 2 = ![-(1 / 2), -(Real.sqrt 3 / 2)] := rfl

/-- **`m = 3` is NOT rigid**, and not merely for parity reasons: the Mercedes
frame is a unit-norm tight frame of three pairwise non-parallel planar directions
in which NO two atoms are orthogonal — every pairing is `−1/2`. -/
theorem exists_planarTightFrame_three_without_orthogonalPair :
    ∃ family : Fin 3 → Fin 2 → ℝ,
      (∀ index, family index ⬝ᵥ family index = 1)
      ∧ (∀ leftIndex rightIndex, leftIndex ≠ rightIndex →
          (family leftIndex ⬝ᵥ family rightIndex) ^ 2 < 1)
      ∧ (∑ index, atomMatrix (family index)
          = ((3 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      ∧ (∀ leftIndex rightIndex, family leftIndex ⬝ᵥ family rightIndex ≠ 0) := by
  have hsquareFloor : ∀ leftIndex rightIndex : Fin 3,
      1 / 10 ≤ (mercedesPlanarFrame leftIndex ⬝ᵥ mercedesPlanarFrame rightIndex) ^ 2 := by
    intro leftIndex rightIndex
    fin_cases leftIndex <;> fin_cases rightIndex <;>
      norm_num [mercedesPlanarFrame, dotProduct, Fin.sum_univ_two] <;>
      nlinarith [sqrtThree_sq, sqrtThree_lower, sqrtThree_upper]
  have hsquareCap : ∀ leftIndex rightIndex : Fin 3, leftIndex ≠ rightIndex →
      (mercedesPlanarFrame leftIndex ⬝ᵥ mercedesPlanarFrame rightIndex) ^ 2 ≤ 99 / 100 := by
    intro leftIndex rightIndex
    fin_cases leftIndex <;> fin_cases rightIndex <;> intro hdistinct <;>
      first
        | exact absurd rfl hdistinct
        | (norm_num [mercedesPlanarFrame, dotProduct, Fin.sum_univ_two] <;>
            nlinarith [sqrtThree_sq, sqrtThree_lower, sqrtThree_upper])
  refine ⟨mercedesPlanarFrame, ?_, ?_, ?_, ?_⟩
  · intro index
    fin_cases index <;>
      norm_num [mercedesPlanarFrame, dotProduct, Fin.sum_univ_two] <;>
      nlinarith [sqrtThree_sq]
  · intro leftIndex rightIndex hdistinct
    linarith [hsquareCap leftIndex rightIndex hdistinct]
  · ext rowIndex colIndex
    rw [Matrix.sum_apply, Fin.sum_univ_three, mercedesPlanarFrame_zero, mercedesPlanarFrame_one,
      mercedesPlanarFrame_two]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      (norm_num [atomMatrix, Matrix.vecMulVec_apply, Matrix.one_apply]
        <;> nlinarith [sqrtThree_sq])
  · intro leftIndex rightIndex hvanishes
    have hfloor := hsquareFloor leftIndex rightIndex
    rw [hvanishes] at hfloor
    norm_num at hfloor

/-- Two Mercedes frames at the rational relative rotation `(3/5, 4/5)`: six unit
planar vectors, tight at level three. -/
noncomputable def doubleMercedesPlanarFrame : Fin 6 → Fin 2 → ℝ :=
  ![![1, 0],
    ![-(1 / 2), Real.sqrt 3 / 2],
    ![-(1 / 2), -(Real.sqrt 3 / 2)],
    ![3 / 5, 4 / 5],
    ![-(3 + 4 * Real.sqrt 3) / 10, (3 * Real.sqrt 3 - 4) / 10],
    ![(4 * Real.sqrt 3 - 3) / 10, -(4 + 3 * Real.sqrt 3) / 10]]

private theorem doubleMercedesPlanarFrame_zero : doubleMercedesPlanarFrame 0 = ![1, 0] := rfl
private theorem doubleMercedesPlanarFrame_one :
    doubleMercedesPlanarFrame 1 = ![-(1 / 2), Real.sqrt 3 / 2] := rfl
private theorem doubleMercedesPlanarFrame_two :
    doubleMercedesPlanarFrame 2 = ![-(1 / 2), -(Real.sqrt 3 / 2)] := rfl
private theorem doubleMercedesPlanarFrame_three : doubleMercedesPlanarFrame 3 = ![3 / 5, 4 / 5] :=
  rfl
private theorem doubleMercedesPlanarFrame_four :
    doubleMercedesPlanarFrame 4
      = ![-(3 + 4 * Real.sqrt 3) / 10, (3 * Real.sqrt 3 - 4) / 10] := rfl
private theorem doubleMercedesPlanarFrame_five :
    doubleMercedesPlanarFrame 5
      = ![(4 * Real.sqrt 3 - 3) / 10, -(4 + 3 * Real.sqrt 3) / 10] := rfl

set_option maxHeartbeats 2000000 in
/-- **`m = 6` is NOT rigid either, so the `(m, 2)` generalisation of V5 is FALSE
and no parity argument saves the even sizes.**  Two Mercedes frames at the
rational relative rotation `(3/5, 4/5)` form a unit-norm tight frame of six
pairwise non-parallel planar directions containing NO orthogonal pair at all:
the fifteen pairings are `−1/2` (six times), `3/5` (three times),
`−(3 + 4√3)/10` (three times) and `(4√3 − 3)/10` (three times).

Bloch reading (`Gtz.blochSquare`): a unit-norm planar tight frame is a family of
points on the unit circle summing to zero and an orthogonal pair is an antipodal
pair.  Two equilateral triangles at a generic relative rotation sum to zero and
have no antipodal pair — the rigidity is a fact about FOUR points and about no
other count. -/
theorem exists_planarTightFrame_six_without_orthogonalPair :
    ∃ family : Fin 6 → Fin 2 → ℝ,
      (∀ index, family index ⬝ᵥ family index = 1)
      ∧ (∀ leftIndex rightIndex, leftIndex ≠ rightIndex →
          (family leftIndex ⬝ᵥ family rightIndex) ^ 2 < 1)
      ∧ (∑ index, atomMatrix (family index) = (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      ∧ (∀ leftIndex rightIndex, family leftIndex ⬝ᵥ family rightIndex ≠ 0) := by
  have hsquareFloor : ∀ leftIndex rightIndex : Fin 6,
      1 / 10 ≤ (doubleMercedesPlanarFrame leftIndex ⬝ᵥ doubleMercedesPlanarFrame rightIndex) ^ 2 := by
    intro leftIndex rightIndex
    fin_cases leftIndex <;> fin_cases rightIndex <;>
      norm_num [doubleMercedesPlanarFrame, dotProduct, Fin.sum_univ_two] <;>
      nlinarith [sqrtThree_sq, sqrtThree_lower, sqrtThree_upper]
  have hsquareCap : ∀ leftIndex rightIndex : Fin 6, leftIndex ≠ rightIndex →
      (doubleMercedesPlanarFrame leftIndex ⬝ᵥ doubleMercedesPlanarFrame rightIndex) ^ 2
        ≤ 99 / 100 := by
    intro leftIndex rightIndex
    fin_cases leftIndex <;> fin_cases rightIndex <;> intro hdistinct <;>
      first
        | exact absurd rfl hdistinct
        | (norm_num [doubleMercedesPlanarFrame, dotProduct, Fin.sum_univ_two] <;>
            nlinarith [sqrtThree_sq, sqrtThree_lower, sqrtThree_upper])
  refine ⟨doubleMercedesPlanarFrame, ?_, ?_, ?_, ?_⟩
  · intro index
    fin_cases index <;>
      norm_num [doubleMercedesPlanarFrame, dotProduct, Fin.sum_univ_two] <;>
      nlinarith [sqrtThree_sq]
  · intro leftIndex rightIndex hdistinct
    linarith [hsquareCap leftIndex rightIndex hdistinct]
  · ext rowIndex colIndex
    rw [Matrix.sum_apply, Fin.sum_univ_six, doubleMercedesPlanarFrame_zero,
      doubleMercedesPlanarFrame_one, doubleMercedesPlanarFrame_two,
      doubleMercedesPlanarFrame_three, doubleMercedesPlanarFrame_four,
      doubleMercedesPlanarFrame_five]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [atomMatrix, Matrix.vecMulVec_apply, Matrix.one_apply] <;>
      nlinarith [sqrtThree_sq]
  · intro leftIndex rightIndex hvanishes
    have hfloor := hsquareFloor leftIndex rightIndex
    rw [hvanishes] at hfloor
    norm_num at hfloor

/-! ## The merge boundary: axis plus orthogonal pair dominates at every weight -/

/-- The two names for the normalised atom agree definitionally.  `Gtz.unitAtom` is
design-indexed (`Gtz/Design/FrameConservation.lean`) and `Gtz.unitDirection` is
vector-indexed (`Gtz/Design/DominationGates.lean`); this file states everything in
the second, and the frontier layer works in the first. -/
theorem unitDirection_atom_eq_unitAtom (D : WeightedDesign size rank) (atomIndex : Fin size) :
    unitDirection (D.atom atomIndex) = unitAtom D atomIndex := rfl

/-- **The residue of a saturated axis is a planar tight frame.**  On the stratum
where one atom carries share one and every other atom carries share one half — the
merge boundary of the `(6,3)` collar, where a near-parallel pair has fused into a
single saturated atom — the unit directions off the axis resolve exactly twice the
axis's orthogonal projector, which is the hypothesis
`exists_orthogonalMatching_of_axisTightResidue` consumes.

Pen argument: rewrite the design equation `Σ_c t_c g_c g_cᵀ = 1` in unit
directions, where the `c`-th term is `s_c · u_c u_cᵀ` with `s_c` the share.  The
axis contributes `u_a u_aᵀ` and every other atom contributes `(1/2) u_c u_cᵀ`. -/
theorem sum_atomMatrix_unitDirection_erase_of_saturatedAxis (D : WeightedDesign size rank)
    (axisIndex : Fin size)
    (hpositive : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex))
    (haxisShare : D.weight axisIndex * leverageOf (D.atom axisIndex) = 1)
    (hresidueShare : ∀ atomIndex, atomIndex ≠ axisIndex →
      D.weight atomIndex * leverageOf (D.atom atomIndex) = 1 / 2) :
    ∑ atomIndex ∈ Finset.univ.erase axisIndex,
        atomMatrix (unitDirection (D.atom atomIndex))
      = (2 : ℝ) • ((1 : Matrix (Fin rank) (Fin rank) ℝ)
        - atomMatrix (unitDirection (D.atom axisIndex))) := by
  classical
  have hshareForm : ∀ atomIndex : Fin size,
      D.weight atomIndex • atomMatrix (D.atom atomIndex)
        = (D.weight atomIndex * leverageOf (D.atom atomIndex))
          • atomMatrix (unitDirection (D.atom atomIndex)) := by
    intro atomIndex
    rw [mul_smul, leverage_smul_atomMatrix_unitDirection (hpositive atomIndex)]
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun atomIndex => D.weight atomIndex • atomMatrix (D.atom atomIndex))
    (Finset.mem_univ axisIndex)
  rw [D.isParseval] at hsplit
  have hresidueSum : ∑ atomIndex ∈ Finset.univ.erase axisIndex,
      D.weight atomIndex • atomMatrix (D.atom atomIndex)
      = ((1 : ℝ) / 2) • ∑ atomIndex ∈ Finset.univ.erase axisIndex,
          atomMatrix (unitDirection (D.atom atomIndex)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun atomIndex hmember => ?_
    rw [hshareForm atomIndex, hresidueShare atomIndex (Finset.ne_of_mem_erase hmember)]
  rw [hresidueSum, hshareForm axisIndex, haxisShare, one_smul] at hsplit
  have hhalf : ((1 : ℝ) / 2) • ∑ atomIndex ∈ Finset.univ.erase axisIndex,
        atomMatrix (unitDirection (D.atom atomIndex))
      = (1 : Matrix (Fin rank) (Fin rank) ℝ) - atomMatrix (unitDirection (D.atom axisIndex)) := by
    rw [← hsplit]
    abel
  calc ∑ atomIndex ∈ Finset.univ.erase axisIndex,
        atomMatrix (unitDirection (D.atom atomIndex))
      = ((2 : ℝ) * ((1 : ℝ) / 2)) • ∑ atomIndex ∈ Finset.univ.erase axisIndex,
          atomMatrix (unitDirection (D.atom atomIndex)) := by
        rw [show ((2 : ℝ) * ((1 : ℝ) / 2)) = 1 by norm_num, one_smul]
    _ = (2 : ℝ) • (((1 : ℝ) / 2) • ∑ atomIndex ∈ Finset.univ.erase axisIndex,
          atomMatrix (unitDirection (D.atom atomIndex))) := by rw [mul_smul]
    _ = (2 : ℝ) • ((1 : Matrix (Fin rank) (Fin rank) ℝ)
          - atomMatrix (unitDirection (D.atom axisIndex))) := by rw [hhalf]

/-- Orthogonality of unit directions is orthogonality of the atoms, when both
leverages are positive. -/
theorem dotProduct_eq_zero_of_unitDirection_dotProduct_eq_zero {leftVec rightVec : Fin rank → ℝ}
    (hleftPositive : 0 < leverageOf leftVec) (hrightPositive : 0 < leverageOf rightVec)
    (horthogonal : unitDirection leftVec ⬝ᵥ unitDirection rightVec = 0) :
    leftVec ⬝ᵥ rightVec = 0 := by
  rw [unitDirection_dotProduct] at horthogonal
  have hleftNonzero : (Real.sqrt (leverageOf leftVec))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hleftPositive))
  have hrightNonzero : (Real.sqrt (leverageOf rightVec))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hrightPositive))
  rcases mul_eq_zero.mp horthogonal with hscalar | hpairing
  · exact absurd hscalar (mul_ne_zero hleftNonzero hrightNonzero)
  · exact hpairing

/-- **The merge-boundary corollary.**  A rank-three design with a heavy axis atom
orthogonal to four heavy atoms whose unit directions resolve twice the axis's
orthogonal projector has a dominating triple through the axis — and domination is
weight-free, so this holds at EVERY weight vector on the stratum.

Pen argument (V5): the four residue directions form a planar tight frame in the
axis's orthogonal complement, so by
`exists_orthogonalMatching_of_axisTightResidue` two of them are orthogonal; with
the axis that is a pairwise-orthogonal triple, and
`Gtz.dominates_of_orthogonalTriple_of_one_le` finishes.  The near-parallel collar
of the `(6,3)` stratum is therefore covered by a WEIGHT-INDEPENDENT mechanism. -/
theorem exists_dominating_triple_of_axisTightResidue (D : WeightedDesign size 3)
    (axisIndex : Fin size) (pick : Fin 4 → Fin size) (hinjective : Function.Injective pick)
    (haxisDistinct : ∀ index, pick index ≠ axisIndex)
    (haxisHeavy : 1 ≤ leverageOf (D.atom axisIndex))
    (hresidueHeavy : ∀ index, 1 ≤ leverageOf (D.atom (pick index)))
    (haxisOrthogonal : ∀ index, D.atom axisIndex ⬝ᵥ D.atom (pick index) = 0)
    (hresidueTight : ∑ index, atomMatrix (unitDirection (D.atom (pick index)))
      = (2 : ℝ) • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - atomMatrix (unitDirection (D.atom axisIndex)))) :
    ∃ leftIndex rightIndex : Fin 4, leftIndex ≠ rightIndex ∧
      Dominates D {axisIndex, pick leftIndex, pick rightIndex} := by
  have haxisPositive : 0 < leverageOf (D.atom axisIndex) := lt_of_lt_of_le zero_lt_one haxisHeavy
  have hresiduePositive : ∀ index, 0 < leverageOf (D.atom (pick index)) :=
    fun index => lt_of_lt_of_le zero_lt_one (hresidueHeavy index)
  have hmatching := exists_orthogonalMatching_of_axisTightResidue
    (axis := unitDirection (D.atom axisIndex))
    (fun index => unitDirection (D.atom (pick index)))
    (fun index => unitDirection_dotProduct_self (hresiduePositive index))
    (fun index => unitDirection_dotProduct_eq_zero (haxisOrthogonal index))
    hresidueTight
  have hassemble : ∀ leftIndex rightIndex : Fin 4, leftIndex ≠ rightIndex →
      unitDirection (D.atom (pick leftIndex)) ⬝ᵥ unitDirection (D.atom (pick rightIndex)) = 0 →
      ∃ leftLabel rightLabel : Fin 4, leftLabel ≠ rightLabel ∧
        Dominates D {axisIndex, pick leftLabel, pick rightLabel} := by
    intro leftIndex rightIndex hdistinct horthogonal
    refine ⟨leftIndex, rightIndex, hdistinct, ?_⟩
    exact dominates_of_orthogonalTriple_of_one_le D (Ne.symm (haxisDistinct leftIndex))
      (Ne.symm (haxisDistinct rightIndex))
      (fun hcontra => hdistinct (hinjective hcontra)) haxisHeavy (hresidueHeavy leftIndex)
      (hresidueHeavy rightIndex) (haxisOrthogonal leftIndex) (haxisOrthogonal rightIndex)
      (dotProduct_eq_zero_of_unitDirection_dotProduct_eq_zero (hresiduePositive leftIndex)
        (hresiduePositive rightIndex) horthogonal)
  rcases hmatching with ⟨hleft, _⟩ | ⟨hleft, _⟩ | ⟨hleft, _⟩
  · exact hassemble 0 1 (by decide) hleft
  · exact hassemble 0 2 (by decide) hleft
  · exact hassemble 0 3 (by decide) hleft

/-- **The merge boundary, assembled from the stratum data alone.**  A rank-three
design whose axis atom carries share one, whose four remaining atoms carry share
one half, and whose leverages are all at least one has a dominating triple
through the axis.  Every hypothesis is share arithmetic; nothing geometric is
asked of the caller.

The three ingredients: saturation forces every other atom orthogonal to the axis
(`Gtz.dotProduct_eq_zero_of_weightedLeverage_eq_one`); the shares turn the design
equation into the planar tight-frame equation on the residue
(`sum_atomMatrix_unitDirection_erase_of_saturatedAxis`); and V5 plus
`Gtz.dominates_of_orthogonalTriple_of_one_le` finish
(`exists_dominating_triple_of_axisTightResidue`).  Note the enumeration
hypothesis `himage` forces `size = 5`, which is exactly the merge boundary of the
`(6,3)` stratum: one fused atom of share one plus four survivors of share one
half, total share three. -/
theorem exists_dominating_triple_of_saturatedAxisStratum (D : WeightedDesign size 3)
    (axisIndex : Fin size) (pick : Fin 4 → Fin size) (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = Finset.univ.erase axisIndex)
    (hpositive : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex))
    (haxisShare : D.weight axisIndex * leverageOf (D.atom axisIndex) = 1)
    (hresidueShare : ∀ atomIndex, atomIndex ≠ axisIndex →
      D.weight atomIndex * leverageOf (D.atom atomIndex) = 1 / 2)
    (haxisHeavy : 1 ≤ leverageOf (D.atom axisIndex))
    (hresidueHeavy : ∀ index, 1 ≤ leverageOf (D.atom (pick index))) :
    ∃ leftIndex rightIndex : Fin 4, leftIndex ≠ rightIndex ∧
      Dominates D {axisIndex, pick leftIndex, pick rightIndex} := by
  classical
  have haxisDistinct : ∀ index, pick index ≠ axisIndex := by
    intro index
    have hmember : pick index ∈ Finset.image pick Finset.univ :=
      Finset.mem_image_of_mem pick (Finset.mem_univ index)
    rw [himage] at hmember
    exact Finset.ne_of_mem_erase hmember
  refine exists_dominating_triple_of_axisTightResidue D axisIndex pick hinjective haxisDistinct
    haxisHeavy hresidueHeavy (fun index => ?_) ?_
  · rw [dotProduct_comm]
    exact dotProduct_eq_zero_of_weightedLeverage_eq_one D haxisShare (haxisDistinct index)
  · rw [← sum_atomMatrix_unitDirection_erase_of_saturatedAxis D axisIndex hpositive haxisShare
      hresidueShare, ← himage,
      Finset.sum_image fun leftIndex _ rightIndex _ hequal => hinjective hequal]

end Gtz
