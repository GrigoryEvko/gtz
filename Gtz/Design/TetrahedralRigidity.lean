/-
# The tetrahedral degeneration of the `(6,3)` all-tied locus

**The question inherited.**  Is `{D : WeightedDesign 6 3 | ∀ C, C.card = 3 → Dominates D C}`
empty?  The sibling lane measured that it is, with ZERO MARGIN, and proved
`weightPositivity_isIndispensable`: the projection data, the twenty block inequalities
and `∑ t = 1` are together CONSISTENT — the `(4,3)` tetrahedron padded with two
weightless atoms satisfies all of them — so any refutation must consume strict
positivity of all six weights, and no certificate with slack can exist.

This file mechanizes the mechanism by which strict positivity is consumed, kills the
tetrahedral stratum outright, and reduces emptiness to one named premise.

**The coordinates.**  With `a_c := sqrt(t_c) g_c` and `P := A Aᵀ` the design projection
on the index space, `dominates_iff_posSemidef_projectionBlock` reads domination off `P`:
`Dominates D C  ↔  P[C,C] ⪰ diag(t_C)`.  Write `alpha_c := P_cc − t_c` for the gap
diagonal, so `∑_c alpha_c = 3 − 1 = 2`, and `alpha_c ≥ 0` whenever any triple through
`c` dominates.

## The unconditional content

**(1) The pivot inequality** (`pivotPairInequality`).  Fix an atom `p` and any two
others `i, j`.  Domination of the single triple `{i,j,p}` forces, for every
`(x_i, x_j) ∈ ℝ²`,

        (x_i P_ip + x_j P_jp)²  ≤  P_pp · ( alpha_i x_i² + 2 P_ij x_i x_j + alpha_j x_j² ).

This is the Schur complement of the pivot corner, with the corner value `alpha_p`
relaxed to `P_pp = alpha_p + t_p`; the relaxation is exactly where `t_p > 0` is spent,
and the proof needs no case split and no square root.  Geometrically, writing
`n := a_p/‖a_p‖` and `w_c := ⟨a_c, n⟩ = P_cp/sqrt(P_pp)`, it says
`[[alpha_i, P_ij], [P_ij, alpha_j]] ⪰ w wᵀ` — an `eps`-free condition that survives the
degeneration `a_p → 0` because `n` survives it.  `P_pp > 0` is not an assumption: it
follows from `alpha_p ≥ 0` and `t_p > 0` (`pivotLeverage_pos`).

**(2) The `3/8` law** (`pairQuadratic_le_of_nearTetrahedralPair`, and its exact case
`pairQuadratic_le_of_tetrahedralPair`).  At the tetrahedron the left block is
`[[1/2, −1/4], [−1/4, 1/2]]`, whose inverse is `[[8/3, 4/3], [4/3, 8/3]]`, so
`w B⁻¹ wᵀ ≤ 1` reads

        w_i² + w_i w_j + w_j²  ≤  3/8.

Mechanized by testing (1) at the optimal probe `(x_i, x_j) = (2w_i + w_j, w_i + 2w_j)`,
which turns the pivot inequality into `4 Q² ≤ (3/2) Q` for `Q` the pair form — exactly
`Q ≤ 3/8`, with no eigenvalues and no inverse ever written down.  The perturbed version
carries an explicit constant: within `tolerance` of the tetrahedral block,
`Q ≤ P_pp (3/8 + 3·tolerance)`, from the two ring identities
`(2a+b)² + (a+2b)² = 6Q − (a−b)²` and `2|xy| ≤ x² + y²`.

**(3) The averaging brick** (`exists_pair_exceeding_threshold`).  Over four indices the
six pair forms total `3 ∑ w² + e₂(w)`, and `e₂(w) = ((∑w)² − ∑w²)/2 ≥ −(∑w²)/2`, so the
total is at least `(5/2) ∑ w²`; at `∑ w² = 1` the maximum is at least `5/12 > 3/8`.

**The sum-zero hypothesis is REMOVABLE, and this file proves it.**  The brief's form
carries `∑ w = 0` — true at the tetrahedron, since its four atoms sum to zero — but the
bound `e₂ ≥ −(∑w²)/2` needs only `∑ w² = 1`; sum-zero is the equality case, not an
ingredient.  `exists_pair_exceeding_threshold` is the hypothesis-free statement and
`exists_tetrahedral_pair_exceeding_threshold` is the requested one, derived from it,
with the redundant hypothesis carried as an underscore.  The averaging bound `5/12` is
not tight: at `w = (1,−1,0,0)/sqrt 2` the six pair values are `{0, 1/2}`, and the sibling
lane MEASURED the minimax to be `1/2` — that measurement is neither used nor reproved
here.  What is used is `5/12 > 3/8`, with room `1/24`, and that room is the whole budget
below.

**(4) THE STRATUM THEOREM** (`not_isAllTied_of_hasApproxTetrahedralPivot`).  Combining
(1)–(3): NO all-tied `(6,3)` design has an approximately tetrahedral pivot at tolerance
`1/100`.  Chaining the constants, six copies of `Q ≤ P_pp(3/8 + 3δ)` against
`(5/2)(1−δ)P_pp` forces `δ ≥ 1/82`, so any `δ < 1/82` closes; `1/100` is the round
number below it.  This is unconditional, and it empties exactly the region into which
the sibling lane's measured `sigma → 1` sequence converges.

**(5) The stratum is inhabited — three explicit witnesses, all mechanized.**  Let `P` be
the projection of `tetraWitnessDesign`: four atoms along the tetrahedron directions
`(±1,±1,±1)` with an even number of minus signs, scaled by `101/100`, plus two zero
atoms.  Then `P_cc = 3/4` and `P_cd = −1/4` on the core and the whole atom-`5` column
vanishes, so:

  * `rigidityPadWeight_hasApproxTetrahedralPivot`: with the sibling's own relaxed weight
    `(1/4,1/4,1/4,1/4,0,0)` the stratum conditions hold at tolerance EXACTLY ZERO.  This
    is the padded tetrahedron of `tetraPadRelaxation_isSolvable`, and it is the point at
    which premise (b) below is anchored.
  * `witness_hasApproxTetrahedralPivot`: with the STRICTLY POSITIVE weight
    `(2500/10201)×4` and `(201/20402)×2` — chosen so that `t_c |g_c|² = 3/4` exactly —
    the stratum conditions hold at tolerance `201/40804 ≈ 0.00493 < 1/100`.  So an honest
    `WeightedDesign 6 3` lies in the stratum, and `witness_not_isAllTied` reads (4) off it.
  * `squashed_hasApproxTetrahedralPivot`: the same, but with `P_55 = 399/40000 > 0`.  Both
    witnesses above put `P_pp = 0` at the pivot, which satisfies the mass clause for free
    — whereas the proof of (4) only does work when `P_pp > 0`.  So `squashedDesign`
    squashes the tetrahedron by `199/200` along one axis and hands the recovered mass to
    atom `5`; its four gap diagonals are EXACTLY `1/2`, its off-diagonals miss `−1/4` by
    exactly `399/160000`, and its pivot leverage is strictly positive and inside the
    tolerance, as `pivotLeverage_le_tolerance_of_hasApproxTetrahedralPivot` says it must
    be.  `squashed_not_isAllTied` is (4) read off it.

**Exactly what the witnesses do and do not certify.**  They prove the hypothesis of (4)
is CONSISTENT with being a genuine strictly-positive-weight design, in both the `P_pp = 0`
and the `P_pp > 0` regimes, so (4) is not vacuous.  They do NOT show (4) is the cheapest
route to their conclusions: each of these three designs has a null atom, hence fails
all-tiedness for the elementary reason that a triple through a null atom has a negative
gap diagonal.  The content of (4) is not that these particular designs fail; it is that
NOTHING in the stratum can succeed.

Also mechanized: `pivotLeverage_le_tolerance_of_hasApproxTetrahedralPivot`.  Idempotence
gives `∑_c P_cp² = P_pp` exactly, hence `∑_{c≠p} P_cp² = P_pp(1 − P_pp)`, so the mass
clause forces `P_pp ≤ tolerance` — the hypothesis really does say the pivot atom is
nearly null and carries nearly all of its column mass on the four corners.

## What is CONDITIONAL, and on exactly what — two premises, honestly distinguished

**(a) The localization, `TetrahedralRigidityAtHundredth`**: every all-tied design has an
approximately tetrahedral pivot at `1/100`.  This yields emptiness
(`allTiedLocus_isEmpty_of_tetrahedralRigidity`) — but
`tetrahedralRigidity_iff_allTiedLocus_isEmpty` PROVES it is equivalent to emptiness,
because (4) makes the converse automatic.  So (a) relocates the problem and does not
reduce it; its value is that it names where to look, and the equivalence is stated so the
conditional cannot be read as more than it is.

**(b) The classification, `RelaxedTetrahedralClassification`**: every solution of the
RELAXED system — a symmetric idempotent of trace `3`, weights only `≥ 0` summing to one,
and all twenty block inequalities — has an approximately tetrahedral pivot at `1/100`.
This is NOT equivalent to emptiness: the relaxed solution set is nonempty by the
sibling's `tetraPadRelaxation_isSolvable` (cited, not re-proved here) and is constrained
by (b) whether or not the all-tied locus is empty;
`rigidityPadWeight_hasApproxTetrahedralPivot` confirms (b) at that known point.
`allTiedLocus_isEmpty_of_relaxedClassification` derives emptiness from (b) alone: an
all-tied design has `t > 0 ≥ 0`, so it IS a relaxed solution, and (4) finishes.  (b) is a
genuine classification target — "the relaxed solution set is the tetra-pad orbit" — and
it is strictly stronger than the goal, which is the price of not being vacuous.

Neither premise is proved here, and no evidence for either is offered beyond the
sibling's measured table.  Both are the rigidity / equality analysis at the tetrahedral
degeneration; the emptiness has zero margin (`V(eta) ≈ −0.82 eta`, vanishing linearly),
so no inequality with slack can establish either.

**What was measured and NOT proved.**  Two aggregation routes were computed by hand
against the tetrahedral limit and both are genuinely dead, as the sibling predicted.
First, summing the pivot inequality over the ten pairs at a fixed pivot gives
`A·tau − tau² + ∑ w_i² t_i ≤ e₂(alpha) − ∑ P_ij²`, violated by exactly `1/8` at the
tetrahedral limit when the pivot is a vanishing atom — but summing it over ALL SIX
pivots restores feasibility (`4 ≤ 4.5`), so the aggregate needs a canonical pivot choice
that no identity supplies.  Second, summing the twenty block determinants gives
`−2 + ∑ t_c P_cc + 3 e₂(t) + ∑ P_cc t_c² − e₃(t) ≥ 0`, exactly `0` at the tetrahedron and
about `−1.125 eta` just inside it — but `+0.296` at `t ≈ (1/3,1/3,1/3,0,0,0)` with
`P_cc = (1,1,1,0,0,0)`, so it does not close the cell.  Neither computation is mechanized
and neither is claimed as evidence for anything beyond the shape of the wall.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## The pair form and the averaging brick -/

/-- The pair form `w_i² + w_i w_j + w_j²` cut out by the tetrahedral block. -/
def pairQuadratic (firstValue secondValue : ℝ) : ℝ :=
  firstValue ^ 2 + firstValue * secondValue + secondValue ^ 2

theorem pairQuadratic_nonneg (firstValue secondValue : ℝ) :
    0 ≤ pairQuadratic firstValue secondValue := by
  unfold pairQuadratic
  nlinarith [sq_nonneg (firstValue + secondValue), sq_nonneg firstValue, sq_nonneg secondValue]

/-- **The six-pair identity.**  Over four indices the pair forms total
`3 ∑ w² + e₂(w)`, and `e₂(w) = ((∑ w)² − ∑ w²)/2`. -/
theorem sum_pairQuadratic_four (deviation : Fin 4 → ℝ) :
    pairQuadratic (deviation 0) (deviation 1) + pairQuadratic (deviation 0) (deviation 2)
        + pairQuadratic (deviation 0) (deviation 3) + pairQuadratic (deviation 1) (deviation 2)
        + pairQuadratic (deviation 1) (deviation 3) + pairQuadratic (deviation 2) (deviation 3)
      = 3 * (∑ index, deviation index ^ 2)
        + ((∑ index, deviation index) ^ 2 - ∑ index, deviation index ^ 2) / 2 := by
  simp only [Fin.sum_univ_four, pairQuadratic]
  ring

/-- **Brick 1, hypothesis-free form.**  Normalisation alone forces one of the six pair
forms above `3/8`: the six total at least `5/2`, so the largest is at least
`5/12 > 3/8`.  Sum-zero is the equality case of `e₂(w) ≥ −(∑ w²)/2`, not an ingredient. -/
theorem exists_pair_exceeding_threshold (deviation : Fin 4 → ℝ)
    (hnormalized : (∑ index, deviation index ^ 2) = 1) :
    ∃ firstIndex secondIndex : Fin 4, firstIndex ≠ secondIndex ∧
      3 / 8 < pairQuadratic (deviation firstIndex) (deviation secondIndex) := by
  by_contra hcontra
  have hbound : ∀ firstIndex secondIndex : Fin 4, firstIndex ≠ secondIndex →
      pairQuadratic (deviation firstIndex) (deviation secondIndex) ≤ 3 / 8 := by
    intro firstIndex secondIndex hdistinct
    by_contra hlarge
    exact hcontra ⟨firstIndex, secondIndex, hdistinct, not_le.mp hlarge⟩
  have hzeroOne := hbound 0 1 (by decide)
  have hzeroTwo := hbound 0 2 (by decide)
  have hzeroThree := hbound 0 3 (by decide)
  have honeTwo := hbound 1 2 (by decide)
  have honeThree := hbound 1 3 (by decide)
  have htwoThree := hbound 2 3 (by decide)
  have hidentity := sum_pairQuadratic_four deviation
  rw [hnormalized] at hidentity
  nlinarith [sq_nonneg (∑ index, deviation index)]

/-- **Brick 1 as requested.**  The sum-zero clause is carried as an underscore because
it is genuinely unused: `exists_pair_exceeding_threshold` proves the same conclusion
from normalisation alone, which IS the proof that the hypothesis is removable. -/
theorem exists_tetrahedral_pair_exceeding_threshold (deviation : Fin 4 → ℝ)
    (_hsumIsRedundant : (∑ index, deviation index) = 0)
    (hnormalized : (∑ index, deviation index ^ 2) = 1) :
    ∃ firstIndex secondIndex : Fin 4, firstIndex ≠ secondIndex ∧
      3 / 8 < deviation firstIndex ^ 2
        + deviation firstIndex * deviation secondIndex + deviation secondIndex ^ 2 :=
  exists_pair_exceeding_threshold deviation hnormalized

/-! ## The all-tied locus and the projection gap -/

/-- All twenty `3`-subsets of a `(6,3)` design dominate. -/
def IsAllTied (design : WeightedDesign 6 3) : Prop :=
  ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected

/-- The gap diagonal `alpha_c = P_cc − t_c`, on raw projection-and-weight data.
(Distinct from `Gtz.gapDiagonal`, which is the Gram-normalised `|g_c|² − 1`.) -/
def blockGapDiagonal (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ)
    (atomIndex : Fin 6) : ℝ :=
  projection atomIndex atomIndex - weight atomIndex

/-- Three distinct atoms give an injective selection map. -/
theorem injective_tripleSelect {Carrier : Type} (firstAtom secondAtom thirdAtom : Carrier)
    (hfirstSecond : firstAtom ≠ secondAtom) (hfirstThird : firstAtom ≠ thirdAtom)
    (hsecondThird : secondAtom ≠ thirdAtom) :
    Function.Injective ![firstAtom, secondAtom, thirdAtom] := by
  intro leftSlot rightSlot hvalues
  fin_cases leftSlot <;> fin_cases rightSlot <;> simp_all

/-- The quadratic form of a `3 × 3` positive semidefinite matrix, written out. -/
theorem quadraticForm_of_posSemidef_three {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : form.PosSemidef) (firstCoord secondCoord thirdCoord : ℝ) :
    0 ≤ form 0 0 * firstCoord ^ 2 + form 1 1 * secondCoord ^ 2 + form 2 2 * thirdCoord ^ 2
      + 2 * form 0 1 * firstCoord * secondCoord + 2 * form 0 2 * firstCoord * thirdCoord
      + 2 * form 1 2 * secondCoord * thirdCoord := by
  have hsymmetric : formᵀ = form := hpsd.1
  have hflipOne : form 1 0 = form 0 1 := by
    conv_lhs => rw [← hsymmetric]
    rfl
  have hflipTwo : form 2 0 = form 0 2 := by
    conv_lhs => rw [← hsymmetric]
    rfl
  have hflipThree : form 2 1 = form 1 2 := by
    conv_lhs => rw [← hsymmetric]
    rfl
  have hnonneg := hpsd.dotProduct_mulVec_nonneg ![firstCoord, secondCoord, thirdCoord]
  rw [star_trivial] at hnonneg
  have hexpand : ![firstCoord, secondCoord, thirdCoord]
        ⬝ᵥ (form *ᵥ ![firstCoord, secondCoord, thirdCoord])
      = form 0 0 * firstCoord ^ 2 + form 1 1 * secondCoord ^ 2 + form 2 2 * thirdCoord ^ 2
        + 2 * form 0 1 * firstCoord * secondCoord + 2 * form 0 2 * firstCoord * thirdCoord
        + 2 * form 1 2 * secondCoord * thirdCoord := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    rw [hflipOne, hflipTwo, hflipThree]
    ring
  rwa [hexpand] at hnonneg

/-- The block inequality of one dominating triple, as a scalar quadratic form. -/
theorem tripleBlockQuadratic_nonneg (design : WeightedDesign 6 3) (hallTied : IsAllTied design)
    (firstAtom secondAtom pivotAtom : Fin 6)
    (hfirstSecond : firstAtom ≠ secondAtom) (hfirstPivot : firstAtom ≠ pivotAtom)
    (hsecondPivot : secondAtom ≠ pivotAtom) (firstCoord secondCoord pivotCoord : ℝ) :
    0 ≤ blockGapDiagonal (projectionOfDesign design) design.weight firstAtom * firstCoord ^ 2
      + blockGapDiagonal (projectionOfDesign design) design.weight secondAtom * secondCoord ^ 2
      + blockGapDiagonal (projectionOfDesign design) design.weight pivotAtom * pivotCoord ^ 2
      + 2 * projectionOfDesign design firstAtom secondAtom * firstCoord * secondCoord
      + 2 * projectionOfDesign design firstAtom pivotAtom * firstCoord * pivotCoord
      + 2 * projectionOfDesign design secondAtom pivotAtom * secondCoord * pivotCoord := by
  have hinjective := injective_tripleSelect firstAtom secondAtom pivotAtom hfirstSecond
    hfirstPivot hsecondPivot
  have hcard : (Finset.image ![firstAtom, secondAtom, pivotAtom] Finset.univ).card = 3 := by
    rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]
  have hpsd := (dominates_iff_posSemidef_projectionBlock design _ hinjective).mp
    (hallTied _ hcard)
  simpa [blockGapDiagonal] using
    quadraticForm_of_posSemidef_three hpsd firstCoord secondCoord pivotCoord

/-! ## The pivot inequality

The Schur complement of the pivot corner.  Testing the block form at
`(P_pp x_i, P_pp x_j, −(x_i P_ip + x_j P_jp))` — a scaling chosen so that no division
appears — collapses the pivot row against the pivot corner and leaves

    P_pp² · (block form in i, j)  ≥  (P_pp + t_p) · (x_i P_ip + x_j P_jp)² .

Dropping the `t_p` and cancelling one `P_pp > 0` is the statement below.  The dropped
`t_p` is the strict-positivity budget: it is what makes the inequality survive the
limit `a_p → 0` rather than degenerating with it. -/

/-- **The pivot inequality, purely scalar.** -/
theorem pivotPairBound_of_blockQuadratic
    (gapFirst gapSecond crossFirstSecond crossFirstPivot crossSecondPivot
      pivotLeverage pivotWeight : ℝ)
    (hpivotWeight : 0 < pivotWeight)
    (hblock : ∀ firstCoord secondCoord pivotCoord : ℝ,
      0 ≤ gapFirst * firstCoord ^ 2 + gapSecond * secondCoord ^ 2
        + (pivotLeverage - pivotWeight) * pivotCoord ^ 2
        + 2 * crossFirstSecond * firstCoord * secondCoord
        + 2 * crossFirstPivot * firstCoord * pivotCoord
        + 2 * crossSecondPivot * secondCoord * pivotCoord) :
    0 < pivotLeverage ∧
      ∀ firstCoord secondCoord : ℝ,
        (firstCoord * crossFirstPivot + secondCoord * crossSecondPivot) ^ 2
          ≤ pivotLeverage * (gapFirst * firstCoord ^ 2
              + 2 * crossFirstSecond * firstCoord * secondCoord
              + gapSecond * secondCoord ^ 2) := by
  have hcorner := hblock 0 0 1
  have hleveragePos : 0 < pivotLeverage := by nlinarith [hcorner, hpivotWeight]
  refine ⟨hleveragePos, fun firstCoord secondCoord => ?_⟩
  have hscaled := hblock (pivotLeverage * firstCoord) (pivotLeverage * secondCoord)
    (-(firstCoord * crossFirstPivot + secondCoord * crossSecondPivot))
  have hexpand : gapFirst * (pivotLeverage * firstCoord) ^ 2
        + gapSecond * (pivotLeverage * secondCoord) ^ 2
        + (pivotLeverage - pivotWeight)
            * (-(firstCoord * crossFirstPivot + secondCoord * crossSecondPivot)) ^ 2
        + 2 * crossFirstSecond * (pivotLeverage * firstCoord) * (pivotLeverage * secondCoord)
        + 2 * crossFirstPivot * (pivotLeverage * firstCoord)
            * (-(firstCoord * crossFirstPivot + secondCoord * crossSecondPivot))
        + 2 * crossSecondPivot * (pivotLeverage * secondCoord)
            * (-(firstCoord * crossFirstPivot + secondCoord * crossSecondPivot))
      = pivotLeverage * (pivotLeverage * (gapFirst * firstCoord ^ 2
            + 2 * crossFirstSecond * firstCoord * secondCoord + gapSecond * secondCoord ^ 2))
        - (pivotLeverage + pivotWeight)
            * (firstCoord * crossFirstPivot + secondCoord * crossSecondPivot) ^ 2 := by
    ring
  rw [hexpand] at hscaled
  have hcancel : pivotLeverage
        * (firstCoord * crossFirstPivot + secondCoord * crossSecondPivot) ^ 2
      ≤ pivotLeverage * (pivotLeverage * (gapFirst * firstCoord ^ 2
          + 2 * crossFirstSecond * firstCoord * secondCoord + gapSecond * secondCoord ^ 2)) := by
    nlinarith [hscaled, hpivotWeight,
      sq_nonneg (firstCoord * crossFirstPivot + secondCoord * crossSecondPivot)]
  exact le_of_mul_le_mul_left hcancel hleveragePos

/-- The pivot atom of any dominating triple has strictly positive leverage. -/
theorem pivotLeverage_pos (design : WeightedDesign 6 3) (hallTied : IsAllTied design)
    (firstAtom secondAtom pivotAtom : Fin 6)
    (hfirstSecond : firstAtom ≠ secondAtom) (hfirstPivot : firstAtom ≠ pivotAtom)
    (hsecondPivot : secondAtom ≠ pivotAtom) :
    0 < projectionOfDesign design pivotAtom pivotAtom :=
  (pivotPairBound_of_blockQuadratic _ _ _ _ _ _ _ (design.weight_pos pivotAtom)
    (tripleBlockQuadratic_nonneg design hallTied firstAtom secondAtom pivotAtom
      hfirstSecond hfirstPivot hsecondPivot)).1

/-- **The pivot inequality on a design.**  Domination of the single triple `{i, j, p}`
bounds the pivot column against the `2 × 2` gap block of `i, j`. -/
theorem pivotPairInequality (design : WeightedDesign 6 3) (hallTied : IsAllTied design)
    (firstAtom secondAtom pivotAtom : Fin 6)
    (hfirstSecond : firstAtom ≠ secondAtom) (hfirstPivot : firstAtom ≠ pivotAtom)
    (hsecondPivot : secondAtom ≠ pivotAtom) (firstCoord secondCoord : ℝ) :
    (firstCoord * projectionOfDesign design firstAtom pivotAtom
        + secondCoord * projectionOfDesign design secondAtom pivotAtom) ^ 2
      ≤ projectionOfDesign design pivotAtom pivotAtom
        * (blockGapDiagonal (projectionOfDesign design) design.weight firstAtom * firstCoord ^ 2
            + 2 * projectionOfDesign design firstAtom secondAtom * firstCoord * secondCoord
            + blockGapDiagonal (projectionOfDesign design) design.weight secondAtom
                * secondCoord ^ 2) :=
  (pivotPairBound_of_blockQuadratic _ _ _ _ _ _ _ (design.weight_pos pivotAtom)
    (tripleBlockQuadratic_nonneg design hallTied firstAtom secondAtom pivotAtom
      hfirstSecond hfirstPivot hsecondPivot)).2 firstCoord secondCoord

/-! ## The `3/8` law

Testing the pivot inequality at `(x_i, x_j) = (2 w_i + w_j, w_i + 2 w_j)` — the probe
`B⁻¹ w` for the tetrahedral block, up to the harmless factor `3/4` — turns it into
`4 Q² ≤ P_pp (3/2) Q`, i.e. `Q ≤ (3/8) P_pp`.  Two ring identities carry the
perturbation: `(2a+b)² + (a+2b)² = 6Q − (a−b)²` bounds the probe norm by `6Q`, and
`2|xy| ≤ x² + y²` bounds the cross term. -/

/-- **The perturbed `3/8` law.**  Within `tolerance` of the tetrahedral gap block, the
pair form of the pivot column is at most `P_pp (3/8 + 3·tolerance)`. -/
theorem pairQuadratic_le_of_nearTetrahedralPair
    (pivotLeverage tolerance gapFirst gapSecond crossFirstSecond
      columnFirst columnSecond : ℝ)
    (htolerance : 0 ≤ tolerance) (hleverage : 0 ≤ pivotLeverage)
    (hgapFirst : |gapFirst - 1 / 2| ≤ tolerance)
    (hgapSecond : |gapSecond - 1 / 2| ≤ tolerance)
    (hcross : |crossFirstSecond + 1 / 4| ≤ tolerance)
    (hpivot : ∀ firstCoord secondCoord : ℝ,
      (firstCoord * columnFirst + secondCoord * columnSecond) ^ 2
        ≤ pivotLeverage * (gapFirst * firstCoord ^ 2
            + 2 * crossFirstSecond * firstCoord * secondCoord + gapSecond * secondCoord ^ 2)) :
    pairQuadratic columnFirst columnSecond ≤ pivotLeverage * (3 / 8 + 3 * tolerance) := by
  obtain ⟨_, hgapFirstHigh⟩ := abs_le.mp hgapFirst
  obtain ⟨_, hgapSecondHigh⟩ := abs_le.mp hgapSecond
  obtain ⟨hcrossLow, hcrossHigh⟩ := abs_le.mp hcross
  set probeFirst : ℝ := 2 * columnFirst + columnSecond with hprobeFirst
  set probeSecond : ℝ := columnFirst + 2 * columnSecond with hprobeSecond
  have hpairNonneg := pairQuadratic_nonneg columnFirst columnSecond
  have hprobeNormBound :
      probeFirst ^ 2 + probeSecond ^ 2 ≤ 6 * pairQuadratic columnFirst columnSecond := by
    rw [hprobeFirst, hprobeSecond, pairQuadratic]
    nlinarith [sq_nonneg (columnFirst - columnSecond)]
  have hcrossProbe : 2 * (crossFirstSecond + 1 / 4) * probeFirst * probeSecond
      ≤ tolerance * (probeFirst ^ 2 + probeSecond ^ 2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ tolerance - (crossFirstSecond + 1 / 4))
        (sq_nonneg (probeFirst + probeSecond)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ tolerance + (crossFirstSecond + 1 / 4))
        (sq_nonneg (probeFirst - probeSecond))]
  have hinnerBound : gapFirst * probeFirst ^ 2
        + 2 * crossFirstSecond * probeFirst * probeSecond + gapSecond * probeSecond ^ 2
      ≤ (3 / 2) * pairQuadratic columnFirst columnSecond
        + 12 * tolerance * pairQuadratic columnFirst columnSecond := by
    have htetra : (1 / 2 : ℝ) * probeFirst ^ 2
          + 2 * (-(1 / 4) : ℝ) * probeFirst * probeSecond + (1 / 2 : ℝ) * probeSecond ^ 2
        = (3 / 2) * pairQuadratic columnFirst columnSecond := by
      rw [hprobeFirst, hprobeSecond, pairQuadratic]
      ring
    have hfirstTerm : (gapFirst - 1 / 2) * probeFirst ^ 2 ≤ tolerance * probeFirst ^ 2 :=
      mul_le_mul_of_nonneg_right hgapFirstHigh (sq_nonneg probeFirst)
    have hsecondTerm : (gapSecond - 1 / 2) * probeSecond ^ 2 ≤ tolerance * probeSecond ^ 2 :=
      mul_le_mul_of_nonneg_right hgapSecondHigh (sq_nonneg probeSecond)
    have hscaleNorm : 2 * tolerance * (probeFirst ^ 2 + probeSecond ^ 2)
        ≤ 2 * tolerance * (6 * pairQuadratic columnFirst columnSecond) :=
      mul_le_mul_of_nonneg_left hprobeNormBound (by linarith)
    nlinarith [htetra, hfirstTerm, hsecondTerm, hcrossProbe, hscaleNorm]
  have hprobeValue : probeFirst * columnFirst + probeSecond * columnSecond
      = 2 * pairQuadratic columnFirst columnSecond := by
    rw [hprobeFirst, hprobeSecond, pairQuadratic]
    ring
  have hsquared := hpivot probeFirst probeSecond
  rw [hprobeValue] at hsquared
  have hscaleLeverage : pivotLeverage * (gapFirst * probeFirst ^ 2
        + 2 * crossFirstSecond * probeFirst * probeSecond + gapSecond * probeSecond ^ 2)
      ≤ pivotLeverage * ((3 / 2) * pairQuadratic columnFirst columnSecond
        + 12 * tolerance * pairQuadratic columnFirst columnSecond) :=
    mul_le_mul_of_nonneg_left hinnerBound hleverage
  have hmaster : 4 * pairQuadratic columnFirst columnSecond ^ 2
      ≤ pivotLeverage * pairQuadratic columnFirst columnSecond * (3 / 2 + 12 * tolerance) := by
    nlinarith [hsquared, hscaleLeverage]
  rcases eq_or_lt_of_le hpairNonneg with hzero | hpositive
  · rw [← hzero]
    positivity
  · nlinarith [hmaster, hpositive]

/-- **The exact `3/8` law.**  At the tetrahedral gap block the pair form of the pivot
column is at most `(3/8) P_pp`. -/
theorem pairQuadratic_le_of_tetrahedralPair
    (pivotLeverage gapFirst gapSecond crossFirstSecond columnFirst columnSecond : ℝ)
    (hleverage : 0 ≤ pivotLeverage)
    (hgapFirst : gapFirst = 1 / 2) (hgapSecond : gapSecond = 1 / 2)
    (hcross : crossFirstSecond = -(1 / 4))
    (hpivot : ∀ firstCoord secondCoord : ℝ,
      (firstCoord * columnFirst + secondCoord * columnSecond) ^ 2
        ≤ pivotLeverage * (gapFirst * firstCoord ^ 2
            + 2 * crossFirstSecond * firstCoord * secondCoord + gapSecond * secondCoord ^ 2)) :
    pairQuadratic columnFirst columnSecond ≤ pivotLeverage * (3 / 8) := by
  have hmain := pairQuadratic_le_of_nearTetrahedralPair pivotLeverage 0 gapFirst gapSecond
    crossFirstSecond columnFirst columnSecond le_rfl hleverage
    (by rw [hgapFirst]; norm_num) (by rw [hgapSecond]; norm_num)
    (by rw [hcross]; norm_num) hpivot
  linarith [hmain]

/-! ## The approximately tetrahedral stratum -/

/-- **The stratum.**  Projection-and-weight data has an approximately tetrahedral pivot
at `tolerance` when some atom `p` and four other distinct atoms satisfy: each of the four
gap diagonals is within `tolerance` of `1/2`, each of the six gap off-diagonals is within
`tolerance` of `−1/4`, and the four squared pivot-column entries carry at least
`(1 − tolerance)` of the pivot leverage.  This is exactly the tetrahedral degeneration of
the sibling lane's witness, read in projection coordinates. -/
def HasApproxTetrahedralPivot (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ)
    (tolerance : ℝ) : Prop :=
  ∃ (pivotAtom : Fin 6) (corner : Fin 4 → Fin 6),
    Function.Injective corner ∧
    (∀ slot, corner slot ≠ pivotAtom) ∧
    (∀ slot, |blockGapDiagonal projection weight (corner slot) - 1 / 2| ≤ tolerance) ∧
    (∀ leftSlot rightSlot, leftSlot ≠ rightSlot →
      |projection (corner leftSlot) (corner rightSlot) + 1 / 4| ≤ tolerance) ∧
    (1 - tolerance) * projection pivotAtom pivotAtom
      ≤ ∑ slot, projection (corner slot) pivotAtom ^ 2

/-- Idempotence, read on one column: `∑_c P_cp² = P_pp`. -/
theorem sum_sq_projectionColumn {projection : Matrix (Fin 6) (Fin 6) ℝ}
    (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection) (pivotAtom : Fin 6) :
    (∑ atomIndex, projection atomIndex pivotAtom ^ 2) = projection pivotAtom pivotAtom := by
  have hentry : ∑ atomIndex, projection pivotAtom atomIndex * projection atomIndex pivotAtom
      = projection pivotAtom pivotAtom := by
    have := congrArg (fun matrix => matrix pivotAtom pivotAtom) hidempotent
    simpa [Matrix.mul_apply] using this
  rw [← hentry]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  have hflip : projection pivotAtom atomIndex = projection atomIndex pivotAtom :=
    congrFun (congrFun hsymmetric atomIndex) pivotAtom
  rw [hflip, sq]

/-- A symmetric idempotent has nonnegative diagonal: it is a sum of squares. -/
theorem projectionDiagonal_nonneg {projection : Matrix (Fin 6) (Fin 6) ℝ}
    (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection) (pivotAtom : Fin 6) :
    0 ≤ projection pivotAtom pivotAtom := by
  rw [← sum_sq_projectionColumn hsymmetric hidempotent pivotAtom]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The stratum hypothesis is substantive.**  An approximately tetrahedral pivot has
leverage at most `tolerance`: idempotence caps the off-pivot column mass at
`P_pp(1 − P_pp)`, so demanding `(1 − tolerance) P_pp` of it on four corners forces the
pivot atom to be nearly null.  No domination hypothesis is used. -/
theorem pivotLeverage_le_tolerance_of_hasApproxTetrahedralPivot
    {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ} {tolerance : ℝ}
    (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection) (htolerance : 0 ≤ tolerance)
    (hstratum : HasApproxTetrahedralPivot projection weight tolerance) :
    ∃ pivotAtom : Fin 6, projection pivotAtom pivotAtom ≤ tolerance := by
  obtain ⟨pivotAtom, corner, hinjective, hoffPivot, _, _, hmass⟩ := hstratum
  refine ⟨pivotAtom, ?_⟩
  have hsubset : Finset.image corner Finset.univ ⊆ Finset.univ.erase pivotAtom := by
    intro element hmember
    obtain ⟨slot, _, hvalue⟩ := Finset.mem_image.mp hmember
    exact Finset.mem_erase.mpr ⟨hvalue ▸ hoffPivot slot, Finset.mem_univ _⟩
  have hcornerSum : (∑ slot, projection (corner slot) pivotAtom ^ 2)
      = ∑ element ∈ Finset.image corner Finset.univ, projection element pivotAtom ^ 2 := by
    rw [Finset.sum_image fun _ _ _ _ hvalue => hinjective hvalue]
  have hdominated : (∑ element ∈ Finset.image corner Finset.univ,
        projection element pivotAtom ^ 2)
      ≤ ∑ element ∈ Finset.univ.erase pivotAtom, projection element pivotAtom ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => sq_nonneg _
  have hsplit : (∑ element ∈ Finset.univ.erase pivotAtom, projection element pivotAtom ^ 2)
      + projection pivotAtom pivotAtom ^ 2 = projection pivotAtom pivotAtom := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ pivotAtom)]
    exact sum_sq_projectionColumn hsymmetric hidempotent pivotAtom
  have hleverageNonneg := projectionDiagonal_nonneg hsymmetric hidempotent pivotAtom
  rcases eq_or_lt_of_le hleverageNonneg with hzero | hpositive
  · linarith
  · nlinarith [hmass, hcornerSum, hdominated, hsplit, hpositive]

/-- **THE STRATUM THEOREM.**  No all-tied `(6,3)` design has an approximately
tetrahedral pivot at tolerance `1/100`.  Six copies of the perturbed `3/8` law against
the six-pair averaging identity force `tolerance ≥ 1/82`; `1/100` is below it.  This is
unconditional, and it empties exactly the region into which the sibling lane's measured
`sigma → 1` sequence converges. -/
theorem not_isAllTied_of_hasApproxTetrahedralPivot (design : WeightedDesign 6 3)
    (tolerance : ℝ) (htolerance : 0 ≤ tolerance) (hsmall : tolerance ≤ 1 / 100)
    (hstratum : HasApproxTetrahedralPivot (projectionOfDesign design) design.weight tolerance) :
    ¬ IsAllTied design := by
  intro hallTied
  obtain ⟨pivotAtom, corner, hinjective, hoffPivot, hgap, hcross, hmass⟩ := hstratum
  set columnEntry : Fin 4 → ℝ :=
    fun slot => projectionOfDesign design (corner slot) pivotAtom with hcolumnEntry
  set pivotLeverage : ℝ := projectionOfDesign design pivotAtom pivotAtom with hpivotLeverage
  have hleveragePos : 0 < pivotLeverage :=
    pivotLeverage_pos design hallTied (corner 0) (corner 1) pivotAtom
      (fun hvalue => absurd (hinjective hvalue) (by decide)) (hoffPivot 0) (hoffPivot 1)
  have hpairBound : ∀ leftSlot rightSlot : Fin 4, leftSlot ≠ rightSlot →
      pairQuadratic (columnEntry leftSlot) (columnEntry rightSlot)
        ≤ pivotLeverage * (3 / 8 + 3 * tolerance) := by
    intro leftSlot rightSlot hdistinct
    refine pairQuadratic_le_of_nearTetrahedralPair pivotLeverage tolerance
      (blockGapDiagonal (projectionOfDesign design) design.weight (corner leftSlot))
      (blockGapDiagonal (projectionOfDesign design) design.weight (corner rightSlot))
      (projectionOfDesign design (corner leftSlot) (corner rightSlot))
      (columnEntry leftSlot) (columnEntry rightSlot) htolerance hleveragePos.le
      (hgap leftSlot) (hgap rightSlot) (hcross leftSlot rightSlot hdistinct)
      fun firstCoord secondCoord => ?_
    exact pivotPairInequality design hallTied (corner leftSlot) (corner rightSlot) pivotAtom
      (fun hvalue => hdistinct (hinjective hvalue)) (hoffPivot leftSlot) (hoffPivot rightSlot)
      firstCoord secondCoord
  have hzeroOne := hpairBound 0 1 (by decide)
  have hzeroTwo := hpairBound 0 2 (by decide)
  have hzeroThree := hpairBound 0 3 (by decide)
  have honeTwo := hpairBound 1 2 (by decide)
  have honeThree := hpairBound 1 3 (by decide)
  have htwoThree := hpairBound 2 3 (by decide)
  have hidentity := sum_pairQuadratic_four columnEntry
  have hmassBound : (1 - tolerance) * pivotLeverage ≤ ∑ slot, columnEntry slot ^ 2 := hmass
  nlinarith [hidentity, hzeroOne, hzeroTwo, hzeroThree, honeTwo, honeThree, htwoThree,
    hmassBound, hleveragePos, sq_nonneg (∑ slot, columnEntry slot)]

/-! ## Two explicit points of the stratum

Four atoms along the tetrahedron directions `(±1, ±1, ±1)` with an even number of minus
signs, scaled by `101/100`, plus two zero atoms.  With the strictly positive weight
`2500/10201` on the core the scaling is exactly right for Parseval, since
`(2500/10201)·(101/100)² = 1/4`; the leftover `201/10201` is split between the two null
atoms.  The projection is then the padded tetrahedron: `P_cc = 3/4` and `P_cd = −1/4` on
the core, and the entire atom-`5` column vanishes. -/

/-- The four tetrahedron directions scaled by `101/100`, padded by two zero atoms. -/
noncomputable def tetraWitnessAtom : Fin 6 → (Fin 3 → ℝ) := fun atomIndex coord =>
  if atomIndex = 0 then 101 / 100
  else if atomIndex = 1 then (if coord = 0 then 101 / 100 else -(101 / 100))
  else if atomIndex = 2 then (if coord = 1 then 101 / 100 else -(101 / 100))
  else if atomIndex = 3 then (if coord = 2 then 101 / 100 else -(101 / 100))
  else 0

/-- The strictly positive weight: `2500/10201` on the core, `201/20402` on the padding. -/
noncomputable def witnessWeight : Fin 6 → ℝ := fun atomIndex =>
  if atomIndex = 4 ∨ atomIndex = 5 then 201 / 20402 else 2500 / 10201

theorem atomMatrix_apply_entry {rank : ℕ} (vector : Fin rank → ℝ) (rowIndex colIndex : Fin rank) :
    atomMatrix vector rowIndex colIndex = vector rowIndex * vector colIndex := rfl

theorem witnessWeight_pos (atomIndex : Fin 6) : 0 < witnessWeight atomIndex := by
  fin_cases atomIndex <;> simp [witnessWeight]

theorem witnessWeight_sum : ∑ atomIndex, witnessWeight atomIndex = 1 := by
  simp only [Fin.sum_univ_six]
  simp only [witnessWeight]
  norm_num [show ¬((0 : Fin 6) = 4 ∨ (0 : Fin 6) = 5) from by decide,
    show ¬((1 : Fin 6) = 4 ∨ (1 : Fin 6) = 5) from by decide,
    show ¬((2 : Fin 6) = 4 ∨ (2 : Fin 6) = 5) from by decide,
    show ¬((3 : Fin 6) = 4 ∨ (3 : Fin 6) = 5) from by decide,
    show ((4 : Fin 6) = 4 ∨ (4 : Fin 6) = 5) from by decide,
    show ((5 : Fin 6) = 4 ∨ (5 : Fin 6) = 5) from by decide]

theorem witnessParseval :
    ∑ atomIndex, witnessWeight atomIndex • atomMatrix (tetraWitnessAtom atomIndex) = 1 := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Fin.sum_univ_six, atomMatrix_apply_entry, tetraWitnessAtom, witnessWeight] <;> norm_num

/-- An honest `(6,3)` design sitting on the padded tetrahedron. -/
noncomputable def tetraWitnessDesign : WeightedDesign 6 3 where
  atom := tetraWitnessAtom
  weight := witnessWeight
  weight_pos := witnessWeight_pos
  weight_sum_one := witnessWeight_sum
  isParseval := witnessParseval

/-- The four core slots. -/
def witnessCorner : Fin 4 → Fin 6 := ![0, 1, 2, 3]

/-- Core atoms share one weight, so the two square roots collapse to it. -/
theorem witnessCoreEntry (leftIndex rightIndex : Fin 6)
    (hleft : witnessWeight leftIndex = 2500 / 10201)
    (hright : witnessWeight rightIndex = 2500 / 10201) :
    projectionOfDesign tetraWitnessDesign leftIndex rightIndex
      = 2500 / 10201 * (tetraWitnessAtom leftIndex ⬝ᵥ tetraWitnessAtom rightIndex) := by
  rw [projectionOfDesign_apply]
  show Real.sqrt (witnessWeight leftIndex) * Real.sqrt (witnessWeight rightIndex)
      * (tetraWitnessAtom leftIndex ⬝ᵥ tetraWitnessAtom rightIndex) = _
  rw [hleft, hright, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2500 / 10201)]

/-- The core block is exactly tetrahedral: `3/4` on the diagonal, `−1/4` off it. -/
theorem witnessCornerEntry (leftSlot rightSlot : Fin 4) :
    projectionOfDesign tetraWitnessDesign (witnessCorner leftSlot) (witnessCorner rightSlot)
      = if leftSlot = rightSlot then 3 / 4 else -(1 / 4) := by
  fin_cases leftSlot <;> fin_cases rightSlot <;>
    · rw [witnessCoreEntry _ _ (by simp [witnessCorner, witnessWeight])
        (by simp [witnessCorner, witnessWeight])]
      simp [witnessCorner, tetraWitnessAtom, dotProduct, Fin.sum_univ_three]
      norm_num

/-- The pivot column vanishes identically: atom `5` is the zero vector. -/
theorem witnessPivotColumn (atomIndex : Fin 6) :
    projectionOfDesign tetraWitnessDesign atomIndex 5 = 0 := by
  rw [projectionOfDesign_apply]
  show Real.sqrt (witnessWeight atomIndex) * Real.sqrt (witnessWeight 5)
      * (tetraWitnessAtom atomIndex ⬝ᵥ tetraWitnessAtom 5) = 0
  have hzero : tetraWitnessAtom 5 = fun _ => (0 : ℝ) := by
    funext coord
    simp [tetraWitnessAtom]
  rw [hzero]
  simp [dotProduct]

theorem witnessCornerWeight (slot : Fin 4) :
    tetraWitnessDesign.weight (witnessCorner slot) = 2500 / 10201 := by
  fin_cases slot <;> simp [witnessCorner, tetraWitnessDesign, witnessWeight]

/-- **An honest positive-weight design in the stratum.**  The gap diagonals sit at
`3/4 − 2500/10201`, off `1/2` by `201/40804 < 1/100`; the off-diagonals are exactly
`−1/4`; the pivot column and pivot leverage are exactly zero. -/
theorem witness_hasApproxTetrahedralPivot :
    HasApproxTetrahedralPivot (projectionOfDesign tetraWitnessDesign) tetraWitnessDesign.weight
      (1 / 100) := by
  refine ⟨5, witnessCorner, by decide, by decide, ?_, ?_, ?_⟩
  · intro slot
    rw [blockGapDiagonal, witnessCornerEntry slot slot, if_pos rfl, witnessCornerWeight slot,
      abs_le]
    constructor <;> norm_num
  · intro leftSlot rightSlot hdistinct
    rw [witnessCornerEntry leftSlot rightSlot, if_neg hdistinct]
    norm_num
  · simp [witnessPivotColumn]

/-- **The stratum theorem, read on the explicit design.**  This `(6,3)` design, with all
six weights strictly positive, provably fails to have all twenty triples dominating. -/
theorem witness_not_isAllTied : ¬ IsAllTied tetraWitnessDesign :=
  not_isAllTied_of_hasApproxTetrahedralPivot tetraWitnessDesign (1 / 100) (by norm_num) le_rfl
    witness_hasApproxTetrahedralPivot

/-- The sibling lane's relaxed weight on the same projection: uniform `1/4` on the
tetrahedron, zero on the padding. -/
noncomputable def rigidityPadWeight : Fin 6 → ℝ := fun atomIndex =>
  if atomIndex = 4 ∨ atomIndex = 5 then 0 else 1 / 4

/-- **The relaxed witness lies in the stratum at tolerance EXACTLY ZERO.**  This is
`tetraPadRelaxation_isSolvable`'s point — the `(4,3)` tetrahedron padded with two
weightless atoms — and it is where premise (b) below is anchored. -/
theorem rigidityPadWeight_hasApproxTetrahedralPivot :
    HasApproxTetrahedralPivot (projectionOfDesign tetraWitnessDesign) rigidityPadWeight 0 := by
  refine ⟨5, witnessCorner, by decide, by decide, ?_, ?_, ?_⟩
  · intro slot
    have hweight : rigidityPadWeight (witnessCorner slot) = 1 / 4 := by
      fin_cases slot <;> simp [witnessCorner, rigidityPadWeight]
    rw [blockGapDiagonal, witnessCornerEntry slot slot, if_pos rfl, hweight]
    norm_num
  · intro leftSlot rightSlot hdistinct
    rw [witnessCornerEntry leftSlot rightSlot, if_neg hdistinct]
    norm_num
  · simp [witnessPivotColumn]

/-! ## A stratum point with STRICTLY POSITIVE pivot leverage

The witness above has `P_pp = 0`, which makes the mass clause `(1 − delta)·0 ≤ 0` hold for
free; the stratum theorem's proof, by contrast, only does work when `P_pp > 0`.  So here
is a second honest design in the stratum, with `P_55 > 0`.  Squash the tetrahedron by
`199/200` along coordinate `0`, leave atom `4` null and give atom `5` the recovered mass
`a_5 = sqrt(399/40000) e_0`.  Choosing `t_c = (199/400)²` on the core makes `sqrt(t_c)`
rational, so every core atom `g_c = (v_c0, (200/199) v_c1, (200/199) v_c2)` is rational
and only `g_5 = (sqrt 2, 0, 0)` is not.  Then the four gap diagonals are EXACTLY `1/2`,
the six off-diagonals miss `−1/4` by exactly `399/160000`, and
`P_55 = 399/40000 ≈ 0.009975`, just inside the tolerance — as it must be, by
`pivotLeverage_le_tolerance_of_hasApproxTetrahedralPivot`.  The mass clause holds with
slack `399/1600000000`. -/

/-- The tetrahedron squashed by `199/200` along coordinate `0`, atom `4` null, atom `5`
carrying the recovered mass along coordinate `0`. -/
noncomputable def squashedAtom : Fin 6 → (Fin 3 → ℝ) := fun atomIndex coord =>
  if atomIndex = 4 then 0
  else if atomIndex = 5 then (if coord = 0 then Real.sqrt 2 else 0)
  else
    (if coord = 0 then 1 else 200 / 199) *
      (if atomIndex = 0 then 1
        else if atomIndex = 1 then (if coord = 0 then 1 else -1)
        else if atomIndex = 2 then (if coord = 1 then 1 else -1)
        else (if coord = 2 then 1 else -1))

noncomputable def squashedWeight : Fin 6 → ℝ := fun atomIndex =>
  if atomIndex = 4 ∨ atomIndex = 5 then 399 / 80000 else 39601 / 160000

theorem squashedWeight_pos (atomIndex : Fin 6) : 0 < squashedWeight atomIndex := by
  fin_cases atomIndex <;> simp [squashedWeight]

theorem squashedWeight_sum : ∑ atomIndex, squashedWeight atomIndex = 1 := by
  simp only [Fin.sum_univ_six]
  simp only [squashedWeight]
  norm_num [show ¬((0 : Fin 6) = 4 ∨ (0 : Fin 6) = 5) from by decide,
    show ¬((1 : Fin 6) = 4 ∨ (1 : Fin 6) = 5) from by decide,
    show ¬((2 : Fin 6) = 4 ∨ (2 : Fin 6) = 5) from by decide,
    show ¬((3 : Fin 6) = 4 ∨ (3 : Fin 6) = 5) from by decide,
    show ((4 : Fin 6) = 4 ∨ (4 : Fin 6) = 5) from by decide,
    show ((5 : Fin 6) = 4 ∨ (5 : Fin 6) = 5) from by decide]

theorem squashedParseval :
    ∑ atomIndex, squashedWeight atomIndex • atomMatrix (squashedAtom atomIndex) = 1 := by
  have hroot : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Fin.sum_univ_six, atomMatrix_apply_entry, squashedAtom, squashedWeight, hroot] <;>
    norm_num

noncomputable def squashedDesign : WeightedDesign 6 3 where
  atom := squashedAtom
  weight := squashedWeight
  weight_pos := squashedWeight_pos
  weight_sum_one := squashedWeight_sum
  isParseval := squashedParseval

def squashedCorner : Fin 4 → Fin 6 := ![0, 1, 2, 3]

theorem squashedCoreEntry (leftIndex rightIndex : Fin 6)
    (hleft : squashedWeight leftIndex = 39601 / 160000)
    (hright : squashedWeight rightIndex = 39601 / 160000) :
    projectionOfDesign squashedDesign leftIndex rightIndex
      = 39601 / 160000 * (squashedAtom leftIndex ⬝ᵥ squashedAtom rightIndex) := by
  rw [projectionOfDesign_apply]
  show Real.sqrt (squashedWeight leftIndex) * Real.sqrt (squashedWeight rightIndex)
      * (squashedAtom leftIndex ⬝ᵥ squashedAtom rightIndex) = _
  rw [hleft, hright, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 39601 / 160000)]

theorem squashedCornerDiagonal (slot : Fin 4) :
    projectionOfDesign squashedDesign (squashedCorner slot) (squashedCorner slot)
      = 119601 / 160000 := by
  fin_cases slot <;>
    · rw [squashedCoreEntry _ _ (by simp [squashedCorner, squashedWeight])
        (by simp [squashedCorner, squashedWeight])]
      simp [squashedCorner, squashedAtom, dotProduct, Fin.sum_univ_three]
      norm_num

theorem squashedCornerCrossBound (leftSlot rightSlot : Fin 4) (hdistinct : leftSlot ≠ rightSlot) :
    |projectionOfDesign squashedDesign (squashedCorner leftSlot) (squashedCorner rightSlot)
        + 1 / 4| ≤ 1 / 100 := by
  fin_cases leftSlot <;> fin_cases rightSlot <;>
    first
      | exact absurd rfl hdistinct
      | · rw [squashedCoreEntry _ _ (by simp [squashedCorner, squashedWeight])
            (by simp [squashedCorner, squashedWeight])]
          simp [squashedCorner, squashedAtom, dotProduct, Fin.sum_univ_three]
          rw [abs_le]
          constructor <;> norm_num

theorem squashedPivotDiagonal : projectionOfDesign squashedDesign 5 5 = 399 / 40000 := by
  rw [projectionOfDesign_diagonal]
  show squashedWeight 5 * leverageOf (squashedAtom 5) = _
  have hlevel : leverageOf (squashedAtom 5) = 2 := by
    simp [leverageOf, squashedAtom, Real.sq_sqrt]
  rw [hlevel]
  norm_num [squashedWeight]

theorem squashedPivotColumnSq (slot : Fin 4) :
    projectionOfDesign squashedDesign (squashedCorner slot) 5 ^ 2
      = 39601 / 160000 * (399 / 80000) * 2 := by
  have hleft : squashedWeight (squashedCorner slot) = 39601 / 160000 := by
    fin_cases slot <;> simp [squashedCorner, squashedWeight]
  have hright : squashedWeight 5 = 399 / 80000 := by simp [squashedWeight]
  have hdot : (squashedAtom (squashedCorner slot) ⬝ᵥ squashedAtom 5) ^ 2 = 2 := by
    fin_cases slot <;>
      simp [squashedCorner, squashedAtom, dotProduct, Real.sq_sqrt]
  rw [projectionOfDesign_apply]
  show (Real.sqrt (squashedWeight (squashedCorner slot)) * Real.sqrt (squashedWeight 5)
      * (squashedAtom (squashedCorner slot) ⬝ᵥ squashedAtom 5)) ^ 2 = _
  rw [mul_pow, mul_pow, Real.sq_sqrt (by rw [hleft]; norm_num),
    Real.sq_sqrt (by rw [hright]; norm_num), hleft, hright, hdot]

theorem squashedCornerWeight (slot : Fin 4) :
    squashedDesign.weight (squashedCorner slot) = 39601 / 160000 := by
  fin_cases slot <;> simp [squashedCorner, squashedDesign, squashedWeight]

theorem squashed_hasApproxTetrahedralPivot :
    HasApproxTetrahedralPivot (projectionOfDesign squashedDesign) squashedDesign.weight
      (1 / 100) := by
  refine ⟨5, squashedCorner, by decide, by decide, ?_, squashedCornerCrossBound, ?_⟩
  · intro slot
    rw [blockGapDiagonal, squashedCornerDiagonal slot, squashedCornerWeight slot]
    norm_num
  · rw [squashedPivotDiagonal]
    simp only [Fin.sum_univ_four, squashedPivotColumnSq]
    norm_num

/-- **The stratum theorem on the positive-leverage witness.** -/
theorem squashed_not_isAllTied : ¬ IsAllTied squashedDesign :=
  not_isAllTied_of_hasApproxTetrahedralPivot squashedDesign (1 / 100) (by norm_num) le_rfl
    squashed_hasApproxTetrahedralPivot

/-! ## The conditional emptiness, on two honestly distinguished premises -/

/-- **Premise (a), the LOCALIZATION.**  Every all-tied `(6,3)` design lies in the
approximately tetrahedral stratum at tolerance `1/100`. -/
def TetrahedralRigidityAtHundredth : Prop :=
  ∀ design : WeightedDesign 6 3, IsAllTied design →
    HasApproxTetrahedralPivot (projectionOfDesign design) design.weight (1 / 100)

/-- Premise (a) yields emptiness. -/
theorem allTiedLocus_isEmpty_of_tetrahedralRigidity (hrigidity : TetrahedralRigidityAtHundredth)
    (design : WeightedDesign 6 3) : ¬ IsAllTied design := fun hallTied =>
  not_isAllTied_of_hasApproxTetrahedralPivot design (1 / 100) (by norm_num) le_rfl
    (hrigidity design hallTied) hallTied

/-- **Premise (a) is EQUIVALENT to the conclusion**, because the stratum theorem makes
the converse automatic: if the locus is empty then rigidity holds vacuously.  So (a)
relocates the problem and does not reduce it.  Stated, and proved, so that the
conditional above cannot be read as more than it is. -/
theorem tetrahedralRigidity_iff_allTiedLocus_isEmpty :
    TetrahedralRigidityAtHundredth ↔ ∀ design : WeightedDesign 6 3, ¬ IsAllTied design := by
  refine ⟨allTiedLocus_isEmpty_of_tetrahedralRigidity, fun hempty design hallTied => ?_⟩
  exact absurd hallTied (hempty design)

/-- **Premise (b), the CLASSIFICATION.**  Every solution of the relaxed system — a
symmetric idempotent of trace `3`, weights only `≥ 0` summing to one, all twenty block
inequalities — lies in the approximately tetrahedral stratum at `1/100`.  The relaxed
solution set is nonempty (the sibling's `tetraPadRelaxation_isSolvable`) and
`rigidityPadWeight_hasApproxTetrahedralPivot` confirms (b) at that point, so unlike premise
(a) this is not vacuously implied by emptiness — it constrains a set known to be
inhabited. -/
def RelaxedTetrahedralClassification : Prop :=
  ∀ (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ),
    projectionᵀ = projection →
    projection * projection = projection →
    Matrix.trace projection = 3 →
    (∀ atomIndex, 0 ≤ weight atomIndex) →
    (∑ atomIndex, weight atomIndex) = 1 →
    (∀ pick : Fin 3 → Fin 6, Function.Injective pick →
      (projection.submatrix pick pick
        - Matrix.diagonal fun slot => weight (pick slot)).PosSemidef) →
    HasApproxTetrahedralPivot projection weight (1 / 100)

/-- An all-tied design is a solution of the relaxed system: strict positivity is
forgotten, everything else is already there. -/
theorem relaxedData_of_isAllTied (design : WeightedDesign 6 3) (hallTied : IsAllTied design) :
    (projectionOfDesign design)ᵀ = projectionOfDesign design ∧
      projectionOfDesign design * projectionOfDesign design = projectionOfDesign design ∧
      Matrix.trace (projectionOfDesign design) = 3 ∧
      (∀ atomIndex, 0 ≤ design.weight atomIndex) ∧
      (∑ atomIndex, design.weight atomIndex) = 1 ∧
      (∀ pick : Fin 3 → Fin 6, Function.Injective pick →
        ((projectionOfDesign design).submatrix pick pick
          - Matrix.diagonal fun slot => design.weight (pick slot)).PosSemidef) := by
  refine ⟨projectionOfDesign_transpose design, projectionOfDesign_mul_self design, ?_,
    fun atomIndex => (design.weight_pos atomIndex).le, design.weight_sum_one,
    fun pick hinjective => ?_⟩
  · rw [trace_projectionOfDesign design]
    norm_num
  · have hcard : (Finset.image pick Finset.univ).card = 3 := by
      rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]
    exact (dominates_iff_posSemidef_projectionBlock design pick hinjective).mp
      (hallTied _ hcard)

/-- **The conditional emptiness on premise (b).**  An all-tied design solves the relaxed
system, so the classification puts it in the stratum, and the stratum theorem kills it. -/
theorem allTiedLocus_isEmpty_of_relaxedClassification
    (hclassification : RelaxedTetrahedralClassification) (design : WeightedDesign 6 3) :
    ¬ IsAllTied design := by
  intro hallTied
  obtain ⟨hsymmetric, hidempotent, htrace, hnonneg, hsum, hblocks⟩ :=
    relaxedData_of_isAllTied design hallTied
  exact not_isAllTied_of_hasApproxTetrahedralPivot design (1 / 100) (by norm_num) le_rfl
    (hclassification (projectionOfDesign design) design.weight hsymmetric hidempotent htrace
      hnonneg hsum hblocks) hallTied

/-- The locus form: under the classification, no `(6,3)` design has all twenty of its
`3`-subsets dominating. -/
theorem not_exists_allTied_of_relaxedClassification
    (hclassification : RelaxedTetrahedralClassification) :
    ¬ ∃ design : WeightedDesign 6 3, IsAllTied design := by
  rintro ⟨design, hallTied⟩
  exact allTiedLocus_isEmpty_of_relaxedClassification hclassification design hallTied

end Gtz

#print axioms Gtz.exists_pair_exceeding_threshold
#print axioms Gtz.exists_tetrahedral_pair_exceeding_threshold
#print axioms Gtz.sum_pairQuadratic_four
#print axioms Gtz.pivotPairBound_of_blockQuadratic
#print axioms Gtz.pivotLeverage_pos
#print axioms Gtz.pivotPairInequality
#print axioms Gtz.pairQuadratic_le_of_tetrahedralPair
#print axioms Gtz.pairQuadratic_le_of_nearTetrahedralPair
#print axioms Gtz.sum_sq_projectionColumn
#print axioms Gtz.pivotLeverage_le_tolerance_of_hasApproxTetrahedralPivot
#print axioms Gtz.not_isAllTied_of_hasApproxTetrahedralPivot
#print axioms Gtz.witnessCornerEntry
#print axioms Gtz.witness_hasApproxTetrahedralPivot
#print axioms Gtz.witness_not_isAllTied
#print axioms Gtz.rigidityPadWeight_hasApproxTetrahedralPivot
#print axioms Gtz.squashedCornerDiagonal
#print axioms Gtz.squashedPivotDiagonal
#print axioms Gtz.squashed_hasApproxTetrahedralPivot
#print axioms Gtz.squashed_not_isAllTied
#print axioms Gtz.tetrahedralRigidity_iff_allTiedLocus_isEmpty
#print axioms Gtz.allTiedLocus_isEmpty_of_tetrahedralRigidity
#print axioms Gtz.relaxedData_of_isAllTied
#print axioms Gtz.allTiedLocus_isEmpty_of_relaxedClassification
#print axioms Gtz.not_exists_allTied_of_relaxedClassification
