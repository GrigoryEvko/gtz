/-
# The rank-four minor system, and why the compression lift cannot be completed

Two things live here, and they are the two halves of one experiment.

**The system.** `Gtz.Quantitative.DiscriminantSystem` turns rank-three
domination into two scalar polynomial inequalities per triple. That
construction was written for `WeightedDesign m 3` and its scalars
(`heavyExcess`, `atomPairing`) are typed at rank three. This file re-founds
them at EVERY rank (`gapDiagonal`, `gapPairing`, and the principal minors
`gapPairMinor` / `gapTripleMinor` / `gapQuadMinor` of `Gram − I`), checks the
re-founding against the rank-three originals by definitional bridges, and runs
the same chart one rank up:

  `Dominates D {pivot, first, second, third}` is EXACTLY the nonnegativity of
  the SEVEN principal minors of `Gram − I` that CONTAIN the pivot — three of
  degree 2, three of degree 3, one of degree 4 in the ten Gram entries (4, 6, 8
  in the sixteen atom coordinates), at any heavy pivot
  (`dominates_quad_iff_pivotMinorSystem`).

Seven of the other eight principal minors are thereby redundant; the eighth is
the corner itself, which is the HYPOTHESIS rather than a redundancy, and its
strict positivity is genuinely required
(`exists_negative_form_with_pivotMinors_zero`). Whence
`gtzWeightedHeavy_four_iff_pivotMinorCoveringFour` and, with the size-monotone
all-heavy top of `Gtz.Reduction.RankFourWindow`,

  `PivotMinorCoveringFour 11 ↔ GtzWeightedAll 4`,

330 subsets × 7 inequalities at `(11,4)` — the rank-4 analogue of
`discriminantCovering_seven_iff_rank_three`, with no matrices, no test vectors
and no analysis in the statement. The three-leg compression (`quadTraceLeg`,
`quadMinorLeg`, `quadTieLeg` — the elementary symmetric functions of the Schur
block, degrees 2/3/4) is recorded with its exact algebraic relations and its
NECESSITY proved; its sufficiency needs "symmetric `3×3` is PSD iff its three
elementary symmetric functions are nonnegative", which is an eigenvalue fact
the repo's PsdKit deliberately does not carry, so it is not claimed.

**The wall.** The prize this file was aimed at is the induction step
`GtzWeightedAll k → GtzWeighted (M(k+1)) (k+1)`, which would collapse
`gtz_iff_top_of_each_rank` to its first rung. It is NOT here, and the
experiment says why. `exists_all_certificates_but_discriminant` delivers six of
the Lifting Lemma's seven certificates from the rank-`k` hypothesis; the
seventh (`LiftingLemma`, the `∀ testVec` conjunct) is `r rᵀ ⪯ A · (G′ − I)` in
the Loewner order — not a leverage inequality but a demand that the projected
domination have SLACK in the single direction `r`. The rank-`k` hypothesis
supplies only the qualitative `G′ − I ⪰ 0`. The gap is exact, and it kills
the GIVEN `(pivot, subset)` pair outright — not the design, which typically
still has many dominating subsets:

* `crossSum_eq_zero_of_dominates_insert_of_tight` — wherever the projected
  domination is TIGHT, the bordered subset dominates only if the cross vector
  is orthogonal to that direction. No quantity of pivot leverage substitutes.
* `not_dominates_insert_of_tight_direction` — one tight direction with nonzero
  cross component and the lift FAILS outright, at any rank, at any pivot, for
  every design.
* `exists_borderedData_failing_discriminant_at_every_floor` — a SCALAR
  statement: for every floor there are bordered coefficients meeting it with
  the discriminant condition false and the bordered form negative. Read it as
  what it is — the leading coefficient of the bordered quadratic cannot be
  raised to force nonnegativity. The design-level version (data satisfying
  certificates 1–6 with the seventh false at unbounded pivot leverage) is NOT
  proved here; it was verified in exact rationals during audit on an `m = 11`,
  `dim = 4` integer design with `G′ − I` exactly zero, pivot leverages
  `4, 9, 25, …, 10⁶` and bordered forms `−1/4, −1/3, −1/7, …, −4/1000003`,
  and mechanizing that witness is open.

Measured (float sweeps, margins as `σ_min(G_C) − 1` by SVD, negatives
re-verified at 80 digits with exact Cholesky whitening): at rank 4 the forced
form fails on a large and strongly ensemble-dependent fraction of designs
across `m = 8..11` — 12.8%–43.8% on the builder's sample, 3.3%–76.7% on the
auditor's independent integer-coordinate sample — with an `m = 8`
witness where all eight pivots fail, the leverage floor and the projected
domination hold at every one of them, and only the seventh conjunct breaks —
by factors 3.4× to 26058×, tracking `1/lambdaMin(G′ − I)` exactly as the
theorems below predict. The one downstairs rule the hypothesis supplies for
free — take the subset maximising `lambdaMin`, which maximises precisely the
quantity that controls the failure — is itself refuted at 80 digits.

What survives, and is not derived from anything here, is the existential
`HasHeavyPivotInDominator`: some dominating `(k+1)`-subset contains an atom of
leverage at least the rank. Its projected certificate is FREE at every pivot
of every dominating subset, with NO induction hypothesis at all
(`dominates_pushforward_of_dominates_insert`) — which is where the route's
content actually sits, and it is a selection problem, not an estimate.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.Reductions
import Gtz.Reduction.LiftingLemma
import Gtz.Reduction.PrincipalMinorsThree
import Gtz.Reduction.RankFourWindow
import Gtz.Quantitative.DiscriminantSystem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m dim : ℕ}

/-! ### The gap scalars, at every rank

`Gram − I` of a selected family has the atom leverages minus one on its
diagonal and the atom pairings off it. These two scalars generate every
polynomial in this file. -/

/-- The **gap diagonal** `|g_c|² − 1` of an atom, at any rank: the diagonal of
`Gram − I`. `AllHeavy` says exactly that it is strictly positive everywhere. -/
def gapDiagonal (D : WeightedDesign m dim) (atomIndex : Fin m) : ℝ :=
  leverageOf (D.atom atomIndex) - 1

/-- The **gap pairing** `⟨g_c, g_d⟩` of two atoms, at any rank: the
off-diagonal of `Gram − I`. -/
def gapPairing (D : WeightedDesign m dim) (atomFirst atomSecond : Fin m) : ℝ :=
  D.atom atomFirst ⬝ᵥ D.atom atomSecond

theorem gapPairing_comm (D : WeightedDesign m dim) (atomFirst atomSecond : Fin m) :
    gapPairing D atomFirst atomSecond = gapPairing D atomSecond atomFirst :=
  dotProduct_comm _ _

theorem gapPairing_self (D : WeightedDesign m dim) (atomIndex : Fin m) :
    gapPairing D atomIndex atomIndex = leverageOf (D.atom atomIndex) :=
  dotProduct_self_eq_sum_sq (D.atom atomIndex)

/-- All-heaviness is strict positivity of the gap diagonal. -/
theorem gapDiagonal_pos_of_heavy {D : WeightedDesign m dim} (atomIndex : Fin m)
    (hheavy : 1 < leverageOf (D.atom atomIndex)) : 0 < gapDiagonal D atomIndex := by
  rw [gapDiagonal]
  linarith

/-! ### The principal minors of the gap, at every rank -/

/-- The `2×2` principal minor of `Gram − I` on a pair: degree 2 in the Gram
entries, degree 4 in the atom coordinates. -/
def gapPairMinor (D : WeightedDesign m dim) (atomFirst atomSecond : Fin m) : ℝ :=
  gapDiagonal D atomFirst * gapDiagonal D atomSecond
    - gapPairing D atomFirst atomSecond ^ 2

/-- The `3×3` principal minor of `Gram − I` on a triple: degree 3 in the Gram
entries, degree 6 in the atom coordinates. At rank three this IS the repo's
`discriminantTie` (`gapTripleMinor_eq_discriminantTie`). -/
def gapTripleMinor (D : WeightedDesign m dim)
    (atomFirst atomSecond atomThird : Fin m) : ℝ :=
  gapDiagonal D atomFirst
      * (gapDiagonal D atomSecond * gapDiagonal D atomThird
          - gapPairing D atomSecond atomThird ^ 2)
    - (gapDiagonal D atomThird * gapPairing D atomFirst atomSecond ^ 2
        - 2 * gapPairing D atomSecond atomThird
            * gapPairing D atomFirst atomSecond * gapPairing D atomFirst atomThird
        + gapDiagonal D atomSecond * gapPairing D atomFirst atomThird ^ 2)

/-- The `4×4` principal minor of `Gram − I` on a quadruple: degree 4 in the
Gram entries, degree 8 in the atom coordinates, 17 monomials. Written as the
cofactor expansion along the pivot row, so the leading term is the pivot's gap
diagonal times the pivot-free triple minor and the three quadratic corrections
reuse `gapPairMinor` on the pivot-free pairs. -/
def gapQuadMinor (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond atomThird : Fin m) : ℝ :=
  gapDiagonal D pivot * gapTripleMinor D atomFirst atomSecond atomThird
    - gapPairing D pivot atomFirst ^ 2 * gapPairMinor D atomSecond atomThird
    - gapPairing D pivot atomSecond ^ 2 * gapPairMinor D atomFirst atomThird
    - gapPairing D pivot atomThird ^ 2 * gapPairMinor D atomFirst atomSecond
    + 2 * gapPairing D pivot atomFirst * gapPairing D pivot atomSecond
        * (gapDiagonal D atomThird * gapPairing D atomFirst atomSecond
            - gapPairing D atomFirst atomThird * gapPairing D atomSecond atomThird)
    + 2 * gapPairing D pivot atomFirst * gapPairing D pivot atomThird
        * (gapDiagonal D atomSecond * gapPairing D atomFirst atomThird
            - gapPairing D atomFirst atomSecond * gapPairing D atomSecond atomThird)
    + 2 * gapPairing D pivot atomSecond * gapPairing D pivot atomThird
        * (gapDiagonal D atomFirst * gapPairing D atomSecond atomThird
            - gapPairing D atomFirst atomSecond * gapPairing D atomFirst atomThird)

/-- The off-diagonal entry of the division-free Schur complement of `Gram − I`
at the pivot corner: `corner · ⟨g_x, g_y⟩ − ⟨g_p, g_x⟩⟨g_p, g_y⟩`. Its diagonal
counterpart is `gapPairMinor` at the pivot. -/
def schurCross (D : WeightedDesign m dim) (pivot atomFirst atomSecond : Fin m) : ℝ :=
  gapDiagonal D pivot * gapPairing D atomFirst atomSecond
    - gapPairing D pivot atomFirst * gapPairing D pivot atomSecond

/-! ### The bridges to the rank-three system

The re-founding is back-compatible on the nose: at rank three every scalar and
every minor above is DEFINITIONALLY the rank-three original, so the rank-4
system below shares substrate with `Gtz.Quantitative.DiscriminantSystem`
instead of duplicating it. -/

theorem gapDiagonal_eq_heavyExcess (D : WeightedDesign m 3) (atomIndex : Fin m) :
    gapDiagonal D atomIndex = heavyExcess D atomIndex := rfl

theorem gapPairing_eq_atomPairing (D : WeightedDesign m 3)
    (atomFirst atomSecond : Fin m) :
    gapPairing D atomFirst atomSecond = atomPairing D atomFirst atomSecond := rfl

/-- The generic triple minor IS the rank-three tie leg. -/
theorem gapTripleMinor_eq_discriminantTie (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    gapTripleMinor D pivot pairFirst pairSecond
      = discriminantTie D pivot pairFirst pairSecond := rfl

/-- The rank-three trace leg is the sum of the two pair minors through the
pivot — the `legOne` pattern at rank three. -/
theorem gapPairMinor_add_eq_discriminantTrace (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    gapPairMinor D pivot pairFirst + gapPairMinor D pivot pairSecond
      = discriminantTrace D pivot pairFirst pairSecond := rfl

/-! ### The quadruple chart: frame operator, Gram, and the ten scalars -/

/-- The four atoms of an ordered quadruple, as a slot-indexed family. -/
def quadAtom (D : WeightedDesign m 4) (pivot atomFirst atomSecond atomThird : Fin m)
    (slot : Fin 4) : Fin 4 → ℝ :=
  D.atom (![pivot, atomFirst, atomSecond, atomThird] slot)

theorem quadAtom_pivot (D : WeightedDesign m 4)
    (pivot atomFirst atomSecond atomThird : Fin m) :
    quadAtom D pivot atomFirst atomSecond atomThird 0 = D.atom pivot := rfl

theorem quadAtom_first (D : WeightedDesign m 4)
    (pivot atomFirst atomSecond atomThird : Fin m) :
    quadAtom D pivot atomFirst atomSecond atomThird 1 = D.atom atomFirst := rfl

theorem quadAtom_second (D : WeightedDesign m 4)
    (pivot atomFirst atomSecond atomThird : Fin m) :
    quadAtom D pivot atomFirst atomSecond atomThird 2 = D.atom atomSecond := rfl

theorem quadAtom_third (D : WeightedDesign m 4)
    (pivot atomFirst atomSecond atomThird : Fin m) :
    quadAtom D pivot atomFirst atomSecond atomThird 3 = D.atom atomThird := rfl

/-- The `4×4` matrix whose COLUMNS are the four atoms of an ordered quadruple.
Its `M Mᵀ` is the frame operator of the subset and its `Mᵀ M` is the Gram —
the same spectrum, which is what turns domination into a condition on the ten
inner products. -/
def quadMatrix (D : WeightedDesign m 4) (pivot atomFirst atomSecond atomThird : Fin m) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun coordIndex slot =>
    quadAtom D pivot atomFirst atomSecond atomThird slot coordIndex

/-- `M Mᵀ` recovers the frame operator of the quadruple. -/
theorem quadMatrix_mul_transpose (D : WeightedDesign m 4)
    {pivot atomFirst atomSecond atomThird : Fin m}
    (hpivotFirst : pivot ≠ atomFirst) (hpivotSecond : pivot ≠ atomSecond)
    (hpivotThird : pivot ≠ atomThird) (hfirstSecond : atomFirst ≠ atomSecond)
    (hfirstThird : atomFirst ≠ atomThird) (hsecondThird : atomSecond ≠ atomThird) :
    quadMatrix D pivot atomFirst atomSecond atomThird
        * (quadMatrix D pivot atomFirst atomSecond atomThird)ᵀ
      = subsetSum D {pivot, atomFirst, atomSecond, atomThird} := by
  rw [subsetSum,
    show ({pivot, atomFirst, atomSecond, atomThird} : Finset (Fin m))
      = insert pivot (insert atomFirst (insert atomSecond {atomThird})) from rfl,
    Finset.sum_insert (by simp [hpivotFirst, hpivotSecond, hpivotThird]),
    Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton]
  ext rowIdx colIdx
  simp only [Matrix.mul_apply, Matrix.transpose_apply, quadMatrix, Matrix.of_apply,
    Fin.sum_univ_four, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    quadAtom_pivot, quadAtom_first, quadAtom_second, quadAtom_third]
  ring

/-- `Mᵀ M` is the Gram matrix of the quadruple. -/
theorem quadMatrix_transpose_mul_apply (D : WeightedDesign m 4)
    (pivot atomFirst atomSecond atomThird : Fin m) (slotRow slotCol : Fin 4) :
    ((quadMatrix D pivot atomFirst atomSecond atomThird)ᵀ
        * quadMatrix D pivot atomFirst atomSecond atomThird) slotRow slotCol
      = quadAtom D pivot atomFirst atomSecond atomThird slotRow
          ⬝ᵥ quadAtom D pivot atomFirst atomSecond atomThird slotCol := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, quadMatrix, Matrix.of_apply,
    dotProduct]

/-- The Gram gap of a square column matrix is symmetric, at every size. -/
theorem gramGap_transpose {size : ℕ} (columns : Matrix (Fin size) (Fin size) ℝ) :
    (columnsᵀ * columns - 1)ᵀ = columnsᵀ * columns - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- The quadratic form of a symmetric `4×4` matrix, in its ten independent
entries. -/
theorem quadForm_four_eq {form : Matrix (Fin 4) (Fin 4) ℝ} (hsymm : formᵀ = form)
    (testVec : Fin 4 → ℝ) :
    testVec ⬝ᵥ (form *ᵥ testVec)
      = form 0 0 * testVec 0 ^ 2 + form 1 1 * testVec 1 ^ 2
        + form 2 2 * testVec 2 ^ 2 + form 3 3 * testVec 3 ^ 2
        + 2 * form 0 1 * testVec 0 * testVec 1
        + 2 * form 0 2 * testVec 0 * testVec 2
        + 2 * form 0 3 * testVec 0 * testVec 3
        + 2 * form 1 2 * testVec 1 * testVec 2
        + 2 * form 1 3 * testVec 1 * testVec 3
        + 2 * form 2 3 * testVec 2 * testVec 3 := by
  have hentry : ∀ rowIdx colIdx : Fin 4, form colIdx rowIdx = form rowIdx colIdx :=
    fun rowIdx colIdx => by
      have hcongr := congrFun (congrFun hsymm rowIdx) colIdx
      simpa using hcongr
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  rw [hentry 0 1, hentry 0 2, hentry 0 3, hentry 1 2, hentry 1 3, hentry 2 3]
  ring

private theorem quadGap_diag (D : WeightedDesign m 4)
    (pivot atomFirst atomSecond atomThird : Fin m) (slot : Fin 4) :
    ((quadMatrix D pivot atomFirst atomSecond atomThird)ᵀ
        * quadMatrix D pivot atomFirst atomSecond atomThird - 1) slot slot
      = leverageOf (quadAtom D pivot atomFirst atomSecond atomThird slot) - 1 := by
  rw [Matrix.sub_apply, quadMatrix_transpose_mul_apply, Matrix.one_apply_eq,
    dotProduct_self_eq_sum_sq]
  rfl

private theorem quadGap_offDiag (D : WeightedDesign m 4)
    (pivot atomFirst atomSecond atomThird : Fin m) {slotRow slotCol : Fin 4}
    (hne : slotRow ≠ slotCol) :
    ((quadMatrix D pivot atomFirst atomSecond atomThird)ᵀ
        * quadMatrix D pivot atomFirst atomSecond atomThird - 1) slotRow slotCol
      = quadAtom D pivot atomFirst atomSecond atomThird slotRow
          ⬝ᵥ quadAtom D pivot atomFirst atomSecond atomThird slotCol := by
  rw [Matrix.sub_apply, quadMatrix_transpose_mul_apply, Matrix.one_apply_ne hne,
    sub_zero]

/-- The quadratic form of the Gram gap of a quadruple, in the ten scalars. -/
private theorem quadGapForm_eq (D : WeightedDesign m 4)
    (pivot atomFirst atomSecond atomThird : Fin m) (testVec : Fin 4 → ℝ) :
    testVec ⬝ᵥ (((quadMatrix D pivot atomFirst atomSecond atomThird)ᵀ
        * quadMatrix D pivot atomFirst atomSecond atomThird - 1) *ᵥ testVec)
      = gapDiagonal D pivot * testVec 0 ^ 2
        + gapDiagonal D atomFirst * testVec 1 ^ 2
        + gapDiagonal D atomSecond * testVec 2 ^ 2
        + gapDiagonal D atomThird * testVec 3 ^ 2
        + 2 * gapPairing D pivot atomFirst * testVec 0 * testVec 1
        + 2 * gapPairing D pivot atomSecond * testVec 0 * testVec 2
        + 2 * gapPairing D pivot atomThird * testVec 0 * testVec 3
        + 2 * gapPairing D atomFirst atomSecond * testVec 1 * testVec 2
        + 2 * gapPairing D atomFirst atomThird * testVec 1 * testVec 3
        + 2 * gapPairing D atomSecond atomThird * testVec 2 * testVec 3 := by
  rw [quadForm_four_eq (gramGap_transpose _), quadGap_diag, quadGap_diag,
    quadGap_diag, quadGap_diag,
    quadGap_offDiag D pivot atomFirst atomSecond atomThird (by decide : (0 : Fin 4) ≠ 1),
    quadGap_offDiag D pivot atomFirst atomSecond atomThird (by decide : (0 : Fin 4) ≠ 2),
    quadGap_offDiag D pivot atomFirst atomSecond atomThird (by decide : (0 : Fin 4) ≠ 3),
    quadGap_offDiag D pivot atomFirst atomSecond atomThird (by decide : (1 : Fin 4) ≠ 2),
    quadGap_offDiag D pivot atomFirst atomSecond atomThird (by decide : (1 : Fin 4) ≠ 3),
    quadGap_offDiag D pivot atomFirst atomSecond atomThird (by decide : (2 : Fin 4) ≠ 3)]
  simp only [quadAtom_pivot, quadAtom_first, quadAtom_second, quadAtom_third,
    gapDiagonal, gapPairing]

/-! ### The division-free Schur complement at a positive corner, `4×4` -/

/-- **Completing the square at the corner**, `4×4`, pure `ring`: multiplying a
symmetric quaternary quadratic form by its corner entry splits it into one
exact square plus the Schur form in the remaining three variables. The
identity that makes the rank-4 corner reduction division-free — the direct
analogue of `cornerCompleteSquare`. -/
theorem cornerCompleteSquareFour (corner crossFirst crossSecond crossThird
    diagFirst diagSecond diagThird pairingFirstSecond pairingFirstThird
    pairingSecondThird firstCoord secondCoord thirdCoord fourthCoord : ℝ) :
    corner * (corner * firstCoord ^ 2 + diagFirst * secondCoord ^ 2
        + diagSecond * thirdCoord ^ 2 + diagThird * fourthCoord ^ 2
        + 2 * crossFirst * firstCoord * secondCoord
        + 2 * crossSecond * firstCoord * thirdCoord
        + 2 * crossThird * firstCoord * fourthCoord
        + 2 * pairingFirstSecond * secondCoord * thirdCoord
        + 2 * pairingFirstThird * secondCoord * fourthCoord
        + 2 * pairingSecondThird * thirdCoord * fourthCoord)
      = (corner * firstCoord + crossFirst * secondCoord + crossSecond * thirdCoord
            + crossThird * fourthCoord) ^ 2
        + ((corner * diagFirst - crossFirst ^ 2) * secondCoord ^ 2
            + (corner * diagSecond - crossSecond ^ 2) * thirdCoord ^ 2
            + (corner * diagThird - crossThird ^ 2) * fourthCoord ^ 2
            + 2 * (corner * pairingFirstSecond - crossFirst * crossSecond)
                * secondCoord * thirdCoord
            + 2 * (corner * pairingFirstThird - crossFirst * crossThird)
                * secondCoord * fourthCoord
            + 2 * (corner * pairingSecondThird - crossSecond * crossThird)
                * thirdCoord * fourthCoord) := by
  ring

/-- **The Schur complement at a positive corner**, `4×4`, division-free: a
symmetric quaternary quadratic form with strictly positive corner entry is
globally nonnegative iff its `3×3` Schur form is. Forward by evaluating at the
square-killing first coordinate, backward by `cornerCompleteSquareFour` and
dividing by the positive corner. -/
theorem quadFour_nonneg_iff_schur_nonneg (corner crossFirst crossSecond crossThird
    diagFirst diagSecond diagThird pairingFirstSecond pairingFirstThird
    pairingSecondThird : ℝ) (hcorner : 0 < corner) :
    (∀ firstCoord secondCoord thirdCoord fourthCoord : ℝ,
        0 ≤ corner * firstCoord ^ 2 + diagFirst * secondCoord ^ 2
          + diagSecond * thirdCoord ^ 2 + diagThird * fourthCoord ^ 2
          + 2 * crossFirst * firstCoord * secondCoord
          + 2 * crossSecond * firstCoord * thirdCoord
          + 2 * crossThird * firstCoord * fourthCoord
          + 2 * pairingFirstSecond * secondCoord * thirdCoord
          + 2 * pairingFirstThird * secondCoord * fourthCoord
          + 2 * pairingSecondThird * thirdCoord * fourthCoord)
      ↔ (∀ testFirst testSecond testThird : ℝ,
        0 ≤ (corner * diagFirst - crossFirst ^ 2) * testFirst ^ 2
          + (corner * diagSecond - crossSecond ^ 2) * testSecond ^ 2
          + (corner * diagThird - crossThird ^ 2) * testThird ^ 2
          + 2 * (corner * pairingFirstSecond - crossFirst * crossSecond)
              * testFirst * testSecond
          + 2 * (corner * pairingFirstThird - crossFirst * crossThird)
              * testFirst * testThird
          + 2 * (corner * pairingSecondThird - crossSecond * crossThird)
              * testSecond * testThird) := by
  constructor
  · intro hform testFirst testSecond testThird
    have hkey := hform
      (-(crossFirst * testFirst + crossSecond * testSecond
          + crossThird * testThird) / corner) testFirst testSecond testThird
    have hidentity := cornerCompleteSquareFour corner crossFirst crossSecond
      crossThird diagFirst diagSecond diagThird pairingFirstSecond
      pairingFirstThird pairingSecondThird
      (-(crossFirst * testFirst + crossSecond * testSecond
          + crossThird * testThird) / corner) testFirst testSecond testThird
    have hsquareZero : corner
        * (-(crossFirst * testFirst + crossSecond * testSecond
            + crossThird * testThird) / corner)
        + crossFirst * testFirst + crossSecond * testSecond
        + crossThird * testThird = 0 := by
      have hne : corner ≠ 0 := ne_of_gt hcorner
      field_simp
      ring
    rw [hsquareZero] at hidentity
    have hprod := mul_nonneg hcorner.le hkey
    rw [hidentity] at hprod
    linarith [hprod]
  · intro hschur firstCoord secondCoord thirdCoord fourthCoord
    have hidentity := cornerCompleteSquareFour corner crossFirst crossSecond
      crossThird diagFirst diagSecond diagThird pairingFirstSecond
      pairingFirstThird pairingSecondThird firstCoord secondCoord thirdCoord
      fourthCoord
    have hschurHere := hschur secondCoord thirdCoord fourthCoord
    have hsq := sq_nonneg (corner * firstCoord + crossFirst * secondCoord
      + crossSecond * thirdCoord + crossThird * fourthCoord)
    have hcornerMul : 0 ≤ corner * (corner * firstCoord ^ 2
        + diagFirst * secondCoord ^ 2 + diagSecond * thirdCoord ^ 2
        + diagThird * fourthCoord ^ 2
        + 2 * crossFirst * firstCoord * secondCoord
        + 2 * crossSecond * firstCoord * thirdCoord
        + 2 * crossThird * firstCoord * fourthCoord
        + 2 * pairingFirstSecond * secondCoord * thirdCoord
        + 2 * pairingFirstThird * secondCoord * fourthCoord
        + 2 * pairingSecondThird * thirdCoord * fourthCoord) := by
      rw [hidentity]; linarith [hsq, hschurHere]
    exact (mul_nonneg_iff_of_pos_left hcorner).mp hcornerMul

/-! ### The Schur block as a matrix, and its seven minors -/

/-- The division-free Schur complement of `Gram − I` at the pivot corner, as a
symmetric `3×3` matrix over the pivot-free slots. Its diagonal is
`gapPairMinor` at the pivot and its off-diagonal is `schurCross`. -/
def schurBlockFour (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond atomThird : Fin m) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![gapPairMinor D pivot atomFirst, schurCross D pivot atomFirst atomSecond,
        schurCross D pivot atomFirst atomThird;
     schurCross D pivot atomFirst atomSecond, gapPairMinor D pivot atomSecond,
        schurCross D pivot atomSecond atomThird;
     schurCross D pivot atomFirst atomThird, schurCross D pivot atomSecond atomThird,
        gapPairMinor D pivot atomThird]

theorem schurBlockFour_transpose (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond atomThird : Fin m) :
    (schurBlockFour D pivot atomFirst atomSecond atomThird)ᵀ
      = schurBlockFour D pivot atomFirst atomSecond atomThird := by
  ext rowIdx colIdx
  fin_cases rowIdx <;> fin_cases colIdx <;> rfl

/-- The quadratic form of the Schur block, in the six scalars of the
pivot-free slots. -/
private theorem schurBlockFour_form_eq (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond atomThird : Fin m) (testVec : Fin 3 → ℝ) :
    testVec ⬝ᵥ (schurBlockFour D pivot atomFirst atomSecond atomThird *ᵥ testVec)
      = gapPairMinor D pivot atomFirst * testVec 0 ^ 2
        + gapPairMinor D pivot atomSecond * testVec 1 ^ 2
        + gapPairMinor D pivot atomThird * testVec 2 ^ 2
        + 2 * schurCross D pivot atomFirst atomSecond * testVec 0 * testVec 1
        + 2 * schurCross D pivot atomFirst atomThird * testVec 0 * testVec 2
        + 2 * schurCross D pivot atomSecond atomThird * testVec 1 * testVec 2 := by
  rw [quadForm_three_eq (schurBlockFour_transpose D pivot atomFirst atomSecond atomThird)]
  rfl

/-- **The pair minors of the Schur block are the triple minors of the gap**,
scaled by the corner: a pure `ring` identity, the rank-4 generalisation of
`schurDet_eq_excess_mul_tie`. -/
theorem schurBlockFour_pairMinor_eq (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond : Fin m) :
    gapPairMinor D pivot atomFirst * gapPairMinor D pivot atomSecond
        - schurCross D pivot atomFirst atomSecond ^ 2
      = gapDiagonal D pivot * gapTripleMinor D pivot atomFirst atomSecond := by
  simp only [gapPairMinor, gapTripleMinor, schurCross]
  ring

/-- **The determinant of the Schur block is the quadruple minor of the gap**,
scaled by the SQUARE of the corner: a pure `ring` identity. -/
theorem schurBlockFour_det (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond atomThird : Fin m) :
    (schurBlockFour D pivot atomFirst atomSecond atomThird).det
      = gapDiagonal D pivot ^ 2
        * gapQuadMinor D pivot atomFirst atomSecond atomThird := by
  rw [Matrix.det_fin_three]
  simp only [schurBlockFour, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    gapPairMinor, gapTripleMinor, gapQuadMinor, schurCross]
  ring

/-! ### The narrowing at rank four -/

/-- The Gram-gap form of a quadruple, reduced to the Schur form at a strictly
positive corner. -/
private theorem quadGap_form_iff_schurForm (D : WeightedDesign m 4)
    (pivot atomFirst atomSecond atomThird : Fin m)
    (hcornerPos : 0 < gapDiagonal D pivot) :
    (∀ testVec : Fin 4 → ℝ, 0 ≤ testVec
        ⬝ᵥ (((quadMatrix D pivot atomFirst atomSecond atomThird)ᵀ
            * quadMatrix D pivot atomFirst atomSecond atomThird - 1) *ᵥ testVec))
      ↔ (∀ testFirst testSecond testThird : ℝ,
        0 ≤ gapPairMinor D pivot atomFirst * testFirst ^ 2
          + gapPairMinor D pivot atomSecond * testSecond ^ 2
          + gapPairMinor D pivot atomThird * testThird ^ 2
          + 2 * schurCross D pivot atomFirst atomSecond * testFirst * testSecond
          + 2 * schurCross D pivot atomFirst atomThird * testFirst * testThird
          + 2 * schurCross D pivot atomSecond atomThird * testSecond * testThird) := by
  have hscalar : (∀ testVec : Fin 4 → ℝ, 0 ≤ testVec
        ⬝ᵥ (((quadMatrix D pivot atomFirst atomSecond atomThird)ᵀ
            * quadMatrix D pivot atomFirst atomSecond atomThird - 1) *ᵥ testVec))
      ↔ ∀ firstCoord secondCoord thirdCoord fourthCoord : ℝ,
        0 ≤ gapDiagonal D pivot * firstCoord ^ 2
          + gapDiagonal D atomFirst * secondCoord ^ 2
          + gapDiagonal D atomSecond * thirdCoord ^ 2
          + gapDiagonal D atomThird * fourthCoord ^ 2
          + 2 * gapPairing D pivot atomFirst * firstCoord * secondCoord
          + 2 * gapPairing D pivot atomSecond * firstCoord * thirdCoord
          + 2 * gapPairing D pivot atomThird * firstCoord * fourthCoord
          + 2 * gapPairing D atomFirst atomSecond * secondCoord * thirdCoord
          + 2 * gapPairing D atomFirst atomThird * secondCoord * fourthCoord
          + 2 * gapPairing D atomSecond atomThird * thirdCoord * fourthCoord := by
    constructor
    · intro hquad firstCoord secondCoord thirdCoord fourthCoord
      have hhere := hquad ![firstCoord, secondCoord, thirdCoord, fourthCoord]
      rw [quadGapForm_eq] at hhere
      simpa using hhere
    · intro hform testVec
      rw [quadGapForm_eq]
      exact hform (testVec 0) (testVec 1) (testVec 2) (testVec 3)
  rw [hscalar, quadFour_nonneg_iff_schur_nonneg _ _ _ _ _ _ _ _ _ _ hcornerPos]
  simp only [gapPairMinor, schurCross]

/-- **THE RANK-FOUR NARROWING**: for an ordered quadruple whose PIVOT is heavy,
domination of the quadruple is EXACTLY the nonnegativity of the SEVEN principal
minors of `Gram − I` that contain the pivot — the three pair minors, the three
triple minors, and the quadruple minor. No matrices, no test vectors, no
deflation coisometry: the conclusion mentions only the ten inner products of
the quadruple, in degrees `2, 2, 2, 3, 3, 3, 4`. An equivalence in both
directions, with NO strictness anywhere except the pivot's heaviness (which
`exists_leverage_ge_rank` supplies at the max-leverage atom of any design and
`AllHeavy` supplies at every atom).

Seven of the remaining eight principal minors of `Gram − I` are therefore
redundant — a sharpening of the classical all-principal-minors criterion that
the corner positivity buys. The eighth is the corner, which is the hypothesis. Strictness of
the corner is indispensable: see `exists_negative_form_with_pivotMinors_zero`.
-/
theorem dominates_quad_iff_pivotMinorSystem (D : WeightedDesign m 4)
    {pivot atomFirst atomSecond atomThird : Fin m}
    (hpivotFirst : pivot ≠ atomFirst) (hpivotSecond : pivot ≠ atomSecond)
    (hpivotThird : pivot ≠ atomThird) (hfirstSecond : atomFirst ≠ atomSecond)
    (hfirstThird : atomFirst ≠ atomThird) (hsecondThird : atomSecond ≠ atomThird)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot)) :
    Dominates D {pivot, atomFirst, atomSecond, atomThird}
      ↔ (0 ≤ gapPairMinor D pivot atomFirst
          ∧ 0 ≤ gapPairMinor D pivot atomSecond
          ∧ 0 ≤ gapPairMinor D pivot atomThird
          ∧ 0 ≤ gapTripleMinor D pivot atomFirst atomSecond
          ∧ 0 ≤ gapTripleMinor D pivot atomFirst atomThird
          ∧ 0 ≤ gapTripleMinor D pivot atomSecond atomThird
          ∧ 0 ≤ gapQuadMinor D pivot atomFirst atomSecond atomThird) := by
  have hcornerPos : 0 < gapDiagonal D pivot :=
    gapDiagonal_pos_of_heavy pivot hpivotHeavy
  have hframe := quadMatrix_mul_transpose D hpivotFirst hpivotSecond hpivotThird
    hfirstSecond hfirstThird hsecondThird
  have hgram : Dominates D {pivot, atomFirst, atomSecond, atomThird}
      ↔ ((quadMatrix D pivot atomFirst atomSecond atomThird)ᵀ
          * quadMatrix D pivot atomFirst atomSecond atomThird - 1).PosSemidef := by
    rw [Dominates, ← hframe]
    exact (posSemidef_transpose_mul_sub_one_comm
      (quadMatrix D pivot atomFirst atomSecond atomThird)).symm
  rw [hgram, posSemidef_iff_quadForm_nonneg _ (gramGap_transpose _),
    quadGap_form_iff_schurForm D pivot atomFirst atomSecond atomThird hcornerPos]
  constructor
  · intro hschur
    have hpairFirst : 0 ≤ gapPairMinor D pivot atomFirst := by
      have hhere := hschur 1 0 0
      nlinarith [hhere]
    have hpairSecond : 0 ≤ gapPairMinor D pivot atomSecond := by
      have hhere := hschur 0 1 0
      nlinarith [hhere]
    have hpairThird : 0 ≤ gapPairMinor D pivot atomThird := by
      have hhere := hschur 0 0 1
      nlinarith [hhere]
    have htripleFirstSecond : 0 ≤ gapTripleMinor D pivot atomFirst atomSecond := by
      have hplane : ∀ leftCoord rightCoord : ℝ,
          0 ≤ gapPairMinor D pivot atomFirst * leftCoord ^ 2
            + 2 * schurCross D pivot atomFirst atomSecond * leftCoord * rightCoord
            + gapPairMinor D pivot atomSecond * rightCoord ^ 2 := by
        intro leftCoord rightCoord
        have hhere := hschur leftCoord rightCoord 0
        nlinarith [hhere]
      have hdet := ((twoByTwoForm_nonneg_iff_trace_det_nonneg _ _ _).mp hplane).2
      rw [schurBlockFour_pairMinor_eq D pivot atomFirst atomSecond] at hdet
      exact (mul_nonneg_iff_of_pos_left hcornerPos).mp hdet
    have htripleFirstThird : 0 ≤ gapTripleMinor D pivot atomFirst atomThird := by
      have hplane : ∀ leftCoord rightCoord : ℝ,
          0 ≤ gapPairMinor D pivot atomFirst * leftCoord ^ 2
            + 2 * schurCross D pivot atomFirst atomThird * leftCoord * rightCoord
            + gapPairMinor D pivot atomThird * rightCoord ^ 2 := by
        intro leftCoord rightCoord
        have hhere := hschur leftCoord 0 rightCoord
        nlinarith [hhere]
      have hdet := ((twoByTwoForm_nonneg_iff_trace_det_nonneg _ _ _).mp hplane).2
      rw [schurBlockFour_pairMinor_eq D pivot atomFirst atomThird] at hdet
      exact (mul_nonneg_iff_of_pos_left hcornerPos).mp hdet
    have htripleSecondThird : 0 ≤ gapTripleMinor D pivot atomSecond atomThird := by
      have hplane : ∀ leftCoord rightCoord : ℝ,
          0 ≤ gapPairMinor D pivot atomSecond * leftCoord ^ 2
            + 2 * schurCross D pivot atomSecond atomThird * leftCoord * rightCoord
            + gapPairMinor D pivot atomThird * rightCoord ^ 2 := by
        intro leftCoord rightCoord
        have hhere := hschur 0 leftCoord rightCoord
        nlinarith [hhere]
      have hdet := ((twoByTwoForm_nonneg_iff_trace_det_nonneg _ _ _).mp hplane).2
      rw [schurBlockFour_pairMinor_eq D pivot atomSecond atomThird] at hdet
      exact (mul_nonneg_iff_of_pos_left hcornerPos).mp hdet
    have hblockPsd : (schurBlockFour D pivot atomFirst atomSecond atomThird).PosSemidef := by
      refine (posSemidef_iff_quadForm_nonneg _
        (schurBlockFour_transpose D pivot atomFirst atomSecond atomThird)).mpr
        (fun testVec => ?_)
      rw [schurBlockFour_form_eq]
      exact hschur (testVec 0) (testVec 1) (testVec 2)
    have hquad : 0 ≤ gapQuadMinor D pivot atomFirst atomSecond atomThird := by
      have hdet := hblockPsd.det_nonneg
      rw [schurBlockFour_det] at hdet
      exact (mul_nonneg_iff_of_pos_left (pow_pos hcornerPos 2)).mp hdet
    exact ⟨hpairFirst, hpairSecond, hpairThird, htripleFirstSecond,
      htripleFirstThird, htripleSecondThird, hquad⟩
  · rintro ⟨hpairFirst, hpairSecond, hpairThird, htripleFirstSecond,
      htripleFirstThird, htripleSecondThird, hquad⟩
    have hblockPsd : (schurBlockFour D pivot atomFirst atomSecond atomThird).PosSemidef := by
      refine posSemidef_three_of_principalMinors
        (schurBlockFour_transpose D pivot atomFirst atomSecond atomThird)
        hpairFirst hpairSecond hpairThird ?_ ?_ ?_ ?_
      · show 0 ≤ gapPairMinor D pivot atomFirst * gapPairMinor D pivot atomSecond
          - schurCross D pivot atomFirst atomSecond ^ 2
        rw [schurBlockFour_pairMinor_eq D pivot atomFirst atomSecond]
        exact mul_nonneg hcornerPos.le htripleFirstSecond
      · show 0 ≤ gapPairMinor D pivot atomFirst * gapPairMinor D pivot atomThird
          - schurCross D pivot atomFirst atomThird ^ 2
        rw [schurBlockFour_pairMinor_eq D pivot atomFirst atomThird]
        exact mul_nonneg hcornerPos.le htripleFirstThird
      · show 0 ≤ gapPairMinor D pivot atomSecond * gapPairMinor D pivot atomThird
          - schurCross D pivot atomSecond atomThird ^ 2
        rw [schurBlockFour_pairMinor_eq D pivot atomSecond atomThird]
        exact mul_nonneg hcornerPos.le htripleSecondThird
      · rw [schurBlockFour_det]
        exact mul_nonneg (pow_two_nonneg _) hquad
    intro testFirst testSecond testThird
    have hform := (posSemidef_iff_quadForm_nonneg _
      (schurBlockFour_transpose D pivot atomFirst atomSecond atomThird)).mp hblockPsd
      ![testFirst, testSecond, testThird]
    rw [schurBlockFour_form_eq] at hform
    simpa using hform

/-! ### The rank-four covering statement -/

/-- **The rank-four covering system** at size `m`: every all-heavy weighted
`(m,4)` design has an ordered quadruple at which the seven pivot-containing
principal minors of `Gram − I` are all nonnegative. A purely real-algebraic
sentence: at `m = 11` it is 55 real variables (44 coordinates and 11 weights),
11 polynomial equations (10 Parseval and the weight sum), 22 strict
inequalities (positivity and all-heaviness), and a disjunction over the 330
quadruples of seven polynomial inequalities of degrees 4, 6 and 8 in the atom
coordinates. Read over quadruples, never over (pivot, triple) combinations:
the four readings of a quadruple are equivalent (they are all equivalent to
domination of the same subset). -/
def PivotMinorCoveringFour (m : ℕ) : Prop :=
  ∀ D : WeightedDesign m 4, AllHeavy D →
    ∃ pivot atomFirst atomSecond atomThird : Fin m,
      pivot ≠ atomFirst ∧ pivot ≠ atomSecond ∧ pivot ≠ atomThird
        ∧ atomFirst ≠ atomSecond ∧ atomFirst ≠ atomThird
        ∧ atomSecond ≠ atomThird
        ∧ 0 ≤ gapPairMinor D pivot atomFirst
        ∧ 0 ≤ gapPairMinor D pivot atomSecond
        ∧ 0 ≤ gapPairMinor D pivot atomThird
        ∧ 0 ≤ gapTripleMinor D pivot atomFirst atomSecond
        ∧ 0 ≤ gapTripleMinor D pivot atomFirst atomThird
        ∧ 0 ≤ gapTripleMinor D pivot atomSecond atomThird
        ∧ 0 ≤ gapQuadMinor D pivot atomFirst atomSecond atomThird

/-- **The narrowing, at the level of the statement**: all-heavy weighted GTZ at
rank four IS the rank-four minor covering — an equivalence, not a sufficiency,
exactly as `gtzWeightedHeavy_three_iff_discriminantCovering` at rank three. -/
theorem gtzWeightedHeavy_four_iff_pivotMinorCoveringFour (m : ℕ) :
    GtzWeightedHeavy m 4 ↔ PivotMinorCoveringFour m := by
  classical
  constructor
  · intro hgtz D hheavy
    obtain ⟨C, hcard, hdominates⟩ := hgtz D hheavy
    obtain ⟨pivot, atomFirst, atomSecond, atomThird, hpivotFirst, hpivotSecond,
      hpivotThird, hfirstSecond, hfirstThird, hsecondThird, hCeq⟩ :=
      Finset.card_eq_four.mp hcard
    subst hCeq
    refine ⟨pivot, atomFirst, atomSecond, atomThird, hpivotFirst, hpivotSecond,
      hpivotThird, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
    exact (dominates_quad_iff_pivotMinorSystem D hpivotFirst hpivotSecond
      hpivotThird hfirstSecond hfirstThird hsecondThird (hheavy pivot)).mp hdominates
  · intro hcover D hheavy
    obtain ⟨pivot, atomFirst, atomSecond, atomThird, hpivotFirst, hpivotSecond,
      hpivotThird, hfirstSecond, hfirstThird, hsecondThird, hminors⟩ :=
      hcover D hheavy
    refine ⟨{pivot, atomFirst, atomSecond, atomThird}, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem
          (by simp [hpivotFirst, hpivotSecond, hpivotThird]),
        Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
        Finset.card_insert_of_notMem (by simp [hsecondThird]),
        Finset.card_singleton]
    · exact (dominates_quad_iff_pivotMinorSystem D hpivotFirst hpivotSecond
        hpivotThird hfirstSecond hfirstThird hsecondThird (hheavy pivot)).mpr hminors

/-- **The four readings of a quadruple agree** at an all-heavy design: which
atom plays the pivot does not change the verdict, because both readings are
equivalent to domination of the same subset. So a case analysis is organised
over quadruples, never over (pivot, triple) pairs — the rank-4 analogue of
`discriminantSystem_pivot_independent`. -/
theorem pivotMinorSystem_pivot_independent (D : WeightedDesign m 4)
    {pivot atomFirst atomSecond atomThird : Fin m}
    (hpivotFirst : pivot ≠ atomFirst) (hpivotSecond : pivot ≠ atomSecond)
    (hpivotThird : pivot ≠ atomThird) (hfirstSecond : atomFirst ≠ atomSecond)
    (hfirstThird : atomFirst ≠ atomThird) (hsecondThird : atomSecond ≠ atomThird)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hfirstHeavy : 1 < leverageOf (D.atom atomFirst)) :
    (0 ≤ gapPairMinor D pivot atomFirst
        ∧ 0 ≤ gapPairMinor D pivot atomSecond
        ∧ 0 ≤ gapPairMinor D pivot atomThird
        ∧ 0 ≤ gapTripleMinor D pivot atomFirst atomSecond
        ∧ 0 ≤ gapTripleMinor D pivot atomFirst atomThird
        ∧ 0 ≤ gapTripleMinor D pivot atomSecond atomThird
        ∧ 0 ≤ gapQuadMinor D pivot atomFirst atomSecond atomThird)
      ↔ (0 ≤ gapPairMinor D atomFirst pivot
          ∧ 0 ≤ gapPairMinor D atomFirst atomSecond
          ∧ 0 ≤ gapPairMinor D atomFirst atomThird
          ∧ 0 ≤ gapTripleMinor D atomFirst pivot atomSecond
          ∧ 0 ≤ gapTripleMinor D atomFirst pivot atomThird
          ∧ 0 ≤ gapTripleMinor D atomFirst atomSecond atomThird
          ∧ 0 ≤ gapQuadMinor D atomFirst pivot atomSecond atomThird) := by
  rw [← dominates_quad_iff_pivotMinorSystem D hpivotFirst hpivotSecond hpivotThird
      hfirstSecond hfirstThird hsecondThird hpivotHeavy,
    ← dominates_quad_iff_pivotMinorSystem D hpivotFirst.symm hfirstSecond
      hfirstThird hpivotSecond hpivotThird hsecondThird hfirstHeavy,
    Finset.insert_comm]

/-! ### The all-heavy top object carries its rank, at every rank

`gtzWeightedAll_of_heavy_bounded` caps the sizes that must be checked at
`M(k) = k(k+1)/2 + 1` and `gtzWeightedHeavy_of_le` supplies every smaller size
from the cap. Both are rank-generic, so the collapse of a rank to ONE all-heavy
object is generic too — `rank_three_of_heavy_top` was a special case that did
not need its two hypotheses. -/

/-- **One all-heavy object per rank.** -/
theorem gtzWeightedAll_of_heavyTop (rank : ℕ) (hrank : 1 ≤ rank)
    (htop : GtzWeightedHeavy (rank * (rank + 1) / 2 + 1) rank) : GtzWeightedAll rank :=
  gtzWeightedAll_of_heavy_bounded hrank
    fun _ hsize => gtzWeightedHeavy_of_le hsize htop

/-- **Rank four from the all-heavy top object `(11,4)` alone.** -/
theorem rank_four_of_heavy_top (heavyTop : GtzWeightedHeavy 11 4) : GtzWeightedAll 4 :=
  gtzWeightedAll_of_heavyTop 4 (by norm_num) (by norm_num; exact heavyTop)

/-- **Rank five from the all-heavy top object `(16,5)` alone** — the same
one-liner one rank up, `M(5) = 16`. -/
theorem rank_five_of_heavy_top (heavyTop : GtzWeightedHeavy 16 5) : GtzWeightedAll 5 :=
  gtzWeightedAll_of_heavyTop 5 (by norm_num) (by norm_num; exact heavyTop)

/-- Rank-four coverings are monotone in the number of atoms, through the
all-heavy statement they are equivalent to. -/
theorem pivotMinorCoveringFour_of_le {size larger : ℕ} (hle : size ≤ larger)
    (hcover : PivotMinorCoveringFour larger) : PivotMinorCoveringFour size :=
  (gtzWeightedHeavy_four_iff_pivotMinorCoveringFour size).mp
    (gtzWeightedHeavy_of_le hle
      ((gtzWeightedHeavy_four_iff_pivotMinorCoveringFour larger).mpr hcover))

/-- **The polynomial frontier of rank four, as a single equivalence.** GTZ at
rank four for every `n` IS the one covering sentence at `(11,4)`: every
all-heavy weighted `(11,4)` design has one of its 330 quadruples at which the
seven pivot-containing principal minors of `Gram − I` are all nonnegative.
Seven polynomial inequalities of degrees 2, 3 and 4 in the ten Gram entries of
a quadruple, quantified over a real semialgebraic parameter space, with no
matrices, no test vectors and no analysis anywhere in the statement. -/
theorem pivotMinorCoveringFour_eleven_iff_rank_four :
    PivotMinorCoveringFour 11 ↔ GtzWeightedAll 4 := by
  constructor
  · intro hcover
    exact rank_four_of_heavy_top
      ((gtzWeightedHeavy_four_iff_pivotMinorCoveringFour 11).mpr hcover)
  · intro hrank
    exact (gtzWeightedHeavy_four_iff_pivotMinorCoveringFour 11).mp
      (fun D _ => hrank 11 D)

/-- **The 1997 statement at rank four from the single covering sentence.** -/
theorem gtz_original_rank_four_of_pivotMinorCoveringFour
    (hcover : PivotMinorCoveringFour 11) : ∀ n, 0 < n → GtzOriginal n 4 :=
  original_of_weighted 4 (pivotMinorCoveringFour_eleven_iff_rank_four.mp hcover)

/-! ### The three-leg compression

The seven minors group into the three elementary symmetric functions of the
Schur block, of degrees 2, 3 and 4 in the Gram entries — the direct
generalisation of the rank-three pair `(discriminantTrace, discriminantTie)`,
whose legs are exactly `quadTraceLeg` and `quadMinorLeg` one rank down. All
three relations below are pure `ring` identities.

NECESSITY is proved (`quadLegs_nonneg_of_dominates`). SUFFICIENCY is NOT
claimed: it needs "a symmetric `3×3` form is PSD iff its three elementary
symmetric functions are nonnegative", which is true but is an eigenvalue fact,
and the repo's PsdKit is deliberately spectral-theorem-free. The seven-minor
system above is therefore the load-bearing one; the legs are the compression it
would collapse to. -/

/-- The trace leg: the sum of the three pair minors through the pivot, i.e. the
trace of the Schur block. Degree 2 in the Gram entries, 6 monomials. -/
def quadTraceLeg (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond atomThird : Fin m) : ℝ :=
  gapPairMinor D pivot atomFirst + gapPairMinor D pivot atomSecond
    + gapPairMinor D pivot atomThird

/-- The minor leg: the sum of the three triple minors through the pivot. Degree
3 in the Gram entries, 15 monomials. -/
def quadMinorLeg (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond atomThird : Fin m) : ℝ :=
  gapTripleMinor D pivot atomFirst atomSecond
    + gapTripleMinor D pivot atomFirst atomThird
    + gapTripleMinor D pivot atomSecond atomThird

/-- The tie leg: the quadruple minor `det(Gram − I)` itself, pivot-free in
value. Degree 4 in the Gram entries, 17 monomials. Its vanishing is the
tightness boundary — at the `(k+1)`-simplex the gap on any `k`-subset is
`k·I − J`, whose determinant is zero at every rank, so no strictly positive
Positivstellensatz can certify the rank-four covering either. -/
def quadTieLeg (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond atomThird : Fin m) : ℝ :=
  gapQuadMinor D pivot atomFirst atomSecond atomThird

/-- The trace leg IS the trace of the Schur block. -/
theorem schurBlockFour_trace_eq_quadTraceLeg (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond atomThird : Fin m) :
    (schurBlockFour D pivot atomFirst atomSecond atomThird).trace
      = quadTraceLeg D pivot atomFirst atomSecond atomThird := by
  rw [Matrix.trace_fin_three]
  simp only [schurBlockFour, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    quadTraceLeg]

/-- The minor leg is the second elementary symmetric function of the Schur
block, divided by the corner: the sum of the block's three pair minors is
`corner · quadMinorLeg`. -/
theorem schurBlockFour_minorSum_eq_quadMinorLeg (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond atomThird : Fin m) :
    (gapPairMinor D pivot atomFirst * gapPairMinor D pivot atomSecond
          - schurCross D pivot atomFirst atomSecond ^ 2)
        + (gapPairMinor D pivot atomFirst * gapPairMinor D pivot atomThird
          - schurCross D pivot atomFirst atomThird ^ 2)
        + (gapPairMinor D pivot atomSecond * gapPairMinor D pivot atomThird
          - schurCross D pivot atomSecond atomThird ^ 2)
      = gapDiagonal D pivot * quadMinorLeg D pivot atomFirst atomSecond atomThird := by
  simp only [gapPairMinor, gapTripleMinor, schurCross, quadMinorLeg]
  ring

/-- The tie leg is the determinant of the Schur block, divided by the square of
the corner. -/
theorem schurBlockFour_det_eq_quadTieLeg (D : WeightedDesign m dim)
    (pivot atomFirst atomSecond atomThird : Fin m) :
    (schurBlockFour D pivot atomFirst atomSecond atomThird).det
      = gapDiagonal D pivot ^ 2
        * quadTieLeg D pivot atomFirst atomSecond atomThird :=
  schurBlockFour_det D pivot atomFirst atomSecond atomThird

/-- **The three legs are necessary.** A dominating quadruple with a heavy pivot
has all three legs nonnegative — each is a sum of pivot-containing principal
minors, and those are nonnegative by the narrowing. -/
theorem quadLegs_nonneg_of_dominates (D : WeightedDesign m 4)
    {pivot atomFirst atomSecond atomThird : Fin m}
    (hpivotFirst : pivot ≠ atomFirst) (hpivotSecond : pivot ≠ atomSecond)
    (hpivotThird : pivot ≠ atomThird) (hfirstSecond : atomFirst ≠ atomSecond)
    (hfirstThird : atomFirst ≠ atomThird) (hsecondThird : atomSecond ≠ atomThird)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hdominates : Dominates D {pivot, atomFirst, atomSecond, atomThird}) :
    0 ≤ quadTraceLeg D pivot atomFirst atomSecond atomThird
      ∧ 0 ≤ quadMinorLeg D pivot atomFirst atomSecond atomThird
      ∧ 0 ≤ quadTieLeg D pivot atomFirst atomSecond atomThird := by
  obtain ⟨hpairFirst, hpairSecond, hpairThird, htripleFirstSecond,
    htripleFirstThird, htripleSecondThird, hquad⟩ :=
    (dominates_quad_iff_pivotMinorSystem D hpivotFirst hpivotSecond hpivotThird
      hfirstSecond hfirstThird hsecondThird hpivotHeavy).mp hdominates
  refine ⟨?_, ?_, hquad⟩
  · rw [quadTraceLeg]; linarith
  · rw [quadMinorLeg]; linarith

/-! ### Calibration: the corner must be STRICTLY positive -/

/-- **A strictly positive corner is indispensable.** With the corner at zero
the seven-minor system goes silent: the Schur block of `diag(0,0,0,−1)`
vanishes identically, so all seven pivot-containing minors are zero, while the
quaternary form is negative along the last axis. The analogue of
`exists_dominatingTriple_withoutStrictGate` for the rank-four system, and the
reason `dominates_quad_iff_pivotMinorSystem` carries its heaviness hypothesis
rather than a nonnegative one. -/
theorem exists_negative_form_with_pivotMinors_zero :
    ∃ corner crossFirst crossSecond crossThird diagFirst diagSecond diagThird
      pairingFirstSecond pairingFirstThird pairingSecondThird : ℝ,
      corner = 0
        ∧ corner * diagFirst - crossFirst ^ 2 = 0
        ∧ corner * diagSecond - crossSecond ^ 2 = 0
        ∧ corner * diagThird - crossThird ^ 2 = 0
        ∧ corner * pairingFirstSecond - crossFirst * crossSecond = 0
        ∧ corner * pairingFirstThird - crossFirst * crossThird = 0
        ∧ corner * pairingSecondThird - crossSecond * crossThird = 0
        ∧ ¬ (∀ firstCoord secondCoord thirdCoord fourthCoord : ℝ,
          0 ≤ corner * firstCoord ^ 2 + diagFirst * secondCoord ^ 2
            + diagSecond * thirdCoord ^ 2 + diagThird * fourthCoord ^ 2
            + 2 * crossFirst * firstCoord * secondCoord
            + 2 * crossSecond * firstCoord * thirdCoord
            + 2 * crossThird * firstCoord * fourthCoord
            + 2 * pairingFirstSecond * secondCoord * thirdCoord
            + 2 * pairingFirstThird * secondCoord * fourthCoord
            + 2 * pairingSecondThird * thirdCoord * fourthCoord) := by
  refine ⟨0, 0, 0, 0, 0, 0, -1, 0, 0, 0, rfl, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, ?_⟩
  intro hform
  have hbad := hform 0 0 0 1
  norm_num at hbad

/-! ### Pins: the rank-three system, re-read through the generic minors -/

/-- The generic triple minor at the regular tetrahedron is EXACTLY zero — the
re-founded machinery reproduces `tetraDesign_discriminantTie`, the campaign's
sharpest object, on the nose. -/
theorem tetraDesign_gapTripleMinor : gapTripleMinor tetraDesign 0 1 2 = 0 :=
  (gapTripleMinor_eq_discriminantTie tetraDesign 0 1 2).trans
    tetraDesign_discriminantTie

/-- The two pair minors of the tetrahedron's triple sum to `6`, reproducing
`tetraDesign_discriminantTrace` through the generic minors. -/
theorem tetraDesign_gapPairMinor_sum :
    gapPairMinor tetraDesign 0 1 + gapPairMinor tetraDesign 0 2 = 6 :=
  (gapPairMinor_add_eq_discriminantTrace tetraDesign 0 1 2).trans
    tetraDesign_discriminantTrace

/-! ### The wall: the seventh Lifting-Lemma conjunct is not implied by the six

`exists_all_certificates_but_discriminant` produces, from `GtzWeightedAll k`,
six of the seven certificates of `LiftingLemma k` at a heavy pivot. The
seventh is the `∀ testVec` conjunct — classically `r rᵀ ⪯ A · (G′ − I)`, where
`A` is the pivot excess, `G′` the projected Gram of the selected subset and `r`
the cross vector. The hypothesis delivers only `G′ − I ⪰ 0`. The four results
below say that gap can never be bridged: on the tightness locus of the
projected domination the seventh conjunct degenerates into an exact
ORTHOGONALITY demand, which no amount of pivot leverage can supply. -/

/-- The deflation kills its own pivot direction: the completeness split plus
the coisometry identity force `B u = 0`. Used to recover the adapted
coordinates without carrying an extra hypothesis. -/
theorem deflator_kills_pivotUnit {rank : ℕ} {pivotUnit : Fin (rank + 1) → ℝ}
    {deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ}
    (hcoisometry : deflator * deflatorᵀ = 1)
    (hunit : pivotUnit ⬝ᵥ pivotUnit = 1)
    (hsplit : deflatorᵀ * deflator + atomMatrix pivotUnit = 1) :
    deflator *ᵥ pivotUnit = 0 := by
  have hsum := decompose_along_deflation hsplit pivotUnit
  rw [hunit, one_smul] at hsum
  have hzero : deflatorᵀ *ᵥ (deflator *ᵥ pivotUnit) = 0 :=
    add_right_cancel (hsum.trans (zero_add pivotUnit).symm)
  have hkey : deflator *ᵥ pivotUnit
      = deflator *ᵥ (deflatorᵀ *ᵥ (deflator *ᵥ pivotUnit)) := by
    rw [Matrix.mulVec_mulVec, hcoisometry, Matrix.one_mulVec]
  rw [hkey, hzero, Matrix.mulVec_zero]

/-- **The bordered form at every adapted coordinate.** A dominating bordered
subset makes the scalar quadratic of `bordered_form_eq` globally nonnegative in
BOTH adapted coordinates, because `w ↦ Bᵀv + a·u` covers the whole space. This
is the extraction step of `liftingLemma_of_gtzWeighted`, exported at a GIVEN
dominating subset instead of the one GTZ produces. -/
theorem borderedQuadratic_nonneg_of_dominates_insert {rank : ℕ}
    (D : WeightedDesign m (rank + 1)) (pivot : Fin m)
    {pivotUnit : Fin (rank + 1) → ℝ}
    {deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ}
    (hcoisometry : deflator * deflatorᵀ = 1)
    (hunit : pivotUnit ⬝ᵥ pivotUnit = 1)
    (hsplit : deflatorᵀ * deflator + atomMatrix pivotUnit = 1)
    (hkill : deflator *ᵥ D.atom pivot = 0)
    (subset : Finset (Fin m)) (hnotMem : pivot ∉ subset)
    (hdominates : Dominates D (insert pivot subset))
    (testVec : Fin rank → ℝ) (coordinate : ℝ) :
    0 ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
          + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1) * coordinate ^ 2
      + 2 * coordinate
        * (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
            * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec))
      + ((∑ c ∈ subset, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
        - testVec ⬝ᵥ testVec) := by
  have hkillUnit : deflator *ᵥ pivotUnit = 0 :=
    deflator_kills_pivotUnit hcoisometry hunit hsplit
  set adaptedVec : Fin (rank + 1) → ℝ :=
    deflatorᵀ *ᵥ testVec + coordinate • pivotUnit with hadaptedVec
  have hpivotOrthToLift : pivotUnit ⬝ᵥ (deflatorᵀ *ᵥ testVec) = 0 := by
    rw [dotProduct_comm, dotProduct_mulVec_transpose, hkillUnit, dotProduct_zero]
  have hcoordRecover : pivotUnit ⬝ᵥ adaptedVec = coordinate := by
    rw [hadaptedVec, dotProduct_add, hpivotOrthToLift, dotProduct_smul,
      smul_eq_mul, hunit, mul_one, zero_add]
  have hprojRecover : deflator *ᵥ adaptedVec = testVec := by
    rw [hadaptedVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, hcoisometry,
      Matrix.one_mulVec, Matrix.mulVec_smul, hkillUnit, smul_zero, add_zero]
  have hexpansion := bordered_form_eq D pivot hsplit hkill subset hnotMem adaptedVec
  have hcoercive := sum_sq_ge_of_dominates hdominates adaptedVec
  rw [← subsetSum_form_eq_sum_sq] at hcoercive
  rw [hcoordRecover, hprojRecover] at hexpansion
  linarith [hexpansion, hcoercive]

/-- **The seventh conjunct is NECESSARY at every dominating bordered subset** —
the converse reading of the discriminant, extracted per (pivot, subset) rather
than per design. Together with `dominates_insert_of_projection_certificates`
this makes the coupling an exact identity at each fixed pair, which is what
makes the tightness obstruction below unavoidable rather than an artifact of
the packaging. -/
theorem discriminant_of_dominates_insert {rank : ℕ}
    (D : WeightedDesign m (rank + 1)) (pivot : Fin m)
    {pivotUnit : Fin (rank + 1) → ℝ}
    {deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ}
    (hcoisometry : deflator * deflatorᵀ = 1)
    (hunit : pivotUnit ⬝ᵥ pivotUnit = 1)
    (hsplit : deflatorᵀ * deflator + atomMatrix pivotUnit = 1)
    (hkill : deflator *ᵥ D.atom pivot = 0)
    (subset : Finset (Fin m)) (hnotMem : pivot ∉ subset)
    (hfloor : 0 ≤ (pivotUnit ⬝ᵥ D.atom pivot) ^ 2
      + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
    (hdominates : Dominates D (insert pivot subset))
    (testVec : Fin rank → ℝ) :
    (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
        * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec)) ^ 2
      ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
            + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
          * ((∑ c ∈ subset, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
            - testVec ⬝ᵥ testVec) :=
  discriminant_le_of_quadratic_nonneg hfloor
    (borderedQuadratic_nonneg_of_dominates_insert D pivot hcoisometry hunit hsplit
      hkill subset hnotMem hdominates testVec)

/-- **THE WALL, half one: on the tightness locus the seventh conjunct is an
ORTHOGONALITY demand, not an estimate.** Wherever the projected domination is
TIGHT — the selected subset meets the identity form exactly along `testVec` —
a dominating bordered subset forces the cross sum to VANISH there. The pivot
excess multiplies a zero, so no leverage whatsoever enters: this is why the
numerically observed violation factors track `1/lambdaMin(G′ − I)` and blow up
(to 26058× on the `m = 8` rank-4 witness) exactly as the projected selection
approaches its own boundary. -/
theorem crossSum_eq_zero_of_dominates_insert_of_tight {rank : ℕ}
    (D : WeightedDesign m (rank + 1)) (pivot : Fin m)
    {pivotUnit : Fin (rank + 1) → ℝ}
    {deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ}
    (hcoisometry : deflator * deflatorᵀ = 1)
    (hunit : pivotUnit ⬝ᵥ pivotUnit = 1)
    (hsplit : deflatorᵀ * deflator + atomMatrix pivotUnit = 1)
    (hkill : deflator *ᵥ D.atom pivot = 0)
    (subset : Finset (Fin m)) (hnotMem : pivot ∉ subset)
    (hfloor : 0 ≤ (pivotUnit ⬝ᵥ D.atom pivot) ^ 2
      + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
    (hdominates : Dominates D (insert pivot subset))
    (testVec : Fin rank → ℝ)
    (htight : (∑ c ∈ subset, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
      = testVec ⬝ᵥ testVec) :
    (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
      * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec)) = 0 := by
  have hdiscriminant := discriminant_of_dominates_insert D pivot hcoisometry hunit
    hsplit hkill subset hnotMem hfloor hdominates testVec
  rw [htight, sub_self, mul_zero] at hdiscriminant
  exact pow_eq_zero_iff (two_ne_zero) |>.mp
    (le_antisymm hdiscriminant (sq_nonneg _))

/-- **THE WALL, half two: one tight direction with a cross component and the
lift FAILS.** At any rank, for any design, at any pivot: if the projected
selection is tight along some direction and the cross sum there is nonzero,
the bordered subset does NOT dominate — however heavy the pivot. This is the
exact mechanism behind the measured failure of the forced compression lift
(12.8%–43.8% of rank-4 designs across `m = 8..11`, and an 80-digit `m = 8`
witness where all eight pivots fail with the leverage floor and the projected
domination both holding). The induction hypothesis `GtzWeightedAll k` returns
a subset that dominates the projection; it says NOTHING about slack, and a
subset on its own PSD boundary is exactly what it is entitled to return. -/
theorem not_dominates_insert_of_tight_direction {rank : ℕ}
    (D : WeightedDesign m (rank + 1)) (pivot : Fin m)
    {pivotUnit : Fin (rank + 1) → ℝ}
    {deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ}
    (hcoisometry : deflator * deflatorᵀ = 1)
    (hunit : pivotUnit ⬝ᵥ pivotUnit = 1)
    (hsplit : deflatorᵀ * deflator + atomMatrix pivotUnit = 1)
    (hkill : deflator *ᵥ D.atom pivot = 0)
    (subset : Finset (Fin m)) (hnotMem : pivot ∉ subset)
    (hfloor : 0 ≤ (pivotUnit ⬝ᵥ D.atom pivot) ^ 2
      + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
    (testVec : Fin rank → ℝ)
    (htight : (∑ c ∈ subset, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
      = testVec ⬝ᵥ testVec)
    (hcross : (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
      * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec)) ≠ 0) :
    ¬ Dominates D (insert pivot subset) := fun hdominates =>
  hcross (crossSum_eq_zero_of_dominates_insert_of_tight D pivot hcoisometry hunit
    hsplit hkill subset hnotMem hfloor hdominates testVec htight)

/-- **THE WALL, half three, at the SCALAR level.** For every floor there are
bordered coefficients — leading coefficient above the floor and nonnegative,
constant term nonnegative — whose discriminant condition is false and whose
bordered form is genuinely negative at an adapted coordinate. Equivalently: a
quadratic with vanishing constant term and nonvanishing cross term is negative
somewhere however large its leading coefficient, so raising the pivot's
contribution alone can never force the bordered form nonnegative.

SCOPE, stated precisely because the name invites more: this quantifies over
four REALS. It does NOT say that data satisfying the Lifting Lemma's first six
certificates exist at every leverage with the seventh false — no
`WeightedDesign`, pivot, deflator or subset occurs in the statement. That
design-level claim is true and was verified in exact rationals during audit
(an `m = 11`, `dim = 4` integer design whose projected gap `G′ − I` is exactly
the zero matrix, realizing pivot leverages `4, 9, 25, 64, …, 10⁶` with the
seventh conjunct false and bordered forms `−1/4, −1/3, −1/7, …, −4/1000003`,
while the design itself still has 32–36 dominating quadruples), but it is NOT
mechanized here. Read this theorem as the scalar obstruction only. -/
theorem exists_borderedData_failing_discriminant_at_every_floor (floor : ℝ) :
    ∃ leading crossTerm constantTerm coordinate : ℝ,
      floor ≤ leading ∧ 0 ≤ leading ∧ 0 ≤ constantTerm
        ∧ ¬ (crossTerm ^ 2 ≤ leading * constantTerm)
        ∧ leading * coordinate ^ 2 + 2 * coordinate * crossTerm
            + constantTerm < 0 := by
  refine ⟨|floor| + 1, |floor| + 1, 0, -1, ?_, ?_, le_refl 0, ?_, ?_⟩
  · have hself := le_abs_self floor
    linarith
  · have habs : 0 ≤ |floor| := abs_nonneg floor
    linarith
  · have habs : 0 ≤ |floor| := abs_nonneg floor
    intro hbad
    rw [mul_zero] at hbad
    nlinarith [hbad]
  · have habs : 0 ≤ |floor| := abs_nonneg floor
    nlinarith

/-! ### What survives: the projected certificate is free, the selection is not

The route's projected-domination certificate needs NO induction hypothesis at
the right pivot: if a `(k+1)`-subset dominates upstairs then, at every one of
its atoms, the remaining `k` projections dominate the compression. So the
rank-`k` hypothesis is not what supplies the projected subset; it merely
supplies SOME projected subset at an ARBITRARY pivot, and the walls above show
that is not enough. What is left is the purely existential
`HasHeavyPivotInDominator` — a selection statement, formally stronger than GTZ
and not derived from anything here. -/

/-- A coercive family of atoms dominates: the converse of
`sum_sq_ge_of_dominates`, at every rank. -/
theorem dominates_of_coercive (D : WeightedDesign m dim) (C : Finset (Fin m))
    (hcoercive : ∀ probe : Fin dim → ℝ,
      probe ⬝ᵥ probe ≤ ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2) :
    Dominates D C := by
  have hsymmetric : (subsetSum D C - 1)ᵀ = subsetSum D C - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
    exact congrArg (· - 1) (Finset.sum_congr rfl fun c _ => by
      rw [atomMatrix, Matrix.transpose_vecMulVec])
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymmetric, fun probe => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    subsetSum_form_eq_sum_sq]
  linarith [hcoercive probe]

/-- **The projected certificate is FREE at every pivot of a dominating
subset** — no induction hypothesis, no leverage condition, no selection. Test
the upstairs domination at `Bᵀv`: the coisometry preserves its norm and the
killed pivot contributes nothing, so the remaining `k` projections carry the
identity form in the orthocomplement. This sharpens
`exists_good_in_projection`, which buys the same certificate from
`GtzWeightedAll k` at an arbitrary pivot. -/
theorem dominates_pushforward_of_dominates_insert {rank : ℕ}
    (D : WeightedDesign m (rank + 1)) (pivot : Fin m)
    {deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ}
    (hcoisometry : deflator * deflatorᵀ = 1)
    (hkill : deflator *ᵥ D.atom pivot = 0)
    (subset : Finset (Fin m)) (hnotMem : pivot ∉ subset)
    (hdominates : Dominates D (insert pivot subset)) :
    Dominates (coisometryPushforward D deflator hcoisometry) subset := by
  refine dominates_of_coercive _ _ fun probe => ?_
  have hliftNorm : (deflatorᵀ *ᵥ probe) ⬝ᵥ (deflatorᵀ *ᵥ probe) = probe ⬝ᵥ probe := by
    rw [dotProduct_mulVec_transpose, Matrix.mulVec_mulVec, hcoisometry,
      Matrix.one_mulVec]
  have hpivotDead : D.atom pivot ⬝ᵥ (deflatorᵀ *ᵥ probe) = 0 := by
    rw [dotProduct_comm, dotProduct_mulVec_transpose, hkill, dotProduct_zero]
  have hcoercive := sum_sq_ge_of_dominates hdominates (deflatorᵀ *ᵥ probe)
  rw [Finset.sum_insert hnotMem, hpivotDead, hliftNorm] at hcoercive
  have hterms : ∀ c ∈ subset,
      (D.atom c ⬝ᵥ (deflatorᵀ *ᵥ probe)) ^ 2
        = ((coisometryPushforward D deflator hcoisometry).atom c ⬝ᵥ probe) ^ 2 :=
    fun c _ => by
      rw [coisometryPushforward_atom, dotProduct_comm (D.atom c),
        dotProduct_mulVec_transpose, dotProduct_comm probe]
  rw [Finset.sum_congr rfl hterms] at hcoercive
  simpa using hcoercive

/-- **The residual of the route**, stated honestly: some dominating
`(k+1)`-subset contains an atom of leverage at least the rank. It IMPLIES
weighted GTZ (forget the pivot) and it is not implied by anything in this repo;
`exists_leverage_ge_rank` produces a heavy atom of the DESIGN, not a heavy atom
inside a DOMINATING subset, and the walls above show the difference is the
whole problem. Measured: over 21000 random rank-4 designs plus hill-climbing,
the minimum margin of this existential equals the design's own GTZ margin
exactly, and only 3 heavy pivots in 68756 sat outside every dominator — but
"GTZ implies this" is unproven, so it is a Prop here, not a theorem. -/
def HasHeavyPivotInDominator (m rank : ℕ) : Prop :=
  ∀ D : WeightedDesign m (rank + 1),
    ∃ (dominator : Finset (Fin m)) (pivot : Fin m),
      dominator.card = rank + 1 ∧ pivot ∈ dominator
        ∧ ((rank : ℝ) + 1 ≤ leverageOf (D.atom pivot))
        ∧ Dominates D dominator

/-- The residual implies weighted GTZ one rank up. -/
theorem gtzWeighted_succ_of_heavyPivotInDominator {rank : ℕ}
    (hresidual : HasHeavyPivotInDominator m rank) : GtzWeighted m (rank + 1) := by
  intro D
  obtain ⟨dominator, pivot, hcard, hpivotMem, hheavy, hdominates⟩ := hresidual D
  exact ⟨dominator, hcard, hdominates⟩

/-- **A dominating subset carries the whole PROJECTED side of the Lifting
Lemma, with no induction hypothesis.** Deflate at any pivot inside a dominating
subset: the compression's remaining atoms dominate outright. So the projected
certificate — the one the rank-`k` hypothesis was invoked for — is free once a
dominating subset with a usable pivot is in hand.

SCOPE: the conclusion is exactly the four projected certificates listed. It
does NOT contain the seventh conjunct, and this proof discards the `scale`,
`hsplit` and `hunitNorm` components of `exists_pivot_deflation` that
`discriminant_of_dominates_insert` would need to produce it. The name says
"of a dominating pivot", not "of `HasHeavyPivotInDominator`", because the
statement takes the pieces rather than that `Prop`. -/
theorem exists_projected_dominator_of_dominating_pivot {rank : ℕ}
    (D : WeightedDesign m (rank + 1)) (dominator : Finset (Fin m)) (pivot : Fin m)
    (hpivotMem : pivot ∈ dominator) (hcard : dominator.card = rank + 1)
    (hdominates : Dominates D dominator) (hpivotNonzero : D.atom pivot ≠ 0) :
    ∃ (deflator : Matrix (Fin rank) (Fin (rank + 1)) ℝ)
      (hcoisometry : deflator * deflatorᵀ = 1),
      deflator *ᵥ D.atom pivot = 0
        ∧ pivot ∉ dominator.erase pivot
        ∧ (dominator.erase pivot).card = rank
        ∧ Dominates (coisometryPushforward D deflator hcoisometry)
            (dominator.erase pivot) := by
  obtain ⟨scale, deflator, hscalePos, hcoisometry, hkill, hsplit, hunitNorm⟩ :=
    exists_pivot_deflation D pivot hpivotNonzero
  refine ⟨deflator, hcoisometry, hkill, Finset.notMem_erase pivot dominator, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hpivotMem, hcard]
    omega
  · refine dominates_pushforward_of_dominates_insert D pivot hcoisometry hkill
      (dominator.erase pivot) (Finset.notMem_erase pivot dominator) ?_
    rw [Finset.insert_erase hpivotMem]
    exact hdominates

end Gtz
