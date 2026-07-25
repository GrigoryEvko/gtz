/-
# The discriminant system: the rank-three residual as a finite polynomial covering

`Gtz.Quantitative.OneObjectNarrowing` eliminated the `∀ test vector` quantifier
from the seventh Lifting-Lemma conjunct, leaving two scalar inequalities per
(pivot, pair) — but as FREE-FLOATING scalar lemmas, with no map from a
`WeightedDesign` to the six scalars they speak about. This file supplies that
map and closes the loop: at rank three the whole conjecture becomes a covering
statement about explicit polynomials in the atom inner products, with no
matrices, no test vectors, and no deflation coisometry left in the conclusion.

The chart is the SCHUR-COMPLEMENT-AT-THE-PIVOT-CORNER one, which is strictly
simpler than the deflation chart and lands on the same abstract shape:

* domination of a 3-subset is `S_C ⪰ I` with `S_C = M Mᵀ` for the square matrix
  `M` whose columns are the three atoms; since `M` is square, `M Mᵀ ⪰ I ⟺
  Mᵀ M ⪰ I` (`posSemidef_transpose_mul_sub_one_comm`), and `Mᵀ M` is the GRAM.
  So domination is an `O(3)`-invariant condition on the six inner products —
  and it carries no pivot: the 60 (pivot, pair) combinations at `(6,3)` are 20
  triples read three ways (`discriminantSystem_pivot_independent`).
* the Gram minus identity has diagonal `heavyExcess c = |g_c|² − 1`, which
  `AllHeavy` makes STRICTLY POSITIVE at every atom. A symmetric `3×3` form with
  a positive corner completes the square exactly
  (`quadThree_nonneg_iff_schur_nonneg`, a division-free Schur complement), so
  nonnegativity collapses to a `2×2` form, and `2×2` collapses to trace and
  determinant (`twoByTwoForm_nonneg_iff_trace_det_nonneg`).
* the determinant factors through the resolvent tie
  (`discriminantDet_eq_resolventTie`), and the pivot's positive excess divides
  out, leaving `discriminantTie = det(Gram − I)` — the SAME polynomial for all
  three readings of a triple.

Net: `GtzWeightedHeavy m 3 ↔ DiscriminantCovering m`
(`gtzWeightedHeavy_three_iff_discriminantCovering`), an equivalence, not a
sufficiency; and chaining `rank_three_of_heavy_residuals`,

  `DiscriminantCovering 6 ∧ DiscriminantCovering 7 ↔ GtzWeightedAll 3`.

`discriminantTrace` has degree 2 and `discriminantTie` degree 3 in the six Gram
entries of a triple (degree 4 and 6 in the 18 atom coordinates). Nothing here
certifies the covering — that is the open content — but every future
certificate now has a fixed audited interface to plug into.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.Design.StressCertificate
import Gtz.Quantitative.OneObjectNarrowing
import Gtz.Reduction.Reductions
import Gtz.Reduction.RankFourWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ### The division-free Schur complement at a positive corner -/

/-- **Completing the square at the corner** (pure `ring`): multiplying a
symmetric `3×3` quadratic form by its corner entry splits it into one exact
square plus the Schur form in the remaining two variables. The identity that
makes the corner reduction division-free. -/
theorem cornerCompleteSquare (corner crossFirst crossSecond diagFirst pairing
    diagSecond firstCoord secondCoord thirdCoord : ℝ) :
    corner * (corner * firstCoord ^ 2 + diagFirst * secondCoord ^ 2
        + diagSecond * thirdCoord ^ 2
        + 2 * crossFirst * firstCoord * secondCoord
        + 2 * crossSecond * firstCoord * thirdCoord
        + 2 * pairing * secondCoord * thirdCoord)
      = (corner * firstCoord + crossFirst * secondCoord
            + crossSecond * thirdCoord) ^ 2
        + ((corner * diagFirst - crossFirst ^ 2) * secondCoord ^ 2
            + 2 * (corner * pairing - crossFirst * crossSecond)
                * secondCoord * thirdCoord
            + (corner * diagSecond - crossSecond ^ 2) * thirdCoord ^ 2) := by
  ring

/-- **The Schur complement at a positive corner**, `3×3`, division-free: a
symmetric ternary quadratic form with positive corner entry is globally
nonnegative iff its `2×2` Schur form is. Forward by evaluating at the
square-killing first coordinate, backward by `cornerCompleteSquare` and
dividing by the positive corner. -/
theorem quadThree_nonneg_iff_schur_nonneg (corner crossFirst crossSecond
    diagFirst pairing diagSecond : ℝ) (hcorner : 0 < corner) :
    (∀ firstCoord secondCoord thirdCoord : ℝ,
        0 ≤ corner * firstCoord ^ 2 + diagFirst * secondCoord ^ 2
          + diagSecond * thirdCoord ^ 2
          + 2 * crossFirst * firstCoord * secondCoord
          + 2 * crossSecond * firstCoord * thirdCoord
          + 2 * pairing * secondCoord * thirdCoord)
      ↔ (∀ testFirst testSecond : ℝ,
        0 ≤ (corner * diagFirst - crossFirst ^ 2) * testFirst ^ 2
          + 2 * (corner * pairing - crossFirst * crossSecond)
              * testFirst * testSecond
          + (corner * diagSecond - crossSecond ^ 2) * testSecond ^ 2) := by
  constructor
  · intro hform testFirst testSecond
    have hkey := hform
      (-(crossFirst * testFirst + crossSecond * testSecond) / corner)
      testFirst testSecond
    have hidentity := cornerCompleteSquare corner crossFirst crossSecond
      diagFirst pairing diagSecond
      (-(crossFirst * testFirst + crossSecond * testSecond) / corner)
      testFirst testSecond
    have hsquareZero : corner
        * (-(crossFirst * testFirst + crossSecond * testSecond) / corner)
        + crossFirst * testFirst + crossSecond * testSecond = 0 := by
      have hne : corner ≠ 0 := ne_of_gt hcorner
      field_simp
      ring
    rw [hsquareZero] at hidentity
    have hprod := mul_nonneg hcorner.le hkey
    rw [hidentity] at hprod
    linarith [hprod]
  · intro hschur firstCoord secondCoord thirdCoord
    have hidentity := cornerCompleteSquare corner crossFirst crossSecond
      diagFirst pairing diagSecond firstCoord secondCoord thirdCoord
    have hschurHere := hschur secondCoord thirdCoord
    have hsq := sq_nonneg (corner * firstCoord + crossFirst * secondCoord
      + crossSecond * thirdCoord)
    have hcornerMul : 0 ≤ corner * (corner * firstCoord ^ 2
        + diagFirst * secondCoord ^ 2 + diagSecond * thirdCoord ^ 2
        + 2 * crossFirst * firstCoord * secondCoord
        + 2 * crossSecond * firstCoord * thirdCoord
        + 2 * pairing * secondCoord * thirdCoord) := by
      rw [hidentity]; linarith [hsq, hschurHere]
    exact (mul_nonneg_iff_of_pos_left hcorner).mp hcornerMul

/-! ### The quadratic form of a symmetric `3×3` matrix -/

/-- Positive semidefiniteness of a symmetric real matrix is exactly global
nonnegativity of its quadratic form. -/
theorem posSemidef_iff_quadForm_nonneg {dim : ℕ} (gapMatrix : Matrix (Fin dim) (Fin dim) ℝ)
    (hsymm : gapMatrixᵀ = gapMatrix) :
    gapMatrix.PosSemidef ↔ ∀ testVec : Fin dim → ℝ, 0 ≤ testVec ⬝ᵥ (gapMatrix *ᵥ testVec) := by
  constructor
  · intro hpsd testVec
    have hquad := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 testVec
    rwa [star_trivial] at hquad
  · intro hquad
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hsymm, fun testVec => ?_⟩
    rw [star_trivial]
    exact hquad testVec

/-- The quadratic form of a symmetric `3×3` matrix, written out in its six
independent entries. -/
theorem quadForm_three_eq {gapMatrix : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : gapMatrixᵀ = gapMatrix) (testVec : Fin 3 → ℝ) :
    testVec ⬝ᵥ (gapMatrix *ᵥ testVec)
      = gapMatrix 0 0 * testVec 0 ^ 2 + gapMatrix 1 1 * testVec 1 ^ 2
        + gapMatrix 2 2 * testVec 2 ^ 2
        + 2 * gapMatrix 0 1 * testVec 0 * testVec 1
        + 2 * gapMatrix 0 2 * testVec 0 * testVec 2
        + 2 * gapMatrix 1 2 * testVec 1 * testVec 2 := by
  have hentry : ∀ rowIdx colIdx : Fin 3, gapMatrix colIdx rowIdx = gapMatrix rowIdx colIdx :=
    fun rowIdx colIdx => by
      have hcongr := congrFun (congrFun hsymm rowIdx) colIdx
      simpa using hcongr
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  rw [hentry 0 1, hentry 0 2, hentry 1 2]
  ring

/-! ### The triple chart: frame operator, Gram, and the six scalars -/

/-- The three atoms of an ordered triple, as a slot-indexed family. -/
def tripleAtom (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m)
    (slot : Fin 3) : Fin 3 → ℝ :=
  D.atom (![pivot, pairFirst, pairSecond] slot)

/-- The `3×3` matrix whose COLUMNS are the three atoms of an ordered triple.
Its `M Mᵀ` is the frame operator `S_C` and its `Mᵀ M` is the Gram — the same
spectrum, which is what makes domination an inner-product condition. -/
def tripleMatrix (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun coordIndex slot => tripleAtom D pivot pairFirst pairSecond slot coordIndex

/-- `M Mᵀ` recovers the frame operator of the triple. -/
theorem tripleMatrix_mul_transpose (D : WeightedDesign m 3) {pivot pairFirst pairSecond : Fin m}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) :
    tripleMatrix D pivot pairFirst pairSecond
        * (tripleMatrix D pivot pairFirst pairSecond)ᵀ
      = subsetSum D {pivot, pairFirst, pairSecond} := by
  rw [subsetSum,
    show ({pivot, pairFirst, pairSecond} : Finset (Fin m))
      = insert pivot (insert pairFirst {pairSecond}) from rfl,
    Finset.sum_insert (by simp [hpivotFirst, hpivotSecond]),
    Finset.sum_insert (by simp [hpairDistinct]), Finset.sum_singleton]
  ext rowIdx colIdx
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tripleMatrix, Matrix.of_apply,
    tripleAtom, Fin.sum_univ_three, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- `Mᵀ M` is the Gram matrix of the triple: its entries are the atom pairings. -/
theorem tripleMatrix_transpose_mul_apply (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) (slotRow slotCol : Fin 3) :
    ((tripleMatrix D pivot pairFirst pairSecond)ᵀ
        * tripleMatrix D pivot pairFirst pairSecond) slotRow slotCol
      = tripleAtom D pivot pairFirst pairSecond slotRow
          ⬝ᵥ tripleAtom D pivot pairFirst pairSecond slotCol := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tripleMatrix, Matrix.of_apply,
    dotProduct]

/-- The Gram gap `Gram − I` is symmetric. -/
theorem tripleGap_transpose (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) :
    ((tripleMatrix D pivot pairFirst pairSecond)ᵀ
        * tripleMatrix D pivot pairFirst pairSecond - 1)ᵀ
      = (tripleMatrix D pivot pairFirst pairSecond)ᵀ
          * tripleMatrix D pivot pairFirst pairSecond - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-! ### The six polynomial scalars of an ordered triple -/

/-- The **heavy excess** `|g_c|² − 1` of an atom: the diagonal of `Gram − I`.
`AllHeavy` says exactly that this is strictly positive at every atom. -/
def heavyExcess (D : WeightedDesign m 3) (atomIndex : Fin m) : ℝ :=
  leverageOf (D.atom atomIndex) - 1

/-- The **atom pairing** `⟨g_c, g_d⟩`: the off-diagonal of the Gram. -/
def atomPairing (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) : ℝ :=
  D.atom atomFirst ⬝ᵥ D.atom atomSecond

theorem atomPairing_comm (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    atomPairing D atomFirst atomSecond = atomPairing D atomSecond atomFirst :=
  dotProduct_comm _ _

theorem atomPairing_self (D : WeightedDesign m 3) (atomIndex : Fin m) :
    atomPairing D atomIndex atomIndex = leverageOf (D.atom atomIndex) :=
  dotProduct_self_eq_sum_sq (D.atom atomIndex)

/-- **The trace leg** of the discriminant system at an ordered triple: degree
two in the Gram entries, degree four in the atom coordinates. This is the trace
of the Schur complement of `Gram − I` at the pivot corner. -/
def discriminantTrace (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) : ℝ :=
  (heavyExcess D pivot * heavyExcess D pairFirst - atomPairing D pivot pairFirst ^ 2)
    + (heavyExcess D pivot * heavyExcess D pairSecond
        - atomPairing D pivot pairSecond ^ 2)

/-- **The tie leg** of the discriminant system: `det(Gram − I)`, degree three in
the Gram entries, degree six in the atom coordinates. It is the resolvent tie of
`discriminantDet_eq_resolventTie`; its vanishing is the tie boundary where the
covering margin is exactly zero (the tetrahedron, its splits, and — as the
`(6,3)` split of `sharpDesign` shows — strictly more). -/
def discriminantTie (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) : ℝ :=
  heavyExcess D pivot
      * (heavyExcess D pairFirst * heavyExcess D pairSecond
          - atomPairing D pairFirst pairSecond ^ 2)
    - (heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
        - 2 * atomPairing D pairFirst pairSecond * atomPairing D pivot pairFirst
            * atomPairing D pivot pairSecond
        + heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2)

/-! ### The entries of the Gram gap, in the six scalars -/

private theorem tripleGap_diag (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m)
    (slot : Fin 3) :
    ((tripleMatrix D pivot pairFirst pairSecond)ᵀ
        * tripleMatrix D pivot pairFirst pairSecond - 1) slot slot
      = leverageOf (tripleAtom D pivot pairFirst pairSecond slot) - 1 := by
  rw [Matrix.sub_apply, tripleMatrix_transpose_mul_apply, Matrix.one_apply_eq,
    dotProduct_self_eq_sum_sq]
  rfl

private theorem tripleGap_offDiag (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) {slotRow slotCol : Fin 3}
    (hne : slotRow ≠ slotCol) :
    ((tripleMatrix D pivot pairFirst pairSecond)ᵀ
        * tripleMatrix D pivot pairFirst pairSecond - 1) slotRow slotCol
      = tripleAtom D pivot pairFirst pairSecond slotRow
          ⬝ᵥ tripleAtom D pivot pairFirst pairSecond slotCol := by
  rw [Matrix.sub_apply, tripleMatrix_transpose_mul_apply, Matrix.one_apply_ne hne,
    sub_zero]

/-- The quadratic form of the Gram gap, in the six scalars of the triple. -/
private theorem tripleQuadForm_eq (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) (testVec : Fin 3 → ℝ) :
    testVec ⬝ᵥ (((tripleMatrix D pivot pairFirst pairSecond)ᵀ
        * tripleMatrix D pivot pairFirst pairSecond - 1) *ᵥ testVec)
      = heavyExcess D pivot * testVec 0 ^ 2
        + heavyExcess D pairFirst * testVec 1 ^ 2
        + heavyExcess D pairSecond * testVec 2 ^ 2
        + 2 * atomPairing D pivot pairFirst * testVec 0 * testVec 1
        + 2 * atomPairing D pivot pairSecond * testVec 0 * testVec 2
        + 2 * atomPairing D pairFirst pairSecond * testVec 1 * testVec 2 := by
  rw [quadForm_three_eq (tripleGap_transpose D pivot pairFirst pairSecond),
    tripleGap_diag, tripleGap_diag, tripleGap_diag,
    tripleGap_offDiag D pivot pairFirst pairSecond (by decide : (0 : Fin 3) ≠ 1),
    tripleGap_offDiag D pivot pairFirst pairSecond (by decide : (0 : Fin 3) ≠ 2),
    tripleGap_offDiag D pivot pairFirst pairSecond (by decide : (1 : Fin 3) ≠ 2)]
  simp only [tripleAtom, heavyExcess, atomPairing, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- The Schur determinant of the Gram gap factors as the pivot's heavy excess
times the resolvent tie — the `2×2` matrix-determinant lemma of
`discriminantDet_eq_resolventTie`, read in the triple's own scalars. -/
private theorem schurDet_eq_excess_mul_tie (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    (heavyExcess D pivot * heavyExcess D pairFirst
          - atomPairing D pivot pairFirst ^ 2)
        * (heavyExcess D pivot * heavyExcess D pairSecond
          - atomPairing D pivot pairSecond ^ 2)
      - (heavyExcess D pivot * atomPairing D pairFirst pairSecond
          - atomPairing D pivot pairFirst * atomPairing D pivot pairSecond) ^ 2
      = heavyExcess D pivot * discriminantTie D pivot pairFirst pairSecond := by
  simp only [discriminantTie]
  ring

/-! ### The narrowing -/

/-- **THE NARROWING**: for an ordered triple whose PIVOT is heavy, domination of
the triple is EXACTLY the pair of scalar polynomial inequalities
`discriminantTrace ≥ 0` and `discriminantTie ≥ 0`. No matrices, no test vectors,
no deflation coisometry: the conclusion mentions only the six inner products of
the triple. An equivalence, in both directions, unconditionally apart from the
pivot being heavy (which `exists_leverage_ge_rank` supplies at the max-leverage
atom of ANY design, and `AllHeavy` supplies at every atom). -/
theorem dominates_triple_iff_discriminantSystem (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot)) :
    Dominates D {pivot, pairFirst, pairSecond}
      ↔ (0 ≤ discriminantTrace D pivot pairFirst pairSecond
          ∧ 0 ≤ discriminantTie D pivot pairFirst pairSecond) := by
  have hexcessPos : 0 < heavyExcess D pivot := by
    rw [heavyExcess]; linarith
  have hframe := tripleMatrix_mul_transpose D hpivotFirst hpivotSecond hpairDistinct
  have hgram : Dominates D {pivot, pairFirst, pairSecond}
      ↔ ((tripleMatrix D pivot pairFirst pairSecond)ᵀ
          * tripleMatrix D pivot pairFirst pairSecond - 1).PosSemidef := by
    rw [Dominates, ← hframe]
    exact (posSemidef_transpose_mul_sub_one_comm
      (tripleMatrix D pivot pairFirst pairSecond)).symm
  rw [hgram, posSemidef_iff_quadForm_nonneg _ (tripleGap_transpose D pivot pairFirst pairSecond)]
  have hform : (∀ testVec : Fin 3 → ℝ, 0 ≤ testVec
        ⬝ᵥ (((tripleMatrix D pivot pairFirst pairSecond)ᵀ
            * tripleMatrix D pivot pairFirst pairSecond - 1) *ᵥ testVec))
      ↔ ∀ firstCoord secondCoord thirdCoord : ℝ,
        0 ≤ heavyExcess D pivot * firstCoord ^ 2
          + heavyExcess D pairFirst * secondCoord ^ 2
          + heavyExcess D pairSecond * thirdCoord ^ 2
          + 2 * atomPairing D pivot pairFirst * firstCoord * secondCoord
          + 2 * atomPairing D pivot pairSecond * firstCoord * thirdCoord
          + 2 * atomPairing D pairFirst pairSecond * secondCoord * thirdCoord := by
    constructor
    · intro hquad firstCoord secondCoord thirdCoord
      have hhere := hquad ![firstCoord, secondCoord, thirdCoord]
      rw [tripleQuadForm_eq] at hhere
      simpa using hhere
    · intro hscalar testVec
      rw [tripleQuadForm_eq]
      exact hscalar (testVec 0) (testVec 1) (testVec 2)
  rw [hform, quadThree_nonneg_iff_schur_nonneg _ _ _ _ _ _ hexcessPos,
    twoByTwoForm_nonneg_iff_trace_det_nonneg, schurDet_eq_excess_mul_tie,
    mul_nonneg_iff_of_pos_left hexcessPos]
  exact Iff.rfl

/-! ### The covering statement -/

/-- **The DISC-QE covering system** at size `m`: every all-heavy weighted
`(m,3)` design has an ordered triple at which the two polynomial legs are both
nonnegative. This is a purely real-algebraic sentence: 24 real variables at
`m = 6`, seven quadratic design equations, `m` strict all-heavy inequalities, and
a disjunction over ordered triples of one degree-4 and one degree-6 polynomial
inequality in the atom coordinates. -/
def DiscriminantCovering (m : ℕ) : Prop :=
  ∀ D : WeightedDesign m 3, AllHeavy D →
    ∃ pivot pairFirst pairSecond : Fin m,
      pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ 0 ≤ discriminantTrace D pivot pairFirst pairSecond
        ∧ 0 ≤ discriminantTie D pivot pairFirst pairSecond

/-- **The narrowing, at the level of the statement**: all-heavy weighted GTZ at
rank three IS the discriminant covering — an equivalence, not a sufficiency. The
`∀ design ∃ subset` shape survives; what disappears is every trace of linear
algebra in the inner condition. -/
theorem gtzWeightedHeavy_three_iff_discriminantCovering (m : ℕ) :
    GtzWeightedHeavy m 3 ↔ DiscriminantCovering m := by
  constructor
  · intro hgtz D hheavy
    obtain ⟨C, hcard, hdominates⟩ := hgtz D hheavy
    obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      hCeq⟩ := Finset.card_eq_three.mp hcard
    subst hCeq
    refine ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct, ?_⟩
    exact (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
      hpairDistinct (hheavy pivot)).mp hdominates
  · intro hcover D hheavy
    obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      htrace, htie⟩ := hcover D hheavy
    refine ⟨{pivot, pairFirst, pairSecond}, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simp [hpivotFirst, hpivotSecond]),
        Finset.card_insert_of_notMem (by simp [hpairDistinct]), Finset.card_singleton]
    · exact (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
        hpairDistinct (hheavy pivot)).mpr ⟨htrace, htie⟩

/-- **The pivot collapse**: at an all-heavy design the discriminant reading of a
triple does not depend on which of its three atoms is taken as pivot — both
readings are equivalent to domination of the same subset. So the 60 (pivot,
pair) combinations at `(6,3)` are 20 triples read three ways, and the 35 at
`(7,3)` are 35 triples read three ways; a case split should be organised over
triples, never over combinations. -/
theorem discriminantSystem_pivot_independent (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hfirstHeavy : 1 < leverageOf (D.atom pairFirst)) :
    (0 ≤ discriminantTrace D pivot pairFirst pairSecond
        ∧ 0 ≤ discriminantTie D pivot pairFirst pairSecond)
      ↔ (0 ≤ discriminantTrace D pairFirst pivot pairSecond
          ∧ 0 ≤ discriminantTie D pairFirst pivot pairSecond) := by
  rw [← dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
      hpairDistinct hpivotHeavy,
    ← dominates_triple_iff_discriminantSystem D hpivotFirst.symm hpairDistinct
      hpivotSecond hfirstHeavy,
    Finset.insert_comm]

/-- The tie leg is invariant under swapping the pivot with the first pair atom —
a `ring` fact, independent of the geometric collapse above, reflecting that
`discriminantTie` is `det(Gram − I)` and determinants are relabelling-invariant. -/
theorem discriminantTie_swap (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    discriminantTie D pivot pairFirst pairSecond
      = discriminantTie D pairFirst pivot pairSecond := by
  simp only [discriminantTie, atomPairing_comm D pairFirst pivot]
  ring

/-! ### The rank-three residual, as polynomials -/

/-- **The two residuals become two polynomial covering statements.** Chaining
`rank_three_of_heavy_residuals`, the entire remaining content of the 1997
conjecture at rank three is the covering of the all-heavy `(6,3)` and `(7,3)`
parameter spaces by the finitely many basic closed semialgebraic sets
`{discriminantTrace ≥ 0} ∩ {discriminantTie ≥ 0}`. -/
theorem rank_three_of_discriminantCovering (hsix : DiscriminantCovering 6)
    (hseven : DiscriminantCovering 7) : GtzWeightedAll 3 :=
  rank_three_of_heavy_residuals
    ((gtzWeightedHeavy_three_iff_discriminantCovering 6).mpr hsix)
    ((gtzWeightedHeavy_three_iff_discriminantCovering 7).mpr hseven)

/-- **The equivalence, at the residual level**: the two polynomial coverings are
not merely sufficient for rank three — they are equivalent to it. There is no
slack in the narrowing. -/
theorem discriminantCovering_iff_rank_three :
    (DiscriminantCovering 6 ∧ DiscriminantCovering 7) ↔ GtzWeightedAll 3 := by
  constructor
  · rintro ⟨hsix, hseven⟩
    exact rank_three_of_discriminantCovering hsix hseven
  · intro hrank
    refine ⟨(gtzWeightedHeavy_three_iff_discriminantCovering 6).mp
        (fun D _ => hrank 6 D), ?_⟩
    exact (gtzWeightedHeavy_three_iff_discriminantCovering 7).mp (fun D _ => hrank 7 D)

/-- **The original 1997 statement at rank three, from the polynomial coverings
alone.** Every remaining ingredient is a kernel-checked theorem of this repo;
what is open is exactly the two covering sentences, which contain no analysis. -/
theorem gtz_original_rank_three_of_discriminantCovering (hsix : DiscriminantCovering 6)
    (hseven : DiscriminantCovering 7) : ∀ n, 0 < n → GtzOriginal n 3 :=
  original_of_weighted 3 (rank_three_of_discriminantCovering hsix hseven)

/-! ### The covering is one sentence, not a pair

`replicatedDesign` splits an atom's WEIGHT while duplicating its VECTOR, so it
preserves all-heaviness (`replicatedDesign_allHeavy`); hence size monotonicity
runs inside the all-heavy statement (`gtzWeightedHeavy_of_le`) and the covering
at the crystallization cap `M(3) = 7` implies the covering at every smaller
size. The pair `(6,3) ∧ (7,3)` above is therefore redundant on its first
component, matching the collapse `gtzWeighted_six_three_of_seven_three` already
proved for the unrestricted statement. -/

/-- Coverings are monotone in the number of atoms, through the all-heavy
statement they are equivalent to. -/
theorem discriminantCovering_of_le {size larger : ℕ} (hle : size ≤ larger)
    (hcover : DiscriminantCovering larger) : DiscriminantCovering size :=
  (gtzWeightedHeavy_three_iff_discriminantCovering size).mp
    (gtzWeightedHeavy_of_le hle
      ((gtzWeightedHeavy_three_iff_discriminantCovering larger).mpr hcover))

/-- **Rank three from the `(7,3)` covering alone.** -/
theorem rank_three_of_discriminantCovering_seven (hseven : DiscriminantCovering 7) :
    GtzWeightedAll 3 :=
  rank_three_of_heavy_top
    ((gtzWeightedHeavy_three_iff_discriminantCovering 7).mpr hseven)

/-- **The polynomial frontier of rank three, as a single equivalence.** GTZ at
rank three for every `n` IS the one covering sentence at `(7,3)`: every all-heavy
weighted `(7,3)` design has one of its `35` triples at which `discriminantTrace`
and `discriminantTie` are both nonnegative. Two polynomial inequalities of
degrees `2` and `3` in the six Gram entries of a triple (`4` and `6` in the `21`
atom coordinates), quantified over a real semialgebraic parameter space, with no
matrices, no test vectors and no analysis anywhere in the statement. -/
theorem discriminantCovering_seven_iff_rank_three :
    DiscriminantCovering 7 ↔ GtzWeightedAll 3 := by
  constructor
  · exact rank_three_of_discriminantCovering_seven
  · intro hrank
    exact (gtzWeightedHeavy_three_iff_discriminantCovering 7).mp (fun D _ => hrank 7 D)

/-- **The 1997 statement at rank three from the single covering sentence.** -/
theorem gtz_original_rank_three_of_discriminantCovering_seven
    (hseven : DiscriminantCovering 7) : ∀ n, 0 < n → GtzOriginal n 3 :=
  original_of_weighted 3 (rank_three_of_discriminantCovering_seven hseven)

/-! ### Calibration: the system is not vacuous -/

/-- **A necessary condition that is NOT part of the system**: the second
elementary symmetric function of `Gram − I` is nonnegative whenever the triple
dominates. It follows from the two legs at an all-heavy triple but is listed
separately because the numerics say it is genuinely active — about a third of
random all-heavy `(6,3)` designs carry a triple with `discriminantTie ≥ 0` and
this quantity negative, so dropping the trace leg would prove a strictly weaker
statement. -/
def discriminantMinorSum (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) : ℝ :=
  (heavyExcess D pivot * heavyExcess D pairFirst - atomPairing D pivot pairFirst ^ 2)
    + (heavyExcess D pivot * heavyExcess D pairSecond
        - atomPairing D pivot pairSecond ^ 2)
    + (heavyExcess D pairFirst * heavyExcess D pairSecond
        - atomPairing D pairFirst pairSecond ^ 2)

/-- The minor sum exceeds the trace leg by the pair's own minor, so a
dominating triple with a heavy pivot has both nonnegative — the trace leg is the
strictly stronger of the two. -/
theorem discriminantMinorSum_eq (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    discriminantMinorSum D pivot pairFirst pairSecond
      = discriminantTrace D pivot pairFirst pairSecond
        + (heavyExcess D pairFirst * heavyExcess D pairSecond
            - atomPairing D pairFirst pairSecond ^ 2) := by
  simp only [discriminantMinorSum, discriminantTrace]

/-- At an all-heavy design every atom is a legal pivot, so the max-leverage
pivot of `exists_leverage_ge_rank` is never needed: the covering may be searched
over ordered triples freely. -/
theorem allHeavy_heavyExcess_pos {D : WeightedDesign m 3} (hheavy : AllHeavy D)
    (atomIndex : Fin m) : 0 < heavyExcess D atomIndex := by
  have hlev := hheavy atomIndex
  rw [heavyExcess]
  linarith


/-! ### Kernel pin: the system evaluated at the regular tetrahedron -/

/-- Every tetrahedron atom has leverage `3`. -/
theorem tetraDesign_leverage (atomIndex : Fin 4) :
    leverageOf (tetraDesign.atom atomIndex) = 3 := by
  have hdot := tetraAtom_dot_self atomIndex
  simp only [leverageOf]
  rw [← dotProduct_self_eq_sum_sq]
  exact hdot

/-- Every tetrahedron atom has heavy excess `2` (leverage `3`). -/
theorem tetraDesign_heavyExcess (atomIndex : Fin 4) :
    heavyExcess tetraDesign atomIndex = 2 := by
  rw [heavyExcess, tetraDesign_leverage]
  norm_num

/-- The tetrahedron's pairings are all `-1` on the triple `{0,1,2}`. -/
theorem tetraDesign_atomPairing_zeroOne : atomPairing tetraDesign 0 1 = -1 := by
  simp [atomPairing, tetraDesign, tetraAtom, dotProduct, Fin.sum_univ_three]

theorem tetraDesign_atomPairing_zeroTwo : atomPairing tetraDesign 0 2 = -1 := by
  simp [atomPairing, tetraDesign, tetraAtom, dotProduct, Fin.sum_univ_three]

theorem tetraDesign_atomPairing_oneTwo : atomPairing tetraDesign 1 2 = -1 := by
  simp [atomPairing, tetraDesign, tetraAtom, dotProduct, Fin.sum_univ_three]

/-- **The trace leg at the tetrahedron is `6`.** -/
theorem tetraDesign_discriminantTrace : discriminantTrace tetraDesign 0 1 2 = 6 := by
  rw [discriminantTrace, tetraDesign_heavyExcess, tetraDesign_heavyExcess,
    tetraDesign_heavyExcess, tetraDesign_atomPairing_zeroOne,
    tetraDesign_atomPairing_zeroTwo]
  norm_num

/-- **The tie leg at the tetrahedron is EXACTLY zero** — the covering has no
slack at the corner-fiber equality case, which is why no strictly-positive
Positivstellensatz can certify the covering globally. -/
theorem tetraDesign_discriminantTie : discriminantTie tetraDesign 0 1 2 = 0 := by
  rw [discriminantTie, tetraDesign_heavyExcess, tetraDesign_heavyExcess,
    tetraDesign_heavyExcess, tetraDesign_atomPairing_zeroOne,
    tetraDesign_atomPairing_zeroTwo, tetraDesign_atomPairing_oneTwo]
  norm_num

/-- **The pin**: the narrowing, fed the two tetrahedron scalars, re-derives
domination of `{0,1,2}` at the regular tetrahedron — a fact the repo also proves
by an independent sum-of-squares route (`Gtz.Ties.TetrahedronTie`). The
symbolic system and the kernel agree at the campaign's sharpest object. -/
theorem tetraDesign_dominates_of_discriminantSystem :
    Dominates tetraDesign {0, 1, 2} := by
  refine (dominates_triple_iff_discriminantSystem tetraDesign (by decide)
    (by decide) (by decide) ?_).mpr ?_
  · rw [tetraDesign_leverage]; norm_num
  · rw [tetraDesign_discriminantTrace, tetraDesign_discriminantTie]
    exact ⟨by norm_num, le_refl 0⟩

/-- The tetrahedron is all-heavy, so every one of its atoms is a legal pivot and
all three readings of the triple `{0,1,2}` agree. -/
theorem tetraDesign_allHeavy : AllHeavy tetraDesign := by
  intro atomIndex
  rw [tetraDesign_leverage]; norm_num

/-! ### A stratum on which the covering is PROVED -/

/-- **The near-orthogonal stratum, closed unconditionally.** A triple whose
three pairings satisfy `4·p² ≤ a·a` on every pair dominates. The constant `4`
is SHARP: the regular tetrahedron has `a = 2` and `p = -1` on every pair, so it
sits exactly on the boundary of this stratum — and exactly there
`discriminantTie = 0` (`tetraDesign_discriminantTie`). So this is not a soft
sufficient condition with room to spare; it is the covering proved on the
largest stratum this normalisation can reach, tight at the tie.

Proof: the three hypotheses bound each squared pairing by a quarter of the
matching excess product, so the negative part of the tie leg is at most
`(3/4)·a·a·a`, while the triple product term is at least `-(1/4)·a·a·a` — the
latter division-free, by squaring the three hypotheses together. -/
theorem dominates_of_dominantPairings (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hfirstHeavy : 1 < leverageOf (D.atom pairFirst))
    (hsecondHeavy : 1 < leverageOf (D.atom pairSecond))
    (hpivotFirstSmall : 4 * atomPairing D pivot pairFirst ^ 2
        ≤ heavyExcess D pivot * heavyExcess D pairFirst)
    (hpivotSecondSmall : 4 * atomPairing D pivot pairSecond ^ 2
        ≤ heavyExcess D pivot * heavyExcess D pairSecond)
    (hpairSmall : 4 * atomPairing D pairFirst pairSecond ^ 2
        ≤ heavyExcess D pairFirst * heavyExcess D pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  have hpivotPos : 0 < heavyExcess D pivot := by rw [heavyExcess]; linarith
  have hfirstPos : 0 < heavyExcess D pairFirst := by rw [heavyExcess]; linarith
  have hsecondPos : 0 < heavyExcess D pairSecond := by rw [heavyExcess]; linarith
  refine (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
    hpairDistinct hpivotHeavy).mpr ⟨?_, ?_⟩
  · rw [discriminantTrace]
    nlinarith [hpivotFirstSmall, hpivotSecondSmall, hpivotPos, hfirstPos,
      hsecondPos, mul_pos hpivotPos hfirstPos, mul_pos hpivotPos hsecondPos]
  · have hsquareStep : (4 * atomPairing D pivot pairFirst ^ 2)
        * (4 * atomPairing D pivot pairSecond ^ 2)
        ≤ (heavyExcess D pivot * heavyExcess D pairFirst)
          * (heavyExcess D pivot * heavyExcess D pairSecond) :=
      mul_le_mul hpivotFirstSmall hpivotSecondSmall (by positivity)
        (le_of_lt (mul_pos hpivotPos hfirstPos))
    have hcubeStep : ((4 * atomPairing D pivot pairFirst ^ 2)
          * (4 * atomPairing D pivot pairSecond ^ 2))
        * (4 * atomPairing D pairFirst pairSecond ^ 2)
        ≤ ((heavyExcess D pivot * heavyExcess D pairFirst)
            * (heavyExcess D pivot * heavyExcess D pairSecond))
          * (heavyExcess D pairFirst * heavyExcess D pairSecond) :=
      mul_le_mul hsquareStep hpairSmall (by positivity)
        (le_of_lt (mul_pos (mul_pos hpivotPos hfirstPos)
          (mul_pos hpivotPos hsecondPos)))
    have htripleProduct : (2 * atomPairing D pivot pairFirst
          * atomPairing D pivot pairSecond * atomPairing D pairFirst pairSecond) ^ 2
        ≤ (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond
            / 4) ^ 2 := by nlinarith [hcubeStep]
    have hexcessProductPos : 0 < heavyExcess D pivot * heavyExcess D pairFirst
        * heavyExcess D pairSecond :=
      mul_pos (mul_pos hpivotPos hfirstPos) hsecondPos
    have hlowerBound : -(heavyExcess D pivot * heavyExcess D pairFirst
          * heavyExcess D pairSecond / 4)
        ≤ 2 * atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
            * atomPairing D pairFirst pairSecond := by
      nlinarith [htripleProduct, hexcessProductPos]
    rw [discriminantTie]
    nlinarith [hlowerBound, hpivotFirstSmall, hpivotSecondSmall, hpairSmall,
      hpivotPos, hfirstPos, hsecondPos, hexcessProductPos,
      mul_pos hpivotPos hfirstPos, mul_pos hpivotPos hsecondPos,
      mul_pos hfirstPos hsecondPos]

/-- **The orthogonal-triple corner of the stratum**: a triple of pairwise
orthogonal heavy atoms always dominates. Immediate from
`dominates_of_dominantPairings`, and a useful sanity anchor — it is the only
part of the covering that needs no inequality at all. -/
theorem dominates_of_orthogonalTriple (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hfirstHeavy : 1 < leverageOf (D.atom pairFirst))
    (hsecondHeavy : 1 < leverageOf (D.atom pairSecond))
    (hpivotFirstZero : atomPairing D pivot pairFirst = 0)
    (hpivotSecondZero : atomPairing D pivot pairSecond = 0)
    (hpairZero : atomPairing D pairFirst pairSecond = 0) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  have hpivotPos : 0 < heavyExcess D pivot := by rw [heavyExcess]; linarith
  have hfirstPos : 0 < heavyExcess D pairFirst := by rw [heavyExcess]; linarith
  have hsecondPos : 0 < heavyExcess D pairSecond := by rw [heavyExcess]; linarith
  refine dominates_of_dominantPairings D hpivotFirst hpivotSecond hpairDistinct
    hpivotHeavy hfirstHeavy hsecondHeavy ?_ ?_ ?_
  · rw [hpivotFirstZero]; nlinarith [mul_pos hpivotPos hfirstPos]
  · rw [hpivotSecondZero]; nlinarith [mul_pos hpivotPos hsecondPos]
  · rw [hpairZero]; nlinarith [mul_pos hfirstPos hsecondPos]

/-- **The stratum, at the level of the covering statement**: a design that owns
one near-orthogonal triple is covered. So the open content of
`DiscriminantCovering` lives entirely on designs whose EVERY triple has a pair
violating `4·p² ≤ a·a` — the regular tetrahedron and its splits sit exactly on
that boundary. -/
theorem discriminantCovering_of_dominantPairingTriple {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) {pivot pairFirst pairSecond : Fin m}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotFirstSmall : 4 * atomPairing D pivot pairFirst ^ 2
        ≤ heavyExcess D pivot * heavyExcess D pairFirst)
    (hpivotSecondSmall : 4 * atomPairing D pivot pairSecond ^ 2
        ≤ heavyExcess D pivot * heavyExcess D pairSecond)
    (hpairSmall : 4 * atomPairing D pairFirst pairSecond ^ 2
        ≤ heavyExcess D pairFirst * heavyExcess D pairSecond) :
    ∃ chosenPivot chosenFirst chosenSecond : Fin m,
      chosenPivot ≠ chosenFirst ∧ chosenPivot ≠ chosenSecond
        ∧ chosenFirst ≠ chosenSecond
        ∧ 0 ≤ discriminantTrace D chosenPivot chosenFirst chosenSecond
        ∧ 0 ≤ discriminantTie D chosenPivot chosenFirst chosenSecond :=
  ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
    ((dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
      hpairDistinct (hheavy pivot)).mp
        (dominates_of_dominantPairings D hpivotFirst hpivotSecond hpairDistinct
          (hheavy pivot) (hheavy pairFirst) (hheavy pairSecond)
          hpivotFirstSmall hpivotSecondSmall hpairSmall)).1,
    ((dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
      hpairDistinct (hheavy pivot)).mp
        (dominates_of_dominantPairings D hpivotFirst hpivotSecond hpairDistinct
          (hheavy pivot) (hheavy pairFirst) (hheavy pairSecond)
          hpivotFirstSmall hpivotSecondSmall hpairSmall)).2⟩

/-- The tetrahedron sits exactly ON the stratum boundary: `4·p² = a·a` on every
pair. This is the calibration that shows the constant cannot be improved. -/
theorem tetraDesign_pairing_boundary :
    4 * atomPairing tetraDesign 0 1 ^ 2
      = heavyExcess tetraDesign 0 * heavyExcess tetraDesign 1 := by
  rw [tetraDesign_atomPairing_zeroOne, tetraDesign_heavyExcess,
    tetraDesign_heavyExcess]
  norm_num

end Gtz
