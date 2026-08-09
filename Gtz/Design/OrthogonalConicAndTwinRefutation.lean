import Gtz.Design.LineClassObstructions
import Gtz.Design.LineFreeConicBridge
import Gtz.Design.OneDeterminantReduction
import Gtz.Reduction.TwoVanishedBoundary
import Gtz.Quantitative.PhaseFreeNoGo
import Gtz.LinAlg.PsdKit
import Gtz.Core.Sanity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# Off-conicity bites: orthogonal triples are conic, and the twin's canonical pair fails

Two independent results, both closing questions the Phase-2 reports left named and
open.

## Part A.  An orthogonal triple forces a common conic

Retry agent 1 recorded, as an UNFORMALISED structural observation, that a `(6,3)`
design whose base triple is orthogonal can never be off-conic.  That is proved
here, in the sharpest form, with no normalisation and no square roots.

Let `u`, `v`, `w` be three pairwise orthogonal nonzero atoms of a design.  They
are automatically a basis, and the three symmetric outer products
`u vᵀ + v uᵀ`, `u wᵀ + w uᵀ`, `v wᵀ + w vᵀ` are quadrics that ALL THREE base atoms
already satisfy -- the orthogonality kills every term.  So the six atoms lie on a
common conic as soon as the remaining three atoms can be made to satisfy one
nonzero combination of the three, i.e. as soon as the `3x3` matrix

    M[freeLabel][basePair]  =  (u_i . a_free) * (u_j . a_free)

is singular.  And it always is: polarised Parseval against the base pair `(u_i,
u_j)` reads `u_i . u_j = 0` on the left, the three base atoms contribute nothing
on the right by orthogonality, and what is left is exactly the statement that the
POSITIVE weight vector of the three free labels is a left null vector of `M`.

Consequences.

* `Gtz.not_hasNoCommonQuadric_of_orthogonalTriple` -- no `(6,3)` design with three
  mutually orthogonal atoms is off-conic.
* `Gtz.not_orthogonalTriple_of_hasNoCommonQuadric` -- read the other way: on the
  off-conic stratum NO three atoms are mutually orthogonal.  Since
  `Gtz.dominates_of_orthogonalTriple_of_one_le` turns a heavy orthogonal triple
  into a dominator for free, this says the one cheap source of dominators is
  exactly what off-conicity forbids.
* `Gtz.subsetSum_eq_one_iff_orthonormalTriple`,
  `Gtz.subsetSum_sub_one_ne_zero_of_hasNoCommonQuadric` and
  `Gtz.baseTripleGap_psd_singular_ne_zero_of_offConic` -- a triple's gap vanishes
  identically exactly when the triple is an orthonormal basis, so on the off-conic
  stratum the gap of a weakly dominating triple is a NONZERO singular positive
  semidefinite matrix.  Its rank is one or two; it is never the zero form.

This is, as far as the Phase-2 record goes, the first place in the campaign where
the off-conic hypothesis of `Gtz.BaseTripleTightLineFreeOffConicWeakToStrict` does
any work at all.  Both `Gtz.UThreeSixDisjunction`-style balance arguments and the
`Gtz.ComplementFrame` lane treat it as carried and unspent.

## Part B.  The twin's canonical triples can both fail

Retry agent 1 also left this OPEN, and named it the obvious next exact-rational
search: on the two-meeting-lines stratum, every chartless certificate nominates
one of the two line complements, `{3,4,5}` for the line `{0,1,2}` and `{1,2,5}`
for the line `{0,3,4}`.  `Gtz.twinFailureDesign` is a HEAVY member of that
stratum, carrying a weakly dominating triple, on which NEITHER canonical triple
even dominates.  So the twin's two reductions have a genuinely nonempty joint
residual, and a certificate must nominate a mixed triple.

The design refutes the strategy, never the obligation: `{2,4,5}` is strictly
dominating on it.
-/

namespace Gtz

open Matrix

/-! ## Part A.1.  The symmetric outer product -/

/-- The symmetric outer product `x yᵀ + y xᵀ`, the quadric whose value at a probe
is twice the product of the two readings. -/
def symmetricOuterPair (leftVec rightVec : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.vecMulVec leftVec rightVec + Matrix.vecMulVec rightVec leftVec

/-- It is symmetric, which is half of what `Gtz.HasNoCommonQuadric` asks of a
candidate conic. -/
theorem transpose_symmetricOuterPair (leftVec rightVec : Fin 3 → ℝ) :
    (symmetricOuterPair leftVec rightVec)ᵀ = symmetricOuterPair leftVec rightVec := by
  ext rowIndex colIndex
  simp only [symmetricOuterPair, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply]
  ring

/-- The full bilinear reading of the symmetric outer product. -/
theorem dotProduct_symmetricOuterPair_mulVec_pair
    (leftVec rightVec probeLeft probeRight : Fin 3 → ℝ) :
    probeLeft ⬝ᵥ (symmetricOuterPair leftVec rightVec *ᵥ probeRight)
      = (leftVec ⬝ᵥ probeLeft) * (rightVec ⬝ᵥ probeRight)
        + (rightVec ⬝ᵥ probeLeft) * (leftVec ⬝ᵥ probeRight) := by
  simp only [symmetricOuterPair, Matrix.add_mulVec, dotProduct_add,
    vecMulVec_mulVec_eq_dotProduct_smul, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm probeLeft leftVec, dotProduct_comm probeLeft rightVec]
  ring

/-- The quadratic reading: twice the product of the two projections. -/
theorem dotProduct_symmetricOuterPair_mulVec (leftVec rightVec probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ (symmetricOuterPair leftVec rightVec *ᵥ probeVec)
      = 2 * ((leftVec ⬝ᵥ probeVec) * (rightVec ⬝ᵥ probeVec)) := by
  rw [dotProduct_symmetricOuterPair_mulVec_pair]
  ring

/-- The same reading with the probe on the left of both pairings, which is the
slot order polarised Parseval hands over. -/
theorem dotProduct_symmetricOuterPair_mulVec_probeLeft
    (leftVec rightVec probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ (symmetricOuterPair leftVec rightVec *ᵥ probeVec)
      = 2 * ((probeVec ⬝ᵥ leftVec) * (probeVec ⬝ᵥ rightVec)) := by
  rw [dotProduct_symmetricOuterPair_mulVec, dotProduct_comm probeVec leftVec,
    dotProduct_comm probeVec rightVec]

/-! ## Part A.2.  Three rows with a nontrivial dependence share an orthogonal vector -/

/-- Expanding a three-entry row against a probe WITHOUT touching whatever the
entries themselves are built from.  Unfolding `dotProduct` globally would also
shred the pairings sitting inside the entries and leave the two sides of a
`linear_combination` at different depths. -/
theorem consThree_dotProduct (entryFirst entrySecond entryThird : ℝ)
    (probeVec : Fin 3 → ℝ) :
    (![entryFirst, entrySecond, entryThird] : Fin 3 → ℝ) ⬝ᵥ probeVec
      = entryFirst * probeVec 0 + entrySecond * probeVec 1 + entryThird * probeVec 2 := by
  simp [dotProduct, Fin.sum_univ_three]

/-- **Three vectors of `R^3` carrying a nontrivial linear dependence share a
common nonzero orthogonal vector.**  Stated with the dependence coefficients
explicit so a positive weight triple can be handed straight in.  This is the only
place a determinant is used, and it is used only to produce a kernel vector. -/
theorem exists_orthogonal_of_dependent_rows
    (rowFirst rowSecond rowThird : Fin 3 → ℝ)
    (coeffFirst coeffSecond coeffThird : ℝ) (hcoeffFirstNe : coeffFirst ≠ 0)
    (hdependence : ∀ coordIndex : Fin 3,
      coeffFirst * rowFirst coordIndex + coeffSecond * rowSecond coordIndex
        + coeffThird * rowThird coordIndex = 0) :
    ∃ normalVec : Fin 3 → ℝ, normalVec ≠ 0 ∧ rowFirst ⬝ᵥ normalVec = 0 ∧
      rowSecond ⬝ᵥ normalVec = 0 ∧ rowThird ⬝ᵥ normalVec = 0 := by
  classical
  set rowMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun rowIndex colIndex => (![rowFirst, rowSecond, rowThird] rowIndex) colIndex
    with hrowMatrix
  have hdeterminantZero : rowMatrix.det = 0 := by
    refine Matrix.exists_vecMul_eq_zero_iff.mp
      ⟨![coeffFirst, coeffSecond, coeffThird], ?_, ?_⟩
    · intro hzero
      have hentry : (![coeffFirst, coeffSecond, coeffThird] : Fin 3 → ℝ) 0 = 0 := by
        rw [hzero]; rfl
      simp only [Matrix.cons_val_zero] at hentry
      exact hcoeffFirstNe hentry
    · funext colIndex
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, hrowMatrix, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, Pi.zero_apply]
      exact hdependence colIndex
  obtain ⟨normalVec, hnormalNe, hnormalKernel⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdeterminantZero
  have hrowKernel : ∀ rowIndex : Fin 3,
      (![rowFirst, rowSecond, rowThird] rowIndex) ⬝ᵥ normalVec = 0 := by
    intro rowIndex
    have hentry := congrFun hnormalKernel rowIndex
    simpa [Matrix.mulVec, hrowMatrix, dotProduct] using hentry
  exact ⟨normalVec, hnormalNe, by simpa using hrowKernel 0, by simpa using hrowKernel 1,
    by simpa using hrowKernel 2⟩

/-! ## Part A.3.  An orthogonal triple forces a common conic -/

/-- The conic attached to an orthogonal base triple and three coefficients: a
combination of the three symmetric outer products of DISTINCT base atoms.  Every
base atom satisfies it outright, because orthogonality kills each term. -/
def orthogonalTripleConic (baseFirstVec baseSecondVec baseThirdVec : Fin 3 → ℝ)
    (coeff : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  coeff 0 • symmetricOuterPair baseFirstVec baseSecondVec
    + coeff 1 • symmetricOuterPair baseFirstVec baseThirdVec
    + coeff 2 • symmetricOuterPair baseSecondVec baseThirdVec

theorem transpose_orthogonalTripleConic (baseFirstVec baseSecondVec baseThirdVec : Fin 3 → ℝ)
    (coeff : Fin 3 → ℝ) :
    (orthogonalTripleConic baseFirstVec baseSecondVec baseThirdVec coeff)ᵀ
      = orthogonalTripleConic baseFirstVec baseSecondVec baseThirdVec coeff := by
  simp only [orthogonalTripleConic, Matrix.transpose_add, Matrix.transpose_smul,
    transpose_symmetricOuterPair]

/-- Its quadratic form at a probe is twice the pairing of the coefficient vector
against the probe's three pair readings. -/
theorem dotProduct_orthogonalTripleConic_mulVec
    (baseFirstVec baseSecondVec baseThirdVec probeVec : Fin 3 → ℝ) (coeff : Fin 3 → ℝ) :
    probeVec ⬝ᵥ (orthogonalTripleConic baseFirstVec baseSecondVec baseThirdVec coeff *ᵥ probeVec)
      = 2 * (coeff 0 * ((probeVec ⬝ᵥ baseFirstVec) * (probeVec ⬝ᵥ baseSecondVec))
          + coeff 1 * ((probeVec ⬝ᵥ baseFirstVec) * (probeVec ⬝ᵥ baseThirdVec))
          + coeff 2 * ((probeVec ⬝ᵥ baseSecondVec) * (probeVec ⬝ᵥ baseThirdVec))) := by
  simp only [orthogonalTripleConic, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, dotProduct_symmetricOuterPair_mulVec_probeLeft]
  ring

/-- Its bilinear form on two DISTINCT base atoms isolates one coefficient. -/
theorem dotProduct_orthogonalTripleConic_mulVec_pair
    (baseFirstVec baseSecondVec baseThirdVec probeLeft probeRight : Fin 3 → ℝ)
    (coeff : Fin 3 → ℝ) :
    probeLeft ⬝ᵥ (orthogonalTripleConic baseFirstVec baseSecondVec baseThirdVec coeff
        *ᵥ probeRight)
      = coeff 0 * ((baseFirstVec ⬝ᵥ probeLeft) * (baseSecondVec ⬝ᵥ probeRight)
            + (baseSecondVec ⬝ᵥ probeLeft) * (baseFirstVec ⬝ᵥ probeRight))
        + coeff 1 * ((baseFirstVec ⬝ᵥ probeLeft) * (baseThirdVec ⬝ᵥ probeRight)
            + (baseThirdVec ⬝ᵥ probeLeft) * (baseFirstVec ⬝ᵥ probeRight))
        + coeff 2 * ((baseSecondVec ⬝ᵥ probeLeft) * (baseThirdVec ⬝ᵥ probeRight)
            + (baseThirdVec ⬝ᵥ probeLeft) * (baseSecondVec ⬝ᵥ probeRight)) := by
  simp only [orthogonalTripleConic, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, dotProduct_symmetricOuterPair_mulVec_pair]

/-- **AN ORTHOGONAL TRIPLE FORCES A COMMON CONIC.**  No `(6,3)` design with three
pairwise orthogonal nonzero atoms is off-conic.

The conic is explicit and needs no normalisation: it is a combination of the three
symmetric outer products of distinct base atoms, whose coefficient vector is any
kernel vector of the `3x3` matrix of the free labels' base-pair readings.  That
matrix is singular because polarised Parseval against a base pair says the
POSITIVE free weight vector annihilates it from the left -- the base atoms
contribute nothing to those three moments, again by orthogonality. -/
theorem not_hasNoCommonQuadric_of_orthogonalTriple (design : WeightedDesign 6 3)
    {baseFirst baseSecond baseThird : Fin 6}
    (hfirstSecond : baseFirst ≠ baseSecond) (hfirstThird : baseFirst ≠ baseThird)
    (hsecondThird : baseSecond ≠ baseThird)
    (hfirstNonzero : design.atom baseFirst ≠ 0)
    (hsecondNonzero : design.atom baseSecond ≠ 0)
    (hthirdNonzero : design.atom baseThird ≠ 0)
    (horthFirstSecond : design.atom baseFirst ⬝ᵥ design.atom baseSecond = 0)
    (horthFirstThird : design.atom baseFirst ⬝ᵥ design.atom baseThird = 0)
    (horthSecondThird : design.atom baseSecond ⬝ᵥ design.atom baseThird = 0) :
    ¬ HasNoCommonQuadric design.atom := by
  classical
  intro hnoConic
  have horthSecondFirst : design.atom baseSecond ⬝ᵥ design.atom baseFirst = 0 := by
    rw [dotProduct_comm]; exact horthFirstSecond
  have horthThirdFirst : design.atom baseThird ⬝ᵥ design.atom baseFirst = 0 := by
    rw [dotProduct_comm]; exact horthFirstThird
  have horthThirdSecond : design.atom baseThird ⬝ᵥ design.atom baseSecond = 0 := by
    rw [dotProduct_comm]; exact horthSecondThird
  set baseSet : Finset (Fin 6) := {baseFirst, baseSecond, baseThird} with hbaseSet
  have hbaseCard : baseSet.card = 3 := by
    rw [hbaseSet, Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
      Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]
  have hcomplCard : baseSetᶜ.card = 3 := by
    rw [Finset.card_compl, hbaseCard]
    rfl
  obtain ⟨freeFirst, freeSecond, freeThird, hfreeFirstSecond, hfreeFirstThird,
    hfreeSecondThird, hcomplEq⟩ := Finset.card_eq_three.mp hcomplCard
  -- The three mixed moments over the complement vanish.
  have hmixedMoment : ∀ leftLabel rightLabel : Fin 6,
      design.atom leftLabel ⬝ᵥ design.atom rightLabel = 0 →
      (∀ baseLabel ∈ baseSet, (design.atom baseLabel ⬝ᵥ design.atom leftLabel)
          * (design.atom baseLabel ⬝ᵥ design.atom rightLabel) = 0) →
      design.weight freeFirst * ((design.atom freeFirst ⬝ᵥ design.atom leftLabel)
            * (design.atom freeFirst ⬝ᵥ design.atom rightLabel))
        + design.weight freeSecond * ((design.atom freeSecond ⬝ᵥ design.atom leftLabel)
            * (design.atom freeSecond ⬝ᵥ design.atom rightLabel))
        + design.weight freeThird * ((design.atom freeThird ⬝ᵥ design.atom leftLabel)
            * (design.atom freeThird ⬝ᵥ design.atom rightLabel)) = 0 := by
    intro leftLabel rightLabel horthogonal hbaseVanishes
    have hpolar := dotProduct_eq_sum_weight_mul_pair design (design.atom leftLabel)
      (design.atom rightLabel)
    rw [horthogonal, ← Finset.sum_add_sum_compl baseSet] at hpolar
    have hbaseSum : (∑ baseLabel ∈ baseSet, design.weight baseLabel
        * ((design.atom baseLabel ⬝ᵥ design.atom leftLabel)
          * (design.atom baseLabel ⬝ᵥ design.atom rightLabel))) = 0 :=
      Finset.sum_eq_zero fun baseLabel hmem => by
        rw [hbaseVanishes baseLabel hmem, mul_zero]
    rw [hbaseSum, zero_add, hcomplEq, Finset.sum_insert (by simp [hfreeFirstSecond,
      hfreeFirstThird]), Finset.sum_insert (by simp [hfreeSecondThird]),
      Finset.sum_singleton] at hpolar
    linarith
  have hmomentFirstSecond := hmixedMoment baseFirst baseSecond horthFirstSecond (by
    intro baseLabel hmem
    rw [hbaseSet] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [horthFirstSecond, mul_zero]
    · rw [horthSecondFirst, zero_mul]
    · rw [horthThirdFirst, zero_mul])
  have hmomentFirstThird := hmixedMoment baseFirst baseThird horthFirstThird (by
    intro baseLabel hmem
    rw [hbaseSet] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [horthFirstThird, mul_zero]
    · rw [horthSecondFirst, zero_mul]
    · rw [horthThirdFirst, zero_mul])
  have hmomentSecondThird := hmixedMoment baseSecond baseThird horthSecondThird (by
    intro baseLabel hmem
    rw [hbaseSet] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · rw [horthFirstSecond, zero_mul]
    · rw [horthSecondThird, mul_zero]
    · rw [horthThirdSecond, zero_mul])
  -- The free labels' reading rows carry a positive dependence, hence a common normal.
  obtain ⟨coeff, hcoeffNe, hkernelFirst, hkernelSecond, hkernelThird⟩ :=
    exists_orthogonal_of_dependent_rows
      ![(design.atom freeFirst ⬝ᵥ design.atom baseFirst)
          * (design.atom freeFirst ⬝ᵥ design.atom baseSecond),
        (design.atom freeFirst ⬝ᵥ design.atom baseFirst)
          * (design.atom freeFirst ⬝ᵥ design.atom baseThird),
        (design.atom freeFirst ⬝ᵥ design.atom baseSecond)
          * (design.atom freeFirst ⬝ᵥ design.atom baseThird)]
      ![(design.atom freeSecond ⬝ᵥ design.atom baseFirst)
          * (design.atom freeSecond ⬝ᵥ design.atom baseSecond),
        (design.atom freeSecond ⬝ᵥ design.atom baseFirst)
          * (design.atom freeSecond ⬝ᵥ design.atom baseThird),
        (design.atom freeSecond ⬝ᵥ design.atom baseSecond)
          * (design.atom freeSecond ⬝ᵥ design.atom baseThird)]
      ![(design.atom freeThird ⬝ᵥ design.atom baseFirst)
          * (design.atom freeThird ⬝ᵥ design.atom baseSecond),
        (design.atom freeThird ⬝ᵥ design.atom baseFirst)
          * (design.atom freeThird ⬝ᵥ design.atom baseThird),
        (design.atom freeThird ⬝ᵥ design.atom baseSecond)
          * (design.atom freeThird ⬝ᵥ design.atom baseThird)]
      (design.weight freeFirst) (design.weight freeSecond) (design.weight freeThird)
      (ne_of_gt (design.weight_pos freeFirst))
      (by
        intro coordIndex
        fin_cases coordIndex
        · simpa using hmomentFirstSecond
        · simpa using hmomentFirstThird
        · simpa using hmomentSecondThird)
  -- Assemble the conic and check it kills every atom.
  set conicForm := orthogonalTripleConic (design.atom baseFirst) (design.atom baseSecond)
    (design.atom baseThird) coeff with hconicForm
  have hkillsBase : ∀ baseLabel ∈ baseSet,
      design.atom baseLabel ⬝ᵥ (conicForm *ᵥ design.atom baseLabel) = 0 := by
    intro baseLabel hmem
    rw [hbaseSet] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rw [hconicForm, dotProduct_orthogonalTripleConic_mulVec]
    rcases hmem with rfl | rfl | rfl
    · rw [horthFirstSecond, horthFirstThird]; ring
    · rw [horthSecondFirst, horthSecondThird]; ring
    · rw [horthThirdFirst, horthThirdSecond]; ring
  have hkillsFree : ∀ freeLabel : Fin 6, freeLabel ∈ baseSetᶜ →
      design.atom freeLabel ⬝ᵥ (conicForm *ᵥ design.atom freeLabel) = 0 := by
    intro freeLabel hmem
    rw [hcomplEq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rw [hconicForm, dotProduct_orthogonalTripleConic_mulVec]
    rcases hmem with rfl | rfl | rfl
    · have hrow : coeff 0 * ((design.atom freeLabel ⬝ᵥ design.atom baseFirst)
            * (design.atom freeLabel ⬝ᵥ design.atom baseSecond))
          + coeff 1 * ((design.atom freeLabel ⬝ᵥ design.atom baseFirst)
            * (design.atom freeLabel ⬝ᵥ design.atom baseThird))
          + coeff 2 * ((design.atom freeLabel ⬝ᵥ design.atom baseSecond)
            * (design.atom freeLabel ⬝ᵥ design.atom baseThird)) = 0 := by
        have hexpand := hkernelFirst
        rw [consThree_dotProduct] at hexpand
        linear_combination hexpand
      rw [hrow]; ring
    · have hrow : coeff 0 * ((design.atom freeLabel ⬝ᵥ design.atom baseFirst)
            * (design.atom freeLabel ⬝ᵥ design.atom baseSecond))
          + coeff 1 * ((design.atom freeLabel ⬝ᵥ design.atom baseFirst)
            * (design.atom freeLabel ⬝ᵥ design.atom baseThird))
          + coeff 2 * ((design.atom freeLabel ⬝ᵥ design.atom baseSecond)
            * (design.atom freeLabel ⬝ᵥ design.atom baseThird)) = 0 := by
        have hexpand := hkernelSecond
        rw [consThree_dotProduct] at hexpand
        linear_combination hexpand
      rw [hrow]; ring
    · have hrow : coeff 0 * ((design.atom freeLabel ⬝ᵥ design.atom baseFirst)
            * (design.atom freeLabel ⬝ᵥ design.atom baseSecond))
          + coeff 1 * ((design.atom freeLabel ⬝ᵥ design.atom baseFirst)
            * (design.atom freeLabel ⬝ᵥ design.atom baseThird))
          + coeff 2 * ((design.atom freeLabel ⬝ᵥ design.atom baseSecond)
            * (design.atom freeLabel ⬝ᵥ design.atom baseThird)) = 0 := by
        have hexpand := hkernelThird
        rw [consThree_dotProduct] at hexpand
        linear_combination hexpand
      rw [hrow]; ring
  have hconicZero : conicForm = 0 := by
    refine hnoConic conicForm (by rw [hconicForm]; exact transpose_orthogonalTripleConic _ _ _ _)
      fun atomIndex => ?_
    by_cases hmem : atomIndex ∈ baseSet
    · exact hkillsBase atomIndex hmem
    · exact hkillsFree atomIndex (Finset.mem_compl.mpr hmem)
  -- But the conic is nonzero: it isolates one coefficient on each base pair.
  have hleverageFirst : 0 < design.atom baseFirst ⬝ᵥ design.atom baseFirst :=
    dotProduct_self_pos hfirstNonzero
  have hleverageSecond : 0 < design.atom baseSecond ⬝ᵥ design.atom baseSecond :=
    dotProduct_self_pos hsecondNonzero
  have hleverageThird : 0 < design.atom baseThird ⬝ᵥ design.atom baseThird :=
    dotProduct_self_pos hthirdNonzero
  have hpairFirstSecond : design.atom baseFirst ⬝ᵥ (conicForm *ᵥ design.atom baseSecond)
      = coeff 0 * ((design.atom baseFirst ⬝ᵥ design.atom baseFirst)
        * (design.atom baseSecond ⬝ᵥ design.atom baseSecond)) := by
    rw [hconicForm, dotProduct_orthogonalTripleConic_mulVec_pair, horthFirstSecond,
      horthSecondFirst, horthThirdFirst, horthThirdSecond]
    ring
  have hpairFirstThird : design.atom baseFirst ⬝ᵥ (conicForm *ᵥ design.atom baseThird)
      = coeff 1 * ((design.atom baseFirst ⬝ᵥ design.atom baseFirst)
        * (design.atom baseThird ⬝ᵥ design.atom baseThird)) := by
    rw [hconicForm, dotProduct_orthogonalTripleConic_mulVec_pair, horthFirstThird,
      horthSecondFirst, horthSecondThird, horthThirdFirst]
    ring
  have hpairSecondThird : design.atom baseSecond ⬝ᵥ (conicForm *ᵥ design.atom baseThird)
      = coeff 2 * ((design.atom baseSecond ⬝ᵥ design.atom baseSecond)
        * (design.atom baseThird ⬝ᵥ design.atom baseThird)) := by
    rw [hconicForm, dotProduct_orthogonalTripleConic_mulVec_pair, horthFirstSecond,
      horthFirstThird, horthSecondThird, horthThirdSecond]
    ring
  have hvanishAt : ∀ probeLeft probeRight : Fin 3 → ℝ,
      probeLeft ⬝ᵥ (conicForm *ᵥ probeRight) = 0 := by
    intro probeLeft probeRight
    rw [hconicZero, Matrix.zero_mulVec, dotProduct_zero]
  have hcoeffZeroFirst : coeff 0 = 0 := by
    have hvalue := hvanishAt (design.atom baseFirst) (design.atom baseSecond)
    rw [hpairFirstSecond] at hvalue
    rcases mul_eq_zero.mp hvalue with hzero | hproduct
    · exact hzero
    · exact absurd hproduct (ne_of_gt (mul_pos hleverageFirst hleverageSecond))
  have hcoeffZeroSecond : coeff 1 = 0 := by
    have hvalue := hvanishAt (design.atom baseFirst) (design.atom baseThird)
    rw [hpairFirstThird] at hvalue
    rcases mul_eq_zero.mp hvalue with hzero | hproduct
    · exact hzero
    · exact absurd hproduct (ne_of_gt (mul_pos hleverageFirst hleverageThird))
  have hcoeffZeroThird : coeff 2 = 0 := by
    have hvalue := hvanishAt (design.atom baseSecond) (design.atom baseThird)
    rw [hpairSecondThird] at hvalue
    rcases mul_eq_zero.mp hvalue with hzero | hproduct
    · exact hzero
    · exact absurd hproduct (ne_of_gt (mul_pos hleverageSecond hleverageThird))
  exact hcoeffNe
    (eq_zero_of_coordinates_eq_zero hcoeffZeroFirst hcoeffZeroSecond hcoeffZeroThird)

/-- **On the off-conic stratum no three atoms are mutually orthogonal.**  The
contrapositive reading, and the campaign-relevant one: a heavy orthogonal triple
dominates for free by `Gtz.dominates_of_orthogonalTriple_of_one_le`, so the one
cheap source of dominators is exactly what off-conicity removes. -/
theorem not_orthogonalTriple_of_hasNoCommonQuadric (design : WeightedDesign 6 3)
    (hoffConic : HasNoCommonQuadric design.atom)
    {baseFirst baseSecond baseThird : Fin 6}
    (hfirstSecond : baseFirst ≠ baseSecond) (hfirstThird : baseFirst ≠ baseThird)
    (hsecondThird : baseSecond ≠ baseThird)
    (hfirstNonzero : design.atom baseFirst ≠ 0)
    (hsecondNonzero : design.atom baseSecond ≠ 0)
    (hthirdNonzero : design.atom baseThird ≠ 0) :
    ¬ (design.atom baseFirst ⬝ᵥ design.atom baseSecond = 0 ∧
       design.atom baseFirst ⬝ᵥ design.atom baseThird = 0 ∧
       design.atom baseSecond ⬝ᵥ design.atom baseThird = 0) := by
  rintro ⟨horthFirstSecond, horthFirstThird, horthSecondThird⟩
  exact not_hasNoCommonQuadric_of_orthogonalTriple design hfirstSecond hfirstThird hsecondThird
    hfirstNonzero hsecondNonzero hthirdNonzero horthFirstSecond horthFirstThird
    horthSecondThird hoffConic

/-! ## Part A.4.  A triple's gap vanishes exactly on an orthonormal basis -/

/-- The unweighted atom sum of three distinct labels, entrywise. -/
theorem subsetSum_tripleSet_apply (design : WeightedDesign 6 3)
    {baseFirst baseSecond baseThird : Fin 6}
    (hfirstSecond : baseFirst ≠ baseSecond) (hfirstThird : baseFirst ≠ baseThird)
    (hsecondThird : baseSecond ≠ baseThird) (rowIndex colIndex : Fin 3) :
    subsetSum design {baseFirst, baseSecond, baseThird} rowIndex colIndex
      = design.atom baseFirst rowIndex * design.atom baseFirst colIndex
        + design.atom baseSecond rowIndex * design.atom baseSecond colIndex
        + design.atom baseThird rowIndex * design.atom baseThird colIndex := by
  rw [subsetSum, Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton]
  simp only [Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply]
  ring

/-- **A TRIPLE'S GAP IS THE ZERO FORM EXACTLY ON AN ORTHONORMAL BASIS.**  Three
atoms whose unweighted sum of rank-one projectors is the identity are pairwise
orthogonal AND of unit leverage: the matrix carrying them as columns satisfies
`U Uᵀ = 1`, hence `Uᵀ U = 1`, and the entries of `Uᵀ U` are exactly the pairings. -/
theorem orthonormalTriple_of_subsetSum_eq_one (design : WeightedDesign 6 3)
    {baseFirst baseSecond baseThird : Fin 6}
    (hfirstSecond : baseFirst ≠ baseSecond) (hfirstThird : baseFirst ≠ baseThird)
    (hsecondThird : baseSecond ≠ baseThird)
    (hsumEqOne : subsetSum design {baseFirst, baseSecond, baseThird} = 1) :
    design.atom baseFirst ⬝ᵥ design.atom baseSecond = 0 ∧
      design.atom baseFirst ⬝ᵥ design.atom baseThird = 0 ∧
      design.atom baseSecond ⬝ᵥ design.atom baseThird = 0 ∧
      design.atom baseFirst ⬝ᵥ design.atom baseFirst = 1 ∧
      design.atom baseSecond ⬝ᵥ design.atom baseSecond = 1 ∧
      design.atom baseThird ⬝ᵥ design.atom baseThird = 1 := by
  classical
  set baseColumn : Fin 3 → (Fin 3 → ℝ) :=
    ![design.atom baseFirst, design.atom baseSecond, design.atom baseThird] with hbaseColumn
  set frameMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun rowIndex colIndex => baseColumn colIndex rowIndex with hframeMatrix
  have hframeProduct : frameMatrix * frameMatrixᵀ = 1 := by
    ext rowIndex colIndex
    rw [← hsumEqOne, subsetSum_tripleSet_apply design hfirstSecond hfirstThird hsecondThird]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hframeMatrix, Matrix.of_apply,
      Fin.sum_univ_three, hbaseColumn, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  have hframeSwapped : frameMatrixᵀ * frameMatrix = 1 := mul_eq_one_comm.mp hframeProduct
  have hpairing : ∀ leftIndex rightIndex : Fin 3,
      baseColumn leftIndex ⬝ᵥ baseColumn rightIndex
        = (1 : Matrix (Fin 3) (Fin 3) ℝ) leftIndex rightIndex := by
    intro leftIndex rightIndex
    rw [← hframeSwapped]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hframeMatrix, Matrix.of_apply,
      dotProduct]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hbaseColumn, Matrix.one_apply] using hpairing 0 1
  · simpa [hbaseColumn, Matrix.one_apply] using hpairing 0 2
  · simpa [hbaseColumn, Matrix.one_apply] using hpairing 1 2
  · simpa [hbaseColumn, Matrix.one_apply] using hpairing 0 0
  · simpa [hbaseColumn, Matrix.one_apply] using hpairing 1 1
  · simpa [hbaseColumn, Matrix.one_apply] using hpairing 2 2

/-- The converse: an orthonormal triple's unweighted projector sum IS the
identity, so the gap is the zero form. -/
theorem subsetSum_eq_one_of_orthonormalTriple (design : WeightedDesign 6 3)
    {baseFirst baseSecond baseThird : Fin 6}
    (hfirstSecond : baseFirst ≠ baseSecond) (hfirstThird : baseFirst ≠ baseThird)
    (hsecondThird : baseSecond ≠ baseThird)
    (horthFirstSecond : design.atom baseFirst ⬝ᵥ design.atom baseSecond = 0)
    (horthFirstThird : design.atom baseFirst ⬝ᵥ design.atom baseThird = 0)
    (horthSecondThird : design.atom baseSecond ⬝ᵥ design.atom baseThird = 0)
    (hunitFirst : design.atom baseFirst ⬝ᵥ design.atom baseFirst = 1)
    (hunitSecond : design.atom baseSecond ⬝ᵥ design.atom baseSecond = 1)
    (hunitThird : design.atom baseThird ⬝ᵥ design.atom baseThird = 1) :
    subsetSum design {baseFirst, baseSecond, baseThird} = 1 := by
  classical
  have horthSecondFirst : design.atom baseSecond ⬝ᵥ design.atom baseFirst = 0 := by
    rw [dotProduct_comm]; exact horthFirstSecond
  have horthThirdFirst : design.atom baseThird ⬝ᵥ design.atom baseFirst = 0 := by
    rw [dotProduct_comm]; exact horthFirstThird
  have horthThirdSecond : design.atom baseThird ⬝ᵥ design.atom baseSecond = 0 := by
    rw [dotProduct_comm]; exact horthSecondThird
  set baseColumn : Fin 3 → (Fin 3 → ℝ) :=
    ![design.atom baseFirst, design.atom baseSecond, design.atom baseThird] with hbaseColumn
  set frameMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun rowIndex colIndex => baseColumn colIndex rowIndex with hframeMatrix
  have hframeSwapped : frameMatrixᵀ * frameMatrix = 1 := by
    ext leftIndex rightIndex
    have hpairing : (frameMatrixᵀ * frameMatrix) leftIndex rightIndex
        = baseColumn leftIndex ⬝ᵥ baseColumn rightIndex := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hframeMatrix, Matrix.of_apply,
        dotProduct]
    rw [hpairing]
    fin_cases leftIndex <;> fin_cases rightIndex
    · simpa [hbaseColumn] using hunitFirst
    · simpa [hbaseColumn] using horthFirstSecond
    · simpa [hbaseColumn] using horthFirstThird
    · simpa [hbaseColumn] using horthSecondFirst
    · simpa [hbaseColumn] using hunitSecond
    · simpa [hbaseColumn] using horthSecondThird
    · simpa [hbaseColumn] using horthThirdFirst
    · simpa [hbaseColumn] using horthThirdSecond
    · simpa [hbaseColumn] using hunitThird
  have hframeProduct : frameMatrix * frameMatrixᵀ = 1 := mul_eq_one_comm.mp hframeSwapped
  ext rowIndex colIndex
  rw [subsetSum_tripleSet_apply design hfirstSecond hfirstThird hsecondThird, ← hframeProduct]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hframeMatrix, Matrix.of_apply,
    Fin.sum_univ_three, hbaseColumn, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- The two halves as one equivalence: a triple's gap is the zero form exactly on
an orthonormal basis. -/
theorem subsetSum_eq_one_iff_orthonormalTriple (design : WeightedDesign 6 3)
    {baseFirst baseSecond baseThird : Fin 6}
    (hfirstSecond : baseFirst ≠ baseSecond) (hfirstThird : baseFirst ≠ baseThird)
    (hsecondThird : baseSecond ≠ baseThird) :
    subsetSum design {baseFirst, baseSecond, baseThird} = 1
      ↔ (design.atom baseFirst ⬝ᵥ design.atom baseSecond = 0 ∧
          design.atom baseFirst ⬝ᵥ design.atom baseThird = 0 ∧
          design.atom baseSecond ⬝ᵥ design.atom baseThird = 0 ∧
          design.atom baseFirst ⬝ᵥ design.atom baseFirst = 1 ∧
          design.atom baseSecond ⬝ᵥ design.atom baseSecond = 1 ∧
          design.atom baseThird ⬝ᵥ design.atom baseThird = 1) := by
  refine ⟨orthonormalTriple_of_subsetSum_eq_one design hfirstSecond hfirstThird hsecondThird,
    fun horthonormal => ?_⟩
  obtain ⟨horthFirstSecond, horthFirstThird, horthSecondThird, hunitFirst, hunitSecond,
    hunitThird⟩ := horthonormal
  exact subsetSum_eq_one_of_orthonormalTriple design hfirstSecond hfirstThird hsecondThird
    horthFirstSecond horthFirstThird horthSecondThird hunitFirst hunitSecond hunitThird

/-- **ON THE OFF-CONIC STRATUM NO TRIPLE HAS A VANISHING GAP.**  Combining the two
halves of Part A: a zero gap forces an orthonormal base triple, an orthonormal
base triple is three mutually orthogonal nonzero atoms, and those force a conic.

Read against `Gtz.BaseTripleTightLineFreeOffConicWeakToStrict`: on that
obligation's antecedent region the base gap is positive semidefinite (it
dominates), singular (a nonzero tight direction kills it) and NEVER ZERO.  Its
rank is one or two, so the tight direction spans a proper subspace and the
obligation always has a genuine two-dimensional or one-dimensional positive part
to work with. -/
theorem subsetSum_sub_one_ne_zero_of_hasNoCommonQuadric (design : WeightedDesign 6 3)
    (hoffConic : HasNoCommonQuadric design.atom)
    {baseFirst baseSecond baseThird : Fin 6}
    (hfirstSecond : baseFirst ≠ baseSecond) (hfirstThird : baseFirst ≠ baseThird)
    (hsecondThird : baseSecond ≠ baseThird) :
    subsetSum design {baseFirst, baseSecond, baseThird} - 1 ≠ 0 := by
  intro hgapZero
  have hsumEqOne : subsetSum design {baseFirst, baseSecond, baseThird} = 1 :=
    sub_eq_zero.mp hgapZero
  obtain ⟨horthFirstSecond, horthFirstThird, horthSecondThird, hunitFirst, hunitSecond,
    hunitThird⟩ :=
    orthonormalTriple_of_subsetSum_eq_one design hfirstSecond hfirstThird hsecondThird hsumEqOne
  have hfirstNonzero : design.atom baseFirst ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunitFirst
    exact zero_ne_one hunitFirst
  have hsecondNonzero : design.atom baseSecond ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunitSecond
    exact zero_ne_one hunitSecond
  have hthirdNonzero : design.atom baseThird ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunitThird
    exact zero_ne_one hunitThird
  exact not_orthogonalTriple_of_hasNoCommonQuadric design hoffConic hfirstSecond hfirstThird
    hsecondThird hfirstNonzero hsecondNonzero hthirdNonzero
    ⟨horthFirstSecond, horthFirstThird, horthSecondThird⟩

/-- **THE `U(3,6)` BASE GAP IS A NONZERO SINGULAR POSITIVE SEMIDEFINITE FORM.**
Packaged in exactly the antecedent shape of
`Gtz.BaseTripleTightLineFreeOffConicWeakToStrict`: off-conicity plus the weak
dominance of `{0,1,2}` plus one nonzero tight direction give a gap that is
positive semidefinite, annihilates the tight direction, and is NOT the zero
matrix.  Off-conicity is what supplies the last conjunct, and nothing else in the
campaign spends it. -/
theorem baseTripleGap_psd_singular_ne_zero_of_offConic (design : WeightedDesign 6 3)
    (hoffConic : HasNoCommonQuadric design.atom)
    (hdominates : Dominates design {0, 1, 2})
    {tightDir : Fin 3 → ℝ}
    (htight : tightDir ⬝ᵥ ((subsetSum design {0, 1, 2} - 1) *ᵥ tightDir) = 0) :
    (subsetSum design {0, 1, 2} - 1).PosSemidef ∧
      (subsetSum design {0, 1, 2} - 1) *ᵥ tightDir = 0 ∧
      subsetSum design {0, 1, 2} - 1 ≠ 0 := by
  refine ⟨hdominates, ?_, subsetSum_sub_one_ne_zero_of_hasNoCommonQuadric design hoffConic
    (by decide) (by decide) (by decide)⟩
  refine (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hdominates tightDir).mp ?_
  rw [star_trivial]
  exact htight

/-! ## Part B.  The two-meeting-lines canonical triples can both fail

The stratum is `Gtz.lineFamilyPattern [[0,1,2], [0,3,4]]`: two three-point lines
meeting at label `0`, with label `5` off both and every unlisted triple
independent.  The two nominated triples are the line complements, `{3,4,5}` and
`{1,2,5}`.
-/

/-- Two three-point lines meeting at label `0`, atom `5` off both.  All entries
are integers. -/
def twinFailureAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![0, 1, -1]
  | 1 => ![1, 0, -1]
  | 2 => ![1, -1, 0]
  | 3 => ![-2, -1, -2]
  | 4 => ![-2, -2, -1]
  | 5 => ![1, -1, -2]

/-- Exact ninetieths, written in lowest terms. -/
noncomputable def twinFailureWeight : Fin 6 → ℝ
  | 0 => 1 / 3
  | 1 => 1 / 5
  | 2 => 3 / 10
  | 3 => 2 / 45
  | 4 => 1 / 15
  | 5 => 1 / 18

/-- **The refuting two-meeting-lines design.**  Parseval holds exactly. -/
noncomputable def twinFailureDesign : WeightedDesign 6 3 where
  atom := twinFailureAtom
  weight := twinFailureWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [twinFailureWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [twinFailureWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [twinFailureAtom, twinFailureWeight, atomMatrix] <;> norm_num

/-- The design sits on the two-meeting-lines stratum: `{0,1,2}` and `{0,3,4}` are
its ONLY dependent triples. -/
theorem twinFailureDesign_hasLinePattern :
    HasLinePattern twinFailureDesign
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, twinFailureDesign,
            twinFailureAtom, Matrix.cons_val_two])
          (by decide)
      | exact iff_of_true
          (by norm_num [atomBracket, tripleBracket_eq, twinFailureDesign,
            twinFailureAtom, Matrix.cons_val_two])
          (by decide)

/-- Every atom is heavy: the leverages are `2, 2, 2, 9, 9, 6`. -/
theorem twinFailureDesign_allHeavy (label : Fin 6) :
    1 ≤ leverageOf (twinFailureDesign.atom label) := by
  fin_cases label <;>
    norm_num [leverageOf, Fin.sum_univ_three, twinFailureDesign, twinFailureAtom,
      Matrix.cons_val_two]

/-! ### The winning mixed triple `{2,4,5}` -/

/-- The gap of `{2,4,5}` as an explicit sum of three squares.  The coefficients
`5`, `21/5`, `4/21` multiply out to the determinant `4`. -/
theorem twinFailure_dominatorGap_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ ((subsetSum twinFailureDesign {2, 4, 5} - 1) *ᵥ probeVec)
      = 5 * (probeVec 0 + 2 / 5 * probeVec 1) ^ 2
        + 21 / 5 * (probeVec 1 + 20 / 21 * probeVec 2) ^ 2
        + 4 / 21 * probeVec 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [twinFailureDesign, twinFailureAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

/-- `{2,4,5}` is STRICTLY dominating, so the obligation's conclusion holds on the
refuting design. -/
theorem twinFailure_mixedTripleGap_posDef :
    (subsetSum twinFailureDesign {2, 4, 5} - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one twinFailureDesign _),
      fun probeVec hprobeNe => ?_⟩
  rw [star_trivial, twinFailure_dominatorGap_form]
  by_contra hnonpos
  push Not at hnonpos
  have hfirstSq := sq_nonneg (probeVec 0 + 2 / 5 * probeVec 1)
  have hsecondSq := sq_nonneg (probeVec 1 + 20 / 21 * probeVec 2)
  have hthirdSq := sq_nonneg (probeVec 2)
  have hthirdZero : probeVec 2 = 0 := sq_eq_zero_iff.mp (by linarith)
  have hsecondZero : probeVec 1 = 0 := by
    have hshifted : probeVec 1 + 20 / 21 * probeVec 2 = 0 := sq_eq_zero_iff.mp (by linarith)
    rw [hthirdZero] at hshifted
    linarith
  have hfirstZero : probeVec 0 = 0 := by
    have hshifted : probeVec 0 + 2 / 5 * probeVec 1 = 0 := sq_eq_zero_iff.mp (by linarith)
    rw [hsecondZero] at hshifted
    linarith
  exact hprobeNe (eq_zero_of_coordinates_eq_zero hfirstZero hsecondZero hthirdZero)

/-- So the antecedent of `Gtz.PatternHeavyWeakToStrict` is met: the design carries
a weakly dominating card-three subset. -/
theorem twinFailureDesign_hasWeakDominator :
    ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧
      Dominates twinFailureDesign dominator :=
  ⟨{2, 4, 5}, by decide, twinFailure_mixedTripleGap_posDef.posSemidef⟩

/-! ### Both canonical triples fail -/

/-- The first line's complement `{3,4,5}` reads `-120` at the probe
`(10, -28, 15)`.  That probe is nearly a null direction: the gap sends it to
`(0, 0, -8)`. -/
theorem twinFailure_firstComplementGap_at_witness :
    (![10, -28, 15] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum twinFailureDesign {3, 4, 5} - 1) *ᵥ ![10, -28, 15]) = -120 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [twinFailureDesign, twinFailureAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-- **The line-`{0,1,2}` complement does not even dominate weakly.** -/
theorem twinFailure_firstComplement_not_dominates :
    ¬ Dominates twinFailureDesign {3, 4, 5} := by
  intro hdominates
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2
    (![10, -28, 15] : Fin 3 → ℝ)
  rw [star_trivial, twinFailure_firstComplementGap_at_witness] at hnonneg
  norm_num at hnonneg

/-- The second line's complement `{1,2,5}` reads `-2` at the probe `(1, 2, 0)`. -/
theorem twinFailure_secondComplementGap_at_witness :
    (![1, 2, 0] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum twinFailureDesign {1, 2, 5} - 1) *ᵥ ![1, 2, 0]) = -2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [twinFailureDesign, twinFailureAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-- **The line-`{0,3,4}` complement does not even dominate weakly.** -/
theorem twinFailure_secondComplement_not_dominates :
    ¬ Dominates twinFailureDesign {1, 2, 5} := by
  intro hdominates
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2
    (![1, 2, 0] : Fin 3 → ℝ)
  rw [star_trivial, twinFailure_secondComplementGap_at_witness] at hnonneg
  norm_num at hnonneg

/-- A fortiori neither is strictly dominating. -/
theorem twinFailure_canonicalTriples_not_posDef :
    ¬ (subsetSum twinFailureDesign {3, 4, 5} - 1).PosDef ∧
      ¬ (subsetSum twinFailureDesign {1, 2, 5} - 1).PosDef :=
  ⟨fun hposDef => twinFailure_firstComplement_not_dominates hposDef.posSemidef,
    fun hposDef => twinFailure_secondComplement_not_dominates hposDef.posSemidef⟩

/-- **REFUTATION.**  There is a HEAVY two-meeting-lines design carrying a weakly
dominating card-three subset on which BOTH canonical line complements fail to
dominate.  Every twin certificate that nominates `{3,4,5}` or `{1,2,5}` therefore
has a genuinely nonempty joint residual, and a proof of
`Gtz.PatternHeavyWeakToStrict` at the two-meeting-lines pattern must nominate a
MIXED triple. -/
theorem exists_twoMeetingLines_heavy_weaklyDominated_bothComplements_fail :
    ∃ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) ∧
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) ∧
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) ∧
      ¬ Dominates design {3, 4, 5} ∧ ¬ Dominates design {1, 2, 5} :=
  ⟨twinFailureDesign, twinFailureDesign_hasLinePattern, twinFailureDesign_allHeavy,
    twinFailureDesign_hasWeakDominator, twinFailure_firstComplement_not_dominates,
    twinFailure_secondComplement_not_dominates⟩

/-- The refutation is of the STRATEGY, never of the obligation: the same design
carries the strictly dominating mixed triple `{2,4,5}`. -/
theorem twinFailure_exists_posDef_cardThree :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum twinFailureDesign selected - 1).PosDef :=
  ⟨{2, 4, 5}, by decide, twinFailure_mixedTripleGap_posDef⟩

end Gtz
