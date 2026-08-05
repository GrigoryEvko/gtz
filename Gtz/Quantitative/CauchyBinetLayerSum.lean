/-
# Cauchy–Binet at every level, and the GENERAL-WEIGHT layer sum

`Gtz.sum_det_subsetSum_sub_one_sixThree` computes the twenty-triple aggregate
`Σ_C det(S_C − 1)` at a UNIFORM weight and gets the design-blind `-56`.  Its route is
the chart: at `t ≡ 1/size` the scalar shift `1/size` presents the chart gap, and the
shifted minor sum has a closed form.  Off the uniform slice that route dies — the gap
is `P − diag t` and no scalar shift presents it.

This file proves the aggregate at EVERY weight, by a completely different route that
never mentions the chart, the weights, or Parseval.  The identity is weight-free:

    Σ_{|C| = rank} det(S_C − 1) = Σ_j (−1)^{rank+j} C(size−j, rank−j) e_j(N)

with `N = Σ_c g_c g_cᵀ` the UNWEIGHTED second moment and `e_j` the total of the
`j`-sized principal minors.  Nothing about the design enters; it holds for any `size`
vectors in `ℝ^rank`.  At `(6,3)` it reads

    Σ_C det(S_C − 1) = det N − 4 e_2(N) + 10 tr N − 20 ,

the twenty triples, the ten triples through an atom, the four through a pair.

## The missing ingredient, supplied here

**CAUCHY–BINET AT EVERY LEVEL** (`sum_det_principalMinors_mul_transpose_comm`), at
general shape and over any commutative ring:

    Σ_{|I| = level} det (A Aᵀ)[I]  =  Σ_{|J| = level} det (Aᵀ A)[J] .

Neither Mathlib nor this repository carries it.  Mathlib has no Cauchy–Binet and no
compound matrices at all; the repository has `Gtz.sum_det_frameMinors_rank` and
`Gtz.sum_det_projectionMinors`, both of which need an orthonormality or design
hypothesis and neither of which is this.  The proof is three lines once the right
two Mathlib lemmas are put next to each other: both sides are the same coefficient of
`det(1 + X · M)`, and the two generating functions agree by Weinstein–Aronszajn.  At
`level = rank` and `A` of shape `size × rank` the left side is `Σ_{|J| = rank}
det(A_J)²` and the right side is `det(AᵀA)`, which is classical Cauchy–Binet.

## What is REUSED, not re-proved — REPORTED, because it is easy to miss

Both combinatorial steps this identity needs ARE ALREADY IN THE TREE, in
`Gtz.Quantitative.MixtureAggregates`, at general index type and general commutative
ring, put there for the derivative identity and exactly right here.  Anyone reaching
for this identity should reuse them rather than rebuild them: the only genuinely
missing ingredient was Cauchy–Binet.

* `Gtz.sum_powersetCard_sum_powersetCard` — the double count.  Each `level`-subset
  sits inside `C(size−level, rank−level)` of the `rank`-subsets.
* `Gtz.sum_det_principalSubmatrix_subtype` — the subtype-of-subtype reindexing.  The
  `level`-sized principal minors of the block on `C` are the whole matrix's minors
  over the subsets of `C`.

`Gtz.det_mul_transpose_sub_one_comm` (`Gtz.Quantitative.ChartHadamard`) is the same
Weinstein–Aronszajn flip this file needs, but only at index type `Fin dimension`; the
general-index form is proved here because the block index is a subtype.

## The three levels separately

`sum_principalMinorTotal_subsetSum_eq` is the layer law at ONE level, and it is the
whole content: at `level = rank` it is the determinant aggregate, at `level = 1` the
trace aggregate `Σ_C tr S_C = C(size−1, rank−1) tr N`, at `level = 2` the `e_2`
aggregate.  The headline is the alternating sum of the three (four, counting the
constant) and nothing more.

## The two anchors, both in-kernel

`sum_det_subsetSum_sub_one_sixThree_recheck` is `-56` at every uniform `(6,3)` design,
an independent re-derivation of the shipped `Gtz.sum_det_subsetSum_sub_one_sixThree`
along a route sharing no step with it.  `sum_det_subsetSum_sub_one_splitTetra` is `-64`
at the whole two-parameter split-tetrahedron family — the number
`Gtz.Quantitative.ChartHadamard`'s header quotes as measured outside Lean and offers as
the reason the uniform statement needs a uniformity hypothesis.  Both were exact
rational cross-checks before; both are now theorems.

## HONESTY — the de-uniformised no-go is WINDOWED, and that is not a shortcoming of
the mechanization but a fact about the object

At `t ≡ 1/size` Parseval forces `N = size · 1`, so the aggregate collapses to a function
of `(size, rank)` and the uniform no-go is unconditional.  Off that slice the aggregate
is a genuine function of the design, and it CAN vanish inside the region a tie with all
twenty triples dominating forces.  Concretely: all twenty dominating gives
`Σ_C (S_C − 1) = 10N − 20·1 ⪰ 0`, hence `N ⪰ 2·1`; Parseval's trace gives
`Σ_c t_c |g_c|² = 3` with `Σ_c t_c = 1`, hence some leverage is at least `3`, hence
`λ_max(N) ≥ 3`.  Both constraints are satisfied by spectra on which
`det N − 4 e_2(N) + 10 tr N − 20` is exactly zero — for instance `(58/5, 8, 8)` and
`(73/5, 46/5, 13/2)` [EXACT rational, outside Lean].  So the aggregate alone does NOT
close the general-weight cell, and any claim that it does is false.

What the general-weight form therefore buys is the window itself:
`layerWindow_eq_zero_of_isTie_of_forall_dominates` turns the conditional chain's second
arrow into ONE SCALAR EQUATION on three numbers computed from the unweighted moment, at
every weighting; `not_forall_dominates_of_isTie_sixThree` kills every design missing it.
The uniform theorem (`-56`) and the whole split-tetrahedron family (`-64`) are two
instances, and the second is a non-uniform cell the shipped statement cannot reach.
Whether some `(6,3)` design actually SITS on the window with all twenty triples exactly
tied is a separate question — twenty equations on fifteen effective parameters, expected
empty, not settled here.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm
import Gtz.Quantitative.ChartHadamard
import Gtz.Quantitative.MixtureAggregates
import Gtz.Certificates.ResidueDissolution
import Gtz.Ties.SplitTetrahedronTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## The principal-minor total -/

section MinorTotal

variable {baseRing : Type*} [CommRing baseRing]
variable {indexType : Type*} [Fintype indexType] [DecidableEq indexType]

/-- **`e_level` of a square matrix**: the total of its `level`-sized principal minors.
At `level = 0` it is one, at `level = 1` the trace, at `level = Fintype.card` the
determinant, and in general the `level`-th coefficient of `det(1 + X·M)`. -/
def principalMinorTotal (form : Matrix indexType indexType baseRing) (level : ℕ) : baseRing :=
  ∑ chosen ∈ (Finset.univ : Finset indexType).powersetCard level,
    (form.submatrix (Subtype.val : { index // index ∈ chosen } → indexType)
      (Subtype.val : { index // index ∈ chosen } → indexType)).det

/-- The principal-minor total IS the generating-function coefficient. -/
theorem principalMinorTotal_eq_coeff (form : Matrix indexType indexType baseRing) (level : ℕ) :
    principalMinorTotal form level
      = (Matrix.det (1 + (Polynomial.X : Polynomial baseRing) •
          form.map Polynomial.C)).coeff level :=
  (Matrix.coeff_det_one_add_X_smul_eq_sum_minors form level).symm

/-- Level zero: the empty minor is one. -/
@[simp] theorem principalMinorTotal_zero (form : Matrix indexType indexType baseRing) :
    principalMinorTotal form 0 = 1 := by
  rw [principalMinorTotal, Finset.powersetCard_zero, Finset.sum_singleton]
  exact Matrix.det_isEmpty

/-- Level one: the trace. -/
@[simp] theorem principalMinorTotal_one (form : Matrix indexType indexType baseRing) :
    principalMinorTotal form 1 = Matrix.trace form := by
  rw [principalMinorTotal_eq_coeff, Matrix.coeff_det_one_add_X_smul_one]

/-- Level equal to the dimension: the determinant. -/
theorem principalMinorTotal_card (form : Matrix indexType indexType baseRing) :
    principalMinorTotal form (Fintype.card indexType) = form.det := by
  classical
  have hcard : (Finset.univ : Finset indexType).card = Fintype.card indexType :=
    Finset.card_univ
  rw [principalMinorTotal, ← hcard, Finset.powersetCard_self, Finset.sum_singleton]
  exact Matrix.det_submatrix_equiv_self
    (Equiv.subtypeUnivEquiv (fun index : indexType => Finset.mem_univ index)) form

/-- Above the dimension every minor sum is empty. -/
theorem principalMinorTotal_of_card_lt (form : Matrix indexType indexType baseRing) {level : ℕ}
    (hlevel : Fintype.card indexType < level) : principalMinorTotal form level = 0 := by
  rw [principalMinorTotal,
    Finset.powersetCard_eq_empty.mpr (by rwa [Finset.card_univ]), Finset.sum_empty]

/-- Scaling the matrix scales the level-th total by that power: every summand is a
`level × level` determinant. -/
theorem principalMinorTotal_smul (scale : baseRing) (form : Matrix indexType indexType baseRing)
    (level : ℕ) :
    principalMinorTotal (scale • form) level = scale ^ level * principalMinorTotal form level := by
  rw [principalMinorTotal, principalMinorTotal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun chosen hchosen => ?_
  have hcard : chosen.card = level := (Finset.mem_powersetCard.mp hchosen).2
  have hblock : (scale • form).submatrix
        (Subtype.val : { index // index ∈ chosen } → indexType)
        (Subtype.val : { index // index ∈ chosen } → indexType)
      = scale • form.submatrix
          (Subtype.val : { index // index ∈ chosen } → indexType)
          (Subtype.val : { index // index ∈ chosen } → indexType) := rfl
  rw [hblock, Matrix.det_smul, Fintype.card_coe, hcard]

/-- Every principal minor of the identity is one, so its level-th total counts the
subsets. -/
theorem principalMinorTotal_one_matrix (level : ℕ) :
    principalMinorTotal (1 : Matrix indexType indexType baseRing) level
      = (((Fintype.card indexType).choose level : ℕ) : baseRing) := by
  have hblock : ∀ chosen : Finset indexType,
      (1 : Matrix indexType indexType baseRing).submatrix
          (Subtype.val : { index // index ∈ chosen } → indexType)
          (Subtype.val : { index // index ∈ chosen } → indexType)
        = (1 : Matrix { index // index ∈ chosen } { index // index ∈ chosen } baseRing) := by
    intro chosen
    ext leftSlot rightSlot
    by_cases hsame : leftSlot = rightSlot
    · rw [hsame, Matrix.submatrix_apply, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.submatrix_apply,
        Matrix.one_apply_ne (fun hvalue => hsame (Subtype.ext hvalue)),
        Matrix.one_apply_ne hsame]
  simp only [principalMinorTotal, hblock, Matrix.det_one, Finset.sum_const,
    Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- A scalar matrix's level-th total: `scale^level · C(dim, level)`. -/
theorem principalMinorTotal_smul_one (scale : baseRing) (level : ℕ) :
    principalMinorTotal (scale • (1 : Matrix indexType indexType baseRing)) level
      = scale ^ level * (((Fintype.card indexType).choose level : ℕ) : baseRing) := by
  rw [principalMinorTotal_smul, principalMinorTotal_one_matrix]

end MinorTotal

/-! ## Cauchy–Binet at every level -/

section CauchyBinet

variable {baseRing : Type*} [CommRing baseRing]
variable {rowIndex colIndex : Type*} [Fintype rowIndex] [DecidableEq rowIndex]
  [Fintype colIndex] [DecidableEq colIndex]

/-- **CAUCHY–BINET, AT EVERY LEVEL AND EVERY SHAPE.**  For a rectangular `A`, the two
square products `A Aᵀ` and `Aᵀ A` have the SAME principal-minor total at every level:

    `Σ_{|I| = level} det (A Aᵀ)[I]  =  Σ_{|J| = level} det (Aᵀ A)[J]` .

At `level = Fintype.card colIndex` this is classical Cauchy–Binet — the right side is
`det(Aᵀ A)` and the left side is the sum of the squared maximal minors of `A`, since
`(A Aᵀ)[I] = A_I (A_I)ᵀ`.  At `level = 1` it is `trace (A Aᵀ) = trace (Aᵀ A)`.

Neither Mathlib nor this repository has this in any form: Mathlib carries no
Cauchy–Binet and no compound matrices, and the repository's `sum_det_frameMinors_rank`
and `sum_det_projectionMinors` both need an orthonormality or design hypothesis.

The proof is Weinstein–Aronszajn under a coefficient extraction.  Both totals are the
`level`-th coefficient of a determinant over `baseRing[X]`
(`Matrix.coeff_det_one_add_X_smul_eq_sum_minors`), and the two determinants agree
because `1 + (X·A) Aᵀ` and `1 + Aᵀ (X·A)` do
(`Matrix.det_one_add_mul_comm`).  Nothing about the ring, the shape, or the two
cardinalities is assumed. -/
theorem sum_det_principalMinors_mul_transpose_comm (rect : Matrix rowIndex colIndex baseRing)
    (level : ℕ) :
    principalMinorTotal (rect * rectᵀ) level = principalMinorTotal (rectᵀ * rect) level := by
  set liftedRect : Matrix rowIndex colIndex (Polynomial baseRing) :=
    rect.map Polynomial.C with hliftedRect
  have hleftMap : (rect * rectᵀ).map Polynomial.C = liftedRect * liftedRectᵀ := by
    rw [hliftedRect, Matrix.map_mul (f := (Polynomial.C : baseRing →+* Polynomial baseRing)),
      Matrix.transpose_map]
  have hrightMap : (rectᵀ * rect).map Polynomial.C = liftedRectᵀ * liftedRect := by
    rw [hliftedRect, Matrix.map_mul (f := (Polynomial.C : baseRing →+* Polynomial baseRing)),
      Matrix.transpose_map]
  have hgenerating :
      Matrix.det (1 + (Polynomial.X : Polynomial baseRing) • (rect * rectᵀ).map Polynomial.C)
        = Matrix.det (1 + (Polynomial.X : Polynomial baseRing) •
            (rectᵀ * rect).map Polynomial.C) := by
    rw [hleftMap, hrightMap, ← Matrix.smul_mul, ← Matrix.mul_smul]
    exact Matrix.det_one_add_mul_comm ((Polynomial.X : Polynomial baseRing) • liftedRect)
      liftedRectᵀ
  rw [principalMinorTotal_eq_coeff, principalMinorTotal_eq_coeff, hgenerating]

/-- **CLASSICAL CAUCHY–BINET**, the top-level corner: for `A` of shape
`rowIndex × colIndex`, the total of the `card colIndex`-sized principal minors of
`A Aᵀ` is `det (Aᵀ A)`. -/
theorem sum_det_principalMinors_mul_transpose_card (rect : Matrix rowIndex colIndex baseRing) :
    principalMinorTotal (rect * rectᵀ) (Fintype.card colIndex) = (rectᵀ * rect).det := by
  rw [sum_det_principalMinors_mul_transpose_comm, principalMinorTotal_card]

end CauchyBinet

/-! ## `det(M − 1)` as the alternating total of the principal-minor totals -/

section ShiftedDeterminant

variable {indexType : Type*} [Fintype indexType] [DecidableEq indexType]

/-- The generating polynomial `det(1 + X·M)` has degree at most the dimension:
above it every coefficient is an empty minor sum. -/
theorem natDegree_det_one_add_X_smul_lt (form : Matrix indexType indexType ℝ) :
    (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • form.map Polynomial.C)).natDegree
      < Fintype.card indexType + 1 := by
  refine Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun level hlevel => ?_)
  rw [← principalMinorTotal_eq_coeff]
  exact principalMinorTotal_of_card_lt form hlevel

/-- Evaluating the generating polynomial at `-1` returns `det(1 − M)`. -/
theorem eval_neg_one_det_one_add_X_smul (form : Matrix indexType indexType ℝ) :
    (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • form.map Polynomial.C)).eval (-1)
      = (1 - form).det := by
  have hmapDet := RingHom.map_det (Polynomial.evalRingHom (-1 : ℝ))
    (1 + (Polynomial.X : Polynomial ℝ) • form.map Polynomial.C)
  simp only [Polynomial.coe_evalRingHom, RingHom.mapMatrix_apply] at hmapDet
  rw [hmapDet]
  congr 1
  ext rowIndex colIndex
  by_cases hdiagonal : rowIndex = colIndex
  · subst hdiagonal
    simp [Matrix.one_apply_eq, sub_eq_add_neg]
  · simp [Matrix.one_apply_ne hdiagonal]

/-- **THE SHIFTED DETERMINANT AS AN ALTERNATING MINOR TOTAL.**  For every square
matrix,

    `det (M − 1) = Σ_{level ≤ dim} (−1)^{dim + level} e_level(M)` ,

the characteristic polynomial read at one.  No symmetry, no positivity: it is the
expansion of `det(1 + X·M)` at `X = −1` composed with `det(−A) = (−1)^dim det A`. -/
theorem det_sub_one_eq_sum_signed_principalMinorTotal (form : Matrix indexType indexType ℝ) :
    (form - 1).det
      = ∑ level ∈ Finset.range (Fintype.card indexType + 1),
          (-1 : ℝ) ^ (Fintype.card indexType + level) * principalMinorTotal form level := by
  have hexpand := Polynomial.eval_eq_sum_range' (natDegree_det_one_add_X_smul_lt form) (-1 : ℝ)
  rw [eval_neg_one_det_one_add_X_smul] at hexpand
  have hnegate : (form - 1).det = (-1 : ℝ) ^ Fintype.card indexType * (1 - form).det := by
    rw [← Matrix.det_neg, neg_sub]
  rw [hnegate, hexpand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun level _ => ?_
  rw [← principalMinorTotal_eq_coeff, pow_add]
  ring

end ShiftedDeterminant

/-! ## The atom frame and its two Grams -/

section AtomFrame

variable {m k : ℕ}

/-- **The atom-row frame** of a design: the `size × rank` matrix whose rows are the
atoms.  Its two square products are the rank-side unweighted moment `N = Aᵀ A` and
the size-side Gram `G = A Aᵀ` of atom pairings. -/
def atomRowFrame (D : WeightedDesign m k) : Matrix (Fin m) (Fin k) ℝ :=
  selectedAtomRows D (id : Fin m → Fin m)

theorem atomRowFrame_apply (D : WeightedDesign m k) (atomIndex : Fin m) (coord : Fin k) :
    atomRowFrame D atomIndex coord = D.atom atomIndex coord := rfl

/-- **The atom Gram** `G = A Aᵀ`, the `size × size` matrix of atom pairings. -/
def atomGramMatrix (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  atomRowFrame D * (atomRowFrame D)ᵀ

theorem atomGramMatrix_apply (D : WeightedDesign m k) (firstAtom secondAtom : Fin m) :
    atomGramMatrix D firstAtom secondAtom = D.atom firstAtom ⬝ᵥ D.atom secondAtom := rfl

/-- The rank-side product of the whole frame is the unweighted second moment
`N = Σ_c g_c g_cᵀ`, which is `subsetSum` over everything. -/
theorem transpose_mul_atomRowFrame (D : WeightedDesign m k) :
    (atomRowFrame D)ᵀ * atomRowFrame D = subsetSum D Finset.univ := by
  rw [atomRowFrame, transpose_mul_selectedAtomRows D (id : Fin m → Fin m) Function.injective_id,
    Finset.image_id]

/-- The frame restricted to the atoms of a subset. -/
def selectedRowFrame (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    Matrix { atomIndex // atomIndex ∈ selected } (Fin k) ℝ :=
  (atomRowFrame D).submatrix (Subtype.val : { atomIndex // atomIndex ∈ selected } → Fin m) id

/-- The rank-side product of a restricted frame is the selected atom sum. -/
theorem transpose_mul_selectedRowFrame (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    (selectedRowFrame D selected)ᵀ * selectedRowFrame D selected = subsetSum D selected := by
  ext rowCoord colCoord
  rw [Matrix.mul_apply, subsetSum, Matrix.sum_apply]
  rw [← Finset.sum_attach selected
    (fun atomIndex => atomMatrix (D.atom atomIndex) rowCoord colCoord)]
  exact Finset.sum_congr rfl fun slot _ => rfl

/-- The size-side product of a restricted frame is the Gram block on that subset. -/
theorem selectedRowFrame_mul_transpose (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    selectedRowFrame D selected * (selectedRowFrame D selected)ᵀ
      = (atomGramMatrix D).submatrix
          (Subtype.val : { atomIndex // atomIndex ∈ selected } → Fin m)
          (Subtype.val : { atomIndex // atomIndex ∈ selected } → Fin m) := by
  ext firstSlot secondSlot
  simp only [selectedRowFrame, atomGramMatrix, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.transpose_apply, id_eq]

end AtomFrame

/-! ## The layer law, one level at a time -/

section LayerLaw

variable {m k : ℕ}

/-- **THE LAYER LAW AT ONE LEVEL.**  Summing `e_level` of the selected atom sum over
all `rank`-subsets multiplies `e_level` of the whole unweighted moment by the number
of `rank`-subsets containing a given `level`-subset:

    `Σ_{|C| = rank} e_level(S_C) = C(size − level, rank − level) · e_level(N)` .

Three shipped steps and one new one.  Cauchy–Binet
(`sum_det_principalMinors_mul_transpose_comm`) moves `e_level(S_C)` off the `rank × rank`
atom sum and onto the `|C| × |C|` Gram block; `Gtz.sum_det_principalSubmatrix_subtype`
reindexes the block's minors as the whole Gram's minors over subsets of `C`;
`Gtz.sum_powersetCard_sum_powersetCard` double-counts; Cauchy–Binet again returns to
the rank side.

At `level = 1` this is `Σ_C tr S_C = C(size−1, rank−1) · tr N`, at `level = 2` the
`e_2` aggregate, and at `level = rank` the determinant aggregate
`Σ_C det S_C = C(size−rank, 0) · e_rank(N) = det N` when `rank = k`. -/
theorem sum_principalMinorTotal_subsetSum_eq (D : WeightedDesign m k) (level : ℕ)
    (hlevel : level ≤ k) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        principalMinorTotal (subsetSum D selected) level
      = (((m - level).choose (k - level) : ℕ) : ℝ)
        * principalMinorTotal (subsetSum D Finset.univ) level := by
  classical
  have hblock : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      principalMinorTotal (subsetSum D selected) level
        = ∑ inner ∈ selected.powersetCard level,
            ((atomGramMatrix D).submatrix
              (Subtype.val : { atomIndex // atomIndex ∈ inner } → Fin m)
              (Subtype.val : { atomIndex // atomIndex ∈ inner } → Fin m)).det := by
    intro selected _
    rw [← transpose_mul_selectedRowFrame D selected,
      ← sum_det_principalMinors_mul_transpose_comm (selectedRowFrame D selected) level,
      selectedRowFrame_mul_transpose]
    exact sum_det_principalSubmatrix_subtype (atomGramMatrix D) selected level
  have hmoment : principalMinorTotal (subsetSum D Finset.univ) level
      = principalMinorTotal (atomGramMatrix D) level := by
    rw [← transpose_mul_atomRowFrame D,
      ← sum_det_principalMinors_mul_transpose_comm (atomRowFrame D) level, atomGramMatrix]
  have hcount := sum_powersetCard_sum_powersetCard (indexType := Fin m) (baseRing := ℝ) k level
    hlevel (fun inner => ((atomGramMatrix D).submatrix
      (Subtype.val : { atomIndex // atomIndex ∈ inner } → Fin m)
      (Subtype.val : { atomIndex // atomIndex ∈ inner } → Fin m)).det)
  rw [Finset.sum_congr rfl hblock, hcount, hmoment, principalMinorTotal, Fintype.card_fin,
    nsmul_eq_mul]

/-- **THE GENERAL-WEIGHT LAYER SUM.**  The aggregate of the twenty (in general
`C(size, rank)`) tie determinants, at EVERY weight, is a fixed integral combination of
the elementary symmetric functions of the UNWEIGHTED second moment `N = Σ_c g_c g_cᵀ`:

    `Σ_{|C| = rank} det(S_C − 1) = Σ_j (−1)^{rank+j} C(size−j, rank−j) e_j(N)` .

No weight appears on either side, and no design hypothesis is used: this holds for any
`size` vectors in `ℝ^rank`.  `Gtz.sum_det_subsetSum_sub_one_uniform` is the uniform
slice — Parseval at `t ≡ 1/size` forces `N = size·1`, which is exactly why the shipped
aggregate is design-blind and exactly why that blindness is an artefact of uniformity. -/
theorem sum_det_subsetSum_sub_one_eq (D : WeightedDesign m k) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (subsetSum D selected - 1).det
      = ∑ level ∈ Finset.range (k + 1),
          (-1 : ℝ) ^ (k + level) * (((m - level).choose (k - level) : ℕ) : ℝ)
            * principalMinorTotal (subsetSum D Finset.univ) level := by
  have hexpand : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      (subsetSum D selected - 1).det
        = ∑ level ∈ Finset.range (k + 1),
            (-1 : ℝ) ^ (k + level) * principalMinorTotal (subsetSum D selected) level := by
    intro selected _
    have hshifted := det_sub_one_eq_sum_signed_principalMinorTotal (subsetSum D selected)
    rwa [Fintype.card_fin] at hshifted
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun level hlevel => ?_
  rw [← Finset.mul_sum,
    sum_principalMinorTotal_subsetSum_eq D level (Nat.lt_succ_iff.mp (Finset.mem_range.mp hlevel)),
    ← mul_assoc]

end LayerLaw

/-! ## The `(6,3)` reading -/

/-- **THE `(6,3)` GENERAL-WEIGHT LAYER SUM, in the campaign's form.**  With
`N = Σ_c g_c g_cᵀ` the unweighted second moment of a `(6,3)` design,

    `Σ_C det(S_C − 1) = det N − 4 e_2(N) + 10 tr N − 20` ,

the sum over all twenty triples.  The three coefficients are the three layer counts:
each atom lies in `C(5,2) = 10` triples, each pair in `C(4,1) = 4`, and there are
`C(6,3) = 20` triples in all.

At a uniform weight Parseval gives `N = 6·1`, so the right side is
`216 − 4·108 + 10·18 − 20 = −56`, reproducing `Gtz.sum_det_subsetSum_sub_one_sixThree`
by a route that never touches the chart.  At the split tetrahedron `N` has spectrum
`(8, 6, 4)` and the right side is `192 − 4·104 + 10·18 − 20 = −64`. -/
theorem sum_det_subsetSum_sub_one_sixThree_eq (D : WeightedDesign 6 3) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        (subsetSum D selected - 1).det
      = (subsetSum D Finset.univ).det
        - 4 * principalMinorTotal (subsetSum D Finset.univ) 2
        + 10 * Matrix.trace (subsetSum D Finset.univ)
        - 20 := by
  have hdet : principalMinorTotal (subsetSum D Finset.univ) 3 = (subsetSum D Finset.univ).det := by
    have hcard := principalMinorTotal_card (subsetSum D Finset.univ)
    rwa [Fintype.card_fin] at hcard
  have hexpanded := sum_det_subsetSum_sub_one_eq D
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    hdet, principalMinorTotal_one, principalMinorTotal_zero] at hexpanded
  rw [hexpanded]
  norm_num [Nat.choose]
  ring

/-! ## The three elementary-symmetric layer aggregates at `(6,3)`, separately -/

section SixThreeLayers

variable (D : WeightedDesign 6 3)

/-- **THE DETERMINANT LAYER SUM** — classical Cauchy–Binet read on a design: the twenty
triple determinants total the determinant of the unweighted moment.  The layer count is
`C(3,0) = 1`: a triple contains exactly one triple. -/
theorem sum_det_subsetSum_sixThree :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3, (subsetSum D selected).det
      = (subsetSum D Finset.univ).det := by
  have hlevel := sum_principalMinorTotal_subsetSum_eq D 3 le_rfl
  have hblock : ∀ selected : Finset (Fin 6),
      principalMinorTotal (subsetSum D selected) 3 = (subsetSum D selected).det := by
    intro selected
    have hcard := principalMinorTotal_card (subsetSum D selected)
    rwa [Fintype.card_fin] at hcard
  simp only [hblock] at hlevel
  rw [hlevel]
  norm_num

/-- **THE `e_2` LAYER SUM**: each pair lies in `C(4,1) = 4` of the twenty triples. -/
theorem sum_principalMinorTotal_two_subsetSum_sixThree :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        principalMinorTotal (subsetSum D selected) 2
      = 4 * principalMinorTotal (subsetSum D Finset.univ) 2 := by
  rw [sum_principalMinorTotal_subsetSum_eq D 2 (by norm_num)]
  norm_num

/-- **THE TRACE LAYER SUM**: each atom lies in `C(5,2) = 10` of the twenty triples. -/
theorem sum_trace_subsetSum_sixThree :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        Matrix.trace (subsetSum D selected)
      = 10 * Matrix.trace (subsetSum D Finset.univ) := by
  have hlevel := sum_principalMinorTotal_subsetSum_eq D 1 (by norm_num)
  have hchoose : ((6 - 1).choose (3 - 1) : ℕ) = 10 := by norm_num [Nat.choose]
  simp only [principalMinorTotal_one] at hlevel
  rw [hlevel, hchoose]
  norm_num

end SixThreeLayers

/-! ## The uniform slice, in the campaign brief's own presentation -/

section Uniform

variable {m k : ℕ}

/-- **PARSEVAL AT A UNIFORM WEIGHT PINS THE MOMENT.**  When every weight is `1/size`,
the unweighted second moment is the scalar `size · 1`.  This one line is the whole
reason the shipped uniform aggregate is design-blind. -/
theorem subsetSum_univ_eq_smul_one_of_uniform (D : WeightedDesign m k)
    (huniform : ∀ atomIndex : Fin m, D.weight atomIndex = ((m : ℝ))⁻¹) :
    subsetSum D Finset.univ = ((m : ℝ)) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hsizeNe : ((m : ℝ)) ≠ 0 := by
    have hsizePos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast size_pos_of_design D
    exact ne_of_gt hsizePos
  have hscaled : ((m : ℝ))⁻¹ • subsetSum D Finset.univ = (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [subsetSum, Finset.smul_sum, ← D.isParseval]
    exact Finset.sum_congr rfl fun atomIndex _ => by rw [huniform atomIndex]
  calc subsetSum D Finset.univ
      = ((m : ℝ)) • (((m : ℝ))⁻¹ • subsetSum D Finset.univ) := by
        rw [smul_smul, mul_inv_cancel₀ hsizeNe, one_smul]
    _ = ((m : ℝ)) • (1 : Matrix (Fin k) (Fin k) ℝ) := by rw [hscaled]

/-- **(I8) IN THE BRIEF'S PRESENTATION.**  At a uniform weight the aggregate is

    `Σ_j (−1)^{rank+j} C(size−j, rank−j) · size^j · C(rank, j)` ,

which is exactly the form the campaign brief states and which
`Gtz.Quantitative.ChartHadamard`'s header records as NOT proved there — that file
proves the coefficient convolution of the generating function instead and says of the
two forms "THEY ARE NOT PROVED EQUAL HERE".  Both are now available, and since each
equals the same left-hand side they agree at every cell carrying a uniform design.

The route here never touches the chart: the general-weight layer sum plus
`subsetSum_univ_eq_smul_one_of_uniform`. -/
theorem sum_det_subsetSum_sub_one_uniform_choose (D : WeightedDesign m k)
    (huniform : ∀ atomIndex : Fin m, D.weight atomIndex = ((m : ℝ))⁻¹) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (subsetSum D selected - 1).det
      = ∑ level ∈ Finset.range (k + 1),
          (-1 : ℝ) ^ (k + level) * (((m - level).choose (k - level) : ℕ) : ℝ)
            * ((m : ℝ) ^ level * ((k.choose level : ℕ) : ℝ)) := by
  rw [sum_det_subsetSum_sub_one_eq D]
  refine Finset.sum_congr rfl fun level _ => ?_
  rw [subsetSum_univ_eq_smul_one_of_uniform D huniform, principalMinorTotal_smul_one,
    Fintype.card_fin]

end Uniform

/-- **THE `-56` ANCHOR, RE-DERIVED.**  The shipped
`Gtz.sum_det_subsetSum_sub_one_sixThree` gets this through the chart pencil and a
scalar shift; this route goes through Cauchy–Binet and the layer counts and never
mentions the chart.  Two independent proofs of one number. -/
theorem sum_det_subsetSum_sub_one_sixThree_recheck (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, D.weight atomIndex = ((6 : ℝ))⁻¹) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        (subsetSum D selected - 1).det = -56 := by
  rw [sum_det_subsetSum_sub_one_uniform_choose D huniform]
  norm_num [Finset.sum_range_succ, Nat.choose]

/-! ## The `(6,3)` window as three explicit numbers -/

/-- `e_2` of a `3 × 3` matrix from its determinant, its trace, and its shifted
determinant — the level sum solved for the middle term.  This is what makes the window
computable at an explicit design without ever enumerating the three pair blocks. -/
theorem principalMinorTotal_two_fin_three (form : Matrix (Fin 3) (Fin 3) ℝ) :
    principalMinorTotal form 2 = form.det + Matrix.trace form - 1 - (form - 1).det := by
  have hlevel := det_sub_one_eq_sum_signed_principalMinorTotal form
  have hdet : principalMinorTotal form 3 = form.det := by
    have hcard := principalMinorTotal_card form
    rwa [Fintype.card_fin] at hcard
  rw [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, hdet, principalMinorTotal_one, principalMinorTotal_zero] at hlevel
  norm_num at hlevel
  linarith

/-! ## The split tetrahedron: the `-64` anchor -/

/-- The unweighted second moment of the split tetrahedron: the tetrahedron's `4 · 1`
plus one extra copy of each duplicated direction. -/
theorem subsetSum_univ_splitTetra (D : WeightedDesign 6 3) (hatom : D.atom = splitTetraAtom) :
    subsetSum D Finset.univ = !![6, 0, 0; 0, 6, -2; 0, -2, 6] := by
  have hfirst : D.atom 0 = ![(1 : ℝ), 1, 1] := by rw [hatom]; rfl
  have hsecond : D.atom 1 = ![(1 : ℝ), -1, -1] := by rw [hatom]; rfl
  have hthird : D.atom 2 = ![(-1 : ℝ), 1, -1] := by rw [hatom]; rfl
  have hfourth : D.atom 3 = ![(-1 : ℝ), 1, -1] := by rw [hatom]; rfl
  have hfifth : D.atom 4 = ![(-1 : ℝ), -1, 1] := by rw [hatom]; rfl
  have hsixth : D.atom 5 = ![(-1 : ℝ), -1, 1] := by rw [hatom]; rfl
  ext rowIndex colIndex
  rw [subsetSum, Matrix.sum_apply, Fin.sum_univ_six]
  simp only [atomMatrix, Matrix.vecMulVec_apply, hfirst, hsecond, hthird, hfourth, hfifth, hsixth]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- **THE `-64` ANCHOR.**  The split-tetrahedron atom family — the four tetrahedron
directions with two of them duplicated — has unweighted moment of spectrum `(8, 6, 4)`,
so `det N = 192`, `e_2(N) = 104`, `tr N = 18`, and the twenty tie determinants total

    `192 − 4 · 104 + 10 · 18 − 20 = -64` ,

against the uniform `-56`.  The whole two-parameter weight family shares one value: the
aggregate does not see the weights at all, only the atoms.  This is the number
`Gtz.Quantitative.ChartHadamard`'s header quotes as measured outside Lean and offers as
the reason the uniform statement carries a uniformity hypothesis. -/
theorem sum_det_subsetSum_sub_one_splitTetra (D : WeightedDesign 6 3)
    (hatom : D.atom = splitTetraAtom) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
        (subsetSum D selected - 1).det = -64 := by
  have hmoment := subsetSum_univ_splitTetra D hatom
  have hdet : (subsetSum D Finset.univ).det = 192 := by
    rw [hmoment, Matrix.det_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have htrace : Matrix.trace (subsetSum D Finset.univ) = 18 := by
    rw [hmoment, Matrix.trace_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hgapDet : (subsetSum D Finset.univ - 1).det = 105 := by
    have hgap : (!![6, 0, 0; 0, 6, -2; 0, -2, 6] : Matrix (Fin 3) (Fin 3) ℝ) - 1
        = !![5, 0, 0; 0, 5, -2; 0, -2, 5] := by
      ext rowIndex colIndex
      fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]
    rw [hmoment, hgap, Matrix.det_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hpairTotal : principalMinorTotal (subsetSum D Finset.univ) 2 = 104 := by
    rw [principalMinorTotal_two_fin_three, hdet, htrace, hgapDet]
    norm_num
  rw [sum_det_subsetSum_sub_one_sixThree_eq D, hdet, htrace, hpairTotal]
  norm_num

/-! ## The `(6,3)` no-go, de-uniformised -/

section NoGo

/-- At a tie every weakly dominating subset of the critical size has vanishing gap
determinant: the gap is positive semidefinite and, by the tie, not positive definite,
so it is singular. -/
theorem det_subsetSum_sub_one_eq_zero_of_isTie_of_dominates {size rank : ℕ}
    (design : WeightedDesign size rank) (htie : IsTie design) {selected : Finset (Fin size)}
    (hcard : selected.card = rank) (hdominates : Dominates design selected) :
    (subsetSum design selected - 1).det = 0 := by
  by_contra hne
  exact htie.2 selected hcard (hdominates.posDef_iff_det_ne_zero.mpr hne)

/-- **THE WINDOW EQUATION — the no-go promoted off the uniform slice.**  A `(6,3)` tie
with all twenty triples weakly dominating forces ONE SCALAR EQUATION on the unweighted
second moment, at EVERY weighting:

    `det N − 4 e_2(N) + 10 tr N − 20 = 0` .

The twenty gap determinants are individually zero, so their total is zero; the total is
the general-weight layer sum.  No uniformity, no Parseval beyond what the design carries
anyway.

`Gtz.sum_det_subsetSum_sub_one_sixThree`, which is the uniform cell, is the corner
`N = 6 · 1` of this, where the left side is `-56`. -/
theorem layerWindow_eq_zero_of_isTie_of_forall_dominates (design : WeightedDesign 6 3)
    (htie : IsTie design)
    (hall : ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected) :
    (subsetSum design Finset.univ).det
        - 4 * principalMinorTotal (subsetSum design Finset.univ) 2
        + 10 * Matrix.trace (subsetSum design Finset.univ) - 20 = 0 := by
  rw [← sum_det_subsetSum_sub_one_sixThree_eq design]
  refine Finset.sum_eq_zero fun selected hselected => ?_
  have hcard := (Finset.mem_powersetCard.mp hselected).2
  exact det_subsetSum_sub_one_eq_zero_of_isTie_of_dominates design htie hcard (hall selected hcard)

/-- **NO `(6,3)` TIE OFF THE WINDOW HAS ALL TWENTY TRIPLES DOMINATING**, at any
weighting.  The uniformity hypothesis of the shipped no-go is replaced by an explicit
inequality on three numbers computed from the unweighted moment alone. -/
theorem not_forall_dominates_of_isTie_sixThree (design : WeightedDesign 6 3)
    (htie : IsTie design)
    (hwindow : (subsetSum design Finset.univ).det
        - 4 * principalMinorTotal (subsetSum design Finset.univ) 2
        + 10 * Matrix.trace (subsetSum design Finset.univ) - 20 ≠ 0)
    (hall : ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected) :
    False :=
  hwindow (layerWindow_eq_zero_of_isTie_of_forall_dominates design htie hall)

/-- **THE UNIFORM NO-GO, RECOVERED.**  Parseval at `t ≡ 1/6` pins `N = 6 · 1`, whose
window value is `216 − 432 + 180 − 20 = -56 ≠ 0`.  So the shipped
`not_forall_dominates_of_isTie_uniform_sixThree` is the `N = 6 · 1` instance of the
windowed statement, and the promotion is strict: the window is a condition on the
moment, and uniformity is one way — not the only way — to violate it. -/
theorem not_forall_dominates_of_isTie_uniform_sixThree (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = ((6 : ℝ))⁻¹)
    (htie : IsTie design)
    (hall : ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected) :
    False := by
  refine not_forall_dominates_of_isTie_sixThree design htie ?_ hall
  rw [subsetSum_univ_eq_smul_one_of_uniform design huniform, principalMinorTotal_smul_one,
    Matrix.trace_smul, Matrix.trace_one, Matrix.det_smul, Matrix.det_one]
  norm_num

/-- **THE SPLIT-TETRAHEDRON FAMILY MISSES THE WINDOW.**  Its value is `-64`, so no
member of the two-parameter split-tetrahedron tie family has all twenty triples
dominating — a NON-UNIFORM cell the shipped statement cannot reach, since the family's
weights are `1/4, 1/4, a, 1/4 − a, b, 1/4 − b`. -/
theorem not_forall_dominates_of_isTie_splitTetra (design : WeightedDesign 6 3)
    (hatom : design.atom = splitTetraAtom) (htie : IsTie design)
    (hall : ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected) :
    False := by
  have hzero : ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (subsetSum design selected - 1).det = 0 := by
    refine Finset.sum_eq_zero fun selected hselected => ?_
    have hcard := (Finset.mem_powersetCard.mp hselected).2
    exact det_subsetSum_sub_one_eq_zero_of_isTie_of_dominates design htie hcard
      (hall selected hcard)
  rw [sum_det_subsetSum_sub_one_splitTetra design hatom] at hzero
  norm_num at hzero

end NoGo

end Gtz
