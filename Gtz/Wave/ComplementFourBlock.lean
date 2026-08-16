/-
# The complement four-block at an excluded pair

Fix a weighted design of rank three and a pair of labels `first ≠ second`.  Delete
that pair.  At six labels the four survivors carry a `4 × 4` principal block of the
projection form, and this file computes that block completely.

The block turns out to be governed entirely by the `2 × 2` block of the EXCLUDED
pair.  Nothing about the four surviving labels enters.

* `det_complementBlock_eq_zero` — the four-block is singular at every excluded
  pair, because a principal block of `V Vᵀ` wider than `V` cannot have full rank.
* `det_one_sub_complementBlock_eq_zero` — one minus the four-block is singular
  too, because the complementary Gram differs from the identity by a sum of two
  rank-one forms.
* Together those two pin `1` and `0` in the spectrum of the four-block, at every
  excluded pair, with no spectral theorem and no eigenvalue in any proof.
* `det_complementGram_eq_one_sub_sub_add` — the level-three symmetric function of
  the four-block is `(1 - P a a) * (1 - P b b) - P a b ^ 2`.  That is the
  determinant of `1` minus the excluded pair's own block.
* `sum_sq_det_complementTriple_eq` — the four `3 × 3` principal minors of the
  four-block are perfect squares and they total that same number.
* `complementMean_le_quarter` and `not_complementMean_gt_third` — the mean of the
  four never passes `1 / 4`, so the averaged determinant cell can never reach the
  `1 / 3` weight floor that the four lightest labels leave.
* `complementTriple_det_eq_of_sum_eq_zero` — when the four surviving atoms add to
  zero the four minors are EQUAL.  The mean is attained, so no lower bound written
  in the block's symmetric functions can beat it.

The route this file closes is the complement half of the pair marginal.  The
through-pair half is `Gtz.exists_det_tripleBlock_ge`, and its own threshold was
refuted by `Gtz.not_pairGapReaches_cell_threshold`.  Both halves are now closed.
-/
import Gtz.Wave.PairGapFloor
import Gtz.Quantitative.CauchyBinetLayerSum

set_option maxHeartbeats 2000000

namespace Gtz

open scoped BigOperators

open Matrix

variable {size rank : ℕ}

/-! ## Rank-three vector identities

Three scalar identities carry every determinant in this file.  Each is a
polynomial identity in the coordinates of two or three vectors of `ℝ³`, closed by
`ring` after the three-by-three expansion.  No matrix inverse, no eigenvalue, no
square root. -/

/-- **A sum of two rank-one forms in three variables is singular.**  Two vectors
span at most a plane, so the form they build cannot be invertible in space.  The
statement is a polynomial identity and its proof reads the explicit `3 × 3`
expansion. -/
theorem det_two_outer_eq_zero (left right : Fin 3 → ℝ) :
    (atomMatrix left + atomMatrix right).det = 0 := by
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.add_apply, Matrix.vecMulVec_apply]
  ring

/-- **The excluded pair decides the complement Gram.**  Subtracting two rank-one
forms from the identity leaves a determinant that reads only the three inner
products of the two vectors — their two squared lengths and their pairing.  This
is the level-two Cauchy-Binet step written out, and it is where the four
surviving labels stop mattering. -/
theorem det_one_sub_two_outer (left right : Fin 3 → ℝ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix left - atomMatrix right).det
      = (1 - left ⬝ᵥ left) * (1 - right ⬝ᵥ right) - (left ⬝ᵥ right) ^ 2 := by
  simp only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.one_apply, atomMatrix,
    Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring

/-- The identity minus two rank-one forms differs from the identity by a singular
form.  This is the shape that pins the eigenvalue `1`. -/
theorem det_one_sub_one_sub_two_outer (left right : Fin 3 → ℝ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix left - atomMatrix right)).det = 0 := by
  have hrewrite : (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix left - atomMatrix right)
      = atomMatrix left + atomMatrix right := by
    ext row col
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [hrewrite, det_two_outer_eq_zero]

/-! ## Cauchy-Binet at four rows and three columns, written out

The general layer law lives in `Gtz.sum_det_principalMinors_mul_transpose_comm`.
At the one shape this file needs — four rows, three columns — the law is a single
polynomial identity in twelve variables, and stating it explicitly removes every
`powersetCard` index-matching step from the arguments below. -/

/-- The three-row selections of a four-row frame, indexed by the omitted row. -/
def omitRow : Fin 4 → Fin 3 → Fin 4
  | 0 => ![1, 2, 3]
  | 1 => ![0, 2, 3]
  | 2 => ![0, 1, 3]
  | _ => ![0, 1, 2]

/-- **CAUCHY-BINET AT `(4,3)`, EXPLICIT.**  The Gram determinant of a four-by-three
frame is the sum of the squares of its four maximal minors.  Every principal
`3 × 3` minor of `V Vᵀ` is a perfect square, and the four of them total
`det (Vᵀ V)`. -/
theorem det_transpose_mul_fourThree (frame : Matrix (Fin 4) (Fin 3) ℝ) :
    (frameᵀ * frame).det = ∑ omitted : Fin 4, (frame.submatrix (omitRow omitted) id).det ^ 2 := by
  simp only [Fin.sum_univ_four, omitRow, Matrix.det_fin_three, Matrix.submatrix_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, id_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-! ## The level collapse

A principal block of `V Vᵀ` strictly wider than `V` is singular.  Cauchy-Binet
moves the top level total across to `Vᵀ V`, where the level exceeds the index card
and the powerset is empty.  No rank theory is used. -/

/-- A submatrix of `frame * frameᵀ` along a row pick is the picked frame's own
Gram, at any index type.  The `Fin`-indexed version is `Gtz.submatrix_mul_transpose_eq`
and this is the same one-line proof without the finiteness. -/
theorem submatrix_mul_transpose_eq_general {rowType colType pickType : Type*} [Fintype colType]
    (frame : Matrix rowType colType ℝ) (pick : pickType → rowType) :
    (frame * frameᵀ).submatrix pick pick
      = (frame.submatrix pick id) * (frame.submatrix pick id)ᵀ := by
  ext leftIndex rightIndex
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id_eq]

/-- **THE LEVEL COLLAPSE.**  Every principal block of `frame * frameᵀ` of size
strictly larger than the number of columns is singular.  The proof is three
rewrites: the block is a Gram, the top principal-minor total of a Gram is its
determinant, and Cauchy-Binet sends that total to a level the column index cannot
reach. -/
theorem det_submatrix_mul_transpose_eq_zero_of_lt {rowCount colCount blockCount : ℕ}
    (frame : Matrix (Fin rowCount) (Fin colCount) ℝ) (pick : Fin blockCount → Fin rowCount)
    (hlt : colCount < blockCount) :
    ((frame * frameᵀ).submatrix pick pick).det = 0 := by
  have hgram := submatrix_mul_transpose_eq_general frame pick
  have htop :
      principalMinorTotal ((frame.submatrix pick id) * (frame.submatrix pick id)ᵀ) blockCount
        = ((frame.submatrix pick id) * (frame.submatrix pick id)ᵀ).det := by
    simpa using
      principalMinorTotal_card ((frame.submatrix pick id) * (frame.submatrix pick id)ᵀ)
  rw [hgram, ← htop, sum_det_principalMinors_mul_transpose_comm,
    principalMinorTotal_of_card_lt _ (by simpa using hlt)]

/-- The level total of a Gram block at exactly the column count is the small
Gram's determinant.  This is the companion of the collapse one level down, and it
is what turns four maximal minors into one three-by-three determinant. -/
theorem principalMinorTotal_submatrix_mul_transpose_eq_det {rowCount colCount blockCount : ℕ}
    (frame : Matrix (Fin rowCount) (Fin colCount) ℝ) (pick : Fin blockCount → Fin rowCount) :
    principalMinorTotal ((frame * frameᵀ).submatrix pick pick) colCount
      = ((frame.submatrix pick id)ᵀ * (frame.submatrix pick id)).det := by
  rw [submatrix_mul_transpose_eq_general, sum_det_principalMinors_mul_transpose_comm]
  simpa using
    principalMinorTotal_card ((frame.submatrix pick id)ᵀ * (frame.submatrix pick id))

/-! ## The complement frame at an excluded pair

`complementFrame` picks four rows of the scaled frame.  `complementGram` is their
Gram.  The covering hypothesis says the four picked labels are exactly the labels
other than the excluded pair. -/

/-- The four picked rows of the scaled frame, as a `4 × rank` matrix. -/
noncomputable def complementFrame (design : WeightedDesign size rank)
    (pick : Fin 4 → Fin size) : Matrix (Fin 4) (Fin rank) ℝ :=
  (scaledAtomRows design).submatrix pick id

/-- The Gram of the four picked rows, a `rank × rank` matrix. -/
noncomputable def complementGram (design : WeightedDesign size rank)
    (pick : Fin 4 → Fin size) : Matrix (Fin rank) (Fin rank) ℝ :=
  (complementFrame design pick)ᵀ * (complementFrame design pick)

/-- The projection entry is the pairing of two scaled rows.  This is the bridge
between the matrix language of the projection form and the vector language of the
identities above. -/
theorem dotProduct_scaledAtomRows (design : WeightedDesign size rank)
    (leftLabel rightLabel : Fin size) :
    scaledAtomRows design leftLabel ⬝ᵥ scaledAtomRows design rightLabel
      = projectionOfDesign design leftLabel rightLabel := by
  simp only [projectionOfDesign, Matrix.mul_apply, Matrix.transpose_apply, dotProduct]

/-- The complement Gram is the sum of the four picked outer forms. -/
theorem complementGram_eq_sum (design : WeightedDesign size rank) (pick : Fin 4 → Fin size) :
    complementGram design pick = ∑ slot : Fin 4, atomMatrix (scaledAtomRows design (pick slot)) := by
  rw [complementGram, complementFrame, transpose_mul_self_eq_sum_rows]
  refine Finset.sum_congr rfl fun slot _ => ?_
  congr 1

/-- **The picked rows exhaust the complement.**  An injective map from four slots
into six labels that avoids two named labels has exactly the other four as its
image.  Card counting alone. -/
theorem image_pick_eq_erase_pair {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    Finset.image pick Finset.univ = (Finset.univ.erase first).erase second := by
  classical
  have hsubset : Finset.image pick Finset.univ ⊆ (Finset.univ.erase first).erase second := by
    intro label hlabel
    obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp hlabel
    exact Finset.mem_erase.mpr ⟨hmissSecond slot,
      Finset.mem_erase.mpr ⟨hmissFirst slot, Finset.mem_univ _⟩⟩
  have hcardImage : (Finset.image pick Finset.univ).card = 4 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hcardTarget : ((Finset.univ.erase first).erase second).card = 4 := by
    have hcard := card_erase_pair_off (size := 6) hne
    simpa using hcard
  exact Finset.eq_of_subset_of_card_le hsubset (by rw [hcardImage, hcardTarget])

/-- **The complement Gram is the identity minus the excluded pair's two forms.**
Parseval says the six outer forms total the identity.  Deleting two of them leaves
the four the pick enumerates. -/
theorem complementGram_eq_one_sub_two_outer (design : WeightedDesign 6 rank)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    complementGram design pick
      = 1 - atomMatrix (scaledAtomRows design first)
          - atomMatrix (scaledAtomRows design second) := by
  classical
  have hparseval : ∑ label : Fin 6, atomMatrix (scaledAtomRows design label) = 1 := by
    rw [← transpose_mul_self_eq_sum_rows]
    exact transpose_mul_scaledAtomRows design
  have himage := image_pick_eq_erase_pair hinj hne hmissFirst hmissSecond
  have hsumImage : ∑ slot : Fin 4, atomMatrix (scaledAtomRows design (pick slot))
      = ∑ label ∈ Finset.image pick Finset.univ, atomMatrix (scaledAtomRows design label) := by
    rw [Finset.sum_image fun left _ right _ hlr => hinj hlr]
  have hsecondMem : second ∈ Finset.univ.erase first :=
    Finset.mem_erase.mpr ⟨fun hcontra => hne hcontra.symm, Finset.mem_univ _⟩
  have hsplitSecond : ∑ label ∈ Finset.univ.erase first,
        atomMatrix (scaledAtomRows design label)
      = atomMatrix (scaledAtomRows design second)
        + ∑ label ∈ (Finset.univ.erase first).erase second,
            atomMatrix (scaledAtomRows design label) :=
    (Finset.add_sum_erase _ _ hsecondMem).symm
  have hsplitFirst : ∑ label : Fin 6, atomMatrix (scaledAtomRows design label)
      = atomMatrix (scaledAtomRows design first)
        + ∑ label ∈ Finset.univ.erase first, atomMatrix (scaledAtomRows design label) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ first)).symm
  rw [complementGram_eq_sum, hsumImage, himage]
  rw [hsplitFirst, hsplitSecond] at hparseval
  rw [← hparseval]
  abel

/-! ## The four-block, computed

Everything above meets here.  The three-by-three identities give the level-three
symmetric function, the level collapse gives the top one, and the pair block gives
both. -/

/-- **THE COMPLEMENT DETERMINANT.**  The complement Gram's determinant is the
determinant of `1` minus the excluded pair's own `2 × 2` block:
`(1 - P a a) * (1 - P b b) - P a b ^ 2`.  Expanded, that is
`1 - P a a - P b b + pairMinorAt P a b`. -/
theorem det_complementGram_eq (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    (complementGram design pick).det
      = (1 - projectionOfDesign design first first)
          * (1 - projectionOfDesign design second second)
        - projectionOfDesign design first second ^ 2 := by
  rw [complementGram_eq_one_sub_two_outer design hinj hne hmissFirst hmissSecond,
    det_one_sub_two_outer, dotProduct_scaledAtomRows, dotProduct_scaledAtomRows,
    dotProduct_scaledAtomRows]

/-- The same determinant read through the landed pair minor. -/
theorem det_complementGram_eq_one_sub_sub_add (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    (complementGram design pick).det
      = 1 - projectionOfDesign design first first - projectionOfDesign design second second
        + pairMinorAt (projectionOfDesign design) first second := by
  rw [det_complementGram_eq design hinj hne hmissFirst hmissSecond, pairMinorAt]
  ring

/-- **THE FOUR-BLOCK IS SINGULAR.**  At every excluded pair, at every design of
rank three on six labels.  Four labels cannot be independent in space. -/
theorem det_complementBlock_eq_zero (design : WeightedDesign 6 3) (pick : Fin 4 → Fin 6) :
    ((projectionOfDesign design).submatrix pick pick).det = 0 := by
  rw [projectionOfDesign]
  exact det_submatrix_mul_transpose_eq_zero_of_lt (scaledAtomRows design) pick (by omega)

/-- **ONE MINUS THE FOUR-BLOCK IS SINGULAR TOO.**  The complement Gram sits a
sum of two rank-one forms away from the identity, and `det (1 - V Vᵀ)` equals
`det (1 - Vᵀ V)` at any shape.  So the four-block carries the eigenvalue `1`.

With `Gtz.det_complementBlock_eq_zero` this pins two of the four eigenvalues, `1`
and `0`, at every excluded pair — and neither proof mentions an eigenvalue. -/
theorem det_one_sub_complementBlock_eq_zero (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    ((1 : Matrix (Fin 4) (Fin 4) ℝ)
        - (projectionOfDesign design).submatrix pick pick).det = 0 := by
  have hblock : (projectionOfDesign design).submatrix pick pick
      = complementFrame design pick * (complementFrame design pick)ᵀ := by
    rw [projectionOfDesign, complementFrame]
    exact submatrix_mul_transpose_eq_general (scaledAtomRows design) pick
  have hcomm : ((1 : Matrix (Fin 4) (Fin 4) ℝ)
        - complementFrame design pick * (complementFrame design pick)ᵀ).det
      = ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (complementFrame design pick)ᵀ * complementFrame design pick).det := by
    have hleft : (1 : Matrix (Fin 4) (Fin 4) ℝ)
        - complementFrame design pick * (complementFrame design pick)ᵀ
        = 1 + (-(complementFrame design pick)) * (complementFrame design pick)ᵀ := by
      rw [Matrix.neg_mul]; abel
    have hright : (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (complementFrame design pick)ᵀ * complementFrame design pick
        = 1 + (complementFrame design pick)ᵀ * (-(complementFrame design pick)) := by
      rw [Matrix.mul_neg]; abel
    rw [hleft, hright, Matrix.det_one_add_mul_comm]
  rw [hblock, hcomm, ← complementGram,
    complementGram_eq_one_sub_two_outer design hinj hne hmissFirst hmissSecond]
  exact det_one_sub_one_sub_two_outer _ _

/-! ## The four principal minors

Each `3 × 3` principal minor of the four-block is a perfect square, and the four
total the complement Gram's determinant.  That is the explicit Cauchy-Binet
identity read at the design. -/

/-- The three-label pick that omits one of the four surviving slots. -/
def complementTriplePick (pick : Fin 4 → Fin size) (omitted : Fin 4) : Fin 3 → Fin size :=
  fun slot => pick (omitRow omitted slot)

/-- Every complement triple minor is a perfect square: the block is the Gram of a
square `3 × 3` frame. -/
theorem det_complementTriple_eq_sq (design : WeightedDesign size 3) (pick : Fin 4 → Fin size)
    (omitted : Fin 4) :
    ((projectionOfDesign design).submatrix (complementTriplePick pick omitted)
        (complementTriplePick pick omitted)).det
      = ((scaledAtomRows design).submatrix (complementTriplePick pick omitted) id).det ^ 2 := by
  rw [projectionOfDesign, submatrix_mul_transpose_eq_general, Matrix.det_mul,
    Matrix.det_transpose]
  ring

/-- Every complement triple minor is non-negative. -/
theorem det_complementTriple_nonneg (design : WeightedDesign size 3) (pick : Fin 4 → Fin size)
    (omitted : Fin 4) :
    0 ≤ ((projectionOfDesign design).submatrix (complementTriplePick pick omitted)
        (complementTriplePick pick omitted)).det := by
  rw [det_complementTriple_eq_sq]
  exact sq_nonneg _

/-- **THE FOUR MINORS TOTAL THE COMPLEMENT DETERMINANT.**  Explicit Cauchy-Binet
at four rows and three columns, read at the design. -/
theorem sum_det_complementTriple_eq (design : WeightedDesign size 3) (pick : Fin 4 → Fin size) :
    ∑ omitted : Fin 4,
        ((projectionOfDesign design).submatrix (complementTriplePick pick omitted)
          (complementTriplePick pick omitted)).det
      = (complementGram design pick).det := by
  have hframe : ∀ omitted : Fin 4,
      (scaledAtomRows design).submatrix (complementTriplePick pick omitted) id
        = (complementFrame design pick).submatrix (omitRow omitted) id := by
    intro omitted
    ext row col
    rfl
  rw [complementGram, det_transpose_mul_fourThree]
  refine Finset.sum_congr rfl fun omitted _ => ?_
  rw [det_complementTriple_eq_sq, hframe]

/-! ## The cap, the mean, and the no-go

The complement determinant never passes one.  So the four minors never average
past a quarter, and the averaged determinant cell — which needs a third once the
two heaviest labels are excluded — can never fire through the mean. -/

/-- The complement determinant is capped by the excluded pair's own slack
product, hence by one.  The pairing enters only with a minus sign. -/
theorem det_complementGram_le_slack_product (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    (complementGram design pick).det
      ≤ (1 - projectionOfDesign design first first)
        * (1 - projectionOfDesign design second second) := by
  rw [det_complementGram_eq design hinj hne hmissFirst hmissSecond]
  nlinarith [sq_nonneg (projectionOfDesign design first second)]

/-- **THE CAP.**  The complement determinant never passes one, because both
excluded leverages lie in the unit interval. -/
theorem det_complementGram_le_one (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    (complementGram design pick).det ≤ 1 := by
  obtain ⟨hfirstLow, hfirstHigh⟩ := projectionDiagonal_mem_unitInterval design first
  obtain ⟨hsecondLow, hsecondHigh⟩ := projectionDiagonal_mem_unitInterval design second
  have hcap := det_complementGram_le_slack_product design hinj hne hmissFirst hmissSecond
  nlinarith

/-- **THE MEAN NEVER PASSES A QUARTER.**  Four non-negative minors totalling at
most one. -/
theorem complementMean_le_quarter (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    (complementGram design pick).det / 4 ≤ 1 / 4 := by
  have hcap := det_complementGram_le_one design hinj hne hmissFirst hmissSecond
  linarith

/-- **THE NO-GO.**  The averaged complement threshold never reaches a third.

Excluding the two heaviest labels leaves four whose weights are each at most a
third, so the averaged determinant cell would need `det / 4 > 1 / 3`.  The mean is
capped at a quarter.  The complement half of the pair marginal is closed, exactly
as `Gtz.not_pairGapReaches_cell_threshold` closed the through-pair half. -/
theorem not_complementMean_gt_third (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    ¬ (1 / 3 : ℝ) < (complementGram design pick).det / 4 := by
  have hmean := complementMean_le_quarter design hinj hne hmissFirst hmissSecond
  intro hcontra
  linarith

/-- The averaging existence step, kept for the record: some complement triple
carries at least the mean.  It is sound, and by the no-go above its threshold is
never enough. -/
theorem exists_det_complementTriple_ge_mean (design : WeightedDesign 6 3)
    (pick : Fin 4 → Fin 6) :
    ∃ omitted : Fin 4,
      (complementGram design pick).det / 4
        ≤ ((projectionOfDesign design).submatrix (complementTriplePick pick omitted)
          (complementTriplePick pick omitted)).det := by
  classical
  by_contra hcontra
  simp only [not_exists, not_le] at hcontra
  have hstrict : ∑ omitted : Fin 4,
      ((projectionOfDesign design).submatrix (complementTriplePick pick omitted)
        (complementTriplePick pick omitted)).det
      < ∑ _omitted : Fin 4, (complementGram design pick).det / 4 := by
    refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun omitted _ => hcontra omitted
  rw [sum_det_complementTriple_eq] at hstrict
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hstrict
  linarith

/-! ## The mean is attained, so no symmetric-function bound beats it

The four minors are the squared maximal minors of the four-by-three complement
frame.  When the four surviving atoms add to zero, deleting any one of them
leaves a determinant of the same magnitude, so the four minors are EQUAL and each
is exactly the mean.  Hence no lower bound written in the block's symmetric
functions can improve on `det / 4`. -/

/-- Four vectors of `ℝ³` that add to zero have maximal minors of equal magnitude:
deleting any one leaves the same determinant up to sign. -/
theorem sq_det_omitRow_eq_of_sum_eq_zero (frame : Matrix (Fin 4) (Fin 3) ℝ)
    (hsum : ∀ coord : Fin 3, frame 0 coord + frame 1 coord + frame 2 coord + frame 3 coord = 0)
    (leftOmit rightOmit : Fin 4) :
    (frame.submatrix (omitRow leftOmit) id).det ^ 2
      = (frame.submatrix (omitRow rightOmit) id).det ^ 2 := by
  have hzero : ∀ coord : Fin 3,
      frame 3 coord = -(frame 0 coord) - frame 1 coord - frame 2 coord := by
    intro coord
    have := hsum coord
    linarith
  have hcase : ∀ slot : Fin 4, slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by decide
  rcases hcase leftOmit with rfl | rfl | rfl | rfl <;>
    rcases hcase rightOmit with rfl | rfl | rfl | rfl <;>
    simp only [omitRow, Matrix.det_fin_three, Matrix.submatrix_apply, id_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, hzero] <;> ring

/-- **THE MEAN IS ATTAINED.**  When the four surviving atoms add to zero, every
complement triple minor equals exactly a quarter of the complement determinant.

So the averaging bound `det / 4` is sharp on that locus, and **no lower bound on
the largest complement minor written in the four-block's symmetric functions can
beat the mean.**  The four minors are then all equal, and the symmetric functions
cannot tell them apart. -/
theorem det_complementTriple_eq_quarter_of_sum_eq_zero (design : WeightedDesign size 3)
    (pick : Fin 4 → Fin size)
    (hsum : ∀ coord : Fin 3,
      complementFrame design pick 0 coord + complementFrame design pick 1 coord
        + complementFrame design pick 2 coord + complementFrame design pick 3 coord = 0)
    (omitted : Fin 4) :
    ((projectionOfDesign design).submatrix (complementTriplePick pick omitted)
        (complementTriplePick pick omitted)).det
      = (complementGram design pick).det / 4 := by
  classical
  have hframe : ∀ slot : Fin 4,
      (scaledAtomRows design).submatrix (complementTriplePick pick slot) id
        = (complementFrame design pick).submatrix (omitRow slot) id := by
    intro slot
    ext row col
    rfl
  have hall : ∀ slot : Fin 4,
      ((projectionOfDesign design).submatrix (complementTriplePick pick slot)
          (complementTriplePick pick slot)).det
        = ((projectionOfDesign design).submatrix (complementTriplePick pick omitted)
          (complementTriplePick pick omitted)).det := by
    intro slot
    rw [det_complementTriple_eq_sq, det_complementTriple_eq_sq, hframe, hframe]
    exact sq_det_omitRow_eq_of_sum_eq_zero _ hsum slot omitted
  have htotal := sum_det_complementTriple_eq design pick
  rw [Finset.sum_congr rfl fun slot _ => hall slot] at htotal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
  push_cast at htotal
  linarith

/-- **THE COMPLEMENT ROUTE IS CLOSED.**  On the zero-sum locus the largest
complement minor is exactly the mean, and the mean never passes a quarter.  So the
determinant cell, which needs a third at the four lightest labels, cannot fire
through any complement triple there. -/
theorem det_complementTriple_le_quarter_of_sum_eq_zero (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second)
    (hsum : ∀ coord : Fin 3,
      complementFrame design pick 0 coord + complementFrame design pick 1 coord
        + complementFrame design pick 2 coord + complementFrame design pick 3 coord = 0)
    (omitted : Fin 4) :
    ((projectionOfDesign design).submatrix (complementTriplePick pick omitted)
        (complementTriplePick pick omitted)).det ≤ 1 / 4 := by
  rw [det_complementTriple_eq_quarter_of_sum_eq_zero design pick hsum omitted]
  exact complementMean_le_quarter design hinj hne hmissFirst hmissSecond

/-! ## The two halves of the pair marginal are complementary pair minors

The through-pair marginal of the projection totals `pairMinorAt P a b`, by the
landed `Gtz.sum_det_tripleBlock_erase`.  The complement marginal totals
`pairMinorAt (1 - P) a b`.  So the pair marginal splits into the pair minors of
the two complementary projections, and neither half sees the four surviving
labels at all. -/

/-- **THE DUALITY.**  The complement determinant is the pair minor of the
complementary projection at the excluded pair. -/
theorem det_complementGram_eq_pairMinorAt_one_sub (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    (complementGram design pick).det
      = pairMinorAt (1 - projectionOfDesign design) first second := by
  have hoff : (1 - projectionOfDesign design) first second
      = -projectionOfDesign design first second := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne]
    ring
  rw [det_complementGram_eq design hinj hne hmissFirst hmissSecond, pairMinorAt, hoff,
    Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_eq]
  ring

/-! ## The complement sum, and the four-block's full symmetric data -/

/-- **THE COMPLEMENT SUM.**  Summing any weight over the four picked labels is
summing over all six and deleting the excluded pair.  The scalar companion of
`Gtz.complementGram_eq_one_sub_two_outer`. -/
theorem sum_pick_eq_sum_sub_sub
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second)
    (weightOf : Fin 6 → ℝ) :
    ∑ slot : Fin 4, weightOf (pick slot)
      = (∑ label : Fin 6, weightOf label) - weightOf first - weightOf second := by
  classical
  have himage := image_pick_eq_erase_pair hinj hne hmissFirst hmissSecond
  have hsumImage : ∑ slot : Fin 4, weightOf (pick slot)
      = ∑ label ∈ Finset.image pick Finset.univ, weightOf label := by
    rw [Finset.sum_image fun left _ right _ hlr => hinj hlr]
  have hsecondMem : second ∈ Finset.univ.erase first :=
    Finset.mem_erase.mpr ⟨fun hcontra => hne hcontra.symm, Finset.mem_univ _⟩
  have hsplitSecond : ∑ label ∈ Finset.univ.erase first, weightOf label
      = weightOf second + ∑ label ∈ (Finset.univ.erase first).erase second, weightOf label :=
    (Finset.add_sum_erase _ _ hsecondMem).symm
  have hsplitFirst : ∑ label : Fin 6, weightOf label
      = weightOf first + ∑ label ∈ Finset.univ.erase first, weightOf label :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ first)).symm
  rw [hsumImage, himage, hsplitFirst, hsplitSecond]
  ring

/-- **LEVEL ONE.**  The four-block's trace is the rank minus the two excluded
leverages. -/
theorem principalMinorTotal_one_complementBlock (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    principalMinorTotal ((projectionOfDesign design).submatrix pick pick) 1
      = 3 - projectionOfDesign design first first
        - projectionOfDesign design second second := by
  have htrace : ∑ label : Fin 6, projectionOfDesign design label label = 3 := by
    have hraw := trace_projectionOfDesign design
    simpa [Matrix.trace, Matrix.diag_apply] using hraw
  rw [principalMinorTotal_one, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  rw [sum_pick_eq_sum_sub_sub hinj hne hmissFirst hmissSecond
    fun label => projectionOfDesign design label label, htrace]

/-- **LEVEL FOUR.**  The four-block's determinant vanishes, restated as a level
total for composition with the signed expansion. -/
theorem principalMinorTotal_four_complementBlock (design : WeightedDesign 6 3)
    (pick : Fin 4 → Fin 6) :
    principalMinorTotal ((projectionOfDesign design).submatrix pick pick) 4 = 0 := by
  have hdet := det_complementBlock_eq_zero design pick
  have hcard :
      principalMinorTotal ((projectionOfDesign design).submatrix pick pick) 4
        = ((projectionOfDesign design).submatrix pick pick).det := by
    simpa using principalMinorTotal_card ((projectionOfDesign design).submatrix pick pick)
  rw [hcard, hdet]

/-- **LEVEL THREE.**  The four-block's third symmetric function is the complement
Gram's determinant, hence the complementary pair minor. -/
theorem principalMinorTotal_three_complementBlock (design : WeightedDesign 6 3)
    (pick : Fin 4 → Fin 6) :
    principalMinorTotal ((projectionOfDesign design).submatrix pick pick) 3
      = (complementGram design pick).det := by
  rw [projectionOfDesign, principalMinorTotal_submatrix_mul_transpose_eq_det, complementGram,
    complementFrame]

/-- **LEVEL TWO, FROM THE TWO SINGULARITIES.**  The signed level expansion of
`det (M - 1)` at four labels reads `e₀ - e₁ + e₂ - e₃ + e₄`.  Both singularities
kill the left side and the top level, so the second symmetric function is forced:
`e₂ = e₁ + e₃ - 1`.  No new computation enters. -/
theorem principalMinorTotal_two_complementBlock (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    principalMinorTotal ((projectionOfDesign design).submatrix pick pick) 2
      = principalMinorTotal ((projectionOfDesign design).submatrix pick pick) 1
        + principalMinorTotal ((projectionOfDesign design).submatrix pick pick) 3 - 1 := by
  set block := (projectionOfDesign design).submatrix pick pick with hblock
  have hexpand := det_sub_one_eq_sum_signed_principalMinorTotal block
  have hcard : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
  rw [hcard] at hexpand
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hexpand
  have hflip : (block - 1).det = ((1 : Matrix (Fin 4) (Fin 4) ℝ) - block).det := by
    rw [show block - 1 = -((1 : Matrix (Fin 4) (Fin 4) ℝ) - block) by abel, Matrix.det_neg]
    norm_num
  have hzero : ((1 : Matrix (Fin 4) (Fin 4) ℝ) - block).det = 0 :=
    det_one_sub_complementBlock_eq_zero design hinj hne hmissFirst hmissSecond
  have htop : principalMinorTotal block 4 = 0 :=
    principalMinorTotal_four_complementBlock design pick
  rw [hflip, hzero, principalMinorTotal_zero, htop] at hexpand
  norm_num at hexpand
  simp only [principalMinorTotal_one]
  linarith

/-- **THE NONTRIVIAL SPECTRUM IS THE EXCLUDED PAIR'S.**  Deleting the forced
eigenvalues `1` and `0` leaves a pair whose sum and product are exactly the trace
and determinant of `1` minus the excluded pair's own `2 × 2` block.  So the whole
four-block is a function of four numbers read off the two DELETED labels. -/
theorem sum_nontrivial_eigenvalues_complementBlock (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    principalMinorTotal ((projectionOfDesign design).submatrix pick pick) 1 - 1
      = (1 - projectionOfDesign design first first)
        + (1 - projectionOfDesign design second second) := by
  rw [principalMinorTotal_one_complementBlock design hinj hne hmissFirst hmissSecond]
  ring

/-- **THE DISCRIMINANT IS A SUM OF SQUARES.**  The two remaining eigenvalues are
real and coincide exactly when the excluded leverages agree and the excluded
pairing vanishes.  Explicit, and closed by `ring`. -/
theorem discriminant_complementBlock (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    ((1 - projectionOfDesign design first first)
        + (1 - projectionOfDesign design second second)) ^ 2
      - 4 * (complementGram design pick).det
      = (projectionOfDesign design first first - projectionOfDesign design second second) ^ 2
        + 4 * projectionOfDesign design first second ^ 2 := by
  rw [det_complementGram_eq design hinj hne hmissFirst hmissSecond]
  ring

/-! ## The weight floor at the two heaviest labels, and the closed route -/

/-- **THE THIRD IS FORCED.**  A label no heavier than two other distinct labels
carries at most a third of the total weight.  Three positive weights out of six
cannot all pass a third. -/
theorem weight_le_third_of_le_two (design : WeightedDesign 6 rank)
    {first second other : Fin 6} (hne : first ≠ second)
    (hotherFirst : other ≠ first) (hotherSecond : other ≠ second)
    (hfirst : design.weight other ≤ design.weight first)
    (hsecond : design.weight other ≤ design.weight second) :
    design.weight other ≤ 1 / 3 := by
  classical
  have hsubset : ({first, second, other} : Finset (Fin 6)) ⊆ Finset.univ := Finset.subset_univ _
  have hnonneg : ∀ label ∈ Finset.univ, label ∉ ({first, second, other} : Finset (Fin 6)) →
      0 ≤ design.weight label := fun label _ _ => (design.weight_pos label).le
  have hpart : ∑ label ∈ ({first, second, other} : Finset (Fin 6)), design.weight label
      ≤ ∑ label : Fin 6, design.weight label :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have hsecondMem : second ∉ ({other} : Finset (Fin 6)) := by
    simp only [Finset.mem_singleton]
    exact fun hcontra => hotherSecond hcontra.symm
  have hfirstMem : first ∉ ({second, other} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun hcontra => hcontra.elim hne fun hsame => hotherFirst hsame.symm
  rw [Finset.sum_insert hfirstMem, Finset.sum_insert hsecondMem, Finset.sum_singleton,
    design.weight_sum_one] at hpart
  linarith

/-- **THE COMPLEMENT ROUTE IS CLOSED.**  Delete the two heaviest labels.  The four
survivors then each carry at most a third of the weight, so the averaged
determinant cell needs a complement minor above a third.  The four minors average
at most a quarter, so the averaged step never delivers one.

This is the complement half of the pair marginal.  The through-pair half is closed
by `Gtz.not_pairGapReaches_cell_threshold`, whose own threshold needs a pair minor
above two thirds while none passes two fifths.  Both halves of the pair marginal
are now refuted, from opposite ends. -/
theorem not_complementMean_reaches_weight_floor (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second)
    (hheaviestFirst : ∀ slot, design.weight (pick slot) ≤ design.weight first)
    (hheaviestSecond : ∀ slot, design.weight (pick slot) ≤ design.weight second) :
    (∀ slot : Fin 4, design.weight (pick slot) ≤ 1 / 3)
      ∧ (complementGram design pick).det / 4 ≤ 1 / 4
      ∧ ¬ (1 / 3 : ℝ) < (complementGram design pick).det / 4 := by
  refine ⟨fun slot => weight_le_third_of_le_two design hne (hmissFirst slot) (hmissSecond slot)
    (hheaviestFirst slot) (hheaviestSecond slot),
    complementMean_le_quarter design hinj hne hmissFirst hmissSecond,
    not_complementMean_gt_third design hinj hne hmissFirst hmissSecond⟩

/-- The averaged complement threshold is capped by a quarter while the weight floor
it must beat sits at a third.  The gap is `1 / 12` and it never closes. -/
theorem complementMean_lt_weight_floor_gap (design : WeightedDesign 6 3)
    {pick : Fin 4 → Fin 6} (hinj : Function.Injective pick)
    {first second : Fin 6} (hne : first ≠ second)
    (hmissFirst : ∀ slot, pick slot ≠ first) (hmissSecond : ∀ slot, pick slot ≠ second) :
    (complementGram design pick).det / 4 + 1 / 12 ≤ 1 / 3 := by
  have hmean := complementMean_le_quarter design hinj hne hmissFirst hmissSecond
  linarith

end Gtz
