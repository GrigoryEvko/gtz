/-
# The gap determinant of a triple is its own reading minus the volume of the complement

At `(6, 3)` a triple and the three labels it omits carry the same amount of the
design.  This file prices that exchange exactly.

Write `A` for the frame whose columns are three atoms, `W` for the diagonal of
their three weights and `G = A^T A` for their Gram.  The weighted atom sum of the
triple is `A W A^T`, and the isotropy of the design says the weighted atom sum of
the triple plus the weighted atom sum of the complement is the identity.  Moving
the frame across the identity with Sylvester's determinant law gives

  `(u v w)_in * det G_in = det (1 - W_out G_out)` ,

with `(u v w)_in` the product of the three weights inside.  The right side is a
three by three determinant on the OMITTED labels alone.

Expanding it names two quantities.  The **split total** of a triple is

  `sum of the weighted leverages  -  sum of the weighted pair energies` ,

and the **complement volume** is the weight product of the omitted labels times
their Gram determinant.  The law then reads

  `volume_in + volume_out = 1 - splitTotal_out` ,

and the left side is symmetric, so `splitTotal_in = splitTotal_out`.  A triple
and its complement carry the same split total.  That is the exchange law, and it
holds with no positivity hypothesis and no genericity.

The consequence for the campaign target is one line.  The third Sylvester minor
of a triple gap is `det G - pairEnergySum + leverageSum - 1`, so

  `w_in * det (S_C - 1)
     = (1 - splitTotal_C - w_in * (pairEnergySum_C - leverageSum_C + 1))
       - volume of the complement` .

Every term of the bracket reads the triple itself.  The only entrance of the
omitted labels is one non-negative number, the complement volume.  So the gap
determinant of a triple is a self reading MINUS the volume the complement takes
away, and a triple whose complement is DEGENERATE reads its own sign exactly.

That last case is the complete graph on four vertices.  Its four dominating
triples are exactly the four vertex stars, and the complement of a star is a
triangle, whose three edges are dependent.  Section 9 lands that census: the
star at `5/4`, the triangle at `-49/4` and a triple carrying a matching pair at
`-1`, together with the vanishing of the star's complement bracket.

## What this file does NOT claim

It does not produce a positive gap determinant at an arbitrary design.  It
prices the determinant against one non-negative number and shows the price is
zero exactly when the complement is degenerate.

## Reconnaissance recorded in the campaign log

Eight hundred thousand adversarial descents over the whole `(6, 3)` design space,
four hundred thousand from uniform starts and four hundred thousand directed from
the two adversaries, never drove the largest of the twenty gap determinants to
zero or below.  The measured infimum is zero, and every approach to it is the
same boundary: a `(4, 3)` tie padded with two atoms whose weights go to zero.
Along that boundary the four surviving determinants stay strictly positive, of
the order of the vanishing weight.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.TripleGramSylvester

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Finset Matrix

/-! ## 1. The frame of a triple, its weight diagonal and its weighted atom sum -/

/-- **THE FRAME OF A TRIPLE.**  The three by three matrix whose COLUMNS are the
three vectors. -/
def tripleFrame (firstVec secondVec thirdVec : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun coord slot => (![firstVec, secondVec, thirdVec] slot) coord

/-- The diagonal matrix of three weights. -/
def tripleWeightDiag (firstWeight secondWeight thirdWeight : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![firstWeight, secondWeight, thirdWeight]

/-- **THE WEIGHTED ATOM SUM OF A TRIPLE.**  The share of the identity that three
labels of a design carry. -/
def weightedTripleSum (firstVec secondVec thirdVec : Fin 3 → ℝ)
    (firstWeight secondWeight thirdWeight : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  firstWeight • atomMatrix firstVec + secondWeight • atomMatrix secondVec
    + thirdWeight • atomMatrix thirdVec

theorem tripleFrame_apply (firstVec secondVec thirdVec : Fin 3 → ℝ) (coord slot : Fin 3) :
    tripleFrame firstVec secondVec thirdVec coord slot
      = (![firstVec, secondVec, thirdVec] slot) coord := rfl

/-- The Gram of a triple is the frame against itself. -/
theorem transpose_tripleFrame_mul_self (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    (tripleFrame firstVec secondVec thirdVec)ᵀ * tripleFrame firstVec secondVec thirdVec
      = tripleGram firstVec secondVec thirdVec := by
  ext rowSlot colSlot
  rw [Matrix.mul_apply, tripleGram_apply]
  simp only [Matrix.transpose_apply, tripleFrame_apply, dotProduct]

/-- **THE FRAME FACTORS THE WEIGHTED ATOM SUM.**  No hypothesis on the weights. -/
theorem tripleFrame_mul_weightDiag_mul_transpose (firstVec secondVec thirdVec : Fin 3 → ℝ)
    (firstWeight secondWeight thirdWeight : ℝ) :
    tripleFrame firstVec secondVec thirdVec
        * tripleWeightDiag firstWeight secondWeight thirdWeight
        * (tripleFrame firstVec secondVec thirdVec)ᵀ
      = weightedTripleSum firstVec secondVec thirdVec firstWeight secondWeight thirdWeight := by
  ext rowCoord colCoord
  fin_cases rowCoord <;> fin_cases colCoord <;>
    simp [Matrix.mul_apply, tripleFrame, tripleWeightDiag, weightedTripleSum, atomMatrix,
      Matrix.vecMulVec_apply, Matrix.diagonal_apply, Fin.sum_univ_three] <;> ring

/-- The determinant of a weight diagonal is the weight product. -/
theorem det_tripleWeightDiag (firstWeight secondWeight thirdWeight : ℝ) :
    (tripleWeightDiag firstWeight secondWeight thirdWeight).det
      = firstWeight * secondWeight * thirdWeight := by
  rw [tripleWeightDiag, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- The squared frame determinant is the Gram determinant. -/
theorem sq_det_tripleFrame (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    (tripleFrame firstVec secondVec thirdVec).det ^ 2
      = (tripleGram firstVec secondVec thirdVec).det := by
  rw [← transpose_tripleFrame_mul_self, Matrix.det_mul, Matrix.det_transpose, ← pow_two]

/-- **THE WEIGHTED ATOM SUM HAS THE WEIGHT PRODUCT AS ITS DETERMINANT FACTOR.** -/
theorem det_weightedTripleSum (firstVec secondVec thirdVec : Fin 3 → ℝ)
    (firstWeight secondWeight thirdWeight : ℝ) :
    (weightedTripleSum firstVec secondVec thirdVec firstWeight secondWeight thirdWeight).det
      = firstWeight * secondWeight * thirdWeight
        * (tripleGram firstVec secondVec thirdVec).det := by
  rw [← tripleFrame_mul_weightDiag_mul_transpose, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, det_tripleWeightDiag, ← sq_det_tripleFrame]
  ring

/-! ## 2. The Sylvester transfer

The frame moves across the identity, and the three by three determinant on the
coordinate side becomes a three by three determinant on the LABEL side. -/

/-- **THE SYLVESTER TRANSFER.**  The gap of a weighted atom sum against the
identity is the gap of the weight-scaled Gram, at any weights, with no
positivity and no invertibility. -/
theorem det_one_sub_weightedTripleSum (firstVec secondVec thirdVec : Fin 3 → ℝ)
    (firstWeight secondWeight thirdWeight : ℝ) :
    (1 - weightedTripleSum firstVec secondVec thirdVec
        firstWeight secondWeight thirdWeight).det
      = (1 - tripleWeightDiag firstWeight secondWeight thirdWeight
          * tripleGram firstVec secondVec thirdVec).det := by
  have hfactor := tripleFrame_mul_weightDiag_mul_transpose firstVec secondVec thirdVec
    firstWeight secondWeight thirdWeight
  have hassoc : tripleFrame firstVec secondVec thirdVec
      * tripleWeightDiag firstWeight secondWeight thirdWeight
      * (tripleFrame firstVec secondVec thirdVec)ᵀ
      = tripleFrame firstVec secondVec thirdVec
        * (tripleWeightDiag firstWeight secondWeight thirdWeight
          * (tripleFrame firstVec secondVec thirdVec)ᵀ) := Matrix.mul_assoc _ _ _
  have hswap : (1 - tripleFrame firstVec secondVec thirdVec
        * (tripleWeightDiag firstWeight secondWeight thirdWeight
          * (tripleFrame firstVec secondVec thirdVec)ᵀ)).det
      = (1 - tripleWeightDiag firstWeight secondWeight thirdWeight
          * (tripleFrame firstVec secondVec thirdVec)ᵀ
          * tripleFrame firstVec secondVec thirdVec).det :=
    Matrix.det_one_sub_mul_comm _ _
  rw [← hfactor, hassoc, hswap, Matrix.mul_assoc, transpose_tripleFrame_mul_self]

/-! ## 3. The complement volume law

The isotropy of a design splits the identity into the weighted atom sum of a
triple and the weighted atom sum of the three labels it omits.  Section 2 then
prices the first by a determinant read on the second. -/

/-- The weight product of a triple times its Gram determinant.  This is the
DPP mass of the triple, the object that totals to one over all triples. -/
noncomputable def tripleVolume (firstVec secondVec thirdVec : Fin 3 → ℝ)
    (firstWeight secondWeight thirdWeight : ℝ) : ℝ :=
  firstWeight * secondWeight * thirdWeight * (tripleGram firstVec secondVec thirdVec).det

/-- **THE COMPLEMENT VOLUME LAW.**  At a split of the identity into two weighted
triple sums, the volume of one triple is a determinant of the OTHER triple's
weight-scaled Gram.  No positivity, no genericity, no rank hypothesis beyond the
shape. -/
theorem tripleVolume_eq_det_one_sub_weightDiag_mul_gram
    (inFirst inSecond inThird outFirst outSecond outThird : Fin 3 → ℝ)
    (inWeightOne inWeightTwo inWeightThree outWeightOne outWeightTwo outWeightThree : ℝ)
    (hsplit : weightedTripleSum inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
        + weightedTripleSum outFirst outSecond outThird
            outWeightOne outWeightTwo outWeightThree = 1) :
    tripleVolume inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
      = (1 - tripleWeightDiag outWeightOne outWeightTwo outWeightThree
          * tripleGram outFirst outSecond outThird).det := by
  have hcomplement : weightedTripleSum inFirst inSecond inThird
      inWeightOne inWeightTwo inWeightThree
      = 1 - weightedTripleSum outFirst outSecond outThird
          outWeightOne outWeightTwo outWeightThree := by
    rw [eq_sub_iff_add_eq]; exact hsplit
  rw [tripleVolume, ← det_weightedTripleSum, hcomplement,
    det_one_sub_weightedTripleSum]

/-! ## 4. The expansion in shares and pair energies

The three by three determinant on the label side is a polynomial in the weighted
leverages, the weighted pair energies and the triple's own volume. -/

/-- The pair energy of two vectors: the squared area of the parallelogram they
span, written without a cross product. -/
def pairEnergy (leftVec rightVec : Fin 3 → ℝ) : ℝ :=
  leverageOf leftVec * leverageOf rightVec - (leftVec ⬝ᵥ rightVec) ^ 2

/-- **THE SPLIT TOTAL OF A TRIPLE.**  The weighted leverage total minus the
weighted pair energy total.  Section 5 shows a triple and its complement share
this number. -/
def splitTotal (firstVec secondVec thirdVec : Fin 3 → ℝ)
    (firstWeight secondWeight thirdWeight : ℝ) : ℝ :=
  (firstWeight * leverageOf firstVec + secondWeight * leverageOf secondVec
      + thirdWeight * leverageOf thirdVec)
    - (firstWeight * secondWeight * pairEnergy firstVec secondVec
      + firstWeight * thirdWeight * pairEnergy firstVec thirdVec
      + secondWeight * thirdWeight * pairEnergy secondVec thirdVec)

theorem tripleGram_diag (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    tripleGram firstVec secondVec thirdVec 0 0 = leverageOf firstVec
      ∧ tripleGram firstVec secondVec thirdVec 1 1 = leverageOf secondVec
      ∧ tripleGram firstVec secondVec thirdVec 2 2 = leverageOf thirdVec := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [tripleGram_apply] <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, leverageOf_eq_dotProduct]

theorem tripleGram_off (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    tripleGram firstVec secondVec thirdVec 0 1 = firstVec ⬝ᵥ secondVec
      ∧ tripleGram firstVec secondVec thirdVec 1 0 = firstVec ⬝ᵥ secondVec
      ∧ tripleGram firstVec secondVec thirdVec 0 2 = firstVec ⬝ᵥ thirdVec
      ∧ tripleGram firstVec secondVec thirdVec 2 0 = firstVec ⬝ᵥ thirdVec
      ∧ tripleGram firstVec secondVec thirdVec 1 2 = secondVec ⬝ᵥ thirdVec
      ∧ tripleGram firstVec secondVec thirdVec 2 1 = secondVec ⬝ᵥ thirdVec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [tripleGram_apply] <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;>
    try rw [dotProduct_comm]

/-- **THE GRAM DETERMINANT OF A TRIPLE, EXPANDED.**  Three leverages and three
pairings, with the oriented product carrying the only sign. -/
theorem det_tripleGram_eq (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    (tripleGram firstVec secondVec thirdVec).det
      = leverageOf firstVec * leverageOf secondVec * leverageOf thirdVec
        - leverageOf firstVec * (secondVec ⬝ᵥ thirdVec) ^ 2
        - leverageOf secondVec * (firstVec ⬝ᵥ thirdVec) ^ 2
        - leverageOf thirdVec * (firstVec ⬝ᵥ secondVec) ^ 2
        + 2 * (firstVec ⬝ᵥ secondVec) * (firstVec ⬝ᵥ thirdVec)
          * (secondVec ⬝ᵥ thirdVec) := by
  obtain ⟨hzero, hone, htwo⟩ := tripleGram_diag firstVec secondVec thirdVec
  obtain ⟨hab, hba, hac, hca, hbc, hcb⟩ := tripleGram_off firstVec secondVec thirdVec
  rw [Matrix.det_fin_three, hzero, hone, htwo, hab, hba, hac, hca, hbc, hcb]
  ring

/-- **THE LABEL-SIDE DETERMINANT, EXPANDED.**  One shares term, one pair energy
term, and the triple's own volume. -/
theorem det_one_sub_weightDiag_mul_gram (firstVec secondVec thirdVec : Fin 3 → ℝ)
    (firstWeight secondWeight thirdWeight : ℝ) :
    (1 - tripleWeightDiag firstWeight secondWeight thirdWeight
        * tripleGram firstVec secondVec thirdVec).det
      = 1 - splitTotal firstVec secondVec thirdVec firstWeight secondWeight thirdWeight
        - tripleVolume firstVec secondVec thirdVec firstWeight secondWeight thirdWeight := by
  obtain ⟨hzero, hone, htwo⟩ := tripleGram_diag firstVec secondVec thirdVec
  obtain ⟨hab, hba, hac, hca, hbc, hcb⟩ := tripleGram_off firstVec secondVec thirdVec
  have hdiagEntry : ∀ rowSlot colSlot : Fin 3,
      (tripleWeightDiag firstWeight secondWeight thirdWeight
          * tripleGram firstVec secondVec thirdVec) rowSlot colSlot
        = (![firstWeight, secondWeight, thirdWeight] rowSlot)
          * tripleGram firstVec secondVec thirdVec rowSlot colSlot := fun rowSlot colSlot => by
    rw [tripleWeightDiag, Matrix.diagonal_mul]
  have hsame : ∀ slot : Fin 3,
      (1 - tripleWeightDiag firstWeight secondWeight thirdWeight
          * tripleGram firstVec secondVec thirdVec) slot slot
        = 1 - (![firstWeight, secondWeight, thirdWeight] slot)
          * tripleGram firstVec secondVec thirdVec slot slot := fun slot => by
    rw [Matrix.sub_apply, Matrix.one_apply_eq, hdiagEntry]
  have hoff : ∀ rowSlot colSlot : Fin 3, rowSlot ≠ colSlot →
      (1 - tripleWeightDiag firstWeight secondWeight thirdWeight
          * tripleGram firstVec secondVec thirdVec) rowSlot colSlot
        = -((![firstWeight, secondWeight, thirdWeight] rowSlot)
          * tripleGram firstVec secondVec thirdVec rowSlot colSlot) := by
    intro rowSlot colSlot hne
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, hdiagEntry, zero_sub]
  rw [Matrix.det_fin_three, hsame 0, hsame 1, hsame 2,
    hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 0 (by decide),
    hoff 1 2 (by decide), hoff 2 0 (by decide), hoff 2 1 (by decide)]
  simp only [hzero, hone, htwo, hab, hba, hac, hca, hbc, hcb, splitTotal, tripleVolume,
    pairEnergy, det_tripleGram_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
  ring

/-! ## 5. The exchange law

The volume total of the two triples is symmetric, so the split total is the same
on both sides of the partition.  A triple and the three labels it omits carry
the same weighted leverage minus weighted pair energy. -/

/-- **THE VOLUME BUDGET.**  The two volumes total one minus the shared split
total. -/
theorem tripleVolume_add_tripleVolume
    (inFirst inSecond inThird outFirst outSecond outThird : Fin 3 → ℝ)
    (inWeightOne inWeightTwo inWeightThree outWeightOne outWeightTwo outWeightThree : ℝ)
    (hsplit : weightedTripleSum inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
        + weightedTripleSum outFirst outSecond outThird
            outWeightOne outWeightTwo outWeightThree = 1) :
    tripleVolume inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
        + tripleVolume outFirst outSecond outThird outWeightOne outWeightTwo outWeightThree
      = 1 - splitTotal outFirst outSecond outThird
          outWeightOne outWeightTwo outWeightThree := by
  have hlaw := tripleVolume_eq_det_one_sub_weightDiag_mul_gram inFirst inSecond inThird
    outFirst outSecond outThird inWeightOne inWeightTwo inWeightThree
    outWeightOne outWeightTwo outWeightThree hsplit
  rw [det_one_sub_weightDiag_mul_gram] at hlaw
  linarith [hlaw]

/-- **THE EXCHANGE LAW.**  A triple and its complement carry the SAME split
total.  This is one polynomial identity in the twelve readings of the two
triples, with no hypothesis beyond the isotropy split. -/
theorem splitTotal_eq_splitTotal_complement
    (inFirst inSecond inThird outFirst outSecond outThird : Fin 3 → ℝ)
    (inWeightOne inWeightTwo inWeightThree outWeightOne outWeightTwo outWeightThree : ℝ)
    (hsplit : weightedTripleSum inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
        + weightedTripleSum outFirst outSecond outThird
            outWeightOne outWeightTwo outWeightThree = 1) :
    splitTotal inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
      = splitTotal outFirst outSecond outThird outWeightOne outWeightTwo outWeightThree := by
  have hforward := tripleVolume_add_tripleVolume inFirst inSecond inThird
    outFirst outSecond outThird inWeightOne inWeightTwo inWeightThree
    outWeightOne outWeightTwo outWeightThree hsplit
  have hbackward := tripleVolume_add_tripleVolume outFirst outSecond outThird
    inFirst inSecond inThird outWeightOne outWeightTwo outWeightThree
    inWeightOne inWeightTwo inWeightThree (by rw [add_comm]; exact hsplit)
  linarith [hforward, hbackward]

/-- The mirror of the volume budget, with the split total read INSIDE. -/
theorem tripleVolume_add_tripleVolume_inside
    (inFirst inSecond inThird outFirst outSecond outThird : Fin 3 → ℝ)
    (inWeightOne inWeightTwo inWeightThree outWeightOne outWeightTwo outWeightThree : ℝ)
    (hsplit : weightedTripleSum inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
        + weightedTripleSum outFirst outSecond outThird
            outWeightOne outWeightTwo outWeightThree = 1) :
    tripleVolume inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
        + tripleVolume outFirst outSecond outThird outWeightOne outWeightTwo outWeightThree
      = 1 - splitTotal inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree := by
  rw [splitTotal_eq_splitTotal_complement inFirst inSecond inThird outFirst outSecond outThird
    inWeightOne inWeightTwo inWeightThree outWeightOne outWeightTwo outWeightThree hsplit]
  exact tripleVolume_add_tripleVolume inFirst inSecond inThird outFirst outSecond outThird
    inWeightOne inWeightTwo inWeightThree outWeightOne outWeightTwo outWeightThree hsplit

/-! ## 6. The gap determinant of a triple

The third Sylvester minor of a triple gap is the Gram determinant minus the pair
energy total plus the leverage total minus one.  Combining that with section 5
prices the gap determinant against the complement volume. -/

/-- The unweighted leverage total of a triple. -/
def leverageSum (firstVec secondVec thirdVec : Fin 3 → ℝ) : ℝ :=
  leverageOf firstVec + leverageOf secondVec + leverageOf thirdVec

/-- The unweighted pair energy total of a triple. -/
def pairEnergySum (firstVec secondVec thirdVec : Fin 3 → ℝ) : ℝ :=
  pairEnergy firstVec secondVec + pairEnergy firstVec thirdVec + pairEnergy secondVec thirdVec

/-- **THE THIRD MINOR IN VOLUME VOCABULARY.**  Every ingredient is a Gram
reading. -/
theorem det_tripleGram_sub_one_eq (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    (tripleGram firstVec secondVec thirdVec - 1).det
      = (tripleGram firstVec secondVec thirdVec).det
        - pairEnergySum firstVec secondVec thirdVec
        + leverageSum firstVec secondVec thirdVec - 1 := by
  obtain ⟨hzero, hone, htwo⟩ := tripleGram_diag firstVec secondVec thirdVec
  obtain ⟨hab, hba, hac, hca, hbc, hcb⟩ := tripleGram_off firstVec secondVec thirdVec
  have hsame : ∀ slot : Fin 3,
      (tripleGram firstVec secondVec thirdVec - 1) slot slot
        = tripleGram firstVec secondVec thirdVec slot slot - 1 := fun slot => by
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
  have hoff : ∀ rowSlot colSlot : Fin 3, rowSlot ≠ colSlot →
      (tripleGram firstVec secondVec thirdVec - 1) rowSlot colSlot
        = tripleGram firstVec secondVec thirdVec rowSlot colSlot := by
    intro rowSlot colSlot hne
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
  rw [Matrix.det_fin_three, hsame 0, hsame 1, hsame 2,
    hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 0 (by decide),
    hoff 1 2 (by decide), hoff 2 0 (by decide), hoff 2 1 (by decide),
    det_tripleGram_eq]
  simp only [hzero, hone, htwo, hab, hba, hac, hca, hbc, hcb, pairEnergySum, leverageSum,
    pairEnergy]
  ring

/-- **THE SELF READING OF A TRIPLE.**  Everything the triple can say about its
own gap determinant, before the complement takes its share. -/
def selfReading (firstVec secondVec thirdVec : Fin 3 → ℝ)
    (firstWeight secondWeight thirdWeight : ℝ) : ℝ :=
  1 - splitTotal firstVec secondVec thirdVec firstWeight secondWeight thirdWeight
    - firstWeight * secondWeight * thirdWeight
      * (pairEnergySum firstVec secondVec thirdVec
        - leverageSum firstVec secondVec thirdVec + 1)

/-- **THE PRICE OF THE GAP DETERMINANT.**  The weighted gap determinant of a
triple is its self reading minus the volume of the complement.

The self reading uses the triple's own weights, leverages and pairings only.  The
complement enters through ONE number, and that number is non-negative on every
real design because it is a weight product times a Gram determinant. -/
theorem weightProduct_mul_det_tripleGram_sub_one
    (inFirst inSecond inThird outFirst outSecond outThird : Fin 3 → ℝ)
    (inWeightOne inWeightTwo inWeightThree outWeightOne outWeightTwo outWeightThree : ℝ)
    (hsplit : weightedTripleSum inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
        + weightedTripleSum outFirst outSecond outThird
            outWeightOne outWeightTwo outWeightThree = 1) :
    inWeightOne * inWeightTwo * inWeightThree
        * (tripleGram inFirst inSecond inThird - 1).det
      = selfReading inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
        - tripleVolume outFirst outSecond outThird
            outWeightOne outWeightTwo outWeightThree := by
  have hbudget := tripleVolume_add_tripleVolume_inside inFirst inSecond inThird
    outFirst outSecond outThird inWeightOne inWeightTwo inWeightThree
    outWeightOne outWeightTwo outWeightThree hsplit
  rw [det_tripleGram_sub_one_eq, selfReading]
  have hvolume : tripleVolume inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
      = inWeightOne * inWeightTwo * inWeightThree
        * (tripleGram inFirst inSecond inThird).det := rfl
  rw [hvolume] at hbudget
  nlinarith [hbudget]

/-- **THE SIGN CRITERION.**  With a positive weight product, the gap determinant
of a triple is positive exactly when the complement volume falls below the self
reading.  Two invariants, one from each side of the partition. -/
theorem det_tripleGram_sub_one_pos_iff
    (inFirst inSecond inThird outFirst outSecond outThird : Fin 3 → ℝ)
    (inWeightOne inWeightTwo inWeightThree outWeightOne outWeightTwo outWeightThree : ℝ)
    (hweight : 0 < inWeightOne * inWeightTwo * inWeightThree)
    (hsplit : weightedTripleSum inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
        + weightedTripleSum outFirst outSecond outThird
            outWeightOne outWeightTwo outWeightThree = 1) :
    0 < (tripleGram inFirst inSecond inThird - 1).det
      ↔ tripleVolume outFirst outSecond outThird outWeightOne outWeightTwo outWeightThree
        < selfReading inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree := by
  have hprice := weightProduct_mul_det_tripleGram_sub_one inFirst inSecond inThird
    outFirst outSecond outThird inWeightOne inWeightTwo inWeightThree
    outWeightOne outWeightTwo outWeightThree hsplit
  constructor
  · intro hpos
    nlinarith [hprice, mul_pos hweight hpos]
  · intro hgap
    by_contra hnonpos
    push Not at hnonpos
    nlinarith [hprice, mul_nonneg hweight.le (neg_nonneg.mpr hnonpos)]

/-- **THE DEGENERATE COMPLEMENT READS THE SIGN EXACTLY.**  When the three omitted
atoms are dependent their volume is zero, and the triple's own reading is the
whole of its weighted gap determinant. -/
theorem weightProduct_mul_det_tripleGram_sub_one_of_degenerate
    (inFirst inSecond inThird outFirst outSecond outThird : Fin 3 → ℝ)
    (inWeightOne inWeightTwo inWeightThree outWeightOne outWeightTwo outWeightThree : ℝ)
    (hsplit : weightedTripleSum inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
        + weightedTripleSum outFirst outSecond outThird
            outWeightOne outWeightTwo outWeightThree = 1)
    (hdegenerate : (tripleGram outFirst outSecond outThird).det = 0) :
    inWeightOne * inWeightTwo * inWeightThree
        * (tripleGram inFirst inSecond inThird - 1).det
      = selfReading inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree := by
  have hprice := weightProduct_mul_det_tripleGram_sub_one inFirst inSecond inThird
    outFirst outSecond outThird inWeightOne inWeightTwo inWeightThree
    outWeightOne outWeightTwo outWeightThree hsplit
  have hzero : tripleVolume outFirst outSecond outThird
      outWeightOne outWeightTwo outWeightThree = 0 := by
    rw [tripleVolume, hdegenerate, mul_zero]
  rw [hzero, sub_zero] at hprice
  exact hprice

/-- **THE DEGENERATE COMPLEMENT SIGN TEST.**  A dependent complement turns the
sign question into one polynomial inequality in the triple's own data. -/
theorem det_tripleGram_sub_one_pos_of_degenerate_of_selfReading_pos
    (inFirst inSecond inThird outFirst outSecond outThird : Fin 3 → ℝ)
    (inWeightOne inWeightTwo inWeightThree outWeightOne outWeightTwo outWeightThree : ℝ)
    (hweight : 0 < inWeightOne * inWeightTwo * inWeightThree)
    (hsplit : weightedTripleSum inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree
        + weightedTripleSum outFirst outSecond outThird
            outWeightOne outWeightTwo outWeightThree = 1)
    (hdegenerate : (tripleGram outFirst outSecond outThird).det = 0)
    (hself : 0 < selfReading inFirst inSecond inThird inWeightOne inWeightTwo inWeightThree) :
    0 < (tripleGram inFirst inSecond inThird - 1).det := by
  have hexact := weightProduct_mul_det_tripleGram_sub_one_of_degenerate inFirst inSecond inThird
    outFirst outSecond outThird inWeightOne inWeightTwo inWeightThree
    outWeightOne outWeightTwo outWeightThree hsplit hdegenerate
  by_contra hnonpos
  push Not at hnonpos
  nlinarith [hexact, mul_nonneg hweight.le (neg_nonneg.mpr hnonpos)]

/-! ## 7. The design instance

A triple of labels of a `(6, 3)` design and the three labels it omits split the
isotropy, so every law of sections 3 thru 6 reads at a design. -/

/-- The weighted atom sum of three labels of a design. -/
theorem sum_triple_weight_smul_atomMatrix {size : ℕ} (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    ∑ label ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
        design.weight label • atomMatrix (design.atom label)
      = weightedTripleSum (design.atom firstLabel) (design.atom secondLabel)
          (design.atom thirdLabel) (design.weight firstLabel) (design.weight secondLabel)
          (design.weight thirdLabel) := by
  classical
  rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, weightedTripleSum,
    add_assoc]

/-- **THE ISOTROPY SPLIT AT A DESIGN.**  A triple and its complement partition
the resolution of the identity. -/
theorem weightedTripleSum_add_weightedTripleSum_of_partition
    (design : WeightedDesign 6 3)
    {inOne inTwo inThree outOne outTwo outThree : Fin 6}
    (hinOneTwo : inOne ≠ inTwo) (hinOneThree : inOne ≠ inThree) (hinTwoThree : inTwo ≠ inThree)
    (houtOneTwo : outOne ≠ outTwo) (houtOneThree : outOne ≠ outThree)
    (houtTwoThree : outTwo ≠ outThree)
    (hpartition : ({inOne, inTwo, inThree} : Finset (Fin 6))ᶜ = {outOne, outTwo, outThree}) :
    weightedTripleSum (design.atom inOne) (design.atom inTwo) (design.atom inThree)
        (design.weight inOne) (design.weight inTwo) (design.weight inThree)
      + weightedTripleSum (design.atom outOne) (design.atom outTwo) (design.atom outThree)
          (design.weight outOne) (design.weight outTwo) (design.weight outThree) = 1 := by
  classical
  have hin := sum_triple_weight_smul_atomMatrix design hinOneTwo hinOneThree hinTwoThree
  have hout := sum_triple_weight_smul_atomMatrix design houtOneTwo houtOneThree houtTwoThree
  have hcomplement := Finset.sum_add_sum_compl
    ({inOne, inTwo, inThree} : Finset (Fin 6))
    (fun label => design.weight label • atomMatrix (design.atom label))
  rw [hpartition] at hcomplement
  rw [← hin, ← hout, hcomplement]
  exact design.isParseval

/-- The gap determinant of a design triple is the Gram gap determinant. -/
theorem det_subsetSum_triple_sub_one_eq_det_tripleGram_sub_one {size : ℕ}
    (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    (subsetSum design ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)) - 1).det
      = (tripleGram (design.atom firstLabel) (design.atom secondLabel)
          (design.atom thirdLabel) - 1).det := by
  classical
  have hsum : subsetSum design ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size))
      = weightedTripleSum (design.atom firstLabel) (design.atom secondLabel)
          (design.atom thirdLabel) 1 1 1 := by
    rw [subsetSum, Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
      Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, weightedTripleSum]
    simp only [one_smul]
    rw [add_assoc]
  have hone : tripleWeightDiag (1 : ℝ) 1 1 = 1 := by
    rw [tripleWeightDiag]
    ext rowSlot colSlot
    rw [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with hmatch
    · subst hmatch; fin_cases rowSlot <;> norm_num
    · rfl
  have hneg : ∀ form : Matrix (Fin 3) (Fin 3) ℝ, (form - 1).det = -((1 - form).det) := by
    intro form
    rw [← neg_sub (1 : Matrix (Fin 3) (Fin 3) ℝ) form, Matrix.det_neg]
    norm_num
  rw [hsum, hneg, hneg, det_one_sub_weightedTripleSum, hone, Matrix.one_mul]

/-- **THE PRICE OF A DESIGN TRIPLE'S GAP DETERMINANT.**  The campaign object, at
a design, priced against the volume of the three labels it omits. -/
theorem weightProduct_mul_det_gap_eq_selfReading_sub_complementVolume
    (design : WeightedDesign 6 3)
    {inOne inTwo inThree outOne outTwo outThree : Fin 6}
    (hinOneTwo : inOne ≠ inTwo) (hinOneThree : inOne ≠ inThree) (hinTwoThree : inTwo ≠ inThree)
    (houtOneTwo : outOne ≠ outTwo) (houtOneThree : outOne ≠ outThree)
    (houtTwoThree : outTwo ≠ outThree)
    (hpartition : ({inOne, inTwo, inThree} : Finset (Fin 6))ᶜ = {outOne, outTwo, outThree}) :
    design.weight inOne * design.weight inTwo * design.weight inThree
        * (subsetSum design ({inOne, inTwo, inThree} : Finset (Fin 6)) - 1).det
      = selfReading (design.atom inOne) (design.atom inTwo) (design.atom inThree)
          (design.weight inOne) (design.weight inTwo) (design.weight inThree)
        - tripleVolume (design.atom outOne) (design.atom outTwo) (design.atom outThree)
            (design.weight outOne) (design.weight outTwo) (design.weight outThree) := by
  rw [det_subsetSum_triple_sub_one_eq_det_tripleGram_sub_one design hinOneTwo hinOneThree
    hinTwoThree]
  exact weightProduct_mul_det_tripleGram_sub_one _ _ _ _ _ _ _ _ _ _ _ _
    (weightedTripleSum_add_weightedTripleSum_of_partition design hinOneTwo hinOneThree
      hinTwoThree houtOneTwo houtOneThree houtTwoThree hpartition)

/-- The weight product of a triple of a design is strictly positive. -/
theorem tripleWeightProduct_pos {size : ℕ} (design : WeightedDesign size 3)
    (firstLabel secondLabel thirdLabel : Fin size) :
    0 < design.weight firstLabel * design.weight secondLabel * design.weight thirdLabel :=
  mul_pos (mul_pos (design.weight_pos firstLabel) (design.weight_pos secondLabel))
    (design.weight_pos thirdLabel)

/-- **THE DESIGN-LEVEL SIGN CRITERION.**  Two invariants at once: the self
reading of a triple and the volume of the triple it omits. -/
theorem det_gap_pos_iff_complementVolume_lt_selfReading (design : WeightedDesign 6 3)
    {inOne inTwo inThree outOne outTwo outThree : Fin 6}
    (hinOneTwo : inOne ≠ inTwo) (hinOneThree : inOne ≠ inThree) (hinTwoThree : inTwo ≠ inThree)
    (houtOneTwo : outOne ≠ outTwo) (houtOneThree : outOne ≠ outThree)
    (houtTwoThree : outTwo ≠ outThree)
    (hpartition : ({inOne, inTwo, inThree} : Finset (Fin 6))ᶜ = {outOne, outTwo, outThree}) :
    0 < (subsetSum design ({inOne, inTwo, inThree} : Finset (Fin 6)) - 1).det
      ↔ tripleVolume (design.atom outOne) (design.atom outTwo) (design.atom outThree)
            (design.weight outOne) (design.weight outTwo) (design.weight outThree)
        < selfReading (design.atom inOne) (design.atom inTwo) (design.atom inThree)
            (design.weight inOne) (design.weight inTwo) (design.weight inThree) := by
  rw [det_subsetSum_triple_sub_one_eq_det_tripleGram_sub_one design hinOneTwo hinOneThree
    hinTwoThree]
  exact det_tripleGram_sub_one_pos_iff _ _ _ _ _ _ _ _ _ _ _ _
    (tripleWeightProduct_pos design inOne inTwo inThree)
    (weightedTripleSum_add_weightedTripleSum_of_partition design hinOneTwo hinOneThree
      hinTwoThree houtOneTwo houtOneThree houtTwoThree hpartition)

/-- **THE EXCHANGE LAW AT A DESIGN.**  A triple and the three labels it omits
carry the same split total. -/
theorem splitTotal_eq_splitTotal_complement_design (design : WeightedDesign 6 3)
    {inOne inTwo inThree outOne outTwo outThree : Fin 6}
    (hinOneTwo : inOne ≠ inTwo) (hinOneThree : inOne ≠ inThree) (hinTwoThree : inTwo ≠ inThree)
    (houtOneTwo : outOne ≠ outTwo) (houtOneThree : outOne ≠ outThree)
    (houtTwoThree : outTwo ≠ outThree)
    (hpartition : ({inOne, inTwo, inThree} : Finset (Fin 6))ᶜ = {outOne, outTwo, outThree}) :
    splitTotal (design.atom inOne) (design.atom inTwo) (design.atom inThree)
        (design.weight inOne) (design.weight inTwo) (design.weight inThree)
      = splitTotal (design.atom outOne) (design.atom outTwo) (design.atom outThree)
          (design.weight outOne) (design.weight outTwo) (design.weight outThree) :=
  splitTotal_eq_splitTotal_complement _ _ _ _ _ _ _ _ _ _ _ _
    (weightedTripleSum_add_weightedTripleSum_of_partition design hinOneTwo hinOneThree
      hinTwoThree houtOneTwo houtOneThree houtTwoThree hpartition)

/-- **A DEGENERATE COMPLEMENT PRODUCES A STRICT WITNESS.**  A dependent
complementary triple plus a positive self reading gives a strictly positive gap
determinant, which is the object every landed tie refutation consumes. -/
theorem det_gap_pos_of_degenerate_complement (design : WeightedDesign 6 3)
    {inOne inTwo inThree outOne outTwo outThree : Fin 6}
    (hinOneTwo : inOne ≠ inTwo) (hinOneThree : inOne ≠ inThree) (hinTwoThree : inTwo ≠ inThree)
    (houtOneTwo : outOne ≠ outTwo) (houtOneThree : outOne ≠ outThree)
    (houtTwoThree : outTwo ≠ outThree)
    (hpartition : ({inOne, inTwo, inThree} : Finset (Fin 6))ᶜ = {outOne, outTwo, outThree})
    (hdegenerate : (tripleGram (design.atom outOne) (design.atom outTwo)
      (design.atom outThree)).det = 0)
    (hself : 0 < selfReading (design.atom inOne) (design.atom inTwo) (design.atom inThree)
      (design.weight inOne) (design.weight inTwo) (design.weight inThree)) :
    0 < (subsetSum design ({inOne, inTwo, inThree} : Finset (Fin 6)) - 1).det := by
  rw [det_subsetSum_triple_sub_one_eq_det_tripleGram_sub_one design hinOneTwo hinOneThree
    hinTwoThree]
  exact det_tripleGram_sub_one_pos_of_degenerate_of_selfReading_pos _ _ _ _ _ _ _ _ _ _ _ _
    (tripleWeightProduct_pos design inOne inTwo inThree)
    (weightedTripleSum_add_weightedTripleSum_of_partition design hinOneTwo hinOneThree
      hinTwoThree houtOneTwo houtOneThree houtTwoThree hpartition)
    hdegenerate hself

/-! ## 8. The uniform reading

At the campaign's crux stratum every weight is `1/6` and every leverage is `3`.
The price of section 6 then collapses to ONE linear statement in two numbers: the
squared pairing total of the triple and the Gram determinant of its complement. -/

/-- The squared pairing total of a triple. -/
def pairingEnergy (firstVec secondVec thirdVec : Fin 3 → ℝ) : ℝ :=
  (firstVec ⬝ᵥ secondVec) ^ 2 + (firstVec ⬝ᵥ thirdVec) ^ 2 + (secondVec ⬝ᵥ thirdVec) ^ 2

/-- **THE SELF READING AT UNIFORM WEIGHT AND LEVERAGE THREE.**  Two hundred
sixteen times the self reading is `35` minus five times the squared pairing
total. -/
theorem selfReading_uniform (firstVec secondVec thirdVec : Fin 3 → ℝ)
    (hfirst : leverageOf firstVec = 3) (hsecond : leverageOf secondVec = 3)
    (hthird : leverageOf thirdVec = 3) :
    selfReading firstVec secondVec thirdVec (1 / 6) (1 / 6) (1 / 6)
      = (35 - 5 * pairingEnergy firstVec secondVec thirdVec) / 216 := by
  simp only [selfReading, splitTotal, pairEnergySum, leverageSum, pairEnergy, pairingEnergy,
    hfirst, hsecond, hthird]
  ring

/-- **THE UNIFORM GAP DETERMINANT LAW.**  At weight `1/6` and leverage `3` the
gap determinant of a triple is `35`, minus five times its own squared pairing
total, minus the Gram determinant of the three labels it omits.

This is the whole `(6, 3)` uniform stratum in one line.  It reads exactly two
invariants, one from each side of the partition, and section 9 checks it against
both adversaries. -/
theorem det_gap_uniform_eq (design : WeightedDesign 6 3)
    {inOne inTwo inThree outOne outTwo outThree : Fin 6}
    (hinOneTwo : inOne ≠ inTwo) (hinOneThree : inOne ≠ inThree) (hinTwoThree : inTwo ≠ inThree)
    (houtOneTwo : outOne ≠ outTwo) (houtOneThree : outOne ≠ outThree)
    (houtTwoThree : outTwo ≠ outThree)
    (hpartition : ({inOne, inTwo, inThree} : Finset (Fin 6))ᶜ = {outOne, outTwo, outThree})
    (hweight : ∀ label : Fin 6, design.weight label = 1 / 6)
    (hleverage : ∀ label : Fin 6, leverageOf (design.atom label) = 3) :
    (subsetSum design ({inOne, inTwo, inThree} : Finset (Fin 6)) - 1).det
      = 35 - 5 * pairingEnergy (design.atom inOne) (design.atom inTwo) (design.atom inThree)
        - (tripleGram (design.atom outOne) (design.atom outTwo) (design.atom outThree)).det := by
  have hprice := weightProduct_mul_det_gap_eq_selfReading_sub_complementVolume design
    hinOneTwo hinOneThree hinTwoThree houtOneTwo houtOneThree houtTwoThree hpartition
  rw [hweight inOne, hweight inTwo, hweight inThree,
    selfReading_uniform _ _ _ (hleverage inOne) (hleverage inTwo) (hleverage inThree),
    tripleVolume, hweight outOne, hweight outTwo, hweight outThree] at hprice
  linarith [hprice]

/-- **THE UNIFORM SIGN CRITERION.**  Five times the squared pairing total of the
triple, plus the volume of its complement, decides the sign against the constant
`35`. -/
theorem det_gap_pos_iff_uniform (design : WeightedDesign 6 3)
    {inOne inTwo inThree outOne outTwo outThree : Fin 6}
    (hinOneTwo : inOne ≠ inTwo) (hinOneThree : inOne ≠ inThree) (hinTwoThree : inTwo ≠ inThree)
    (houtOneTwo : outOne ≠ outTwo) (houtOneThree : outOne ≠ outThree)
    (houtTwoThree : outTwo ≠ outThree)
    (hpartition : ({inOne, inTwo, inThree} : Finset (Fin 6))ᶜ = {outOne, outTwo, outThree})
    (hweight : ∀ label : Fin 6, design.weight label = 1 / 6)
    (hleverage : ∀ label : Fin 6, leverageOf (design.atom label) = 3) :
    0 < (subsetSum design ({inOne, inTwo, inThree} : Finset (Fin 6)) - 1).det
      ↔ 5 * pairingEnergy (design.atom inOne) (design.atom inTwo) (design.atom inThree)
          + (tripleGram (design.atom outOne) (design.atom outTwo)
              (design.atom outThree)).det < 35 := by
  rw [det_gap_uniform_eq design hinOneTwo hinOneThree hinTwoThree houtOneTwo houtOneThree
    houtTwoThree hpartition hweight hleverage]
  constructor
  · intro hpos; linarith [hpos]
  · intro hlow; linarith [hlow]

/-! ## 9. The complete graph on four vertices, as a kernel calibration

The six edges of `K4`, carried at leverage three, are the campaign's tightest
adversary.  Its four dominating triples are the four vertex STARS, and the
complement of a star is a TRIANGLE, whose three edges are dependent.  So the
degenerate branch of section 6 reads the whole census.

The vectors below are the six edge vectors scaled so that every leverage is
three.  The scale is irrational, but every quantity here depends on its SQUARE,
which is `3/2`.  With the labelling below the star is `{0, 2, 4}`, its complement
`{1, 3, 5}` is a triangle, and `{0, 1, 2}` carries the matching pair `{0, 1}`. -/

/-- The six edge vectors of `K4`, before the leverage scaling.  The three pairs
`{0,1}`, `{2,3}` and `{4,5}` are the three perfect matchings, and they are the
three orthogonal pairs. -/
def kFourEdge : Fin 6 → Fin 3 → ℝ :=
  ![![1, 1, 0], ![1, -1, 0], ![1, 0, 1], ![1, 0, -1], ![0, 1, 1], ![0, 1, -1]]

theorem kFourEdge_zero : kFourEdge 0 = ![1, 1, 0] := rfl
theorem kFourEdge_one : kFourEdge 1 = ![1, -1, 0] := rfl
theorem kFourEdge_two : kFourEdge 2 = ![1, 0, 1] := rfl
theorem kFourEdge_three : kFourEdge 3 = ![1, 0, -1] := rfl
theorem kFourEdge_four : kFourEdge 4 = ![0, 1, 1] := rfl
theorem kFourEdge_five : kFourEdge 5 = ![0, 1, -1] := rfl

/-- The scaled edge vectors. -/
noncomputable def kFourScaledEdge (scale : ℝ) (edge : Fin 6) : Fin 3 → ℝ :=
  fun coord => scale * kFourEdge edge coord

theorem kFourScaledEdge_dot (scale : ℝ) (leftEdge rightEdge : Fin 6) :
    kFourScaledEdge scale leftEdge ⬝ᵥ kFourScaledEdge scale rightEdge
      = scale ^ 2 * (kFourEdge leftEdge ⬝ᵥ kFourEdge rightEdge) := by
  simp only [kFourScaledEdge, dotProduct, Fin.sum_univ_three]
  ring

theorem kFourEdge_normSq (edge : Fin 6) : kFourEdge edge ⬝ᵥ kFourEdge edge = 2 := by
  fin_cases edge <;>
    norm_num [kFourEdge, kFourEdge_zero, kFourEdge_one, kFourEdge_two, kFourEdge_three,
      kFourEdge_four, kFourEdge_five, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem leverageOf_kFourScaledEdge (scale : ℝ) (hscale : scale ^ 2 = 3 / 2) (edge : Fin 6) :
    leverageOf (kFourScaledEdge scale edge) = 3 := by
  rw [leverageOf_eq_dotProduct, kFourScaledEdge_dot, kFourEdge_normSq, hscale]
  norm_num

theorem kFourEdge_dot_starPairs :
    kFourEdge 0 ⬝ᵥ kFourEdge 2 = 1 ∧ kFourEdge 0 ⬝ᵥ kFourEdge 4 = 1
      ∧ kFourEdge 2 ⬝ᵥ kFourEdge 4 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [kFourEdge_zero, kFourEdge_one, kFourEdge_two, kFourEdge_three, kFourEdge_four,
      kFourEdge_five, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem kFourEdge_dot_trianglePairs :
    kFourEdge 1 ⬝ᵥ kFourEdge 3 = 1 ∧ kFourEdge 1 ⬝ᵥ kFourEdge 5 = -1
      ∧ kFourEdge 3 ⬝ᵥ kFourEdge 5 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [kFourEdge_zero, kFourEdge_one, kFourEdge_two, kFourEdge_three, kFourEdge_four,
      kFourEdge_five, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem kFourEdge_dot_matchingPairs :
    kFourEdge 0 ⬝ᵥ kFourEdge 1 = 0 ∧ kFourEdge 0 ⬝ᵥ kFourEdge 2 = 1
      ∧ kFourEdge 1 ⬝ᵥ kFourEdge 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [kFourEdge_zero, kFourEdge_one, kFourEdge_two, kFourEdge_three, kFourEdge_four,
      kFourEdge_five, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **THE TRIANGLE OF `K4` IS DEGENERATE.**  Its three edge vectors are
dependent, so its Gram determinant vanishes.  This is the hypothesis the
degenerate branch of section 6 asks for. -/
theorem det_tripleGram_kFour_triangle (scale : ℝ) (hscale : scale ^ 2 = 3 / 2) :
    (tripleGram (kFourScaledEdge scale 1) (kFourScaledEdge scale 3)
      (kFourScaledEdge scale 5)).det = 0 := by
  obtain ⟨p13, p15, p35⟩ := kFourEdge_dot_trianglePairs
  rw [det_tripleGram_eq, leverageOf_kFourScaledEdge scale hscale 1,
    leverageOf_kFourScaledEdge scale hscale 3, leverageOf_kFourScaledEdge scale hscale 5,
    kFourScaledEdge_dot, kFourScaledEdge_dot, kFourScaledEdge_dot, p13, p15, p35, hscale]
  norm_num

/-- **THE STAR TRIPLE OF `K4` HAS GAP DETERMINANT `5/4`.**  Three edges through
one vertex, all three pairings `3/2`, oriented product positive. -/
theorem det_tripleGram_kFour_star_sub_one (scale : ℝ) (hscale : scale ^ 2 = 3 / 2) :
    (tripleGram (kFourScaledEdge scale 0) (kFourScaledEdge scale 2)
      (kFourScaledEdge scale 4) - 1).det = 5 / 4 := by
  obtain ⟨p02, p04, p24⟩ := kFourEdge_dot_starPairs
  rw [det_tripleGram_sub_one_eq, det_tripleGram_eq]
  simp only [pairEnergySum, leverageSum, pairEnergy, leverageOf_kFourScaledEdge scale hscale,
    kFourScaledEdge_dot, p02, p04, p24, hscale]
  norm_num

/-- **THE TRIANGLE TRIPLE OF `K4` HAS GAP DETERMINANT `-49/4`.**  The same three
pairing moduli as the star, with a NEGATIVE oriented product.  Nothing below the
determinant separates the two. -/
theorem det_tripleGram_kFour_triangle_sub_one (scale : ℝ) (hscale : scale ^ 2 = 3 / 2) :
    (tripleGram (kFourScaledEdge scale 1) (kFourScaledEdge scale 3)
      (kFourScaledEdge scale 5) - 1).det = -(49 / 4) := by
  obtain ⟨p13, p15, p35⟩ := kFourEdge_dot_trianglePairs
  rw [det_tripleGram_sub_one_eq, det_tripleGram_eq]
  simp only [pairEnergySum, leverageSum, pairEnergy, leverageOf_kFourScaledEdge scale hscale,
    kFourScaledEdge_dot, p13, p15, p35, hscale]
  norm_num

/-- **A TRIPLE CARRYING A MATCHING PAIR OF `K4` HAS GAP DETERMINANT `-1`.**  The
edges `0` and `1` are disjoint, so their pairing vanishes and the oriented
product is zero.  The determinant is still negative, so a vanishing bracket cycle
is NOT enough. -/
theorem det_tripleGram_kFour_matching_sub_one (scale : ℝ) (hscale : scale ^ 2 = 3 / 2) :
    (tripleGram (kFourScaledEdge scale 0) (kFourScaledEdge scale 1)
      (kFourScaledEdge scale 2) - 1).det = -1 := by
  obtain ⟨p01, p02, p12⟩ := kFourEdge_dot_matchingPairs
  rw [det_tripleGram_sub_one_eq, det_tripleGram_eq]
  simp only [pairEnergySum, leverageSum, pairEnergy, leverageOf_kFourScaledEdge scale hscale,
    kFourScaledEdge_dot, p01, p02, p12, hscale]
  norm_num

/-- **THE STAR READS ITS OWN SIGN.**  At `K4` the complement of the star is the
triangle, whose bracket vanishes, so section 6 gives the star determinant as its
self reading alone.  The number is `5/864`, and dividing by the weight product
`1/216` returns `5/4`. -/
theorem selfReading_kFour_star (scale : ℝ) (hscale : scale ^ 2 = 3 / 2) :
    selfReading (kFourScaledEdge scale 0) (kFourScaledEdge scale 2)
        (kFourScaledEdge scale 4) (1 / 6) (1 / 6) (1 / 6) = 5 / 864 := by
  obtain ⟨p02, p04, p24⟩ := kFourEdge_dot_starPairs
  rw [selfReading_uniform _ _ _ (leverageOf_kFourScaledEdge scale hscale 0)
    (leverageOf_kFourScaledEdge scale hscale 2) (leverageOf_kFourScaledEdge scale hscale 4)]
  simp only [pairingEnergy, kFourScaledEdge_dot, p02, p04, p24, hscale]
  norm_num

/-- **THE TIGHTNESS CERTIFICATE.**  The star determinant times the weight product
is exactly the self reading, and the complement volume is exactly zero.  So the
price of section 6 is attained at `K4`, and the criterion cannot be weakened at
that design. -/
theorem kFour_star_price (scale : ℝ) (hscale : scale ^ 2 = 3 / 2) :
    (1 / 6 : ℝ) * (1 / 6) * (1 / 6)
        * (tripleGram (kFourScaledEdge scale 0) (kFourScaledEdge scale 2)
            (kFourScaledEdge scale 4) - 1).det
      = selfReading (kFourScaledEdge scale 0) (kFourScaledEdge scale 2)
          (kFourScaledEdge scale 4) (1 / 6) (1 / 6) (1 / 6)
        - tripleVolume (kFourScaledEdge scale 1) (kFourScaledEdge scale 3)
            (kFourScaledEdge scale 5) (1 / 6) (1 / 6) (1 / 6) := by
  rw [det_tripleGram_kFour_star_sub_one scale hscale, selfReading_kFour_star scale hscale,
    tripleVolume, det_tripleGram_kFour_triangle scale hscale]
  norm_num

/-- **THE `K4` CENSUS, IN ONE STATEMENT.**  Star `5/4`, triangle `-49/4`,
matching triple `-1`, and the vanishing of the star's complement bracket.  The
star is the only positive one, and it is the only one whose complement is
degenerate. -/
theorem kFour_census (scale : ℝ) (hscale : scale ^ 2 = 3 / 2) :
    (tripleGram (kFourScaledEdge scale 0) (kFourScaledEdge scale 2)
        (kFourScaledEdge scale 4) - 1).det = 5 / 4
      ∧ (tripleGram (kFourScaledEdge scale 1) (kFourScaledEdge scale 3)
          (kFourScaledEdge scale 5) - 1).det = -(49 / 4)
      ∧ (tripleGram (kFourScaledEdge scale 0) (kFourScaledEdge scale 1)
          (kFourScaledEdge scale 2) - 1).det = -1
      ∧ (tripleGram (kFourScaledEdge scale 1) (kFourScaledEdge scale 3)
          (kFourScaledEdge scale 5)).det = 0 :=
  ⟨det_tripleGram_kFour_star_sub_one scale hscale,
    det_tripleGram_kFour_triangle_sub_one scale hscale,
    det_tripleGram_kFour_matching_sub_one scale hscale,
    det_tripleGram_kFour_triangle scale hscale⟩

end Gtz
