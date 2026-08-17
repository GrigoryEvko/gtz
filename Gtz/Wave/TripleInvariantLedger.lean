import Gtz.Wave.CertificateFreeMomentLaws
import Gtz.Quantitative.WindowPolarity
import Gtz.Design.StratumEmptinessLedger
import Gtz.Reduction.PolarGapDeterminant
import Gtz.Quantitative.RealnessEngine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The exact invariant ledger of the twenty triples, and the measure that sees angles

Three results live here, and the third closes a branch of the `(6,3)` case split.

## 1. The exact positivity criterion, sharpened

`Gtz.posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos` reads a Descartes sign rule off
the characteristic cubic and asks for all three coefficients STRICTLY positive.  Two of the
three strict signs are free.  At a nonpositive point the cubic term is already nonpositive,
the trace term is nonpositive when the trace is only WEAKLY positive, and the linear term is
nonpositive when the second invariant is only weakly positive.  So

    `0 ≤ e₁ ∧ 0 ≤ e₂ ∧ 0 < e₃  ⟹  M ≻ 0`

is `Gtz.posDef_of_invariants_nonneg_of_det_pos`.  The converse of the landed bridge is here
as well (`Gtz.invariants_pos_of_posDef`), so the criterion becomes an EQUIVALENCE
(`Gtz.posDef_iff_invariants_pos`).

The sharpening matters at `(6,3)`.  The leverage floor `Gtz.leverage_one_le_of_isTie_sixThree`
is unconditional, so at a tie every triple has `0 ≤ e₁(S_C − I)`.  Under the ORIGINAL bridge
each triple must fail one of three tests and `e₁ = 0` survives as a third branch.  Under the
sharpened bridge that branch disappears:

    at a tie, EVERY triple obeys `e₂(S_C − I) < 0  ∨  e₃(S_C − I) ≤ 0` .

That is `Gtz.secondInvariant_neg_or_det_nonpos_of_isTie`, a two-valued label on the twenty
triples with no escape clause.

## 2. The product measure carries NO information

Read on ORDERED index triples against the Parseval product measure `t_p t_l t_r`, the three
layer moments of the gap are universal constants,

    `Σ e₁(S_C − I) · t_p t_l t_r = 6` ,  `Σ e₂ · t_p t_l t_r = 3` ,  `Σ e₃ · t_p t_l t_r = −4` ,

at EVERY rank-three design and EVERY size (`Gtz.productLayer_gapTrace`,
`Gtz.productLayer_gapSecond`, `Gtz.productLayer_gapDet`).  No design data survives, and
`Gtz.productLayer_gap_moments_congr` states that as a congruence.  The determinant constant
is NEGATIVE, so a product-weighted determinant layer can never deliver a positive gap
determinant and that route is closed once and for all (`Gtz.productLayer_gapDet_neg`).

The unordered twenty-triple totals that the tree already carries differ from these constants
only by the degenerate index triples.  That difference is an artifact of the unordered
normalisation, not design information.

## 3. The volume measure DOES see angles, and it forces a sign

Weight each ordered triple by its squared bracket as well.  The bracket annihilates the
degenerate index triples, so this is volume sampling.  Three landed marginals collapse the
moments to

    `Σ 1 · w = 6` ,
    `Σ e₁(S_C − I) · w = 6 m − 18` ,
    `Σ e₂(S_C − I) · w = 3 p₂ − 12 m + 18` ,
    `Σ e₃(S_C − I) · w = b₄ − 3 p₂ + 6 m − 6` ,

with `w = t_p t_l t_r [p,l,r]²`, `m = Σ_c t_c ℓ_c²` (`Gtz.leverageSquareMoment`),
`p₂ = Σ_{d,e} t_d t_e ⟨d,e⟩²` (`Gtz.pairGramSecondMoment`) and
`b₄ = Σ_{p,l,r} t_p t_l t_r [p,l,r]⁴` (`Gtz.bracketFourthMoment`).

Two elementary square expansions pin two of the three.  `Σ_c t_c (ℓ_c − 3)² ≥ 0` gives
`9 ≤ m`, and `Σ_e t_e (⟨d,e⟩ − 2 ℓ_d)² ≥ 0` gives `4 m ≤ p₂`.  Hence

    `18 ≤ Σ e₂(S_C − I) · w`   (`Gtz.eighteen_le_volumeLayer_gapSecond`)

for every rank-three design, with NO hypothesis.  A positive total of terms each of which is
a positive weight times a squared bracket times a reading produces one term with a nonzero
bracket and a positive reading, and a nonzero bracket makes its three labels distinct.  So

    every rank-three design carries a SPANNING triple with `0 < e₂(S_C − I)`

(`Gtz.exists_spanning_triple_gapSecond_pos`).  At a `(6,3)` tie the two-valued label then
forces that triple onto the other branch
(`Gtz.exists_spanning_triple_gapDet_nonpos_of_isTie`).  The all-`e₂ < 0` label pattern is
refuted, so the case split over the twenty triples starts from a nonempty second branch.

The determinant moment does NOT close the same way, and this file says so.  The third square
expansion `Σ_r t_r ([p,l,r]² − ⟨p,l⟩)² ≥ 0` gives `p₂ ≤ b₄`
(`Gtz.pairGramSecondMoment_le_bracketFourthMoment`), which points the wrong way for
`b₄ − 3 p₂ + 6 m − 6`.  The determinant layer is not sign-forced.

## 4. The witness that the two measures differ

`Gtz.icosaDesign` and `Gtz.coordinateDiagonalDesign` are both landed `(6,3)` designs at
uniform weight `1/6` and uniform leverage `3`.  Their weight profiles agree label by label
and their leverage profiles agree label by label, so no functional of the profile alone can
tell them apart.  Their second pair moments are `216/5` and `351/8`
(`Gtz.pairGramSecondMoment_icosaDesign`, `Gtz.pairGramSecondMoment_coordinateDiagonalDesign`),
because the icosahedron is equiangular at squared cosine `1/5` while the tetrahedral edge
directions carry two different squared cosines, `0` and `1/4`.

So the product-measure gap second moment is `3` at both
(`Gtz.productLayer_gapSecond_agrees_at_the_witness`) while the volume-measure gap second
moment is `198/5` at one and `333/8` at the other
(`Gtz.volumeLayer_gapSecond_differs_at_the_witness`).  That is the exact sense in which the
volume measure reads an angle and the product measure does not.
-/

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## 1. The exact positivity criterion -/

/-- The quadratic form of a three-by-three matrix at an explicit vector, on entries. -/
theorem dotProduct_mulVec_fin_three (form : Matrix (Fin 3) (Fin 3) ℝ)
    (first second third : ℝ) :
    (![first, second, third] : Fin 3 → ℝ) ⬝ᵥ (form *ᵥ ![first, second, third])
      = form 0 0 * first ^ 2 + form 1 1 * second ^ 2 + form 2 2 * third ^ 2
        + (form 0 1 + form 1 0) * (first * second)
        + (form 0 2 + form 2 0) * (first * third)
        + (form 1 2 + form 2 1) * (second * third) := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- A positive definite matrix is symmetric on entries. -/
theorem entry_symm_of_posDef {form : Matrix (Fin 3) (Fin 3) ℝ} (hpos : form.PosDef)
    (rowIndex colIndex : Fin 3) : form colIndex rowIndex = form rowIndex colIndex := by
  have hbase := congrFun (congrFun hpos.1 rowIndex) colIndex
  simpa [Matrix.conjTranspose_apply] using hbase

/-- The quadratic form of a positive definite matrix is positive off the origin. -/
theorem posDef_quadratic_pos {form : Matrix (Fin 3) (Fin 3) ℝ} (hpos : form.PosDef)
    {probe : Fin 3 → ℝ} (hne : probe ≠ 0) : 0 < probe ⬝ᵥ (form *ᵥ probe) :=
  (Matrix.posDef_iff_dotProduct_mulVec.mp hpos).2 hne

/-- Every diagonal entry of a positive definite three-by-three matrix is positive. -/
theorem diagonal_pos_of_posDef {form : Matrix (Fin 3) (Fin 3) ℝ} (hpos : form.PosDef)
    (index : Fin 3) : 0 < form index index := by
  fin_cases index
  · have hne : (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hval := congrFun hzero 0
      simp at hval
    have hval := posDef_quadratic_pos hpos hne
    rw [dotProduct_mulVec_fin_three] at hval
    norm_num at hval
    exact hval
  · have hne : (![0, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hval := congrFun hzero 1
      simp at hval
    have hval := posDef_quadratic_pos hpos hne
    rw [dotProduct_mulVec_fin_three] at hval
    norm_num at hval
    exact hval
  · have hne : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hval := congrFun hzero 2
      simp at hval
    have hval := posDef_quadratic_pos hpos hne
    rw [dotProduct_mulVec_fin_three] at hval
    norm_num at hval
    exact hval

/-- The `(0,1)` principal minor of a positive definite three-by-three matrix is positive.
The probe is the vector at which the quadratic form equals the minor times the leading
entry. -/
theorem minorZeroOne_pos_of_posDef {form : Matrix (Fin 3) (Fin 3) ℝ} (hpos : form.PosDef) :
    0 < form 0 0 * form 1 1 - form 0 1 * form 1 0 := by
  have hlead := diagonal_pos_of_posDef hpos 0
  have hsym := entry_symm_of_posDef hpos 0 1
  have hne : (![form 0 1, -(form 0 0), 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hval := congrFun hzero 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Pi.zero_apply,
      neg_eq_zero] at hval
    exact absurd hval hlead.ne'
  have hval := posDef_quadratic_pos hpos hne
  rw [dotProduct_mulVec_fin_three] at hval
  nlinarith [hval, hlead, hsym]

/-- The `(0,2)` principal minor of a positive definite three-by-three matrix is positive. -/
theorem minorZeroTwo_pos_of_posDef {form : Matrix (Fin 3) (Fin 3) ℝ} (hpos : form.PosDef) :
    0 < form 0 0 * form 2 2 - form 0 2 * form 2 0 := by
  have hlead := diagonal_pos_of_posDef hpos 0
  have hsym := entry_symm_of_posDef hpos 0 2
  have hne : (![form 0 2, 0, -(form 0 0)] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hval := congrFun hzero 2
    simp only [Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons,
      Pi.zero_apply, neg_eq_zero] at hval
    exact absurd hval hlead.ne'
  have hval := posDef_quadratic_pos hpos hne
  rw [dotProduct_mulVec_fin_three] at hval
  nlinarith [hval, hlead, hsym]

/-- The `(1,2)` principal minor of a positive definite three-by-three matrix is positive. -/
theorem minorOneTwo_pos_of_posDef {form : Matrix (Fin 3) (Fin 3) ℝ} (hpos : form.PosDef) :
    0 < form 1 1 * form 2 2 - form 1 2 * form 2 1 := by
  have hlead := diagonal_pos_of_posDef hpos 1
  have hsym := entry_symm_of_posDef hpos 1 2
  have hne : (![0, form 1 2, -(form 1 1)] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hval := congrFun hzero 2
    simp only [Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons,
      Pi.zero_apply, neg_eq_zero] at hval
    exact absurd hval hlead.ne'
  have hval := posDef_quadratic_pos hpos hne
  rw [dotProduct_mulVec_fin_three] at hval
  nlinarith [hval, hlead, hsym]

/-- **THE CONVERSE OF THE INERTIA BRIDGE.**  A positive definite three-by-three matrix has
positive trace, positive second invariant and positive determinant.  The trace is a total of
diagonal entries and the second invariant a total of two-by-two principal minors, and every
one of those is the quadratic form of the matrix at an explicit probe. -/
theorem invariants_pos_of_posDef {form : Matrix (Fin 3) (Fin 3) ℝ} (hpos : form.PosDef) :
    0 < Matrix.trace form ∧ 0 < secondInvariantOfThree form ∧ 0 < form.det := by
  refine ⟨?_, ?_, hpos.det_pos⟩
  · rw [Matrix.trace_fin_three]
    have h0 := diagonal_pos_of_posDef hpos 0
    have h1 := diagonal_pos_of_posDef hpos 1
    have h2 := diagonal_pos_of_posDef hpos 2
    linarith
  · rw [secondInvariantOfThree]
    have h01 := minorZeroOne_pos_of_posDef hpos
    have h02 := minorZeroTwo_pos_of_posDef hpos
    have h12 := minorOneTwo_pos_of_posDef hpos
    linarith

/-- **THE EXACT CRITERION.**  A real symmetric three-by-three matrix is positive definite
exactly when its three characteristic invariants are positive.  Nothing but the
characteristic cubic and three explicit probes enters. -/
theorem posDef_iff_invariants_pos {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hhermitian : form.IsHermitian) :
    form.PosDef ↔ (0 < Matrix.trace form ∧ 0 < secondInvariantOfThree form ∧ 0 < form.det) := by
  constructor
  · exact invariants_pos_of_posDef
  · rintro ⟨htrace, hsecond, hdet⟩
    exact posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos hhermitian htrace hsecond hdet

/-- **THE SHARPENED SUFFICIENT FORM.**  Two of the three strict signs are free.  A weakly
positive trace and a weakly positive second invariant already suffice, provided the
determinant is strictly positive.

At a nonpositive point the characteristic cubic reads `λ³ − e₁ λ² + e₂ λ − e₃`.  The first
term is nonpositive because `λ ≤ 0`, the second because `0 ≤ e₁`, the third because
`0 ≤ e₂` and `λ ≤ 0`, and the fourth is strictly negative.  The cubic is strictly negative
there, so it cannot vanish and no eigenvalue is nonpositive. -/
theorem posDef_of_invariants_nonneg_of_det_pos {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hhermitian : form.IsHermitian) (htrace : 0 ≤ Matrix.trace form)
    (hsecond : 0 ≤ secondInvariantOfThree form) (hdet : 0 < form.det) :
    form.PosDef := by
  rw [hhermitian.posDef_iff_eigenvalues_pos]
  intro index
  by_contra hnotpositive
  have hle : hhermitian.eigenvalues index ≤ 0 := not_lt.mp hnotpositive
  have hroot : form.charpoly.eval (hhermitian.eigenvalues index) = 0 := by
    rw [hhermitian.charpoly_eq, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ index) (by simp)
  rw [Matrix.eval_charpoly, det_scalar_sub_eq_characteristicCubic] at hroot
  have hsquareNonneg : 0 ≤ hhermitian.eigenvalues index ^ 2 := sq_nonneg _
  have hcubeNonpos : hhermitian.eigenvalues index ^ 3 ≤ 0 := by nlinarith
  have hquadNonneg : 0 ≤ Matrix.trace form * hhermitian.eigenvalues index ^ 2 :=
    mul_nonneg htrace hsquareNonneg
  have hlinearNonpos : secondInvariantOfThree form * hhermitian.eigenvalues index ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsecond hle
  linarith

/-! ## 2. The three invariants of a triple, in scalar form -/

/-- The gap trace of an ordered triple of labels. -/
noncomputable def gapTraceAt (design : WeightedDesign size 3) (pivot left right : Fin size) : ℝ :=
  leverageOf (design.atom pivot) + leverageOf (design.atom left)
    + leverageOf (design.atom right) - 3

/-- The gap second invariant of an ordered triple of labels. -/
noncomputable def gapSecondAt (design : WeightedDesign size 3)
    (pivot left right : Fin size) : ℝ :=
  (pairBracketSq (design.atom pivot) (design.atom left)
      + pairBracketSq (design.atom pivot) (design.atom right)
      + pairBracketSq (design.atom left) (design.atom right))
    - 2 * (leverageOf (design.atom pivot) + leverageOf (design.atom left)
        + leverageOf (design.atom right)) + 3

/-- The gap determinant of an ordered triple of labels. -/
noncomputable def gapDetAt (design : WeightedDesign size 3) (pivot left right : Fin size) : ℝ :=
  tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
    - (pairBracketSq (design.atom pivot) (design.atom left)
      + pairBracketSq (design.atom pivot) (design.atom right)
      + pairBracketSq (design.atom left) (design.atom right))
    + (leverageOf (design.atom pivot) + leverageOf (design.atom left)
      + leverageOf (design.atom right)) - 1

/-- The trace of the three-by-three identity. -/
theorem trace_one_fin_three : Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℝ) = 3 := by
  simp [Matrix.trace_fin_three]

/-- The shift of the second invariant by the identity, on entries. -/
theorem secondInvariantOfThree_sub_one_ledger (form : Matrix (Fin 3) (Fin 3) ℝ) :
    secondInvariantOfThree (form - 1)
      = secondInvariantOfThree form - 2 * Matrix.trace form + 3 := by
  have h00 : (form - 1) 0 0 = form 0 0 - 1 := by simp [Matrix.sub_apply, Matrix.one_apply]
  have h11 : (form - 1) 1 1 = form 1 1 - 1 := by simp [Matrix.sub_apply, Matrix.one_apply]
  have h22 : (form - 1) 2 2 = form 2 2 - 1 := by simp [Matrix.sub_apply, Matrix.one_apply]
  have h01 : (form - 1) 0 1 = form 0 1 := by simp [Matrix.sub_apply, Matrix.one_apply]
  have h10 : (form - 1) 1 0 = form 1 0 := by simp [Matrix.sub_apply, Matrix.one_apply]
  have h02 : (form - 1) 0 2 = form 0 2 := by simp [Matrix.sub_apply, Matrix.one_apply]
  have h20 : (form - 1) 2 0 = form 2 0 := by simp [Matrix.sub_apply, Matrix.one_apply]
  have h12 : (form - 1) 1 2 = form 1 2 := by simp [Matrix.sub_apply, Matrix.one_apply]
  have h21 : (form - 1) 2 1 = form 2 1 := by simp [Matrix.sub_apply, Matrix.one_apply]
  simp only [secondInvariantOfThree, Matrix.trace_fin_three, h00, h11, h22, h01, h10, h02,
    h20, h12, h21]
  ring

/-- The second invariant of a sum of three rank-one atom matrices is the total of the three
pair Gram determinants.  A rank-one summand contributes nothing alone, and the mixed term of
a pair is exactly that pair's Gram determinant. -/
theorem secondInvariantOfThree_atomMatrix_triple (leftVec midVec rightVec : Fin 3 → ℝ) :
    secondInvariantOfThree (atomMatrix leftVec + (atomMatrix midVec + atomMatrix rightVec))
      = pairBracketSq leftVec midVec + pairBracketSq leftVec rightVec
        + pairBracketSq midVec rightVec := by
  simp only [secondInvariantOfThree, pairBracketSq, leverageOf, atomMatrix,
    Matrix.add_apply, Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- The trace of the gap of a three-element set, on leverages. -/
theorem trace_subsetSum_triple_sub_one (design : WeightedDesign size 3)
    {pivot left right : Fin size} (hpl : pivot ≠ left) (hpr : pivot ≠ right)
    (hlr : left ≠ right) :
    Matrix.trace (subsetSum design ({pivot, left, right} : Finset (Fin size)) - 1)
      = gapTraceAt design pivot left right := by
  have hsum : subsetSum design ({pivot, left, right} : Finset (Fin size))
      = atomMatrix (design.atom pivot)
        + (atomMatrix (design.atom left) + atomMatrix (design.atom right)) :=
    sum_triple_eq hpl hpr hlr fun label => atomMatrix (design.atom label)
  rw [hsum, gapTraceAt, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add,
    trace_atomMatrix, trace_atomMatrix, trace_atomMatrix, trace_one_fin_three]
  ring

/-- The second invariant of the gap of a three-element set, on pair Gram determinants and
leverages. -/
theorem secondInvariantOfThree_subsetSum_triple_sub_one (design : WeightedDesign size 3)
    {pivot left right : Fin size} (hpl : pivot ≠ left) (hpr : pivot ≠ right)
    (hlr : left ≠ right) :
    secondInvariantOfThree (subsetSum design ({pivot, left, right} : Finset (Fin size)) - 1)
      = gapSecondAt design pivot left right := by
  have hsum : subsetSum design ({pivot, left, right} : Finset (Fin size))
      = atomMatrix (design.atom pivot)
        + (atomMatrix (design.atom left) + atomMatrix (design.atom right)) :=
    sum_triple_eq hpl hpr hlr fun label => atomMatrix (design.atom label)
  have htrace : Matrix.trace (atomMatrix (design.atom pivot)
        + (atomMatrix (design.atom left) + atomMatrix (design.atom right)))
      = leverageOf (design.atom pivot) + leverageOf (design.atom left)
        + leverageOf (design.atom right) := by
    rw [Matrix.trace_add, Matrix.trace_add, trace_atomMatrix, trace_atomMatrix,
      trace_atomMatrix]
    ring
  rw [hsum, secondInvariantOfThree_sub_one_ledger, secondInvariantOfThree_atomMatrix_triple,
    htrace, gapSecondAt]

/-- The determinant of the gap of a three-element set, on the squared bracket, the pair Gram
determinants and the leverages.  The landed `Gtz.polarGapDet` is the same polynomial. -/
theorem det_subsetSum_triple_sub_one_eq_gapDetAt (design : WeightedDesign size 3)
    {pivot left right : Fin size} (hpl : pivot ≠ left) (hpr : pivot ≠ right)
    (hlr : left ≠ right) :
    (subsetSum design ({pivot, left, right} : Finset (Fin size)) - 1).det
      = gapDetAt design pivot left right := by
  rw [subsetSum_triple_sub_one_det design hpl hpr hlr, polarGapDet, gapDetAt]
  simp only [pairBracketSq, leverageOf_eq_dotProduct_self,
    dotProduct_comm (design.atom right) (design.atom pivot)]
  ring

/-! ### A nonzero bracket separates its three labels -/

/-- **A POSITIVE SQUARED BRACKET SPANS.**  The three labels of a triple with a nonzero
bracket are pairwise distinct, so the triple is a genuine three-element set. -/
theorem distinct_of_bracket_sq_pos (design : WeightedDesign size 3)
    {pivot left right : Fin size}
    (hbracket : 0 < tripleBracket (design.atom pivot) (design.atom left)
      (design.atom right) ^ 2) :
    pivot ≠ left ∧ pivot ≠ right ∧ left ≠ right := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    rw [heq, tripleBracket_self_left] at hbracket
    norm_num at hbracket
  · intro heq
    rw [heq, tripleBracket_repeat_first] at hbracket
    norm_num at hbracket
  · intro heq
    rw [heq, tripleBracket_repeat_second] at hbracket
    norm_num at hbracket

/-! ## 3. The two layer measures on ordered index triples

Both measures run over ALL ordered index triples, so no cardinality bookkeeping and no
`Finset.powersetCard` enters this file. -/

/-- The product-measure layer moment of a triple reading. -/
noncomputable def productLayer (design : WeightedDesign size 3)
    (reading : Fin size → Fin size → Fin size → ℝ) : ℝ :=
  ∑ pivot, ∑ left, ∑ right,
    design.weight pivot * design.weight left * design.weight right * reading pivot left right

/-- The volume-measure layer moment of a triple reading.  The extra squared bracket is the
volume-sampling density, and it annihilates every degenerate index triple. -/
noncomputable def volumeLayer (design : WeightedDesign size 3)
    (reading : Fin size → Fin size → Fin size → ℝ) : ℝ :=
  ∑ pivot, ∑ left, ∑ right,
    design.weight pivot * design.weight left * design.weight right
      * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
      * reading pivot left right

/-- The second moment of the leverage against the design. -/
noncomputable def leverageSquareMoment (design : WeightedDesign size 3) : ℝ :=
  ∑ label, design.weight label * leverageOf (design.atom label) ^ 2

/-- The second moment of the pair Gram determinant against the design.  This is the first
ANGLE-AWARE moment of the ladder: the one-point marginal `Σ_e t_e ⟨d,e⟩ = 2 ℓ_d` has no
angle in it, but its second moment does. -/
noncomputable def pairGramSecondMoment (design : WeightedDesign size 3) : ℝ :=
  ∑ leftLabel, ∑ rightLabel, design.weight leftLabel * design.weight rightLabel
    * pairBracketSq (design.atom leftLabel) (design.atom rightLabel) ^ 2

/-- The fourth moment of the bracket against the design. -/
noncomputable def bracketFourthMoment (design : WeightedDesign size 3) : ℝ :=
  ∑ pivot, ∑ left, ∑ right, design.weight pivot * design.weight left * design.weight right
    * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 4

/-! ### Reordering the three slots -/

/-- Rotating three nested sums over one index type. -/
theorem sum_rotate_three {M : Type*} [AddCommMonoid M]
    (summand : Fin size → Fin size → Fin size → M) :
    ∑ pivot, ∑ left, ∑ right, summand pivot left right
      = ∑ left, ∑ right, ∑ pivot, summand pivot left right := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The product measure reads the second slot as it reads the first. -/
theorem productLayer_slot_two (design : WeightedDesign size 3) (reading : Fin size → ℝ) :
    (∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right * reading left)
      = ∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right * reading pivot := by
  rw [sum_rotate_three fun pivot left right =>
    design.weight pivot * design.weight left * design.weight right * reading left]
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- The product measure reads the third slot as it reads the second. -/
theorem productLayer_slot_three_two (design : WeightedDesign size 3) (reading : Fin size → ℝ) :
    (∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right * reading right)
      = ∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right * reading left := by
  rw [sum_rotate_three fun pivot left right =>
    design.weight pivot * design.weight left * design.weight right * reading right]
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- The product measure reads the third slot as it reads the first. -/
theorem productLayer_slot_three (design : WeightedDesign size 3) (reading : Fin size → ℝ) :
    (∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right * reading right)
      = ∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right * reading pivot :=
  (productLayer_slot_three_two design reading).trans (productLayer_slot_two design reading)

/-- The volume measure reads the second slot as it reads the first. -/
theorem volumeLayer_slot_two (design : WeightedDesign size 3) (reading : Fin size → ℝ) :
    (∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * reading left)
      = ∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * reading pivot := by
  have hrotate : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * reading left
        = design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom left) (design.atom right) (design.atom pivot) ^ 2
          * reading left := fun pivot left right => by
    rw [sq_tripleBracket_rotate]
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hrotate pivot left right]
  rw [sum_rotate_three fun pivot left right =>
    design.weight pivot * design.weight left * design.weight right
      * tripleBracket (design.atom left) (design.atom right) (design.atom pivot) ^ 2
      * reading left]
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- The volume measure reads the third slot as it reads the second. -/
theorem volumeLayer_slot_three_two (design : WeightedDesign size 3) (reading : Fin size → ℝ) :
    (∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * reading right)
      = ∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * reading left := by
  have hrotate : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * reading right
        = design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom left) (design.atom right) (design.atom pivot) ^ 2
          * reading right := fun pivot left right => by
    rw [sq_tripleBracket_rotate]
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hrotate pivot left right]
  rw [sum_rotate_three fun pivot left right =>
    design.weight pivot * design.weight left * design.weight right
      * tripleBracket (design.atom left) (design.atom right) (design.atom pivot) ^ 2
      * reading right]
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- The volume measure reads the third slot as it reads the first. -/
theorem volumeLayer_slot_three (design : WeightedDesign size 3) (reading : Fin size → ℝ) :
    (∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * reading right)
      = ∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * reading pivot :=
  (volumeLayer_slot_three_two design reading).trans (volumeLayer_slot_two design reading)

/-! ### The product-measure moments are universal constants -/

/-- The total mass of the product measure is one. -/
theorem productLayer_one (design : WeightedDesign size 3) :
    productLayer design (fun _ _ _ => 1) = 1 := by
  have hsum := design.weight_sum_one
  unfold productLayer
  have hinner : ∀ pivot left : Fin size,
      (∑ right, design.weight pivot * design.weight left * design.weight right * 1)
        = design.weight pivot * design.weight left := by
    intro pivot left
    rw [Finset.sum_congr rfl fun right _ =>
      show design.weight pivot * design.weight left * design.weight right * 1
        = design.weight pivot * design.weight left * design.weight right from by ring,
      ← Finset.mul_sum, hsum, mul_one]
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ => hinner pivot left]
  rw [Finset.sum_congr rfl fun pivot _ => by rw [← Finset.mul_sum, hsum, mul_one], hsum]

/-- The product measure integrated against a one-slot reading. -/
theorem productLayer_pivot_reading (design : WeightedDesign size 3) (reading : Fin size → ℝ) :
    (∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right * reading pivot)
      = ∑ pivot, design.weight pivot * reading pivot := by
  have hsum := design.weight_sum_one
  have hinner : ∀ pivot left : Fin size,
      (∑ right, design.weight pivot * design.weight left * design.weight right * reading pivot)
        = design.weight pivot * reading pivot * design.weight left := by
    intro pivot left
    rw [Finset.sum_congr rfl fun right _ =>
      show design.weight pivot * design.weight left * design.weight right * reading pivot
        = design.weight pivot * reading pivot * design.weight left * design.weight right from
        by ring, ← Finset.mul_sum, hsum, mul_one]
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ => hinner pivot left]
  exact Finset.sum_congr rfl fun pivot _ => by rw [← Finset.mul_sum, hsum, mul_one]

/-- **THE PRODUCT-MEASURE LEVERAGE MOMENT IS NINE.** -/
theorem productLayer_leverageSum (design : WeightedDesign size 3) :
    productLayer design (fun pivot left right => leverageOf (design.atom pivot)
      + leverageOf (design.atom left) + leverageOf (design.atom right)) = 9 := by
  have hrank : ∑ label, design.weight label * leverageOf (design.atom label) = (3 : ℝ) := by
    have hbase := sum_weight_mul_leverage design
    simpa using hbase
  unfold productLayer
  have hsplit : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * (leverageOf (design.atom pivot) + leverageOf (design.atom left)
            + leverageOf (design.atom right))
        = design.weight pivot * design.weight left * design.weight right
            * leverageOf (design.atom pivot)
          + design.weight pivot * design.weight left * design.weight right
            * leverageOf (design.atom left)
          + design.weight pivot * design.weight left * design.weight right
            * leverageOf (design.atom right) := fun _ _ _ => by ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hsplit pivot left right]
  simp only [Finset.sum_add_distrib]
  rw [productLayer_slot_two design fun label => leverageOf (design.atom label),
    productLayer_slot_three design fun label => leverageOf (design.atom label),
    productLayer_pivot_reading design fun label => leverageOf (design.atom label), hrank]
  norm_num

/-- **THE PRODUCT-MEASURE PAIR MOMENT IS EIGHTEEN.**  Three copies of the pair energy, and
the pair energy is twice the rank at every design. -/
theorem productLayer_pairSum (design : WeightedDesign size 3) :
    productLayer design (fun pivot left right =>
      pairBracketSq (design.atom pivot) (design.atom left)
        + pairBracketSq (design.atom pivot) (design.atom right)
        + pairBracketSq (design.atom left) (design.atom right)) = 18 := by
  have hsum := design.weight_sum_one
  have hpair := sum_weight_pair_mul_pairBracketSq design
  have hfirst : (∑ pivot, ∑ left, ∑ right,
      design.weight pivot * design.weight left * design.weight right
        * pairBracketSq (design.atom pivot) (design.atom left)) = 6 := by
    have hinner : ∀ pivot left : Fin size,
        (∑ right, design.weight pivot * design.weight left * design.weight right
            * pairBracketSq (design.atom pivot) (design.atom left))
          = design.weight pivot * design.weight left
              * pairBracketSq (design.atom pivot) (design.atom left) := by
      intro pivot left
      rw [Finset.sum_congr rfl fun right _ =>
        show design.weight pivot * design.weight left * design.weight right
            * pairBracketSq (design.atom pivot) (design.atom left)
          = design.weight pivot * design.weight left
              * pairBracketSq (design.atom pivot) (design.atom left)
            * design.weight right from by ring, ← Finset.mul_sum, hsum, mul_one]
    rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ => hinner pivot left]
    exact hpair
  have hthird : (∑ pivot, ∑ left, ∑ right,
      design.weight pivot * design.weight left * design.weight right
        * pairBracketSq (design.atom left) (design.atom right)) = 6 := by
    have hinner : ∀ pivot : Fin size,
        (∑ left, ∑ right, design.weight pivot * design.weight left * design.weight right
            * pairBracketSq (design.atom left) (design.atom right))
          = design.weight pivot * 6 := by
      intro pivot
      rw [← hpair, Finset.mul_sum]
      refine Finset.sum_congr rfl fun left _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun right _ => by ring
    rw [Finset.sum_congr rfl fun pivot _ => hinner pivot, ← Finset.sum_mul, hsum, one_mul]
  have hsecond : (∑ pivot, ∑ left, ∑ right,
      design.weight pivot * design.weight left * design.weight right
        * pairBracketSq (design.atom pivot) (design.atom right)) = 6 := by
    rw [sum_rotate_three fun pivot left right =>
      design.weight pivot * design.weight left * design.weight right
        * pairBracketSq (design.atom pivot) (design.atom right)]
    rw [← hthird]
    refine Finset.sum_congr rfl fun _ _ => ?_
    refine Finset.sum_congr rfl fun _ _ => ?_
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [pairBracketSq_comm]
    ring
  unfold productLayer
  have hsplit : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * (pairBracketSq (design.atom pivot) (design.atom left)
            + pairBracketSq (design.atom pivot) (design.atom right)
            + pairBracketSq (design.atom left) (design.atom right))
        = design.weight pivot * design.weight left * design.weight right
            * pairBracketSq (design.atom pivot) (design.atom left)
          + design.weight pivot * design.weight left * design.weight right
            * pairBracketSq (design.atom pivot) (design.atom right)
          + design.weight pivot * design.weight left * design.weight right
            * pairBracketSq (design.atom left) (design.atom right) := fun _ _ _ => by ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hsplit pivot left right]
  simp only [Finset.sum_add_distrib]
  rw [hfirst, hsecond, hthird]
  norm_num

/-- **THE PRODUCT-MEASURE BRACKET MOMENT IS SIX.**  Cauchy-Binet at Parseval, landed. -/
theorem productLayer_bracketSq (design : WeightedDesign size 3) :
    productLayer design (fun pivot left right =>
      tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2) = 6 := by
  unfold productLayer
  exact sum_weight_triple_mul_sq_tripleBracket design

/-- **THE PRODUCT-MEASURE GAP TRACE MOMENT IS SIX.** -/
theorem productLayer_gapTrace (design : WeightedDesign size 3) :
    productLayer design (gapTraceAt design) = 6 := by
  have hlev := productLayer_leverageSum design
  have hone := productLayer_one design
  unfold productLayer at hlev hone ⊢
  have hsplit : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * gapTraceAt design pivot left right
        = design.weight pivot * design.weight left * design.weight right
            * (leverageOf (design.atom pivot) + leverageOf (design.atom left)
              + leverageOf (design.atom right))
          - 3 * (design.weight pivot * design.weight left * design.weight right * 1) := by
    intro pivot left right
    rw [gapTraceAt]; ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hsplit pivot left right]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hlev, hone]
  norm_num

/-- **THE PRODUCT-MEASURE GAP SECOND-INVARIANT MOMENT IS THREE.** -/
theorem productLayer_gapSecond (design : WeightedDesign size 3) :
    productLayer design (gapSecondAt design) = 3 := by
  have hpairs := productLayer_pairSum design
  have hlev := productLayer_leverageSum design
  have hone := productLayer_one design
  unfold productLayer at hpairs hlev hone ⊢
  have hsplit : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * gapSecondAt design pivot left right
        = design.weight pivot * design.weight left * design.weight right
            * (pairBracketSq (design.atom pivot) (design.atom left)
              + pairBracketSq (design.atom pivot) (design.atom right)
              + pairBracketSq (design.atom left) (design.atom right))
          - 2 * (design.weight pivot * design.weight left * design.weight right
            * (leverageOf (design.atom pivot) + leverageOf (design.atom left)
              + leverageOf (design.atom right)))
          + 3 * (design.weight pivot * design.weight left * design.weight right * 1) := by
    intro pivot left right
    rw [gapSecondAt]; ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hsplit pivot left right]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hpairs, hlev, hone]
  norm_num

/-- **THE PRODUCT-MEASURE GAP DETERMINANT MOMENT IS MINUS FOUR.**  A universal NEGATIVE
constant, at every rank-three design and every size. -/
theorem productLayer_gapDet (design : WeightedDesign size 3) :
    productLayer design (gapDetAt design) = -4 := by
  have hbracket := productLayer_bracketSq design
  have hpairs := productLayer_pairSum design
  have hlev := productLayer_leverageSum design
  have hone := productLayer_one design
  unfold productLayer at hbracket hpairs hlev hone ⊢
  have hsplit : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * gapDetAt design pivot left right
        = design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          - design.weight pivot * design.weight left * design.weight right
            * (pairBracketSq (design.atom pivot) (design.atom left)
              + pairBracketSq (design.atom pivot) (design.atom right)
              + pairBracketSq (design.atom left) (design.atom right))
          + design.weight pivot * design.weight left * design.weight right
            * (leverageOf (design.atom pivot) + leverageOf (design.atom left)
              + leverageOf (design.atom right))
          - design.weight pivot * design.weight left * design.weight right * 1 := by
    intro pivot left right
    rw [gapDetAt]; ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hsplit pivot left right]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hbracket, hpairs, hlev, hone]
  norm_num

/-- **THE PRODUCT-WEIGHTED DETERMINANT ROUTE IS CLOSED.**  The moment is the negative
constant `−4` at EVERY rank-three design, so no design makes it positive and no selection of
a strictly dominating triple can come out of it. -/
theorem productLayer_gapDet_neg (design : WeightedDesign size 3) :
    productLayer design (gapDetAt design) < 0 := by
  rw [productLayer_gapDet]; norm_num

/-- **THE PRODUCT MEASURE IS BLIND.**  Two rank-three designs of the same size carry the same
three product-measure gap moments, whatever their atoms and whatever their weights. -/
theorem productLayer_gap_moments_congr (design other : WeightedDesign size 3) :
    productLayer design (gapTraceAt design) = productLayer other (gapTraceAt other)
      ∧ productLayer design (gapSecondAt design) = productLayer other (gapSecondAt other)
      ∧ productLayer design (gapDetAt design) = productLayer other (gapDetAt other) :=
  ⟨by rw [productLayer_gapTrace, productLayer_gapTrace],
    by rw [productLayer_gapSecond, productLayer_gapSecond],
    by rw [productLayer_gapDet, productLayer_gapDet]⟩

/-! ### The volume-measure moments -/

/-- The total mass of the volume measure is twice the rank. -/
theorem volumeLayer_one (design : WeightedDesign size 3) :
    volumeLayer design (fun _ _ _ => 1) = 6 := by
  unfold volumeLayer
  rw [← sum_weight_triple_mul_sq_tripleBracket design]
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- The volume measure integrated against a one-slot reading collapses onto the pivot's
leverage through the two-slot marginal of the squared bracket. -/
theorem volumeLayer_pivot_reading (design : WeightedDesign size 3) (reading : Fin size → ℝ) :
    (∑ pivot, ∑ left, ∑ right,
        design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * reading pivot)
      = ∑ pivot, design.weight pivot * (2 * leverageOf (design.atom pivot)) * reading pivot := by
  refine Finset.sum_congr rfl fun pivot _ => ?_
  have hmarginal := sum_weight_pair_mul_sq_tripleBracket design pivot
  calc (∑ left, ∑ right, design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * reading pivot)
      = (design.weight pivot * reading pivot)
        * ∑ left, ∑ right, design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun left _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun right _ => by ring
    _ = design.weight pivot * (2 * leverageOf (design.atom pivot)) * reading pivot := by
        rw [hmarginal]; ring

/-- **THE VOLUME-MEASURE LEVERAGE MOMENT.**  Six times the second leverage moment. -/
theorem volumeLayer_leverageSum (design : WeightedDesign size 3) :
    volumeLayer design (fun pivot left right => leverageOf (design.atom pivot)
        + leverageOf (design.atom left) + leverageOf (design.atom right))
      = 6 * leverageSquareMoment design := by
  have hpivot : (∑ pivot, ∑ left, ∑ right,
      design.weight pivot * design.weight left * design.weight right
        * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
        * leverageOf (design.atom pivot)) = 2 * leverageSquareMoment design := by
    rw [volumeLayer_pivot_reading design fun label => leverageOf (design.atom label)]
    rw [leverageSquareMoment, Finset.mul_sum]
    exact Finset.sum_congr rfl fun pivot _ => by ring
  unfold volumeLayer
  have hsplit : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * (leverageOf (design.atom pivot) + leverageOf (design.atom left)
            + leverageOf (design.atom right))
        = design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * leverageOf (design.atom pivot)
          + design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * leverageOf (design.atom left)
          + design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * leverageOf (design.atom right) := fun _ _ _ => by ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hsplit pivot left right]
  simp only [Finset.sum_add_distrib]
  rw [volumeLayer_slot_two design fun label => leverageOf (design.atom label),
    volumeLayer_slot_three design fun label => leverageOf (design.atom label), hpivot]
  ring

/-- **THE VOLUME-MEASURE PAIR MOMENT.**  Three times the second moment of the pair Gram
determinant.  The two-point marginal of the squared bracket turns each pair reading into the
SQUARE of that pair's Gram determinant, and that square is the first quantity of the ladder
that is not a function of the weight and leverage profile. -/
theorem volumeLayer_pairSum (design : WeightedDesign size 3) :
    volumeLayer design (fun pivot left right =>
        pairBracketSq (design.atom pivot) (design.atom left)
          + pairBracketSq (design.atom pivot) (design.atom right)
          + pairBracketSq (design.atom left) (design.atom right))
      = 3 * pairGramSecondMoment design := by
  have hfirst : (∑ pivot, ∑ left, ∑ right,
      design.weight pivot * design.weight left * design.weight right
        * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
        * pairBracketSq (design.atom pivot) (design.atom left))
      = pairGramSecondMoment design := by
    unfold pairGramSecondMoment
    refine Finset.sum_congr rfl fun pivot _ => ?_
    refine Finset.sum_congr rfl fun left _ => ?_
    have hmarginal := sum_weight_mul_sq_tripleBracket design pivot left
    calc (∑ right, design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * pairBracketSq (design.atom pivot) (design.atom left))
        = (design.weight pivot * design.weight left
            * pairBracketSq (design.atom pivot) (design.atom left))
          * ∑ right, design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun right _ => by ring
      _ = design.weight pivot * design.weight left
            * pairBracketSq (design.atom pivot) (design.atom left) ^ 2 := by
          rw [hmarginal]; ring
  have hthird : (∑ pivot, ∑ left, ∑ right,
      design.weight pivot * design.weight left * design.weight right
        * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
        * pairBracketSq (design.atom left) (design.atom right))
      = pairGramSecondMoment design := by
    rw [sum_rotate_three fun pivot left right =>
      design.weight pivot * design.weight left * design.weight right
        * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
        * pairBracketSq (design.atom left) (design.atom right)]
    unfold pairGramSecondMoment
    refine Finset.sum_congr rfl fun leftLabel _ => ?_
    refine Finset.sum_congr rfl fun rightLabel _ => ?_
    have hmarginal := sum_weight_mul_sq_tripleBracket design leftLabel rightLabel
    calc (∑ pivot, design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * tripleBracket (design.atom pivot) (design.atom leftLabel)
              (design.atom rightLabel) ^ 2
            * pairBracketSq (design.atom leftLabel) (design.atom rightLabel))
        = (design.weight leftLabel * design.weight rightLabel
            * pairBracketSq (design.atom leftLabel) (design.atom rightLabel))
          * ∑ pivot, design.weight pivot
            * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
              (design.atom pivot) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun pivot _ => ?_
          rw [sq_tripleBracket_rotate (design.atom pivot) (design.atom leftLabel)
            (design.atom rightLabel)]
          ring
      _ = design.weight leftLabel * design.weight rightLabel
            * pairBracketSq (design.atom leftLabel) (design.atom rightLabel) ^ 2 := by
          rw [hmarginal]; ring
  have hsecond : (∑ pivot, ∑ left, ∑ right,
      design.weight pivot * design.weight left * design.weight right
        * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
        * pairBracketSq (design.atom pivot) (design.atom right))
      = pairGramSecondMoment design := by
    rw [← hthird]
    rw [sum_rotate_three fun pivot left right =>
      design.weight pivot * design.weight left * design.weight right
        * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
        * pairBracketSq (design.atom pivot) (design.atom right)]
    refine Finset.sum_congr rfl fun leftLabel _ => ?_
    refine Finset.sum_congr rfl fun rightLabel _ => ?_
    refine Finset.sum_congr rfl fun pivotLabel _ => ?_
    rw [sq_tripleBracket_rotate (design.atom pivotLabel) (design.atom leftLabel)
      (design.atom rightLabel), pairBracketSq_comm (design.atom pivotLabel)
      (design.atom rightLabel)]
    ring
  unfold volumeLayer
  have hsplit : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * (pairBracketSq (design.atom pivot) (design.atom left)
            + pairBracketSq (design.atom pivot) (design.atom right)
            + pairBracketSq (design.atom left) (design.atom right))
        = design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * pairBracketSq (design.atom pivot) (design.atom left)
          + design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * pairBracketSq (design.atom pivot) (design.atom right)
          + design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * pairBracketSq (design.atom left) (design.atom right) := fun _ _ _ => by ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hsplit pivot left right]
  simp only [Finset.sum_add_distrib]
  rw [hfirst, hsecond, hthird]
  ring

/-- **THE VOLUME-MEASURE BRACKET MOMENT.**  The fourth moment of the bracket. -/
theorem volumeLayer_bracketSq (design : WeightedDesign size 3) :
    volumeLayer design (fun pivot left right =>
        tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2)
      = bracketFourthMoment design := by
  unfold volumeLayer bracketFourthMoment
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **THE VOLUME-MEASURE GAP TRACE MOMENT.** -/
theorem volumeLayer_gapTrace (design : WeightedDesign size 3) :
    volumeLayer design (gapTraceAt design) = 6 * leverageSquareMoment design - 18 := by
  have hlev := volumeLayer_leverageSum design
  have hone := volumeLayer_one design
  unfold volumeLayer at hlev hone ⊢
  have hsplit : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * gapTraceAt design pivot left right
        = design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * (leverageOf (design.atom pivot) + leverageOf (design.atom left)
              + leverageOf (design.atom right))
          - 3 * (design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * 1) := by
    intro pivot left right
    rw [gapTraceAt]; ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hsplit pivot left right]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hlev, hone]
  ring

/-- **THE VOLUME-MEASURE GAP SECOND-INVARIANT MOMENT.**  Angle-aware through the second
moment of the pair Gram determinant. -/
theorem volumeLayer_gapSecond (design : WeightedDesign size 3) :
    volumeLayer design (gapSecondAt design)
      = 3 * pairGramSecondMoment design - 12 * leverageSquareMoment design + 18 := by
  have hpairs := volumeLayer_pairSum design
  have hlev := volumeLayer_leverageSum design
  have hone := volumeLayer_one design
  unfold volumeLayer at hpairs hlev hone ⊢
  have hsplit : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * gapSecondAt design pivot left right
        = design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * (pairBracketSq (design.atom pivot) (design.atom left)
              + pairBracketSq (design.atom pivot) (design.atom right)
              + pairBracketSq (design.atom left) (design.atom right))
          - 2 * (design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * (leverageOf (design.atom pivot) + leverageOf (design.atom left)
              + leverageOf (design.atom right)))
          + 3 * (design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * 1) := by
    intro pivot left right
    rw [gapSecondAt]; ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hsplit pivot left right]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hpairs, hlev, hone]
  ring

/-- **THE VOLUME-MEASURE GAP DETERMINANT MOMENT.**  Angle-aware through both the fourth
bracket moment and the second pair moment. -/
theorem volumeLayer_gapDet (design : WeightedDesign size 3) :
    volumeLayer design (gapDetAt design)
      = bracketFourthMoment design - 3 * pairGramSecondMoment design
        + 6 * leverageSquareMoment design - 6 := by
  have hbracket := volumeLayer_bracketSq design
  have hpairs := volumeLayer_pairSum design
  have hlev := volumeLayer_leverageSum design
  have hone := volumeLayer_one design
  unfold volumeLayer at hbracket hpairs hlev hone ⊢
  have hsplit : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          * gapDetAt design pivot left right
        = design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
          - design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * (pairBracketSq (design.atom pivot) (design.atom left)
              + pairBracketSq (design.atom pivot) (design.atom right)
              + pairBracketSq (design.atom left) (design.atom right))
          + design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * (leverageOf (design.atom pivot) + leverageOf (design.atom left)
              + leverageOf (design.atom right))
          - design.weight pivot * design.weight left * design.weight right
            * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
            * 1 := by
    intro pivot left right
    rw [gapDetAt]; ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun left _ =>
    Finset.sum_congr rfl fun right _ => hsplit pivot left right]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hbracket, hpairs, hlev, hone]

/-! ## 4. Three square expansions, and the sign they force -/

/-- **THE LEVERAGE VARIANCE FLOOR.**  The second leverage moment is at least the square of
the rank.  One expanded square, and the Parseval trace identity. -/
theorem nine_le_leverageSquareMoment (design : WeightedDesign size 3) :
    9 ≤ leverageSquareMoment design := by
  have hrank : ∑ label, design.weight label * leverageOf (design.atom label) = (3 : ℝ) := by
    have hbase := sum_weight_mul_leverage design
    simpa using hbase
  have hmass := design.weight_sum_one
  have hnonneg : 0 ≤ ∑ label, design.weight label * (leverageOf (design.atom label) - 3) ^ 2 :=
    Finset.sum_nonneg fun label _ =>
      mul_nonneg (design.weight_pos label).le (sq_nonneg _)
  have hexpand : (∑ label, design.weight label * (leverageOf (design.atom label) - 3) ^ 2)
      = leverageSquareMoment design
        - 6 * (∑ label, design.weight label * leverageOf (design.atom label))
        + 9 * ∑ label, design.weight label := by
    rw [leverageSquareMoment, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun label _ => by ring
  rw [hexpand, hrank, hmass] at hnonneg
  linarith

/-- **THE PAIR-MOMENT FLOOR.**  The second moment of the pair Gram determinant is at least
four times the second leverage moment.  One expanded square against the landed one-point
marginal `Σ_e t_e ⟨d,e⟩ = 2 ℓ_d`. -/
theorem four_mul_leverageSquareMoment_le_pairGramSecondMoment (design : WeightedDesign size 3) :
    4 * leverageSquareMoment design ≤ pairGramSecondMoment design := by
  have hmass := design.weight_sum_one
  have hrow : ∀ leftLabel : Fin size,
      4 * leverageOf (design.atom leftLabel) ^ 2
        ≤ ∑ rightLabel, design.weight rightLabel
          * pairBracketSq (design.atom leftLabel) (design.atom rightLabel) ^ 2 := by
    intro leftLabel
    have hmarginal := sum_weight_mul_pairBracketSq design leftLabel
    have hnonneg : 0 ≤ ∑ rightLabel, design.weight rightLabel
        * (pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
          - 2 * leverageOf (design.atom leftLabel)) ^ 2 :=
      Finset.sum_nonneg fun rightLabel _ =>
        mul_nonneg (design.weight_pos rightLabel).le (sq_nonneg _)
    have hexpand : (∑ rightLabel, design.weight rightLabel
          * (pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
            - 2 * leverageOf (design.atom leftLabel)) ^ 2)
        = (∑ rightLabel, design.weight rightLabel
            * pairBracketSq (design.atom leftLabel) (design.atom rightLabel) ^ 2)
          - 4 * leverageOf (design.atom leftLabel)
            * (∑ rightLabel, design.weight rightLabel
              * pairBracketSq (design.atom leftLabel) (design.atom rightLabel))
          + 4 * leverageOf (design.atom leftLabel) ^ 2 * ∑ rightLabel, design.weight rightLabel := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun rightLabel _ => by ring
    rw [hexpand, hmarginal, hmass] at hnonneg
    linarith
  have hweighted : ∀ leftLabel : Fin size,
      design.weight leftLabel * (4 * leverageOf (design.atom leftLabel) ^ 2)
        ≤ design.weight leftLabel * ∑ rightLabel, design.weight rightLabel
          * pairBracketSq (design.atom leftLabel) (design.atom rightLabel) ^ 2 := by
    intro leftLabel
    exact mul_le_mul_of_nonneg_left (hrow leftLabel) (design.weight_pos leftLabel).le
  have htotal := Finset.sum_le_sum fun leftLabel (_ : leftLabel ∈ Finset.univ) =>
    hweighted leftLabel
  have hleft : (∑ leftLabel, design.weight leftLabel
        * (4 * leverageOf (design.atom leftLabel) ^ 2))
      = 4 * leverageSquareMoment design := by
    rw [leverageSquareMoment, Finset.mul_sum]
    exact Finset.sum_congr rfl fun leftLabel _ => by ring
  have hright : (∑ leftLabel, design.weight leftLabel * ∑ rightLabel, design.weight rightLabel
        * pairBracketSq (design.atom leftLabel) (design.atom rightLabel) ^ 2)
      = pairGramSecondMoment design := by
    rw [pairGramSecondMoment]
    refine Finset.sum_congr rfl fun leftLabel _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  rw [hleft, hright] at htotal
  exact htotal

/-- **THE BRACKET-MOMENT CEILING.**  The second moment of the pair Gram determinant never
exceeds the fourth moment of the bracket.  One expanded square against the landed two-point
marginal `Σ_a t_a [d,e,a]² = ⟨d,e⟩`.  The direction is the wrong one for the determinant
layer, and this file records that. -/
theorem pairGramSecondMoment_le_bracketFourthMoment (design : WeightedDesign size 3) :
    pairGramSecondMoment design ≤ bracketFourthMoment design := by
  have hmass := design.weight_sum_one
  have hrow : ∀ leftLabel rightLabel : Fin size,
      pairBracketSq (design.atom leftLabel) (design.atom rightLabel) ^ 2
        ≤ ∑ third, design.weight third
          * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
            (design.atom third) ^ 4 := by
    intro leftLabel rightLabel
    have hmarginal := sum_weight_mul_sq_tripleBracket design leftLabel rightLabel
    have hnonneg : 0 ≤ ∑ third, design.weight third
        * (tripleBracket (design.atom leftLabel) (design.atom rightLabel)
            (design.atom third) ^ 2
          - pairBracketSq (design.atom leftLabel) (design.atom rightLabel)) ^ 2 :=
      Finset.sum_nonneg fun third _ => mul_nonneg (design.weight_pos third).le (sq_nonneg _)
    have hexpand : (∑ third, design.weight third
          * (tripleBracket (design.atom leftLabel) (design.atom rightLabel)
              (design.atom third) ^ 2
            - pairBracketSq (design.atom leftLabel) (design.atom rightLabel)) ^ 2)
        = (∑ third, design.weight third
            * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
              (design.atom third) ^ 4)
          - 2 * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
            * (∑ third, design.weight third
              * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
                (design.atom third) ^ 2)
          + pairBracketSq (design.atom leftLabel) (design.atom rightLabel) ^ 2
            * ∑ third, design.weight third := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun third _ => by ring
    rw [hexpand, hmarginal, hmass] at hnonneg
    linarith
  have hstep : ∀ leftLabel rightLabel : Fin size,
      design.weight leftLabel * design.weight rightLabel
          * pairBracketSq (design.atom leftLabel) (design.atom rightLabel) ^ 2
        ≤ ∑ third, design.weight leftLabel * design.weight rightLabel * design.weight third
          * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
            (design.atom third) ^ 4 := by
    intro leftLabel rightLabel
    have hscale : (∑ third, design.weight leftLabel * design.weight rightLabel
          * design.weight third
          * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
            (design.atom third) ^ 4)
        = design.weight leftLabel * design.weight rightLabel
          * ∑ third, design.weight third
            * tripleBracket (design.atom leftLabel) (design.atom rightLabel)
              (design.atom third) ^ 4 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun third _ => by ring
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hrow leftLabel rightLabel)
      (mul_nonneg (design.weight_pos leftLabel).le (design.weight_pos rightLabel).le)
  unfold pairGramSecondMoment bracketFourthMoment
  refine Finset.sum_le_sum fun leftLabel _ => ?_
  exact Finset.sum_le_sum fun rightLabel _ => hstep leftLabel rightLabel

/-- **THE VOLUME-MEASURE GAP TRACE MOMENT IS AT LEAST THIRTY-SIX.** -/
theorem thirtysix_le_volumeLayer_gapTrace (design : WeightedDesign size 3) :
    36 ≤ volumeLayer design (gapTraceAt design) := by
  rw [volumeLayer_gapTrace]
  have hlev := nine_le_leverageSquareMoment design
  linarith

/-- **THE VOLUME-MEASURE GAP SECOND-INVARIANT MOMENT IS AT LEAST EIGHTEEN.**  The two square
expansions combine: the pair moment floor `4 m ≤ p₂` cancels the leverage term outright and
leaves the constant.  No hypothesis at all. -/
theorem eighteen_le_volumeLayer_gapSecond (design : WeightedDesign size 3) :
    18 ≤ volumeLayer design (gapSecondAt design) := by
  rw [volumeLayer_gapSecond]
  have hpair := four_mul_leverageSquareMoment_le_pairGramSecondMoment design
  linarith

/-! ## 5. The spanning triple with a positive second invariant -/

/-- **EVERY RANK-THREE DESIGN CARRIES A SPANNING TRIPLE WITH A POSITIVE SECOND GAP
INVARIANT.**  The volume-measure moment is at least eighteen, and a positive total of terms
with nonnegative brackets and positive weights produces a term whose bracket is nonzero and
whose reading is positive. -/
theorem exists_spanning_triple_gapSecond_pos (design : WeightedDesign size 3) :
    ∃ pivot left right : Fin size,
      0 < tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
        ∧ 0 < gapSecondAt design pivot left right := by
  by_contra hnone
  push Not at hnone
  have hterm : ∀ pivot left right : Fin size,
      design.weight pivot * design.weight left * design.weight right
        * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2
        * gapSecondAt design pivot left right ≤ 0 := by
    intro pivot left right
    rcases eq_or_lt_of_le (sq_nonneg
      (tripleBracket (design.atom pivot) (design.atom left) (design.atom right))) with
      hzero | hpos
    · rw [← hzero]; simp
    · have hread := hnone pivot left right hpos
      have hweights : 0 < design.weight pivot * design.weight left * design.weight right
          * tripleBracket (design.atom pivot) (design.atom left) (design.atom right) ^ 2 :=
        mul_pos (mul_pos (mul_pos (design.weight_pos pivot) (design.weight_pos left))
          (design.weight_pos right)) hpos
      exact mul_nonpos_of_nonneg_of_nonpos hweights.le hread
  have htotal : volumeLayer design (gapSecondAt design) ≤ 0 := by
    unfold volumeLayer
    refine Finset.sum_nonpos fun pivot _ => ?_
    refine Finset.sum_nonpos fun left _ => ?_
    exact Finset.sum_nonpos fun right _ => hterm pivot left right
  have hfloor := eighteen_le_volumeLayer_gapSecond design
  linarith

/-- The same statement with the distinctness of the three labels spelled out. -/
theorem exists_distinct_triple_gapSecond_pos (design : WeightedDesign size 3) :
    ∃ pivot left right : Fin size, pivot ≠ left ∧ pivot ≠ right ∧ left ≠ right
      ∧ 0 < gapSecondAt design pivot left right := by
  obtain ⟨pivot, left, right, hbracket, hread⟩ := exists_spanning_triple_gapSecond_pos design
  obtain ⟨hpl, hpr, hlr⟩ := distinct_of_bracket_sq_pos design hbracket
  exact ⟨pivot, left, right, hpl, hpr, hlr, hread⟩

/-! ## 6. What the ledger says at a `(6,3)` tie -/

/-- At a `(6,3)` tie every triple has a nonnegative gap trace.  The leverage floor is
unconditional. -/
theorem gapTrace_nonneg_of_isTie (design : WeightedDesign 6 3) (htie : IsTie design)
    (pivot left right : Fin 6) : 0 ≤ gapTraceAt design pivot left right := by
  have hpivot := leverage_one_le_of_isTie_sixThree design htie pivot
  have hleft := leverage_one_le_of_isTie_sixThree design htie left
  have hright := leverage_one_le_of_isTie_sixThree design htie right
  rw [gapTraceAt]
  linarith

/-- A three-element set from three distinct labels. -/
theorem card_tripleLedger_eq_three {pivot left right : Fin 6} (hpl : pivot ≠ left)
    (hpr : pivot ≠ right) (hlr : left ≠ right) :
    ({pivot, left, right} : Finset (Fin 6)).card = 3 :=
  Finset.card_eq_three.mpr ⟨pivot, left, right, hpl, hpr, hlr, rfl⟩

/-- **THE TWO-VALUED LABEL AT A TIE.**  At a `(6,3)` tie every spanning triple obeys
`e₂ < 0` or `e₃ ≤ 0`.  The third branch `e₁ = 0` that the original inertia bridge left open
is closed by the sharpened bridge, because the leverage floor already gives `0 ≤ e₁`. -/
theorem secondInvariant_neg_or_det_nonpos_of_isTie (design : WeightedDesign 6 3)
    (htie : IsTie design) {pivot left right : Fin 6} (hpl : pivot ≠ left) (hpr : pivot ≠ right)
    (hlr : left ≠ right) :
    gapSecondAt design pivot left right < 0 ∨ gapDetAt design pivot left right ≤ 0 := by
  by_contra hboth
  push Not at hboth
  obtain ⟨hsecond, hdet⟩ := hboth
  have hposDef : (subsetSum design ({pivot, left, right} : Finset (Fin 6)) - 1).PosDef := by
    refine posDef_of_invariants_nonneg_of_det_pos
      (isHermitian_subsetSum_sub_one design _) ?_ ?_ ?_
    · rw [trace_subsetSum_triple_sub_one design hpl hpr hlr]
      exact gapTrace_nonneg_of_isTie design htie pivot left right
    · rw [secondInvariantOfThree_subsetSum_triple_sub_one design hpl hpr hlr]
      exact hsecond
    · rw [det_subsetSum_triple_sub_one_eq_gapDetAt design hpl hpr hlr]
      exact hdet
  exact htie.2 _ (card_tripleLedger_eq_three hpl hpr hlr) hposDef

/-- **THE ALL-NEGATIVE LABEL PATTERN IS REFUTED.**  At a `(6,3)` tie there is a spanning
triple whose second gap invariant is STRICTLY POSITIVE, so the branch `e₂ < 0` cannot hold at
every triple.  That triple is then forced onto the other branch and its gap determinant is
nonpositive.

This is where the two halves meet.  The floor `18 ≤ Σ e₂ · w` is unconditional and comes from
the volume measure, which sees angles.  The label is unconditional at `(6,3)` and comes from
the leverage floor and the sharpened inertia bridge. -/
theorem exists_spanning_triple_gapDet_nonpos_of_isTie (design : WeightedDesign 6 3)
    (htie : IsTie design) :
    ∃ pivot left right : Fin 6, pivot ≠ left ∧ pivot ≠ right ∧ left ≠ right
      ∧ 0 < gapSecondAt design pivot left right
      ∧ gapDetAt design pivot left right ≤ 0 := by
  obtain ⟨pivot, left, right, hpl, hpr, hlr, hsecond⟩ :=
    exists_distinct_triple_gapSecond_pos design
  refine ⟨pivot, left, right, hpl, hpr, hlr, hsecond, ?_⟩
  rcases secondInvariant_neg_or_det_nonpos_of_isTie design htie hpl hpr hlr with hneg | hdet
  · linarith
  · exact hdet

/-- **THE GAP DETERMINANT OF THAT TRIPLE, IN THE MATRIX VOCABULARY.**  The same statement
read on `S_C − 1` rather than on the scalar readings. -/
theorem exists_triple_det_nonpos_of_isTie (design : WeightedDesign 6 3) (htie : IsTie design) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ 0 < secondInvariantOfThree (subsetSum design selected - 1)
      ∧ (subsetSum design selected - 1).det ≤ 0 := by
  obtain ⟨pivot, left, right, hpl, hpr, hlr, hsecond, hdet⟩ :=
    exists_spanning_triple_gapDet_nonpos_of_isTie design htie
  refine ⟨{pivot, left, right}, card_tripleLedger_eq_three hpl hpr hlr, ?_, ?_⟩
  · rw [secondInvariantOfThree_subsetSum_triple_sub_one design hpl hpr hlr]
    exact hsecond
  · rw [det_subsetSum_triple_sub_one_eq_gapDetAt design hpl hpr hlr]
    exact hdet

/-- **THE LABEL, ON SUBSETS.**  Every three-element subset of a `(6,3)` tie carries the
two-valued label.  Written on `Finset` so a counting argument over the twenty triples can
consume it directly. -/
theorem secondInvariant_neg_or_det_nonpos_of_isTie_subset (design : WeightedDesign 6 3)
    (htie : IsTie design) {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    secondInvariantOfThree (subsetSum design selected - 1) < 0
      ∨ (subsetSum design selected - 1).det ≤ 0 := by
  obtain ⟨pivot, left, right, hpl, hpr, hlr, hset⟩ := Finset.card_eq_three.mp hcard
  subst hset
  rcases secondInvariant_neg_or_det_nonpos_of_isTie design htie hpl hpr hlr with hneg | hdet
  · left
    rw [secondInvariantOfThree_subsetSum_triple_sub_one design hpl hpr hlr]
    exact hneg
  · right
    rw [det_subsetSum_triple_sub_one_eq_gapDetAt design hpl hpr hlr]
    exact hdet

/-! ## 7. The witness: two designs with one profile and two pair moments -/

/-- Every weight of the icosahedral design is `1/6`. -/
theorem icosaDesign_weight_apply (atomLabel : Fin 6) : icosaDesign.weight atomLabel = 1 / 6 :=
  rfl

/-- Every atom of the icosahedral design has leverage three. -/
theorem leverageOf_icosaDesign (atomLabel : Fin 6) :
    leverageOf (icosaDesign.atom atomLabel) = 3 := by
  rw [leverageOf_eq_dotProduct_self, icosaDesign_atom, icosaAtom_leverage]

/-- The pair Gram determinant of the icosahedral design: zero on the diagonal and `36/5`
off it.  Equiangularity at squared cosine `1/5` makes the table two-valued. -/
theorem icosaDesign_pairBracketSq (firstLabel secondLabel : Fin 6) :
    pairBracketSq (icosaDesign.atom firstLabel) (icosaDesign.atom secondLabel)
      = if firstLabel = secondLabel then 0 else 36 / 5 := by
  by_cases hsame : firstLabel = secondLabel
  · rw [hsame, if_pos rfl, pairBracketSq_self]
  · rw [if_neg hsame, pairBracketSq, leverageOf_eq_dotProduct_self,
      leverageOf_eq_dotProduct_self, icosaDesign_atom, icosaAtom_leverage,
      icosaAtom_leverage, icosaAtom_dot_sq_of_ne hsame]
    norm_num

/-- **THE SECOND PAIR MOMENT OF THE ICOSAHEDRAL DESIGN.**  Thirty ordered distinct pairs at
`36/5`, and six diagonal terms at zero. -/
theorem pairGramSecondMoment_icosaDesign :
    pairGramSecondMoment icosaDesign = 216 / 5 := by
  have hterm : ∀ firstLabel secondLabel : Fin 6,
      icosaDesign.weight firstLabel * icosaDesign.weight secondLabel
          * pairBracketSq (icosaDesign.atom firstLabel) (icosaDesign.atom secondLabel) ^ 2
        = 1 / 36 * (if firstLabel = secondLabel then 0 else 36 / 5) ^ 2 := by
    intro firstLabel secondLabel
    rw [icosaDesign_weight_apply, icosaDesign_weight_apply, icosaDesign_pairBracketSq]
    ring
  rw [pairGramSecondMoment, Finset.sum_congr rfl fun firstLabel _ =>
    Finset.sum_congr rfl fun secondLabel _ => hterm firstLabel secondLabel]
  simp only [Fin.sum_univ_six]
  norm_num [Fin.ext_iff]

/-- **THE SECOND PAIR MOMENT OF THE ROOT DESIGN.**  The tetrahedral edge directions carry
TWO squared cosines, so the table is three-valued: zero on the diagonal, `9` at the three
orthogonal partners, and `27/4` at the remaining twenty-four ordered pairs. -/
theorem pairGramSecondMoment_coordinateDiagonalDesign :
    pairGramSecondMoment coordinateDiagonalDesign = 351 / 8 := by
  have hterm : ∀ firstLabel secondLabel : Fin 6,
      coordinateDiagonalDesign.weight firstLabel * coordinateDiagonalDesign.weight secondLabel
          * pairBracketSq (coordinateDiagonalDesign.atom firstLabel)
            (coordinateDiagonalDesign.atom secondLabel) ^ 2
        = 1 / 36 * (3 / 2 * (diagonalPattern firstLabel ⬝ᵥ diagonalPattern firstLabel)
            * (3 / 2 * (diagonalPattern secondLabel ⬝ᵥ diagonalPattern secondLabel))
          - (3 / 2 * (diagonalPattern firstLabel ⬝ᵥ diagonalPattern secondLabel)) ^ 2) ^ 2 := by
    intro firstLabel secondLabel
    rw [coordinateDiagonalDesign_weight_apply, coordinateDiagonalDesign_weight_apply,
      coordinateDiagonalDesign_pairBracketSq]
    ring
  rw [pairGramSecondMoment, Finset.sum_congr rfl fun firstLabel _ =>
    Finset.sum_congr rfl fun secondLabel _ => hterm firstLabel secondLabel]
  simp only [Fin.sum_univ_six]
  norm_num [diagonalPattern_zero, diagonalPattern_one, diagonalPattern_two,
    diagonalPattern_three, diagonalPattern_four, diagonalPattern_five, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- The second leverage moment of a `(6,3)` design at uniform weight `1/6` and uniform
leverage `3` is nine, the floor of `Gtz.nine_le_leverageSquareMoment`. -/
theorem leverageSquareMoment_icosaDesign : leverageSquareMoment icosaDesign = 9 := by
  have hterm : ∀ atomLabel : Fin 6,
      icosaDesign.weight atomLabel * leverageOf (icosaDesign.atom atomLabel) ^ 2
        = 3 / 2 := by
    intro atomLabel
    rw [icosaDesign_weight_apply, leverageOf_icosaDesign]
    norm_num
  rw [leverageSquareMoment, Finset.sum_congr rfl fun atomLabel _ => hterm atomLabel]
  simp only [Fin.sum_univ_six]
  norm_num

/-- The same at the root design. -/
theorem leverageSquareMoment_coordinateDiagonalDesign :
    leverageSquareMoment coordinateDiagonalDesign = 9 := by
  have hterm : ∀ atomLabel : Fin 6,
      coordinateDiagonalDesign.weight atomLabel
          * leverageOf (coordinateDiagonalDesign.atom atomLabel) ^ 2 = 3 / 2 := by
    intro atomLabel
    rw [coordinateDiagonalDesign_weight_apply, leverageOf_coordinateDiagonalDesign]
    norm_num
  rw [leverageSquareMoment, Finset.sum_congr rfl fun atomLabel _ => hterm atomLabel]
  simp only [Fin.sum_univ_six]
  norm_num

/-- **THE TWO DESIGNS CARRY ONE PROFILE.**  Equal weights label by label, and equal
leverages label by label. -/
theorem icosaDesign_coordinateDiagonalDesign_same_profile :
    (∀ atomLabel : Fin 6,
        icosaDesign.weight atomLabel = coordinateDiagonalDesign.weight atomLabel)
      ∧ ∀ atomLabel : Fin 6, leverageOf (icosaDesign.atom atomLabel)
          = leverageOf (coordinateDiagonalDesign.atom atomLabel) := by
  refine ⟨fun atomLabel => ?_, fun atomLabel => ?_⟩
  · rw [icosaDesign_weight_apply, coordinateDiagonalDesign_weight_apply]
  · rw [leverageOf_icosaDesign, leverageOf_coordinateDiagonalDesign]

/-- **THE SECOND PAIR MOMENT IS NOT A FUNCTION OF THE PROFILE.**  One weight profile, one
leverage profile, two values. -/
theorem pairGramSecondMoment_not_determined_by_profile :
    pairGramSecondMoment icosaDesign ≠ pairGramSecondMoment coordinateDiagonalDesign := by
  rw [pairGramSecondMoment_icosaDesign, pairGramSecondMoment_coordinateDiagonalDesign]
  norm_num

/-- **THE PRODUCT MEASURE CANNOT TELL THE WITNESS PAIR APART.**  Both values are the
universal constant three. -/
theorem productLayer_gapSecond_agrees_at_the_witness :
    productLayer icosaDesign (gapSecondAt icosaDesign)
      = productLayer coordinateDiagonalDesign (gapSecondAt coordinateDiagonalDesign) := by
  rw [productLayer_gapSecond, productLayer_gapSecond]

/-- The volume-measure gap second moment of the icosahedral design. -/
theorem volumeLayer_gapSecond_icosaDesign :
    volumeLayer icosaDesign (gapSecondAt icosaDesign) = 198 / 5 := by
  rw [volumeLayer_gapSecond, pairGramSecondMoment_icosaDesign,
    leverageSquareMoment_icosaDesign]
  norm_num

/-- The volume-measure gap second moment of the root design. -/
theorem volumeLayer_gapSecond_coordinateDiagonalDesign :
    volumeLayer coordinateDiagonalDesign (gapSecondAt coordinateDiagonalDesign) = 333 / 8 := by
  rw [volumeLayer_gapSecond, pairGramSecondMoment_coordinateDiagonalDesign,
    leverageSquareMoment_coordinateDiagonalDesign]
  norm_num

/-- **THE VOLUME MEASURE TELLS THE WITNESS PAIR APART.**  The two designs share a weight
profile and a leverage profile, and the product-measure moment is the same constant at both,
but the volume-measure moment is `198/5` at one and `333/8` at the other.  So the volume
layer reads something that no functional of the weight-and-leverage profile can read, and the
angle-blindness that closes the product family does not close this one. -/
theorem volumeLayer_gapSecond_differs_at_the_witness :
    volumeLayer icosaDesign (gapSecondAt icosaDesign)
      ≠ volumeLayer coordinateDiagonalDesign (gapSecondAt coordinateDiagonalDesign) := by
  rw [volumeLayer_gapSecond_icosaDesign, volumeLayer_gapSecond_coordinateDiagonalDesign]
  norm_num

end Gtz
