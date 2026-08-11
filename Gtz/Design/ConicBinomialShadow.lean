import Gtz.Design.PairingMinorPlueckerBridge
import Gtz.Design.StressFreeStratum
import Gtz.Design.PairDifferenceCover
import Gtz.Design.LiftCriterion
import Gtz.Design.LineFreeConicBridge
import Gtz.Quantitative.PhaseFreeNoGo
import Gtz.Core.Sanity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix

/-!
# The polarized cross-axis Parseval, and what the pairing-minor bridge really is

`Gtz.sum_weight_mul_atomBracket_sq` is the DIAGONAL cross-axis Parseval: the
weighted squares of the brackets through a fixed pair total that pair's cross-axis
budget.  This file supplies the POLARIZED form, which the tree did not have:

    pairingMinor a_L a_R a_p a_q  =  sum over y of  t_y * [L,R,y] * [p,q,y] .

So the whole metric pairing-minor algebra of
`Gtz/Design/PairingMinorPlueckerBridge.lean` is a positive-weight bracket bilinear
form.  Three consequences are recorded here.

FIRST, `pairArea` at atoms IS the landed `Gtz.crossAxisBudget`.  The lane module
introduced a second name for a formula the tree already had, and proved
`0 < pairArea` from liveness where `Gtz.one_lt_crossAxisBudget_of_isLivePair`
already gives `1 < crossAxisBudget` from the same hypothesis.

SECOND, and this is the reason the file exists: the `IsLivePair` hypothesis of
`Gtz.weighted_atom_pairing_covariance_three_pos_of_lineFree` is REDUNDANT.  One
nonvanishing bracket through the pair already forces `0 < crossAxisBudget`, and
line-freeness supplies one at every distinct pair.  The strengthened statement
below asks only for distinctness and covers the pairs that are not live -- at
`Gtz.baseTieKillerDesign` that is six of the fifteen pairs, at
`Gtz.freePairKillerDesign` six, at `Gtz.windowRefusalWitnessDesign` five.  This is
line-freeness entering as a NONVANISHING that produces a strict sign, with no
magnitude bounded below anywhere: exactly the admissible shape, and with no
live-pair input at all.

THIRD, the second-exterior Parseval law: the cross axes of the pairs, weighted by
the products of the two weights, are themselves a Parseval frame of total mass two.
Its trace is `sum over pairs of t_i t_j * crossAxisBudget = 3`.
-/

/-- The bracket, read as a pairing against the bracket normal of its LAST two
slots. -/
theorem tripleBracket_eq_dotProduct_bracketNormal_right
    (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec rightVec = leftVec ⬝ᵥ bracketNormal midVec rightVec := by
  simp only [tripleBracket_eq, bracketNormal, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- **The pairing minor is the Euclidean pairing of two bracket normals.**  This
is the Binet--Cauchy identity, and it is what makes every statement of
`Gtz/Design/PairingMinorPlueckerBridge.lean` a statement about the cross axes. -/
theorem pairingMinor_eq_bracketNormal_dotProduct
    (leftVec rightVec firstVec secondVec : Fin 3 → ℝ) :
    pairingMinor leftVec rightVec firstVec secondVec
      = bracketNormal leftVec rightVec ⬝ᵥ bracketNormal firstVec secondVec := by
  simp only [pairingMinor, bracketNormal, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- The pair area is the squared length of the bracket normal. -/
theorem pairArea_eq_bracketNormal_dotProduct_self (leftVec rightVec : Fin 3 → ℝ) :
    pairArea leftVec rightVec
      = bracketNormal leftVec rightVec ⬝ᵥ bracketNormal leftVec rightVec := by
  rw [bracketNormal_self_dotProduct, pairArea]

/-- **`pairArea` at atoms is the landed `Gtz.crossAxisBudget`.**  Same formula,
two names. -/
theorem pairArea_atom_eq_crossAxisBudget {m : ℕ} (design : WeightedDesign m 3)
    (leftLabel rightLabel : Fin m) :
    pairArea (design.atom leftLabel) (design.atom rightLabel)
      = crossAxisBudget design leftLabel rightLabel := by
  simp only [pairArea, crossAxisBudget, atomPairing, dotProduct_self_eq_leverageOf]

/-- **THE POLARIZED CROSS-AXIS PARSEVAL.**  The metric pairing minor of two label
pairs is the weighted bracket bilinear form of those pairs.  Hypothesis-free, any
size.  Specializing both pairs to the same one recovers
`Gtz.sum_weight_mul_atomBracket_sq`. -/
theorem pairingMinor_atom_eq_sum_weight_mul_atomBracket {m : ℕ}
    (design : WeightedDesign m 3) (leftLabel rightLabel firstLabel secondLabel : Fin m) :
    pairingMinor (design.atom leftLabel) (design.atom rightLabel)
        (design.atom firstLabel) (design.atom secondLabel)
      = ∑ probeLabel, design.weight probeLabel
          * (atomBracket design leftLabel rightLabel probeLabel
            * atomBracket design firstLabel secondLabel probeLabel) := by
  rw [pairingMinor_eq_bracketNormal_dotProduct,
    dotProduct_eq_sum_weight_mul_pair design
      (bracketNormal (design.atom leftLabel) (design.atom rightLabel))
      (bracketNormal (design.atom firstLabel) (design.atom secondLabel))]
  refine Finset.sum_congr rfl fun probeLabel _ => ?_
  rw [atomBracket, atomBracket, tripleBracket_eq_bracketNormal_dotProduct,
    tripleBracket_eq_bracketNormal_dotProduct,
    dotProduct_comm (bracketNormal (design.atom leftLabel) (design.atom rightLabel))
      (design.atom probeLabel),
    dotProduct_comm (bracketNormal (design.atom firstLabel) (design.atom secondLabel))
      (design.atom probeLabel)]

/-- **One nonvanishing bracket through a pair makes its cross-axis budget strictly
positive.**  No liveness, no heaviness, no domination -- this is the whole of what
`Gtz.pairArea_pos_of_isLivePair` was used for, from a strictly weaker hypothesis. -/
theorem pos_crossAxisBudget_of_atomBracket_ne_zero {m : ℕ} (design : WeightedDesign m 3)
    {leftLabel rightLabel probeLabel : Fin m}
    (hbracket : atomBracket design leftLabel rightLabel probeLabel ≠ 0) :
    0 < crossAxisBudget design leftLabel rightLabel := by
  rw [← sum_weight_mul_atomBracket_sq design leftLabel rightLabel]
  refine Finset.sum_pos' (fun otherLabel _ => ?_) ⟨probeLabel, Finset.mem_univ probeLabel, ?_⟩
  · exact mul_nonneg (design.weight_pos otherLabel).le (sq_nonneg _)
  · exact mul_pos (design.weight_pos probeLabel) (pow_pos (abs_pos.mpr hbracket) 2 |>.trans_le
      (le_of_eq (sq_abs _)))

/-- **The covariance theorem without the redundant live-pair hypothesis.**  For a
line-free `(6,3)` design, ANY two distinct labels and any three distinct labels give
a strictly positive weighted covariance determinant of the two pairing columns. -/
theorem weighted_atom_pairing_covariance_three_pos_of_lineFree_of_ne
    (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {leftLabel rightLabel firstLabel secondLabel thirdLabel : Fin 6}
    (hleftRight : leftLabel ≠ rightLabel)
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    0 <
      (design.weight firstLabel
            * (design.atom leftLabel ⬝ᵥ design.atom firstLabel) ^ 2
          + design.weight secondLabel
            * (design.atom leftLabel ⬝ᵥ design.atom secondLabel) ^ 2
          + design.weight thirdLabel
            * (design.atom leftLabel ⬝ᵥ design.atom thirdLabel) ^ 2)
        * (design.weight firstLabel
            * (design.atom rightLabel ⬝ᵥ design.atom firstLabel) ^ 2
          + design.weight secondLabel
            * (design.atom rightLabel ⬝ᵥ design.atom secondLabel) ^ 2
          + design.weight thirdLabel
            * (design.atom rightLabel ⬝ᵥ design.atom thirdLabel) ^ 2)
        - (design.weight firstLabel
              * (design.atom leftLabel ⬝ᵥ design.atom firstLabel)
              * (design.atom rightLabel ⬝ᵥ design.atom firstLabel)
          + design.weight secondLabel
              * (design.atom leftLabel ⬝ᵥ design.atom secondLabel)
              * (design.atom rightLabel ⬝ᵥ design.atom secondLabel)
          + design.weight thirdLabel
              * (design.atom leftLabel ⬝ᵥ design.atom thirdLabel)
              * (design.atom rightLabel ⬝ᵥ design.atom thirdLabel)) ^ 2 := by
  obtain ⟨spareLabel, hspareLeft, hspareRight⟩ :
      ∃ spareLabel : Fin 6, spareLabel ≠ leftLabel ∧ spareLabel ≠ rightLabel := by
    revert hleftRight
    revert leftLabel rightLabel
    decide
  have hpairArea : pairArea (design.atom leftLabel) (design.atom rightLabel) ≠ 0 := by
    rw [pairArea_atom_eq_crossAxisBudget]
    exact (pos_crossAxisBudget_of_atomBracket_ne_zero design
      (atomBracket_ne_zero_of_lineFree design hlineFree hleftRight
        (Ne.symm hspareLeft) (Ne.symm hspareRight))).ne'
  apply weighted_pairing_covariance_three_pos
  · exact design.weight_pos firstLabel
  · exact design.weight_pos secondLabel
  · exact design.weight_pos thirdLabel
  · exact exists_pairingMinor_ne_zero hpairArea
      (by
        simpa only [atomBracket] using
          atomBracket_ne_zero_of_lineFree design hlineFree hfirstSecond hfirstThird
            hsecondThird)

/-- **THE SECOND-EXTERIOR PARSEVAL LAW.**  The cross axes of the label pairs,
weighted by the products of the two weights, form a Parseval frame of total mass
two.  No hypothesis beyond the design; the diagonal terms vanish on their own
because a cross axis of a label with itself is zero. -/
theorem sum_weight_pair_mul_tripleBracket_sq {m : ℕ} (design : WeightedDesign m 3)
    (probeVec : Fin 3 → ℝ) :
    ∑ pairFirst, ∑ pairSecond,
        design.weight pairFirst * design.weight pairSecond
          * tripleBracket (design.atom pairFirst) (design.atom pairSecond) probeVec ^ 2
      = 2 * (probeVec ⬝ᵥ probeVec) := by
  have hinner : ∀ pairFirst : Fin m,
      ∑ pairSecond, design.weight pairFirst * design.weight pairSecond
          * tripleBracket (design.atom pairFirst) (design.atom pairSecond) probeVec ^ 2
        = design.weight pairFirst
            * (leverageOf (design.atom pairFirst) * (probeVec ⬝ᵥ probeVec)
              - (design.atom pairFirst ⬝ᵥ probeVec) ^ 2) := by
    intro pairFirst
    have hrotate : ∀ pairSecond : Fin m,
        tripleBracket (design.atom pairFirst) (design.atom pairSecond) probeVec
          = design.atom pairSecond ⬝ᵥ bracketNormal probeVec (design.atom pairFirst) := by
      intro pairSecond
      rw [← tripleBracket_eq_dotProduct_bracketNormal_right, tripleBracket_rotate,
        tripleBracket_rotate]
    calc
      ∑ pairSecond, design.weight pairFirst * design.weight pairSecond
            * tripleBracket (design.atom pairFirst) (design.atom pairSecond) probeVec ^ 2
          = design.weight pairFirst
              * ∑ pairSecond, design.weight pairSecond
                * (design.atom pairSecond
                    ⬝ᵥ bracketNormal probeVec (design.atom pairFirst)) ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun pairSecond _ => by rw [hrotate pairSecond]; ring
      _ = design.weight pairFirst
              * (bracketNormal probeVec (design.atom pairFirst)
                  ⬝ᵥ bracketNormal probeVec (design.atom pairFirst)) := by
            rw [← dotProduct_self_eq_sum_weight_mul_sq design
              (bracketNormal probeVec (design.atom pairFirst))]
      _ = design.weight pairFirst
              * (leverageOf (design.atom pairFirst) * (probeVec ⬝ᵥ probeVec)
                - (design.atom pairFirst ⬝ᵥ probeVec) ^ 2) := by
            rw [bracketNormal_self_dotProduct, dotProduct_self_eq_leverageOf,
              dotProduct_self_eq_leverageOf, dotProduct_comm probeVec (design.atom pairFirst)]
            ring
  rw [Finset.sum_congr rfl fun pairFirst _ => hinner pairFirst]
  have hsplit :
      ∑ pairFirst, design.weight pairFirst
            * (leverageOf (design.atom pairFirst) * (probeVec ⬝ᵥ probeVec)
              - (design.atom pairFirst ⬝ᵥ probeVec) ^ 2)
        = (∑ pairFirst, design.weight pairFirst * leverageOf (design.atom pairFirst))
              * (probeVec ⬝ᵥ probeVec)
            - ∑ pairFirst, design.weight pairFirst
                * (design.atom pairFirst ⬝ᵥ probeVec) ^ 2 := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun pairFirst _ => by ring
  rw [hsplit, sum_weighted_leverage design,
    ← dotProduct_self_eq_sum_weight_mul_sq design probeVec]
  push_cast
  ring

/-- The trace of the second-exterior Parseval law: the weighted total of the
cross-axis budgets over all ordered label pairs is `2 * 3 = 6`. -/
theorem sum_weight_pair_mul_crossAxisBudget {m : ℕ} (design : WeightedDesign m 3) :
    ∑ pairFirst, ∑ pairSecond,
        design.weight pairFirst * design.weight pairSecond
          * crossAxisBudget design pairFirst pairSecond
      = 6 := by
  have haxisNorm : ∀ coord : Fin 3,
      (Pi.single coord (1 : ℝ)) ⬝ᵥ (Pi.single coord (1 : ℝ)) = 1 := by
    intro coord
    simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  have hcoord : ∀ coord : Fin 3,
      ∑ pairFirst, ∑ pairSecond,
          design.weight pairFirst * design.weight pairSecond
            * tripleBracket (design.atom pairFirst) (design.atom pairSecond)
                (Pi.single coord 1) ^ 2
        = 2 := by
    intro coord
    rw [sum_weight_pair_mul_tripleBracket_sq design (Pi.single coord (1 : ℝ)),
      haxisNorm coord]
    norm_num
  have hcomponent : ∀ (pairFirst pairSecond : Fin m) (coord : Fin 3),
      tripleBracket (design.atom pairFirst) (design.atom pairSecond) (Pi.single coord 1)
        = bracketNormal (design.atom pairFirst) (design.atom pairSecond) coord := by
    intro pairFirst pairSecond coord
    rw [tripleBracket_eq_bracketNormal_dotProduct]
    simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  have hbudget : ∀ pairFirst pairSecond : Fin m,
      ∑ coord : Fin 3,
          tripleBracket (design.atom pairFirst) (design.atom pairSecond)
            (Pi.single coord 1) ^ 2
        = crossAxisBudget design pairFirst pairSecond := by
    intro pairFirst pairSecond
    rw [← pairArea_atom_eq_crossAxisBudget, pairArea_eq_bracketNormal_dotProduct_self]
    simp only [hcomponent, dotProduct, sq]
  calc
    ∑ pairFirst, ∑ pairSecond,
          design.weight pairFirst * design.weight pairSecond
            * crossAxisBudget design pairFirst pairSecond
        = ∑ pairFirst, ∑ pairSecond, ∑ coord : Fin 3,
            design.weight pairFirst * design.weight pairSecond
              * tripleBracket (design.atom pairFirst) (design.atom pairSecond)
                  (Pi.single coord 1) ^ 2 := by
          refine Finset.sum_congr rfl fun pairFirst _ =>
            Finset.sum_congr rfl fun pairSecond _ => ?_
          rw [← hbudget pairFirst pairSecond, Finset.mul_sum]
    _ = ∑ pairFirst, ∑ coord : Fin 3, ∑ pairSecond,
            design.weight pairFirst * design.weight pairSecond
              * tripleBracket (design.atom pairFirst) (design.atom pairSecond)
                  (Pi.single coord 1) ^ 2 :=
          Finset.sum_congr rfl fun pairFirst _ => Finset.sum_comm
    _ = ∑ coord : Fin 3, ∑ pairFirst, ∑ pairSecond,
            design.weight pairFirst * design.weight pairSecond
              * tripleBracket (design.atom pairFirst) (design.atom pairSecond)
                  (Pi.single coord 1) ^ 2 := Finset.sum_comm
    _ = 6 := by rw [Finset.sum_congr rfl fun coord _ => hcoord coord]; norm_num

/-! ## Off-conicity in the Gram alone

`Gtz.hasNoCommonQuadric_iff_veroneseGrid_det_ne_zero` reads off-conicity off a
determinant of the ATOMS.  The three statements below move it into the GRAM, where
line-freeness and the whole refusal system already live: the entrywise square of
the atom Gram is the Veronese Gram, so it is positive semidefinite, and
off-conicity is exactly its nonsingularity.  Nothing here needs a chart, a base
triple, a bracket or a weight. -/

/-- The entrywise square of the atom Gram of a six-atom family. -/
def squaredPairingGrid (atomFamily : Fin 6 → Fin 3 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun leftIndex rightIndex =>
    (atomFamily leftIndex ⬝ᵥ atomFamily rightIndex) ^ 2

/-- **The entrywise square of the Gram IS the Veronese Gram**, with the diagonal
`(1,1,1,2,2,2)` that the `(x^2, y^2, z^2, xy, xz, yz)` ordering forces. -/
theorem squaredPairingGrid_eq_veroneseGrid_congr (atomFamily : Fin 6 → Fin 3 → ℝ) :
    squaredPairingGrid atomFamily
      = veroneseGrid atomFamily * Matrix.diagonal ![1, 1, 1, 2, 2, 2]
          * (veroneseGrid atomFamily)ᵀ := by
  ext leftIndex rightIndex
  simp [squaredPairingGrid, Matrix.mul_apply, Matrix.diagonal_apply, veroneseGrid,
    veroneseCoords, Fin.sum_univ_six, dotProduct, Fin.sum_univ_three]
  ring

/-- The determinant of the squared-pairing grid is eight times the square of the
Veronese determinant. -/
theorem det_squaredPairingGrid (atomFamily : Fin 6 → Fin 3 → ℝ) :
    (squaredPairingGrid atomFamily).det = 8 * (veroneseGrid atomFamily).det ^ 2 := by
  rw [squaredPairingGrid_eq_veroneseGrid_congr, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_diagonal]
  simp [Fin.prod_univ_six]
  ring

/-- **OFF-CONICITY IS ONE GRAM DETERMINANT.**  No chart, no base triple, no
bracket, no weight: the six directions lie on no common conic exactly when the
entrywise square of their Gram matrix is nonsingular. -/
theorem hasNoCommonQuadric_iff_det_squaredPairingGrid_ne_zero
    (atomFamily : Fin 6 → Fin 3 → ℝ) :
    HasNoCommonQuadric atomFamily ↔ (squaredPairingGrid atomFamily).det ≠ 0 := by
  rw [hasNoCommonQuadric_iff_veroneseGrid_det_ne_zero, det_squaredPairingGrid]
  constructor
  · intro hveronese hzero
    exact hveronese (by
      have hsquare : (veroneseGrid atomFamily).det ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (two_ne_zero) |>.mp hsquare)
  · intro hproduct hveronese
    exact hproduct (by rw [hveronese]; ring)

/-- The squared-pairing grid is positive semidefinite, so off-conicity is a STRICT
POSITIVITY: `0 < det` off every conic, `0 = det` on one. -/
theorem posSemidef_squaredPairingGrid (atomFamily : Fin 6 → Fin 3 → ℝ) :
    (squaredPairingGrid atomFamily).PosSemidef := by
  rw [squaredPairingGrid_eq_veroneseGrid_congr]
  have hdiagonal : (Matrix.diagonal ![(1 : ℝ), 1, 1, 2, 2, 2]).PosSemidef := by
    refine Matrix.posSemidef_diagonal_iff.mpr fun index => ?_
    fin_cases index <;> norm_num
  simpa [Matrix.mul_assoc] using hdiagonal.mul_mul_conjTranspose_same
    (veroneseGrid atomFamily)

/-! ## Part two.  The octahedral binomials: off-conicity in the
bracket-square layer

`Gtz.hasNoCommonQuadric_iff_det_squaredPairingGrid_ne_zero` above puts off-conicity
in the GRAM.  The two statements of this part put its combinatorial skeleton in the
BRACKETS, and in a form the Cauchy-Binet layer can read.

The eight triples carrying the two four-bracket products of the landed axis-base
identity `Gtz.freeOffDiagonalGrid_det_eq_bracketProducts` are the eight faces of an
OCTAHEDRON whose three antipodal pairs are `{0,5}`, `{1,4}`, `{2,3}`: a face meets
each antipodal pair once, and the two four-bracket products are the two alternating
classes of four faces.  The decomposition is therefore indexed by a PERFECT MATCHING
of the six labels, and there are FIFTEEN of them, not one.

Two facts follow, and the second is the point.

  * Every triple is a face of exactly six of the fifteen octahedra, because a triple
    is a face for a matching exactly when the matching pairs it bijectively with its
    complement.  So the product of all thirty class-products is the product of all
    twenty brackets to the sixth power -- a strictly positive number as soon as the
    family is line-free.

  * FIFTEEN IS ODD.  So if every one of the fifteen binomials
    `oddProduct ^ 2 = evenProduct ^ 2` holds -- and each of those is an identity
    between two MONOMIALS in the twenty squared brackets, hence a statement the
    bracket-square coordinate can express -- then an even number of the fifteen can
    have `oddProduct = -evenProduct`, so at least one has `oddProduct = evenProduct`.

Measured outside Lean and NOT mechanized here: an octahedral coincidence
`oddProduct = evenProduct` is exactly `(Gtz.veroneseGrid atomFamily).det = 0`, for
every one of the fifteen matchings, so the theorem below says that on the line-free
locus the fifteen binomials TOGETHER are equivalent to lying on a common conic --
and hence that OFF-conicity is the failure of at least one explicit binomial in the
twenty squared brackets.  The unmechanized leg is the general six-point identity
`(veroneseGrid atomFamily).det = P - Q`, verified at nine tree fixtures and four
thousand random integer configurations with zero failures. -/

/-- The bracket of three atoms of a six-vector family, addressed by label.  This is
`Gtz.atomBracket` without a weighted design attached. -/
def familyBracket (atomFamily : Fin 6 → Fin 3 → ℝ)
    (leftLabel midLabel rightLabel : Fin 6) : ℝ :=
  tripleBracket (atomFamily leftLabel) (atomFamily midLabel) (atomFamily rightLabel)

/-- Relabelling the six directions by a transposition FLIPS the sign of the
off-conic determinant. -/
theorem det_veroneseGrid_swap (atomFamily : Fin 6 → Fin 3 → ℝ)
    {leftLabel rightLabel : Fin 6} (hne : leftLabel ≠ rightLabel) :
    (veroneseGrid (fun label => atomFamily (Equiv.swap leftLabel rightLabel label))).det
      = -(veroneseGrid atomFamily).det := by
  have hsub : veroneseGrid (fun label => atomFamily (Equiv.swap leftLabel rightLabel label))
      = (veroneseGrid atomFamily).submatrix (Equiv.swap leftLabel rightLabel) id := rfl
  rw [hsub, Matrix.det_permute, Equiv.Perm.sign_swap hne]
  simp

/-- **ONLY THE SQUARE OF THE OFF-CONIC DETERMINANT IS A RELABELLING INVARIANT.**
Together with `Gtz.det_veroneseGrid_swap` this says that the SIGN of the off-conic
determinant -- equivalently the sign of the four-bracket difference `P - Q` -- is
not a property of the six directions at all: both signs are realised by
relabellings of one and the same family.  Any certificate that consumes that sign
must first break the symmetric group, and nothing distinguishes a labelling. -/
theorem sq_det_veroneseGrid_relabel (atomFamily : Fin 6 → Fin 3 → ℝ)
    (relabel : Equiv.Perm (Fin 6)) :
    (veroneseGrid (fun label => atomFamily (relabel label))).det ^ 2
      = (veroneseGrid atomFamily).det ^ 2 := by
  have hsub : veroneseGrid (fun label => atomFamily (relabel label))
      = (veroneseGrid atomFamily).submatrix relabel id := rfl
  rw [hsub, Matrix.det_permute, mul_pow]
  rcases Int.units_eq_one_or (Equiv.Perm.sign relabel) with hsign | hsign <;>
    rw [hsign] <;> norm_num

/-- For each of the fifteen perfect matchings of the six labels -- equivalently
each way of seeing the six directions as the antipodal pairs of an octahedron -- the
product of the four brackets of the faces of ODD parity, every face written in
increasing label order.  The matchings are listed lexicographically. -/
def octahedralOddProduct (atomFamily : Fin 6 → Fin 3 → ℝ) : Fin 15 → ℝ :=
  ![familyBracket atomFamily 0 2 5 * familyBracket atomFamily 0 3 4 * familyBracket atomFamily 1 2 4 * familyBracket atomFamily 1 3 5,
    familyBracket atomFamily 0 2 5 * familyBracket atomFamily 0 3 4 * familyBracket atomFamily 1 2 3 * familyBracket atomFamily 1 4 5,
    familyBracket atomFamily 0 2 4 * familyBracket atomFamily 0 3 5 * familyBracket atomFamily 1 2 3 * familyBracket atomFamily 1 4 5,
    familyBracket atomFamily 0 1 5 * familyBracket atomFamily 0 3 4 * familyBracket atomFamily 1 2 4 * familyBracket atomFamily 2 3 5,
    familyBracket atomFamily 0 1 5 * familyBracket atomFamily 0 3 4 * familyBracket atomFamily 1 2 3 * familyBracket atomFamily 2 4 5,
    familyBracket atomFamily 0 1 4 * familyBracket atomFamily 0 3 5 * familyBracket atomFamily 1 2 3 * familyBracket atomFamily 2 4 5,
    familyBracket atomFamily 0 1 5 * familyBracket atomFamily 0 2 4 * familyBracket atomFamily 1 3 4 * familyBracket atomFamily 2 3 5,
    familyBracket atomFamily 0 1 5 * familyBracket atomFamily 0 2 4 * familyBracket atomFamily 1 2 3 * familyBracket atomFamily 3 4 5,
    familyBracket atomFamily 0 1 4 * familyBracket atomFamily 0 2 5 * familyBracket atomFamily 1 2 3 * familyBracket atomFamily 3 4 5,
    familyBracket atomFamily 0 1 5 * familyBracket atomFamily 0 2 3 * familyBracket atomFamily 1 3 4 * familyBracket atomFamily 2 4 5,
    familyBracket atomFamily 0 1 5 * familyBracket atomFamily 0 2 3 * familyBracket atomFamily 1 2 4 * familyBracket atomFamily 3 4 5,
    familyBracket atomFamily 0 1 3 * familyBracket atomFamily 0 2 5 * familyBracket atomFamily 1 2 4 * familyBracket atomFamily 3 4 5,
    familyBracket atomFamily 0 1 4 * familyBracket atomFamily 0 2 3 * familyBracket atomFamily 1 3 5 * familyBracket atomFamily 2 4 5,
    familyBracket atomFamily 0 1 4 * familyBracket atomFamily 0 2 3 * familyBracket atomFamily 1 2 5 * familyBracket atomFamily 3 4 5,
    familyBracket atomFamily 0 1 3 * familyBracket atomFamily 0 2 4 * familyBracket atomFamily 1 2 5 * familyBracket atomFamily 3 4 5]

/-- The companion product over the four faces of EVEN parity, in the same matching
order. -/
def octahedralEvenProduct (atomFamily : Fin 6 → Fin 3 → ℝ) : Fin 15 → ℝ :=
  ![familyBracket atomFamily 0 2 4 * familyBracket atomFamily 0 3 5 * familyBracket atomFamily 1 2 5 * familyBracket atomFamily 1 3 4,
    familyBracket atomFamily 0 2 3 * familyBracket atomFamily 0 4 5 * familyBracket atomFamily 1 2 5 * familyBracket atomFamily 1 3 4,
    familyBracket atomFamily 0 2 3 * familyBracket atomFamily 0 4 5 * familyBracket atomFamily 1 2 4 * familyBracket atomFamily 1 3 5,
    familyBracket atomFamily 0 1 4 * familyBracket atomFamily 0 3 5 * familyBracket atomFamily 1 2 5 * familyBracket atomFamily 2 3 4,
    familyBracket atomFamily 0 1 3 * familyBracket atomFamily 0 4 5 * familyBracket atomFamily 1 2 5 * familyBracket atomFamily 2 3 4,
    familyBracket atomFamily 0 1 3 * familyBracket atomFamily 0 4 5 * familyBracket atomFamily 1 2 4 * familyBracket atomFamily 2 3 5,
    familyBracket atomFamily 0 1 4 * familyBracket atomFamily 0 2 5 * familyBracket atomFamily 1 3 5 * familyBracket atomFamily 2 3 4,
    familyBracket atomFamily 0 1 2 * familyBracket atomFamily 0 4 5 * familyBracket atomFamily 1 3 5 * familyBracket atomFamily 2 3 4,
    familyBracket atomFamily 0 1 2 * familyBracket atomFamily 0 4 5 * familyBracket atomFamily 1 3 4 * familyBracket atomFamily 2 3 5,
    familyBracket atomFamily 0 1 3 * familyBracket atomFamily 0 2 5 * familyBracket atomFamily 1 4 5 * familyBracket atomFamily 2 3 4,
    familyBracket atomFamily 0 1 2 * familyBracket atomFamily 0 3 5 * familyBracket atomFamily 1 4 5 * familyBracket atomFamily 2 3 4,
    familyBracket atomFamily 0 1 2 * familyBracket atomFamily 0 3 5 * familyBracket atomFamily 1 3 4 * familyBracket atomFamily 2 4 5,
    familyBracket atomFamily 0 1 3 * familyBracket atomFamily 0 2 4 * familyBracket atomFamily 1 4 5 * familyBracket atomFamily 2 3 5,
    familyBracket atomFamily 0 1 2 * familyBracket atomFamily 0 3 4 * familyBracket atomFamily 1 4 5 * familyBracket atomFamily 2 3 5,
    familyBracket atomFamily 0 1 2 * familyBracket atomFamily 0 3 4 * familyBracket atomFamily 1 3 5 * familyBracket atomFamily 2 4 5]

/-- **THE OCTAHEDRAL PRODUCT LAW.**  Sweeping all `15 * 8 = 120` face incidences
produces every one of the twenty brackets exactly six times. -/
theorem prod_octahedralProducts_eq_bracketProduct_pow_six
    (atomFamily : Fin 6 → Fin 3 → ℝ) :
    (∏ index : Fin 15,
        octahedralOddProduct atomFamily index * octahedralEvenProduct atomFamily index)
      = (familyBracket atomFamily 0 1 2 * familyBracket atomFamily 0 1 3 * familyBracket atomFamily 0 1 4 * familyBracket atomFamily 0 1 5 * familyBracket atomFamily 0 2 3 * familyBracket atomFamily 0 2 4 * familyBracket atomFamily 0 2 5 * familyBracket atomFamily 0 3 4 * familyBracket atomFamily 0 3 5 * familyBracket atomFamily 0 4 5 * familyBracket atomFamily 1 2 3 * familyBracket atomFamily 1 2 4 * familyBracket atomFamily 1 2 5 * familyBracket atomFamily 1 3 4 * familyBracket atomFamily 1 3 5 * familyBracket atomFamily 1 4 5 * familyBracket atomFamily 2 3 4 * familyBracket atomFamily 2 3 5 * familyBracket atomFamily 2 4 5 * familyBracket atomFamily 3 4 5) ^ 6 := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, octahedralOddProduct,
    octahedralEvenProduct, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
  ring

/-- **THE ODD-COUNT LEMMA.**  Fifteen pairs of reals, each pair with equal squares
and with a strictly positive total product, cannot all be opposite: an odd number of
sign flips would make the product negative. -/
theorem exists_eq_of_odd_family_sq_eq (leftFamily rightFamily : Fin 15 → ℝ)
    (hsq : ∀ index, leftFamily index ^ 2 = rightFamily index ^ 2)
    (hpos : 0 < ∏ index, leftFamily index * rightFamily index) :
    ∃ index, leftFamily index = rightFamily index := by
  by_contra! hnone
  have hopposite : ∀ index, leftFamily index * rightFamily index
      = -(rightFamily index ^ 2) := by
    intro index
    have hfactor : (leftFamily index - rightFamily index)
        * (leftFamily index + rightFamily index) = 0 := by
      linear_combination hsq index
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · exact absurd (sub_eq_zero.mp hzero) (hnone index)
    · have hflip : leftFamily index = -rightFamily index := by linarith
      rw [hflip]; ring
  have hcollapse : (∏ index : Fin 15, leftFamily index * rightFamily index)
      = -∏ index : Fin 15, rightFamily index ^ 2 := by
    rw [Finset.prod_congr rfl (fun index (_ : index ∈ Finset.univ) => hopposite index)]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    ring
  rw [hcollapse] at hpos
  have hnonneg : (0 : ℝ) ≤ ∏ index : Fin 15, rightFamily index ^ 2 :=
    Finset.prod_nonneg fun index _ => sq_nonneg _
  linarith

/-- **THE OCTAHEDRAL COINCIDENCE THEOREM.**  If a six-vector family is line-free and
satisfies all fifteen binomial identities in the squared brackets, then at least one
of the fifteen octahedral decompositions has its two four-bracket products EQUAL, not
merely equal up to sign. -/
theorem exists_octahedralCoincidence_of_forall_sq_eq
    (atomFamily : Fin 6 → Fin 3 → ℝ)
    (hlineFree : ∀ leftLabel midLabel rightLabel : Fin 6,
        leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        familyBracket atomFamily leftLabel midLabel rightLabel ≠ 0)
    (hbinomial : ∀ index : Fin 15,
        octahedralOddProduct atomFamily index ^ 2
          = octahedralEvenProduct atomFamily index ^ 2) :
    ∃ index : Fin 15,
      octahedralOddProduct atomFamily index = octahedralEvenProduct atomFamily index := by
  refine exists_eq_of_odd_family_sq_eq _ _ hbinomial ?_
  rw [prod_octahedralProducts_eq_bracketProduct_pow_six]
  have hbig : (familyBracket atomFamily 0 1 2 * familyBracket atomFamily 0 1 3 * familyBracket atomFamily 0 1 4 * familyBracket atomFamily 0 1 5 * familyBracket atomFamily 0 2 3 * familyBracket atomFamily 0 2 4 * familyBracket atomFamily 0 2 5 * familyBracket atomFamily 0 3 4 * familyBracket atomFamily 0 3 5 * familyBracket atomFamily 0 4 5 * familyBracket atomFamily 1 2 3 * familyBracket atomFamily 1 2 4 * familyBracket atomFamily 1 2 5 * familyBracket atomFamily 1 3 4 * familyBracket atomFamily 1 3 5 * familyBracket atomFamily 1 4 5 * familyBracket atomFamily 2 3 4 * familyBracket atomFamily 2 3 5 * familyBracket atomFamily 2 4 5 * familyBracket atomFamily 3 4 5) ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hlineFree 0 1 2 (by decide) (by decide) (by decide)) (hlineFree 0 1 3 (by decide) (by decide) (by decide))) (hlineFree 0 1 4 (by decide) (by decide) (by decide))) (hlineFree 0 1 5 (by decide) (by decide) (by decide))) (hlineFree 0 2 3 (by decide) (by decide) (by decide))) (hlineFree 0 2 4 (by decide) (by decide) (by decide))) (hlineFree 0 2 5 (by decide) (by decide) (by decide))) (hlineFree 0 3 4 (by decide) (by decide) (by decide))) (hlineFree 0 3 5 (by decide) (by decide) (by decide))) (hlineFree 0 4 5 (by decide) (by decide) (by decide))) (hlineFree 1 2 3 (by decide) (by decide) (by decide))) (hlineFree 1 2 4 (by decide) (by decide) (by decide))) (hlineFree 1 2 5 (by decide) (by decide) (by decide))) (hlineFree 1 3 4 (by decide) (by decide) (by decide))) (hlineFree 1 3 5 (by decide) (by decide) (by decide))) (hlineFree 1 4 5 (by decide) (by decide) (by decide))) (hlineFree 2 3 4 (by decide) (by decide) (by decide))) (hlineFree 2 3 5 (by decide) (by decide) (by decide))) (hlineFree 2 4 5 (by decide) (by decide) (by decide))) (hlineFree 3 4 5 (by decide) (by decide) (by decide))
  have hrewrite : (familyBracket atomFamily 0 1 2 * familyBracket atomFamily 0 1 3 * familyBracket atomFamily 0 1 4 * familyBracket atomFamily 0 1 5 * familyBracket atomFamily 0 2 3 * familyBracket atomFamily 0 2 4 * familyBracket atomFamily 0 2 5 * familyBracket atomFamily 0 3 4 * familyBracket atomFamily 0 3 5 * familyBracket atomFamily 0 4 5 * familyBracket atomFamily 1 2 3 * familyBracket atomFamily 1 2 4 * familyBracket atomFamily 1 2 5 * familyBracket atomFamily 1 3 4 * familyBracket atomFamily 1 3 5 * familyBracket atomFamily 1 4 5 * familyBracket atomFamily 2 3 4 * familyBracket atomFamily 2 3 5 * familyBracket atomFamily 2 4 5 * familyBracket atomFamily 3 4 5) ^ 6 = ((familyBracket atomFamily 0 1 2 * familyBracket atomFamily 0 1 3 * familyBracket atomFamily 0 1 4 * familyBracket atomFamily 0 1 5 * familyBracket atomFamily 0 2 3 * familyBracket atomFamily 0 2 4 * familyBracket atomFamily 0 2 5 * familyBracket atomFamily 0 3 4 * familyBracket atomFamily 0 3 5 * familyBracket atomFamily 0 4 5 * familyBracket atomFamily 1 2 3 * familyBracket atomFamily 1 2 4 * familyBracket atomFamily 1 2 5 * familyBracket atomFamily 1 3 4 * familyBracket atomFamily 1 3 5 * familyBracket atomFamily 1 4 5 * familyBracket atomFamily 2 3 4 * familyBracket atomFamily 2 3 5 * familyBracket atomFamily 2 4 5 * familyBracket atomFamily 3 4 5) ^ 3) ^ 2 := by ring
  rw [hrewrite]
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (pow_ne_zero 3 hbig)))

/-- **THE PUNCHLINE, IN THE FORM THE ENDPOINT NEEDS.**  For a line-free family, if
no octahedral decomposition has its two four-bracket products equal -- which,
by the measured identity `(veroneseGrid atomFamily).det = P - Q`, is exactly
off-conicity -- then at least one of the fifteen BINOMIALS IN THE SQUARED BRACKETS
fails.  Off-conicity is therefore not invisible to the bracket-square layer: it is
the failure of one of fifteen explicit monomial identities in the twenty
`Gtz.shadowDeterminant` coordinates, up to their positive weight factors. -/
theorem exists_octahedralBinomial_ne_of_forall_ne
    (atomFamily : Fin 6 → Fin 3 → ℝ)
    (hlineFree : ∀ leftLabel midLabel rightLabel : Fin 6,
        leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        familyBracket atomFamily leftLabel midLabel rightLabel ≠ 0)
    (hnoCoincidence : ∀ index : Fin 15,
        octahedralOddProduct atomFamily index ≠ octahedralEvenProduct atomFamily index) :
    ∃ index : Fin 15,
      octahedralOddProduct atomFamily index ^ 2
        ≠ octahedralEvenProduct atomFamily index ^ 2 := by
  by_contra! hall
  obtain ⟨index, hindex⟩ :=
    exists_octahedralCoincidence_of_forall_sq_eq atomFamily hlineFree hall
  exact hnoCoincidence index hindex


end Gtz
