import Mathlib
import Gtz.Design.PrimitiveTightClassification
import Gtz.Reduction.ExchangeInvariant
import Gtz.LinAlg.ProjectionForm

/-!
PROVENANCE.  Harvested by the sweep from the recon-chirotope reconnaissance rung,
which derived the Grassmann-Pluecker realness separator, measured its defect exactly
at both shipped complex counterexamples and prototyped every statement below.  The
sweep replaced the draft's `import Gtz` -- a build cycle for any module the umbrella
imports, invisible to `lake env lean` -- with the modules actually consumed, then
re-compiled, re-audited and wired it; the mathematics is recon-chirotope's.

# The Grassmann-Pluecker realness layer, on the tree's own bracket

The tree carries the bracket (`Gtz.tripleBracket`, `Gtz.atomBracket`,
Gtz/Design/PrimitiveTightClassification.lean:256/290) and the Cauchy-Binet
reading of a maximal principal minor
(`Gtz.shadowDeterminant_eq_weightProduct_mul_detSq`, ExchangeInvariant.lean:1129):
the shadow determinant of a `k`-selection is a positive weight product times the
SQUARE of the bracket.  Over `ℂ` the identical expansion holds with `|det|²` in
place of `det ^ 2` -- which is precisely why every mechanism built on it so far
is field-blind (gtz-g3 think-basis, exhausted invariant family (iv)).

What is NOT field-blind is the RELATION BETWEEN brackets.  Five vectors in three
dimensions obey the three-term Grassmann-Pluecker relation

    [s a b][s c d] - [s a c][s b d] + [s a d][s b c] = 0,

and over `ℝ` those three products are REAL numbers in alternating balance.  Three
reals in that position have degenerate Heron determinant: one magnitude is the
sum of the other two.  Squaring erases every sign, and what survives is a
polynomial identity in the SQUARED brackets alone -- equivalently, since the
weight factors are common to all three products and the identity is homogeneous
of degree two, in the tree's own shadow determinants:

    (P₁ + P₂ + P₃)²  =  4 (P₁P₂ + P₂P₃ + P₃P₁),
    P₁ = shadow{s,a,b}·shadow{s,c,d},
    P₂ = shadow{s,a,c}·shadow{s,b,d},
    P₃ = shadow{s,a,d}·shadow{s,b,c}.

Over `ℂ` the three products are COMPLEX numbers in alternating balance, so their
moduli obey only the triangle INEQUALITY and the identity degrades to
`(P₁+P₂+P₃)² ≤ 4(P₁P₂+P₂P₃+P₃P₁)`, strict off the collinear locus.  Measured
exactly (sympy, no floats) at the two shipped complex counterexamples: the defect
`4(P₁P₂+P₂P₃+P₃P₁) − (P₁+P₂+P₃)²` is `4096/27` at `Gtz.sicDesign` and
`4096·10¹²/3¹⁹` at `Gtz.paddedDesign`, and is `0` at all nine real reference
designs (`splitTetraSym`, `splitTetraAsym`, `splitSevenDesign`, `diamondDesign`,
`diamondSixSpine`, `diamondSixRim`, `diamondSevenDesign`, `icosaDesign`,
`tetraDesign`), across 30 quadruples at size six and 105 at size seven.

This is the first realness quantum of the campaign that is simultaneously
(i) a polynomial identity in Gram-level data, (ii) a theorem over `ℝ`, and
(iii) FALSE over `ℂ` at the very witness the field gap is proved from.  Nothing
here decides GTZ; it supplies the shape boundary condition B1 demands.

Generality: the algebraic half is rank-free; the bracket relation is stated at
rank three and ARBITRARY SIZE, so it covers the whole rank-three tower
`T₃ = GtzWeighted 6 3`, `(7,3)`, and every `(m,3)`.  The general-`k` form needs
the Pfaffian vanishing of the alternating form `ω(u,v) = det[S,u,v]`, which is
not attempted here.
-/

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## The rank-free algebraic half -/

/-- **Three reals in alternating balance have degenerate Heron determinant.**
If `x - y + z = 0` then the squares satisfy the equality case of the triangle
condition.  This is the entire arithmetic content of realness in the bracket
layer: over `ℂ` the same hypothesis yields only `≤`. -/
theorem sumSquares_sq_eq_four_mul_pairSquareProducts_of_alternatingSum_eq_zero
    (first second third : ℝ) (halternating : first - second + third = 0) :
    (first ^ 2 + second ^ 2 + third ^ 2) ^ 2
      = 4 * (first ^ 2 * second ^ 2 + second ^ 2 * third ^ 2 + third ^ 2 * first ^ 2) := by
  have hsecond : second = first + third := by linarith
  subst hsecond
  ring

/-! ## The three-term relation on the tree's bracket -/

/-- **The three-term Grassmann-Pluecker relation.**  Five arbitrary vectors in
three dimensions; repetitions allowed, in which case every term vanishes.
Proved by expanding all six brackets through `Gtz.tripleBracket_eq` and `ring` --
no exterior algebra and no oriented-matroid theory is invoked. -/
theorem threeTermBracketRelation (base first second third fourth : Fin 3 → ℝ) :
    tripleBracket base first second * tripleBracket base third fourth
      - tripleBracket base first third * tripleBracket base second fourth
      + tripleBracket base first fourth * tripleBracket base second third = 0 := by
  simp only [tripleBracket_eq]
  ring

/-- The design-side reading: the same relation on `Gtz.atomBracket`, at rank
three and any size. -/
theorem threeTermAtomBracketRelation (D : WeightedDesign m 3)
    (base first second third fourth : Fin m) :
    atomBracket D base first second * atomBracket D base third fourth
      - atomBracket D base first third * atomBracket D base second fourth
      + atomBracket D base first fourth * atomBracket D base second third = 0 := by
  simpa only [atomBracket] using
    threeTermBracketRelation (D.atom base) (D.atom first) (D.atom second)
      (D.atom third) (D.atom fourth)

/-! ## The realness identity in squared brackets -/

/-- **The Heron identity on squared brackets.**  For every real design of rank
three, every base atom and every four further atoms, the three complementary
products of squared brackets satisfy the degenerate-triangle equality.  Every
sign has been erased: the statement is a polynomial identity in the squared
brackets, which are the weight-free principal Gram minors. -/
theorem squaredBracketProducts_heronDegenerate (D : WeightedDesign m 3)
    (base first second third fourth : Fin m) :
    (atomBracket D base first second ^ 2 * atomBracket D base third fourth ^ 2
      + atomBracket D base first third ^ 2 * atomBracket D base second fourth ^ 2
      + atomBracket D base first fourth ^ 2 * atomBracket D base second third ^ 2) ^ 2
      = 4 * ((atomBracket D base first second ^ 2 * atomBracket D base third fourth ^ 2)
            * (atomBracket D base first third ^ 2 * atomBracket D base second fourth ^ 2)
          + (atomBracket D base first third ^ 2 * atomBracket D base second fourth ^ 2)
            * (atomBracket D base first fourth ^ 2 * atomBracket D base second third ^ 2)
          + (atomBracket D base first fourth ^ 2 * atomBracket D base second third ^ 2)
            * (atomBracket D base first second ^ 2 * atomBracket D base third fourth ^ 2)) := by
  have hidentity :=
    sumSquares_sq_eq_four_mul_pairSquareProducts_of_alternatingSum_eq_zero
      (atomBracket D base first second * atomBracket D base third fourth)
      (atomBracket D base first third * atomBracket D base second fourth)
      (atomBracket D base first fourth * atomBracket D base second third)
      (threeTermAtomBracketRelation D base first second third fourth)
  linear_combination hidentity

/-! ## The same identity on shipped shadow determinants -/

/-- The bracket of three atom labels is the determinant of the selected atom
rows: the bridge between `Gtz.atomBracket` and `Gtz.selectedAtomRows`.

DISCLOSURE.  This is a DEFINITIONAL UNFOLDING, not new content: a statement-level
defeq scan reports it equal to the auto-generated equation lemma `Gtz.atomBracket.eq_1`.
It is kept only as the named API entry point the statements below rewrite through, and
a reader should treat it as carrying no information beyond the definition of
`Gtz.atomBracket` itself. -/
theorem det_selectedAtomRows_three_eq_atomBracket (D : WeightedDesign m 3)
    (first second third : Fin m) :
    (selectedAtomRows D ![first, second, third]).det = atomBracket D first second third := by
  rw [atomBracket, tripleBracket_eq, Matrix.det_fin_three]
  simp only [selectedAtomRows, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- **THE REALNESS IDENTITY ON SHADOW DETERMINANTS.**  The three products carry
the identical positive weight factor `t_base² t_first t_second t_third t_fourth`,
and the Heron equality is homogeneous of degree two, so the weights cancel and
the statement transports verbatim onto the tree's own `Gtz.shadowDeterminant`.

This is the form a realness consumer would cite: it constrains exactly the
twenty numbers `shadowDeterminant D C` that the twenty domination tests read,
it holds at every real design, and it fails at `Gtz.paddedDesign`. -/
theorem shadowDeterminantProducts_heronDegenerate (D : WeightedDesign m 3)
    (base first second third fourth : Fin m)
    {selectedOneLeft selectedOneRight selectedTwoLeft selectedTwoRight
      selectedThreeLeft selectedThreeRight : Finset (Fin m)}
    (hOneLeftInj : Function.Injective ![base, first, second])
    (hOneRightInj : Function.Injective ![base, third, fourth])
    (hTwoLeftInj : Function.Injective ![base, first, third])
    (hTwoRightInj : Function.Injective ![base, second, fourth])
    (hThreeLeftInj : Function.Injective ![base, first, fourth])
    (hThreeRightInj : Function.Injective ![base, second, third])
    (hOneLeft : Finset.image ![base, first, second] Finset.univ = selectedOneLeft)
    (hOneRight : Finset.image ![base, third, fourth] Finset.univ = selectedOneRight)
    (hTwoLeft : Finset.image ![base, first, third] Finset.univ = selectedTwoLeft)
    (hTwoRight : Finset.image ![base, second, fourth] Finset.univ = selectedTwoRight)
    (hThreeLeft : Finset.image ![base, first, fourth] Finset.univ = selectedThreeLeft)
    (hThreeRight : Finset.image ![base, second, third] Finset.univ = selectedThreeRight) :
    (shadowDeterminant D selectedOneLeft * shadowDeterminant D selectedOneRight
      + shadowDeterminant D selectedTwoLeft * shadowDeterminant D selectedTwoRight
      + shadowDeterminant D selectedThreeLeft * shadowDeterminant D selectedThreeRight) ^ 2
      = 4 * ((shadowDeterminant D selectedOneLeft * shadowDeterminant D selectedOneRight)
            * (shadowDeterminant D selectedTwoLeft * shadowDeterminant D selectedTwoRight)
          + (shadowDeterminant D selectedTwoLeft * shadowDeterminant D selectedTwoRight)
            * (shadowDeterminant D selectedThreeLeft * shadowDeterminant D selectedThreeRight)
          + (shadowDeterminant D selectedThreeLeft * shadowDeterminant D selectedThreeRight)
            * (shadowDeterminant D selectedOneLeft * shadowDeterminant D selectedOneRight)) := by
  rw [shadowDeterminant_eq_weightProduct_mul_detSq D _ hOneLeftInj hOneLeft,
    shadowDeterminant_eq_weightProduct_mul_detSq D _ hOneRightInj hOneRight,
    shadowDeterminant_eq_weightProduct_mul_detSq D _ hTwoLeftInj hTwoLeft,
    shadowDeterminant_eq_weightProduct_mul_detSq D _ hTwoRightInj hTwoRight,
    shadowDeterminant_eq_weightProduct_mul_detSq D _ hThreeLeftInj hThreeLeft,
    shadowDeterminant_eq_weightProduct_mul_detSq D _ hThreeRightInj hThreeRight,
    det_selectedAtomRows_three_eq_atomBracket, det_selectedAtomRows_three_eq_atomBracket,
    det_selectedAtomRows_three_eq_atomBracket, det_selectedAtomRows_three_eq_atomBracket,
    det_selectedAtomRows_three_eq_atomBracket, det_selectedAtomRows_three_eq_atomBracket]
  have hheron := squaredBracketProducts_heronDegenerate D base first second third fourth
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination
    (D.weight base ^ 2 * D.weight first * D.weight second * D.weight third
      * D.weight fourth) ^ 2 * hheron

end Gtz
