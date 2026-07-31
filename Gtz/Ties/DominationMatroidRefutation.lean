/-
# The family of dominating triples is NOT a matroid

At rank three the atoms carry a rank-three DIRECTION matroid, and the shipped
`Gtz.not_dominates_of_commonOrthogonal` already puts every dominating triple inside
its basis family.  The question this file settles is whether the dominating triples
are themselves the bases of a matroid — if they were, greedy and exchange selection
would apply and the selection problem would be combinatorial rather than metric.

They are not.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `twoFrameDesign` — a genuine all-heavy `(7,3)` design, entirely rational, built
  from two orthogonal frames in general position: an axis frame of length `2` (its
  first atom duplicated, to reach seven labels) and a second frame of length `3/2`
  obtained by the rational rotation `(1/3)*!![2,-1,2; 2,2,-1; -1,2,2]`.  Its
  dominating triples are exactly the two frames, and they are DISJOINT.
* `HasDominationBasisExchange` — the matroid basis-exchange axiom read on the
  domination mask.
* `not_hasDominationBasisExchange_twoFrameDesign` and
  `exists_allHeavy_sevenThree_dominationMask_not_matroid` — THE REFUTATION.  Both
  frames dominate, they are disjoint, and no single swap between them dominates:
  removing any rotated atom and inserting any axis atom destroys domination.  A
  non-empty family of equicardinal sets is the basis family of a matroid exactly
  when it satisfies the exchange axiom, so the dominating triples of an all-heavy
  rank-three configuration on seven points are not the bases of a matroid.

Consequence for the campaign: no greedy, exchange, or basis-augmentation argument
can produce a dominating triple, because the object those arguments run on does not
exist.  Note what does the work — not the mask being SMALL (the tree's
`Gtz.heavyPivotDesign` already has a one-element mask at `(6,3)`, and a one-element
mask IS a matroid: three coloops and three loops) but the mask being DISCONNECTED:
two dominating triples that no single swap joins.

## NOT proved here

Nothing about the mask at other cells, and nothing about weaker exchange axioms.
The tree's own exchange vocabulary (`Gtz.DoesExchangeImprove`,
`Gtz.IsExchangeStuck`) is about SCORE IMPROVEMENT and is a different notion
entirely; this file does not touch it.

Provenance: scratch report 20 (`matroid`).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.Reductions
import Gtz.Reduction.ExchangeInvariant
import Gtz.Ties.SelectionObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The two-frame design -/

/-- Seven atoms: the axis frame `2*e_i` at labels `0,1,2` (repeated at label `6`), and
the rotated frame `(3/2)*f_j` at labels `3,4,5`. -/
noncomputable def twoFrameAtom : Fin 7 → (Fin 3 → ℝ) :=
  ![![2, 0, 0], ![0, 2, 0], ![0, 0, 2],
    ![1, 1, -(1/2)], ![-(1/2), 1, 1], ![1, -(1/2), 1],
    ![2, 0, 0]]

/-- The weights: `1/14` on the two parallel copies, `1/7` on the other axis atoms,
`4/21` on the rotated frame.  Total mass one, and Parseval is exact. -/
noncomputable def twoFrameWeight : Fin 7 → ℝ :=
  ![1/14, 1/7, 1/7, 4/21, 4/21, 4/21, 1/14]

@[simp] theorem twoFrameAtom_zero : twoFrameAtom 0 = ![2, 0, 0] := rfl
@[simp] theorem twoFrameAtom_one : twoFrameAtom 1 = ![0, 2, 0] := rfl
@[simp] theorem twoFrameAtom_two : twoFrameAtom 2 = ![0, 0, 2] := rfl
@[simp] theorem twoFrameAtom_three : twoFrameAtom 3 = ![1, 1, -(1/2)] := rfl
@[simp] theorem twoFrameAtom_four : twoFrameAtom 4 = ![-(1/2), 1, 1] := rfl
@[simp] theorem twoFrameAtom_five : twoFrameAtom 5 = ![1, -(1/2), 1] := rfl
@[simp] theorem twoFrameAtom_six : twoFrameAtom 6 = ![2, 0, 0] := rfl

@[simp] theorem twoFrameWeight_zero : twoFrameWeight 0 = 1/14 := rfl
@[simp] theorem twoFrameWeight_one : twoFrameWeight 1 = 1/7 := rfl
@[simp] theorem twoFrameWeight_two : twoFrameWeight 2 = 1/7 := rfl
@[simp] theorem twoFrameWeight_three : twoFrameWeight 3 = 4/21 := rfl
@[simp] theorem twoFrameWeight_four : twoFrameWeight 4 = 4/21 := rfl
@[simp] theorem twoFrameWeight_five : twoFrameWeight 5 = 4/21 := rfl
@[simp] theorem twoFrameWeight_six : twoFrameWeight 6 = 1/14 := rfl

/-- **The witness design.**  Every entry is rational; Parseval holds on the nose because
each frame resolves the identity: `(1/7)*4*I + (4/21)*(9/4)*I = (4/7 + 3/7)*I`. -/
noncomputable def twoFrameDesign : WeightedDesign 7 3 where
  atom := twoFrameAtom
  weight := twoFrameWeight
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;> norm_num [twoFrameWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_seven]
    simp only [twoFrameWeight_zero, twoFrameWeight_one, twoFrameWeight_two,
      twoFrameWeight_three, twoFrameWeight_four, twoFrameWeight_five, twoFrameWeight_six]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul, Fin.sum_univ_seven, twoFrameAtom_zero, twoFrameAtom_one,
      twoFrameAtom_two, twoFrameAtom_three, twoFrameAtom_four, twoFrameAtom_five,
      twoFrameAtom_six, twoFrameWeight_zero, twoFrameWeight_one, twoFrameWeight_two,
      twoFrameWeight_three, twoFrameWeight_four, twoFrameWeight_five, twoFrameWeight_six]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

@[simp] theorem twoFrameDesign_atom : twoFrameDesign.atom = twoFrameAtom := rfl
@[simp] theorem twoFrameDesign_weight : twoFrameDesign.weight = twoFrameWeight := rfl

/-- **The design is all-heavy**: the axis atoms have leverage `4`, the rotated ones `9/4`.
So the witness lives inside the campaign's sharpened frontier `Gtz.GtzWeightedHeavy`. -/
theorem twoFrameDesign_allHeavy : AllHeavy twoFrameDesign := by
  intro atomIndex
  have hmem : atomIndex ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by
    revert atomIndex
    decide
  fin_cases hmem <;>
    norm_num [leverageOf, Fin.sum_univ_three, twoFrameDesign_atom, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ## The two frames dominate -/

/-- The axis frame dominates with margin `3`: its atom sum is `4*I`. -/
theorem twoFrameDesign_dominates_axisFrame :
    Dominates twoFrameDesign {0, 1, 2} := by
  rw [dominates_iff_leastEigenvalueAtLeast_one, hasLeastEigenvalueAtLeast_iff]
  intro direction
  rw [sum_over_triple _ (by decide) (by decide) (by decide)]
  simp only [twoFrameDesign_atom, twoFrameAtom_zero, twoFrameAtom_one, twoFrameAtom_two,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith [sq_nonneg (direction 0), sq_nonneg (direction 1), sq_nonneg (direction 2)]

/-- The rotated frame dominates with margin `5/4`: its atom sum is `(9/4)*I`. -/
theorem twoFrameDesign_dominates_rotatedFrame :
    Dominates twoFrameDesign {3, 4, 5} := by
  rw [dominates_iff_leastEigenvalueAtLeast_one, hasLeastEigenvalueAtLeast_iff]
  intro direction
  rw [sum_over_triple _ (by decide) (by decide) (by decide)]
  simp only [twoFrameDesign_atom, twoFrameAtom_three, twoFrameAtom_four, twoFrameAtom_five,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith [sq_nonneg (direction 0), sq_nonneg (direction 1), sq_nonneg (direction 2)]

/-! ## Every single-element exchange out of the rotated frame fails

Replacing one rotated atom by one axis atom leaves a triple whose Gram has determinant
`-25/16` after subtracting the identity; each of the three exhibits a gap of `-3/4`. -/

/-- `{0,4,5}` fails: the direction `(-1,-2,1)` has gap `21/4 - 6 = -3/4`. -/
theorem twoFrameDesign_not_dominates_zeroFourFive :
    ¬ Dominates twoFrameDesign {0, 4, 5} := by
  refine not_dominates_triple_of_negativeDirection twoFrameDesign 0 4 5
    (by decide) (by decide) (by decide) ![-1, -2, 1] ?_
  simp only [twoFrameDesign_atom, twoFrameAtom_zero, twoFrameAtom_four, twoFrameAtom_five,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- `{1,4,5}` fails: the direction `(-2,-1,1)` has gap `-3/4`. -/
theorem twoFrameDesign_not_dominates_oneFourFive :
    ¬ Dominates twoFrameDesign {1, 4, 5} := by
  refine not_dominates_triple_of_negativeDirection twoFrameDesign 1 4 5
    (by decide) (by decide) (by decide) ![-2, -1, 1] ?_
  simp only [twoFrameDesign_atom, twoFrameAtom_one, twoFrameAtom_four, twoFrameAtom_five,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- `{2,4,5}` fails: the direction `(1,2,-1)` has gap `-3/4`. -/
theorem twoFrameDesign_not_dominates_twoFourFive :
    ¬ Dominates twoFrameDesign {2, 4, 5} := by
  refine not_dominates_triple_of_negativeDirection twoFrameDesign 2 4 5
    (by decide) (by decide) (by decide) ![1, 2, -1] ?_
  simp only [twoFrameDesign_atom, twoFrameAtom_two, twoFrameAtom_four, twoFrameAtom_five,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-! ## The matroid basis-exchange axiom, and its refutation -/

/-- **The basis-exchange axiom read on the domination mask.**  This is exactly the
matroid basis axiom for the family `{C : C.card = rank and Dominates D C}`: if it held,
that family would be the basis family of a matroid on the atom labels (all its members
already have the same cardinality), and dominating triples could be reached from one
another one swap at a time. -/
def HasDominationBasisExchange {m k : ℕ} (D : WeightedDesign m k) : Prop :=
  ∀ firstBasis secondBasis : Finset (Fin m),
    firstBasis.card = k → secondBasis.card = k →
      Dominates D firstBasis → Dominates D secondBasis →
        ∀ leaving ∈ firstBasis \ secondBasis,
          ∃ entering ∈ secondBasis \ firstBasis,
            Dominates D (insert entering (firstBasis.erase leaving))

/-- **THE DOMINATION MASK IS NOT A MATROID.**  At the all-heavy `(7,3)` two-frame design
the two frames both dominate, they are disjoint, and no single swap between them
dominates: removing any rotated atom and inserting any axis atom destroys domination.
So the family of dominating triples violates the basis-exchange axiom, and therefore is
not the basis family of any matroid — even though it sits inside the basis family of the
rank-three direction matroid. -/
theorem not_hasDominationBasisExchange_twoFrameDesign :
    ¬ HasDominationBasisExchange twoFrameDesign := by
  intro hexchange
  obtain ⟨entering, hentering, hdominates⟩ :=
    hexchange {3, 4, 5} {0, 1, 2} (by decide) (by decide)
      twoFrameDesign_dominates_rotatedFrame twoFrameDesign_dominates_axisFrame 3 (by decide)
  have hmask : ({0, 1, 2} : Finset (Fin 7)) \ {3, 4, 5} = {0, 1, 2} := by decide
  rw [hmask] at hentering
  fin_cases hentering
  · rw [show insert (0 : Fin 7) (({3, 4, 5} : Finset (Fin 7)).erase 3)
        = ({0, 4, 5} : Finset (Fin 7)) from by decide] at hdominates
    exact twoFrameDesign_not_dominates_zeroFourFive hdominates
  · rw [show insert (1 : Fin 7) (({3, 4, 5} : Finset (Fin 7)).erase 3)
        = ({1, 4, 5} : Finset (Fin 7)) from by decide] at hdominates
    exact twoFrameDesign_not_dominates_oneFourFive hdominates
  · rw [show insert (2 : Fin 7) (({3, 4, 5} : Finset (Fin 7)).erase 3)
        = ({2, 4, 5} : Finset (Fin 7)) from by decide] at hdominates
    exact twoFrameDesign_not_dominates_twoFourFive hdominates

/-- The headline, packaged.  There is an all-heavy `(7,3)` design carrying two DISJOINT
dominating triples whose domination mask violates basis exchange. -/
theorem exists_allHeavy_sevenThree_dominationMask_not_matroid :
    ∃ D : WeightedDesign 7 3,
      AllHeavy D ∧
      Dominates D {0, 1, 2} ∧ Dominates D {3, 4, 5} ∧
      Disjoint ({0, 1, 2} : Finset (Fin 7)) {3, 4, 5} ∧
      ¬ HasDominationBasisExchange D :=
  ⟨twoFrameDesign, twoFrameDesign_allHeavy,
    twoFrameDesign_dominates_axisFrame, twoFrameDesign_dominates_rotatedFrame,
    by decide, not_hasDominationBasisExchange_twoFrameDesign⟩

end Gtz
