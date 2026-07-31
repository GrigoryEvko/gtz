/-
# The diamond primitive's five leverages, and the all-heavy hinge

`Gtz.diamondDesign` is the graphic design of `M(K4 - e)` — the diamond graph on four
vertices with five edges, one spine `ab` and four rim edges.  It is a `(5,3)` exact tie
(`Gtz.diamondDesign_isTie`) with pairwise non-parallel atoms
(`Gtz.not_hasParallelPair_diamondDesign`), and it is the witness that refutes the hinge
at `(5,3)` (`Gtz.not_hingeHoldsAtSize_five_three`).

This file computes its five leverages exactly, by solving the reduced Laplacian against
each edge vector and reading off the effective resistance through
`Gtz.leverageOf_graphicAtom_of_solves`.  The spine carries leverage `2`; each of the four
rim edges carries `13/4`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `diamondFullLaplacian_eq` — the reduced Laplacian in closed `3 x 3` form.
* `diamondFullLaplacian_solves_of_check` and its five per-edge instances — the unit-current
  potentials, one per edge.
* `diamondDesign_leverage_spine` and the four `diamondDesign_leverage_rim*` — the exact
  values `2` and `13/4`.
* `diamondDesign_allHeavy` — the diamond tie is ALL-HEAVY.  The tree previously carried
  only the NON-STRICT `Gtz.diamondDesign_forall_leverage_one_le`, derived from the generic
  "ties are heavy" floor, which by construction cannot separate leverage `1` from leverage
  greater than `1`.  Everything downstream that needs strictness needs this declaration.
* `atom_ne_zero_of_allHeavy` — the one-line generic consequence, stated once at the level
  of `Gtz.AllHeavy` rather than as a diamond-only specialisation.
* `not_hingeHoldsAmongAllHeavy_five_three` — narrowing the hinge to all-heavy designs does
  NOT restore it at `(5,3)`.

## NOT proved here

Nothing about `(6,3)` or `(7,3)`.  The leverages are a property of the `(5,3)` primitive;
what the split designs built on it inherit is recorded in
`Gtz/Reduction/LineCountReduction.lean`, not here.

Provenance: the July 2026 scratch corpus, report 16 (`tieclass`).  The numeric values also
appear as prose in the `Gtz/Ties/DiamondTie.lean` header; this is the first kernel-checked
statement of them.
-/
import Mathlib
import Gtz.Design.DiamondPrimitive
import Gtz.Reduction.SplitTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## The reduced Laplacian, and the five unit-current solves -/

/-- The diamond's reduced Laplacian, in closed form.  Rows and columns are indexed by the
three non-grounded vertices; the spine endpoints carry degree `8` after the conductance
scaling and the shared apex carries degree `6`. -/
theorem diamondFullLaplacian_eq :
    diamondData.fullLaplacian = !![(8 : ℝ), -2, -3; -2, 8, -3; -3, -3, 6] := by
  ext rowIndex colIndex
  rw [GraphDesignData.fullLaplacian, laplacianOn]
  simp only [Matrix.sum_apply, Fin.sum_univ_five, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul, diamondEdgeVector_eq]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [diamondData, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]

/-- **The unit-current solve, discharged uniformly in the edge.**  Rewriting both sides
into closed form reduces "this potential drives a unit current across `edge`" to a
numeric matrix-vector identity that `norm_num` settles. -/
theorem diamondFullLaplacian_solves_of_check (edge : Fin 5) (potential : Fin 3 → ℝ)
    (hcheck : !![(8 : ℝ), -2, -3; -2, 8, -3; -3, -3, 6] *ᵥ potential
      = ![![1, -1, 0], ![1, 0, -1], ![1, 0, 0], ![0, 1, -1], ![0, 1, 0]] edge) :
    diamondData.fullLaplacian *ᵥ potential = diamondData.graph.edgeVector edge := by
  rw [diamondFullLaplacian_eq, diamondEdgeVector_eq]
  exact hcheck

theorem diamondFullLaplacian_solves_spine :
    diamondData.fullLaplacian *ᵥ ![(1 : ℝ) / 10, -1 / 10, 0]
      = diamondData.graph.edgeVector 0 := by
  refine diamondFullLaplacian_solves_of_check 0 _ ?_
  funext coord
  fin_cases coord <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons]

theorem diamondFullLaplacian_solves_rimOne :
    diamondData.fullLaplacian *ᵥ ![(1 : ℝ) / 20, -1 / 20, -1 / 6]
      = diamondData.graph.edgeVector 1 := by
  refine diamondFullLaplacian_solves_of_check 1 _ ?_
  funext coord
  fin_cases coord <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons]

theorem diamondFullLaplacian_solves_rimTwo :
    diamondData.fullLaplacian *ᵥ ![(13 : ℝ) / 60, 7 / 60, 1 / 6]
      = diamondData.graph.edgeVector 2 := by
  refine diamondFullLaplacian_solves_of_check 2 _ ?_
  funext coord
  fin_cases coord <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons]

theorem diamondFullLaplacian_solves_rimThree :
    diamondData.fullLaplacian *ᵥ ![(-1 : ℝ) / 20, 1 / 20, -1 / 6]
      = diamondData.graph.edgeVector 3 := by
  refine diamondFullLaplacian_solves_of_check 3 _ ?_
  funext coord
  fin_cases coord <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons]

theorem diamondFullLaplacian_solves_rimFour :
    diamondData.fullLaplacian *ᵥ ![(7 : ℝ) / 60, 13 / 60, 1 / 6]
      = diamondData.graph.edgeVector 4 := by
  refine diamondFullLaplacian_solves_of_check 4 _ ?_
  funext coord
  fin_cases coord <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons]

/-! ## The five leverages -/

/-- **The spine carries leverage `2`.** -/
theorem diamondDesign_leverage_spine : leverageOf (diamondDesign.atom 0) = 2 := by
  rw [show diamondDesign = graphicDesign diamondData from rfl,
    leverageOf_graphicAtom_of_solves diamondData 0 _ diamondFullLaplacian_solves_spine,
    diamondEdgeVector_eq]
  norm_num [diamondData, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons]

/-- **Each rim edge carries leverage `13/4`.** -/
theorem diamondDesign_leverage_rimOne : leverageOf (diamondDesign.atom 1) = 13 / 4 := by
  rw [show diamondDesign = graphicDesign diamondData from rfl,
    leverageOf_graphicAtom_of_solves diamondData 1 _ diamondFullLaplacian_solves_rimOne,
    diamondEdgeVector_eq]
  norm_num [diamondData, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons]

theorem diamondDesign_leverage_rimTwo : leverageOf (diamondDesign.atom 2) = 13 / 4 := by
  rw [show diamondDesign = graphicDesign diamondData from rfl,
    leverageOf_graphicAtom_of_solves diamondData 2 _ diamondFullLaplacian_solves_rimTwo,
    diamondEdgeVector_eq]
  norm_num [diamondData, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons]

theorem diamondDesign_leverage_rimThree : leverageOf (diamondDesign.atom 3) = 13 / 4 := by
  rw [show diamondDesign = graphicDesign diamondData from rfl,
    leverageOf_graphicAtom_of_solves diamondData 3 _ diamondFullLaplacian_solves_rimThree,
    diamondEdgeVector_eq]
  norm_num [diamondData, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons]

theorem diamondDesign_leverage_rimFour : leverageOf (diamondDesign.atom 4) = 13 / 4 := by
  rw [show diamondDesign = graphicDesign diamondData from rfl,
    leverageOf_graphicAtom_of_solves diamondData 4 _ diamondFullLaplacian_solves_rimFour,
    diamondEdgeVector_eq]
  norm_num [diamondData, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons]

/-! ## All-heaviness, and what it forces -/

/-- **THE DIAMOND TIE IS ALL-HEAVY**: its leverages are `2, 13/4, 13/4, 13/4, 13/4`, every
one of them strictly above `1`.

The tree's `Gtz.diamondDesign_forall_leverage_one_le` gives only the non-strict bound,
because it is an instance of the generic "an exact tie has no light atom" floor, which
cannot distinguish leverage exactly `1` from leverage above `1`.  The strict statement
needs the leverages themselves, hence this file. -/
theorem diamondDesign_allHeavy : AllHeavy diamondDesign := by
  intro edge
  fin_cases edge
  · show (1 : ℝ) < leverageOf (diamondDesign.atom 0)
    rw [diamondDesign_leverage_spine]; norm_num
  · show (1 : ℝ) < leverageOf (diamondDesign.atom 1)
    rw [diamondDesign_leverage_rimOne]; norm_num
  · show (1 : ℝ) < leverageOf (diamondDesign.atom 2)
    rw [diamondDesign_leverage_rimTwo]; norm_num
  · show (1 : ℝ) < leverageOf (diamondDesign.atom 3)
    rw [diamondDesign_leverage_rimThree]; norm_num
  · show (1 : ℝ) < leverageOf (diamondDesign.atom 4)
    rw [diamondDesign_leverage_rimFour]; norm_num

/-- An all-heavy design has no zero atom: the zero vector has leverage `0`. -/
theorem atom_ne_zero_of_allHeavy {size rank : ℕ} {D : WeightedDesign size rank}
    (hheavy : AllHeavy D) (label : Fin size) : D.atom label ≠ 0 := by
  intro hzero
  have hstrict := hheavy label
  rw [hzero] at hstrict
  simp only [leverageOf, Pi.zero_apply] at hstrict
  norm_num at hstrict

/-! ## The hinge, narrowed to the all-heavy branch -/

/-- The hinge restricted to the campaign's strict-heavy branch: at this size every
ALL-HEAVY exact tie carries a parallel pair.  This is the narrowing that the open entries
of `Gtz.StratumIsTieFreeAmongAllHeavy` would be able to exploit, so it is worth knowing
where it stands. -/
def HingeHoldsAmongAllHeavy (size rank : ℕ) : Prop :=
  ∀ D : WeightedDesign size rank, AllHeavy D → IsTie D → HasParallelPair D

/-- **NARROWING THE HINGE TO ALL-HEAVY DESIGNS DOES NOT RESTORE IT AT `(5,3)`.**
`Gtz.not_hingeHoldsAtSize_five_three` refutes the plain hinge with the diamond; the
diamond is moreover all-heavy, so the same witness refutes the narrowed hinge.  Before
`diamondDesign_allHeavy` this calibration could not be stated. -/
theorem not_hingeHoldsAmongAllHeavy_five_three : ¬ HingeHoldsAmongAllHeavy 5 3 :=
  fun hhinge => not_hasParallelPair_diamondDesign
    (hhinge diamondDesign diamondDesign_allHeavy diamondDesign_isTie)

end Gtz
