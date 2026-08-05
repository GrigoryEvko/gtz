/-
# The two layer-sum no-goes, with the tie hypothesis deleted

`Gtz.not_forall_dominates_of_isTie_uniform_sixThree` and its split-tetrahedron sibling
both carry `IsTie design`.  Neither needs it.

The tie was used for one step and one step only: at a tie a weakly dominating triple has
a SINGULAR gap, so its gap determinant is exactly zero, so the twenty gap determinants
sum to zero, contradicting the layer anchor `-56`.  But `Dominates` is by definition
`(S_C - 1).PosSemidef`, and a positive semidefinite matrix has NONNEGATIVE determinant.
Twenty nonnegative reals already fail to sum to a negative number.  The tie strengthens
"nonnegative" to "zero" and nothing downstream consumes the strengthening.

So both cells become unconditional:

* `not_forall_dominates_uniform_sixThree` — NO uniform `(6,3)` design, tied or not, has
  all twenty triples weakly dominating.  This is exactly the statement the Gale-dual lane
  set out to reach; the dual route reaches it again independently in `GaleDualWindow`.
* `not_forall_dominates_splitTetra` — no design on the split-tetrahedron ATOM family has
  all twenty triples weakly dominating, at any weighting.

The second one changes character once the tie is dropped, and the change is worth stating
plainly.  The tied proof went through the `-64` layer anchor over all twenty triples.  The
untied proof needs only ONE triple: `splitTetraDirIndex = ![0,1,2,2,3,3]` repeats direction
`2` at atoms `2` and `3`, so the triple `{2,3,4}` spans a plane, its gap determinant is
`-8`, and `Dominates` on that single triple is already false.  The `-64` aggregate is a
sharper instrument than this cell requires; the honest untied statement is the cheap one.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.ChartHadamard
import Gtz.Ties.SplitTetrahedronTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The one-line replacement for the tie -/

/-- **DOMINATION ALONE MAKES THE GAP DETERMINANT NONNEGATIVE.**  `Dominates` IS positive
semidefiniteness of the gap, and a positive semidefinite matrix has nonnegative
determinant.  This is the whole of what the tie was supplying, minus the part nobody
used: at a tie the value is pinned to zero, but only its sign is ever consumed. -/
theorem det_subsetSum_sub_one_nonneg_of_dominates (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected) :
    0 ≤ (subsetSum design selected - 1).det :=
  hdominates.det_nonneg

/-- Every summand of the twenty-triple layer aggregate is nonnegative once all twenty
triples dominate, so the aggregate itself is. -/
theorem sum_det_subsetSum_sub_one_nonneg_of_forall_dominates
    (design : WeightedDesign size rank)
    (hall : ∀ selected : Finset (Fin size), selected.card = rank → Dominates design selected) :
    0 ≤ ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
        (subsetSum design selected - 1).det :=
  Finset.sum_nonneg fun selected hselected =>
    det_subsetSum_sub_one_nonneg_of_dominates design
      (hall selected (Finset.mem_powersetCard.mp hselected).2)

/-! ## The uniform cell, unconditional -/

/-- **NO UNIFORM `(6,3)` DESIGN HAS ALL TWENTY TRIPLES WEAKLY DOMINATING.**  The tie
hypothesis of `Gtz.not_forall_dominates_of_isTie_uniform_sixThree` is deleted: the twenty
gap determinants are each nonnegative under domination alone, so their total is
nonnegative, and the shipped uniform layer anchor says that total is `-56`.

This kills the whole uniform stratum of `(6,3)` outright — no tie, no genericity, no
window condition.  It is the same statement the Gale-dual lane reaches from the
complementary projection in `GaleDualWindow`; the two routes are recorded there to be the
same identity read on `P` and on `1 - P`, related by an exact factor `5^3`. -/
theorem not_forall_dominates_uniform_sixThree (design : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, design.weight atomIndex = ((6 : ℝ))⁻¹)
    (hall : ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected) :
    False := by
  have hnonneg := sum_det_subsetSum_sub_one_nonneg_of_forall_dominates design hall
  rw [sum_det_subsetSum_sub_one_sixThree design huniform] at hnonneg
  norm_num at hnonneg

/-! ## The split-tetrahedron cell, unconditional

The atom family repeats direction `2` at atoms `2` and `3`, so the triple `{2, 3, 4}`
carries only two distinct directions.  Its atom sum is a rank-two matrix, its gap
determinant is `-8`, and one negative gap determinant already refutes domination on that
triple.  No aggregate, no anchor, no tie. -/

/-- The atom sum of the repeated triple `{2, 3, 4}` of the split-tetrahedron family: two
copies of direction `2` and one of direction `3`. -/
theorem subsetSum_repeatedTriple_splitTetra (design : WeightedDesign 6 3)
    (hatom : design.atom = splitTetraAtom) :
    subsetSum design {2, 3, 4} = !![3, -1, 1; -1, 3, -3; 1, -3, 3] := by
  have hsecond : design.atom 2 = ![(-1 : ℝ), 1, -1] := by rw [hatom]; rfl
  have hthird : design.atom 3 = ![(-1 : ℝ), 1, -1] := by rw [hatom]; rfl
  have hfourth : design.atom 4 = ![(-1 : ℝ), -1, 1] := by rw [hatom]; rfl
  have hexpand : ({2, 3, 4} : Finset (Fin 6)) = insert 2 (insert 3 {4}) := rfl
  ext rowIndex colIndex
  rw [subsetSum, hexpand, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply, hsecond, hthird, hfourth]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The repeated triple's gap determinant is `-8`, so it cannot dominate. -/
theorem det_subsetSum_sub_one_repeatedTriple_splitTetra (design : WeightedDesign 6 3)
    (hatom : design.atom = splitTetraAtom) :
    (subsetSum design {2, 3, 4} - 1).det = -8 := by
  have hgap : (!![3, -1, 1; -1, 3, -3; 1, -3, 3] : Matrix (Fin 3) (Fin 3) ℝ) - 1
      = !![2, -1, 1; -1, 2, -3; 1, -3, 2] := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]
  rw [subsetSum_repeatedTriple_splitTetra design hatom, hgap, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- **NO DESIGN ON THE SPLIT-TETRAHEDRON ATOM FAMILY HAS ALL TWENTY TRIPLES WEAKLY
DOMINATING**, at any weighting.  The tie hypothesis of
`Gtz.not_forall_dominates_of_isTie_splitTetra` is deleted, and with it the `-64` layer
anchor: the family repeats a direction, so the triple `{2, 3, 4}` has gap determinant
`-8 < 0`, and domination would force it nonnegative. -/
theorem not_forall_dominates_splitTetra (design : WeightedDesign 6 3)
    (hatom : design.atom = splitTetraAtom)
    (hall : ∀ selected : Finset (Fin 6), selected.card = 3 → Dominates design selected) :
    False := by
  have hcard : ({2, 3, 4} : Finset (Fin 6)).card = 3 := by decide
  have hnonneg := det_subsetSum_sub_one_nonneg_of_dominates design (hall _ hcard)
  rw [det_subsetSum_sub_one_repeatedTriple_splitTetra design hatom] at hnonneg
  norm_num at hnonneg

end Gtz
