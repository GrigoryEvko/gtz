/-
# The pair-conditioned tie criterion fires nowhere on the split-tetrahedron family

`Gtz.exists_pos_discriminantTie_of_pos_surplusForm` certifies a dominating
completion at a pair whose surplus form is strictly positive, and
`Gtz.sum_shareSurplus` prices the whole budget at `5 - m`, hence `-1` at size six.
This file locates the extremal object of that accounting inside a family the tree
already carries.

Every member of `Gtz.splitTetraDesign` is an exact tie
(`Gtz.splitTetraDesign_isTie`).  Here we show the criterion cannot see any of
them: the surplus form is NONPOSITIVE at every one of the thirty-six ordered
pairs, for every admissible split.

The arithmetic is uniform.  Each atom is a tetrahedron direction, so
`heavyExcess = 2` and `shareSurplus c = 5 * t c - 1`, and the pairing squares to
`9` on a duplicated pair and to `1` otherwise.  The form therefore collapses to

    (t a + t b) * (10 - 2 * pairing ^ 2) - 4,

which is `-8 (t a + t b) - 4 < 0` on a duplicated pair and `8 (t a + t b) - 4`
otherwise.  No weight of the family exceeds `1/4`, so the second expression is
nonpositive, and it VANISHES exactly at the pair `{0,1}` of undivided directions,
whose weights are both exactly `1/4`.  The criterion is therefore tight, and tight
on a tie.

Consequence: the criterion's non-firing region contains genuine ties, so it cannot
by itself decide the tie question at size six.  It also contains designs on the
other side -- `Gtz.icosaDesign` has uniform weight `1/6` and leverage `3`, hence
share surplus `-1/6` at every atom, so `Gtz.sum_offPair_weight_mul_discriminantTie_neg`
kills every pair there, yet `Gtz.icosaDesign_hasStrictlyDominatingSubset` holds.
-/
import Gtz.Quantitative.TieRowLaw
import Gtz.Ties.SplitTetrahedronTie
import Gtz.Design.StratumEmptinessLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix

variable (splitA splitB : ℝ) (hAPos : 0 < splitA) (hALt : splitA < 1/4)
  (hBPos : 0 < splitB) (hBLt : splitB < 1/4)

/-- **THE CRITERION FIRES NOWHERE ON THE FAMILY.**  The surplus form of
`Gtz.exists_pos_discriminantTie_of_pos_surplusForm` is nonpositive at every
ordered pair of every member, so that criterion never produces a dominating
completion here -- and every member is an exact tie. -/
theorem splitTetraDesign_surplusForm_nonpos (pivot pairFirst : Fin 6) :
    heavyExcess (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) pairFirst
        * shareSurplus (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) pivot
      + heavyExcess (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) pivot
        * shareSurplus (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) pairFirst
      - 2 * atomPairing (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt)
            pivot pairFirst ^ 2
        * ((splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).weight pivot
            + (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).weight pairFirst)
      ≤ 0 := by
  fin_cases pivot <;> fin_cases pairFirst <;>
    norm_num [heavyExcess, shareSurplus, atomShare, atomPairing, leverageOf,
      splitTetraDesign_atom, splitTetraDesign_weight, splitTetraAtom, splitTetraDirIndex,
      tetraAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.cons_val', Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] <;>
    linarith [hAPos, hALt, hBPos, hBLt]

/-- **THE LEDGER ENTRY.**  A heavy `(6,3)` design that is an exact tie and at which
the pair-conditioned surplus criterion is nonpositive at every pair.  So the
criterion's non-firing region is not confined to designs carrying a strict triple;
pair-conditioned averaging cannot decide the tie question at size six. -/
theorem exists_isTie_allHeavy_with_surplusForm_nonpos :
    ∃ D : WeightedDesign 6 3, AllHeavy D ∧ IsTie D
      ∧ ∀ pivot pairFirst : Fin 6,
          heavyExcess D pairFirst * shareSurplus D pivot
            + heavyExcess D pivot * shareSurplus D pairFirst
            - 2 * atomPairing D pivot pairFirst ^ 2
                * (D.weight pivot + D.weight pairFirst) ≤ 0 :=
  ⟨splitTetraDesign (1/8) (1/8) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    splitTetraDesign_allHeavy _ _ _ _ _ _,
    splitTetraDesign_isTie _ _ _ _ _ _,
    splitTetraDesign_surplusForm_nonpos _ _ _ _ _ _⟩

end Gtz
