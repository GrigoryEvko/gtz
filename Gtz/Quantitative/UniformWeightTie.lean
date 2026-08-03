/-
# The uniform-weight `ℚ(√5)` tie, and the partial-tie obstruction it inhabits

The campaign's sharpest owned equality datum, mechanized.  A `(6,3)` design with
**uniform weights `1/6`** — the extreme feasible weight floor — that is an **exact
tie**: some triple dominates, none dominates strictly.  It is the witness behind
the obituary of the `C·ε²` margin law: a weight floor buys no margin, because the
floor can be pushed to its maximum and a tie survives.

## The construction

Everything descends from a `(5,3)` **parent** in `ℚ(√5)`, built here in
coordinates that make the three square roots orthogonal to each other:

```
    a₀ = ( √(5/3),  0,      0     )        weight 1/3
    a₁ = (-√(2/3),  √3,     0     )        weight 1/6
    a₂ = ( √(2/3),  0,      √3    )        weight 1/6
    a₃ = ( √(2/3),  √3,     0     )        weight 1/6
    a₄ = (-√(2/3),  0,      √3    )        weight 1/6
```

Parseval is exact: the apex contributes `5/3` and the four rim atoms `4·(2/3)` to
the first diagonal slot, summing with the weights to `1`; the two planar slots each
receive `2·(1/6)·3 = 1`; every off-diagonal cancels in sign pairs.  The leverages
are `5/3` at the apex and `11/3` at each rim atom, so the parent is `AllHeavy`, and
the Gram is genuinely irrational — `⟨a₀, a_j⟩ = ±√10/3` — which is why the design
cannot be graphic and why the entries carry `Real.sqrt` rather than rationals.

The `(6,3)` witness is the **parallel split of the apex**: atom `0` is duplicated,
each copy taking half of the apex weight `1/3`.  That makes every weight `1/6`.
The split rides the shipped `Gtz.parallelSplitDesign` and inherits the tie from
`Gtz.parallelSplitDesign_isTie`, so no `(6,3)` domination argument is re-run.

## What lands

* `uniformTieParentDesign` — the `(5,3)` parent, with `isParseval`, its two
  leverages, `AllHeavy`, and `IsTie`.
* `uniformTieParent_det_nonpos` — every one of the ten parent triples has
  `det(S_C − 1) ≤ 0`; the tie's `¬ PosDef` half is read off it through
  `Matrix.PosDef.det_pos`, so the ten cases are discharged once, not twice.
* **The parent's domination is classified completely.**  All EIGHT tight triples
  — `{0,1,2} {0,1,4} {0,2,3} {0,3,4} {1,2,3} {1,2,4} {1,3,4} {2,3,4}` — get an
  explicit `uniformTieParentDesign_dominates_*`, each from a decomposition of the
  gap into TWO rank-one atoms; every tight gap here has rank exactly two, and
  exhibiting the two atoms is cheaper than any spectral argument.  The remaining
  two — `not_dominates_uniformTieParentDesign_zeroOneThree` and `_zeroTwoFour` —
  each fail by a `-1` on the diagonal.  Ten of ten, so `8 of 10` is a theorem list,
  not a measurement.
* `uniformTieDesign` — the `(6,3)` uniform-weight witness, with `IsTie`,
  `AllHeavy`, `HasWeightFloor (1/6)` and `HasParallelPair`.
* `uniformTieStress` — the stress `(1, −1, 0, 0, 0, 0)`, nonzero, annihilating and
  of coordinate sum zero: the tie is stress-carrying at parallel ratio one, which
  is what `Gtz.hasOnlyBalancedStress_of_isTie_sixThree` predicts and what the
  `(6,3)` stress walk consumes.
* `uniformTieDesign_isPartialTie` and `not_hasProductMixtureCertificate_sixThree`
  — the composition the mixture layer was waiting for (below).
* `hasWeightFloor_le_inv_size` — at GENERAL size, no design has a weight floor
  above `1/size`; so `1/6` is the extreme at six atoms, and it is attained here.
* `splitSevenDesign_isPartialTie` and `not_hasProductMixtureCertificate_sevenThree`
  — the same composition at `(7,3)`, from theorems the tree already shipped.

## The mixture composition

`Gtz.IsPartialTie` asks that every `k`-subset have a nonpositive gap determinant
and at least one have it strictly negative.  Before this module it had NO
inhabitant anywhere in the tree, so `Gtz.not_hasProductMixtureCertificate_of_exists_partialTie`
was a theorem with an unwitnessed hypothesis.  Both sizes are now discharged:

* at `(6,3)` by this file's tie — twelve of the twenty gap determinants vanish,
  eight are strictly negative (`−4` on the four triples carrying the parallel pair,
  `−10` on the other four) and none is positive;
* at `(7,3)` by `Gtz.splitSevenDesign`, whose `discriminantTie` is already known to
  be nonpositive everywhere and `−8` on the direction-repeating triples.

Rank three is odd, so the obstruction fires at both sizes and the product-mixture
certificate is refuted UNCONDITIONALLY there.

## Honest scope

**A tie at the extreme floor is not new in substance.**  The shipped
`Gtz.bundledCycleDesign` at `Gtz.bundlingSixThreeHeavy` also carries uniform weight
`1/6` (`Gtz.bundledCycleDesign_weight`) and is also an exact tie
(`Gtz.bundlingSixThreeHeavy_isTie`).  What is new here is a SECOND and different
point of the `(6,3)` tie variety: the bundled cycle's leverages are `5/3` (three
times) and `13/3` (three times), while this design's are `5/3` (twice) and `11/3`
(four times), so the two are not the same design under any relabelling.  The
existence statement `exists_isTie_allHeavy_hasWeightFloor_sixThree` is stated here
because no statement of that shape existed, not because the underlying fact was
unavailable.

The numbers quoted above and in the docstrings — the twelve tight triples, the
eight strict ones, the chart-side data of the original measurement — come from the
campaign's exact `ℚ(√5)` computation.  What is PROVED here is: the design is a
design, it is a tie, it is all-heavy, its weights are uniform, every gap
determinant is nonpositive and one is `−4`, and at the PARENT which eight of the ten
triples dominate and which two do not.  The child's count "twelve of twenty" is NOT
assembled here: it follows from the parent classification through the shipped
`Gtz.dominates_parallelSplitDesign_iff`, but that needs a `Set.InjOn` discharge per
triple and the partial-tie statement does not use it.

A statement-level `isDefEq` scan against the whole tree reports exactly two
coincidences, both of the same degenerate kind and both disclosed at their
declarations: a proposition about a design whose weight is definitionally the
constant `1/6` can be `isDefEq` to the same proposition about another such design.
No landed statement here duplicates shipped content.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer
import Gtz.Certificates.ResidueDissolution
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Design.RhoNormalForm
import Gtz.Quantitative.ExtremalBasisActivity
import Gtz.Quantitative.FlooredSpreadRegion
import Gtz.Quantitative.MixtureAggregates
import Gtz.Quantitative.DecisionAtlasSevenThree

namespace Gtz

open Matrix

/-! ## The three square roots

The parent's coordinates use three irrationalities, one per axis role.  Only their
squares are ever needed.  The two design-specific ones are named — `simp` would
otherwise split `Real.sqrt (5 / 3)` into `√5 / √3` and lose the square rule — while
the third is the bare `Real.sqrt 3`, whose square is already shipped. -/

/-- The apex atom's length `√(5/3)`: its square is the apex leverage. -/
noncomputable def uniformTieApexLength : ℝ := Real.sqrt (5 / 3)

/-- The rim atoms' shared axial component `√(2/3)`. -/
noncomputable def uniformTieRimAxial : ℝ := Real.sqrt (2 / 3)

@[simp] theorem uniformTieApexLength_mul_self :
    uniformTieApexLength * uniformTieApexLength = 5 / 3 :=
  Real.mul_self_sqrt (by norm_num)

@[simp] theorem uniformTieRimAxial_mul_self :
    uniformTieRimAxial * uniformTieRimAxial = 2 / 3 :=
  Real.mul_self_sqrt (by norm_num)

@[simp] theorem uniformTieApexLength_sq : uniformTieApexLength ^ 2 = 5 / 3 := by
  rw [sq]; exact uniformTieApexLength_mul_self

@[simp] theorem uniformTieRimAxial_sq : uniformTieRimAxial ^ 2 = 2 / 3 := by
  rw [sq]; exact uniformTieRimAxial_mul_self

/-! The rim atoms' planar component is the bare `Real.sqrt 3`, whose square is the
SHIPPED `Gtz.sqrt_three_sq`; the `mul_self` form is Mathlib's `Real.mul_self_sqrt`.
No local restatement is made — the tree already carries `√3 ^ 2 = 3` twice
(`Gtz.sqrt_three_sq` and `Gtz.rootThree_sq`).  The two design-specific roots above
DO get local names, and they earn them: `simp` rewrites a bare `Real.sqrt (5 / 3)`
to `√5 / √3` and then no square rule fires, whereas an opaque definition blocks the
split and keeps the arithmetic on rails. -/
/-! ## The `(5,3)` parent -/

/-- The parent's five atoms: one apex on the first axis, and four rim atoms
splitting into a `y`-pair `{1,3}` and a `z`-pair `{2,4}` with opposite axial signs
inside each pair. -/
noncomputable def uniformTieParentAtom : Fin 5 → Fin 3 → ℝ :=
  ![![uniformTieApexLength, 0, 0],
    ![-uniformTieRimAxial, Real.sqrt 3, 0],
    ![uniformTieRimAxial, 0, Real.sqrt 3],
    ![uniformTieRimAxial, Real.sqrt 3, 0],
    ![-uniformTieRimAxial, 0, Real.sqrt 3]]

/-- The parent's weights: `1/3` at the apex, `1/6` at each rim atom.  Splitting the
apex in half is what makes the child uniform. -/
noncomputable def uniformTieParentWeight : Fin 5 → ℝ :=
  ![1 / 3, 1 / 6, 1 / 6, 1 / 6, 1 / 6]

/-- **The `(5,3)` parent is a weighted design.**  Every off-diagonal Parseval entry
cancels between the two members of a rim pair; the diagonal needs only the three
squares. -/
noncomputable def uniformTieParentDesign : WeightedDesign 5 3 where
  atom := uniformTieParentAtom
  weight := uniformTieParentWeight
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num [uniformTieParentWeight]
  weight_sum_one := by simp [Fin.sum_univ_five, uniformTieParentWeight]; norm_num
  isParseval := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Fin.sum_univ_five, atomMatrix, uniformTieParentAtom,
        uniformTieParentWeight] <;> ring

@[simp] theorem uniformTieParentDesign_atom :
    uniformTieParentDesign.atom = uniformTieParentAtom := rfl

@[simp] theorem uniformTieParentDesign_weight :
    uniformTieParentDesign.weight = uniformTieParentWeight := rfl

/-- The apex leverage is `5/3`. -/
theorem uniformTieParent_leverage_apex :
    leverageOf (uniformTieParentAtom 0) = 5 / 3 := by
  simp [leverageOf, Fin.sum_univ_three, uniformTieParentAtom]

/-- Every rim leverage is `11/3`.  The multiset `{5/3, 11/3, 11/3, 11/3, 11/3}` is
what distinguishes this parent from the campaign's `(5,3)` diamond datum, whose
leverages are `2` and `13/4`. -/
theorem uniformTieParent_leverage_rim (atomIndex : Fin 5) (hne : atomIndex ≠ 0) :
    leverageOf (uniformTieParentAtom atomIndex) = 11 / 3 := by
  fin_cases atomIndex
  · exact absurd rfl hne
  all_goals simp [leverageOf, Fin.sum_univ_three, uniformTieParentAtom]
  all_goals try norm_num

theorem uniformTieParentDesign_allHeavy : AllHeavy uniformTieParentDesign := by
  intro atomIndex
  rw [uniformTieParentDesign_atom]
  by_cases hapex : atomIndex = 0
  · rw [hapex, uniformTieParent_leverage_apex]; norm_num
  · rw [uniformTieParent_leverage_rim atomIndex hapex]; norm_num

/-! ### The tie leg, at every triple at once

`Gtz.det_subsetSum_sub_one_eq_discriminantTie` turns the `3 × 3` determinant into a
polynomial in six scalars, so the ten triples cost ten scalar identities rather
than ten matrix computations. -/

set_option maxHeartbeats 2000000 in
/-- **Every parent triple has a nonpositive gap determinant.**  Eight vanish and
two equal `−10`. -/
theorem uniformTieParent_det_triple_nonpos (pivot pairFirst pairSecond : Fin 5)
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) :
    (subsetSum uniformTieParentDesign {pivot, pairFirst, pairSecond} - 1).det ≤ 0 := by
  rw [det_subsetSum_sub_one_eq_discriminantTie uniformTieParentDesign hpivotFirst
    hpivotSecond hpairDistinct]
  fin_cases pivot <;> fin_cases pairFirst <;> fin_cases pairSecond
  all_goals first
    | exact absurd rfl hpivotFirst
    | exact absurd rfl hpivotSecond
    | exact absurd rfl hpairDistinct
    | skip
  all_goals
    simp [discriminantTie, heavyExcess, atomPairing, leverageOf, Fin.sum_univ_three,
      dotProduct, uniformTieParentAtom]
  all_goals try ring_nf
  all_goals try simp
  all_goals try norm_num

theorem uniformTieParent_det_nonpos (selected : Finset (Fin 5)) (hcard : selected.card = 3) :
    (subsetSum uniformTieParentDesign selected - 1).det ≤ 0 := by
  obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct, rfl⟩ :=
    Finset.card_eq_three.mp hcard
  exact uniformTieParent_det_triple_nonpos pivot pairFirst pairSecond hpivotFirst
    hpivotSecond hpairDistinct

/-! ### The dominating half, and the two exceptions -/

/-- **The apex triple's gap is a sum of two rank-one atoms.**  Writing `p` for the
product of the two rim components (`p² = 2`), the gap is
`[[2,−p,p],[−p,2,0],[p,0,2]]`, which is `(p,−1,1)(p,−1,1)ᵀ + (0,1,1)(0,1,1)ᵀ`.
Rank exactly two, hence PSD and singular at once — the tie in one line. -/
theorem uniformTieParent_gap_zeroOneTwo :
    subsetSum uniformTieParentDesign {0, 1, 2} - 1
      = atomMatrix ![uniformTieRimAxial * Real.sqrt 3, -1, 1]
        + atomMatrix ![0, 1, 1] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex
  all_goals
    simp [subsetSum, atomMatrix, uniformTieParentAtom,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  all_goals try ring_nf
  all_goals try simp

theorem uniformTieParentDesign_dominates_zeroOneTwo :
    Dominates uniformTieParentDesign {0, 1, 2} := by
  rw [Dominates, uniformTieParent_gap_zeroOneTwo]
  exact (posSemidef_atomMatrix _).add (posSemidef_atomMatrix _)

/-! The remaining seven tight triples, by the same two-rank-one-atoms recipe.  The
four containing the apex have gap `[[2, ±p, ±p], [±p, 2, 0], [±p, 0, 2]]` with
`p² = 2`; the four made of rim atoms alone have gap `[[1, ·, ·], [·, ·, ·]]` with a
`5` in the slot the missing rim pair would have filled, and `5 = (√(5/3)·√3)²`. -/

theorem uniformTieParent_gap_zeroOneFour :
    subsetSum uniformTieParentDesign {0, 1, 4} - 1
      = atomMatrix ![uniformTieRimAxial * Real.sqrt 3, -1, -1]
        + atomMatrix ![0, 1, -1] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex
  all_goals
    simp [subsetSum, atomMatrix, uniformTieParentAtom,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  all_goals try ring_nf
  all_goals try simp

theorem uniformTieParentDesign_dominates_zeroOneFour :
    Dominates uniformTieParentDesign {0, 1, 4} := by
  rw [Dominates, uniformTieParent_gap_zeroOneFour]
  exact (posSemidef_atomMatrix _).add (posSemidef_atomMatrix _)

theorem uniformTieParent_gap_zeroTwoThree :
    subsetSum uniformTieParentDesign {0, 2, 3} - 1
      = atomMatrix ![uniformTieRimAxial * Real.sqrt 3, 1, 1]
        + atomMatrix ![0, 1, -1] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex
  all_goals
    simp [subsetSum, atomMatrix, uniformTieParentAtom,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  all_goals try ring_nf
  all_goals try simp

theorem uniformTieParentDesign_dominates_zeroTwoThree :
    Dominates uniformTieParentDesign {0, 2, 3} := by
  rw [Dominates, uniformTieParent_gap_zeroTwoThree]
  exact (posSemidef_atomMatrix _).add (posSemidef_atomMatrix _)

theorem uniformTieParent_gap_zeroThreeFour :
    subsetSum uniformTieParentDesign {0, 3, 4} - 1
      = atomMatrix ![uniformTieRimAxial * Real.sqrt 3, 1, -1]
        + atomMatrix ![0, 1, 1] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex
  all_goals
    simp [subsetSum, atomMatrix, uniformTieParentAtom,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  all_goals try ring_nf
  all_goals try simp

theorem uniformTieParentDesign_dominates_zeroThreeFour :
    Dominates uniformTieParentDesign {0, 3, 4} := by
  rw [Dominates, uniformTieParent_gap_zeroThreeFour]
  exact (posSemidef_atomMatrix _).add (posSemidef_atomMatrix _)

theorem uniformTieParent_gap_oneTwoThree :
    subsetSum uniformTieParentDesign {1, 2, 3} - 1
      = atomMatrix ![1, 0, uniformTieRimAxial * Real.sqrt 3] + atomMatrix ![0, uniformTieApexLength * Real.sqrt 3, 0] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex
  all_goals
    simp [subsetSum, atomMatrix, uniformTieParentAtom,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  all_goals try ring_nf
  all_goals try simp

theorem uniformTieParentDesign_dominates_oneTwoThree :
    Dominates uniformTieParentDesign {1, 2, 3} := by
  rw [Dominates, uniformTieParent_gap_oneTwoThree]
  exact (posSemidef_atomMatrix _).add (posSemidef_atomMatrix _)

theorem uniformTieParent_gap_oneTwoFour :
    subsetSum uniformTieParentDesign {1, 2, 4} - 1
      = atomMatrix ![1, -(uniformTieRimAxial * Real.sqrt 3), 0] + atomMatrix ![0, 0, uniformTieApexLength * Real.sqrt 3] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex
  all_goals
    simp [subsetSum, atomMatrix, uniformTieParentAtom,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  all_goals try ring_nf
  all_goals try simp

theorem uniformTieParentDesign_dominates_oneTwoFour :
    Dominates uniformTieParentDesign {1, 2, 4} := by
  rw [Dominates, uniformTieParent_gap_oneTwoFour]
  exact (posSemidef_atomMatrix _).add (posSemidef_atomMatrix _)

theorem uniformTieParent_gap_oneThreeFour :
    subsetSum uniformTieParentDesign {1, 3, 4} - 1
      = atomMatrix ![1, 0, -(uniformTieRimAxial * Real.sqrt 3)] + atomMatrix ![0, uniformTieApexLength * Real.sqrt 3, 0] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex
  all_goals
    simp [subsetSum, atomMatrix, uniformTieParentAtom,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  all_goals try ring_nf
  all_goals try simp

theorem uniformTieParentDesign_dominates_oneThreeFour :
    Dominates uniformTieParentDesign {1, 3, 4} := by
  rw [Dominates, uniformTieParent_gap_oneThreeFour]
  exact (posSemidef_atomMatrix _).add (posSemidef_atomMatrix _)

theorem uniformTieParent_gap_twoThreeFour :
    subsetSum uniformTieParentDesign {2, 3, 4} - 1
      = atomMatrix ![1, uniformTieRimAxial * Real.sqrt 3, 0] + atomMatrix ![0, 0, uniformTieApexLength * Real.sqrt 3] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex
  all_goals
    simp [subsetSum, atomMatrix, uniformTieParentAtom,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  all_goals try ring_nf
  all_goals try simp

theorem uniformTieParentDesign_dominates_twoThreeFour :
    Dominates uniformTieParentDesign {2, 3, 4} := by
  rw [Dominates, uniformTieParent_gap_twoThreeFour]
  exact (posSemidef_atomMatrix _).add (posSemidef_atomMatrix _)

/-- The first exceptional triple takes both members of the `y`-pair and leaves the
`z` axis unspanned: the gap's third diagonal entry is `−1`. -/
theorem uniformTieParent_gap_zeroOneThree_apply :
    (subsetSum uniformTieParentDesign {0, 1, 3} - 1) 2 2 = -1 := by
  simp [subsetSum, atomMatrix, uniformTieParentAtom,
    Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]

/-- The second exceptional triple takes both members of the `z`-pair and leaves the
`y` axis unspanned. -/
theorem uniformTieParent_gap_zeroTwoFour_apply :
    (subsetSum uniformTieParentDesign {0, 2, 4} - 1) 1 1 = -1 := by
  simp [subsetSum, atomMatrix, uniformTieParentAtom,
    Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]

theorem not_dominates_uniformTieParentDesign_zeroOneThree :
    ¬ Dominates uniformTieParentDesign {0, 1, 3} := by
  intro hdominates
  have hnonneg := hdominates.diag_nonneg (i := 2)
  rw [uniformTieParent_gap_zeroOneThree_apply] at hnonneg
  norm_num at hnonneg

theorem not_dominates_uniformTieParentDesign_zeroTwoFour :
    ¬ Dominates uniformTieParentDesign {0, 2, 4} := by
  intro hdominates
  have hnonneg := hdominates.diag_nonneg (i := 1)
  rw [uniformTieParent_gap_zeroTwoFour_apply] at hnonneg
  norm_num at hnonneg

/-- **The `(5,3)` parent is an exact tie.**  The apex triple dominates; nothing
dominates strictly, because a positive-definite gap would need a positive
determinant and every gap determinant here is nonpositive. -/
theorem uniformTieParentDesign_isTie : IsTie uniformTieParentDesign := by
  refine ⟨⟨{0, 1, 2}, by decide, uniformTieParentDesign_dominates_zeroOneTwo⟩, ?_⟩
  intro selected hcard hposDef
  exact absurd hposDef.det_pos (not_lt.mpr (uniformTieParent_det_nonpos selected hcard))

/-! ## The `(6,3)` uniform-weight witness -/

/-- The splitting map: atom `0` of the parent is served by the two child atoms `0`
and `1`; every other parent atom keeps a single child. -/
def uniformTieClassOf : Fin 6 → Fin 5 := ![0, 0, 1, 2, 3, 4]

/-- The child's weights: uniform `1/6`, the extreme feasible floor at six atoms. -/
noncomputable def uniformTieWeight : Fin 6 → ℝ := fun _ => 1 / 6

theorem uniformTie_isParallelSplitting :
    IsParallelSplitting uniformTieParentDesign uniformTieClassOf uniformTieWeight where
  hasPositiveWeights := fun _ => by norm_num [uniformTieWeight]
  hasClassTotals := by
    intro label
    rw [Finset.sum_filter]
    fin_cases label
    all_goals
      simp [uniformTieClassOf, uniformTieWeight, uniformTieParentWeight, Fin.sum_univ_six]
    all_goals try norm_num

/-- **The uniform-weight `ℚ(√5)` tie**, the campaign's sharpest owned equality
datum: six atoms, every weight `1/6`, all-heavy, an exact tie. -/
noncomputable def uniformTieDesign : WeightedDesign 6 3 :=
  parallelSplitDesign uniformTieParentDesign uniformTieClassOf uniformTieWeight
    uniformTie_isParallelSplitting

@[simp] theorem uniformTieDesign_atom (atomIndex : Fin 6) :
    uniformTieDesign.atom atomIndex = uniformTieParentAtom (uniformTieClassOf atomIndex) := rfl

/-- Every weight is `1/6`.  A statement-level `isDefEq` scan reports this as
coinciding with the shipped `Gtz.rootKillDesign_weight`: both propositions reduce to
`1 / 6 = 1 / 6`, because both designs carry a definitionally constant weight.  That
is a degeneracy of the proposition, not a duplication of content. -/
@[simp] theorem uniformTieDesign_weight (atomIndex : Fin 6) :
    uniformTieDesign.weight atomIndex = 1 / 6 := rfl

/-- **The witness is an exact tie**, inherited from the parent through the shipped
splitting law: a section of the parent's dominating triple dominates upstairs, and
nothing dominates strictly because a class-injective subset carries the parent's
gap and a class-repeating one is not even weakly dominating. -/
theorem uniformTieDesign_isTie : IsTie uniformTieDesign :=
  parallelSplitDesign_isTie uniformTieParentDesign uniformTieClassOf uniformTieWeight
    uniformTie_isParallelSplitting uniformTieParentDesign_isTie

theorem uniformTieDesign_allHeavy : AllHeavy uniformTieDesign := by
  intro atomIndex
  rw [uniformTieDesign_atom]
  fin_cases atomIndex
  all_goals
    simp [uniformTieClassOf, leverageOf, Fin.sum_univ_three, uniformTieParentAtom]
  all_goals try norm_num

/-- The witness sits at the extreme feasible floor.  DISCLOSURE: since the weights
are definitionally constant, this proposition is `isDefEq` to the shipped
`Gtz.icosaDesign_hasWeightFloor` — both unfold to `∀ i : Fin 6, 1 / 6 ≤ 1 / 6`.  It
is landed as the named entry point for THIS design; all of its content is
`uniformTieDesign_weight`. -/
theorem uniformTieDesign_hasWeightFloor : HasWeightFloor uniformTieDesign (1 / 6) := by
  intro atomIndex
  rw [uniformTieDesign_weight]

/-- The two apex copies are equal, not merely parallel: the ratio is `1`. -/
theorem uniformTieDesign_hasParallelPair : HasParallelPair uniformTieDesign :=
  ⟨0, 1, 1, by decide, by simp [uniformTieClassOf]⟩

/-! ### The stress

Two equal atoms are a stress, and its coordinate sum vanishes.  That is the
balanced-stress shape `Gtz.hasOnlyBalancedStress_of_isTie_sixThree` forces on every
`(6,3)` tie, exhibited concretely here. -/

/-- The stress `(1, −1, 0, 0, 0, 0)` carried by the parallel apex pair. -/
noncomputable def uniformTieStress : Fin 6 → ℝ := ![1, -1, 0, 0, 0, 0]

theorem uniformTieStress_ne_zero : uniformTieStress ≠ 0 := by
  intro hzero
  have hfirst := congrFun hzero 0
  simp [uniformTieStress] at hfirst

theorem uniformTieStress_annihilates :
    ∑ atomIndex, uniformTieStress atomIndex • atomMatrix (uniformTieDesign.atom atomIndex) = 0 := by
  ext rowIndex colIndex
  simp [Fin.sum_univ_six, uniformTieStress, uniformTieClassOf, atomMatrix]

theorem uniformTieStress_sum_eq_zero : ∑ atomIndex, uniformTieStress atomIndex = 0 := by
  simp [Fin.sum_univ_six, uniformTieStress]

/-! ## The partial-tie obstruction at `(6,3)` -/

set_option maxHeartbeats 4000000 in
/-- **Every one of the twenty triples has a nonpositive gap determinant.**  Twelve
vanish; of the eight strict ones, the four carrying the parallel pair give `−4` and
the four inherited from the parent's exceptions give `−10`. -/
theorem uniformTie_det_triple_nonpos (pivot pairFirst pairSecond : Fin 6)
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) :
    (subsetSum uniformTieDesign {pivot, pairFirst, pairSecond} - 1).det ≤ 0 := by
  rw [det_subsetSum_sub_one_eq_discriminantTie uniformTieDesign hpivotFirst
    hpivotSecond hpairDistinct]
  fin_cases pivot <;> fin_cases pairFirst <;> fin_cases pairSecond
  all_goals first
    | exact absurd rfl hpivotFirst
    | exact absurd rfl hpivotSecond
    | exact absurd rfl hpairDistinct
    | skip
  all_goals
    simp [discriminantTie, heavyExcess, atomPairing, leverageOf, Fin.sum_univ_three,
      dotProduct, uniformTieClassOf, uniformTieParentAtom]
  all_goals try ring_nf
  all_goals try simp
  all_goals try norm_num

/-- The strict witness: the triple made of the two apex copies and one rim atom
fails by exactly `−4`. -/
theorem uniformTie_det_zeroOneTwo :
    (subsetSum uniformTieDesign {0, 1, 2} - 1).det = -4 := by
  rw [det_subsetSum_sub_one_eq_discriminantTie uniformTieDesign
    (show (0 : Fin 6) ≠ 1 by decide) (show (0 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 2 by decide)]
  simp [discriminantTie, heavyExcess, atomPairing, leverageOf, Fin.sum_univ_three,
    dotProduct, uniformTieClassOf, uniformTieParentAtom]
  ring_nf
  simp
  norm_num

/-- **The first inhabitant of `Gtz.IsPartialTie` anywhere in the tree.** -/
theorem uniformTieDesign_isPartialTie : IsPartialTie uniformTieDesign := by
  constructor
  · intro selected hcard
    obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct, rfl⟩ :=
      Finset.card_eq_three.mp hcard
    exact uniformTie_det_triple_nonpos pivot pairFirst pairSecond hpivotFirst
      hpivotSecond hpairDistinct
  · exact ⟨{0, 1, 2}, by decide, by rw [uniformTie_det_zeroOneTwo]; norm_num⟩

/-- **The product-mixture certificate is refuted UNCONDITIONALLY at `(6,3)`** — at
the very design the campaign's measurement was taken on.  No formula `weight(design)`
can certify GTZ through the product mixture. -/
theorem not_hasProductMixtureCertificate_sixThree :
    ¬ HasProductMixtureCertificate 6 3 :=
  not_hasProductMixtureCertificate_of_exists_partialTie (by decide)
    ⟨uniformTieDesign, uniformTieDesign_isPartialTie⟩

/-- The concrete reading at the tie: EVERY strictly positive product weighting puts
a root of the mixture strictly inside `(0,1)`. -/
theorem exists_root_productMixture_lt_one_uniformTieDesign
    (weight : Fin 6 → ℝ) (hpos : ∀ atomIndex : Fin 6, 0 < weight atomIndex) :
    ∃ level : ℝ, 0 < level ∧ level < 1 ∧
      Polynomial.eval level (productMixture uniformTieDesign weight) = 0 :=
  exists_root_productMixture_lt_one_of_odd uniformTieDesign weight (by decide) hpos
    uniformTieDesign_isPartialTie

/-! ## The weight floor is maximal, and a tie survives at the maximum -/

/-- **No design has a weight floor above `1/size`**, at general size: `size` weights
each at least the floor sum to one.  The leverage analogue is the shipped
`Gtz.le_rank_of_forall_le_leverage`; this is the weight side. -/
theorem hasWeightFloor_le_inv_size {size : ℕ} (design : WeightedDesign size 3) {floor : ℝ}
    (hfloor : HasWeightFloor design floor) (atomIndex : Fin size) :
    floor ≤ ((size : ℝ))⁻¹ := by
  have hsizePos : (0 : ℝ) < (size : ℝ) := by exact_mod_cast Fin.pos atomIndex
  have hbudget : (size : ℝ) * floor ≤ 1 := by
    calc (size : ℝ) * floor = ∑ _otherIndex : Fin size, floor := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ otherIndex, design.weight otherIndex :=
          Finset.sum_le_sum fun otherIndex _ => hfloor otherIndex
      _ = 1 := design.weight_sum_one
  refine le_of_mul_le_mul_left ?_ hsizePos
  rw [mul_inv_cancel₀ hsizePos.ne']
  exact hbudget

/-- `1/6` is the extreme feasible floor at six atoms — and this tie attains it. -/
theorem uniformTieDesign_hasWeightFloor_isExtreme {floor : ℝ}
    (hfloor : HasWeightFloor uniformTieDesign floor) : floor ≤ 1 / 6 := by
  have hbound := hasWeightFloor_le_inv_size uniformTieDesign hfloor 0
  norm_num at hbound
  linarith

/-- **A weight floor buys no margin.**  At EVERY feasible floor the all-heavy
`(6,3)` class still contains an exact tie, so no positive lower bound on the
floored covering margin can exist there.  The shipped
`Gtz.bundlingSixThreeHeavy_isTie` is a second, pre-existing witness at the extreme
floor with different leverages; the content added here is the witness, not the
insight. -/
theorem exists_isTie_allHeavy_hasWeightFloor_sixThree {floor : ℝ} (hfloor : floor ≤ 1 / 6) :
    ∃ design : WeightedDesign 6 3,
      IsTie design ∧ AllHeavy design ∧ HasWeightFloor design floor :=
  ⟨uniformTieDesign, uniformTieDesign_isTie, uniformTieDesign_allHeavy,
    hasWeightFloor_mono hfloor uniformTieDesign_hasWeightFloor⟩

/-! ## The same obstruction at `(7,3)`

`Gtz.splitSevenDesign` is a partial tie from theorems the tree already shipped: its
tie leg is nonpositive at every triple, and `−8` on the fifteen triples that repeat
a direction.  `splitSevenDirection = ![0,1,2,3,0,1,2]`, so atoms `0` and `4` share
direction `0` and `{0,4,1}` is the strict witness. -/

/-- **The split tetrahedron is a partial tie.** -/
theorem splitSevenDesign_isPartialTie : IsPartialTie splitSevenDesign := by
  constructor
  · intro selected hcard
    obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct, rfl⟩ :=
      Finset.card_eq_three.mp hcard
    rw [det_subsetSum_sub_one_eq_discriminantTie splitSevenDesign hpivotFirst
      hpivotSecond hpairDistinct]
    exact splitSevenDesign_discriminantTie_nonpos hpivotFirst hpivotSecond hpairDistinct
  · refine ⟨{0, 4, 1}, by decide, ?_⟩
    rw [det_subsetSum_sub_one_eq_discriminantTie splitSevenDesign
        (show (0 : Fin 7) ≠ 4 by decide) (show (0 : Fin 7) ≠ 1 by decide)
        (show (4 : Fin 7) ≠ 1 by decide),
      splitSevenDesign_discriminantTie_of_repeatedDirection
        (show (0 : Fin 7) ≠ 4 by decide) (show (0 : Fin 7) ≠ 1 by decide)
        (show (4 : Fin 7) ≠ 1 by decide) (Or.inl (by decide))]
    norm_num

/-- **The product-mixture certificate is refuted UNCONDITIONALLY at `(7,3)`.** -/
theorem not_hasProductMixtureCertificate_sevenThree :
    ¬ HasProductMixtureCertificate 7 3 :=
  not_hasProductMixtureCertificate_of_exists_partialTie (by decide)
    ⟨splitSevenDesign, splitSevenDesign_isPartialTie⟩

/-- The concrete reading at the split tetrahedron. -/
theorem exists_root_productMixture_lt_one_splitSevenDesign
    (weight : Fin 7 → ℝ) (hpos : ∀ atomIndex : Fin 7, 0 < weight atomIndex) :
    ∃ level : ℝ, 0 < level ∧ level < 1 ∧
      Polynomial.eval level (productMixture splitSevenDesign weight) = 0 :=
  exists_root_productMixture_lt_one_of_odd splitSevenDesign weight (by decide) hpos
    splitSevenDesign_isPartialTie

end Gtz
