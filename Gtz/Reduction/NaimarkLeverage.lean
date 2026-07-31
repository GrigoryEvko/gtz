/-
# The dual-leverage dictionary and the co-singleton narrowing

`Gtz.exists_naimarkDual_loewnerEquiv` (Gtz/Reduction/SplitTransfer.lean) now
returns a third verdict alongside the weights and the complement flip: a DUAL
atom is heavy exactly when the PRIMAL co-singleton it indexes strictly dominates.
This module is what that conjunct is for.

The dictionary matters because it converts a statement about an object nobody can
see — the Naimark dual, which every theorem in the campaign delivers
existentially — into a condition on the design in hand.  `AllHeavy dualDesign` is
uncheckable without building the dual; `∀ c, (subsetSum D {c}ᶜ − 1).PosDef` is a
finite list of definiteness tests on the primal, and by
`hasStrictlyDominatingCoSingletons_iff_forall_pivot_lt_one` it is also a finite
list of comparisons in the shipped pivot chart.

The payoff is unconditional, and it comes from an asymmetry in where the two
deflations land.  A design with a LIGHT dual atom deflates on the DUAL side, one
size down and at the dual rank `size + 1 − k`.  At `(7,3)` that is `(6,4)`, which
is corank two and therefore a theorem; the primal deflation of the same design
would land on `(6,3)`, which is open.  So going through the dual buys a decision
that the primal route cannot make.  At `(6,3)` the same trick lands on `(5,3)`,
again corank two, again a theorem.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* The primal-intrinsic reading of dual all-heaviness, and its bridge to the
  shipped pivot chart.
* `dominating_of_coSingleton_not_posDef` and its `(7,3)` and `(6,3)` instances:
  a design with a failing co-singleton ALREADY has a dominating `k`-subset, with
  no open hypothesis anywhere.
* The narrowed frontier: `GtzWeightedHeavy (size+1) k` may assume its
  co-singletons all strictly dominate, so the residual `(7,3)` obligation is the
  DOUBLY heavy stratum — all-heavy designs whose duals are also all-heavy.
* `lonelyAxisDesign`, an all-heavy `(7,3)` design outside that stratum, so the
  narrowing is PROPER and the decision above has non-empty scope.
* The dual-cell chain: at every rank `4 ≤ rank` a single all-heavy corank-three
  cell carries all of rank three, giving `GtzWeightedHeavy 7 4` as a
  SINGLE-obligation frontier, and the identification of the campaign's two
  independent polynomial encodings one rank apart.

## NOT proved here

`GtzWeightedHeavy 7 3` itself, and `GtzWeightedHeavy 6 3`.  Everything below is a
narrowing or a re-encoding of those two, never a discharge.  The residual
hypothesis `hnarrow` is passed through unexamined in every statement that takes
it, and the reader should treat any theorem carrying it as conditional.

Provenance: scratch reports 05 (`/tmp/gtz-wf/deepen/probe.lean`) and 21
(`/tmp/gtz-wf/dual7/probe.lean`).  Report 05's copy of the Naimark construction
was NOT landed — the shipped theorem was generalised in place instead, so the
tree carries the construction twice rather than three times.  Report 21's
`dominating_of_dual_light_atom` and `dominates_or_dual_allHeavy` were dropped as
strictly weaker packagings of `dominating_of_coSingleton_not_posDef` and
`gtzWeightedHeavy_of_doublyHeavy`: they demand a dual as a hypothesis, which no
caller can supply, whereas these construct it and state the trigger primally.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.Deflation
import Gtz.Reduction.DescentLadder
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.RankFourWindow
import Gtz.Reduction.RankInductionStep
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Ties.CorankOneTieCriterion
import Gtz.Ties.SevenThreeTieLocus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The primal-intrinsic reading of dual all-heaviness -/

/-- **Every co-singleton strictly dominates.**  The primal-intrinsic form of "the
Naimark dual is all-heavy": deleting any single atom still leaves the unweighted
atom sum strictly above the identity.  Stated with the `{c}ᶜ` idiom to match the
dictionary conjunct of `Gtz.exists_naimarkDual_loewnerEquiv`; the equivalent
`Finset.univ.erase c` reading used everywhere else in the tree is
`hasStrictlyDominatingCoSingletons_iff_forall_pivot_lt_one` below. -/
def HasStrictlyDominatingCoSingletons (D : WeightedDesign m k) : Prop :=
  ∀ atomIndex : Fin m, (subsetSum D {atomIndex}ᶜ - 1).PosDef

/-- **The narrowing lives in the shipped pivot chart.**  The co-singleton
condition is exactly "every pivot against the full set is below one", so it is
decided by the same scalar family that `Gtz.card_pivot_le_one_ge` counts and
`Gtz.isTie_iff_forall_pivot_eq_one` tests for equality.  Without this bridge the
predicate above would be an unlinked island beside the tree's existing pivot
vocabulary; with it, the `{c}ᶜ` and `Finset.univ.erase c` idioms are one thing.

Note the direction of the strictness: `Gtz.card_pivot_le_one_ge` supplies at
least `m − k` atoms with `pivot ≤ 1`, which is the WEAK inequality and does NOT
give this predicate for free. -/
theorem hasStrictlyDominatingCoSingletons_iff_forall_pivot_lt_one
    (D : WeightedDesign m k) (hm : 2 ≤ m) :
    HasStrictlyDominatingCoSingletons D
      ↔ ∀ atomIndex, pivot D Finset.univ atomIndex < 1 := by
  classical
  have hbridge : ∀ atomIndex : Fin m,
      (subsetSum D {atomIndex}ᶜ - 1).PosDef ↔ pivot D Finset.univ atomIndex < 1 := by
    intro atomIndex
    rw [Finset.compl_singleton]
    exact erase_strictDominates_iff_pivot_lt_one D Finset.univ (posDef_fullExcess D hm)
      (Finset.mem_univ atomIndex)
  exact ⟨fun hstrict atomIndex => (hbridge atomIndex).mp (hstrict atomIndex),
    fun hpivot atomIndex => (hbridge atomIndex).mpr (hpivot atomIndex)⟩

/-- **The dictionary, packaged.**  Every design has a Naimark dual whose
all-heaviness is exactly the primal co-singleton condition, and which still flips
domination across complements.  This is the form downstream reductions consume:
the dual's defining property is now something the caller can test without ever
constructing it. -/
theorem exists_naimarkDual_allHeavy_iff (hk : 1 ≤ k) (hkm : k + 1 ≤ m)
    (D : WeightedDesign m k) :
    ∃ dualDesign : WeightedDesign m (m - k),
      (∀ c, dualDesign.weight c = D.weight c) ∧
      (AllHeavy dualDesign ↔ HasStrictlyDominatingCoSingletons D) ∧
      ∀ C : Finset (Fin m), C.card = k →
        (Dominates D C ↔ Dominates dualDesign Cᶜ) := by
  obtain ⟨dualDesign, hweights, hdictionary, hequiv⟩ :=
    exists_naimarkDual_loewnerEquiv hk hkm D
  exact ⟨dualDesign, hweights,
    ⟨fun hheavy atomIndex => (hdictionary atomIndex).mp (hheavy atomIndex),
     fun hstrict atomIndex => (hdictionary atomIndex).mpr (hstrict atomIndex)⟩,
    fun C hC => (hequiv C hC).1⟩

/-! ## The unconditional co-singleton decision -/

/-- **A failing co-singleton decides the design.**  If deleting some atom leaves
the unweighted sum NOT strictly above the identity, the design already has a
dominating `k`-subset — provided weighted GTZ is known one size down at the DUAL
rank `size + 1 − k`.

That obligation is the whole point.  It is a strictly different requirement from
the primal recursion, and at the cells this campaign cares about it is strictly
easier: the primal deflation of a `(7,3)` design would need `(6,3)`, which is
open, while this one needs `(6,4)`, which is corank two. -/
theorem dominating_of_coSingleton_not_posDef {size : ℕ} (hk : 1 ≤ k)
    (hkm : k + 1 ≤ size + 1) (hsize : 1 ≤ size)
    (hdualRec : GtzWeighted size (size + 1 - k))
    (D : WeightedDesign (size + 1) k) (atomIndex : Fin (size + 1))
    (hfail : ¬ (subsetSum D {atomIndex}ᶜ - 1).PosDef) :
    ∃ C : Finset (Fin (size + 1)), C.card = k ∧ Dominates D C := by
  obtain ⟨dualDesign, -, hdictionary, hflip⟩ :=
    exists_naimarkDual_loewnerEquiv (m := size + 1) (k := k) hk hkm D
  have hlight : leverageOf (dualDesign.atom atomIndex) ≤ 1 :=
    not_lt.mp fun hheavy => hfail ((hdictionary atomIndex).mp hheavy)
  obtain ⟨dualPick, hdualCard, hdualDominates⟩ :=
    dominating_of_light_atom (m := size) dualDesign hsize hdualRec atomIndex hlight
  have hcompCard : (dualPickᶜ : Finset (Fin (size + 1))).card = k := by
    rw [Finset.card_compl, Fintype.card_fin, hdualCard]
    omega
  exact ⟨dualPickᶜ, hcompCard, (hflip dualPickᶜ hcompCard).1.mpr (by rwa [compl_compl])⟩

/-- **The `(7,3)` instance, unconditional.**  `GtzWeighted 6 4` is corank two, a
theorem, so no open hypothesis survives: any `(7,3)` design with a co-singleton
that fails to dominate strictly ALREADY has a dominating triple. -/
theorem dominating_of_coSingleton_not_posDef_sevenThree (D : WeightedDesign 7 3)
    (atomIndex : Fin 7) (hfail : ¬ (subsetSum D {atomIndex}ᶜ - 1).PosDef) :
    ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C :=
  dominating_of_coSingleton_not_posDef (size := 6) (k := 3) (by norm_num) (by norm_num)
    (by norm_num) (gtzWeighted_corank_two 4 (by norm_num)) D atomIndex hfail

/-- **The `(6,3)` instance, unconditional.**  `(6,3)` is its own Naimark dual, so
the dual deflation lands on `(5,3)` — corank two, and again a theorem.  This is
the cell the current campaign is building toward, and the statement holds there
with no open hypothesis. -/
theorem dominating_of_coSingleton_not_posDef_sixThree (D : WeightedDesign 6 3)
    (atomIndex : Fin 6) (hfail : ¬ (subsetSum D {atomIndex}ᶜ - 1).PosDef) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C :=
  dominating_of_coSingleton_not_posDef (size := 5) (k := 3) (by norm_num) (by norm_num)
    (by norm_num) (gtzWeighted_corank_two 3 (by norm_num)) D atomIndex hfail

/-! ## The narrowed frontier

The dual deflation lands at `(size, size + 1 − k)`, so the narrowing below is
UNCONDITIONAL exactly when weighted GTZ is already known there.  At `(7,3)` that
is `(6,4)` and at `(6,3)` it is `(5,3)` — both corank two, both theorems. -/

/-- **The general narrowed frontier.**  All-heavy GTZ at `(size+1, k)` follows
from its restriction to designs whose co-singletons all strictly dominate, given
weighted GTZ one size down at the DUAL rank.  Everything outside that stratum is
decided by `dominating_of_coSingleton_not_posDef`. -/
theorem gtzWeightedHeavy_of_doublyHeavy {size : ℕ} (hk : 1 ≤ k)
    (hkm : k + 1 ≤ size + 1) (hsize : 1 ≤ size)
    (hdualRec : GtzWeighted size (size + 1 - k))
    (hnarrow : ∀ D : WeightedDesign (size + 1) k, AllHeavy D →
      HasStrictlyDominatingCoSingletons D →
        ∃ C : Finset (Fin (size + 1)), C.card = k ∧ Dominates D C) :
    GtzWeightedHeavy (size + 1) k := by
  classical
  intro D hheavy
  by_cases hstrict : HasStrictlyDominatingCoSingletons D
  · exact hnarrow D hheavy hstrict
  · obtain ⟨atomIndex, hfail⟩ := not_forall.mp hstrict
    exact dominating_of_coSingleton_not_posDef hk hkm hsize hdualRec D atomIndex hfail

/-- **`GtzWeightedHeavy 7 3` may assume its co-singletons strictly dominate.**
The residual frontier is the DOUBLY heavy stratum: designs that are all-heavy AND
whose Naimark duals are all-heavy. -/
theorem gtzWeightedHeavy_seven_three_of_doublyHeavy
    (hnarrow : ∀ D : WeightedDesign 7 3, AllHeavy D →
      HasStrictlyDominatingCoSingletons D →
        ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C) :
    GtzWeightedHeavy 7 3 :=
  gtzWeightedHeavy_of_doublyHeavy (size := 6) (k := 3) (by norm_num) (by norm_num)
    (by norm_num) (gtzWeighted_corank_two 4 (by norm_num)) hnarrow

/-- The `(6,3)` narrowed frontier. -/
theorem gtzWeightedHeavy_six_three_of_doublyHeavy
    (hnarrow : ∀ D : WeightedDesign 6 3, AllHeavy D →
      HasStrictlyDominatingCoSingletons D →
        ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    GtzWeightedHeavy 6 3 :=
  gtzWeightedHeavy_of_doublyHeavy (size := 5) (k := 3) (by norm_num) (by norm_num)
    (by norm_num) (gtzWeighted_corank_two 3 (by norm_num)) hnarrow

/-- **The doubly-heavy stratum at `(7,3)` carries all of rank three.**  Composed
with `Gtz.rank_three_of_heavy_top`, this is the sharpest form of the campaign's
one-object-per-rank frontier that the duality route supports. -/
theorem gtzWeightedAll_three_of_doublyHeavy_seven_three
    (hnarrow : ∀ D : WeightedDesign 7 3, AllHeavy D →
      HasStrictlyDominatingCoSingletons D →
        ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C) :
    GtzWeightedAll 3 :=
  rank_three_of_heavy_top (gtzWeightedHeavy_seven_three_of_doublyHeavy hnarrow)

/-- The 1997 statement at rank three, from the doubly-heavy stratum. -/
theorem gtz_original_rank_three_of_doublyHeavy_seven_three
    (hnarrow : ∀ D : WeightedDesign 7 3, AllHeavy D →
      HasStrictlyDominatingCoSingletons D →
        ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C) :
    ∀ n, 0 < n → GtzOriginal n 3 :=
  original_of_weighted 3 (gtzWeightedAll_three_of_doublyHeavy_seven_three hnarrow)

/-! ## The narrowing is a PROPER restriction

`dominating_of_coSingleton_not_posDef_sevenThree` would be worthless if every
all-heavy `(7,3)` design already had strictly dominating co-singletons.  It does
not.  In the design below atom `0` is the ONLY atom with a first coordinate, so
deleting it leaves the unweighted sum with nothing at all in that direction, and
the gap matrix carries `−1` on its diagonal. -/

/-- Seven axis atoms: one of length `3/2` along the first coordinate, three of
length `3/2` along the second, three of length `3` along the third. -/
noncomputable def lonelyAxisAtom : Fin 7 → Fin 3 → ℝ :=
  ![![3/2, 0, 0], ![0, 3/2, 0], ![0, 3/2, 0], ![0, 3/2, 0],
    ![0, 0, 3], ![0, 0, 3], ![0, 0, 3]]

/-- The matching weights `1 / (multiplicity · leverage)`.  Parseval closes on the
reciprocal-square identity `4/9 + 3·(4/27) + 3·(1/27) = 1`. -/
noncomputable def lonelyAxisWeight : Fin 7 → ℝ :=
  ![4/9, 4/27, 4/27, 4/27, 1/27, 1/27, 1/27]

/-- The witness design. -/
noncomputable def lonelyAxisDesign : WeightedDesign 7 3 where
  atom := lonelyAxisAtom
  weight := lonelyAxisWeight
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;> norm_num [lonelyAxisWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_seven]
    simp [lonelyAxisWeight]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul, Fin.sum_univ_seven, lonelyAxisAtom, lonelyAxisWeight]
    fin_cases rowIndex <;> fin_cases colIndex <;> simp <;> norm_num

@[simp] theorem lonelyAxisDesign_atom : lonelyAxisDesign.atom = lonelyAxisAtom := rfl

@[simp] theorem lonelyAxisDesign_weight : lonelyAxisDesign.weight = lonelyAxisWeight := rfl

/-- The witness is all-heavy: leverages `9/4` on four atoms and `9` on three. -/
theorem allHeavy_lonelyAxisDesign : AllHeavy lonelyAxisDesign := by
  intro atomIndex
  simp only [lonelyAxisDesign_atom, leverageOf, Fin.sum_univ_three, lonelyAxisAtom]
  fin_cases atomIndex <;> simp <;> norm_num

/-- **The first co-singleton fails.**  Deleting atom `0` empties the first
coordinate, so by `Gtz.coSingletonExcess_eq_coParseval_sub_atomMatrix` the gap
matrix has `−1` there and cannot be positive definite. -/
theorem not_posDef_coSingleton_lonelyAxisDesign :
    ¬ (subsetSum lonelyAxisDesign {(0 : Fin 7)}ᶜ - 1).PosDef := by
  intro hposDef
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 (x := ![1, 0, 0])
    (by
      intro hzero
      have hentry := congrFun hzero 0
      norm_num at hentry)
  rw [star_trivial,
    coSingletonExcess_eq_coParseval_sub_atomMatrix lonelyAxisDesign 0] at hform
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, atomMatrix,
    Matrix.vecMulVec_apply, Fin.sum_univ_seven, Fin.sum_univ_three,
    lonelyAxisDesign_atom, lonelyAxisDesign_weight, lonelyAxisAtom, lonelyAxisWeight] at hform
  simp at hform
  norm_num at hform

/-- **The co-singleton hypothesis is not automatic on the all-heavy stratum.**
There is an all-heavy `(7,3)` design outside `HasStrictlyDominatingCoSingletons`,
so `gtzWeightedHeavy_seven_three_of_doublyHeavy` is a genuine narrowing of the
frontier and `dominating_of_coSingleton_not_posDef_sevenThree` has non-empty
scope. -/
theorem exists_allHeavy_sevenThree_not_hasStrictlyDominatingCoSingletons :
    ∃ D : WeightedDesign 7 3, AllHeavy D ∧ ¬ HasStrictlyDominatingCoSingletons D :=
  ⟨lonelyAxisDesign, allHeavy_lonelyAxisDesign,
    fun hstrict => not_posDef_coSingleton_lonelyAxisDesign (hstrict 0)⟩

/-! ## The dual cell: rank three read one rank up

Naimark duality exchanges rank `k` with rank `m − k` at the SAME size, so the
frontier cell `(7,3)` has a dual partner `(7,4)`.  On the dual side the all-heavy
reduction has a SINGLE obligation, because its deflation branch bottoms out at
corank two — a theorem — rather than at another open cell. -/

/-- **The all-heavy reduction on the dual side has a single obligation.**  At
corank three the light branch deflates to corank two, so `GtzWeightedHeavy
(rank+3) rank` alone gives the full `GtzWeighted (rank+3) rank`. -/
theorem gtzWeighted_corank_three_of_heavy (rank : ℕ) (hrank : 2 ≤ rank)
    (hheavy : GtzWeightedHeavy (rank + 3) rank) : GtzWeighted (rank + 3) rank := by
  intro D
  by_cases hlight : ∃ light, leverageOf (D.atom light) ≤ 1
  · obtain ⟨light, hlightLeverage⟩ := hlight
    exact dominating_of_light_atom (m := rank + 2) D (by omega)
      (gtzWeighted_corank_two rank hrank) light hlightLeverage
  · exact hheavy D fun atomIndex =>
      not_le.mp fun hle => hlight ⟨atomIndex, hle⟩

/-- **One all-heavy corank-three cell carries all of rank three**, at every rank
`4 ≤ rank`.  Duality turns `(rank+3, rank)` into `(rank+3, 3)`, and `rank + 3 ≥ 7`
is above the crystallization cap `M(3) = 7`, so size monotonicity lands on
`(7,3)`.

The bound `4 ≤ rank` is exactly where `(6,3)`'s self-duality bites.  At `rank = 3`
the cell is `(6,3)`, the dual rank `6 − 3` is `3` again, the duality step is the
identity `Iff.rfl`, and size monotonicity cannot climb from six atoms back up to
the cap.  That degeneracy is the mechanized form of "size six was the historic
wall", and it is why this route is silent at the very cell it would most help. -/
theorem gtzWeightedAll_three_of_heavy_corank_three (rank : ℕ) (hrank : 4 ≤ rank)
    (hheavy : GtzWeightedHeavy (rank + 3) rank) : GtzWeightedAll 3 := by
  have hfull : GtzWeighted (rank + 3) rank :=
    gtzWeighted_corank_three_of_heavy rank (by omega) hheavy
  have hdualRank : GtzWeighted (rank + 3) 3 := by
    refine gtzWeighted_of_dual_rank (by omega) (by omega) ?_
    have hcomplement : rank + 3 - 3 = rank := by omega
    rw [hcomplement]
    exact hfull
  exact gtzWeightedAll_three_of_seven_three
    (gtzWeighted_of_le (by omega) hdualRank)

/-- **The dual frontier cell: `GtzWeightedHeavy 7 4` alone carries rank three.**
The rank-four reading of the campaign's `(7,3)` residual, with a SINGLE
obligation — there is no `(6,4)` companion, since corank two is a theorem.  The
dual involution is genuinely nontrivial here: `7 − 3 = 4 ≠ 3`, so this frontier
sentence and the primal one live at different ranks. -/
theorem gtzWeightedAll_three_of_heavy_seven_four (hheavy : GtzWeightedHeavy 7 4) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_heavy_corank_three 4 (by norm_num) hheavy

/-- The 1997 statement itself, from the dual frontier cell. -/
theorem gtz_original_rank_three_of_heavy_seven_four
    (hheavy : GtzWeightedHeavy 7 4) : ∀ n, 0 < n → GtzOriginal n 3 :=
  original_of_weighted 3 (gtzWeightedAll_three_of_heavy_seven_four hheavy)

/-- **The rank-four polynomial sentence carries rank three.**
`PivotMinorCoveringFour 7`: over the 35 quadruples of a weighted all-heavy
`(7,4)` design, seven pivot-containing principal minors of `Gram − I` are
simultaneously nonnegative. -/
theorem gtzWeightedAll_three_of_pivotMinorCoveringFour_seven
    (hcover : PivotMinorCoveringFour 7) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_heavy_seven_four
    ((gtzWeightedHeavy_four_iff_pivotMinorCoveringFour 7).mpr hcover)

/-- **The two polynomial frontiers are the same sentence.**
`DiscriminantCovering 7` (35 triples, two inequalities of degrees two and three
in the six Gram entries of a `3 × 3` block) and `PivotMinorCoveringFour 7` (35
quadruples, seven principal minors of a `4 × 4` block) are equivalent — each is
equivalent to the whole of rank three.  So the campaign has a second, independent
polynomial encoding of its frontier, one rank higher. -/
theorem discriminantCovering_seven_iff_pivotMinorCoveringFour_seven :
    DiscriminantCovering 7 ↔ PivotMinorCoveringFour 7 := by
  constructor
  · intro hdisc
    have hrankThree : GtzWeightedAll 3 :=
      discriminantCovering_seven_iff_rank_three.mp hdisc
    refine (gtzWeightedHeavy_four_iff_pivotMinorCoveringFour 7).mp ?_
    have hplain : GtzWeighted 7 4 :=
      gtzWeighted_seven_four_of_seven_three (hrankThree 7)
    exact fun D _ => hplain D
  · intro hcover
    exact discriminantCovering_seven_iff_rank_three.mpr
      (gtzWeightedAll_three_of_pivotMinorCoveringFour_seven hcover)

/-- **The zero-margin obstruction is present at `(7,4)` too.**  The campaign's
`(7,3)` tie witness has a Naimark dual, and `Gtz.isTie_naimarkDual` carries the
DEFINITE verdict across, so the dual is an exact tie at `(7,4)`: some quadruple
dominates and none dominates strictly.  Any uniform-margin argument on the dual
side is dead for the same reason it is dead on the primal side. -/
theorem exists_isTie_seven_four : ∃ dual : WeightedDesign 7 4, IsTie dual := by
  obtain ⟨dual, -, htie⟩ :=
    isTie_naimarkDual (m := 7) (k := 3) (by norm_num) (by norm_num) splitSevenDesign
  exact ⟨dual, htie.mp splitSevenDesign_isTie⟩

end Gtz
