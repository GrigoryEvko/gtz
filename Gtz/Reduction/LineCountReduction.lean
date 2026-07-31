/-
# The line-count reduction, and the two `(7,3)` tie strata it swallows

`HasAtMostLines D lineCount` says the atoms of `D` occupy at most `lineCount` lines through
the origin: they are grouped into `lineCount` classes inside which any two are parallel.
Lengths and signs inside a class are unconstrained, so this is strictly weaker than being
a `Gtz.parallelSplitDesign`, whose classes carry EQUAL atoms.

The reduction transports weighted GTZ from the line count to every size.  Above
`lineCount` atoms, pigeonhole produces a parallel pair; `Gtz.mergedParallelDesign` removes
one atom without adding a line; `Gtz.exists_dominating_of_mergedParallel_dominates` lifts
the selection back.  Iterating lands at size `lineCount`.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `exists_dominating_of_hasAtMostLines` — the reduction itself, at every rank and size.
  This is the first ITERATED merge in the repository: the shipped
  `Gtz.dominating_of_parallel_pair` is one step, and is consumed only as a branch trigger.
* `exists_dominating_of_hasAtMostLines_rankAddTwo` and
  `exists_dominating_of_hasAtMostLines_five_rankThree` — because
  `Gtz.gtzWeighted_corank_two` is UNCONDITIONAL, `rank + 2` lines are free at every rank
  at least two and every size.  At rank three that is five lines, with no heaviness
  hypothesis, no open hypothesis and no size restriction.
* `gtzWeightedAll_three_of_hasAtMostLines_rankAddThree` — THE CEILING.  Raising the free
  line count by one, uniformly in the rank, PROVES `Gtz.GtzWeightedAll 3`.  So `rank + 2`
  is not an artifact of the merge; it is exactly the corank boundary, and no better
  uniform line bound exists below a full solution.  The merge ladder is finished.
* `exists_dominating_of_two_parallel_relations` and its two `(7,3)` corollaries — the
  criterion in purely local form, two sizes down through two merges.
* `hasAtMostLines_parallelSplitDesign`, `hasAtMostLines_splitClassDesign` — the two shipped
  presentations of split designs both land inside the predicate.
* `not_hasAtMostLines_four_sevenSplitDiamondDesign` and
  `exists_allHeavy_isTie_not_hasAtMostLines_four` — CONJECTURE C2 IS FALSE.  There is an
  all-heavy exact `(7,3)` tie whose atoms do not lie on four lines, hence is not a split
  simplex.  The closest shipped relative,
  `Gtz.not_eq_parallelSplitDesign_corankOne_sixSplitDiamondDesign`, runs the same
  pigeonhole one size down, over equal-atom classes only, and is not paired with
  all-heaviness.
* `sevenSplitDiamondDesign_allHeavy` — the second all-heavy `(7,3)` exact-tie witness in
  the repository; every earlier one is built on the tetrahedron primitive.

## NOT proved here

`GtzWeighted 7 3` and `GtzWeightedHeavy 7 3` remain open.  `gtzWeighted_seven_three_of_sixLines`
and `gtzWeightedHeavy_seven_three_of_sixLines` record the residual, they do not discharge
it, and the residual is the generic case: `HasAtMostLines D 5` at size seven is a
positive-codimension condition, so covering it buys nothing towards the frontier.  That
codimension reading is prose, not a theorem.

## Position

Filed under `Gtz/Reduction/` because it is a reduction, but it imports upward out of that
directory into `Gtz/Quantitative/` and `Gtz/Ties/` for the two shipped `(7,3)` tie strata
and the split-class family.  `Gtz/Reduction/AllHeavyMinimiser.lean`,
`Gtz/Reduction/ChartAttainmentWeld.lean` and `Gtz/Reduction/NaimarkLeverage.lean` already
do the same.

Provenance: the July 2026 scratch corpus, reports 11 (`deepen-tie`) and 16 (`tieclass`).
Report 16's own predicate and its own copies of the split designs were dropped in favour
of the stronger predicate here and the shipped `Gtz.sevenSplitDiamondDesign`.
-/
import Mathlib
import Gtz.Design.DiamondLeverage
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.RankFourWindow
import Gtz.Quantitative.DecisionAtlasSevenThree
import Gtz.Quantitative.ExtremalBasisActivity
import Gtz.Ties.SplitClassTieFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## The predicate -/

/-- The atoms of `D` occupy at most `lineCount` lines through the origin: some assignment
of labels to lines makes any two labels on a common line parallel. -/
def HasAtMostLines {size rank : ℕ} (D : WeightedDesign size rank) (lineCount : ℕ) : Prop :=
  ∃ lineOf : Fin size → Fin lineCount,
    ∀ leftLabel rightLabel : Fin size, lineOf leftLabel = lineOf rightLabel →
      ∃ ratio : ℝ, D.atom rightLabel = ratio • D.atom leftLabel

/-- Atoms written as nonzero multiples of a bank of `lineCount` directions. -/
theorem hasAtMostLines_of_directions {size rank lineCount : ℕ} (D : WeightedDesign size rank)
    (lineOf : Fin size → Fin lineCount) (direction : Fin lineCount → Fin rank → ℝ)
    (scale : Fin size → ℝ) (hscale : ∀ label, scale label ≠ 0)
    (hatom : ∀ label, D.atom label = scale label • direction (lineOf label)) :
    HasAtMostLines D lineCount := by
  refine ⟨lineOf, fun leftLabel rightLabel hsame => ?_⟩
  refine ⟨scale rightLabel / scale leftLabel, ?_⟩
  rw [hatom rightLabel, hatom leftLabel, ← hsame, smul_smul,
    div_mul_cancel₀ _ (hscale leftLabel)]

/-! ## The merge does not add a line -/

/-- The merged atom's squared scale is strictly positive, both weights being. -/
theorem mergeScaleSq_pos {weightKept weightDrop ratio : ℝ} (hkept : 0 < weightKept)
    (hdrop : 0 < weightDrop) : 0 < mergeScaleSq weightKept weightDrop ratio := by
  rw [mergeScaleSq]
  refine div_pos ?_ (by linarith)
  nlinarith [sq_nonneg ratio]

/-- **Every merged atom is a strictly POSITIVE multiple of the original atom over it.**
Away from the kept index the merge is a reindexing; at the kept index it rescales by
`sqrt (mergeScaleSq)`, positive because the kept weight is. -/
theorem mergedParallelDesign_atom_eq_posSmul {size rank : ℕ} (D : WeightedDesign (size + 1) rank)
    (keptLabel dropLabel : Fin (size + 1)) (ratio : ℝ) (keptIndex : Fin size)
    (hkeptIndex : dropLabel.succAbove keptIndex = keptLabel)
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel) (index : Fin size) :
    ∃ scale : ℝ, 0 < scale ∧
      (mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel).atom index
        = scale • D.atom (dropLabel.succAbove index) := by
  rcases eq_or_ne index keptIndex with hiskept | hisother
  · subst hiskept
    refine ⟨Real.sqrt (mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio),
      Real.sqrt_pos.mpr (mergeScaleSq_pos (D.weight_pos keptLabel) (D.weight_pos dropLabel)), ?_⟩
    rw [mergedParallelDesign_atom_kept, hkeptIndex]
  · exact ⟨1, one_pos, by
      rw [mergedParallelDesign_atom_of_ne D keptLabel dropLabel ratio hkeptIndex hparallel
        hisother, one_smul]⟩

/-- The merge removes an atom without adding a line: the surviving labels keep the line
assignment they had upstairs. -/
theorem hasAtMostLines_mergedParallelDesign {size rank lineCount : ℕ}
    (D : WeightedDesign (size + 1) rank) (keptLabel dropLabel : Fin (size + 1)) (ratio : ℝ)
    (keptIndex : Fin size) (hkeptIndex : dropLabel.succAbove keptIndex = keptLabel)
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel)
    (hlines : HasAtMostLines D lineCount) :
    HasAtMostLines (mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex
      hparallel) lineCount := by
  obtain ⟨lineOf, hparallelOnLine⟩ := hlines
  refine ⟨fun index => lineOf (dropLabel.succAbove index), fun leftIndex rightIndex hsame => ?_⟩
  obtain ⟨originalRatio, horiginal⟩ :=
    hparallelOnLine (dropLabel.succAbove leftIndex) (dropLabel.succAbove rightIndex) hsame
  obtain ⟨leftScale, hleftPos, hleft⟩ := mergedParallelDesign_atom_eq_posSmul D keptLabel
    dropLabel ratio keptIndex hkeptIndex hparallel leftIndex
  obtain ⟨rightScale, hrightPos, hright⟩ := mergedParallelDesign_atom_eq_posSmul D keptLabel
    dropLabel ratio keptIndex hkeptIndex hparallel rightIndex
  refine ⟨rightScale * originalRatio / leftScale, ?_⟩
  rw [hright, horiginal, hleft, smul_smul, smul_smul, div_mul_cancel₀ _ hleftPos.ne']

/-! ## The reduction -/

/-- **THE LINE-COUNT REDUCTION.**  If weighted GTZ holds at size `lineCount`, then at
EVERY size a design whose atoms occupy at most `lineCount` lines has a dominating
`rank`-subset.  The induction merges one parallel pair per step, which pigeonhole supplies
as long as the size exceeds the line count. -/
theorem exists_dominating_of_hasAtMostLines {rank lineCount : ℕ}
    (hbase : GtzWeighted lineCount rank) :
    ∀ (size : ℕ) (D : WeightedDesign size rank), HasAtMostLines D lineCount →
      ∃ C : Finset (Fin size), C.card = rank ∧ Dominates D C := by
  intro size
  induction size with
  | zero => exact fun D _ => gtzWeighted_of_le (Nat.zero_le _) hbase D
  | succ prevSize ih =>
    intro D hlines
    by_cases hsmall : prevSize + 1 ≤ lineCount
    · exact gtzWeighted_of_le hsmall hbase D
    · obtain ⟨lineOf, hparallelOnLine⟩ := hlines
      have hnotInjective : ¬ Function.Injective lineOf := by
        intro hinjective
        have hcard := Fintype.card_le_of_injective lineOf hinjective
        simp only [Fintype.card_fin] at hcard
        omega
      obtain ⟨keptLabel, dropLabel, hsameLine, hdistinct⟩ :=
        Function.not_injective_iff.mp hnotInjective
      obtain ⟨ratio, hparallel⟩ := hparallelOnLine keptLabel dropLabel hsameLine
      obtain ⟨keptIndex, hkeptIndex⟩ := Fin.exists_succAbove_eq hdistinct
      obtain ⟨mergedSubset, hmergedCard, hmergedDominates⟩ :=
        ih (mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel)
          (hasAtMostLines_mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex
            hparallel ⟨lineOf, hparallelOnLine⟩)
      obtain ⟨C, hcard, hdominates⟩ := exists_dominating_of_mergedParallel_dominates D keptLabel
        dropLabel ratio keptIndex hkeptIndex hparallel hmergedDominates
      exact ⟨C, by rw [hcard, hmergedCard], hdominates⟩

/-- **`rank + 2` lines are free, at every rank at least two and every size** — the base is
the unconditional `Gtz.gtzWeighted_corank_two`. -/
theorem exists_dominating_of_hasAtMostLines_rankAddTwo {rank : ℕ} (hrank : 2 ≤ rank) (size : ℕ)
    (D : WeightedDesign size rank) (hlines : HasAtMostLines D (rank + 2)) :
    ∃ C : Finset (Fin size), C.card = rank ∧ Dominates D C :=
  exists_dominating_of_hasAtMostLines (gtzWeighted_corank_two rank hrank) size D hlines

/-- **At rank three, five lines are free at every size** — no heaviness hypothesis, no
open hypothesis, no size restriction. -/
theorem exists_dominating_of_hasAtMostLines_five_rankThree (size : ℕ) (D : WeightedDesign size 3)
    (hlines : HasAtMostLines D 5) : ∃ C : Finset (Fin size), C.card = 3 ∧ Dominates D C :=
  exists_dominating_of_hasAtMostLines_rankAddTwo (by norm_num) size D hlines

/-! ## The ceiling: `rank + 3` lines is the whole conjecture -/

/-- **THE CEILING.**  Raising the free line count from `rank + 2` to `rank + 3`, uniformly
in the rank, PROVES the conjecture at rank three: at size `rank + 3` the identity
assignment witnesses `HasAtMostLines D (rank + 3)`, so the strengthened bound IS
`GtzWeighted (rank + 3) rank` for every rank, which
`Gtz.gtzWeightedAll_three_of_corank_three` converts into `GtzWeightedAll 3`.

So `rank + 2` is not an artifact of the merge — it is exactly the corank boundary, and no
better uniform line bound exists below a full solution.  The merge ladder is finished, and
a later attempt at a six-line bound at rank three would be an attempt at the conjecture. -/
theorem gtzWeightedAll_three_of_hasAtMostLines_rankAddThree
    (hlineBound : ∀ (rank : ℕ), 1 ≤ rank → ∀ (size : ℕ) (D : WeightedDesign size rank),
      HasAtMostLines D (rank + 3) → ∃ C : Finset (Fin size), C.card = rank ∧ Dominates D C) :
    GtzWeightedAll 3 := by
  refine gtzWeightedAll_three_of_corank_three fun rank hrank D => ?_
  exact hlineBound rank hrank (rank + 3) D ⟨id, fun leftLabel rightLabel hsame => by
    rw [show rightLabel = leftLabel from hsame.symm]
    exact ⟨1, (one_smul ℝ _).symm⟩⟩

/-! ## The residual at `(7,3)`

These two record what the reduction leaves open; they discharge nothing.  The residual is
the generic case, the line condition being a positive-codimension one. -/

theorem gtzWeighted_seven_three_of_sixLines
    (hresidual : ∀ D : WeightedDesign 7 3, ¬ HasAtMostLines D 5 →
      ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C) :
    GtzWeighted 7 3 := by
  intro D
  by_cases hlines : HasAtMostLines D 5
  · exact exists_dominating_of_hasAtMostLines_five_rankThree 7 D hlines
  · exact hresidual D hlines

theorem gtzWeightedHeavy_seven_three_of_sixLines
    (hresidual : ∀ D : WeightedDesign 7 3, AllHeavy D → ¬ HasAtMostLines D 5 →
      ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C) :
    GtzWeightedHeavy 7 3 := by
  intro D hheavy
  by_cases hlines : HasAtMostLines D 5
  · exact exists_dominating_of_hasAtMostLines_five_rankThree 7 D hlines
  · exact hresidual D hheavy hlines

/-! ## The criterion made checkable: two parallel collisions

The line count is a global condition; these theorems replace it by a purely local one, and
go through two merges directly rather than through `HasAtMostLines`. -/

/-- A second parallel relation survives the first merge whenever both of its labels avoid
the dropped one. -/
theorem hasParallelPair_mergedParallelDesign {size rank : ℕ} (D : WeightedDesign (size + 1) rank)
    {keptLabel dropLabel : Fin (size + 1)} {ratio : ℝ} (keptIndex : Fin size)
    (hkeptIndex : dropLabel.succAbove keptIndex = keptLabel)
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel)
    {keptOther dropOther : Fin (size + 1)} {ratioOther : ℝ}
    (hkeptOtherSurvives : keptOther ≠ dropLabel) (hdropOtherSurvives : dropOther ≠ dropLabel)
    (hotherDistinct : keptOther ≠ dropOther)
    (hparallelOther : D.atom dropOther = ratioOther • D.atom keptOther) :
    HasParallelPair (mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex
      hparallel) := by
  obtain ⟨keptOtherIndex, hkeptOtherIndex⟩ := Fin.exists_succAbove_eq hkeptOtherSurvives
  obtain ⟨dropOtherIndex, hdropOtherIndex⟩ := Fin.exists_succAbove_eq hdropOtherSurvives
  have hindexDistinct : keptOtherIndex ≠ dropOtherIndex := by
    intro hsame
    exact hotherDistinct (by rw [← hkeptOtherIndex, ← hdropOtherIndex, hsame])
  obtain ⟨keptScale, hkeptScalePos, hkeptScale⟩ := mergedParallelDesign_atom_eq_posSmul D
    keptLabel dropLabel ratio keptIndex hkeptIndex hparallel keptOtherIndex
  obtain ⟨dropScale, hdropScalePos, hdropScale⟩ := mergedParallelDesign_atom_eq_posSmul D
    keptLabel dropLabel ratio keptIndex hkeptIndex hparallel dropOtherIndex
  refine ⟨keptOtherIndex, dropOtherIndex, dropScale * ratioOther / keptScale, hindexDistinct, ?_⟩
  rw [hdropScale, hdropOtherIndex, hparallelOther, hkeptScale, hkeptOtherIndex, smul_smul,
    smul_smul, div_mul_cancel₀ _ hkeptScalePos.ne']

/-- **TWO INDEPENDENT PARALLEL RELATIONS SUFFICE**, landing two sizes down rather than
one. -/
theorem exists_dominating_of_two_parallel_relations {size rank : ℕ}
    (hbase : GtzWeighted size rank) (D : WeightedDesign (size + 2) rank)
    {keptOne dropOne keptTwo dropTwo : Fin (size + 2)} {ratioOne ratioTwo : ℝ}
    (hdistinctOne : keptOne ≠ dropOne)
    (hparallelOne : D.atom dropOne = ratioOne • D.atom keptOne)
    (hkeptTwoSurvives : keptTwo ≠ dropOne) (hdropTwoSurvives : dropTwo ≠ dropOne)
    (hdistinctTwo : keptTwo ≠ dropTwo)
    (hparallelTwo : D.atom dropTwo = ratioTwo • D.atom keptTwo) :
    ∃ C : Finset (Fin (size + 2)), C.card = rank ∧ Dominates D C := by
  obtain ⟨keptIndexOne, hkeptIndexOne⟩ := Fin.exists_succAbove_eq hdistinctOne
  obtain ⟨mergedKept, mergedDrop, mergedRatio, mergedDistinct, mergedParallel⟩ :=
    hasParallelPair_mergedParallelDesign D keptIndexOne hkeptIndexOne hparallelOne
      hkeptTwoSurvives hdropTwoSurvives hdistinctTwo hparallelTwo
  obtain ⟨innerSubset, hinnerCard, hinnerDominates⟩ :=
    dominating_of_parallel_pair
      (mergedParallelDesign D keptOne dropOne ratioOne keptIndexOne hkeptIndexOne hparallelOne)
      hbase mergedDistinct mergedParallel
  obtain ⟨C, hcard, hdominates⟩ := exists_dominating_of_mergedParallel_dominates D keptOne
    dropOne ratioOne keptIndexOne hkeptIndexOne hparallelOne hinnerDominates
  exact ⟨C, by rw [hcard, hinnerCard], hdominates⟩

/-- **Two disjoint parallel pairs at `(7,3)`.**  The two `keptOne`-hypotheses one might
expect are genuinely unnecessary: only the dropped label of the first pair must avoid the
second pair. -/
theorem exists_dominating_sevenThree_of_two_disjoint_parallel_pairs (D : WeightedDesign 7 3)
    {keptOne dropOne keptTwo dropTwo : Fin 7} {ratioOne ratioTwo : ℝ}
    (hkeptOneDropOne : keptOne ≠ dropOne) (hdropOneKeptTwo : dropOne ≠ keptTwo)
    (hdropOneDropTwo : dropOne ≠ dropTwo) (hkeptTwoDropTwo : keptTwo ≠ dropTwo)
    (hparallelOne : D.atom dropOne = ratioOne • D.atom keptOne)
    (hparallelTwo : D.atom dropTwo = ratioTwo • D.atom keptTwo) :
    ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C :=
  exists_dominating_of_two_parallel_relations (gtzWeighted_corank_two 3 (by norm_num)) D
    hkeptOneDropOne hparallelOne (Ne.symm hdropOneKeptTwo) (Ne.symm hdropOneDropTwo)
    hkeptTwoDropTwo hparallelTwo

/-- **A parallel triple at `(7,3)`** — three atoms on one line. -/
theorem exists_dominating_sevenThree_of_parallel_triple (D : WeightedDesign 7 3)
    {pivot first second : Fin 7} {ratioFirst ratioSecond : ℝ}
    (hpivotFirst : pivot ≠ first) (hpivotSecond : pivot ≠ second) (hfirstSecond : first ≠ second)
    (hparallelFirst : D.atom first = ratioFirst • D.atom pivot)
    (hparallelSecond : D.atom second = ratioSecond • D.atom pivot) :
    ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C :=
  exists_dominating_of_two_parallel_relations (gtzWeighted_corank_two 3 (by norm_num)) D
    hpivotFirst hparallelFirst hpivotFirst (Ne.symm hfirstSecond) hpivotSecond hparallelSecond

/-! ## Where the shipped split families sit -/

/-- **Every parallel splitting occupies at most as many lines as its base has atoms.**
`Gtz.parallelSplitDesign` is the special case in which the atoms of a class are EQUAL;
`HasAtMostLines` also admits classes of differing lengths and signs. -/
theorem hasAtMostLines_parallelSplitDesign {baseSize splitSize rank : ℕ}
    (base : WeightedDesign baseSize rank) (classOf : Fin splitSize → Fin baseSize)
    (weight : Fin splitSize → ℝ) (hsplit : IsParallelSplitting base classOf weight) :
    HasAtMostLines (parallelSplitDesign base classOf weight hsplit) baseSize :=
  hasAtMostLines_of_directions _ classOf base.atom (fun _ => 1) (fun _ => one_ne_zero)
    fun label => by rw [parallelSplitDesign_atom, one_smul]

/-- **Every split simplex occupies at most `rank + 1` lines.**  This is the half of the C2
refutation that says what a split simplex looks like; the other half exhibits an all-heavy
tie that fails it. -/
theorem hasAtMostLines_splitClassDesign {size rank : ℕ} (classOf : Fin size → Fin (rank + 1))
    (weight : Fin size → ℝ) (hrank : 1 ≤ rank) (hsurjective : Function.Surjective classOf)
    (hpos : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1) :
    HasAtMostLines (splitClassDesign classOf weight hrank hsurjective hpos hsum) (rank + 1) :=
  hasAtMostLines_of_directions _ classOf (simplexTieAtom (classTotalWeight classOf weight))
    (fun _ => 1) (fun _ => one_ne_zero) fun label => by rw [splitClassDesign_atom, one_smul]

/-! ## The `(7,3)` diamond tie stratum -/

/-- The five diamond directions sit inside the `(7,3)` split at the doubly-cast labels:
`Gtz.sevenIntoFiveDiamond` is `![0, 1, 2, 3, 4, 0, 1]`, so the first five labels enumerate
the classes. -/
theorem sevenIntoFiveDiamond_castSucc_castSucc (edge : Fin 5) :
    sevenIntoFiveDiamond edge.castSucc.castSucc = edge := by
  fin_cases edge <;> rfl

theorem sevenSplitDiamondDesign_atom_castSucc_castSucc (edge : Fin 5) :
    sevenSplitDiamondDesign.atom edge.castSucc.castSucc = diamondDesign.atom edge := by
  rw [sevenSplitDiamondDesign, parallelSplitDesign_atom,
    sevenIntoFiveDiamond_castSucc_castSucc]

/-- **The `(7,3)` diamond split is ALL-HEAVY.**  Every one of its atoms is a diamond atom,
and `Gtz.diamondDesign_allHeavy` says those are heavy.  This is the second all-heavy
`(7,3)` exact-tie witness in the repository; the earlier ones
(`Gtz.splitSevenDesign_allHeavy`, `Gtz.splitSevenReweighted_allHeavy`,
`Gtz.graphicKFourSevenDesign_allHeavy`) are all built on the tetrahedron. -/
theorem sevenSplitDiamondDesign_allHeavy : AllHeavy sevenSplitDiamondDesign := by
  intro label
  rw [sevenSplitDiamondDesign, parallelSplitDesign_atom]
  exact diamondDesign_allHeavy _

/-- **The `(7,3)` diamond split does NOT occupy four lines.**  Five of its atoms are the
diamond's, which are pairwise non-parallel
(`Gtz.not_hasParallelPair_diamondDesign`); four lines cannot hold five pairwise
non-parallel vectors.  Unlike the shipped
`Gtz.not_eq_parallelSplitDesign_corankOne_sixSplitDiamondDesign`, which runs the same
pigeonhole one size down over EQUAL-atom classes, this covers arbitrary parallel
rescaling, sign included. -/
theorem not_hasAtMostLines_four_sevenSplitDiamondDesign :
    ¬ HasAtMostLines sevenSplitDiamondDesign 4 := by
  rintro ⟨lineOf, hparallelOnLine⟩
  have hnotInjective :
      ¬ Function.Injective (fun edge : Fin 5 => lineOf edge.castSucc.castSucc) := by
    intro hinjective
    have hcard := Fintype.card_le_of_injective _ hinjective
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨edgeLeft, edgeRight, hsameLine, hdistinct⟩ :=
    Function.not_injective_iff.mp hnotInjective
  obtain ⟨ratio, hratio⟩ := hparallelOnLine edgeLeft.castSucc.castSucc
    edgeRight.castSucc.castSucc hsameLine
  rw [sevenSplitDiamondDesign_atom_castSucc_castSucc,
    sevenSplitDiamondDesign_atom_castSucc_castSucc] at hratio
  exact not_hasParallelPair_diamondDesign ⟨edgeLeft, edgeRight, ratio, hdistinct, hratio⟩

/-- **CONJECTURE C2 IS FALSE.**  There is an all-heavy exact `(7,3)` tie whose atoms do not
lie on four lines, so it is NOT a split simplex — every split simplex does, by
`hasAtMostLines_splitClassDesign` at `rank = 3`.

What is new is the kernel-checked all-heaviness and the line separation, not the discovery
of the `(7,3)` diamond tie classes: their existence is already asserted as measured prose
in the `Gtz/Ties/DiamondTie.lean` header, and the design itself is the shipped
`Gtz.sevenSplitDiamondDesign`. -/
theorem exists_allHeavy_isTie_not_hasAtMostLines_four :
    ∃ D : WeightedDesign 7 3, AllHeavy D ∧ IsTie D ∧ ¬ HasAtMostLines D 4 :=
  ⟨sevenSplitDiamondDesign, sevenSplitDiamondDesign_allHeavy, sevenSplitDiamondDesign_isTie,
    not_hasAtMostLines_four_sevenSplitDiamondDesign⟩

/-- **The diamond stratum sits on exactly five lines** — at most five by the splitting, and
not four by the previous theorem. -/
theorem hasAtMostLines_sevenSplitDiamondDesign : HasAtMostLines sevenSplitDiamondDesign 5 :=
  hasAtMostLines_parallelSplitDesign diamondDesign sevenIntoFiveDiamond sevenSplitDiamondWeight
    sevenSplitDiamond_isParallelSplitting

/-! ## The `(7,3)` split-tetrahedron stratum -/

/-- The split-tetrahedron leverage slice: arbitrary NONZERO scales on the four tetrahedron
directions, so not a parallel splitting.  Four lines. -/
theorem hasAtMostLines_tetraScaled (D : WeightedDesign 7 3) (scale : Fin 7 → ℝ)
    (hscale : ∀ label, scale label ≠ 0)
    (hatom : ∀ label, D.atom label = scale label • tetraAtom (splitSevenDirection label)) :
    HasAtMostLines D 4 :=
  hasAtMostLines_of_directions D splitSevenDirection tetraAtom scale hscale hatom

/-- **The tetrahedron slice, with the heaviness hypothesis DELETED**, the positivity of the
scales weakened to nonvanishing, and the base lowered to corank one. -/
theorem exists_dominating_of_tetraScaled (D : WeightedDesign 7 3) (scale : Fin 7 → ℝ)
    (hscale : ∀ label, scale label ≠ 0)
    (hatom : ∀ label, D.atom label = scale label • tetraAtom (splitSevenDirection label)) :
    ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C :=
  exists_dominating_of_hasAtMostLines (gtzWeighted_corank_one 3 (by norm_num)) 7 D
    (hasAtMostLines_tetraScaled D scale hscale hatom)

theorem hasAtMostLines_splitSevenDesign : HasAtMostLines splitSevenDesign 4 :=
  hasAtMostLines_tetraScaled splitSevenDesign (fun _ => 1) (fun _ => one_ne_zero)
    fun label => by rw [splitSevenDesign_atom, one_smul]

/-- **BOTH SHIPPED `(7,3)` TIE STRATA ARE REACHED UNCONDITIONALLY.**  The split tetrahedron
occupies four lines, the diamond class five.

The domination halves are NOT new: they are the `.1` projections of the shipped
`Gtz.splitSevenDesign_isTie` and `Gtz.sevenSplitDiamondDesign_isTie`.  What is new is the
two line counts, and the fact that an UNCONDITIONAL route reaches the same conclusion —
the tree's own `(7,3)` merge branch, `Gtz.gtzWeightedSeven_of_branches`, is gated on the
open `GtzWeighted 6 3`, whereas this route bottoms out at corank one and corank two, both
theorems.  Neither stratum is therefore an obstruction, and neither is evidence about the
frontier: the line condition is a positive-codimension one. -/
theorem both_sevenThree_tieStrata_are_free :
    (HasAtMostLines splitSevenDesign 4 ∧
      ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates splitSevenDesign C)
    ∧ (HasAtMostLines sevenSplitDiamondDesign 5 ∧
      ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates sevenSplitDiamondDesign C) :=
  ⟨⟨hasAtMostLines_splitSevenDesign,
      exists_dominating_of_hasAtMostLines (gtzWeighted_corank_one 3 (by norm_num)) 7
        splitSevenDesign hasAtMostLines_splitSevenDesign⟩,
    ⟨hasAtMostLines_sevenSplitDiamondDesign,
      exists_dominating_of_hasAtMostLines_five_rankThree 7 sevenSplitDiamondDesign
        hasAtMostLines_sevenSplitDiamondDesign⟩⟩

end Gtz
