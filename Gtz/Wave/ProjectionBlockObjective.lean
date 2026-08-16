import Gtz.Quantitative.ProjectionBasisCoordinates
import Gtz.Wave.ChartDesignGauge

/-!
# The objective in projection coordinates, and the heavy set that carries it

`Gtz.ConsolidatedStrictTripleDesign` implies all five on-path obligations
(`Gtz.allFiveOnPath_of_consolidatedStrictTripleDesign`).  This file restates it
with no atom, no Gram and no `subsetSum`, and then reads the restatement.

## The restatement

`Gtz.posDef_subsetSum_iff_posDef_projectionBlock` decides strict domination at
selection size equal to the rank, indexed by an injective `pick`.  The objective
quantifies over a `Finset`, so the `Finset`-indexed form is what is needed, and
it is the strict companion of the landed semidefinite
`Gtz.fieldDominates_iff_posSemidef_chartBlock_finset`.  With it,
`Gtz.consolidatedStrictTripleDesign_iff_projectionBlockSelects` says the
objective is

  every primitive design carries a card-three `C` with `P[C] ≻ diag w_C`.

## The heavy set

`P` is a symmetric idempotent of trace `rank`, so its diagonal is nonnegative,
below one, and totals the rank, while the weights total one.  The excess
`P_cc − w_c` therefore totals `rank − 1`, and each excess is at most `1 − w_c`.
Pigeonhole on that gives **at least `rank` labels of strictly positive excess**
(`Gtz.rank_le_card_heavyLabels`), which is new: the corpus carried the necessity
half — every member of a strict dominator is strictly heavy — with no existence
half beside it.

The two halves compose.  A strict dominator is a card-`rank` subset of the heavy
set, and the heavy set has at least `rank` elements, so when it has exactly
`rank` the dominator **is** the heavy set
(`Gtz.eq_heavyLabels_of_posDef_of_card_eq`).  At such a design the objective is
not a search over the twenty triples: one explicit block decides it, in both
directions (`Gtz.projectionBlockSelects_at_of_card_heavyLabels_eq`).
-/

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## 1. The block gap and the `Finset`-indexed decision -/

/-- **THE PROJECTION BLOCK GAP.**  `P[C] − diag w_C`, read along the selection's
order embedding.  Division-free: no inverse, no root, no eigenvalue. -/
noncomputable def projectionBlockGap (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) :
    Matrix (Fin rank) (Fin rank) ℝ :=
  (projectionOfDesign design).submatrix (selected.orderEmbOfFin hcard)
      (selected.orderEmbOfFin hcard)
    - Matrix.diagonal (fun slot => design.weight (selected.orderEmbOfFin hcard slot))

theorem projectionBlockGap_apply (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) (left right : Fin rank) :
    projectionBlockGap design selected hcard left right
      = projectionOfDesign design (selected.orderEmbOfFin hcard left)
          (selected.orderEmbOfFin hcard right)
        - (if left = right then design.weight (selected.orderEmbOfFin hcard left) else 0) := by
  rw [projectionBlockGap]
  rcases eq_or_ne left right with rfl | hne
  · simp [Matrix.diagonal_apply_eq]
  · simp [hne]

/-- The diagonal of the block gap is the label's leverage excess. -/
theorem projectionBlockGap_diag (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) (slot : Fin rank) :
    projectionBlockGap design selected hcard slot slot
      = projectionOfDesign design (selected.orderEmbOfFin hcard slot)
          (selected.orderEmbOfFin hcard slot)
        - design.weight (selected.orderEmbOfFin hcard slot) := by
  rw [projectionBlockGap_apply, if_pos rfl]

/-- **STRICT DOMINATION IS THE BLOCK INEQUALITY, INDEXED BY THE SUBSET.**  The
landed `Gtz.posDef_subsetSum_iff_posDef_projectionBlock` is stated for an
injective `pick`.  The objective quantifies over a `Finset`, and this is that
form. -/
theorem posDef_subsetSum_iff_projectionBlockGap (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) :
    (subsetSum design selected - 1).PosDef
      ↔ (projectionBlockGap design selected hcard).PosDef := by
  rw [projectionBlockGap]
  conv_lhs => rw [← image_orderEmbOfFin hcard]
  exact posDef_subsetSum_iff_posDef_projectionBlock design _
    (selected.orderEmbOfFin hcard).injective

/-! ## 2. The objective, restated -/

/-- **THE OBJECTIVE IN PROJECTION COORDINATES.**  Every primitive design carries
a card-three selection whose projection block strictly dominates its weight
diagonal.  No atom, no Gram, no `subsetSum`, no matrix square root. -/
def ProjectionBlockSelects : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
      (projectionBlockGap design selected hcard).PosDef

/-- **THE RESTATEMENT.**  The consolidated design statement and the projection
block statement are the same statement. -/
theorem consolidatedStrictTripleDesign_iff_projectionBlockSelects :
    ConsolidatedStrictTripleDesign ↔ ProjectionBlockSelects := by
  constructor
  · intro hdesign design hprimitive
    obtain ⟨selected, hcard, hposDef⟩ := hdesign design hprimitive
    exact ⟨selected, hcard,
      (posDef_subsetSum_iff_projectionBlockGap design selected hcard).mp hposDef⟩
  · intro hblock design hprimitive
    obtain ⟨selected, hcard, hposDef⟩ := hblock design hprimitive
    exact ⟨selected, hcard,
      (posDef_subsetSum_iff_projectionBlockGap design selected hcard).mpr hposDef⟩

/-- **THE PROJECTION BLOCK STATEMENT RETIRES ALL FIVE ON-PATH OBLIGATIONS.** -/
theorem allFiveOnPath_of_projectionBlockSelects (hblock : ProjectionBlockSelects) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  allFiveOnPath_of_consolidatedStrictTripleDesign
    (consolidatedStrictTripleDesign_iff_projectionBlockSelects.mpr hblock)

/-- The chart form follows too, through the landed gauge equivalence. -/
theorem consolidatedStrictTriple_of_projectionBlockSelects
    (hblock : ProjectionBlockSelects) : ConsolidatedStrictTriple :=
  consolidatedStrictTriple_iff_consolidatedStrictTripleDesign.mpr
    (consolidatedStrictTripleDesign_iff_projectionBlockSelects.mpr hblock)

/-! ## 3. The diagonal is majorized by the spectrum -/

/-- The projection diagonal never exceeds one — the landed generic chart bound
`Gtz.chart_diag_le_one` fed the projection's symmetry and idempotence. -/
theorem projectionDiagonal_le_one' (design : WeightedDesign size rank)
    (atomIndex : Fin size) : projectionOfDesign design atomIndex atomIndex ≤ 1 :=
  chart_diag_le_one (projectionOfDesign_transpose design)
    (projectionOfDesign_mul_self design) atomIndex

/-- The projection diagonal is nonnegative: a weight times a squared length. -/
theorem projectionOfDesign_diagonal_nonneg (design : WeightedDesign size rank)
    (atomIndex : Fin size) : 0 ≤ projectionOfDesign design atomIndex atomIndex := by
  rw [projectionOfDesign_diagonal]
  exact mul_nonneg (design.weight_pos atomIndex).le (leverageOf_nonneg _)

/-- The whole projection diagonal totals the rank. -/
theorem sum_projectionDiagonal (design : WeightedDesign size rank) :
    ∑ atomIndex, projectionOfDesign design atomIndex atomIndex = (rank : ℝ) := by
  have htrace := trace_projectionOfDesign design
  rwa [Matrix.trace] at htrace

/-- **THE SUBSET DIAGONAL IS BELOW THE SUBSET SIZE.**  Each diagonal entry of a
projection is at most one, so a subset of them totals at most its cardinality. -/
theorem sum_projectionDiagonal_le_card (design : WeightedDesign size rank)
    (chosen : Finset (Fin size)) :
    ∑ atomIndex ∈ chosen, projectionOfDesign design atomIndex atomIndex
      ≤ (chosen.card : ℝ) := by
  calc ∑ atomIndex ∈ chosen, projectionOfDesign design atomIndex atomIndex
      ≤ ∑ _atomIndex ∈ chosen, (1 : ℝ) :=
        Finset.sum_le_sum fun atomIndex _ => projectionDiagonal_le_one' design atomIndex
    _ = (chosen.card : ℝ) := by simp

/-- **THE SUBSET DIAGONAL IS BELOW THE RANK.**  The whole diagonal totals the
rank and every entry is nonnegative. -/
theorem sum_projectionDiagonal_le_rank (design : WeightedDesign size rank)
    (chosen : Finset (Fin size)) :
    ∑ atomIndex ∈ chosen, projectionOfDesign design atomIndex atomIndex ≤ (rank : ℝ) := by
  calc ∑ atomIndex ∈ chosen, projectionOfDesign design atomIndex atomIndex
      ≤ ∑ atomIndex, projectionOfDesign design atomIndex atomIndex :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ chosen)
          fun atomIndex _ _ => projectionOfDesign_diagonal_nonneg design atomIndex
    _ = (rank : ℝ) := sum_projectionDiagonal design

/-- **THE MAJORIZATION BOUND.**  A subset of the projection diagonal totals at
most the smaller of its own size and the rank.  Both halves are elementary once
the diagonal is nonnegative, below one, and totals the rank, so the sorted
partial-sum form of majorization needs no Schur-Horn theorem here. -/
theorem sum_projectionDiagonal_le_min (design : WeightedDesign size rank)
    (chosen : Finset (Fin size)) :
    ∑ atomIndex ∈ chosen, projectionOfDesign design atomIndex atomIndex
      ≤ min (chosen.card : ℝ) (rank : ℝ) :=
  le_min (sum_projectionDiagonal_le_card design chosen)
    (sum_projectionDiagonal_le_rank design chosen)

/-- The complementary reading: a subset leaves at least the rank minus its own
size behind. -/
theorem rank_sub_card_le_sum_projectionDiagonal_compl (design : WeightedDesign size rank)
    (chosen : Finset (Fin size)) :
    (rank : ℝ) - (chosen.card : ℝ)
      ≤ ∑ atomIndex ∈ chosenᶜ, projectionOfDesign design atomIndex atomIndex := by
  have hsplit : (∑ atomIndex ∈ chosen, projectionOfDesign design atomIndex atomIndex)
      + ∑ atomIndex ∈ chosenᶜ, projectionOfDesign design atomIndex atomIndex = (rank : ℝ) := by
    rw [Finset.sum_add_sum_compl]
    exact sum_projectionDiagonal design
  have hcard := sum_projectionDiagonal_le_card design chosen
  linarith

/-! ## 4. The heavy set -/

/-- **THE HEAVY SET.**  The labels whose projection diagonal strictly exceeds
their weight.  Equivalently, by `Gtz.projectionOfDesign_diagonal`, the labels of
leverage strictly above one. -/
noncomputable def heavyLabels (design : WeightedDesign size rank) : Finset (Fin size) :=
  Finset.univ.filter fun atomIndex =>
    design.weight atomIndex < projectionOfDesign design atomIndex atomIndex

theorem mem_heavyLabels_iff (design : WeightedDesign size rank) (atomIndex : Fin size) :
    atomIndex ∈ heavyLabels design
      ↔ design.weight atomIndex < projectionOfDesign design atomIndex atomIndex := by
  rw [heavyLabels, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ atomIndex, h⟩⟩

/-- Heaviness in leverage vocabulary: the diagonal beats the weight exactly when
the leverage beats one. -/
theorem mem_heavyLabels_iff_one_lt_leverage (design : WeightedDesign size rank)
    (atomIndex : Fin size) :
    atomIndex ∈ heavyLabels design ↔ 1 < leverageOf (design.atom atomIndex) := by
  rw [mem_heavyLabels_iff, projectionOfDesign_diagonal]
  constructor
  · intro h
    nlinarith [design.weight_pos atomIndex]
  · intro h
    nlinarith [design.weight_pos atomIndex]

/-- The total leverage excess is the rank minus one: the diagonal totals the rank
and the weights total one. -/
theorem sum_leverageExcess (design : WeightedDesign size rank) :
    ∑ atomIndex, (projectionOfDesign design atomIndex atomIndex - design.weight atomIndex)
      = (rank : ℝ) - 1 := by
  rw [Finset.sum_sub_distrib, sum_projectionDiagonal design, design.weight_sum_one]

/-- **AT LEAST `rank` LABELS ARE STRICTLY HEAVY.**

The excesses total `rank − 1`.  Off the heavy set every excess is at most zero,
and on it every excess is at most `1 − w_c`, because the projection diagonal
never exceeds one.  So `rank − 1 ≤ k − ∑_{heavy} w_c` with `k` the heavy count,
and the heavy set is nonempty once the rank is at least two, which makes that
weight sum strictly positive.  Hence `rank − 1 < k`.

This is the existence half that the landed leverage floor
(`Gtz.one_lt_leverage_of_posDef`, necessity) had no companion for. -/
theorem rank_le_card_heavyLabels (design : WeightedDesign size rank) (hrank : 2 ≤ rank) :
    rank ≤ (heavyLabels design).card := by
  classical
  set excess : Fin size → ℝ := fun atomIndex =>
    projectionOfDesign design atomIndex atomIndex - design.weight atomIndex with hexcess
  have htotal : ∑ atomIndex, excess atomIndex = (rank : ℝ) - 1 := sum_leverageExcess design
  have hoff : ∀ atomIndex ∈ (heavyLabels design)ᶜ, excess atomIndex ≤ 0 := by
    intro atomIndex hmem
    rw [Finset.mem_compl, mem_heavyLabels_iff, not_lt] at hmem
    simp only [hexcess]
    linarith
  have hon : ∀ atomIndex ∈ heavyLabels design,
      excess atomIndex ≤ 1 - design.weight atomIndex := by
    intro atomIndex _
    have := projectionDiagonal_le_one' design atomIndex
    simp only [hexcess]
    linarith
  have hsplit : (∑ atomIndex ∈ heavyLabels design, excess atomIndex)
      + ∑ atomIndex ∈ (heavyLabels design)ᶜ, excess atomIndex = (rank : ℝ) - 1 := by
    rw [Finset.sum_add_sum_compl]
    exact htotal
  have hoffsum : ∑ atomIndex ∈ (heavyLabels design)ᶜ, excess atomIndex ≤ 0 :=
    Finset.sum_nonpos hoff
  have honsum : ∑ atomIndex ∈ heavyLabels design, excess atomIndex
      ≤ ((heavyLabels design).card : ℝ)
        - ∑ atomIndex ∈ heavyLabels design, design.weight atomIndex := by
    calc ∑ atomIndex ∈ heavyLabels design, excess atomIndex
        ≤ ∑ atomIndex ∈ heavyLabels design, (1 - design.weight atomIndex) :=
          Finset.sum_le_sum hon
      _ = ((heavyLabels design).card : ℝ)
            - ∑ atomIndex ∈ heavyLabels design, design.weight atomIndex := by
          rw [Finset.sum_sub_distrib]
          simp
  -- the heavy set is nonempty, so its weight total is strictly positive
  have hrankreal : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  have hne : (heavyLabels design).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (heavyLabels design) with hempty | hne
    · exfalso
      have hall : ∀ atomIndex ∈ (Finset.univ : Finset (Fin size)), excess atomIndex ≤ 0 := by
        intro atomIndex _
        refine hoff atomIndex ?_
        rw [hempty]
        simp
      have hnp := Finset.sum_nonpos hall
      rw [htotal] at hnp
      linarith
    · exact hne
  have hwpos : 0 < ∑ atomIndex ∈ heavyLabels design, design.weight atomIndex :=
    Finset.sum_pos (fun atomIndex _ => design.weight_pos atomIndex) hne
  have hstrict : (rank : ℝ) - 1 < ((heavyLabels design).card : ℝ) := by linarith
  have hfinal : (rank : ℝ) ≤ ((heavyLabels design).card : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hlt : ((heavyLabels design).card : ℕ) < rank := by exact_mod_cast hcon
    have : ((heavyLabels design).card : ℝ) ≤ (rank : ℝ) - 1 := by
      have : ((heavyLabels design).card : ℕ) + 1 ≤ rank := hlt
      have hcast : (((heavyLabels design).card : ℕ) : ℝ) + 1 ≤ (rank : ℝ) := by exact_mod_cast this
      linarith
    linarith
  exact_mod_cast hfinal

/-! ## 5. The heavy set carries every strict dominator -/

/-- **EVERY MEMBER OF A STRICT DOMINATOR IS STRICTLY HEAVY**, in projection
coordinates and at every rank.  The block gap is positive definite, so each of
its diagonal entries is positive, and that entry is the member's leverage
excess.  At rank three this is `Gtz.one_lt_leverage_of_posDef` read through
`Gtz.projectionOfDesign_diagonal`. -/
theorem weight_lt_projectionDiagonal_of_posDef_block (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hposDef : (projectionBlockGap design selected hcard).PosDef) (slot : Fin rank) :
    design.weight (selected.orderEmbOfFin hcard slot)
      < projectionOfDesign design (selected.orderEmbOfFin hcard slot)
          (selected.orderEmbOfFin hcard slot) := by
  have hdiag : 0 < projectionBlockGap design selected hcard slot slot := hposDef.diag_pos
  rw [projectionBlockGap_diag] at hdiag
  linarith

/-- The same, indexed by the subset: a strict dominator lies inside the heavy
set. -/
theorem subset_heavyLabels_of_posDef (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    selected ⊆ heavyLabels design := by
  classical
  intro atomIndex hmem
  rw [← image_orderEmbOfFin hcard] at hmem
  obtain ⟨slot, -, hslot⟩ := Finset.mem_image.mp hmem
  rw [mem_heavyLabels_iff, ← hslot]
  exact weight_lt_projectionDiagonal_of_posDef_block design selected hcard
    ((posDef_subsetSum_iff_projectionBlockGap design selected hcard).mp hposDef) slot

/-- **THE RIGIDITY.**  A strict dominator is a card-`rank` subset of the heavy
set, and the heavy set has at least `rank` elements.  When it has exactly `rank`,
the dominator has no freedom left: it **is** the heavy set. -/
theorem eq_heavyLabels_of_posDef_of_card_eq (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hposDef : (subsetSum design selected - 1).PosDef)
    (hheavy : (heavyLabels design).card = rank) :
    selected = heavyLabels design :=
  Finset.eq_of_subset_of_card_le (subset_heavyLabels_of_posDef design selected hcard hposDef)
    (by rw [hheavy, hcard])

/-- **AT A DESIGN WITH EXACTLY `rank` HEAVY LABELS THE OBJECTIVE IS DECIDED BY
ONE BLOCK.**  Either the heavy set itself strictly dominates, or no card-`rank`
selection does.  There is nothing to search. -/
theorem exists_posDef_iff_heavyLabels_posDef_of_card_eq (design : WeightedDesign size rank)
    (hheavy : (heavyLabels design).card = rank) :
    (∃ selected : Finset (Fin size), selected.card = rank
        ∧ (subsetSum design selected - 1).PosDef)
      ↔ (subsetSum design (heavyLabels design) - 1).PosDef := by
  constructor
  · rintro ⟨selected, hcard, hposDef⟩
    rwa [eq_heavyLabels_of_posDef_of_card_eq design selected hcard hposDef hheavy] at hposDef
  · intro hposDef
    exact ⟨heavyLabels design, hheavy, hposDef⟩

/-- The same dichotomy in projection coordinates, at the shape the objective
uses. -/
theorem projectionBlockSelects_at_of_card_heavyLabels_eq (design : WeightedDesign 6 3)
    (hheavy : (heavyLabels design).card = 3) :
    (∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
        (projectionBlockGap design selected hcard).PosDef)
      ↔ (projectionBlockGap design (heavyLabels design) hheavy).PosDef := by
  constructor
  · rintro ⟨selected, hcard, hposDef⟩
    have hsum := (posDef_subsetSum_iff_projectionBlockGap design selected hcard).mpr hposDef
    have heq := eq_heavyLabels_of_posDef_of_card_eq design selected hcard hsum hheavy
    subst heq
    exact (posDef_subsetSum_iff_projectionBlockGap design _ hheavy).mp hsum
  · intro hposDef
    exact ⟨heavyLabels design, hheavy, hposDef⟩

/-- **THE HEAVY SET IS NEVER EMPTY OF CANDIDATES AT RANK THREE.**  Three or more
labels are strictly heavy, so the pool a strict dominator must be drawn from
always has enough members.  With the leverage floor this says the search space
is exactly the card-three subsets of the heavy set. -/
theorem three_le_card_heavyLabels (design : WeightedDesign size 3) :
    3 ≤ (heavyLabels design).card :=
  rank_le_card_heavyLabels design (by norm_num)

/-- At rank three and size six, the light labels number at most three. -/
theorem card_heavyLabels_compl_le_three (design : WeightedDesign 6 3) :
    (heavyLabels design)ᶜ.card ≤ 3 := by
  have hheavy := three_le_card_heavyLabels design
  have hsplit : (heavyLabels design).card + (heavyLabels design)ᶜ.card = 6 := by
    rw [Finset.card_add_card_compl]
    simp
  omega

/-! ## 6. The complement duality

`I − P` is a symmetric idempotent too, of trace `size − rank`, and its diagonal
is the co-leverage.  The block gap is the SAME matrix read on the other side:
subtracting `P` from `diag w` is subtracting `diag (1 − w)` from `I − P` with the
sign reversed.  So the objective has two readings, and the second one is the
Loewner inequality the campaign's chart vocabulary was reaching for. -/

/-- The entries of the complement projection. -/
theorem complementProjection_apply (design : WeightedDesign size rank) (left right : Fin size) :
    complementProjection design left right
      = (if left = right then (1 : ℝ) else 0) - projectionOfDesign design left right := by
  rw [complementProjection]
  simp [Matrix.one_apply]

/-- Off the diagonal the complement projection is the negated projection. -/
theorem complementProjection_apply_ne (design : WeightedDesign size rank)
    {left right : Fin size} (hne : left ≠ right) :
    complementProjection design left right = -projectionOfDesign design left right := by
  rw [complementProjection_apply, if_neg hne]
  ring

/-- The complement diagonal is one minus the projection diagonal. -/
theorem complementProjection_diag_eq (design : WeightedDesign size rank) (atomIndex : Fin size) :
    complementProjection design atomIndex atomIndex
      = 1 - projectionOfDesign design atomIndex atomIndex := by
  rw [complementProjection_apply, if_pos rfl]

/-- **THE BLOCK GAP IS A COMPLEMENT DEFECT.**  `P[C] − diag w_C = diag (1 − w)_C
− (I − P)[C]`.  Strict domination therefore reads two ways: the projection block
beats the weights, or the complement projection block stays strictly below the
co-weights.  Both sides are the same matrix. -/
theorem projectionBlockGap_eq_coweight_sub_complementBlock (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) :
    projectionBlockGap design selected hcard
      = Matrix.diagonal (fun slot => 1 - design.weight (selected.orderEmbOfFin hcard slot))
        - (complementProjection design).submatrix (selected.orderEmbOfFin hcard)
            (selected.orderEmbOfFin hcard) := by
  ext left right
  rw [projectionBlockGap_apply]
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.diagonal_apply,
    complementProjection_apply]
  rcases eq_or_ne left right with rfl | hne
  · rw [if_pos rfl, if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg hne, if_neg hne, if_neg (fun heq => hne ((selected.orderEmbOfFin hcard).injective heq))]
    ring

/-- **THE OBJECTIVE, READ ON THE COMPLEMENT.**  A selection strictly dominates
exactly when its complement-projection block is strictly below the co-weight
diagonal. -/
theorem posDef_subsetSum_iff_coweight_sub_complementBlock (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) :
    (subsetSum design selected - 1).PosDef
      ↔ (Matrix.diagonal (fun slot => 1 - design.weight (selected.orderEmbOfFin hcard slot))
          - (complementProjection design).submatrix (selected.orderEmbOfFin hcard)
              (selected.orderEmbOfFin hcard)).PosDef := by
  rw [posDef_subsetSum_iff_projectionBlockGap design selected hcard,
    projectionBlockGap_eq_coweight_sub_complementBlock design selected hcard]

/-- The complement diagonal totals the corank. -/
theorem sum_complementProjection_diagonal (design : WeightedDesign size rank) :
    ∑ atomIndex, complementProjection design atomIndex atomIndex = (size : ℝ) - (rank : ℝ) := by
  have hstep : ∀ atomIndex : Fin size, complementProjection design atomIndex atomIndex
      = 1 - projectionOfDesign design atomIndex atomIndex :=
    complementProjection_diag_eq design
  rw [Finset.sum_congr rfl fun atomIndex _ => hstep atomIndex, Finset.sum_sub_distrib,
    sum_projectionDiagonal design]
  simp

/-! ## 7. The off-diagonal squeeze

The row-square law of an idempotent says a row of squares totals its own
diagonal entry.  Splitting off the diagonal term leaves the off-diagonal energy
of the row equal to `P_cc (1 − P_cc)`, and every single off-diagonal square is
one nonnegative term of that sum.  So each off-diagonal entry is squeezed by the
diagonal AND by its complement at once, and the bound is attained. -/

/-- **THE OFF-DIAGONAL ENERGY OF A ROW.**  The squares off the diagonal total
`P_cc (1 − P_cc)` exactly. -/
theorem sum_erase_sq_projectionRow (design : WeightedDesign size rank) (rowIndex : Fin size) :
    ∑ colIndex ∈ Finset.univ.erase rowIndex, projectionOfDesign design rowIndex colIndex ^ 2
      = projectionOfDesign design rowIndex rowIndex
        * (1 - projectionOfDesign design rowIndex rowIndex) := by
  classical
  have hrow := sum_sq_projectionRow_eq_diagonal (projectionOfDesign_transpose design)
    (projectionOfDesign_mul_self design) rowIndex
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ rowIndex)] at hrow
  nlinarith [hrow]

/-- **THE OFF-DIAGONAL SQUEEZE.**  Every off-diagonal square of the projection is
at most `P_cc (1 − P_cc)`, from either endpoint.  The bound is attained: at the
rank-one projection onto a diagonal direction of the plane both sides are one
quarter. -/
theorem sq_projectionOffDiag_le_mul_one_sub (design : WeightedDesign size rank)
    {rowIndex colIndex : Fin size} (hne : colIndex ≠ rowIndex) :
    projectionOfDesign design rowIndex colIndex ^ 2
      ≤ projectionOfDesign design rowIndex rowIndex
        * (1 - projectionOfDesign design rowIndex rowIndex) := by
  classical
  rw [← sum_erase_sq_projectionRow design rowIndex]
  refine Finset.single_le_sum (f := fun index => projectionOfDesign design rowIndex index ^ 2)
    (fun index _ => sq_nonneg _) ?_
  exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ colIndex⟩

/-- **THE UNIFORM OFF-DIAGONAL CAP.**  No off-diagonal entry of a projection
exceeds one half in absolute value, because `x (1 − x)` never exceeds a
quarter. -/
theorem sq_projectionOffDiag_le_quarter (design : WeightedDesign size rank)
    {rowIndex colIndex : Fin size} (hne : colIndex ≠ rowIndex) :
    projectionOfDesign design rowIndex colIndex ^ 2 ≤ 1 / 4 := by
  have hbound := sq_projectionOffDiag_le_mul_one_sub design hne
  nlinarith [sq_nonneg (projectionOfDesign design rowIndex rowIndex - 1 / 2)]

/-- The squeeze read from the other endpoint, by symmetry of the projection. -/
theorem sq_projectionOffDiag_le_mul_one_sub' (design : WeightedDesign size rank)
    {rowIndex colIndex : Fin size} (hne : rowIndex ≠ colIndex) :
    projectionOfDesign design rowIndex colIndex ^ 2
      ≤ projectionOfDesign design colIndex colIndex
        * (1 - projectionOfDesign design colIndex colIndex) := by
  have hsymm : projectionOfDesign design rowIndex colIndex
      = projectionOfDesign design colIndex rowIndex := by
    conv_lhs => rw [← projectionOfDesign_transpose design]
    rfl
  rw [hsymm]
  exact sq_projectionOffDiag_le_mul_one_sub design hne

/-! ## 8. A certificate that reads the diagonal only

The two-by-two leading minor of the block gap is
`(P_aa − w_a)(P_bb − w_b) − P_ab²`, and the squeeze caps the subtracted term by a
quantity built from the diagonal alone.  So a pair can be certified without ever
reading its off-diagonal entry.  This is the pair-level cell in the coordinates
the objective is now stated in. -/

/-- **THE DIAGONAL PAIR CERTIFICATE.**  If the two leverage excesses multiply to
more than the first endpoint's off-diagonal cap, the pair's two-by-two minor is
strictly positive — with no off-diagonal entry read anywhere.  Strict heaviness
of either endpoint is not assumed: it follows, and
`Gtz.weight_lt_projectionDiagonal_of_pairCertificate` extracts it. -/
theorem posDef_pairBlock_of_diagonalExcess (design : WeightedDesign size rank)
    {first second : Fin size} (hne : first ≠ second)
    (hexcess : projectionOfDesign design first first
        * (1 - projectionOfDesign design first first)
      < (projectionOfDesign design first first - design.weight first)
        * (projectionOfDesign design second second - design.weight second)) :
    0 < (projectionOfDesign design first first - design.weight first)
        * (projectionOfDesign design second second - design.weight second)
      - projectionOfDesign design first second ^ 2 := by
  have hcap := sq_projectionOffDiag_le_mul_one_sub design (Ne.symm hne)
  linarith

/-- The certificate forces the second label to be strictly heavy too: a positive
product with a positive first factor leaves the second factor positive. -/
theorem weight_lt_projectionDiagonal_of_pairCertificate (design : WeightedDesign size rank)
    {first second : Fin size}
    (hfirst : design.weight first < projectionOfDesign design first first)
    (hexcess : projectionOfDesign design first first
        * (1 - projectionOfDesign design first first)
      < (projectionOfDesign design first first - design.weight first)
        * (projectionOfDesign design second second - design.weight second)) :
    design.weight second < projectionOfDesign design second second := by
  by_contra hcon
  push Not at hcon
  have hnonneg : 0 ≤ projectionOfDesign design first first
      * (1 - projectionOfDesign design first first) :=
    mul_nonneg (projectionOfDesign_diagonal_nonneg design first)
      (by linarith [projectionDiagonal_le_one' design first])
  nlinarith

/-- **BOTH ENDPOINTS OF A CERTIFIED PAIR LIE IN THE HEAVY SET.**  The diagonal
certificate therefore never leaves the pool the rigidity theorem describes. -/
theorem pair_subset_heavyLabels_of_certificate (design : WeightedDesign size rank)
    {first second : Fin size}
    (hfirst : design.weight first < projectionOfDesign design first first)
    (hexcess : projectionOfDesign design first first
        * (1 - projectionOfDesign design first first)
      < (projectionOfDesign design first first - design.weight first)
        * (projectionOfDesign design second second - design.weight second)) :
    ({first, second} : Finset (Fin size)) ⊆ heavyLabels design := by
  intro atomIndex hmem
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exact (mem_heavyLabels_iff design atomIndex).mpr hfirst
  · exact (mem_heavyLabels_iff design atomIndex).mpr
      (weight_lt_projectionDiagonal_of_pairCertificate design hfirst hexcess)

end Gtz
