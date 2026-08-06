/-
# Route (b)'s two Props: the relativized window hinge and the anchor reach

Builds on `Gtz.Uniform.UniformPositionBridge`, which wired route (b) as a
uniform kernel arrow resting on `ParallelPairAtWindowTie` and
`WindowAnchorReach`.  This file attacks the two Props separately.  Everything
is uniform in the rank; rank 3 appears only as a cross-check.

## Prop 1 — `ParallelPairAtWindowTie`

Two findings, opposite in sign.

* **A free strengthening** (`ParallelPairAtWindowTieRelative`): the
  window-cell hinge may ASSUME the previous size is already closed.  The size
  induction has `GtzWeighted (size - 1) rank` in hand at every step, so
  relativizing costs nothing — and this is exactly the shape the rank-3
  material has: `Gtz.hingeHoldsAtSize_sevenThree_of_multiLineCases` takes
  `GtzWeighted 6 3` as its first argument.
* **A wall** (`corankTwoCell_not_insideCanonicalWindow`): the window's lower
  cells do NOT fall to the corank-2 tie law.  Every window cell has corank at
  least `rank`, so at rank `>= 3` no window cell is the corank-2 cell, and
  Naimark duality does not help either — the dual of a window cell has corank
  exactly `rank`.  So `ParallelPairAtWindowTie` does NOT collapse to its top
  cell by corank descent; the window's cells are independent obligations.

Also here: the hinge's domination reformulation
(`hingeHoldsAtSize_iff_strictOnPrimitiveLocus`) — once the cell's weighted
theorem is known, the hinge says exactly "every PRIMITIVE design at the cell
has a STRICTLY dominating subset", which is the form the reach argument
consumes.

## Prop 2 — `WindowAnchorReach`

The anchor half is FREE.  Rescaling a design's atoms by positive scalars,
with the weights compensating, keeps Parseval and keeps parallel-freeness
(`rescaledDesign`); pushing the scale up on any weakly dominating rank-subset
makes that subset STRICTLY dominating
(`exists_strictAnchor_of_weakDominator`).  So an anchor never has to be
constructed: any parallel-free weakly-dominating design at the cell can be
reweighted into one.  `WindowAnchorReach` therefore reduces to ONE
topological statement per cell plus non-emptiness of the parallel-free
locus.
-/
import Gtz.Uniform.UniformPositionBridge
import Gtz.Design.LinePatternCompleteness
import Gtz.Reduction.ConnectednessRouteCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz
namespace UniformPositionBridge

open Matrix Finset

/-! ## Prop 1, part A: the relativized window hinge -/

/-- **Route (b)'s first Prop, relativized.**  The window-cell hinge, allowed to
assume the previous size is already closed.  Weaker than
`ParallelPairAtWindowTie` (`parallelPairAtWindowTieRelative_of_windowTie`) and
free in the size induction, which reaches each cell with the previous one in
hand. -/
def ParallelPairAtWindowTieRelative (rank : ℕ) : Prop :=
  ∀ size : ℕ, InductionStep.IsInsideCanonicalWindow size rank →
    GtzWeighted (size - 1) rank → HingeHoldsAtSize size rank

/-- The relativized Prop is weaker. -/
theorem parallelPairAtWindowTieRelative_of_windowTie {rank : ℕ}
    (hwindowTie : ParallelPairAtWindowTie rank) :
    ParallelPairAtWindowTieRelative rank :=
  fun size hinside _ => hwindowTie size hinside

/-- **ROUTE (b), SHARPENED.**  The window closure needs only the RELATIVIZED
hinge: at every rung the size induction already owns the previous size, so it
can hand it to the hinge.  Same conclusion as
`closesCanonicalWindow_of_windowTie_of_reach`, strictly weaker hypothesis. -/
theorem closesCanonicalWindow_of_relativeWindowTie_of_reach (rank : ℕ) (hrank : 3 ≤ rank)
    (hwindowTie : ParallelPairAtWindowTieRelative rank) (hreach : WindowAnchorReach rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) :
    InductionStep.ClosesCanonicalWindow rank := by
  have hwindowRung : ∀ offset : ℕ, 2 * rank + offset ≤ rank * (rank + 1) / 2 + 1 →
      GtzWeighted (2 * rank + offset) rank := by
    intro offset
    induction offset with
    | zero =>
        intro hoffsetTop
        have hsucc : 2 * rank + 0 = (2 * rank - 1) + 1 := by omega
        rw [hsucc]
        have hfloor : GtzWeighted (2 * rank - 1) rank :=
          gtzWeighted_belowWindow_of_predecessor hrank hpredecessor
        refine gtzWeighted_succ_of_hinge_of_reach ?_ ?_ hfloor
        · exact hwindowTie ((2 * rank - 1) + 1) ⟨by omega, by omega⟩ hfloor
        · exact hreach ((2 * rank - 1) + 1) ⟨by omega, by omega⟩
    | succ prevOffset ih =>
        intro hoffsetTop
        have hsucc : 2 * rank + (prevOffset + 1) = (2 * rank + prevOffset) + 1 := by omega
        rw [hsucc]
        have hprevSize : GtzWeighted (2 * rank + prevOffset) rank := ih (by omega)
        refine gtzWeighted_succ_of_hinge_of_reach ?_ ?_ hprevSize
        · exact hwindowTie ((2 * rank + prevOffset) + 1) ⟨by omega, by omega⟩ hprevSize
        · exact hreach ((2 * rank + prevOffset) + 1) ⟨by omega, by omega⟩
  intro size hinside
  obtain ⟨hbelow, habove⟩ := hinside
  have hoffsetSplit : size = 2 * rank + (size - 2 * rank) := by omega
  rw [hoffsetSplit]
  exact hwindowRung (size - 2 * rank) (by omega)

/-- Route (b)'s target from the relativized Prop. -/
theorem routeB_target_relative
    (hwindowTie : ∀ rank : ℕ, 3 ≤ rank → ParallelPairAtWindowTieRelative rank)
    (hreach : ∀ rank : ℕ, 3 ≤ rank → WindowAnchorReach rank) :
    ∀ size rank : ℕ, 1 ≤ rank → rank ≤ size → GtzWeighted size rank := by
  have harrow : InductionStep.WindowArrowFromPredecessorWeighted := by
    intro rank hrank hpredecessor
    exact closesCanonicalWindow_of_relativeWindowTie_of_reach rank hrank
      (hwindowTie rank hrank) (hreach rank hrank) hpredecessor
  intro size rank hrankPos _
  exact InductionStep.forall_gtzWeightedAll_of_windowArrow harrow rank hrankPos size

/-! ## Prop 1, part B: the corank wall — no collapse to the top cell

The natural hope is that the window's LOWER cells fall to the corank-2 tie
law (`CorankTwo.sharedCircuitPairAtCorankTwoTie_holds`), leaving only the top
cell.  The arithmetic refutes it decisively, and in both the primal and the
dual reading. -/

/-- Every canonical-window cell has corank at least the rank: the window starts
at `2 * rank`. -/
theorem windowCell_corank_ge_rank {size rank : ℕ}
    (hinside : InductionStep.IsInsideCanonicalWindow size rank) : rank ≤ size - rank := by
  obtain ⟨hbelow, _⟩ := hinside
  omega

/-- **THE WALL, primal reading.**  At rank `>= 3` the corank-2 cell lies
strictly BELOW the canonical window, so the corank-2 tie law never speaks
about a window cell.  (`InductionStep.corankFloor_meetsWindow_iff` records
the same separation for the GtzWeighted VALUE; this is its tie-side
analogue.) -/
theorem corankTwoCell_not_insideCanonicalWindow {rank : ℕ} (hrank : 3 ≤ rank) :
    ¬ InductionStep.IsInsideCanonicalWindow (rank + 2) rank := by
  rintro ⟨hbelow, _⟩
  omega

/-- **THE WALL, dual reading.**  Naimark duality does not rescue the descent
either: the dual of a cell `(size, rank)` sits at `(size, size - rank)`, whose
corank is exactly `rank`.  At rank `>= 3` that is never `2`, so no window cell's
dual is a corank-2 cell. -/
theorem naimarkDual_corank_eq_rank {size rank : ℕ} (hrankLe : rank ≤ size) :
    size - (size - rank) = rank := by omega

/-- The two walls together: at rank `>= 3` NO window cell is a corank-2 cell and
NO window cell's Naimark dual is one.  So `ParallelPairAtWindowTie` does not
collapse onto its top cell by corank descent — each window cell is an
independent obligation, and the window has `rank * (rank - 3) / 2 + 2` cells. -/
theorem windowCell_neither_corankTwo_nor_dualCorankTwo {size rank : ℕ} (hrank : 3 ≤ rank)
    (hinside : InductionStep.IsInsideCanonicalWindow size rank) :
    size - rank ≠ 2 ∧ size - (size - rank) ≠ 2 := by
  obtain ⟨hbelow, _⟩ := hinside
  exact ⟨by omega, by omega⟩

/-- The canonical window's cell count, for the record: from `2 * rank` to
`M(rank)` inclusive.  At rank 3 it is 2 (the cells 6 and 7); it grows
quadratically, so the per-cell obligations are not a fixed budget. -/
theorem canonicalWindow_cellCount {rank : ℕ} (hrank : 3 ≤ rank) :
    2 * ((rank * (rank + 1) / 2 + 1) + 1 - 2 * rank) = rank * (rank - 3) + 4 := by
  obtain ⟨triangular, htriangular⟩ : ∃ triangular : ℕ, rank * (rank + 1) = 2 * triangular := by
    obtain ⟨half, hhalf⟩ := Nat.even_mul_succ_self rank
    exact ⟨half, by omega⟩
  have hdiv : rank * (rank + 1) / 2 = triangular := by
    rw [htriangular, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hgap : rank * (rank - 3) + 4 * rank = rank * (rank + 1) := by
    obtain ⟨offset, rfl⟩ : ∃ offset : ℕ, rank = offset + 3 := ⟨rank - 3, by omega⟩
    have hsub : offset + 3 - 3 = offset := by omega
    rw [hsub]
    ring
  have htriangularBound : 2 * rank ≤ triangular + 1 := by nlinarith [htriangular]
  omega

/-! ## Prop 1, part C: what the hinge says once the cell is closed -/

/-- **The hinge IS strict domination on the primitive locus.**  Once the cell's
weighted theorem is known — which, inside route (b)'s induction, is exactly the
state at the NEXT cell — the hinge's tie hypothesis collapses: a tie is a design
with a weak dominator and no strict one, and the weighted theorem supplies the
weak dominator unconditionally.  So the hinge says "every primitive design here
dominates STRICTLY", which is precisely the predicate `Gtz.AtomsStrict` that the
connectedness argument propagates along paths. -/
theorem hingeHoldsAtSize_iff_strictOnPrimitiveLocus {size rank : ℕ}
    (hcell : GtzWeighted size rank) :
    HingeHoldsAtSize size rank
      ↔ ∀ design : WeightedDesign size rank, ¬ HasParallelPair design →
          HasStrictlyDominatingSubset design := by
  constructor
  · intro hhinge design hparallelFree
    have hnotTie : ¬ IsTie design := fun htie => hparallelFree (hhinge design htie)
    rcases strict_or_not_dominating_of_not_isTie hnotTie with hstrict | hnoWeak
    · exact hstrict
    · exact absurd (hcell design) hnoWeak
  · intro hstrictOnPrimitive design htie
    by_contra hparallelFree
    obtain ⟨strictSubset, hstrictCard, hstrictPosDef⟩ := hstrictOnPrimitive design hparallelFree
    exact htie.2 strictSubset hstrictCard hstrictPosDef

/-! ## Prop 1, rank-3 cross-check: the relativization is the native shape -/

/-- **Rank-3 cross-check.**  At rank 3 the window is `{6, 7}`, and the
seven-point hinge is stated EXACTLY in the relativized form — it consumes
`GtzWeighted 6 3`, the previous window cell.  So
`ParallelPairAtWindowTieRelative 3` is delivered by the six-point hinge
together with the seven-point enumeration inputs, with the relativization
slot filled by the induction itself rather than by a hypothesis. -/
theorem parallelPairAtWindowTieRelative_three_of_landedInputs
    (hsix : HingeHoldsAtSize 6 3)
    (hmulti : LinearSpaceMultiLineCasesSeven) (hresidual : HingeStratumObligationSeven) :
    ParallelPairAtWindowTieRelative 3 := by
  intro size hinside hprevSize
  obtain ⟨hbelow, habove⟩ := hinside
  have hwindowTwo : size = 6 ∨ size = 7 := by omega
  rcases hwindowTwo with hsix' | hseven'
  · rw [hsix']; exact hsix
  · subst hseven'
    exact hingeHoldsAtSize_sevenThree_of_multiLineCases hprevSize hmulti hresidual

/-! ## Prop 2: `WindowAnchorReach` — the anchor half is FREE

The obligation splits per cell into an ANCHOR (a parallel-free design with a
strictly dominating subset) and a REACH (path-connectedness of the parallel-free
locus to it).  The anchor half does not need a construction at all: rescaling a
design's atoms by positive scalars, with the weights compensating, keeps Parseval
and keeps parallel-freeness, and scaling UP on a WEAKLY dominating subset makes
it dominate STRICTLY.  So the anchor obligation collapses from "exhibit a
strictly dominating parallel-free design" to "exhibit a parallel-free design
that dominates WEAKLY" — an existential, far below the cell's `GtzWeighted`. -/

/-- **Rescaling a design.**  Every atom is scaled by `sqrt (scaleSq label)` and
its weight divided by `scaleSq label`.  Parseval survives on the nose because
`Gtz.atomMatrix` is quadratic in the atom (`Gtz.atomMatrix_smul`), so the scale
cancels against the weight exactly. -/
noncomputable def rescaledDesign {size rank : ℕ} (design : WeightedDesign size rank)
    (scaleSq : Fin size → ℝ) (hscalePos : ∀ label, 0 < scaleSq label)
    (hweightSum : ∑ label, design.weight label / scaleSq label = 1) :
    WeightedDesign size rank where
  atom label := Real.sqrt (scaleSq label) • design.atom label
  weight label := design.weight label / scaleSq label
  weight_pos := fun label => div_pos (design.weight_pos label) (hscalePos label)
  weight_sum_one := hweightSum
  isParseval := by
    rw [← design.isParseval]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [atomMatrix_smul, Real.sq_sqrt (hscalePos label).le, smul_smul]
    congr 1
    rw [div_mul_cancel₀ _ (ne_of_gt (hscalePos label))]

@[simp] theorem rescaledDesign_atom {size rank : ℕ} (design : WeightedDesign size rank)
    (scaleSq : Fin size → ℝ) (hscalePos : ∀ label, 0 < scaleSq label)
    (hweightSum : ∑ label, design.weight label / scaleSq label = 1) (label : Fin size) :
    (rescaledDesign design scaleSq hscalePos hweightSum).atom label
      = Real.sqrt (scaleSq label) • design.atom label := rfl

/-- **Rescaling preserves parallel-freeness**: proportionality of atoms is
invariant under individual positive rescaling. -/
theorem hasParallelPair_of_rescaled {size rank : ℕ} (design : WeightedDesign size rank)
    (scaleSq : Fin size → ℝ) (hscalePos : ∀ label, 0 < scaleSq label)
    (hweightSum : ∑ label, design.weight label / scaleSq label = 1)
    (hrescaled : HasParallelPair (rescaledDesign design scaleSq hscalePos hweightSum)) :
    HasParallelPair design := by
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩ := hrescaled
  rw [rescaledDesign_atom, rescaledDesign_atom] at hparallel
  have hdropPos : 0 < Real.sqrt (scaleSq dropLabel) := Real.sqrt_pos.mpr (hscalePos dropLabel)
  refine ⟨keptLabel, dropLabel,
    (Real.sqrt (scaleSq dropLabel))⁻¹ * (ratio * Real.sqrt (scaleSq keptLabel)),
    hdistinct, ?_⟩
  have hscaled := congrArg (fun vec => (Real.sqrt (scaleSq dropLabel))⁻¹ • vec) hparallel
  simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hdropPos), one_smul] at hscaled
  rw [hscaled, ← smul_smul, ← smul_smul]

/-- The rescaled subset sum on a set where the scale is CONSTANT is the constant
times the original subset sum. -/
theorem subsetSum_rescaledDesign_of_constOn {size rank : ℕ}
    (design : WeightedDesign size rank) (scaleSq : Fin size → ℝ)
    (hscalePos : ∀ label, 0 < scaleSq label)
    (hweightSum : ∑ label, design.weight label / scaleSq label = 1)
    {chosen : Finset (Fin size)} {factor : ℝ}
    (hconst : ∀ label ∈ chosen, scaleSq label = factor) :
    subsetSum (rescaledDesign design scaleSq hscalePos hweightSum) chosen
      = factor • subsetSum design chosen := by
  rw [subsetSum, subsetSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun label hlabel => ?_
  rw [rescaledDesign_atom, atomMatrix_smul, Real.sq_sqrt (hscalePos label).le, hconst label hlabel]

/-- **THE ANCHOR HALF, DISCHARGED.**  A parallel-free design with a WEAKLY
dominating rank-subset rescales into a parallel-free design with a STRICTLY
dominating one: double the scale on the subset (`2 * S - 1 = S + (S - 1)`, a
positive-definite plus a positive-semidefinite), and absorb the weight in the
complement, which is nonempty because `rank < size`.  No anchor construction and
no eigenvalue estimate is needed. -/
theorem exists_strictAnchor_of_weakDominator {size rank : ℕ} (hrankLt : rank < size)
    (design : WeightedDesign size rank) (hfree : ¬ HasParallelPair design)
    {chosen : Finset (Fin size)} (hcard : chosen.card = rank)
    (hdominates : Dominates design chosen) :
    ∃ anchor : WeightedDesign size rank,
      ¬ HasParallelPair anchor ∧ HasStrictlyDominatingSubset anchor := by
  classical
  set chosenMass : ℝ := ∑ label ∈ chosen, design.weight label with hchosenMassDef
  obtain ⟨outsideLabel, houtside⟩ : ∃ label : Fin size, label ∉ chosen := by
    by_contra hall
    push Not at hall
    have huniv : chosen = Finset.univ := Finset.eq_univ_of_forall hall
    rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have hmassLt : chosenMass < 1 := by
    rw [hchosenMassDef, ← design.weight_sum_one]
    exact Finset.sum_lt_sum_of_subset (Finset.subset_univ chosen)
      (Finset.mem_univ outsideLabel) houtside (design.weight_pos outsideLabel)
      (fun other _ _ => (design.weight_pos other).le)
  have hmassNonneg : 0 ≤ chosenMass :=
    Finset.sum_nonneg fun label _ => (design.weight_pos label).le
  have houtsideScalePos : 0 < 2 * (1 - chosenMass) / (2 - chosenMass) := by
    apply div_pos <;> linarith
  set scaleSq : Fin size → ℝ :=
    fun label => if label ∈ chosen then 2 else 2 * (1 - chosenMass) / (2 - chosenMass)
    with hscaleSqDef
  have hscalePos : ∀ label, 0 < scaleSq label := by
    intro label
    rw [hscaleSqDef]
    by_cases hmem : label ∈ chosen
    · simp [hmem]
    · simpa [hmem] using houtsideScalePos
  have hcomplementMass : ∑ label ∈ chosenᶜ, design.weight label = 1 - chosenMass := by
    have hsplit := Finset.sum_add_sum_compl chosen design.weight
    rw [design.weight_sum_one] at hsplit
    rw [hchosenMassDef]
    linarith [hsplit]
  have hweightSum : ∑ label, design.weight label / scaleSq label = 1 := by
    rw [← Finset.sum_add_sum_compl chosen]
    have hinside : ∑ label ∈ chosen, design.weight label / scaleSq label
        = chosenMass / 2 := by
      rw [hchosenMassDef, Finset.sum_div]
      exact Finset.sum_congr rfl fun label hlabel => by rw [hscaleSqDef]; simp [hlabel]
    have houtsideSum : ∑ label ∈ chosenᶜ, design.weight label / scaleSq label
        = (1 - chosenMass) / (2 * (1 - chosenMass) / (2 - chosenMass)) := by
      have hpointwise : ∀ label ∈ chosenᶜ, design.weight label / scaleSq label
          = design.weight label / (2 * (1 - chosenMass) / (2 - chosenMass)) := by
        intro label hlabel
        rw [hscaleSqDef]
        simp [Finset.mem_compl.mp hlabel]
      rw [Finset.sum_congr rfl hpointwise, ← Finset.sum_div, hcomplementMass]
    rw [hinside, houtsideSum]
    have honeMinus : (1 : ℝ) - chosenMass ≠ 0 := by linarith
    have htwoMinus : (2 : ℝ) - chosenMass ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨rescaledDesign design scaleSq hscalePos hweightSum, ?_, ?_⟩
  · exact fun hparallel =>
      hfree (hasParallelPair_of_rescaled design scaleSq hscalePos hweightSum hparallel)
  · refine ⟨chosen, hcard, ?_⟩
    have hconst : ∀ label ∈ chosen, scaleSq label = 2 := by
      intro label hlabel
      rw [hscaleSqDef]
      simp [hlabel]
    rw [subsetSum_rescaledDesign_of_constOn design scaleSq hscalePos hweightSum hconst]
    have hsubsetPosDef : (subsetSum design chosen).PosDef := by
      have hshift := Matrix.PosDef.add_posSemidef Matrix.PosDef.one hdominates
      rwa [add_sub_cancel] at hshift
    have hsplit : (2 : ℝ) • subsetSum design chosen - 1
        = subsetSum design chosen + (subsetSum design chosen - 1) := by
      rw [two_smul]
      abel
    rw [hsplit]
    exact Matrix.PosDef.add_posSemidef hsubsetPosDef hdominates

/-! ### The anchor obligation, restated — and the rank-2 calibration -/

/-- Route (b)'s topological input with the anchor's parallel-freeness made
explicit.  This is what the reduction above naturally delivers, and it is what
the rank-2 refutation below speaks about.  Stronger than `WindowAnchorReach`. -/
def WindowAnchorReachFree (rank : ℕ) : Prop :=
  ∀ size : ℕ, InductionStep.IsInsideCanonicalWindow size rank →
    ∃ anchor : WeightedDesign size rank,
      ¬ HasParallelPair anchor ∧ HasStrictlyDominatingSubset anchor
        ∧ ParallelFreeReachesAnchor size rank anchor

theorem windowAnchorReach_of_windowAnchorReachFree {rank : ℕ}
    (hreach : WindowAnchorReachFree rank) : WindowAnchorReach rank :=
  fun size hinside =>
    let ⟨anchor, _, hstrict, hpath⟩ := hreach size hinside
    ⟨anchor, hstrict, hpath⟩

/-- **THE ANCHOR HALF REDUCES TO WEAK DOMINATION.**  Given, at each window cell,
a parallel-free design that dominates WEAKLY and a reach statement for the
rescaled anchor, the full obligation follows.  The strict-domination half of the
anchor is never an obligation. -/
theorem windowAnchorReachFree_of_weakWitness {rank : ℕ} (hrank : 3 ≤ rank)
    (hwitness : ∀ size : ℕ, InductionStep.IsInsideCanonicalWindow size rank →
      ∃ design : WeightedDesign size rank, ¬ HasParallelPair design
        ∧ ∃ chosen : Finset (Fin size), chosen.card = rank ∧ Dominates design chosen)
    (hpath : ∀ (size : ℕ) (anchor : WeightedDesign size rank),
      InductionStep.IsInsideCanonicalWindow size rank → ¬ HasParallelPair anchor →
      ParallelFreeReachesAnchor size rank anchor) :
    WindowAnchorReachFree rank := by
  intro size hinside
  obtain ⟨design, hfree, chosen, hcard, hdominates⟩ := hwitness size hinside
  have hrankLt : rank < size := by
    obtain ⟨hbelow, _⟩ := hinside
    omega
  obtain ⟨anchor, hanchorFree, hanchorStrict⟩ :=
    exists_strictAnchor_of_weakDominator hrankLt design hfree hcard hdominates
  exact ⟨anchor, hanchorFree, hanchorStrict, hpath size anchor hinside hanchorFree⟩

/-- **THE `3 <= rank` HYPOTHESIS IS LOAD-BEARING, NOT COSMETIC.**  At rank 2
the reach statement is REFUTED for every size and every parallel-free anchor
(`Gtz.not_parallelFreeReachesAnchor_rankTwo` — an orientation argument:
`pairDet` has constant sign along a parallel-free path, but negating an atom
flips it while preserving Parseval and parallel-freeness).  The rank-2 window
is the single cell `size = 4`, so route (b)'s topological input is FALSE
there.  No rank-uniform reach theorem exists; `3 <= rank` must be carried. -/
theorem not_windowAnchorReachFree_two : ¬ WindowAnchorReachFree 2 := by
  intro hreach
  obtain ⟨anchor, hanchorFree, _, hpath⟩ := hreach 4 ⟨by norm_num, by norm_num⟩
  exact not_parallelFreeReachesAnchor_rankTwo (size := 2) anchor hanchorFree hpath

/-- **THE WINDOW IS EXACTLY THE REACH PROOF'S SCHEDULE CONDITION.**  The
`(6,3)` walk moves one atom at a time through a moment-curve hub and needs
`rank` atoms held fixed as a spanning tripod while `rank` others are already
on the curve — i.e. `size >= 2 * rank`, tight at `6 = 2 * 3`.  That is
VERBATIM the canonical window's lower bound, so inside the window the
schedule constraint is never the obstruction: it holds at every window cell
of every rank, with the bottom cell exactly tight. -/
theorem windowCell_meets_walkSchedule {size rank : ℕ}
    (hinside : InductionStep.IsInsideCanonicalWindow size rank) : 2 * rank ≤ size :=
  hinside.1

end UniformPositionBridge
end Gtz
