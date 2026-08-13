/-
# The moment-hub schedule at general rank: T1 is a theorem inside the window

`GeneralRankReachSkeleton` reduced the anchor-reach obligation to two
topological Props per window cell, and left the first one, the SCHEDULE, named
but unwritten:

* `GoodTupleReachesMomentHub size rank` — every good tuple reaches a
  moment-curve hub inside the good tuples.

This file writes it, at every cell of the sharp window.  The single move
(`joinedIn_moveOne`) asks for two things at each step: the target must be off
the line of every other row, and the OTHER rows must span on their own.  The
first is free from the hub hypothesis and from `momentPoint_offLine`.  The
second is the whole schedule problem, and the window floor `2 * rank <= size`
is exactly the room that solves it.

THE TWO PHASES.  Extract a spanning base of at most `rank` rows
(`exists_spansOn_card_le`).  Phase one moves every label OUTSIDE the base onto
the curve, one at a time, in any order: the base is untouched, thus it spans.
Phase two moves the base labels, one at a time: the `size - rank >= rank`
moment points already placed span by `probe_eq_zero_of_manyMomentPoints`.  Both
phases are one `Finset` induction over `joinedIn_hybrid_insert`.

THE EXTRACTION.  A spanning family of `size` rows contains a spanning subfamily
of at most `rank` rows.  The proof drops one row at a time: a family of more
than `rank` vectors in a space of dimension `rank` is dependent, and a row that
carries a nonzero coefficient is redundant.  Nothing here is rank-three bound.

WHAT THIS CLOSES.  `goodTupleConnected_of_window` proves T1 at every cell with
`3 <= rank` and `2 * rank <= size`.  That covers the sharp window and the
canonical window, thus the anchor-reach obligation now rests on the whitening
alone.  `isPathConnected_goodTupleSet` states the same fact as a property of the
set.

THE FLOOR IS NOT DECORATION.  `not_goodTupleConnected_self` refutes T1 at
`size = rank`: a square good tuple is invertible, the determinant is continuous
and never zero along a path of good tuples, and the identity and the identity
with one sign flipped have determinants of opposite sign.  Nothing is claimed
between `rank + 1` and `2 * rank - 1`.
-/
import Gtz.Uniform.GeneralRankReachSkeleton

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz
namespace GeneralRankReach

open Matrix Finset

/-! ## Spanning on a finset of labels

`RowsSpan` is spanning by all the rows.  The schedule needs the same property
for a named subfamily, because the point of the schedule is that a subfamily
carries the span while the other rows move. -/

/-- The rows indexed by `base` span, in the dual form: only the zero probe is
orthogonal to all of them. -/
def SpansOn {size rank : ℕ} (rows : Fin size → Fin rank → ℝ)
    (base : Finset (Fin size)) : Prop :=
  ∀ probe : Fin rank → ℝ, (∀ label ∈ base, rows label ⬝ᵥ probe = 0) → probe = 0

theorem spansOn_univ_of_rowsSpan {size rank : ℕ} {rows : Fin size → Fin rank → ℝ}
    (hspan : RowsSpan rows) : SpansOn rows Finset.univ :=
  fun probe hprobe => hspan probe fun label => hprobe label (Finset.mem_univ label)

theorem rowsSpan_of_spansOn_univ {size rank : ℕ} {rows : Fin size → Fin rank → ℝ}
    (hspan : SpansOn rows Finset.univ) : RowsSpan rows :=
  fun probe hprobe => hspan probe fun label _ => hprobe label

/-- Spanning is monotone in the label set. -/
theorem SpansOn.mono {size rank : ℕ} {rows : Fin size → Fin rank → ℝ}
    {base bigger : Finset (Fin size)} (hspan : SpansOn rows base) (hsub : base ⊆ bigger) :
    SpansOn rows bigger :=
  fun probe hprobe => hspan probe fun label hlabel => hprobe label (hsub hlabel)

/-! ## Extraction of a small spanning base

More than `rank` vectors in a space of dimension `rank` are dependent, and a
vector with a nonzero coefficient in a vanishing combination can be dropped
without losing the span.  Iterating gives a spanning base of at most `rank`
rows. -/

/-- **One redundant row.**  A spanning family of more than `rank` rows keeps its
span after one row is removed. -/
theorem exists_erase_spansOn {size rank : ℕ} {rows : Fin size → Fin rank → ℝ}
    {base : Finset (Fin size)} (hbig : rank < base.card) (hspan : SpansOn rows base) :
    ∃ drop ∈ base, SpansOn rows (base.erase drop) := by
  classical
  have hdep : ¬ LinearIndependent ℝ
      (fun member : {label : Fin size // label ∈ base} => rows (member : Fin size)) := by
    intro hindep
    have hcard := hindep.fintype_card_le_finrank
    rw [Fintype.card_coe, Module.finrank_fin_fun] at hcard
    omega
  obtain ⟨coeffs, hcombo, member, hmemberNe⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨(member : Fin size), member.2, fun probe hprobe => ?_⟩
  refine hspan probe fun label hlabel => ?_
  rcases eq_or_ne label (member : Fin size) with rfl | hoff
  · have hdot : ∑ other : {label : Fin size // label ∈ base},
        coeffs other * (rows (other : Fin size) ⬝ᵥ probe) = 0 := by
      have hmapped := congrArg (fun vec => vec ⬝ᵥ probe) hcombo
      simpa [sum_dotProduct, smul_dotProduct] using hmapped
    rw [Finset.sum_eq_single member
      (fun other _ hotherNe => by
        rw [hprobe (other : Fin size) (Finset.mem_erase.mpr
          ⟨fun hval => hotherNe (Subtype.ext hval), other.2⟩), mul_zero])
      (fun habsent => absurd (Finset.mem_univ member) habsent)] at hdot
    exact (mul_eq_zero.mp hdot).resolve_left hmemberNe
  · exact hprobe label (Finset.mem_erase.mpr ⟨hoff, hlabel⟩)

/-- **THE SPANNING BASE.**  Every spanning label set contains a spanning label
set of at most `rank` labels.  The budget is the recursion measure. -/
theorem exists_spansOn_card_le {size rank : ℕ} (rows : Fin size → Fin rank → ℝ) (budget : ℕ) :
    ∀ base : Finset (Fin size), base.card ≤ budget → SpansOn rows base →
      ∃ small : Finset (Fin size), small ⊆ base ∧ SpansOn rows small ∧ small.card ≤ rank := by
  induction budget with
  | zero =>
      intro base hcard hspan
      exact ⟨base, subset_rfl, hspan, le_trans hcard (Nat.zero_le rank)⟩
  | succ prevBudget ih =>
      intro base hcard hspan
      rcases le_or_gt base.card rank with hsmall | hbig
      · exact ⟨base, subset_rfl, hspan, hsmall⟩
      · obtain ⟨drop, hdropMem, hdropSpan⟩ := exists_erase_spansOn hbig hspan
        obtain ⟨small, hsub, hsmallSpan, hsmallCard⟩ :=
          ih (base.erase drop)
            (by rw [Finset.card_erase_of_mem hdropMem]; omega) hdropSpan
        exact ⟨small, hsub.trans (Finset.erase_subset _ _), hsmallSpan, hsmallCard⟩

/-- **THE BASE OF A GOOD TUPLE.**  A good tuple has a spanning base of at most
`rank` labels. -/
theorem exists_spanning_base {size rank : ℕ} {rows : Fin size → Fin rank → ℝ}
    (hgood : IsGoodTuple rows) :
    ∃ base : Finset (Fin size), SpansOn rows base ∧ base.card ≤ rank := by
  obtain ⟨base, _, hbaseSpan, hbaseCard⟩ :=
    exists_spansOn_card_le rows size Finset.univ
      (le_of_eq (by simp)) (spansOn_univ_of_rowsSpan hgood.2)
  exact ⟨base, hbaseSpan, hbaseCard⟩

/-! ## The hybrid tuple

At every stage of the schedule some labels sit on the moment curve and the rest
still carry their original rows.  `hybridRows` names that stage, and the whole
schedule is a walk through the finsets of placed labels. -/

/-- The tuple with the labels of `placed` moved onto the moment curve. -/
def hybridRows {size rank : ℕ} (rows : Fin size → Fin rank → ℝ) (params : Fin size → ℝ)
    (placed : Finset (Fin size)) : Fin size → Fin rank → ℝ :=
  fun label => if label ∈ placed then momentPoint rank (params label) else rows label

theorem hybridRows_of_mem {size rank : ℕ} (rows : Fin size → Fin rank → ℝ)
    (params : Fin size → ℝ) {placed : Finset (Fin size)} {label : Fin size}
    (hlabel : label ∈ placed) :
    hybridRows rows params placed label = momentPoint rank (params label) := by
  rw [hybridRows, if_pos hlabel]

theorem hybridRows_of_notMem {size rank : ℕ} (rows : Fin size → Fin rank → ℝ)
    (params : Fin size → ℝ) {placed : Finset (Fin size)} {label : Fin size}
    (hlabel : label ∉ placed) : hybridRows rows params placed label = rows label := by
  rw [hybridRows, if_neg hlabel]

@[simp] theorem hybridRows_empty {size rank : ℕ} (rows : Fin size → Fin rank → ℝ)
    (params : Fin size → ℝ) : hybridRows rows params ∅ = rows := by
  funext label
  rw [hybridRows_of_notMem rows params (Finset.notMem_empty label)]

@[simp] theorem hybridRows_univ {size rank : ℕ} (rows : Fin size → Fin rank → ℝ)
    (params : Fin size → ℝ) :
    hybridRows rows params Finset.univ = fun label => momentPoint rank (params label) := by
  funext label
  rw [hybridRows_of_mem rows params (Finset.mem_univ label)]

/-- Adding one label to the placed set is one `Function.update` — the exact
shape `joinedIn_moveOne` consumes. -/
theorem hybridRows_insert {size rank : ℕ} (rows : Fin size → Fin rank → ℝ)
    (params : Fin size → ℝ) (placed : Finset (Fin size)) (mover : Fin size) :
    hybridRows rows params (insert mover placed)
      = Function.update (hybridRows rows params placed) mover
          (momentPoint rank (params mover)) := by
  classical
  funext label
  rcases eq_or_ne label mover with rfl | hoff
  · rw [hybridRows_of_mem rows params (Finset.mem_insert_self label placed),
      Function.update_self]
  · rw [Function.update_of_ne hoff, hybridRows, hybridRows,
      if_congr (Finset.mem_insert.trans (or_iff_right hoff)) rfl rfl]

/-! ## The two span suppliers

Each step of the schedule needs the rows OTHER than the mover to span.  Phase
one reads that from the untouched base, phase two from the moment points
already placed. -/

/-- **PHASE-ONE SUPPLY.**  While the base is untouched and the mover is outside
it, the base still carries the span. -/
theorem hybridSpan_of_base {size rank : ℕ} {rows : Fin size → Fin rank → ℝ}
    {params : Fin size → ℝ} {base placed : Finset (Fin size)} (hbase : SpansOn rows base)
    (hdisjoint : Disjoint base placed) (mover : Fin size) (hmover : mover ∉ base)
    (probe : Fin rank → ℝ)
    (hprobe : ∀ other, other ≠ mover → hybridRows rows params placed other ⬝ᵥ probe = 0) :
    probe = 0 := by
  refine hbase probe fun label hlabel => ?_
  have hlabelOff : label ∉ placed := Finset.disjoint_left.mp hdisjoint hlabel
  have hlabelNe : label ≠ mover := fun hcollide => hmover (hcollide ▸ hlabel)
  have hrow := hprobe label hlabelNe
  rwa [hybridRows_of_notMem rows params hlabelOff] at hrow

/-- **PHASE-TWO SUPPLY.**  Once `rank` labels sit on the moment curve at
distinct parameters, they span on their own, whatever the mover does. -/
theorem hybridSpan_of_hub {size rank : ℕ} {rows : Fin size → Fin rank → ℝ}
    {params : Fin size → ℝ} {hub placed : Finset (Fin size)}
    (hinjective : Function.Injective params) (hcard : rank ≤ hub.card) (hsub : hub ⊆ placed)
    (mover : Fin size) (hmover : mover ∉ hub) (probe : Fin rank → ℝ)
    (hprobe : ∀ other, other ≠ mover → hybridRows rows params placed other ⬝ᵥ probe = 0) :
    probe = 0 := by
  classical
  refine probe_eq_zero_of_manyMomentPoints
    (index := {label : Fin size // label ∈ hub})
    (params := fun member => params (member : Fin size))
    (fun leftMember rightMember hvalue => Subtype.ext (hinjective hvalue))
    (by rwa [Fintype.card_coe]) fun member => ?_
  have hmemberNe : (member : Fin size) ≠ mover := fun hcollide => hmover (hcollide ▸ member.2)
  have hrow := hprobe (member : Fin size) hmemberNe
  rwa [hybridRows_of_mem rows params (hsub member.2)] at hrow

/-! ## One step of the schedule -/

/-- **ONE PLACED LABEL.**  With the span supplied, moving one label onto the
moment curve is a `JoinedIn` inside the good tuples.  Off-line holds against a
placed row because the parameters are distinct, and against an unplaced row by
the hub hypothesis. -/
theorem joinedIn_hybrid_insert {size rank : ℕ} (hsize : 2 ≤ size) (hrank : 3 ≤ rank)
    {rows : Fin size → Fin rank → ℝ} {params : Fin size → ℝ}
    (hinjective : Function.Injective params)
    (hhub : ∀ label other : Fin size, ∀ ratio : ℝ,
      momentPoint rank (params label) ≠ ratio • rows other)
    {placed : Finset (Fin size)} (hgood : IsGoodTuple (hybridRows rows params placed))
    {mover : Fin size}
    (hspan : ∀ probe : Fin rank → ℝ,
      (∀ other, other ≠ mover → hybridRows rows params placed other ⬝ᵥ probe = 0) → probe = 0) :
    JoinedIn (goodTupleSet size rank) (hybridRows rows params placed)
      (hybridRows rows params (insert mover placed)) := by
  classical
  rw [hybridRows_insert]
  refine joinedIn_moveOne hsize hrank hgood mover ?_ hspan
  intro other hother ratio
  by_cases hmem : other ∈ placed
  · rw [hybridRows_of_mem rows params hmem]
    exact momentPoint_offLine (by omega)
      (fun hvalue => hother (hinjective hvalue).symm) ratio
  · rw [hybridRows_of_notMem rows params hmem]
    exact hhub mover other ratio

/-! ## One phase of the schedule -/

/-- **ONE PHASE.**  With a span supply for every intermediate stage, a whole
block of labels moves onto the moment curve, one label at a time. -/
theorem joinedIn_hybrid_union {size rank : ℕ} (hsize : 2 ≤ size) (hrank : 3 ≤ rank)
    {rows : Fin size → Fin rank → ℝ} {params : Fin size → ℝ}
    (hinjective : Function.Injective params)
    (hhub : ∀ label other : Fin size, ∀ ratio : ℝ,
      momentPoint rank (params label) ≠ ratio • rows other)
    (fixed : Finset (Fin size)) (hgoodFixed : IsGoodTuple (hybridRows rows params fixed))
    (walk : Finset (Fin size))
    (hsupply : ∀ step : Finset (Fin size), step ⊆ walk → ∀ mover ∈ walk, mover ∉ step →
      ∀ probe : Fin rank → ℝ,
        (∀ other, other ≠ mover →
          hybridRows rows params (fixed ∪ step) other ⬝ᵥ probe = 0) → probe = 0) :
    JoinedIn (goodTupleSet size rank) (hybridRows rows params fixed)
      (hybridRows rows params (fixed ∪ walk)) := by
  classical
  induction walk using Finset.induction_on with
  | empty =>
      rw [Finset.union_empty]
      exact JoinedIn.refl hgoodFixed
  | insert mover rest hmoverOff ih =>
      have hstep := ih fun step hstepSub other hotherMem hotherOff =>
        hsupply step (hstepSub.trans (Finset.subset_insert mover rest)) other
          (Finset.mem_insert_of_mem hotherMem) hotherOff
      have hunion : fixed ∪ insert mover rest = insert mover (fixed ∪ rest) := by
        ext label
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [hunion]
      refine hstep.trans (joinedIn_hybrid_insert hsize hrank hinjective hhub
        hstep.target_mem ?_)
      exact hsupply rest (Finset.subset_insert mover rest) mover
        (Finset.mem_insert_self mover rest) hmoverOff

/-! ## The schedule -/

/-- **THE SCHEDULE, PROVED INSIDE THE WINDOW.**  Every good tuple reaches a
moment-curve hub, at every cell with `3 <= rank` and `2 * rank <= size`.  This
is the first of the two Props that `sharpWindowAnchorReach_of_schedule` rests
on, and the window floor is exactly what the two phases consume. -/
theorem goodTupleReachesMomentHub_of_window {size rank : ℕ} (hrank : 3 ≤ rank)
    (hwindow : 2 * rank ≤ size) : GoodTupleReachesMomentHub size rank := by
  classical
  intro rows params hgood hinjective hhub
  have hsize : 2 ≤ size := by omega
  obtain ⟨base, hbaseSpan, hbaseCard⟩ := exists_spanning_base hgood
  have hcomplCard : rank ≤ baseᶜ.card := by
    have hcard : baseᶜ.card = size - base.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hphaseOne : JoinedIn (goodTupleSet size rank) rows (hybridRows rows params baseᶜ) := by
    have hrun := joinedIn_hybrid_union hsize hrank hinjective hhub ∅
      (by rw [hybridRows_empty]; exact hgood) baseᶜ ?_
    · rwa [hybridRows_empty, Finset.empty_union] at hrun
    · intro step hstepSub mover hmoverMem _ probe hprobe
      refine hybridSpan_of_base (params := params) (placed := step) hbaseSpan ?_ mover
        (Finset.mem_compl.mp hmoverMem) probe ?_
      · exact Finset.disjoint_left.mpr fun label hlabel hstep =>
          (Finset.mem_compl.mp (hstepSub hstep)) hlabel
      · rwa [Finset.empty_union] at hprobe
  have hphaseTwo : JoinedIn (goodTupleSet size rank) (hybridRows rows params baseᶜ)
      (hybridRows rows params (baseᶜ ∪ base)) := by
    refine joinedIn_hybrid_union hsize hrank hinjective hhub baseᶜ hphaseOne.target_mem base ?_
    intro step _ mover hmoverMem _ probe hprobe
    exact hybridSpan_of_hub hinjective hcomplCard Finset.subset_union_left mover
      (fun hcompl => (Finset.mem_compl.mp hcompl) hmoverMem) probe hprobe
  have hfull : baseᶜ ∪ base = Finset.univ := by
    rw [Finset.union_comm]
    exact Finset.union_compl base
  rw [hfull, hybridRows_univ] at hphaseTwo
  exact hphaseOne.trans hphaseTwo

/-! ## T1 inside the window, and its consumers -/

/-- **T1, THE TUPLE WALK, AT EVERY WINDOW CELL.**  With the schedule proved,
the good tuples of a window cell are path-connected. -/
theorem goodTupleConnected_of_window {size rank : ℕ} (hrank : 3 ≤ rank)
    (hwindow : 2 * rank ≤ size) : GoodTupleConnected size rank :=
  goodTupleConnected_of_reachesMomentHub (by omega)
    (goodTupleReachesMomentHub_of_window hrank hwindow)

/-- T1 at every cell of the canonical window. -/
theorem goodTupleConnected_of_canonicalWindow {size rank : ℕ} (hrank : 3 ≤ rank)
    (hinside : InductionStep.IsInsideCanonicalWindow size rank) :
    GoodTupleConnected size rank :=
  goodTupleConnected_of_window hrank hinside.1

/-- **THE ANCHOR-REACH OBLIGATION, ON THE WHITENING ALONE.**  The schedule half
is discharged, so the sharp-window statement rests on one Prop per cell. -/
theorem sharpWindowAnchorReach_of_whitening {rank : ℕ} (hrank : 3 ≤ rank)
    (hwhiten : ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
      WhiteningTransferAtRank size rank) :
    ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
      ∃ anchor : WeightedDesign size rank,
        HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor size rank anchor :=
  sharpWindowAnchorReach_of_tupleReach hrank
    (fun _ hbelow _ => goodTupleConnected_of_window hrank hbelow) hwhiten

/-- Route (b) on the window tie and the whitening: the tuple walk has left the
hypothesis list. -/
theorem routeB_target_of_whitening
    (hwindowTie : ∀ rank : ℕ, 3 ≤ rank →
      UniformPositionBridge.ParallelPairAtWindowTieRelative rank)
    (hwhiten : ∀ rank : ℕ, 3 ≤ rank → ∀ size : ℕ,
      InductionStep.IsInsideCanonicalWindow size rank → WhiteningTransferAtRank size rank) :
    ∀ size rank : ℕ, 1 ≤ rank → rank ≤ size → GtzWeighted size rank :=
  routeB_target_of_tupleReach hwindowTie
    (fun _ hrank _ hinside => goodTupleConnected_of_canonicalWindow hrank hinside) hwhiten

/-! ## The good tuples of a window cell are a path-connected set

The `JoinedIn` form is what the schedule produces, and it packages as
path-connectedness of `goodTupleSet`.  The set is nonempty because the identity
rows are good. -/

/-- A diagonal tuple with nonzero entries is good: distinct rows disagree where
one of them vanishes, and the diagonal reads each probe coordinate. -/
theorem isGoodTuple_diagonal {rank : ℕ} {scale : Fin rank → ℝ}
    (hscale : ∀ index, scale index ≠ 0) : IsGoodTuple (Matrix.diagonal scale) := by
  classical
  constructor
  · rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
    have hat := congrFun hparallel dropLabel
    rw [Matrix.diagonal_apply_eq, Pi.smul_apply, Matrix.diagonal_apply_ne _ hdistinct,
      smul_eq_mul, mul_zero] at hat
    exact hscale dropLabel hat
  · intro probe hprobe
    funext index
    have hrow := hprobe index
    rw [dotProduct, Finset.sum_eq_single index
      (fun other _ hother => by
        rw [Matrix.diagonal_apply_ne _ (Ne.symm hother), zero_mul])
      (fun habsent => absurd (Finset.mem_univ index) habsent),
      Matrix.diagonal_apply_eq] at hrow
    exact (mul_eq_zero.mp hrow).resolve_left (hscale index)

theorem isGoodTuple_one {rank : ℕ} :
    IsGoodTuple (1 : Matrix (Fin rank) (Fin rank) ℝ) := by
  have hdiagonal := isGoodTuple_diagonal (scale := fun _ : Fin rank => (1 : ℝ))
    fun _ => one_ne_zero
  rwa [Matrix.diagonal_one] at hdiagonal

/-- The moment curve at distinct parameters is a good tuple whenever the rows
outnumber the rank. -/
theorem isGoodTuple_momentCurve {size rank : ℕ} (hrank : 2 ≤ rank) (hsize : rank ≤ size)
    {params : Fin size → ℝ} (hinjective : Function.Injective params) :
    IsGoodTuple (fun label => momentPoint rank (params label)) := by
  constructor
  · rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
    exact momentPoint_offLine hrank
      (fun hvalue => hdistinct (hinjective hvalue).symm) ratio hparallel
  · intro probe hprobe
    exact probe_eq_zero_of_manyMomentPoints hinjective (by rwa [Fintype.card_fin]) hprobe

/-- The label index, cast to a real parameter, is injective. -/
theorem injective_labelParam {size : ℕ} :
    Function.Injective fun label : Fin size => ((label : ℕ) : ℝ) := by
  intro leftLabel rightLabel hvalue
  exact Fin.ext (Nat.cast_injective hvalue)

/-- A global path of good tuples restricts to a `JoinedIn` witness. -/
theorem joinedIn_of_goodTupleConnected {size rank : ℕ}
    (hconnect : GoodTupleConnected size rank) {rowsStart rowsEnd : Fin size → Fin rank → ℝ}
    (hgoodStart : IsGoodTuple rowsStart) (hgoodEnd : IsGoodTuple rowsEnd) :
    JoinedIn (goodTupleSet size rank) rowsStart rowsEnd := by
  obtain ⟨tuplePath, hcont, hstart, hend, hgood⟩ := hconnect rowsStart rowsEnd hgoodStart hgoodEnd
  exact ⟨⟨⟨fun time => tuplePath (time : ℝ), hcont.comp continuous_subtype_val⟩,
    by simpa using hstart, by simpa using hend⟩, fun time => hgood _⟩

/-- **THE GOOD TUPLES OF A WINDOW CELL ARE A PATH-CONNECTED SET.**  The base
point is the moment curve at the label indices. -/
theorem isPathConnected_goodTupleSet {size rank : ℕ} (hrank : 3 ≤ rank)
    (hwindow : 2 * rank ≤ size) : IsPathConnected (goodTupleSet size rank) := by
  have hbase : IsGoodTuple (fun label : Fin size => momentPoint rank ((label : ℕ) : ℝ)) :=
    isGoodTuple_momentCurve (by omega) (by omega) injective_labelParam
  exact ⟨_, hbase, fun rows hrows =>
    joinedIn_of_goodTupleConnected (goodTupleConnected_of_window hrank hwindow) hbase hrows⟩

/-! ## The window floor is not decoration

At `size = rank` a good tuple is an invertible matrix, and the determinant
cannot change sign along a path of good tuples.  So the tuple walk is FALSE
there, and no schedule of any kind can reach it. -/

/-- A square spanning tuple is invertible. -/
theorem det_ne_zero_of_rowsSpan {rank : ℕ} {rows : Matrix (Fin rank) (Fin rank) ℝ}
    (hspan : RowsSpan rows) : rows.det ≠ 0 := by
  intro hzero
  obtain ⟨probe, hprobeNe, hkill⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  exact hprobeNe (hspan probe fun label => by
    simpa [Matrix.mulVec] using congrFun hkill label)

/-- **THE TUPLE WALK IS FALSE AT `size = rank`.**  The identity and the identity
with one sign flipped are both good, and their determinants have opposite
signs, so no path of good tuples joins them. -/
theorem not_goodTupleConnected_self {rank : ℕ} (hrank : 1 ≤ rank) :
    ¬ GoodTupleConnected rank rank := by
  classical
  have hzeroLt : (0 : ℕ) < rank := by omega
  have hflipNe : ∀ index : Fin rank,
      (if index = (⟨0, hzeroLt⟩ : Fin rank) then (-1 : ℝ) else 1) ≠ 0 := by
    intro index
    by_cases hindex : index = (⟨0, hzeroLt⟩ : Fin rank) <;> simp [hindex]
  intro hconnect
  obtain ⟨tuplePath, hcont, hstart, hend, hgood⟩ :=
    hconnect (Matrix.diagonal (fun _ : Fin rank => (1 : ℝ)))
      (Matrix.diagonal fun index => if index = (⟨0, hzeroLt⟩ : Fin rank) then (-1 : ℝ) else 1)
      (isGoodTuple_diagonal fun _ => one_ne_zero) (isGoodTuple_diagonal hflipNe)
  have hdetCont : Continuous fun time => Matrix.det (tuplePath time) := hcont.matrix_det
  have hdetStart : Matrix.det (tuplePath 0) = 1 := by
    rw [hstart, Matrix.det_diagonal, Finset.prod_const_one]
  have hdetEnd : Matrix.det (tuplePath 1) = -1 := by
    rw [hend, Matrix.det_diagonal,
      Finset.prod_ite_eq' Finset.univ (⟨0, hzeroLt⟩ : Fin rank) (fun _ => (-1 : ℝ))]
    simp
  have hreach : (0 : ℝ) ∈ (fun time => Matrix.det (tuplePath time)) '' Set.Icc 0 1 := by
    refine intermediate_value_Icc' zero_le_one hdetCont.continuousOn ?_
    rw [hdetStart, hdetEnd]
    exact ⟨by norm_num, by norm_num⟩
  obtain ⟨time, _, hzero⟩ := hreach
  exact det_ne_zero_of_rowsSpan (hgood time).2 hzero

/-! ## Parity against the landed rank-three walk

The rank-three cell `(6,3)` and the rank-four cell `(8,4)` both sit on the
window floor, so the general schedule covers them.  At `(6,3)` the tree already
owns the walk (`exists_goodTuple_path`), and the two agree. -/

/-- The general schedule reproves T1 at `(6,3)`. -/
theorem goodTupleConnected_six_three_ofSchedule : GoodTupleConnected 6 3 :=
  goodTupleConnected_of_window (by norm_num) (by norm_num)

/-- T1 at the rank-three top cell `(7,3)`. -/
theorem goodTupleConnected_seven_three : GoodTupleConnected 7 3 :=
  goodTupleConnected_of_window (by norm_num) (by norm_num)

/-- T1 at the rank-four window floor `(8,4)`. -/
theorem goodTupleConnected_eight_four : GoodTupleConnected 8 4 :=
  goodTupleConnected_of_window (by norm_num) (by norm_num)

/-- T1 at the rank-four top cell `(11,4)`. -/
theorem goodTupleConnected_eleven_four : GoodTupleConnected 11 4 :=
  goodTupleConnected_of_window (by norm_num) (by norm_num)

/-- T1 at the rank-five window floor `(10,5)`. -/
theorem goodTupleConnected_ten_five : GoodTupleConnected 10 5 :=
  goodTupleConnected_of_window (by norm_num) (by norm_num)

end GeneralRankReach
end Gtz
