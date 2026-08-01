/-
# The COVERING form of `Gtz.ChartGtz`, and its down-set structure

Route E's residue.  `Gtz.chartGtz_iff_gtzWeighted`
(`Gtz/Reduction/ChartPointFactorisation.lean:402`) makes the chart statement and
the weighted statement interchangeable.  A `Gtz.ChartPoint` bundles a projection
with a weight; exchanging the two quantifiers turns `Gtz.ChartGtz` into a
statement about ONE projection at a time:

    GtzWeighted size rank
      <->  for every symmetric idempotent `P` of trace `rank`, the sets
           K_C = { t in the simplex : `RawDominates P t C` },  C of card `rank`,
           COVER the simplex.

`Gtz.RawDominates` is `Gtz.ChartDominates` with the bundle taken apart, so the
chart can be held fixed while the weight moves.  The two agree by `Iff.rfl`
(`Gtz.chartDominates_iff_rawDominates`).

## What the covering form buys, and it is entirely structural

`K_C` depends only on the coordinates IN `C` and is a DOWN-SET there
(`Gtz.rawDominates_of_weight_le`), so the no-domination region is an UP-SET and
the equality constraint `sum t = 1` can be dropped:
`Gtz.coversSimplex_iff_coversSubunit` replaces the simplex by the corner
`{t >= 0, sum t <= 1}`.  Three further laws pin the boundary:

* `Gtz.rawDominates_of_weight_eq_zero` -- a selection carrying NO weight always
  dominates.  So `K_C` contains the face of the simplex spanned by the
  COMPLEMENT of `C`; that is the KKM boundary condition, available on faces of
  dimension `size - rank - 1` and no higher.
* `Gtz.not_rawDominates_of_chart_lt_weight` -- an atom whose weight exceeds its
  chart diagonal is DEAD: no selection through it dominates.
* `Gtz.card_dead_add_rank_le` -- at most `size - rank` atoms can be dead at once.
  This is the first place idempotence does real work: it supplies
  `chart c c <= 1` (`Gtz.chart_diag_le_one`), and with `trace = rank` and
  `sum t = 1` the count follows.  At `(6,3)` it says at most THREE atoms are
  dead, hence at least three are alive, hence at least one selection is alive.

## The domination criterion this yields

`Gtz.rawDominates_of_sum_compl_nonpos`: **if the complement of a selection
carries non-positive total gap `sum_{c not in C} (P_cc - t_c) <= 0`, that
selection dominates.**  Unconditional, field-blind, no smaller rung consumed,
every `(size, rank)`.  Its two ingredients are

  * `Gtz.dotProduct_le_sum_diag_mul_of_posSemidef` -- for a positive
    semidefinite `B` and a probe supported on `C`,
    `x . (B x) <= (sum_{c in C} B_cc) (x . x)`.  Proved from the two-by-two
    minor bound and Cauchy-Schwarz, with no eigenvalue.
  * `I - P` is positive semidefinite for a projection, so the chart's Rayleigh
    quotient is bounded BELOW by `(trace P[C] - (rank - 1)) |x|^2`.

DESIGN-SIDE READING, and the honest scope.  With `s_c = atomShare` and
`t_c = weight`, `s_c - t_c = t_c (leverage_c - 1)`, so the criterion reads "some
`rank`-subset carries the entire heavy excess".  Since the total excess is
`rank - 1 > 0`, on an ALL-HEAVY design every complement carries a strictly
positive share of it and the criterion NEVER fires.  It is therefore a
light-atom criterion and closes no part of the open cell; the shipped
`Gtz.exists_dominating_triple_of_light_atom_sixThree` already covers the
`(6,3)` instance by a different and stronger route (through `GtzWeighted 5 3`).
What is new here is that the chart-side statement is UNCONDITIONAL and
size-generic: it consumes no smaller rung at all.

## NOT here

No claim that the covering form is easier than the weighted form -- it is the
same statement, and `Gtz.gtzWeighted_iff_forall_coversSimplex` says so.  No
KKM result is invoked and none applies: the boundary condition above lives only
on faces of dimension `size - rank - 1`, three short of the top at `(6,3)`, and
twenty closed convex down-sets each containing the complementary face need not
cover -- `K_C = {t : sum_{c in C} t_c <= 2/5}` at `(6,3)` satisfies every one of
those hypotheses and misses the barycentre.  So the covering language is a
faithful restatement, not a lever.
-/
import Mathlib
import Gtz.Reduction.CompactnessReduction
import Gtz.Reduction.ChartPointFactorisation
import Gtz.Reduction.MaximalVolume
import Gtz.Quantitative.ChartHadamard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open scoped Matrix

variable {size rank : ℕ}

/-! ## The unbundled domination predicate -/

/-- Domination at a raw `(chart, weight)` pair: `Gtz.ChartDominates` with the
`Gtz.ChartPoint` bundle taken apart, so the chart can be held fixed while the
weight moves over the simplex. -/
def RawDominates (chart : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
    (selected : Finset (Fin size)) : Prop :=
  ∀ probe : Fin size → ℝ, (∀ atomIndex, atomIndex ∉ selected → probe atomIndex = 0) →
    0 ≤ probe ⬝ᵥ ((chart - Matrix.diagonal weight) *ᵥ probe)

/-- The unbundling is definitional. -/
theorem chartDominates_iff_rawDominates (point : ChartPoint size rank)
    (selected : Finset (Fin size)) :
    ChartDominates point selected ↔ RawDominates point.chart point.weight selected :=
  Iff.rfl

/-- The gap's Rayleigh quotient, split into its chart part and its weight part. -/
theorem dotProduct_gap_mulVec (chart : Matrix (Fin size) (Fin size) ℝ)
    (weight probe : Fin size → ℝ) :
    probe ⬝ᵥ ((chart - Matrix.diagonal weight) *ᵥ probe)
      = probe ⬝ᵥ (chart *ᵥ probe) - ∑ atomIndex, weight atomIndex * probe atomIndex ^ 2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub]
  congr 1
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-! ## The covering form -/

/-- **THE COVERING PREDICATE.**  At a FIXED chart, the `rank`-subset
spectrahedra cover the closed simplex. -/
def CoversSimplex (chart : Matrix (Fin size) (Fin size) ℝ) (rank : ℕ) : Prop :=
  ∀ weight : Fin size → ℝ, (∀ atomIndex, 0 ≤ weight atomIndex) →
    (∑ atomIndex, weight atomIndex = 1) →
      ∃ selected : Finset (Fin size), selected.card = rank ∧ RawDominates chart weight selected

/-- **THE QUANTIFIER EXCHANGE.**  `Gtz.ChartGtz` is the covering statement, one
projection at a time. -/
theorem chartGtz_iff_forall_coversSimplex (size rank : ℕ) :
    ChartGtz size rank ↔ ∀ chart : Matrix (Fin size) (Fin size) ℝ, chartᵀ = chart →
      chart * chart = chart → Matrix.trace chart = (rank : ℝ) → CoversSimplex chart rank := by
  constructor
  · intro hchartGtz chart hsymmetric hidempotent htrace weight hnonneg hsum
    exact hchartGtz ⟨chart, weight, hsymmetric, hidempotent, htrace, hnonneg, hsum⟩
  · intro hcovers point
    exact hcovers point.chart point.isSymmetric point.isIdempotent point.hasTraceRank
      point.weight point.weight_nonneg point.weight_sum_one

/-- **THE COVERING FORM OF THE WEIGHTED CONJECTURE**, through the shipped
`Gtz.chartGtz_iff_gtzWeighted`. -/
theorem gtzWeighted_iff_forall_coversSimplex (size rank : ℕ) :
    GtzWeighted size rank ↔ ∀ chart : Matrix (Fin size) (Fin size) ℝ, chartᵀ = chart →
      chart * chart = chart → Matrix.trace chart = (rank : ℝ) → CoversSimplex chart rank :=
  (chartGtz_iff_gtzWeighted size rank).symm.trans (chartGtz_iff_forall_coversSimplex size rank)

/-- The covering form of the open cell. -/
theorem gtzWeighted_six_three_iff_forall_coversSimplex :
    GtzWeighted 6 3 ↔ ∀ chart : Matrix (Fin 6) (Fin 6) ℝ, chartᵀ = chart →
      chart * chart = chart → Matrix.trace chart = (3 : ℝ) → CoversSimplex chart 3 :=
  gtzWeighted_iff_forall_coversSimplex 6 3

/-! ## The down-set law and its consequences -/

/-- **THE DOWN-SET LAW.**  Domination is monotone DOWNWARD in the weight, on the
selection: lowering the weight of a selected atom can only help.  Hence each
`K_C` is a down-set in the `C` coordinates and the no-domination region is an
UP-SET. -/
theorem rawDominates_of_weight_le {chart : Matrix (Fin size) (Fin size) ℝ}
    {weight lowerWeight : Fin size → ℝ} {selected : Finset (Fin size)}
    (hle : ∀ atomIndex ∈ selected, lowerWeight atomIndex ≤ weight atomIndex)
    (hdominates : RawDominates chart weight selected) :
    RawDominates chart lowerWeight selected := by
  intro probe hsupport
  have hsplitLower := dotProduct_gap_mulVec chart lowerWeight probe
  have hsplitUpper := dotProduct_gap_mulVec chart weight probe
  have hupper := hdominates probe hsupport
  have hterms : ∑ atomIndex, lowerWeight atomIndex * probe atomIndex ^ 2
      ≤ ∑ atomIndex, weight atomIndex * probe atomIndex ^ 2 := by
    refine Finset.sum_le_sum fun atomIndex _ => ?_
    by_cases hmember : atomIndex ∈ selected
    · exact mul_le_mul_of_nonneg_right (hle atomIndex hmember) (sq_nonneg _)
    · rw [hsupport atomIndex hmember]; simp
  rw [hsplitLower]
  rw [hsplitUpper] at hupper
  linarith

/-- **THE FACE LAW.**  A selection carrying no weight always dominates, because
the chart of a projection is positive semidefinite.  So `K_C` contains the face
of the simplex spanned by the complement of `C`. -/
theorem rawDominates_of_weight_eq_zero {chart : Matrix (Fin size) (Fin size) ℝ}
    {weight : Fin size → ℝ} {selected : Finset (Fin size)}
    (hsymmetric : chartᵀ = chart) (hidempotent : chart * chart = chart)
    (hzero : ∀ atomIndex ∈ selected, weight atomIndex = 0) :
    RawDominates chart weight selected := by
  intro probe hsupport
  have hpsd : 0 ≤ probe ⬝ᵥ (chart *ᵥ probe) := by
    have hsplit : probe ⬝ᵥ (chart *ᵥ probe) = (chart *ᵥ probe) ⬝ᵥ (chart *ᵥ probe) := by
      conv_lhs => rw [show chart = chartᵀ * chart by rw [hsymmetric, hidempotent]]
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [hsplit]
    exact dotProduct_self_nonneg _
  have hweightTerm : ∑ atomIndex, weight atomIndex * probe atomIndex ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun atomIndex _ => ?_
    by_cases hmember : atomIndex ∈ selected
    · rw [hzero atomIndex hmember]; ring
    · rw [hsupport atomIndex hmember]; ring
  rw [dotProduct_gap_mulVec, hweightTerm, sub_zero]
  exact hpsd

/-- **THE DEAD-ATOM LAW.**  An atom whose weight exceeds its chart diagonal
kills every selection through it. -/
theorem not_rawDominates_of_chart_lt_weight {chart : Matrix (Fin size) (Fin size) ℝ}
    {weight : Fin size → ℝ} {selected : Finset (Fin size)} {deadIndex : Fin size}
    (hmember : deadIndex ∈ selected) (hdead : chart deadIndex deadIndex < weight deadIndex) :
    ¬ RawDominates chart weight selected := by
  intro hdominates
  have hspike := hdominates (Pi.single deadIndex (1 : ℝ) : Fin size → ℝ)
    (fun atomIndex hnot => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hnot hmember)
  rw [dotProduct_gap_mulVec] at hspike
  have hchartTerm : (Pi.single deadIndex (1 : ℝ) : Fin size → ℝ)
        ⬝ᵥ (chart *ᵥ (Pi.single deadIndex (1 : ℝ) : Fin size → ℝ))
      = chart deadIndex deadIndex := by
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq']
  have hweightTerm : ∑ atomIndex, weight atomIndex
        * (Pi.single deadIndex (1 : ℝ) : Fin size → ℝ) atomIndex ^ 2
      = weight deadIndex := by
    rw [Finset.sum_eq_single deadIndex]
    · simp
    · intro other _ hne; rw [Pi.single_eq_of_ne hne]; ring
    · intro hnot; exact absurd (Finset.mem_univ deadIndex) hnot
  rw [hchartTerm, hweightTerm] at hspike
  linarith

/-! ## The sub-unit reduction -/

/-- **THE UP-SET THEOREM.**  Because each `K_C` is a down-set, the equality
constraint `sum t = 1` may be relaxed to `sum t <= 1`: the covering of the
simplex is equivalent to the covering of the whole corner below it. -/
theorem coversSimplex_iff_coversSubunit [NeZero size]
    {chart : Matrix (Fin size) (Fin size) ℝ} :
    CoversSimplex chart rank ↔ ∀ weight : Fin size → ℝ, (∀ atomIndex, 0 ≤ weight atomIndex) →
      (∑ atomIndex, weight atomIndex ≤ 1) →
        ∃ selected : Finset (Fin size), selected.card = rank
          ∧ RawDominates chart weight selected := by
  constructor
  · intro hcovers weight hnonneg hsum
    classical
    set anchor : Fin size := ⟨0, Nat.pos_of_ne_zero (NeZero.ne size)⟩ with hanchor
    set deficit : ℝ := 1 - ∑ atomIndex, weight atomIndex with hdeficit
    have hdeficitNonneg : 0 ≤ deficit := by rw [hdeficit]; linarith
    set spike : Fin size → ℝ := (Pi.single anchor deficit : Fin size → ℝ) with hspike
    set liftedWeight : Fin size → ℝ := weight + spike with hlifted
    have hliftedNonneg : ∀ atomIndex, 0 ≤ liftedWeight atomIndex := by
      intro atomIndex
      rw [hlifted]
      refine add_nonneg (hnonneg atomIndex) ?_
      rw [hspike]
      by_cases hsame : atomIndex = anchor
      · subst hsame; simpa using hdeficitNonneg
      · rw [Pi.single_eq_of_ne hsame]
    have hliftedSum : ∑ atomIndex, liftedWeight atomIndex = 1 := by
      rw [hlifted]
      simp only [Pi.add_apply, Finset.sum_add_distrib, hspike]
      rw [Finset.sum_pi_single' anchor deficit Finset.univ, if_pos (Finset.mem_univ anchor)]
      rw [hdeficit]; ring
    obtain ⟨selected, hcard, hdominates⟩ := hcovers liftedWeight hliftedNonneg hliftedSum
    refine ⟨selected, hcard, rawDominates_of_weight_le (fun atomIndex _ => ?_) hdominates⟩
    rw [hlifted]
    have hspikeNonneg : 0 ≤ spike atomIndex := by
      rw [hspike]
      by_cases hsame : atomIndex = anchor
      · subst hsame; simpa using hdeficitNonneg
      · rw [Pi.single_eq_of_ne hsame]
    simp only [Pi.add_apply]
    linarith
  · intro hsub weight hnonneg hsum
    exact hsub weight hnonneg (le_of_eq hsum)

/-! ## Idempotence enters: the dead-atom count

The harvested prototype opened this section with two lemmas of its own, a symmetry
reader and a row-square identity.  Both were already shipped, under names a search
for the prototype's own names could not have found:

* its `chart_apply_comm` is `Gtz.projection_apply_comm` (ChartHadamard.lean:187),
  character-for-character including the proof;
* its `chart_diag_eq_sum_sq` is `Gtz.sum_sq_projectionRow_eq_diagonal`
  (ChartHadamard.lean:197), the same identity read in the other direction and with
  `x ^ 2` in place of `x * x`.

Both are gone; `Gtz.Quantitative.ChartHadamard` is imported and the one lemma that
was genuinely absent is stated on top of the shipped pair. -/

/-- **The chart diagonal of a symmetric idempotent is at most one.**  The shipped
`Gtz.chartPoint_diag_le_one` (ChartAttainment.lean:279) is the same bound for a
bundled `Gtz.ChartPoint`, reached through the chart-domain entry bound.  This is the
RAW form: it asks only symmetry and idempotence, carries no trace hypothesis and no
bundle, which is what the covering argument below needs, since it moves the weight
while holding the chart fixed. -/
theorem chart_diag_le_one {chart : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : chartᵀ = chart) (hidempotent : chart * chart = chart)
    (atomIndex : Fin size) : chart atomIndex atomIndex ≤ 1 := by
  have hexpand := sum_sq_projectionRow_eq_diagonal hsymmetric hidempotent atomIndex
  have hnonneg : 0 ≤ chart atomIndex atomIndex := by
    rw [← hexpand]; exact Finset.sum_nonneg fun other _ => sq_nonneg _
  have hsquareLe : chart atomIndex atomIndex ^ 2 ≤ chart atomIndex atomIndex := by
    conv_rhs => rw [← hexpand]
    exact Finset.single_le_sum
      (f := fun other => chart atomIndex other ^ 2)
      (fun other _ => sq_nonneg _) (Finset.mem_univ atomIndex)
  nlinarith

/-- **AT MOST `size - rank` ATOMS ARE DEAD.**  The first place idempotence does
real work in the covering picture: it gives `chart c c <= 1`, and with
`trace chart = rank` and `sum weight = 1` the count follows.  At `(6,3)` at most
three atoms are dead, so at least three are alive and at least one selection is
alive. -/
theorem card_dead_add_rank_le {chart : Matrix (Fin size) (Fin size) ℝ}
    {weight : Fin size → ℝ} (hsymmetric : chartᵀ = chart) (hidempotent : chart * chart = chart)
    (htrace : Matrix.trace chart = (rank : ℝ)) (hnonneg : ∀ atomIndex, 0 ≤ weight atomIndex)
    (hsum : ∑ atomIndex, weight atomIndex = 1) :
    (Finset.univ.filter fun atomIndex => chart atomIndex atomIndex < weight atomIndex).card
      + rank ≤ size := by
  classical
  set deadSet := Finset.univ.filter fun atomIndex => chart atomIndex atomIndex < weight atomIndex
    with hdeadSet
  -- the dead set's weight exceeds its chart diagonal, and is at most one
  have hweightBound : ∑ atomIndex ∈ deadSet, weight atomIndex ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun atomIndex _ _ => hnonneg atomIndex
  -- the complement's chart diagonal is at most its cardinality
  have hcomplBound : ∑ atomIndex ∈ deadSetᶜ, chart atomIndex atomIndex ≤ (deadSetᶜ.card : ℝ) := by
    calc ∑ atomIndex ∈ deadSetᶜ, chart atomIndex atomIndex
        ≤ ∑ _atomIndex ∈ deadSetᶜ, (1 : ℝ) :=
          Finset.sum_le_sum fun atomIndex _ => chart_diag_le_one hsymmetric hidempotent atomIndex
      _ = (deadSetᶜ.card : ℝ) := by simp
  have hsplit : ∑ atomIndex ∈ deadSet, chart atomIndex atomIndex
      + ∑ atomIndex ∈ deadSetᶜ, chart atomIndex atomIndex = (rank : ℝ) := by
    rw [Finset.sum_add_sum_compl]
    exact htrace
  have hcardLe : deadSet.card ≤ size := by
    simpa using Finset.card_le_univ deadSet
  have hcards : deadSet.card + deadSetᶜ.card = size := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hcardsReal : (deadSet.card : ℝ) + (deadSetᶜ.card : ℝ) = (size : ℝ) := by
    have : ((deadSet.card + deadSetᶜ.card : ℕ) : ℝ) = ((size : ℕ) : ℝ) := by rw [hcards]
    push_cast at this
    exact this
  -- the empty and nonempty dead sets are treated apart: only the nonempty one
  -- has the STRICT inequality that gains the last unit
  rcases Finset.eq_empty_or_nonempty deadSet with hempty | hnonempty
  · have hzero : deadSet.card = 0 := by rw [hempty]; rfl
    have hcardZero : (deadSet.card : ℝ) = 0 := by rw [hzero]; norm_num
    have hsumZero : ∑ atomIndex ∈ deadSet, chart atomIndex atomIndex = 0 := by
      rw [hempty]; simp
    have hrankLe : (rank : ℝ) ≤ (size : ℝ) := by linarith
    have : rank ≤ size := by exact_mod_cast hrankLe
    omega
  · have hdiagStrict : ∑ atomIndex ∈ deadSet, chart atomIndex atomIndex
        < ∑ atomIndex ∈ deadSet, weight atomIndex :=
      Finset.sum_lt_sum_of_nonempty hnonempty fun atomIndex hmember =>
        (Finset.mem_filter.mp hmember).2
    have hstrictReal : (deadSet.card : ℝ) + (rank : ℝ) < (size : ℝ) + 1 := by linarith
    have hstrict : deadSet.card + rank < size + 1 := by
      have hcast : ((deadSet.card + rank : ℕ) : ℝ) < ((size + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast hcast
    omega


/-! ## The diagonal-restricted trace bound and the complement-gap criterion -/

/-- **THE DIAGONAL-RESTRICTED TRACE BOUND.**  For a positive semidefinite `form`
and a probe supported on `selected`, the Rayleigh quotient is capped by the sum
of the diagonal entries OVER `selected` alone -- not by the whole trace.  Two
ingredients, no eigenvalue: the two-by-two minor bound
`Gtz.sq_le_mul_diag_of_posSemidef` and Cauchy-Schwarz. -/
theorem dotProduct_le_sum_diag_mul_of_posSemidef {form : Matrix (Fin size) (Fin size) ℝ}
    (hpsd : form.PosSemidef) {selected : Finset (Fin size)} {probe : Fin size → ℝ}
    (hsupport : ∀ atomIndex, atomIndex ∉ selected → probe atomIndex = 0) :
    probe ⬝ᵥ (form *ᵥ probe)
      ≤ (∑ atomIndex ∈ selected, form atomIndex atomIndex) * (probe ⬝ᵥ probe) := by
  classical
  have hdiagNonneg : ∀ atomIndex, 0 ≤ form atomIndex atomIndex := fun atomIndex => by
    have hminor : (0 : ℝ) ≤ (form.submatrix ![atomIndex] ![atomIndex]).det :=
      (hpsd.submatrix _).det_nonneg
    rwa [Matrix.det_fin_one, Matrix.submatrix_apply, Matrix.cons_val_fin_one] at hminor
  -- entrywise bound by the geometric mean of the diagonal
  have hentry : ∀ rowIndex colIndex : Fin size,
      |form rowIndex colIndex| ≤ Real.sqrt (form rowIndex rowIndex)
        * Real.sqrt (form colIndex colIndex) := by
    intro rowIndex colIndex
    have hminor := sq_le_mul_diag_of_posSemidef hpsd rowIndex colIndex
    have hsqrtMul : Real.sqrt (form rowIndex rowIndex) * Real.sqrt (form colIndex colIndex)
        = Real.sqrt (form rowIndex rowIndex * form colIndex colIndex) :=
      (Real.sqrt_mul (hdiagNonneg rowIndex) _).symm
    rw [hsqrtMul, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hminor
  -- the double sum, restricted to the support
  have hquad : probe ⬝ᵥ (form *ᵥ probe)
      = ∑ rowIndex ∈ selected, ∑ colIndex ∈ selected,
          probe rowIndex * form rowIndex colIndex * probe colIndex := by
    rw [dotProduct]
    rw [← Finset.sum_subset (Finset.subset_univ selected)
      (fun rowIndex _ hnot => by rw [hsupport rowIndex hnot]; ring)]
    refine Finset.sum_congr rfl fun rowIndex _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.subset_univ selected)
      (fun colIndex _ hnot => by rw [hsupport colIndex hnot]; ring)]
    exact Finset.sum_congr rfl fun colIndex _ => by ring
  have hbound : ∑ rowIndex ∈ selected, ∑ colIndex ∈ selected,
        probe rowIndex * form rowIndex colIndex * probe colIndex
      ≤ (∑ atomIndex ∈ selected, |probe atomIndex| * Real.sqrt (form atomIndex atomIndex)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun rowIndex _ => Finset.sum_le_sum fun colIndex _ => ?_
    calc probe rowIndex * form rowIndex colIndex * probe colIndex
        ≤ |probe rowIndex * form rowIndex colIndex * probe colIndex| := le_abs_self _
      _ = |probe rowIndex| * |form rowIndex colIndex| * |probe colIndex| := by
          rw [abs_mul, abs_mul]
      _ ≤ |probe rowIndex| * (Real.sqrt (form rowIndex rowIndex)
            * Real.sqrt (form colIndex colIndex)) * |probe colIndex| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hentry rowIndex colIndex) (abs_nonneg _))
            (abs_nonneg _)
      _ = (|probe rowIndex| * Real.sqrt (form rowIndex rowIndex))
            * (|probe colIndex| * Real.sqrt (form colIndex colIndex)) := by ring
  have hcauchy : (∑ atomIndex ∈ selected, |probe atomIndex|
        * Real.sqrt (form atomIndex atomIndex)) ^ 2
      ≤ (∑ atomIndex ∈ selected, |probe atomIndex| ^ 2)
        * (∑ atomIndex ∈ selected, Real.sqrt (form atomIndex atomIndex) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq selected (fun atomIndex => |probe atomIndex|)
      (fun atomIndex => Real.sqrt (form atomIndex atomIndex))
  have hsqrtSq : ∑ atomIndex ∈ selected, Real.sqrt (form atomIndex atomIndex) ^ 2
      = ∑ atomIndex ∈ selected, form atomIndex atomIndex :=
    Finset.sum_congr rfl fun atomIndex _ => Real.sq_sqrt (hdiagNonneg atomIndex)
  have hprobeSq : ∑ atomIndex ∈ selected, |probe atomIndex| ^ 2 = probe ⬝ᵥ probe := by
    rw [dotProduct_self_eq_sum_sq]
    rw [← Finset.sum_subset (Finset.subset_univ selected)
      (fun atomIndex _ hnot => by rw [hsupport atomIndex hnot]; ring)]
    exact Finset.sum_congr rfl fun atomIndex _ => sq_abs _
  rw [hquad]
  calc ∑ rowIndex ∈ selected, ∑ colIndex ∈ selected,
        probe rowIndex * form rowIndex colIndex * probe colIndex
      ≤ (∑ atomIndex ∈ selected, |probe atomIndex|
          * Real.sqrt (form atomIndex atomIndex)) ^ 2 := hbound
    _ ≤ (∑ atomIndex ∈ selected, |probe atomIndex| ^ 2)
          * (∑ atomIndex ∈ selected, Real.sqrt (form atomIndex atomIndex) ^ 2) := hcauchy
    _ = (∑ atomIndex ∈ selected, form atomIndex atomIndex) * (probe ⬝ᵥ probe) := by
        rw [hsqrtSq, hprobeSq]; ring

/-- **THE COMPLEMENT-GAP DOMINATION CRITERION.**  If the complement of a
`rank`-selection carries non-positive total gap, that selection dominates.
Unconditional, field-blind, no smaller rung consumed, every `(size, rank)`.

Design-side this reads "some `rank`-subset carries the entire heavy excess",
since `chart c c - weight c = weight c * (leverage c - 1)`.  On an ALL-HEAVY
design every complement carries a strictly positive share of the total excess
`rank - 1`, so the criterion never fires there and closes no part of the open
cell -- see the module header. -/
theorem rawDominates_of_sum_compl_nonpos {chart : Matrix (Fin size) (Fin size) ℝ}
    {weight : Fin size → ℝ} {selected : Finset (Fin size)}
    (hsymmetric : chartᵀ = chart) (hidempotent : chart * chart = chart)
    (htrace : Matrix.trace chart = (rank : ℝ)) (hcard : selected.card = rank)
    (hnonneg : ∀ atomIndex, 0 ≤ weight atomIndex)
    (hsum : ∑ atomIndex, weight atomIndex = 1)
    (hgap : ∑ atomIndex ∈ selectedᶜ, (chart atomIndex atomIndex - weight atomIndex) ≤ 0) :
    RawDominates chart weight selected := by
  classical
  intro probe hsupport
  rw [dotProduct_gap_mulVec]
  set coChart : Matrix (Fin size) (Fin size) ℝ := 1 - chart with hcoChart
  have hcoSymm : coChartᵀ = coChart := by
    rw [hcoChart, Matrix.transpose_sub, Matrix.transpose_one, hsymmetric]
  have hcoIdem : coChart * coChart = coChart := by
    rw [hcoChart]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hidempotent]
    abel
  have hcoPsd : coChart.PosSemidef := by
    have hfactor : coChart = coChartᴴ * coChart := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, hcoSymm, hcoIdem]
    rw [hfactor]
    exact Matrix.posSemidef_conjTranspose_mul_self coChart
  have hcoDiag : ∀ atomIndex, coChart atomIndex atomIndex = 1 - chart atomIndex atomIndex := by
    intro atomIndex
    rw [hcoChart, Matrix.sub_apply, Matrix.one_apply_eq]
  -- the chart's Rayleigh quotient, bounded BELOW through the complementary projection
  have hsplitCo : probe ⬝ᵥ (coChart *ᵥ probe)
      = probe ⬝ᵥ probe - probe ⬝ᵥ (chart *ᵥ probe) := by
    rw [hcoChart, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
  have hcap := dotProduct_le_sum_diag_mul_of_posSemidef hcoPsd hsupport
  have hcoSum : ∑ atomIndex ∈ selected, coChart atomIndex atomIndex
      = (rank : ℝ) - ∑ atomIndex ∈ selected, chart atomIndex atomIndex := by
    rw [Finset.sum_congr rfl fun atomIndex _ => hcoDiag atomIndex, Finset.sum_sub_distrib]
    simp [hcard]
  -- the weight the selection carries, bounded ABOVE through the complement gap
  have hsplitWeight : ∑ atomIndex ∈ selected, weight atomIndex
      + ∑ atomIndex ∈ selectedᶜ, weight atomIndex = 1 := by
    rw [Finset.sum_add_sum_compl]; exact hsum
  have hsplitChart : ∑ atomIndex ∈ selected, chart atomIndex atomIndex
      + ∑ atomIndex ∈ selectedᶜ, chart atomIndex atomIndex = (rank : ℝ) := by
    rw [Finset.sum_add_sum_compl]; exact htrace
  have hgapSplit : ∑ atomIndex ∈ selectedᶜ, chart atomIndex atomIndex
      ≤ ∑ atomIndex ∈ selectedᶜ, weight atomIndex := by
    rw [Finset.sum_sub_distrib] at hgap; linarith
  have hweightCap : ∑ atomIndex ∈ selected, weight atomIndex
      ≤ ∑ atomIndex ∈ selected, chart atomIndex atomIndex - ((rank : ℝ) - 1) := by linarith
  -- the weight term never exceeds its total times the probe's squared length
  have hprobeSqBound : ∀ atomIndex, probe atomIndex ^ 2 ≤ probe ⬝ᵥ probe := by
    intro atomIndex
    rw [dotProduct_self_eq_sum_sq]
    exact Finset.single_le_sum (f := fun other => probe other ^ 2)
      (fun other _ => sq_nonneg _) (Finset.mem_univ atomIndex)
  have hweightTerm : ∑ atomIndex, weight atomIndex * probe atomIndex ^ 2
      ≤ (∑ atomIndex ∈ selected, weight atomIndex) * (probe ⬝ᵥ probe) := by
    rw [← Finset.sum_subset (Finset.subset_univ selected)
      (fun atomIndex _ hnot => by rw [hsupport atomIndex hnot]; ring), Finset.sum_mul]
    exact Finset.sum_le_sum fun atomIndex _ =>
      mul_le_mul_of_nonneg_left (hprobeSqBound atomIndex) (hnonneg atomIndex)
  have hprobeNonneg : 0 ≤ probe ⬝ᵥ probe := dotProduct_self_nonneg _
  nlinarith [hcap, hsplitCo, hcoSum, hweightCap, hweightTerm, hprobeNonneg]

end Gtz
