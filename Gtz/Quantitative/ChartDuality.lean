/-
# THE CHART DUAL: D1, D2, D3, D5, and the exact boundary of what transports

## WHAT THIS FILE IS

The campaign ledger's TIER D asked for a dual design whose atom pairings are the
NEGATIVES of the primal's (D1), whose leverages are `1/t_c - l_c` (D2), whose
two-graph is the COMPLEMENT of the primal's (D3), and whose chart gap adds to the
primal's to give a diagonal (D5).  All four are proved below, at every size and
every rank, from ONE construction.

There was a live dispute about whether such an object exists.  It is settled here,
and the settlement is that BOTH sides were right about DIFFERENT objects:

* `Gtz.dualDesign` (`Gtz/Reduction/SplitTransfer.lean`) is built from the isometry
  `rows sqrt(1 - t_c) (Rᵀ g_c)` precisely so that the LOEWNER FLIP
  `Gtz.exists_naimarkDual_loewnerEquiv` holds.  It does NOT have negated pairings.
* The object below is built from the COMPLEMENT CHART `1 - Gtz.projectionOfDesign`.
  It has negated pairings exactly.  It does NOT satisfy the Loewner flip --
  `Gtz.not_forall_dominates_chartDual_compl` exhibits a rational `(6,3)`
  counterexample.

The two duals are therefore genuinely different designs, and the properties the
campaign wanted to combine are split between them.  §7 states that consequence for
the D4 band precisely, and it is a NEGATIVE: the band is not available.

## THE CONSTRUCTION, IN ONE LINE

`1 - Gtz.projectionOfDesign design` is symmetric, idempotent, of trace `m - k`.
`Gtz.exists_orthonormalFrame_of_symmetric_idempotent`
(`Gtz/Reduction/ChartPointFactorisation.lean`) factors it as `V Vᵀ` with
`Vᵀ V = 1`, and `Gtz.designOfOrthonormalFrame` turns `V` plus the ORIGINAL weights
into a `Gtz.WeightedDesign m (m - k)`.  Nothing else is needed: D1, D2, D3 and D5
are then entrywise readings of `projectionOfDesign dual = 1 - projectionOfDesign
design`.

A previous draft of this rung recorded the factorisation as the one missing
ingredient and proposed building it from `Matrix.PosSemidef.posSemidefSqrt`.  That
work is unnecessary -- the repository has carried the factorisation since
`Gtz.chartPointHasDesign` landed.

## SECTIONS

1. `Gtz.IsChartDual` and its existence, at every size and rank.
2. D1 and D2 at the ATOM level.
3. The relation is an involution, and the chart-level dictionary.
4. D3 at rank three: edge signs flip, parities flip, the dual two-graph is the
   COMPLEMENT -- on triples with no vanishing pairing, and NOT otherwise.
5. D5, the block identity, with the trace corollary that is its usable form.
6. What transports: weights, shares (`s'_c = 1 - s_c`), the equal-share stratum at
   `(6,3)`, and the two-sided pair-minor dictionary.
7. What does NOT transport, PROVED: domination.  Hence the D4 band is unavailable.
-/
import Mathlib
import Gtz.Quantitative.SwitchingTwoGraph
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.ChartPointFactorisation
import Gtz.Reduction.CompactnessReduction
import Gtz.Quantitative.HollowInvolution
import Gtz.Design.FrameConservation
import Gtz.Ties.TotalTieCorankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The chart dual and its existence -/

/-- **THE CHART DUAL RELATION.**  `dual` carries the SAME weights as `design` and
its projection chart is the ORTHOGONAL COMPLEMENT of the design's.

Everything the campaign's D1, D2, D3 and D5 asked for is a consequence of these two
fields alone.  The relation is symmetric (`Gtz.IsChartDual.symm`), so "the" dual is
an involution on designs-up-to-rotation. -/
structure IsChartDual {dualRank : ℕ} (design : WeightedDesign m k)
    (dual : WeightedDesign m dualRank) : Prop where
  /-- The dual carries the same weights. -/
  weight_eq : dual.weight = design.weight
  /-- The dual's chart is the complement of the design's. -/
  chart_eq : projectionOfDesign dual = 1 - projectionOfDesign design

/-- The complement chart is symmetric. -/
theorem transpose_one_sub_projectionOfDesign (design : WeightedDesign m k) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) - projectionOfDesign design)ᵀ
      = 1 - projectionOfDesign design := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, projectionOfDesign_transpose]

/-- The complement chart is idempotent. -/
theorem one_sub_projectionOfDesign_mul_self (design : WeightedDesign m k) :
    (1 - projectionOfDesign design) * (1 - projectionOfDesign design)
      = 1 - projectionOfDesign design := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one, projectionOfDesign_mul_self]
  abel

/-- The complement chart has trace `m - k`. -/
theorem trace_one_sub_projectionOfDesign (design : WeightedDesign m k) (hrank : k ≤ m) :
    Matrix.trace ((1 : Matrix (Fin m) (Fin m) ℝ) - projectionOfDesign design)
      = ((m - k : ℕ) : ℝ) := by
  rw [Matrix.trace_sub, Matrix.trace_one, trace_projectionOfDesign, Fintype.card_fin,
    Nat.cast_sub hrank]

/-- **THE CHART DUAL EXISTS**, at every size and every rank.

The whole proof is a weld: the complement chart is a symmetric idempotent of trace
`m - k`, `Gtz.exists_orthonormalFrame_of_symmetric_idempotent` factors it, and
`Gtz.designOfOrthonormalFrame` re-attaches the ORIGINAL weights.  Positivity of the
weights is what makes the second step legal and is free from `Gtz.WeightedDesign`. -/
theorem exists_isChartDual (design : WeightedDesign m k) (hrank : k ≤ m) :
    ∃ dual : WeightedDesign m (m - k), IsChartDual design dual := by
  obtain ⟨frame, hortho, hframe⟩ :=
    exists_orthonormalFrame_of_symmetric_idempotent (1 - projectionOfDesign design)
      (transpose_one_sub_projectionOfDesign design)
      (one_sub_projectionOfDesign_mul_self design)
      (trace_one_sub_projectionOfDesign design hrank)
  refine ⟨designOfOrthonormalFrame frame hortho design.weight design.weight_pos
    design.weight_sum_one, ⟨rfl, ?_⟩⟩
  rw [projectionOfDesign_designOfOrthonormalFrame, hframe]

/-- At `(6,3)` the dual is again a `(6,3)` design: `6 - 3` reduces to `3`, so the
cell is LITERALLY its own dual, with no gauge to fix and nothing to choose. -/
theorem exists_isChartDual_sixThree (design : WeightedDesign 6 3) :
    ∃ dual : WeightedDesign 6 3, IsChartDual design dual :=
  exists_isChartDual design (by norm_num)

/-- The `(7,3)` dual is a `(7,4)` design. -/
theorem exists_isChartDual_sevenThree (design : WeightedDesign 7 3) :
    ∃ dual : WeightedDesign 7 4, IsChartDual design dual :=
  exists_isChartDual design (by norm_num)

/-! ## 2. D1 and D2 at the atom level -/

variable {dualRank : ℕ} {design : WeightedDesign m k} {dual : WeightedDesign m dualRank}

/-- The chart entry of the dual, in the primal's data. -/
theorem projectionOfDesign_chartDual_apply (hdual : IsChartDual design dual)
    (rowIndex colIndex : Fin m) :
    Real.sqrt (design.weight rowIndex) * Real.sqrt (design.weight colIndex)
        * (dual.atom rowIndex ⬝ᵥ dual.atom colIndex)
      = (1 : Matrix (Fin m) (Fin m) ℝ) rowIndex colIndex
        - Real.sqrt (design.weight rowIndex) * Real.sqrt (design.weight colIndex)
          * (design.atom rowIndex ⬝ᵥ design.atom colIndex) := by
  have hentry := congrFun (congrFun hdual.chart_eq rowIndex) colIndex
  rw [projectionOfDesign_apply, Matrix.sub_apply, projectionOfDesign_apply,
    hdual.weight_eq] at hentry
  exact hentry

/-- **D1, AT THE ATOM LEVEL.**  Off the diagonal the dual's pairings are the EXACT
NEGATIVES of the design's.  In particular the two designs have the SAME vanishing
pattern -- a pairing is zero on one side exactly when it is zero on the other. -/
theorem dotProduct_chartDual_of_ne (hdual : IsChartDual design dual)
    {rowIndex colIndex : Fin m} (hne : rowIndex ≠ colIndex) :
    dual.atom rowIndex ⬝ᵥ dual.atom colIndex
      = -(design.atom rowIndex ⬝ᵥ design.atom colIndex) := by
  have hentry := projectionOfDesign_chartDual_apply hdual rowIndex colIndex
  rw [Matrix.one_apply_ne hne] at hentry
  have hpos : (0 : ℝ) < Real.sqrt (design.weight rowIndex)
      * Real.sqrt (design.weight colIndex) :=
    mul_pos (Real.sqrt_pos.mpr (design.weight_pos rowIndex))
      (Real.sqrt_pos.mpr (design.weight_pos colIndex))
  have hcancel : Real.sqrt (design.weight rowIndex) * Real.sqrt (design.weight colIndex)
      * (dual.atom rowIndex ⬝ᵥ dual.atom colIndex)
        = Real.sqrt (design.weight rowIndex) * Real.sqrt (design.weight colIndex)
          * -(design.atom rowIndex ⬝ᵥ design.atom colIndex) := by
    rw [hentry]; ring
  exact mul_left_cancel₀ hpos.ne' hcancel

/-- **D2, AT THE ATOM LEVEL.**  The dual leverage is `1/t_c - l_c`. -/
theorem leverageOf_chartDual (hdual : IsChartDual design dual) (atomIndex : Fin m) :
    leverageOf (dual.atom atomIndex)
      = (design.weight atomIndex)⁻¹ - leverageOf (design.atom atomIndex) := by
  have hentry := projectionOfDesign_chartDual_apply hdual atomIndex atomIndex
  rw [Matrix.one_apply_eq, Real.mul_self_sqrt (design.weight_pos atomIndex).le] at hentry
  rw [dotProduct_self_eq_sum_sq, ← leverageOf] at hentry
  rw [dotProduct_self_eq_sum_sq, ← leverageOf] at hentry
  have hweight := (design.weight_pos atomIndex).ne'
  field_simp at hentry ⊢
  linarith [hentry]

/-- The dual leverage is strictly positive exactly when the atom's share is below
one -- i.e. the dual atom vanishes exactly at a SATURATED atom of the primal. -/
theorem atomShare_chartDual (hdual : IsChartDual design dual) (atomIndex : Fin m) :
    atomShare dual atomIndex = 1 - atomShare design atomIndex := by
  rw [atomShare, atomShare, hdual.weight_eq, leverageOf_chartDual hdual,
    mul_sub, mul_inv_cancel₀ (design.weight_pos atomIndex).ne']

/-! ## 3. The relation is an involution -/

/-- **THE DUAL OF THE DUAL IS THE PRIMAL.**  `Gtz.IsChartDual` is a SYMMETRIC
relation, so the chart duality is an involution and every statement below has a
mirror with the roles exchanged.  This is what makes the `(6,3)` cell self-dual. -/
theorem IsChartDual.symm (hdual : IsChartDual design dual) : IsChartDual dual design where
  weight_eq := hdual.weight_eq.symm
  chart_eq := by rw [hdual.chart_eq, sub_sub_cancel]

/-- The dual's chart point is the complement chart point: same weights, complement
chart.  Everything phrased in the CHART transports along this identification --
the gap, the objective, the argmax family, the stationarity bundles. -/
theorem chartPointOfDesign_chartDual_chart (hdual : IsChartDual design dual) :
    (chartPointOfDesign dual).chart = 1 - (chartPointOfDesign design).chart :=
  hdual.chart_eq

theorem chartPointOfDesign_chartDual_weight (hdual : IsChartDual design dual) :
    (chartPointOfDesign dual).weight = (chartPointOfDesign design).weight :=
  hdual.weight_eq

/-! ## 4. D3: the anti-parity law at rank three -/

section RankThree

variable {designThree dualThree : WeightedDesign m 3}

/-- **D1 in the sign layer's vocabulary.** -/
theorem atomPairing_chartDual (hdual : IsChartDual designThree dualThree)
    {atomFirst atomSecond : Fin m} (hne : atomFirst ≠ atomSecond) :
    atomPairing dualThree atomFirst atomSecond
      = -atomPairing designThree atomFirst atomSecond :=
  dotProduct_chartDual_of_ne hdual hne

/-- **D2 in the sign layer's vocabulary.** -/
theorem heavyExcess_chartDual (hdual : IsChartDual designThree dualThree)
    (atomIndex : Fin m) :
    heavyExcess dualThree atomIndex
      = (designThree.weight atomIndex)⁻¹ - leverageOf (designThree.atom atomIndex) - 1 := by
  rw [heavyExcess, leverageOf_chartDual hdual]

/-- **THE EDGE SIGN FLIPS -- and ONLY at a nonvanishing pairing.**

The convention `Gtz.edgeSign` sends `0` to `+1`, so at a VANISHING pairing both
signs read `+1` and the flip fails.  That is not a defect of the proof: it is where
the two-graph of a design stops being determined by the design's zero pattern. -/
theorem edgeSign_chartDual (hdual : IsChartDual designThree dualThree)
    {atomFirst atomSecond : Fin m} (hne : atomFirst ≠ atomSecond)
    (hnonzero : atomPairing designThree atomFirst atomSecond ≠ 0) :
    edgeSign dualThree atomFirst atomSecond = -edgeSign designThree atomFirst atomSecond := by
  have hpair := atomPairing_chartDual hdual hne
  rcases lt_or_gt_of_ne hnonzero with hneg | hpos
  · rw [edgeSign, edgeSign, hpair, if_pos (by linarith), if_neg (not_le.mpr hneg)]
    norm_num
  · rw [edgeSign, edgeSign, hpair, if_neg (not_le.mpr (by linarith)),
      if_pos (by linarith)]

/-- **D3, THE ANTI-PARITY LAW.**  On a triple all of whose pairings are nonzero, the
dual's triple parity is the NEGATIVE of the design's: three edge signs flip, and
`(-1)^3 = -1`.

THE DUAL TWO-GRAPH IS THE COMPLEMENT OF THE PRIMAL TWO-GRAPH.  A coherent triangle
of the design is an incoherent triangle of its dual, and conversely. -/
theorem tripleParity_chartDual (hdual : IsChartDual designThree dualThree)
    {first second third : Fin m} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third)
    (hfsNonzero : atomPairing designThree first second ≠ 0)
    (hftNonzero : atomPairing designThree first third ≠ 0)
    (hstNonzero : atomPairing designThree second third ≠ 0) :
    tripleParity dualThree first second third
      = -tripleParity designThree first second third := by
  rw [tripleParity, tripleParity, edgeSign_chartDual hdual hfs hfsNonzero,
    edgeSign_chartDual hdual hft hftNonzero, edgeSign_chartDual hdual hst hstNonzero]
  ring

/-- The contrapositive reading X4 consumes: a COHERENT triple of the design with no
vanishing pairing is an INCOHERENT triple of the dual. -/
theorem tripleParity_chartDual_eq_neg_one_of_coherent
    (hdual : IsChartDual designThree dualThree)
    {first second third : Fin m} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third)
    (hfsNonzero : atomPairing designThree first second ≠ 0)
    (hftNonzero : atomPairing designThree first third ≠ 0)
    (hstNonzero : atomPairing designThree second third ≠ 0)
    (hcoherent : tripleParity designThree first second third = 1) :
    tripleParity dualThree first second third = -1 := by
  rw [tripleParity_chartDual hdual hfs hft hst hfsNonzero hftNonzero hstNonzero, hcoherent]

/-- And its mirror. -/
theorem tripleParity_chartDual_eq_one_of_incoherent
    (hdual : IsChartDual designThree dualThree)
    {first second third : Fin m} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third)
    (hfsNonzero : atomPairing designThree first second ≠ 0)
    (hftNonzero : atomPairing designThree first third ≠ 0)
    (hstNonzero : atomPairing designThree second third ≠ 0)
    (hincoherent : tripleParity designThree first second third = -1) :
    tripleParity dualThree first second third = 1 := by
  rw [tripleParity_chartDual hdual hfs hft hst hfsNonzero hftNonzero hstNonzero, hincoherent]
  norm_num

/-- A self-edge always reads `+1`: an atom's pairing with itself is its leverage,
which is a sum of squares. -/
theorem edgeSign_self (designSelf : WeightedDesign m 3) (atomIndex : Fin m) :
    edgeSign designSelf atomIndex atomIndex = 1 := by
  rw [edgeSign, if_pos]
  rw [atomPairing_self]
  exact leverageOf_nonneg _

/-- **THE DEGENERATE PARITY IS PINNED TO `+1`**, at every design: a repeated index
contributes a self-edge (`+1`) and a squared edge sign (`+1`).

This is why an anti-parity partnership can only ever be asked for on PAIRWISE
DISTINCT triples.  Demanding `tripleParity partner = -tripleParity design` at ALL
triples is UNSATISFIABLE -- it reads `1 = -1` at `(a, a, b)` -- so a band argument
phrased that way is vacuous rather than strong. -/
theorem tripleParity_degenerate (designSelf : WeightedDesign m 3)
    (atomFirst atomSecond : Fin m) :
    tripleParity designSelf atomFirst atomFirst atomSecond = 1 := by
  rw [tripleParity, edgeSign_self]
  nlinarith [edgeSign_sq designSelf atomFirst atomSecond]

/-- **THE ORIENTED TRIPLE PRODUCT FLIPS SIGN**, with NO nonvanishing hypothesis:
three negations multiply to one negation.  This is the sign-blind half of D3 and it
survives the zero-pairing branch intact. -/
theorem atomPairingProduct_chartDual (hdual : IsChartDual designThree dualThree)
    {first second third : Fin m} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) :
    atomPairing dualThree first second * atomPairing dualThree first third
        * atomPairing dualThree second third
      = -(atomPairing designThree first second * atomPairing designThree first third
          * atomPairing designThree second third) := by
  rw [atomPairing_chartDual hdual hfs, atomPairing_chartDual hdual hft,
    atomPairing_chartDual hdual hst]
  ring

end RankThree

/-! ## 5. D5: the block identity -/

/-- **D5.**  The chart gap of a design and the chart gap of its dual add to the
DIAGONAL matrix `1 - 2 diag t`.  At a crux both summands carry a strictly negative
direction while their sum has no off-diagonal entry at all. -/
theorem chartPointGap_add_chartDual (hdual : IsChartDual design dual) :
    chartPointGap (chartPointOfDesign design) + chartPointGap (chartPointOfDesign dual)
      = 1 - (2 : ℝ) • Matrix.diagonal design.weight := by
  rw [chartPointGap, chartPointGap]
  show (projectionOfDesign design - Matrix.diagonal design.weight)
      + (projectionOfDesign dual - Matrix.diagonal dual.weight)
    = 1 - (2 : ℝ) • Matrix.diagonal design.weight
  rw [hdual.chart_eq, hdual.weight_eq, two_smul]
  abel

/-- D5 entry by entry, which is the form a block argument reads. -/
theorem chartPointGap_add_chartDual_apply (hdual : IsChartDual design dual)
    (rowIndex colIndex : Fin m) :
    chartPointGap (chartPointOfDesign design) rowIndex colIndex
        + chartPointGap (chartPointOfDesign dual) rowIndex colIndex
      = (1 : Matrix (Fin m) (Fin m) ℝ) rowIndex colIndex
        - 2 * Matrix.diagonal design.weight rowIndex colIndex := by
  have hsum := congrFun (congrFun (chartPointGap_add_chartDual hdual) rowIndex) colIndex
  simpa using hsum

/-- **THE OFF-DIAGONAL HALF OF D5, WHICH IS THE USABLE ONE.**  Off the diagonal the
two chart gaps are exact NEGATIVES of each other.  So a strictly negative direction
of one gap block and a strictly negative direction of the other cannot be produced
by "the same" off-diagonal structure: the two blocks differ by a DIAGONAL matrix
only, and every off-diagonal entry is reversed. -/
theorem chartPointGap_chartDual_apply_of_ne (hdual : IsChartDual design dual)
    {rowIndex colIndex : Fin m} (hne : rowIndex ≠ colIndex) :
    chartPointGap (chartPointOfDesign dual) rowIndex colIndex
      = -chartPointGap (chartPointOfDesign design) rowIndex colIndex := by
  have hsum := chartPointGap_add_chartDual_apply hdual rowIndex colIndex
  rw [Matrix.one_apply_ne hne, Matrix.diagonal_apply_ne _ hne] at hsum
  linarith

/-- **THE TRACE COROLLARY**, which is D5's cheapest consequence and needs no
eigenvalue at all: on every index set the two gap traces add to
`|C| - 2 * (total weight of C)`.  With `sum t = 1` this caps the pair of traces
from above by `|C|`, uniformly, at every design. -/
theorem trace_chartPointGap_add_chartDual (hdual : IsChartDual design dual)
    (selected : Finset (Fin m)) :
    (∑ atomIndex ∈ selected,
        chartPointGap (chartPointOfDesign design) atomIndex atomIndex)
      + (∑ atomIndex ∈ selected,
          chartPointGap (chartPointOfDesign dual) atomIndex atomIndex)
      = (selected.card : ℝ) - 2 * ∑ atomIndex ∈ selected, design.weight atomIndex := by
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun atomIndex _ =>
    chartPointGap_add_chartDual_apply hdual atomIndex atomIndex]
  simp only [Matrix.one_apply_eq, Matrix.diagonal_apply_eq, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]

/-! ## 6. What transports -/

/-- **THE EQUAL-SHARE STRATUM TRANSPORTS AT `(6,3)`.**  Uniform weights are literally
the same on both sides, and `1/(1/6) - 3 = 3`, so the dual leverage is again the
rank.  With `Gtz.IsChartDual.symm` this is an IFF: the crux field
`avoidsEqualShareStratum` holds for a `(6,3)` design exactly when it holds for its
chart dual. -/
theorem isEqualShare_chartDual_sixThree {design dual : WeightedDesign 6 3}
    (hdual : IsChartDual design dual) (hequal : IsEqualShare design) : IsEqualShare dual where
  weight_eq := fun atomIndex => by
    rw [hdual.weight_eq]; exact hequal.weight_eq atomIndex
  leverage_eq := fun atomIndex => by
    rw [leverageOf_chartDual hdual, hequal.weight_eq atomIndex, hequal.leverage_eq atomIndex]
    norm_num

theorem isEqualShare_chartDual_sixThree_iff {design dual : WeightedDesign 6 3}
    (hdual : IsChartDual design dual) : IsEqualShare design ↔ IsEqualShare dual :=
  ⟨isEqualShare_chartDual_sixThree hdual, isEqualShare_chartDual_sixThree hdual.symm⟩

/-- **THE PAIR GRAM MINOR** `l_c l_d - p_cd^2`: the `2x2` principal minor of the Gram
at a pair.  It vanishes exactly at a LINEARLY DEPENDENT pair -- this is the
Cauchy-Schwarz equality case, and it is the quantity `Gtz.HasParallelPair` sees.
Note it is NOT `Gtz.pairMinor`, which uses the heavy EXCESSES `l - 1`. -/
def pairGramMinor (design : WeightedDesign m k) (atomFirst atomSecond : Fin m) : ℝ :=
  leverageOf (design.atom atomFirst) * leverageOf (design.atom atomSecond)
    - (design.atom atomFirst ⬝ᵥ design.atom atomSecond) ^ 2

/-- A parallel pair has a vanishing pair Gram minor. -/
theorem pairGramMinor_eq_zero_of_smul (design : WeightedDesign m k)
    {keptLabel dropLabel : Fin m} {ratio : ℝ}
    (hparallel : design.atom dropLabel = ratio • design.atom keptLabel) :
    pairGramMinor design keptLabel dropLabel = 0 := by
  rw [pairGramMinor, hparallel, leverageOf_smul, dotProduct_smul, smul_eq_mul,
    dotProduct_self_eq_sum_sq, ← leverageOf]
  ring

/-- **D1 + D2 COMBINED: the dual's pair Gram minor in the primal's data.**  The
squared pairing is UNCHANGED (a sign is squared away) while both leverages are
replaced by `1/t - l`.  So the two minors are genuinely different expressions and
there is no reason for them to vanish together. -/
theorem pairGramMinor_chartDual (hdual : IsChartDual design dual)
    {atomFirst atomSecond : Fin m} (hne : atomFirst ≠ atomSecond) :
    pairGramMinor dual atomFirst atomSecond
      = ((design.weight atomFirst)⁻¹ - leverageOf (design.atom atomFirst))
          * ((design.weight atomSecond)⁻¹ - leverageOf (design.atom atomSecond))
        - (design.atom atomFirst ⬝ᵥ design.atom atomSecond) ^ 2 := by
  rw [pairGramMinor, leverageOf_chartDual hdual, leverageOf_chartDual hdual,
    dotProduct_chartDual_of_ne hdual hne, neg_pow, neg_one_pow_two, one_mul]

/-- **THE EXACT OBSTRUCTION TO TRANSPORTING PARALLELISM.**  If a pair is dependent
in BOTH the design and its chart dual, then its two shares sum to exactly one.

So parallelism transports only on the `s_c + s_d = 1` locus and NOWHERE ELSE.  It is
not a duality invariant, and the campaign ledger's D4 claim that
`hasNoParallelPair` transports "by D1, since `|gamma| = 1` is unaffected by
negation" is mistaken: `|normalizedPairing|` divides by the heavy EXCESSES, whereas
dependence is Cauchy-Schwarz equality against the LEVERAGES, and D2 moves the
leverages. -/
theorem atomShare_add_atomShare_eq_one_of_pairGramMinor_eq_zero
    (hdual : IsChartDual design dual) {atomFirst atomSecond : Fin m}
    (hne : atomFirst ≠ atomSecond)
    (hprimal : pairGramMinor design atomFirst atomSecond = 0)
    (hdualZero : pairGramMinor dual atomFirst atomSecond = 0) :
    atomShare design atomFirst + atomShare design atomSecond = 1 := by
  rw [pairGramMinor_chartDual hdual hne] at hdualZero
  rw [pairGramMinor] at hprimal
  have hfirst := (design.weight_pos atomFirst).ne'
  have hsecond := (design.weight_pos atomSecond).ne'
  rw [atomShare, atomShare]
  field_simp at hdualZero
  linear_combination (-1 : ℝ) * hdualZero
    + design.weight atomFirst * design.weight atomSecond * hprimal

/-! ## 7. What does NOT transport: DOMINATION.  The D4 band is unavailable. -/

/-- Three MUTUALLY ORTHOGONAL integer directions of squared lengths `3`, `2`, `6`,
each used twice.  The vectors `(1,1,1)`, `(1,-1,0)`, `(1,1,-2)` are pairwise
orthogonal, so Parseval is the statement that the total weight on each direction is
the reciprocal of its squared length. -/
def orthoSplitAtom : Fin 6 → Fin 3 → ℝ :=
  ![![1, 1, 1], ![1, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

/-- **THE `(6,3)` WITNESS**, exactly rational and ALL-HEAVY: leverages `3, 3, 2, 2,
6, 6` and weights `1/6, 1/6, 2/5, 1/10, 1/12, 1/12`.  The weight on each of the
three orthogonal directions is `1/3`, `1/2`, `1/6` -- the reciprocals of `3`, `2`,
`6` -- which is exactly Parseval.

Its purpose is `Gtz.not_forall_dominates_chartDual_compl`: it separates the CHART
dual from `Gtz.dualDesign`. -/
noncomputable def orthoSplitDesign : WeightedDesign 6 3 where
  atom := orthoSplitAtom
  weight := ![1 / 6, 1 / 6, 2 / 5, 1 / 10, 1 / 12, 1 / 12]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_six, smul_eq_mul, orthoSplitAtom, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

@[simp] theorem orthoSplitDesign_atom : orthoSplitDesign.atom = orthoSplitAtom := rfl

@[simp] theorem orthoSplitDesign_weight :
    orthoSplitDesign.weight = ![1 / 6, 1 / 6, 2 / 5, 1 / 10, 1 / 12, 1 / 12] := rfl

/-- Every leverage of the witness, read off its three squared lengths. -/
theorem orthoSplitDesign_leverage (atomIndex : Fin 6) :
    leverageOf (orthoSplitDesign.atom atomIndex)
      = ![3, 3, 2, 2, 6, 6] atomIndex := by
  fin_cases atomIndex <;>
    simp [orthoSplitDesign_atom, orthoSplitAtom, leverageOf, Fin.sum_univ_three] <;>
    norm_num

/-- The witness is all-heavy. -/
theorem orthoSplitDesign_allHeavy : AllHeavy orthoSplitDesign := by
  intro atomIndex
  rw [orthoSplitDesign_leverage]
  fin_cases atomIndex <;> norm_num

/-- **THE PRIMAL SIDE: the odd triple DOMINATES.**  Its three atoms are the three
mutually orthogonal directions themselves, so the selected Gram is
`diag (3, 2, 6)`; the gap `S - 1` is the positive definite
`[[2,1,-1],[1,2,-1],[-1,-1,4]]`, whose quadratic form is the sum of squares
`(x + y - z)^2 + x^2 + y^2 + 3 z^2`. -/
theorem dominates_orthoSplitDesign_oddTriple : Dominates orthoSplitDesign {1, 3, 5} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨(posSemidef_subsetSum orthoSplitDesign {1, 3, 5}).1.sub Matrix.isHermitian_one, ?_⟩
  intro probe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    dotProduct_subsetSum_mulVec_of_finset, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have hone : orthoSplitDesign.atom 1 ⬝ᵥ probe = probe 0 + probe 1 + probe 2 := by
    simp [orthoSplitDesign_atom, orthoSplitAtom, dotProduct, Fin.sum_univ_three]
  have hthree : orthoSplitDesign.atom 3 ⬝ᵥ probe = probe 0 - probe 1 := by
    simp [orthoSplitDesign_atom, orthoSplitAtom, dotProduct, Fin.sum_univ_three]
    ring
  have hfive : orthoSplitDesign.atom 5 ⬝ᵥ probe = probe 0 + probe 1 - 2 * probe 2 := by
    simp [orthoSplitDesign_atom, orthoSplitAtom, dotProduct, Fin.sum_univ_three]
    ring
  have hself : probe ⬝ᵥ probe = probe 0 ^ 2 + probe 1 ^ 2 + probe 2 ^ 2 := by
    simp [dotProduct, Fin.sum_univ_three]
    ring
  rw [hone, hthree, hfive, hself]
  nlinarith [sq_nonneg (probe 0 + probe 1 - probe 2), sq_nonneg (probe 0),
    sq_nonneg (probe 1), sq_nonneg (probe 2)]

/-- **THE DUAL SIDE: the complementary triple DOES NOT DOMINATE.**

The chart dual's atoms at `0`, `2`, `4` are still mutually orthogonal (D1 negates a
pairing, and `-0 = 0`), but D2 sends the middle leverage `2` to
`(2/5)⁻¹ - 2 = 1/2`, which is BELOW one.  Testing the gap against that atom itself
gives `(1/2)^2 - 1/2 = -1/4 < 0`. -/
theorem not_dominates_chartDual_orthoSplit {dual : WeightedDesign 6 3}
    (hdual : IsChartDual orthoSplitDesign dual) : ¬ Dominates dual {0, 2, 4} := by
  intro hdominates
  have hquad := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 (dual.atom 2)
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    dotProduct_subsetSum_mulVec_of_finset, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hquad
  have hzeroFirst : dual.atom 0 ⬝ᵥ dual.atom 2 = 0 := by
    rw [dotProduct_chartDual_of_ne hdual (by decide)]
    simp [orthoSplitDesign_atom, orthoSplitAtom, dotProduct, Fin.sum_univ_three]
  have hzeroThird : dual.atom 4 ⬝ᵥ dual.atom 2 = 0 := by
    rw [dotProduct_chartDual_of_ne hdual (by decide)]
    simp [orthoSplitDesign_atom, orthoSplitAtom, dotProduct, Fin.sum_univ_three]
  have hweightTwo : orthoSplitDesign.weight 2 = 2 / 5 := by
    simp [orthoSplitDesign_weight]
  have hleverageTwo : leverageOf (orthoSplitDesign.atom 2) = 2 := by
    simp [orthoSplitDesign_atom, orthoSplitAtom, leverageOf, Fin.sum_univ_three]
    norm_num
  have hmiddle : dual.atom 2 ⬝ᵥ dual.atom 2 = 1 / 2 := by
    rw [dotProduct_self_eq_sum_sq, ← leverageOf, leverageOf_chartDual hdual,
      hweightTwo, hleverageTwo]
    norm_num
  rw [hzeroFirst, hzeroThird, hmiddle] at hquad
  norm_num at hquad

/-- **THE CHART DUAL IS NOT THE NAIMARK DUAL, AND THE D4 BAND IS UNAVAILABLE.**

`Gtz.exists_naimarkDual_loewnerEquiv` supplies, for every design, a dual carrying
the LOEWNER FLIP: domination on a `k`-subset matches domination of the dual on the
complement.  The CHART dual does NOT: `Gtz.orthoSplitDesign` dominates `{1,3,5}`
while every chart dual of it fails to dominate `{0,2,4}`.

The consequence for the campaign is a NEGATIVE, and it is the point of this file.
The anti-parity law `Gtz.tripleParity_chartDual` lives on the CHART dual.  The crux
fields `isAllHeavy` and `hasNoDominatingTriple` transport along the LOEWNER dual
(`Gtz.exists_naimarkDual_allHeavy_not_dominating`).  These are DIFFERENT designs, so
no single object carries both, and the ledger's D4 band -- "every eligible atom has
at least two coherent AND at least two incoherent triangles, because the dual's
two-graph is the complement of the primal's and the dual is again a crux" -- does
not follow.  X4 must obtain its incoherent-side count some other way. -/
theorem not_forall_dominates_chartDual_compl :
    ¬ ∀ (design dual : WeightedDesign 6 3), IsChartDual design dual →
        ∀ selected : Finset (Fin 6), selected.card = 3 →
          (Dominates design selected ↔ Dominates dual selectedᶜ) := by
  intro hflip
  obtain ⟨dual, hdual⟩ := exists_isChartDual_sixThree orthoSplitDesign
  have hcompl : ({1, 3, 5} : Finset (Fin 6))ᶜ = {0, 2, 4} := by decide
  have hdualDominates :=
    (hflip orthoSplitDesign dual hdual {1, 3, 5} (by decide)).mp
      dominates_orthoSplitDesign_oddTriple
  rw [hcompl] at hdualDominates
  exact not_dominates_chartDual_orthoSplit hdual hdualDominates

/-- **THE TWO DUALS ARE DIFFERENT DESIGNS, EXHIBITED SIDE BY SIDE.**

At `Gtz.orthoSplitDesign` the Naimark dual of `Gtz.exists_naimarkDual_loewnerEquiv`
DOMINATES `{0,2,4}` -- because the primal dominates the complementary `{1,3,5}` and
the Loewner flip transports that -- while every CHART dual FAILS to dominate the
same triple.  Both carry the same weights as the primal.

So "the dual of a `(6,3)` design" is ambiguous, and the ambiguity is not a gauge
choice: the two objects disagree on domination, which is the crux's own predicate.
D1/D2/D3/D5 belong to the chart dual; K6's `allHeavy` and `hasNoDominatingTriple`
transport belongs to the Naimark dual.  THE D4 BAND ASKED FOR BOTH AT ONCE. -/
theorem exists_naimarkDual_dominates_and_chartDual_not_dominates :
    ∃ naimarkDual chartDual : WeightedDesign 6 3,
      (∀ atomIndex, naimarkDual.weight atomIndex = orthoSplitDesign.weight atomIndex) ∧
      Dominates naimarkDual {0, 2, 4} ∧
      IsChartDual orthoSplitDesign chartDual ∧
      ¬ Dominates chartDual {0, 2, 4} := by
  obtain ⟨naimarkDual, hweight, _, hflip⟩ :=
    exists_naimarkDual_loewnerEquiv (k := 3) (m := 6) (by norm_num) (by norm_num)
      orthoSplitDesign
  obtain ⟨chartDual, hchartDual⟩ := exists_isChartDual_sixThree orthoSplitDesign
  have hcompl : ({1, 3, 5} : Finset (Fin 6))ᶜ = {0, 2, 4} := by decide
  have hnaimark : Dominates naimarkDual {0, 2, 4} := by
    have hequiv := (hflip {1, 3, 5} (by decide)).1.mp dominates_orthoSplitDesign_oddTriple
    rwa [hcompl] at hequiv
  exact ⟨naimarkDual, chartDual, hweight, hnaimark, hchartDual,
    not_dominates_chartDual_orthoSplit hchartDual⟩

/-- **THE ANTI-PARITY PARTNER EXISTS AT `(6,3)`, unconditionally on the nonzero
locus.**  This discharges the obligation the coherent-count rung left open: a
design with no vanishing pairing has a partner, carrying the SAME weights and
again with no vanishing pairing, whose two-graph is the exact COMPLEMENT of its
own.

The distinctness hypotheses are not decoration.  `Gtz.tripleParity_degenerate`
shows the parity of a repeated-index triple is `+1` at EVERY design, so no partner
can flip it, and a version of this statement quantified over ALL triples would be
unsatisfiable.

WHAT THIS DOES NOT GIVE.  The partner is the CHART dual, and by
`Gtz.exists_naimarkDual_dominates_and_chartDual_not_dominates` that is NOT the
Naimark dual.  So the partner is not known to be all-heavy, not known to be
non-dominating, and not a crux.  The two-sided per-vertex band follows for the
DESIGN; the ledger's D4 conclusion -- that the band constrains a CRUX because the
complement pattern is itself realised by a crux -- does NOT. -/
theorem exists_antiParityPartner_sixThree (design : WeightedDesign 6 3)
    (hnonzero : ∀ atomFirst atomSecond : Fin 6, atomFirst ≠ atomSecond →
      atomPairing design atomFirst atomSecond ≠ 0) :
    ∃ partner : WeightedDesign 6 3,
      partner.weight = design.weight ∧
      (∀ atomFirst atomSecond : Fin 6, atomFirst ≠ atomSecond →
        atomPairing partner atomFirst atomSecond ≠ 0) ∧
      (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
        tripleParity partner first second third
          = -tripleParity design first second third) := by
  obtain ⟨partner, hpartner⟩ := exists_isChartDual_sixThree design
  refine ⟨partner, hpartner.weight_eq, ?_, ?_⟩
  · intro atomFirst atomSecond hne
    rw [atomPairing_chartDual hpartner hne]
    exact neg_ne_zero.mpr (hnonzero atomFirst atomSecond hne)
  · intro first second third hfs hft hst
    exact tripleParity_chartDual hpartner hfs hft hst (hnonzero first second hfs)
      (hnonzero first third hft) (hnonzero second third hst)

end Gtz
