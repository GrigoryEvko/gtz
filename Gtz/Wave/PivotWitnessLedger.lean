import Gtz.Wave.AtomPivotDeflation
import Gtz.Wave.PlaneWitnessLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The pivot witness ledger — the deflated frame calculus and the dual form of the third rung

The pivot deflation turned the third rung into a PAIR test in the
deflated Gram of one pivot.  The plane witness ledger turned the plane
pair residue into a DUAL certificate whose budget is one less than the
rank.  This module joins the two.

The join needs a calculus that the deflated Gram of a pivot obeys, and
that calculus is exact.  Write `C y z` for the deflated cross entry of
the pivot.  Then, off the pivot:

* the ROW ENERGY of the pivot is `P_pp (1 - P_pp)`,
* the TRACE of the deflated Gram is `R_p (rank - P_pp) - P_pp (1 - P_pp)`,
* the ROW LAW reads `C` against the pivot row and returns that row,
* the IDEMPOTENCE LAW reads `C` against itself and returns `R_p C` plus
  ONE rank-one correction of weight `s_p (1 - s_p)`.

The last law is the exact form of the rank-one defect that a lossy
deflation loses.  It says that the deflated Gram is a projection scaled
by the pivot, PLUS one explicit rank-one block carried by the pivot row.
Nothing is divided, thus every law holds at every rank and at every slot
count, and the pivot needs no sign.

From that calculus the witness engine transfers verbatim.  The MASTER
IDENTITY prices a deflated witness — a bulk term against the deflated
diagonal, plus a weighted family of squared deflated readings — and the
KILL says that no witness of the deflated budget dominates every
deflated gap.  Four strata follow, and each is unconditional or carries
one explicit polynomial hypothesis:

* the HEAVY SLOT — the bulk witness alone.  At a light pivot it is
  unconditional, and it is TIGHT at the regular tetrahedron
* the RANK-ONE stratum — one deflated direction, priced by the deflated
  defect
* the CONIC stratum — a nonnegative family of deflated directions
* the MARGIN — the extension total of the pivot pair, re-derived from
  the cross square total rather than from the Schur split.

The module then reads the witness engine in the ambient space, where the
budget is `rank - 1` and the trace law is free.  The SHARE DEFECT is the
result: at every crux, and at every family of shares whose chart total is
one, some atom reads more share energy than its shifted weight.  That
law SUBSUMES the two unconditional laws of every crux that the plane
ledger supplies — the heavy atom is the constant share, and the Gram
defect is the share of one slot.

A LAUNCH PAD makes the deflated search self-starting.  At one and the
same light pivot the deflated trace is positive, the deflated gap total
beats the scale gap, and one slot outside the pivot carries a positive
pivot minor.  Thus every hypothesis that the deflated ledger asks of a
pivot holds unconditionally, and the residue may consume all four.

The last layers state the third rung in DUAL form.  `AtomPivotWitnessClosed`
asks, at a datum whose deflated pairs all fail, for one bulk value and
six weights.  Its constraints are linear in those unknowns at fixed data,
it carries no combinatorial search, no eigenvalue and no square root, and
it closes the `(6,3)` cell with no side hypothesis.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomPivotCross_comm`, `Gtz.atomPivotCross_self`,
  `Gtz.atomPivotCross_at_pivot_left`, `Gtz.atomPivotCross_at_pivot_right`
  — the shape of the deflated Gram.
* `Gtz.atomPivot_row_energy` — the pivot row energy off the pivot.
* `Gtz.atomPivotCross_row_law` — the deflated Gram against the pivot row.
* `Gtz.atomPivotCross_idempotent` — **THE DEFLATED IDEMPOTENCE LAW**, the
  exact rank-one defect of the deflation.
* `Gtz.atomPivotCross_idempotent_of_zero_scale`,
  `Gtz.atomPivotTrace_of_zero_scale` — **THE BRIDGE TO THE PLANE LANE**:
  at a pivot of vanishing scale the deflated Gram is the pivot against a
  projection of rank two.
* `Gtz.atomPivotCross_row_square`, `Gtz.atomPivotCross_column_square` —
  its diagonal readings.
* `Gtz.atomPivotTrace`, `Gtz.atomPivotTrace_eq` — **THE DEFLATED TRACE
  LAW.**
* `Gtz.atomPairMinor_pivot_total` — the deflated gap total.
* `Gtz.atomPivotDefect`, `Gtz.atomPivotDefect_eq`,
  `Gtz.atomPivotDefect_eq_three` — the deflated defect, and its rank-three
  reading as the pivot scale against the pivot excess.
* `Gtz.atomPivotDefect_nonpos`,
  `Gtz.rank_one_budget_fails_of_nonpos_defect` — **A BANKED NEGATIVE**:
  the rank-one stratum lives only at a HEAVY pivot, whose diagonal entry
  and shifted diagonal total more than one.
* `Gtz.atomPivotTrace_pos_of_light` — a light pivot carries a positive
  deflated trace.
* `Gtz.atomPivot_witness_energy_total` — **THE DEFLATED MASTER
  IDENTITY.**
* `Gtz.false_of_pivot_witness` — **THE DEFLATED KILL.**
* `Gtz.exists_pivot_witness_defect` — its positive reading.
* `Gtz.exists_deflated_heavy_slot`,
  `Gtz.exists_deflated_heavy_slot_of_light_pivot` — **THE HEAVY SLOT
  STRATUM**, tight at the regular tetrahedron.
* `Gtz.atomPairMinor_pivot_total_pos`, `Gtz.exists_positive_pivot_minor`,
  `Gtz.exists_light_pivot_launch`,
  `Gtz.exists_dominating_pair_at_light_pivot` — **THE LAUNCH PAD**: at
  one and the same light pivot the deflated trace is positive, the
  deflated gap total beats the scale gap, and one slot outside carries a
  positive pivot minor.  The deflated search never starts empty.
* `Gtz.atomPivot_weight_dominates` — the deflated pair hypothesis priced
  on a deflated conic witness.
* `Gtz.exists_pivotPair_of_deflated_rank_one` — **THE RANK-ONE STRATUM
  OF THE THIRD RUNG.**
* `Gtz.exists_pivotPair_of_deflated_conic` — **THE CONIC STRATUM OF THE
  THIRD RUNG.**
* `Gtz.exists_pivotPair_of_deflated_mixed` — **THE MIXED STRATUM**, the
  general two-term deflated witness.
* `Gtz.atomPivotCross_row_square_total`,
  `Gtz.exists_pivotPair_of_cross_margin` — **THE MARGIN FROM THE CROSS
  SQUARE TOTAL.**
* `Gtz.exists_frame_witness_defect` — the positive form of the ambient
  kill.
* `Gtz.exists_heavy_reading` — **NO DIRECTION IS UNIFORMLY LIGHT**: at
  every direction one single atom already beats the probe energy.  Tight
  at the regular tetrahedron.
* `Gtz.exists_heavy_share_reading` — its trace-one form.
* `Gtz.exists_heavy_reading_of_plane` — the rank-two projection reading.
* `Gtz.exists_share_defect_slot` — **THE MASTER UNCONDITIONAL LAW OF THE
  ATOM LANE**, with `Gtz.exists_gram_defect_slot`,
  `Gtz.exists_heavy_atom_slot` and `Gtz.exists_single_slot_domination` as
  instances.
* `Gtz.exists_two_pivot_gram_defect` — **THE TWO-PIVOT GRAM DEFECT**: any
  two slots of positive diagonal are beaten together by ONE slot.  The
  ambient budget is one below the rank, thus a rank-one witness wastes a
  whole unit and this law spends it.
* `Gtz.exists_weighted_gram_defect`, `Gtz.exists_region_gram_defect` —
  **THE REGION GRAM DEFECT**: every region of positive diagonal mass is
  beaten by ONE slot.  One slot returns the Gram defect and the whole
  slot set returns the heavy slot, thus the region law carries both.
* `Gtz.SixThreeCrux.exists_witness_defect` — **THE MASTER UNCONDITIONAL
  LAW OF EVERY CRUX.**
* `Gtz.SixThreeCrux.exists_share_defect` — **THE SHARE DEFECT**, and
  `Gtz.SixThreeCrux.exists_heavy_atom_of_share`,
  `Gtz.SixThreeCrux.exists_gram_defect_of_share` — the two landed
  unconditional laws of a crux, both as corollaries of one share law.
* `Gtz.SixThreeCrux.exists_two_pivot_gram_defect` — the two-pivot law of
  every crux.
* `Gtz.SixThreeCrux.exists_region_gram_defect` — **THE REGION LAW OF
  EVERY CRUX**, over all sixty three nonempty regions at once.
* `Gtz.tetraFrame`, `Gtz.tetraFrameScale`, `Gtz.tetraFrame_frame_law`,
  `Gtz.tetraFrameScale_pos`, `Gtz.tetraFrameScale_sum`,
  `Gtz.tetraFrame_shiftedDiag_axis`, `Gtz.tetraFrame_tripleDet`,
  `Gtz.tetraFrame_pivotPair` — the regular tetrahedron as an explicit
  rational datum.
* `Gtz.exists_tight_frame_with_small_margin` — **THE THIRD RUNG IS
  TIGHT**: the determinant margin of every tetrahedral triple goes to
  zero as the scale mass goes to one.
* `Gtz.AtomPivotWitnessClosed`,
  `Gtz.atomPivotPairClosed_of_pivotWitness` — **THE THIRD RUNG IN DUAL
  FORM.**
* `Gtz.atomTripleSylvesterClosed_of_pivotWitness`,
  `Gtz.atomTripleCeilingClosed_of_pivotWitness`,
  `Gtz.gtzWeighted_six_three_of_pivotWitness`,
  `Gtz.gtzWeightedAll_three_of_pivotWitness`,
  `Gtz.isEmpty_sixThreeCrux_of_pivotWitness` — **THE CELL AND ALL OF RANK
  THREE FROM THE DUAL RESIDUE**, with no side hypothesis.
* `Gtz.rankFiveDenseClosed_of_pivotWitness`,
  `Gtz.rankSixDenseClosed_of_pivotWitness`,
  `Gtz.rankSixSupportTwoClosed_of_pivotWitness`,
  `Gtz.rankFiveSupportTwoClosed_of_pivotWitness`,
  `Gtz.rankFourSupportTwoClosed_of_pivotWitness` — the dense branches and
  the support-two closures from the same residue.
* `Gtz.AtomLightPivotWitnessClosed`,
  `Gtz.atomPivotPairClosed_of_lightPivotWitness` — **THE RESIDUE AT THE
  LIGHT PIVOT**, strictly smaller because the launch pad gives it four
  more hypotheses at no cost, with
  `Gtz.gtzWeighted_six_three_of_lightPivotWitness`,
  `Gtz.gtzWeightedAll_three_of_lightPivotWitness` and the same seven
  campaign consequences.

## Vacuity

Every law of layers zero thru four is an unconditional statement about a
family of vectors and a family of scales, or it carries one explicit
polynomial hypothesis in the Gram entries and the scales.  The residue of
layer six is a statement about every such family, thus it is not vacuous.
-/

namespace Gtz

open scoped BigOperators

/-! ## Layer 0 — the shape of the deflated Gram -/

variable {slotCount rank : ℕ}

/-- The deflated cross entry is symmetric in the two outer slots. -/
theorem atomPivotCross_comm (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot rowSlot colSlot : Fin slotCount) :
    atomPivotCross atom scale pivot rowSlot colSlot
      = atomPivotCross atom scale pivot colSlot rowSlot := by
  simp only [atomPivotCross]
  rw [atomGram_comm atom rowSlot colSlot]
  ring

/-- **THE DEFLATED DIAGONAL.**  The deflated cross entry of one slot
against itself is the pivot minor of that slot, plus the scale of that
slot against the shifted diagonal of the pivot. -/
theorem atomPivotCross_self (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot slot : Fin slotCount) :
    atomPivotCross atom scale pivot slot slot
      = atomPairMinor atom scale pivot slot
        + atomShiftedDiag atom scale pivot * scale slot := by
  simp only [atomPivotCross, atomPairMinor, atomShiftedDiag]
  ring

/-- The deflated cross entry at the pivot on the left is the pivot row,
scaled by the negative of the pivot scale. -/
theorem atomPivotCross_at_pivot_left (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot slot : Fin slotCount) :
    atomPivotCross atom scale pivot pivot slot
      = -(scale pivot * atomGram atom pivot slot) := by
  simp only [atomPivotCross, atomShiftedDiag]
  ring

/-- The deflated cross entry at the pivot on the right is the pivot row,
scaled by the negative of the pivot scale. -/
theorem atomPivotCross_at_pivot_right (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot slot : Fin slotCount) :
    atomPivotCross atom scale pivot slot pivot
      = -(scale pivot * atomGram atom pivot slot) := by
  rw [atomPivotCross_comm atom scale pivot slot pivot,
    atomPivotCross_at_pivot_left atom scale pivot slot]

/-- **THE PIVOT ROW ENERGY OFF THE PIVOT.**  The squares of the pivot row
of the Gram, summed over every slot outside the pivot, total the pivot
diagonal against its own gap to one.  The row energy law of the frame
carries the whole proof. -/
theorem atomPivot_row_energy {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (pivot : Fin slotCount) :
    (∑ slot ∈ Finset.univ.erase pivot, atomGram atom pivot slot ^ 2)
      = atomGram atom pivot pivot * (1 - atomGram atom pivot pivot) := by
  classical
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ pivot), atomGram_row_energy hframe pivot]
  ring

/-- **THE DEFLATED ROW LAW.**  The deflated Gram, read against the pivot
row of the Gram, returns that pivot row scaled by the pivot scale and by
the gap of the pivot diagonal to one.

Thus the pivot row is an eigenvector of the deflated Gram off the pivot,
and its eigenvalue is explicit. -/
theorem atomPivotCross_row_law {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (pivot rowSlot : Fin slotCount) :
    (∑ midSlot ∈ Finset.univ.erase pivot,
        atomPivotCross atom scale pivot rowSlot midSlot * atomGram atom pivot midSlot)
      = -(scale pivot * (1 - atomGram atom pivot pivot) * atomGram atom pivot rowSlot) := by
  classical
  have hcell : ∀ midSlot : Fin slotCount,
      atomPivotCross atom scale pivot rowSlot midSlot * atomGram atom pivot midSlot
        = atomShiftedDiag atom scale pivot
            * (atomGram atom rowSlot midSlot * atomGram atom midSlot pivot)
          - atomGram atom pivot rowSlot
            * (atomGram atom pivot midSlot * atomGram atom midSlot pivot) := by
    intro midSlot
    simp only [atomPivotCross]
    rw [atomGram_comm atom midSlot pivot]
    ring
  have hfull : (∑ midSlot, atomPivotCross atom scale pivot rowSlot midSlot
        * atomGram atom pivot midSlot)
      = atomShiftedDiag atom scale pivot * atomGram atom rowSlot pivot
        - atomGram atom pivot rowSlot * atomGram atom pivot pivot := by
    rw [Finset.sum_congr rfl fun midSlot _ => hcell midSlot, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, atomGram_idempotent hframe rowSlot pivot,
      atomGram_idempotent hframe pivot pivot]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ pivot), hfull,
    atomPivotCross_at_pivot_right atom scale pivot rowSlot,
    atomGram_comm atom rowSlot pivot]
  simp only [atomShiftedDiag]
  ring

/-- **THE DEFLATED IDEMPOTENCE LAW.**  The deflated Gram of a pivot,
composed with itself off the pivot, is the deflated Gram scaled by the
shifted diagonal of the pivot, PLUS one rank-one block carried by the
pivot row with weight the pivot scale against its own gap to one.

This is the exact rank-one defect of the deflation.  It is division free,
it needs no sign on the pivot, and it holds at every rank and at every
slot count.  Read at a pivot of vanishing scale the correction vanishes,
and the deflated Gram is a projection scaled by the pivot diagonal. -/
theorem atomPivotCross_idempotent {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (pivot rowSlot colSlot : Fin slotCount) :
    (∑ midSlot ∈ Finset.univ.erase pivot,
        atomPivotCross atom scale pivot rowSlot midSlot
          * atomPivotCross atom scale pivot midSlot colSlot)
      = atomShiftedDiag atom scale pivot * atomPivotCross atom scale pivot rowSlot colSlot
        + scale pivot * (1 - scale pivot)
          * atomGram atom pivot rowSlot * atomGram atom pivot colSlot := by
  classical
  have hcell : ∀ midSlot : Fin slotCount,
      atomPivotCross atom scale pivot rowSlot midSlot
          * atomPivotCross atom scale pivot midSlot colSlot
        = atomShiftedDiag atom scale pivot ^ 2
            * (atomGram atom rowSlot midSlot * atomGram atom midSlot colSlot)
          - atomShiftedDiag atom scale pivot * atomGram atom pivot colSlot
            * (atomGram atom rowSlot midSlot * atomGram atom midSlot pivot)
          - atomShiftedDiag atom scale pivot * atomGram atom pivot rowSlot
            * (atomGram atom pivot midSlot * atomGram atom midSlot colSlot)
          + atomGram atom pivot rowSlot * atomGram atom pivot colSlot
            * (atomGram atom pivot midSlot * atomGram atom midSlot pivot) := by
    intro midSlot
    simp only [atomPivotCross]
    rw [atomGram_comm atom midSlot pivot]
    ring
  have hfull : (∑ midSlot, atomPivotCross atom scale pivot rowSlot midSlot
        * atomPivotCross atom scale pivot midSlot colSlot)
      = atomShiftedDiag atom scale pivot ^ 2 * atomGram atom rowSlot colSlot
        - atomShiftedDiag atom scale pivot * atomGram atom pivot colSlot
          * atomGram atom rowSlot pivot
        - atomShiftedDiag atom scale pivot * atomGram atom pivot rowSlot
          * atomGram atom pivot colSlot
        + atomGram atom pivot rowSlot * atomGram atom pivot colSlot
          * atomGram atom pivot pivot := by
    rw [Finset.sum_congr rfl fun midSlot _ => hcell midSlot, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, atomGram_idempotent hframe rowSlot colSlot,
      atomGram_idempotent hframe rowSlot pivot, atomGram_idempotent hframe pivot colSlot,
      atomGram_idempotent hframe pivot pivot]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ pivot), hfull,
    atomPivotCross_at_pivot_right atom scale pivot rowSlot,
    atomPivotCross_at_pivot_left atom scale pivot colSlot,
    atomGram_comm atom rowSlot pivot]
  simp only [atomPivotCross, atomShiftedDiag]
  ring

/-- **THE DEFLATION AT A PIVOT OF VANISHING SCALE IS A PROJECTION.**  At
a pivot whose scale vanishes the rank-one correction vanishes with it,
and the deflated Gram is the shifted diagonal of the pivot against an
idempotent.

This is the exact bridge to the plane lane: at such a pivot the deflated
pair test is the plane pair test of the dense collapse layer, scaled by
the square of the pivot diagonal. -/
theorem atomPivotCross_idempotent_of_zero_scale {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount} (hzero : scale pivot = 0)
    (rowSlot colSlot : Fin slotCount) :
    (∑ midSlot ∈ Finset.univ.erase pivot,
        atomPivotCross atom scale pivot rowSlot midSlot
          * atomPivotCross atom scale pivot midSlot colSlot)
      = atomShiftedDiag atom scale pivot * atomPivotCross atom scale pivot rowSlot colSlot := by
  rw [atomPivotCross_idempotent hframe scale pivot rowSlot colSlot, hzero]
  ring

/-- **THE DEFLATED ROW ENERGY.**  The squares of one deflated row,
summed off the pivot, are the deflated diagonal entry of that row scaled
by the pivot, plus the rank-one correction. -/
theorem atomPivotCross_row_square {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (pivot rowSlot : Fin slotCount) :
    (∑ midSlot ∈ Finset.univ.erase pivot, atomPivotCross atom scale pivot rowSlot midSlot ^ 2)
      = atomShiftedDiag atom scale pivot * atomPivotCross atom scale pivot rowSlot rowSlot
        + scale pivot * (1 - scale pivot) * atomGram atom pivot rowSlot ^ 2 := by
  classical
  have hcell : ∀ midSlot ∈ Finset.univ.erase pivot,
      atomPivotCross atom scale pivot rowSlot midSlot
          * atomPivotCross atom scale pivot midSlot rowSlot
        = atomPivotCross atom scale pivot rowSlot midSlot ^ 2 := by
    intro midSlot _
    rw [atomPivotCross_comm atom scale pivot midSlot rowSlot, sq]
  rw [← Finset.sum_congr rfl hcell,
    atomPivotCross_idempotent hframe scale pivot rowSlot rowSlot]
  ring

/-- **THE DEFLATED COLUMN ENERGY.**  The deflated Gram is symmetric, thus
the column energy is the row energy. -/
theorem atomPivotCross_column_square {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (pivot colSlot : Fin slotCount) :
    (∑ midSlot ∈ Finset.univ.erase pivot, atomPivotCross atom scale pivot midSlot colSlot ^ 2)
      = atomShiftedDiag atom scale pivot * atomPivotCross atom scale pivot colSlot colSlot
        + scale pivot * (1 - scale pivot) * atomGram atom pivot colSlot ^ 2 := by
  classical
  have hcell : ∀ midSlot ∈ Finset.univ.erase pivot,
      atomPivotCross atom scale pivot midSlot colSlot ^ 2
        = atomPivotCross atom scale pivot colSlot midSlot ^ 2 := by
    intro midSlot _
    rw [atomPivotCross_comm atom scale pivot midSlot colSlot]
  rw [Finset.sum_congr rfl hcell, atomPivotCross_row_square hframe scale pivot colSlot]

/-! ## Layer 1 — the deflated trace, the gap total and the defect -/

/-- The DEFLATED TRACE of a pivot: the diagonal total of the deflated
Gram off the pivot. -/
def atomPivotTrace (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) : ℝ :=
  ∑ slot ∈ Finset.univ.erase pivot, atomPivotCross atom scale pivot slot slot

/-- The deflated trace unfolded. -/
theorem atomPivotTrace_def (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) :
    atomPivotTrace atom scale pivot
      = ∑ slot ∈ Finset.univ.erase pivot, atomPivotCross atom scale pivot slot slot := rfl

/-- **THE DEFLATED TRACE LAW.**  The deflated trace of a pivot is the
shifted diagonal of the pivot against the rank gap of the pivot
diagonal, minus the pivot row energy.  The trace law and the row energy
law of the frame carry the whole proof. -/
theorem atomPivotTrace_eq {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) :
    atomPivotTrace atom scale pivot
      = atomShiftedDiag atom scale pivot * ((rank : ℝ) - atomGram atom pivot pivot)
        - atomGram atom pivot pivot * (1 - atomGram atom pivot pivot) := by
  classical
  have hcell : ∀ slot : Fin slotCount,
      atomPivotCross atom scale pivot slot slot
        = atomShiftedDiag atom scale pivot * atomGram atom slot slot
          - atomGram atom pivot slot ^ 2 := by
    intro slot
    simp only [atomPivotCross]
    ring
  rw [atomPivotTrace_def, Finset.sum_congr rfl fun slot _ => hcell slot, Finset.sum_sub_distrib,
    ← Finset.mul_sum, atomPivot_row_energy hframe pivot,
    Finset.sum_erase_eq_sub (Finset.mem_univ pivot), atomGram_trace hframe]

/-- **THE DEFLATED GAP TOTAL.**  The pivot minors of one pivot, summed
over every slot outside the pivot, are the deflated trace minus the
outside scale mass against the shifted diagonal of the pivot. -/
theorem atomPairMinor_pivot_total (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) :
    (∑ slot ∈ Finset.univ.erase pivot, atomPairMinor atom scale pivot slot)
      = atomPivotTrace atom scale pivot
        - atomShiftedDiag atom scale pivot * ((∑ slot, scale slot) - scale pivot) := by
  classical
  have hcell : ∀ slot : Fin slotCount,
      atomPairMinor atom scale pivot slot
        = atomPivotCross atom scale pivot slot slot
          - atomShiftedDiag atom scale pivot * scale slot := by
    intro slot
    rw [atomPivotCross_self atom scale pivot slot]
    ring
  rw [atomPivotTrace_def, Finset.sum_congr rfl fun slot _ => hcell slot, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ pivot),
    Finset.sum_erase_eq_sub (Finset.mem_univ pivot)]

/-- The DEFLATED DEFECT of a pivot: the deflated trace minus twice the
shifted diagonal of the pivot, corrected by the pivot scale.  It is the
exact budget that a deflated rank-one witness must beat. -/
def atomPivotDefect (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) : ℝ :=
  atomPivotTrace atom scale pivot
    - atomShiftedDiag atom scale pivot * (2 - scale pivot)

/-- The closed form of the deflated defect at every rank. -/
theorem atomPivotDefect_eq {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) :
    atomPivotDefect atom scale pivot
      = atomShiftedDiag atom scale pivot
          * ((rank : ℝ) - 2 - atomShiftedDiag atom scale pivot)
        - atomGram atom pivot pivot * (1 - atomGram atom pivot pivot) := by
  rw [atomPivotDefect, atomPivotTrace_eq hframe scale pivot]
  simp only [atomShiftedDiag]
  ring

/-- **THE RANK-THREE READING OF THE DEFLATED DEFECT.**  At rank three the
defect is the pivot scale against the excess of the pivot: the pivot
diagonal plus the shifted diagonal of the pivot, beyond one.

Thus a pivot of vanishing scale has a vanishing defect, and a pivot pays
a positive defect exactly when it is heavy enough that its diagonal and
its shifted diagonal total more than one. -/
theorem atomPivotDefect_eq_three {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) :
    atomPivotDefect atom scale pivot
      = scale pivot
        * (atomGram atom pivot pivot + atomShiftedDiag atom scale pivot - 1) := by
  rw [atomPivotDefect_eq hframe scale pivot]
  simp only [atomShiftedDiag]
  push_cast
  ring

/-- **THE DEFLATED TRACE AT A PIVOT OF VANISHING SCALE.**  At rank three
a pivot of vanishing scale carries a deflated trace of exactly twice its
own diagonal entry, thus the deflated Gram is that diagonal against a
projection of rank two. -/
theorem atomPivotTrace_of_zero_scale {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount} (hzero : scale pivot = 0) :
    atomPivotTrace atom scale pivot = 2 * atomGram atom pivot pivot := by
  rw [atomPivotTrace_eq hframe scale pivot]
  simp only [atomShiftedDiag, hzero, sub_zero]
  push_cast
  ring

/-- **THE DEFLATED DEFECT NEEDS A HEAVY PIVOT.**  At rank three a pivot
whose diagonal entry and shifted diagonal total at most one carries a
defect that is at most zero. -/
theorem atomPivotDefect_nonpos {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount} (hscale : 0 ≤ scale pivot)
    (hlight : atomGram atom pivot pivot + atomShiftedDiag atom scale pivot ≤ 1) :
    atomPivotDefect atom scale pivot ≤ 0 := by
  rw [atomPivotDefect_eq_three hframe scale pivot]
  nlinarith [hscale, hlight]

/-- **THE RANK-ONE STRATUM CANNOT FIRE AT A LIGHT PIVOT.**  A banked
negative: when the deflated defect is at most zero, the budget of the
deflated rank-one witness fails at every slot of positive scale.

Thus the rank-one stratum lives only at a HEAVY pivot, whose diagonal
entry and shifted diagonal total more than one, and no successor must
look for it elsewhere. -/
theorem rank_one_budget_fails_of_nonpos_defect {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {pivot heavy : Fin slotCount}
    (hdefect : atomPivotDefect atom scale pivot ≤ 0)
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hscale : 0 < scale heavy) (hpivotScale : 0 ≤ scale pivot)
    (hpivotSmall : scale pivot ≤ 1) (hminor : 0 < atomPairMinor atom scale pivot heavy) :
    atomPivotDefect atom scale pivot * atomPairMinor atom scale pivot heavy
      < atomShiftedDiag atom scale pivot ^ 2 * scale heavy
        + scale pivot * (1 - scale pivot) * atomGram atom pivot heavy ^ 2 := by
  have hcorrection : 0 ≤ scale pivot * (1 - scale pivot) * atomGram atom pivot heavy ^ 2 :=
    mul_nonneg (mul_nonneg hpivotScale (by linarith)) (sq_nonneg _)
  have hprod : atomPivotDefect atom scale pivot * atomPairMinor atom scale pivot heavy ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hdefect hminor.le
  have hlead : 0 < atomShiftedDiag atom scale pivot ^ 2 * scale heavy :=
    mul_pos (pow_pos hpivot 2) hscale
  linarith [hprod, hlead, hcorrection]

/-- **A LIGHT PIVOT CARRIES A POSITIVE DEFLATED TRACE.**  The light pivot
of the deflation layer pays at most the scale share of the rank, thus its
shifted diagonal beats twice its scale, thus its deflated trace is
positive.

The deflated ledger needs a positive trace, and this law supplies one at
no cost: a light pivot always exists. -/
theorem atomPivotTrace_pos_of_light {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount}
    (hscale : 0 < scale pivot) (hsmall : (∑ slot, scale slot) < 1)
    (hmass : 0 < ∑ slot, scale slot)
    (hlight : scale pivot * (3 - ∑ slot, scale slot)
      ≤ (∑ slot, scale slot) * atomShiftedDiag atom scale pivot)
    (hpivot : 0 < atomShiftedDiag atom scale pivot) :
    0 < atomPivotTrace atom scale pivot := by
  have hcap := atomGram_diag_le_one hframe pivot
  have hdiag : atomGram atom pivot pivot = atomShiftedDiag atom scale pivot + scale pivot := by
    simp only [atomShiftedDiag]
    ring
  have hheavy : 2 * scale pivot < atomShiftedDiag atom scale pivot := by
    nlinarith [hlight, hscale, hmass, hsmall, hpivot]
  rw [atomPivotTrace_eq hframe scale pivot, hdiag]
  push_cast
  nlinarith [hcap, hpivot, hscale, hheavy, hdiag]

/-! ## Layer 2 — the deflated witness master law -/

/-- **THE DEFLATED MASTER IDENTITY.**  The total deflated witness energy
of a pivot is the deflated witness budget: the bulk term prices the
deflated trace law, and each weight prices the deflated column energy of
its own slot.

No sign condition is necessary.  The identity holds at every real bulk
value, at every real weight family, at every rank and at every slot
count. -/
theorem atomPivot_witness_energy_total {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount)
    (bulk : ℝ) (weight : Fin slotCount → ℝ) :
    (∑ slot ∈ Finset.univ.erase pivot,
        (bulk * atomPivotCross atom scale pivot slot slot
          + ∑ index ∈ Finset.univ.erase pivot,
              weight index * atomPivotCross atom scale pivot slot index ^ 2))
      = bulk * atomPivotTrace atom scale pivot
        + ∑ index ∈ Finset.univ.erase pivot,
            weight index
              * (atomShiftedDiag atom scale pivot
                  * atomPivotCross atom scale pivot index index
                + scale pivot * (1 - scale pivot) * atomGram atom pivot index ^ 2) := by
  classical
  have hbulk : (∑ slot ∈ Finset.univ.erase pivot, bulk * atomPivotCross atom scale pivot slot slot)
      = bulk * atomPivotTrace atom scale pivot := by
    rw [atomPivotTrace_def, Finset.mul_sum]
  have hcross : (∑ slot ∈ Finset.univ.erase pivot, ∑ index ∈ Finset.univ.erase pivot,
        weight index * atomPivotCross atom scale pivot slot index ^ 2)
      = ∑ index ∈ Finset.univ.erase pivot,
          weight index
            * (atomShiftedDiag atom scale pivot
                * atomPivotCross atom scale pivot index index
              + scale pivot * (1 - scale pivot) * atomGram atom pivot index ^ 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [← Finset.mul_sum, atomPivotCross_column_square hframe scale pivot index]
  rw [Finset.sum_add_distrib, hbulk, hcross]

/-- **THE DEFLATED KILL.**  A pivot of positive shifted diagonal at a
frame with scales of total less than one admits NO deflated witness whose
budget stays at the deflated trace minus the pivot cost.

The deflated gap total is exactly the deflated trace minus the outside
scale mass against the pivot, and the scale mass is less than one.  Thus
the strict scale bound is the whole slack, and the kill consumes it with
no waste. -/
theorem false_of_pivot_witness {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hsmall : (∑ slot, scale slot) < 1)
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (bulk : ℝ) (weight : Fin slotCount → ℝ)
    (hbudget : bulk * atomPivotTrace atom scale pivot
        + (∑ index ∈ Finset.univ.erase pivot,
            weight index
              * (atomShiftedDiag atom scale pivot
                  * atomPivotCross atom scale pivot index index
                + scale pivot * (1 - scale pivot) * atomGram atom pivot index ^ 2))
      ≤ atomPivotTrace atom scale pivot
        - atomShiftedDiag atom scale pivot * (1 - scale pivot))
    (hdominate : ∀ slot ∈ Finset.univ.erase pivot,
      atomPairMinor atom scale pivot slot
        ≤ bulk * atomPivotCross atom scale pivot slot slot
          + ∑ index ∈ Finset.univ.erase pivot,
              weight index * atomPivotCross atom scale pivot slot index ^ 2) :
    False := by
  classical
  have hcap := Finset.sum_le_sum hdominate
  rw [atomPivot_witness_energy_total hframe scale pivot bulk weight,
    atomPairMinor_pivot_total atom scale pivot] at hcap
  nlinarith [hcap, hbudget, hpivot, hsmall]

/-- **THE POSITIVE READING OF THE DEFLATED KILL.**  Every deflated
witness of the deflated budget misses at least one slot outside the
pivot. -/
theorem exists_pivot_witness_defect {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hsmall : (∑ slot, scale slot) < 1)
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (bulk : ℝ) (weight : Fin slotCount → ℝ)
    (hbudget : bulk * atomPivotTrace atom scale pivot
        + (∑ index ∈ Finset.univ.erase pivot,
            weight index
              * (atomShiftedDiag atom scale pivot
                  * atomPivotCross atom scale pivot index index
                + scale pivot * (1 - scale pivot) * atomGram atom pivot index ^ 2))
      ≤ atomPivotTrace atom scale pivot
        - atomShiftedDiag atom scale pivot * (1 - scale pivot)) :
    ∃ slot, slot ≠ pivot
      ∧ bulk * atomPivotCross atom scale pivot slot slot
          + (∑ index ∈ Finset.univ.erase pivot,
              weight index * atomPivotCross atom scale pivot slot index ^ 2)
        < atomPairMinor atom scale pivot slot := by
  classical
  by_contra hnone
  refine false_of_pivot_witness hframe hsmall hpivot bulk weight hbudget fun slot hslot => ?_
  by_contra hlt
  exact hnone ⟨slot, (Finset.mem_erase.mp hslot).1, lt_of_not_ge hlt⟩

/-! ## Layer 3 — the deflated strata -/

/-- **THE HEAVY SLOT OF A PIVOT.**  At a pivot of positive deflated trace
some slot outside the pivot carries a deflated diagonal entry above its
own scale share of that trace.

This is the bulk witness of the deflated ledger read positively, and its
proof is one summation: if every slot were light the deflated trace would
have to pay the whole outside scale mass, and the strict scale bound
forbids it.  The law is TIGHT at the regular tetrahedron: the four equal
atoms make it an equality exactly at scale mass one. -/
theorem exists_deflated_heavy_slot {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount}
    (hsmall : (∑ slot, scale slot) < 1)
    (htrace : 0 < atomPivotTrace atom scale pivot) :
    ∃ slot, slot ≠ pivot
      ∧ scale slot * atomPivotTrace atom scale pivot
        < (1 - scale pivot) * atomPivotCross atom scale pivot slot slot := by
  classical
  by_contra hnone
  have hlight : ∀ slot ∈ Finset.univ.erase pivot,
      (1 - scale pivot) * atomPivotCross atom scale pivot slot slot
        ≤ scale slot * atomPivotTrace atom scale pivot := by
    intro slot hslot
    by_contra hlt
    exact hnone ⟨slot, (Finset.mem_erase.mp hslot).1, lt_of_not_ge hlt⟩
  have hsum := Finset.sum_le_sum hlight
  rw [← Finset.mul_sum, ← Finset.sum_mul, ← atomPivotTrace_def,
    Finset.sum_erase_eq_sub (Finset.mem_univ pivot)] at hsum
  nlinarith [hsum, htrace, hsmall]

/-- **THE HEAVY SLOT AT A LIGHT PIVOT IS UNCONDITIONAL.**  A rank-three
frame with positive scales of total less than one carries a pivot of
positive shifted diagonal and, outside it, a slot whose deflated diagonal
entry beats its own scale share of the deflated trace. -/
theorem exists_deflated_heavy_slot_of_light_pivot {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin 6 → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ 0 < atomPivotTrace atom scale pivot
      ∧ ∃ slot, slot ≠ pivot
        ∧ scale slot * atomPivotTrace atom scale pivot
          < (1 - scale pivot) * atomPivotCross atom scale pivot slot slot := by
  classical
  have hnonempty : (Finset.univ : Finset (Fin 6)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hmass : 0 < ∑ slot, scale slot := Finset.sum_pos (fun slot _ => hscale slot) hnonempty
  obtain ⟨pivot, hlight, hpivot⟩ :=
    exists_light_pivot hframe hscale hnonempty (by push_cast; linarith [hsmall])
  have hlight' : scale pivot * (3 - ∑ slot, scale slot)
      ≤ (∑ slot, scale slot) * atomShiftedDiag atom scale pivot := by
    have : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
    rw [this] at hlight
    exact hlight
  have htrace := atomPivotTrace_pos_of_light hframe (hscale pivot) hsmall hmass hlight' hpivot
  exact ⟨pivot, hpivot, htrace, exists_deflated_heavy_slot hsmall htrace⟩

/-- **THE DEFLATED GAP TOTAL IS POSITIVE AT A HEAVY PIVOT.**  At rank
three a pivot whose shifted diagonal beats twice its own scale carries a
deflated gap total above its own shifted diagonal against the scale gap.

The light pivot of the deflation layer obeys that bound at no cost, thus
the deflated pair search never starts empty. -/
theorem atomPairMinor_pivot_total_pos {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount}
    (hscale : 0 < scale pivot)
    (hheavy : 2 * scale pivot < atomShiftedDiag atom scale pivot) :
    atomShiftedDiag atom scale pivot * (1 - ∑ slot, scale slot)
      < ∑ slot ∈ Finset.univ.erase pivot, atomPairMinor atom scale pivot slot := by
  rw [atomPairMinor_pivot_total atom scale pivot, atomPivotTrace_eq hframe scale pivot]
  have hdiag : atomGram atom pivot pivot = atomShiftedDiag atom scale pivot + scale pivot := by
    simp only [atomShiftedDiag]
    ring
  rw [hdiag]
  push_cast
  nlinarith [hscale, hheavy]

/-- **THE DEFLATED PAIR SEARCH IS SELF-STARTING.**  A heavy pivot at a
rank-three frame with scales of total less than one carries a slot of
POSITIVE pivot minor, thus the pair `{pivot, slot}` already dominates its
own carrier. -/
theorem exists_positive_pivot_minor {atom : Fin slotCount → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount}
    (hscale : 0 < scale pivot) (hsmall : (∑ slot, scale slot) < 1)
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hheavy : 2 * scale pivot < atomShiftedDiag atom scale pivot) :
    ∃ slot, slot ≠ pivot ∧ 0 < atomPairMinor atom scale pivot slot := by
  classical
  by_contra hnone
  have hnonpos : ∀ slot ∈ Finset.univ.erase pivot, atomPairMinor atom scale pivot slot ≤ 0 := by
    intro slot hslot
    by_contra hlt
    exact hnone ⟨slot, (Finset.mem_erase.mp hslot).1, lt_of_not_ge hlt⟩
  have hsum := Finset.sum_nonpos hnonpos
  have hpos := atomPairMinor_pivot_total_pos hframe hscale hheavy
  nlinarith [hsum, hpos, hpivot, hsmall]

/-- **THE LAUNCH PAD OF THE DEFLATED SEARCH.**  A rank-three frame on six
slots with positive scales of total less than one carries a pivot that is
at the same time light, heavy against its own scale, of positive deflated
trace, of positive deflated gap total, and paired with a slot of positive
pivot minor.

Thus every hypothesis that the deflated ledger asks of a pivot holds at
one and the same pivot, and it holds unconditionally. -/
theorem exists_light_pivot_launch {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin 6 → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ pivot : Fin 6, 0 < atomShiftedDiag atom scale pivot
      ∧ 2 * scale pivot < atomShiftedDiag atom scale pivot
      ∧ 0 < atomPivotTrace atom scale pivot
      ∧ atomShiftedDiag atom scale pivot * (1 - ∑ slot, scale slot)
        < ∑ slot ∈ Finset.univ.erase pivot, atomPairMinor atom scale pivot slot
      ∧ ∃ slot, slot ≠ pivot ∧ 0 < atomPairMinor atom scale pivot slot := by
  classical
  have hnonempty : (Finset.univ : Finset (Fin 6)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hmass : 0 < ∑ slot, scale slot := Finset.sum_pos (fun slot _ => hscale slot) hnonempty
  obtain ⟨pivot, hlight, hpivot⟩ :=
    exists_light_pivot hframe hscale hnonempty (by push_cast; linarith [hsmall])
  have hlight' : scale pivot * (3 - ∑ slot, scale slot)
      ≤ (∑ slot, scale slot) * atomShiftedDiag atom scale pivot := by
    have hcast : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
    rw [hcast] at hlight
    exact hlight
  have hheavy : 2 * scale pivot < atomShiftedDiag atom scale pivot := by
    nlinarith [hlight', hscale pivot, hmass, hsmall, hpivot]
  exact ⟨pivot, hpivot, hheavy,
    atomPivotTrace_pos_of_light hframe (hscale pivot) hsmall hmass hlight' hpivot,
    atomPairMinor_pivot_total_pos hframe (hscale pivot) hheavy,
    exists_positive_pivot_minor hframe (hscale pivot) hsmall hpivot hheavy⟩

/-- **THE DOMINATING PAIR AT A LIGHT PIVOT.**  The selection theorem of
the Gram layer supplies a dominating pair somewhere.  The launch pad
supplies one whose FIRST slot is the light pivot itself, thus the pivot
of the deflation and the pivot of the selection are the same slot. -/
theorem exists_dominating_pair_at_light_pivot {atom : Fin 6 → (Fin 3 → ℝ)}
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {scale : Fin 6 → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1) :
    ∃ pivot slot : Fin 6, pivot ≠ slot
      ∧ 2 * scale pivot < atomShiftedDiag atom scale pivot
      ∧ 0 < atomShiftedDiag atom scale pivot
      ∧ 0 < atomPairMinor atom scale pivot slot := by
  obtain ⟨pivot, hpivot, hheavy, _, _, slot, hne, hminor⟩ :=
    exists_light_pivot_launch hframe hscale hsmall
  exact ⟨pivot, slot, Ne.symm hne, hheavy, hpivot, hminor⟩

/-- **THE DEFLATED PAIR HYPOTHESIS PRICED ON A CONIC WITNESS.**  When the
deflated witness directions are the deflated columns themselves and the
weights are nonnegative, the failure of every deflated pair turns the
deflated witness energy of one slot into a total over the whole outside
region. -/
theorem atomPivot_weight_dominates (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot : Fin slotCount) (weight : Fin slotCount → ℝ)
    (hweight : ∀ index, 0 ≤ weight index)
    (hfail : ∀ slotOne slotTwo : Fin slotCount, slotOne ≠ pivot → slotTwo ≠ pivot →
      slotOne ≠ slotTwo → 0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2)
    {slot : Fin slotCount} (hslot : slot ≠ pivot)
    (hpos : 0 < atomPairMinor atom scale pivot slot) :
    weight slot * atomPivotCross atom scale pivot slot slot ^ 2
        + atomPairMinor atom scale pivot slot
          * ((∑ index ∈ Finset.univ.erase pivot,
                weight index * atomPairMinor atom scale pivot index)
            - weight slot * atomPairMinor atom scale pivot slot)
      ≤ ∑ index ∈ Finset.univ.erase pivot,
          weight index * atomPivotCross atom scale pivot slot index ^ 2 := by
  classical
  have hmem : slot ∈ Finset.univ.erase pivot := Finset.mem_erase.mpr ⟨hslot, Finset.mem_univ _⟩
  have hsplitLeft : (∑ index ∈ Finset.univ.erase pivot,
        weight index * atomPairMinor atom scale pivot index)
      - weight slot * atomPairMinor atom scale pivot slot
      = ∑ index ∈ (Finset.univ.erase pivot).erase slot,
          weight index * atomPairMinor atom scale pivot index :=
    (Finset.sum_erase_eq_sub hmem).symm
  have hsplitRight : (∑ index ∈ Finset.univ.erase pivot,
        weight index * atomPivotCross atom scale pivot slot index ^ 2)
      = weight slot * atomPivotCross atom scale pivot slot slot ^ 2
        + ∑ index ∈ (Finset.univ.erase pivot).erase slot,
            weight index * atomPivotCross atom scale pivot slot index ^ 2 := by
    rw [Finset.sum_erase_eq_sub hmem]
    ring
  rw [hsplitLeft, hsplitRight, Finset.mul_sum]
  have hcell : ∀ index ∈ (Finset.univ.erase pivot).erase slot,
      atomPairMinor atom scale pivot slot
          * (weight index * atomPairMinor atom scale pivot index)
        ≤ weight index * atomPivotCross atom scale pivot slot index ^ 2 := by
    intro index hindex
    have hne : slot ≠ index := fun heq => (Finset.mem_erase.mp hindex).1 heq.symm
    have hindexPivot : index ≠ pivot :=
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hindex)).1
    have hbound := hfail slot index hslot hindexPivot hne hpos
    calc atomPairMinor atom scale pivot slot
          * (weight index * atomPairMinor atom scale pivot index)
        = weight index * (atomPairMinor atom scale pivot slot
            * atomPairMinor atom scale pivot index) := by ring
      _ ≤ weight index * atomPivotCross atom scale pivot slot index ^ 2 :=
          mul_le_mul_of_nonneg_left hbound (hweight index)
  linarith [Finset.sum_le_sum hcell]

/-- **THE RANK-ONE STRATUM OF THE THIRD RUNG.**  At a pivot of positive
shifted diagonal, a slot of positive pivot minor whose scale and pivot
row stay inside the deflated defect supplies a SECOND slot that passes
the deflated pair test.

The witness is the deflated column of that slot, its budget is the
deflated column energy, and the deflated gap total pays for it.  The
hypothesis is one polynomial inequality in four Gram entries and two
scales, and no estimate enters the proof.

At a pivot and a slot of vanishing scale the hypothesis is an equality,
thus the stratum is exactly sharp on the boundary of the plane lane. -/
theorem exists_pivotPair_of_deflated_rank_one {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {pivot heavy : Fin slotCount}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hnonneg : ∀ slot, 0 ≤ scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hheavy : heavy ≠ pivot)
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hminor : 0 < atomPairMinor atom scale pivot heavy)
    (hbudget : atomShiftedDiag atom scale pivot ^ 2 * scale heavy
        + scale pivot * (1 - scale pivot) * atomGram atom pivot heavy ^ 2
      ≤ atomPivotDefect atom scale pivot * atomPairMinor atom scale pivot heavy) :
    ∃ slot, slot ≠ pivot ∧ slot ≠ heavy
      ∧ atomPivotCross atom scale pivot heavy slot ^ 2
        < atomPairMinor atom scale pivot heavy * atomPairMinor atom scale pivot slot := by
  classical
  by_contra hnone
  have hfail : ∀ slot ∈ Finset.univ.erase pivot,
      atomPairMinor atom scale pivot heavy * atomPairMinor atom scale pivot slot
        ≤ atomPivotCross atom scale pivot heavy slot ^ 2 := by
    intro slot hslot
    have hslotPivot : slot ≠ pivot := (Finset.mem_erase.mp hslot).1
    by_cases hsame : slot = heavy
    · subst hsame
      have hself := atomPivotCross_self atom scale pivot slot
      have hnn : 0 ≤ atomShiftedDiag atom scale pivot * scale slot :=
        mul_nonneg hpivot.le (hnonneg slot)
      nlinarith [hminor, hself, hnn]
    · by_contra hlt
      exact hnone ⟨slot, hslotPivot, hsame, lt_of_not_ge hlt⟩
  have hsum := Finset.sum_le_sum hfail
  rw [← Finset.mul_sum, atomPairMinor_pivot_total atom scale pivot,
    atomPivotCross_row_square hframe scale pivot heavy] at hsum
  have hself := atomPivotCross_self atom scale pivot heavy
  have hdefect : atomPivotDefect atom scale pivot
      = atomPivotTrace atom scale pivot
        - atomShiftedDiag atom scale pivot * (2 - scale pivot) := rfl
  have hslack : atomShiftedDiag atom scale pivot * ((∑ slot, scale slot) - scale pivot)
      < atomShiftedDiag atom scale pivot * (1 - scale pivot) := by
    have hstrict : (∑ slot, scale slot) - scale pivot < 1 - scale pivot := by linarith [hsmall]
    exact mul_lt_mul_of_pos_left hstrict hpivot
  rw [hdefect] at hbudget
  nlinarith [hsum, hbudget, hminor, hslack, hself]

/-- **THE CONIC STRATUM OF THE THIRD RUNG.**  At a pivot of positive
shifted diagonal, a nonnegative family of weights whose deflated budget
stays inside the deflated gap and whose conic law dominates every slot of
positive pivot minor supplies a deflated pair.

The witness directions are the deflated columns themselves, and the
failure of every deflated pair prices every cross term. -/
theorem exists_pivotPair_of_deflated_conic {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount} (weight : Fin slotCount → ℝ)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hsmall : (∑ slot, scale slot) < 1)
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hweight : ∀ index, 0 ≤ weight index)
    (hbudget : (∑ index ∈ Finset.univ.erase pivot,
          weight index
            * (atomShiftedDiag atom scale pivot
                * atomPivotCross atom scale pivot index index
              + scale pivot * (1 - scale pivot) * atomGram atom pivot index ^ 2))
      ≤ atomPivotTrace atom scale pivot
        - atomShiftedDiag atom scale pivot * (1 - scale pivot))
    (hconic : ∀ slot, slot ≠ pivot → 0 < atomPairMinor atom scale pivot slot →
      atomPairMinor atom scale pivot slot
        ≤ weight slot * atomPivotCross atom scale pivot slot slot ^ 2
          + atomPairMinor atom scale pivot slot
            * ((∑ index ∈ Finset.univ.erase pivot,
                  weight index * atomPairMinor atom scale pivot index)
              - weight slot * atomPairMinor atom scale pivot slot)) :
    ∃ slotOne slotTwo : Fin slotCount, slotOne ≠ pivot ∧ slotTwo ≠ pivot ∧ slotOne ≠ slotTwo
      ∧ 0 < atomPairMinor atom scale pivot slotOne
      ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
        < atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo := by
  classical
  by_contra hnone
  have hfail : ∀ slotOne slotTwo : Fin slotCount, slotOne ≠ pivot → slotTwo ≠ pivot →
      slotOne ≠ slotTwo → 0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2 := by
    intro slotOne slotTwo hone htwo hne hpos
    by_contra hlt
    exact hnone ⟨slotOne, slotTwo, hone, htwo, hne, hpos, lt_of_not_ge hlt⟩
  refine false_of_pivot_witness hframe hsmall hpivot 0 weight (by simpa using hbudget)
    fun slot hslot => ?_
  have hslotPivot : slot ≠ pivot := (Finset.mem_erase.mp hslot).1
  rw [zero_mul, zero_add]
  rcases le_or_gt (atomPairMinor atom scale pivot slot) 0 with hneg | hpos
  · exact le_trans hneg (Finset.sum_nonneg fun index _ =>
      mul_nonneg (hweight index) (sq_nonneg _))
  · exact le_trans (hconic slot hslotPivot hpos)
      (atomPivot_weight_dominates atom scale pivot weight hweight hfail hslotPivot hpos)

/-- **THE MIXED STRATUM OF THE THIRD RUNG.**  A deflated witness that
mixes a bulk share of the deflated diagonal with a nonnegative family of
deflated directions supplies a deflated pair.

This is the general two-term stratum: the conic stratum is its vanishing
bulk, and the rank-one stratum is its single-slot weight family.  The
mixing law is one polynomial inequality at each slot of positive pivot
minor, and the deflated diagonal identity turns it into a statement in
the pivot minors alone. -/
theorem exists_pivotPair_of_deflated_mixed {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {pivot : Fin slotCount} (bulk : ℝ) (weight : Fin slotCount → ℝ)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hsmall : (∑ slot, scale slot) < 1)
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hbulk : 0 ≤ bulk) (hbulkCap : bulk ≤ 1)
    (hweight : ∀ index, 0 ≤ weight index)
    (hnonneg : ∀ slot, 0 ≤ scale slot)
    (hbudget : bulk * atomPivotTrace atom scale pivot
        + (∑ index ∈ Finset.univ.erase pivot,
            weight index
              * (atomShiftedDiag atom scale pivot
                  * atomPivotCross atom scale pivot index index
                + scale pivot * (1 - scale pivot) * atomGram atom pivot index ^ 2))
      ≤ atomPivotTrace atom scale pivot
        - atomShiftedDiag atom scale pivot * (1 - scale pivot))
    (hmix : ∀ slot, slot ≠ pivot → 0 < atomPairMinor atom scale pivot slot →
      atomPairMinor atom scale pivot slot
        ≤ bulk * (atomPairMinor atom scale pivot slot
            + atomShiftedDiag atom scale pivot * scale slot)
          + (weight slot * atomPivotCross atom scale pivot slot slot ^ 2
            + atomPairMinor atom scale pivot slot
              * ((∑ index ∈ Finset.univ.erase pivot,
                    weight index * atomPairMinor atom scale pivot index)
                - weight slot * atomPairMinor atom scale pivot slot))) :
    ∃ slotOne slotTwo : Fin slotCount, slotOne ≠ pivot ∧ slotTwo ≠ pivot ∧ slotOne ≠ slotTwo
      ∧ 0 < atomPairMinor atom scale pivot slotOne
      ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
        < atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo := by
  classical
  by_contra hnone
  have hfail : ∀ slotOne slotTwo : Fin slotCount, slotOne ≠ pivot → slotTwo ≠ pivot →
      slotOne ≠ slotTwo → 0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2 := by
    intro slotOne slotTwo hone htwo hne hpos
    by_contra hlt
    exact hnone ⟨slotOne, slotTwo, hone, htwo, hne, hpos, lt_of_not_ge hlt⟩
  refine false_of_pivot_witness hframe hsmall hpivot bulk weight hbudget fun slot hslot => ?_
  have hslotPivot : slot ≠ pivot := (Finset.mem_erase.mp hslot).1
  have hself := atomPivotCross_self atom scale pivot slot
  have hshift : 0 ≤ atomShiftedDiag atom scale pivot * scale slot :=
    mul_nonneg hpivot.le (hnonneg slot)
  rcases le_or_gt (atomPairMinor atom scale pivot slot) 0 with hneg | hpos
  · have hsq : 0 ≤ ∑ index ∈ Finset.univ.erase pivot,
        weight index * atomPivotCross atom scale pivot slot index ^ 2 :=
      Finset.sum_nonneg fun index _ => mul_nonneg (hweight index) (sq_nonneg _)
    nlinarith [hneg, hbulk, hbulkCap, hshift, hself, hsq]
  · have hconic := atomPivot_weight_dominates atom scale pivot weight hweight hfail hslotPivot hpos
    have hmixed := hmix slot hslotPivot hpos
    nlinarith [hmixed, hconic, hself, hbulk]

/-! ## Layer 4 — the cross square total and the margin -/

/-- **THE CROSS SQUARE TOTAL.**  The squares of one deflated row, summed
over every slot outside the pivot AND outside that row, have a closed
form in the Gram of the pivot and of the row.

The proof is the deflated column energy minus the diagonal term, thus it
needs the two frame laws only. -/
theorem atomPivotCross_row_square_total {atom : Fin slotCount → (Fin rank → ℝ)}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (scale : Fin slotCount → ℝ) {pivot rowSlot : Fin slotCount} (hne : rowSlot ≠ pivot) :
    (∑ slot ∈ (Finset.univ.erase pivot).erase rowSlot,
        atomPivotCross atom scale pivot rowSlot slot ^ 2)
      = atomShiftedDiag atom scale pivot * atomPivotCross atom scale pivot rowSlot rowSlot
        + scale pivot * (1 - scale pivot) * atomGram atom pivot rowSlot ^ 2
        - atomPivotCross atom scale pivot rowSlot rowSlot ^ 2 := by
  classical
  have hmem : rowSlot ∈ Finset.univ.erase pivot :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  rw [Finset.sum_erase_eq_sub hmem, atomPivotCross_row_square hframe scale pivot rowSlot]

/-- **THE MARGIN OF A PIVOT PAIR, FROM THE CROSS SQUARE TOTAL.**  A slot
whose pivot minor beats the cross square total of its own deflated row
supplies a second slot that passes the deflated pair test.

This is the extension total of the deflation layer re-derived through the
deflated calculus instead of the Schur split: the two routes agree, and
the cross square total is the closed form that a certificate reads
directly. -/
theorem exists_pivotPair_of_cross_margin {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} {pivot heavy : Fin slotCount}
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hheavy : heavy ≠ pivot)
    (hmargin : atomShiftedDiag atom scale pivot
          * atomPivotCross atom scale pivot heavy heavy
        + scale pivot * (1 - scale pivot) * atomGram atom pivot heavy ^ 2
        - atomPivotCross atom scale pivot heavy heavy ^ 2
      < atomPairMinor atom scale pivot heavy
        * ((∑ slot ∈ Finset.univ.erase pivot, atomPairMinor atom scale pivot slot)
          - atomPairMinor atom scale pivot heavy)) :
    ∃ slot, slot ≠ pivot ∧ slot ≠ heavy
      ∧ atomPivotCross atom scale pivot heavy slot ^ 2
        < atomPairMinor atom scale pivot heavy * atomPairMinor atom scale pivot slot := by
  classical
  by_contra hnone
  have hmem : heavy ∈ Finset.univ.erase pivot :=
    Finset.mem_erase.mpr ⟨hheavy, Finset.mem_univ _⟩
  have hfail : ∀ slot ∈ (Finset.univ.erase pivot).erase heavy,
      atomPairMinor atom scale pivot heavy * atomPairMinor atom scale pivot slot
        ≤ atomPivotCross atom scale pivot heavy slot ^ 2 := by
    intro slot hslot
    have hslotPivot : slot ≠ pivot :=
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hslot)).1
    have hslotHeavy : slot ≠ heavy := (Finset.mem_erase.mp hslot).1
    by_contra hlt
    exact hnone ⟨slot, hslotPivot, hslotHeavy, lt_of_not_ge hlt⟩
  have hsum := Finset.sum_le_sum hfail
  rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hmem,
    atomPivotCross_row_square_total hframe scale hheavy] at hsum
  linarith [hsum, hmargin]

/-! ## Layer 5 — the ambient witness engine read positively -/

/-- **THE POSITIVE READING OF THE AMBIENT KILL.**  Every ambient witness
of budget one below the rank misses at least one slot. -/
theorem exists_frame_witness_defect {witnessCount : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (probe : Fin witnessCount → (Fin rank → ℝ)) (weight : Fin witnessCount → ℝ) (bulk : ℝ)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ first other : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ first) * (atom slot ⬝ᵥ other)) = first ⬝ᵥ other)
    (hbudget : (rank : ℝ) * bulk + (∑ index, weight index * (probe index ⬝ᵥ probe index))
      ≤ (rank : ℝ) - 1) :
    ∃ slot, bulk * (atom slot ⬝ᵥ atom slot)
        + (∑ index, weight index * (atom slot ⬝ᵥ probe index) ^ 2)
      < atom slot ⬝ᵥ atom slot - scale slot := by
  classical
  by_contra hnone
  refine false_of_frame_witness atom scale probe weight bulk hsmall hframe hbudget fun slot => ?_
  by_contra hlt
  exact hnone ⟨slot, lt_of_not_ge hlt⟩

/-- **NO DIRECTION IS UNIFORMLY LIGHT.**  At a tight frame with scales of
total less than one, EVERY nonzero direction is read heavily by ONE
single atom: the squared reading of that atom beats the probe energy
scaled by its own scale.

The witness is the orthogonal projection off the direction, its trace is
one below the rank, and the trace law of the frame pays for it exactly.
The law is strictly stronger than the domination of the whole slot set,
because one atom already carries the whole probe.

The law is TIGHT at the regular tetrahedron: at a coordinate direction
the four equal atoms read exactly one quarter of the probe energy, and
the four equal scales are exactly one quarter at scale mass one. -/
theorem exists_heavy_reading {atom : Fin slotCount → (Fin rank → ℝ)}
    (scale : Fin slotCount → ℝ)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ first other : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ first) * (atom slot ⬝ᵥ other)) = first ⬝ᵥ other)
    {direction : Fin rank → ℝ} (hne : direction ≠ 0) :
    ∃ slot, scale slot * (direction ⬝ᵥ direction) < (atom slot ⬝ᵥ direction) ^ 2 := by
  classical
  have henergy : (0 : ℝ) < direction ⬝ᵥ direction := dotProduct_self_pos hne
  by_contra hnone
  refine false_of_frame_witness atom scale (fun _ : Fin 1 => direction)
    (fun _ => -(direction ⬝ᵥ direction)⁻¹) 1 hsmall hframe ?_ fun slot => ?_
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, mul_one, neg_mul]
    rw [inv_mul_cancel₀ (ne_of_gt henergy)]
    linarith
  · have hcap : (atom slot ⬝ᵥ direction) ^ 2 ≤ scale slot * (direction ⬝ᵥ direction) := by
      by_contra hlt
      exact hnone ⟨slot, lt_of_not_ge hlt⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, one_mul, neg_mul]
    have hshape : (direction ⬝ᵥ direction)⁻¹ * (atom slot ⬝ᵥ direction) ^ 2 ≤ scale slot := by
      rw [inv_mul_eq_div, div_le_iff₀ henergy]
      linarith [hcap]
    linarith [hshape]

/-- **THE SHARE READING.**  At a tight frame with scales of total less
than one, every family of shares whose energy total is one is read
heavily by ONE single atom.

This is the trace-one form of the heavy reading law: the witness is the
identity minus the share form, and its budget is one below the rank. -/
theorem exists_heavy_share_reading {witnessCount : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (probe : Fin witnessCount → (Fin rank → ℝ))
    (share : Fin witnessCount → ℝ)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ first other : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ first) * (atom slot ⬝ᵥ other)) = first ⬝ᵥ other)
    (htrace : (∑ index, share index * (probe index ⬝ᵥ probe index)) = 1) :
    ∃ slot, scale slot < ∑ index, share index * (atom slot ⬝ᵥ probe index) ^ 2 := by
  classical
  by_contra hnone
  refine false_of_frame_witness atom scale probe (fun index => -share index) 1 hsmall hframe
    ?_ fun slot => ?_
  · have hneg : (∑ index, -share index * (probe index ⬝ᵥ probe index))
        = -(∑ index, share index * (probe index ⬝ᵥ probe index)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun index _ => by ring
    rw [hneg, htrace, mul_one]
    linarith
  · have hcap : (∑ index, share index * (atom slot ⬝ᵥ probe index) ^ 2) ≤ scale slot := by
      by_contra hlt
      exact hnone ⟨slot, lt_of_not_ge hlt⟩
    have hneg : (∑ index, -share index * (atom slot ⬝ᵥ probe index) ^ 2)
        = -(∑ index, share index * (atom slot ⬝ᵥ probe index) ^ 2) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun index _ => by ring
    rw [hneg, one_mul]
    linarith [hcap]

/-- **THE PLANE READING.**  Two orthonormal probe directions of a tight
frame with scales of total less than one are read heavily by ONE single
atom: its squared readings of the two directions total more than twice
its own scale. -/
theorem exists_heavy_reading_of_plane {atom : Fin slotCount → (Fin rank → ℝ)}
    (scale : Fin slotCount → ℝ) {first second : Fin rank → ℝ}
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe other : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other)
    (hfirst : first ⬝ᵥ first = 1) (hsecond : second ⬝ᵥ second = 1) :
    ∃ slot, 2 * scale slot < (atom slot ⬝ᵥ first) ^ 2 + (atom slot ⬝ᵥ second) ^ 2 := by
  classical
  obtain ⟨slot, hslot⟩ := exists_heavy_share_reading atom scale ![first, second]
    (fun _ => 1 / 2) hsmall hframe (by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hfirst, hsecond]
      norm_num)
  refine ⟨slot, ?_⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hslot
  linarith [hslot]

/-- **THE SHARE DEFECT IN THE ATOM LANE.**  At a tight frame with scales
of total less than one, every family of shares whose Gram trace is one
leaves a slot whose scale is below its own share energy.

This is the master unconditional law of the atom lane: every named law
that follows is one instance of it. -/
theorem exists_share_defect_slot {atom : Fin slotCount → (Fin rank → ℝ)}
    (scale share : Fin slotCount → ℝ)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (htrace : (∑ index, share index * atomGram atom index index) = 1) :
    ∃ slot, scale slot < ∑ index, share index * atomGram atom slot index ^ 2 :=
  exists_heavy_share_reading atom scale atom share hsmall hframe htrace

/-- **THE GRAM DEFECT IN THE ATOM LANE.**  At every slot of positive
diagonal entry some slot beats the Gram test of that slot.  The share of
one slot returns it. -/
theorem exists_gram_defect_slot {atom : Fin slotCount → (Fin rank → ℝ)}
    (scale : Fin slotCount → ℝ)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {pivot : Fin slotCount} (hpivot : 0 < atomGram atom pivot pivot) :
    ∃ slot, scale slot * atomGram atom pivot pivot < atomGram atom slot pivot ^ 2 := by
  classical
  obtain ⟨slot, hslot⟩ := exists_heavy_reading (atom := atom) scale hsmall hframe
    (direction := atom pivot) (by
      intro hzero
      have hself : atomGram atom pivot pivot = 0 := by
        simp only [atomGram, hzero]
        exact dotProduct_zero _
      rw [hself] at hpivot
      exact absurd hpivot (lt_irrefl 0))
  exact ⟨slot, hslot⟩

/-- **THE TWO-PIVOT GRAM DEFECT.**  At a tight frame with scales of total
less than one, ANY TWO slots of positive diagonal entry are beaten
together by ONE single slot: the two squared Gram entries of that slot,
each weighted by the other diagonal, beat twice its own scale against
the product of the two diagonals.

The budget of the ambient witness is one below the rank, thus a rank-one
witness wastes a whole unit.  This law spends the whole budget, and it is
strictly stronger than the Gram defect at either slot alone. -/
theorem exists_two_pivot_gram_defect {atom : Fin slotCount → (Fin rank → ℝ)}
    (scale : Fin slotCount → ℝ)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {first second : Fin slotCount} (hne : first ≠ second)
    (hfirst : 0 < atomGram atom first first) (hsecond : 0 < atomGram atom second second) :
    ∃ slot, 2 * scale slot * (atomGram atom first first * atomGram atom second second)
      < atomGram atom slot first ^ 2 * atomGram atom second second
        + atomGram atom slot second ^ 2 * atomGram atom first first := by
  classical
  set share : Fin slotCount → ℝ := fun index =>
    if index = first then (2 * atomGram atom first first)⁻¹
    else if index = second then (2 * atomGram atom second second)⁻¹ else 0 with hshare
  have hfirstVal : share first = (2 * atomGram atom first first)⁻¹ := by
    simp only [hshare, if_pos rfl]
  have hswap : second ≠ first := Ne.symm hne
  have hsecondVal : share second = (2 * atomGram atom second second)⁻¹ := by
    simp [hshare, hswap]
  have hother : ∀ index, index ≠ first → index ≠ second → share index = 0 := by
    intro index hone htwo
    simp only [hshare, if_neg hone, if_neg htwo]
  have hpair : ∀ value : Fin slotCount → ℝ,
      (∑ index, share index * value index) = share first * value first
        + share second * value second := by
    intro value
    refine sum_eq_pair_of_support hne fun index hnot => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    rw [hother index hnot.1 hnot.2, zero_mul]
  have htrace : (∑ index, share index * atomGram atom index index) = 1 := by
    rw [hpair, hfirstVal, hsecondVal, inv_mul_eq_div, inv_mul_eq_div]
    field_simp
    norm_num
  obtain ⟨slot, hslot⟩ := exists_share_defect_slot scale share hsmall hframe htrace
  refine ⟨slot, ?_⟩
  rw [hpair, hfirstVal, hsecondVal] at hslot
  have hshape : (2 * atomGram atom first first)⁻¹ * atomGram atom slot first ^ 2
      + (2 * atomGram atom second second)⁻¹ * atomGram atom slot second ^ 2
      = (atomGram atom slot first ^ 2 * atomGram atom second second
          + atomGram atom slot second ^ 2 * atomGram atom first first)
        / (2 * (atomGram atom first first * atomGram atom second second)) := by
    field_simp
  rw [hshape, lt_div_iff₀ (by positivity)] at hslot
  linarith [hslot]

/-- **THE WEIGHTED GRAM DEFECT.**  At a tight frame with scales of total
less than one, every nonnegative weight family of positive diagonal mass
is beaten by ONE slot: the weighted square total of the Gram row of that
slot beats its own scale against the diagonal mass.

This is the trace-one law with the normalization cleared, thus it carries
no division and it is the form that a certificate reads. -/
theorem exists_weighted_gram_defect {atom : Fin slotCount → (Fin rank → ℝ)}
    (scale weight : Fin slotCount → ℝ)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hmass : 0 < ∑ index, weight index * atomGram atom index index) :
    ∃ slot, scale slot * (∑ index, weight index * atomGram atom index index)
      < ∑ index, weight index * atomGram atom slot index ^ 2 := by
  classical
  set mass := ∑ index, weight index * atomGram atom index index with hmassDef
  obtain ⟨slot, hslot⟩ := exists_share_defect_slot scale (fun index => mass⁻¹ * weight index)
    hsmall hframe (by
      have hshape : (∑ index, mass⁻¹ * weight index * atomGram atom index index)
          = mass⁻¹ * ∑ index, weight index * atomGram atom index index := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun index _ => by ring
      rw [hshape, ← hmassDef, inv_mul_cancel₀ (ne_of_gt hmass)])
  refine ⟨slot, ?_⟩
  have hshape : (∑ index, mass⁻¹ * weight index * atomGram atom slot index ^ 2)
      = mass⁻¹ * ∑ index, weight index * atomGram atom slot index ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun index _ => by ring
  rw [hshape, inv_mul_eq_div, lt_div_iff₀ hmass] at hslot
  linarith [hslot]

/-- **THE REGION GRAM DEFECT.**  At a tight frame with scales of total
less than one, EVERY region of positive diagonal mass is beaten by ONE
slot: the square total of the Gram row of that slot over the region beats
its own scale against the diagonal mass of the region.

The law subsumes the Gram defect of one slot and the heavy slot of the
whole frame: a single slot returns the first, and the whole slot set
returns the second through the row energy law. -/
theorem exists_region_gram_defect {atom : Fin slotCount → (Fin rank → ℝ)}
    (scale : Fin slotCount → ℝ) (region : Finset (Fin slotCount))
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hmass : 0 < ∑ index ∈ region, atomGram atom index index) :
    ∃ slot, scale slot * (∑ index ∈ region, atomGram atom index index)
      < ∑ index ∈ region, atomGram atom slot index ^ 2 := by
  classical
  have hcell : ∀ (value : Fin slotCount → ℝ) (index : Fin slotCount),
      (if index ∈ region then (1 : ℝ) else 0) * value index
        = if index ∈ region then value index else 0 := by
    intro value index
    by_cases hmem : index ∈ region
    · rw [if_pos hmem, if_pos hmem, one_mul]
    · rw [if_neg hmem, if_neg hmem, zero_mul]
  have hsum : ∀ value : Fin slotCount → ℝ,
      (∑ index, (if index ∈ region then (1 : ℝ) else 0) * value index)
        = ∑ index ∈ region, value index := by
    intro value
    rw [Finset.sum_congr rfl fun index _ => hcell value index, Finset.sum_ite_mem,
      Finset.univ_inter]
  obtain ⟨slot, hslot⟩ := exists_weighted_gram_defect scale
    (fun index => if index ∈ region then (1 : ℝ) else 0) hsmall hframe
    (by rw [hsum]; exact hmass)
  refine ⟨slot, ?_⟩
  rw [hsum, hsum] at hslot
  exact hslot

/-- **THE HEAVY SLOT IN THE ATOM LANE.**  Some slot of a tight frame with
scales of total less than one carries a diagonal entry above the rank
against its own scale.  The constant share returns it. -/
theorem exists_heavy_atom_slot {atom : Fin slotCount → (Fin rank → ℝ)}
    (scale : Fin slotCount → ℝ) (hrank : 0 < rank)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ slot, (rank : ℝ) * scale slot < atomGram atom slot slot := by
  classical
  have hcast : (0 : ℝ) < (rank : ℝ) := by exact_mod_cast hrank
  obtain ⟨slot, hslot⟩ := exists_share_defect_slot scale (fun _ => ((rank : ℝ))⁻¹) hsmall hframe
    (by
      rw [← Finset.mul_sum, atomGram_trace hframe, inv_mul_cancel₀ (ne_of_gt hcast)])
  refine ⟨slot, ?_⟩
  rw [← Finset.mul_sum, atomGram_row_energy hframe slot, inv_mul_eq_div,
    lt_div_iff₀ hcast] at hslot
  linarith [hslot]

/-- **ONE SLOT ALREADY DOMINATES EVERY DIRECTION.**  At a tight frame
with positive scales of total less than one and reciprocal coefficients,
every nonzero direction is dominated by a SINGLE slot.

This is strictly stronger than the domination of the whole slot set,
which needs all six readings together. -/
theorem exists_single_slot_domination {atom : Fin slotCount → (Fin rank → ℝ)}
    {scale : Fin slotCount → ℝ} (hscale : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (coeff : Fin slotCount → ℝ) (hcoeff : ∀ slot, coeff slot * scale slot = 1)
    {direction : Fin rank → ℝ} (hne : direction ≠ 0) :
    ∃ slot, direction ⬝ᵥ direction < coeff slot * (atom slot ⬝ᵥ direction) ^ 2 := by
  obtain ⟨slot, hslot⟩ := exists_heavy_reading scale hsmall hframe hne
  refine ⟨slot, ?_⟩
  have hcoeffPos : 0 < coeff slot := by
    by_contra hnot
    nlinarith [hcoeff slot, hscale slot, not_lt.mp hnot]
  have hstep := mul_lt_mul_of_pos_left hslot hcoeffPos
  rw [← mul_assoc, hcoeff slot, one_mul] at hstep
  exact hstep

/-! ## Layer 6 — the unconditional share laws of every crux -/

/-- **THE MASTER UNCONDITIONAL LAW OF EVERY CRUX.**  At every crux, and
at every bulk value and share family whose chart budget stays one below
the rank, some atom fails the witness: its shifted weight is more than
the chart diagonal gap that the witness leaves.

The law consumes the frame law of the chart, the nonnegativity of the
shifted weights and the budget, and nothing else. -/
theorem SixThreeCrux.exists_witness_defect (crux : SixThreeCrux)
    (share : Fin 6 → ℝ) (bulk : ℝ)
    (hbudget : 3 * bulk
        + (∑ index, share index * (chartPointOfDesign crux.design).chart index index)
      ≤ 2) :
    ∃ atomIndex : Fin 6,
      bulk * (chartPointOfDesign crux.design).chart atomIndex atomIndex
          + (∑ index, share index
              * (chartPointOfDesign crux.design).chart atomIndex index ^ 2)
        < (chartPointOfDesign crux.design).chart atomIndex atomIndex
          - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex) := by
  classical
  obtain ⟨family, hnorm, horth, hsplit⟩ :=
    exists_orthonormal_family_of_trace 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).isSymmetric
      (chartPointOfDesign crux.design).isIdempotent
      (chartPointOfDesign crux.design).hasTraceRank
  have hentry : ∀ rowIndex colIndex : Fin 6,
      atomVec family rowIndex ⬝ᵥ atomVec family colIndex
        = (chartPointOfDesign crux.design).chart rowIndex colIndex :=
    fun rowIndex colIndex => (atomVec_dot_eq_split_apply hsplit rowIndex colIndex).symm
  obtain ⟨atomIndex, hdefect⟩ := exists_frame_witness_defect (rank := 3) (atomVec family)
    (fun index => chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight index)
    (atomVec family) share bulk crux.shifted_weight_sum_lt_one (atom_frame_law hnorm horth)
    (by
      simp only [hentry]
      push_cast
      linarith [hbudget])
  refine ⟨atomIndex, ?_⟩
  simp only [hentry] at hdefect
  exact hdefect

/-- **THE SHARE DEFECT OF A CRUX.**  At every crux, and at every family
of shares whose chart trace is one, SOME atom reads more share energy
than its own shifted weight.

The law is unconditional, and it SUBSUMES the two landed unconditional
laws of a crux: the constant share returns the heavy atom, and the share
of one slot returns the Gram defect at that slot. -/
theorem SixThreeCrux.exists_share_defect (crux : SixThreeCrux) (share : Fin 6 → ℝ)
    (htrace : (∑ index, share index * (chartPointOfDesign crux.design).chart index index) = 1) :
    ∃ atomIndex : Fin 6,
      chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex
        < ∑ index, share index
            * (chartPointOfDesign crux.design).chart atomIndex index ^ 2 := by
  classical
  obtain ⟨atomIndex, hdefect⟩ := crux.exists_witness_defect (fun index => -share index) 1 (by
    have hneg : (∑ index, -share index * (chartPointOfDesign crux.design).chart index index)
        = -(∑ index, share index * (chartPointOfDesign crux.design).chart index index) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun index _ => by ring
    rw [hneg, htrace]
    norm_num)
  refine ⟨atomIndex, ?_⟩
  have hneg : (∑ index, -share index
        * (chartPointOfDesign crux.design).chart atomIndex index ^ 2)
      = -(∑ index, share index
        * (chartPointOfDesign crux.design).chart atomIndex index ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun index _ => by ring
  rw [hneg, one_mul] at hdefect
  linarith [hdefect]

/-- **THE HEAVY ATOM FROM THE SHARE DEFECT.**  The constant share of one
third returns the heavy atom of every crux: the row energy law of the
chart turns the constant share into the chart diagonal itself. -/
theorem SixThreeCrux.exists_heavy_atom_of_share (crux : SixThreeCrux) :
    ∃ atomIndex : Fin 6,
      3 * (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        < (chartPointOfDesign crux.design).chart atomIndex atomIndex := by
  classical
  obtain ⟨family, hnorm, horth, hsplit⟩ :=
    exists_orthonormal_family_of_trace 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).isSymmetric
      (chartPointOfDesign crux.design).isIdempotent
      (chartPointOfDesign crux.design).hasTraceRank
  have hframe := atom_frame_law hnorm horth
  have hentry : ∀ rowIndex colIndex : Fin 6,
      atomVec family rowIndex ⬝ᵥ atomVec family colIndex
        = (chartPointOfDesign crux.design).chart rowIndex colIndex :=
    fun rowIndex colIndex => (atomVec_dot_eq_split_apply hsplit rowIndex colIndex).symm
  obtain ⟨atomIndex, hdefect⟩ := crux.exists_share_defect (fun _ => 1 / 3) (by
    rw [← Finset.mul_sum]
    have htrace : (∑ index, (chartPointOfDesign crux.design).chart index index) = (3 : ℝ) := by
      rw [Finset.sum_congr rfl fun index _ => (hentry index index).symm]
      have := atomGram_trace (atom := atomVec family) hframe
      simpa [atomGram] using this
    rw [htrace]
    norm_num)
  refine ⟨atomIndex, ?_⟩
  have hrow : (∑ index, (chartPointOfDesign crux.design).chart atomIndex index ^ 2)
      = (chartPointOfDesign crux.design).chart atomIndex atomIndex := by
    rw [Finset.sum_congr rfl fun index _ => by rw [← hentry atomIndex index],
      ← hentry atomIndex atomIndex]
    have := atomGram_row_energy (atom := atomVec family) hframe atomIndex
    simpa [atomGram] using this
  rw [← Finset.mul_sum, hrow] at hdefect
  linarith [hdefect]

/-- **THE GRAM DEFECT FROM THE SHARE DEFECT.**  The share of one slot
returns the Gram defect at that slot: at every atom of positive chart
diagonal some slot beats the Gram test of that atom. -/
theorem SixThreeCrux.exists_gram_defect_of_share (crux : SixThreeCrux) (pivot : Fin 6) :
    ∃ atomIndex : Fin 6,
      (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * (chartPointOfDesign crux.design).chart pivot pivot
        < (chartPointOfDesign crux.design).chart atomIndex pivot ^ 2 := by
  classical
  have hdiag := crux.chart_diagonal_pos pivot
  obtain ⟨atomIndex, hdefect⟩ := crux.exists_share_defect
    (fun index => if index = pivot then ((chartPointOfDesign crux.design).chart pivot pivot)⁻¹
      else 0) (by
      rw [Finset.sum_eq_single pivot]
      · rw [if_pos rfl, inv_mul_cancel₀ (ne_of_gt hdiag)]
      · intro index _ hne
        rw [if_neg hne, zero_mul]
      · intro hnot
        exact absurd (Finset.mem_univ pivot) hnot)
  refine ⟨atomIndex, ?_⟩
  rw [Finset.sum_eq_single pivot] at hdefect
  · rw [if_pos rfl, inv_mul_eq_div, lt_div_iff₀ hdiag] at hdefect
    linarith [hdefect]
  · intro index _ hne
    rw [if_neg hne, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_univ pivot) hnot

/-- **THE TWO-PIVOT GRAM DEFECT OF A CRUX.**  At every crux, any two
atoms are beaten together by ONE single atom: the two squared chart
entries of that atom, each weighted by the other chart diagonal, beat
twice its own shifted weight against the product of the two diagonals.

The chart diagonal of a crux is positive at every atom, thus the law
carries no hypothesis beyond the two atoms being different. -/
theorem SixThreeCrux.exists_two_pivot_gram_defect (crux : SixThreeCrux)
    {first second : Fin 6} (hne : first ≠ second) :
    ∃ atomIndex : Fin 6,
      2 * (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * ((chartPointOfDesign crux.design).chart first first
            * (chartPointOfDesign crux.design).chart second second)
        < (chartPointOfDesign crux.design).chart atomIndex first ^ 2
            * (chartPointOfDesign crux.design).chart second second
          + (chartPointOfDesign crux.design).chart atomIndex second ^ 2
            * (chartPointOfDesign crux.design).chart first first := by
  classical
  obtain ⟨family, hnorm, horth, hsplit⟩ :=
    exists_orthonormal_family_of_trace 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).isSymmetric
      (chartPointOfDesign crux.design).isIdempotent
      (chartPointOfDesign crux.design).hasTraceRank
  have hentry : ∀ rowIndex colIndex : Fin 6,
      atomGram (atomVec family) rowIndex colIndex
        = (chartPointOfDesign crux.design).chart rowIndex colIndex :=
    fun rowIndex colIndex => (atomVec_dot_eq_split_apply hsplit rowIndex colIndex).symm
  have hfirst : 0 < atomGram (atomVec family) first first := by
    rw [hentry]; exact crux.chart_diagonal_pos first
  have hsecond : 0 < atomGram (atomVec family) second second := by
    rw [hentry]; exact crux.chart_diagonal_pos second
  obtain ⟨atomIndex, hslot⟩ := _root_.Gtz.exists_two_pivot_gram_defect (atom := atomVec family)
    (fun index => chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight index)
    crux.shifted_weight_sum_lt_one (atom_frame_law hnorm horth) hne hfirst hsecond
  refine ⟨atomIndex, ?_⟩
  simp only [hentry] at hslot
  exact hslot

/-- **THE REGION GRAM DEFECT OF A CRUX.**  At every crux, EVERY nonempty
region of atoms is beaten by ONE atom: the square total of the chart row
of that atom over the region beats its own shifted weight against the
chart diagonal mass of the region.

The chart diagonal of a crux is positive at every atom, thus a nonempty
region is the only hypothesis.  The law holds over all sixty three
nonempty regions of the six atoms at once. -/
theorem SixThreeCrux.exists_region_gram_defect (crux : SixThreeCrux)
    (region : Finset (Fin 6)) (hregion : region.Nonempty) :
    ∃ atomIndex : Fin 6,
      (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * (∑ index ∈ region, (chartPointOfDesign crux.design).chart index index)
      < ∑ index ∈ region, (chartPointOfDesign crux.design).chart atomIndex index ^ 2 := by
  classical
  obtain ⟨family, hnorm, horth, hsplit⟩ :=
    exists_orthonormal_family_of_trace 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).isSymmetric
      (chartPointOfDesign crux.design).isIdempotent
      (chartPointOfDesign crux.design).hasTraceRank
  have hentry : ∀ rowIndex colIndex : Fin 6,
      atomGram (atomVec family) rowIndex colIndex
        = (chartPointOfDesign crux.design).chart rowIndex colIndex :=
    fun rowIndex colIndex => (atomVec_dot_eq_split_apply hsplit rowIndex colIndex).symm
  have hmass : 0 < ∑ index ∈ region, atomGram (atomVec family) index index := by
    refine Finset.sum_pos (fun index _ => ?_) hregion
    rw [hentry]
    exact crux.chart_diagonal_pos index
  obtain ⟨atomIndex, hslot⟩ := _root_.Gtz.exists_region_gram_defect (atom := atomVec family)
    (fun index => chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight index)
    region crux.shifted_weight_sum_lt_one (atom_frame_law hnorm horth) hmass
  refine ⟨atomIndex, ?_⟩
  simp only [hentry] at hslot
  exact hslot

/-! ## Layer 7 — the tightness of the third rung: the regular tetrahedron -/

/-- The TETRAHEDRAL ATOMS: the four vertices of a regular tetrahedron at
half scale, and two zero atoms.  Every entry is rational, and the four
nonzero atoms form a tight frame of the probe space on their own. -/
noncomputable def tetraFrame : Fin 6 → (Fin 3 → ℝ) :=
  ![![1/2, 1/2, 1/2], ![1/2, -1/2, -1/2], ![-1/2, 1/2, -1/2], ![-1/2, -1/2, 1/2],
    ![0, 0, 0], ![0, 0, 0]]

/-- The TETRAHEDRAL SCALES at one gap value: the four nonzero atoms share
the gap deficit equally, and the two zero atoms carry one eighth of the
gap each. -/
noncomputable def tetraFrameScale (gap : ℝ) : Fin 6 → ℝ :=
  ![(1 - gap) / 4, (1 - gap) / 4, (1 - gap) / 4, (1 - gap) / 4, gap / 8, gap / 8]

/-- The tetrahedral atoms form a tight frame of the probe space. -/
theorem tetraFrame_frame_law : ∀ probe direction : Fin 3 → ℝ,
    (∑ slot, (tetraFrame slot ⬝ᵥ probe) * (tetraFrame slot ⬝ᵥ direction)) = probe ⬝ᵥ direction := by
  intro probe direction
  simp [tetraFrame, dotProduct, Fin.sum_univ_six, Fin.sum_univ_three]
  ring

/-- The tetrahedral scales are positive inside the gap window. -/
theorem tetraFrameScale_pos {gap : ℝ} (hlow : 0 < gap) (hhigh : gap < 1) :
    ∀ slot, 0 < tetraFrameScale gap slot := by
  intro slot
  fin_cases slot <;> simp [tetraFrameScale] <;> linarith

/-- The tetrahedral scale mass is one minus three quarters of the gap. -/
theorem tetraFrameScale_sum (gap : ℝ) : (∑ slot, tetraFrameScale gap slot) = 1 - 3 * gap / 4 := by
  simp [tetraFrameScale, Fin.sum_univ_six]
  ring

/-- The shifted diagonal of the two zero atoms is negative, thus no
carrier that contains one of them is positive on its own span. -/
theorem tetraFrame_shiftedDiag_axis {gap : ℝ} (hlow : 0 < gap) :
    atomShiftedDiag tetraFrame (tetraFrameScale gap) 4 < 0
      ∧ atomShiftedDiag tetraFrame (tetraFrameScale gap) 5 < 0 := by
  constructor <;>
    · simp [atomShiftedDiag, atomGram, tetraFrame, tetraFrameScale, dotProduct, Fin.sum_univ_three]
      linarith

/-- **THE TETRAHEDRAL DETERMINANT.**  Every three-slot block of the four
tetrahedral atoms carries the same determinant: the gap against the
square of the gap plus three, over sixty four.

The determinant vanishes exactly at gap zero, that is exactly at scale
mass one.  Thus the third rung is TIGHT and the strict scale bound is
consumed with no slack. -/
theorem tetraFrame_tripleDet (gap : ℝ) :
    atomTripleDet tetraFrame (tetraFrameScale gap) 0 1 2 = gap * (3 + gap) ^ 2 / 64
      ∧ atomTripleDet tetraFrame (tetraFrameScale gap) 0 1 3 = gap * (3 + gap) ^ 2 / 64
      ∧ atomTripleDet tetraFrame (tetraFrameScale gap) 0 2 3 = gap * (3 + gap) ^ 2 / 64
      ∧ atomTripleDet tetraFrame (tetraFrameScale gap) 1 2 3 = gap * (3 + gap) ^ 2 / 64 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp [atomTripleDet, atomShiftedDiag, atomGram, tetraFrame, tetraFrameScale, dotProduct,
        Fin.sum_univ_three]
      ring

/-- **THE PIVOT PAIR TEST FIRES AT THE TETRAHEDRON, AND ONLY BY THE
GAP.**  At every positive gap the tetrahedral datum passes the deflated
pair test at the pivot zero, and the slack of that test is the shifted
diagonal of the pivot against the tetrahedral determinant. -/
theorem tetraFrame_pivotPair {gap : ℝ} (hlow : 0 < gap) (hhigh : gap < 1) :
    0 < atomShiftedDiag tetraFrame (tetraFrameScale gap) 0
      ∧ 0 < atomPairMinor tetraFrame (tetraFrameScale gap) 0 1
      ∧ atomPivotCross tetraFrame (tetraFrameScale gap) 0 1 2 ^ 2
        < atomPairMinor tetraFrame (tetraFrameScale gap) 0 1
          * atomPairMinor tetraFrame (tetraFrameScale gap) 0 2 := by
  have hdiag : atomShiftedDiag tetraFrame (tetraFrameScale gap) 0 = (2 + gap) / 4 := by
    simp [atomShiftedDiag, atomGram, tetraFrame, tetraFrameScale, dotProduct, Fin.sum_univ_three]
    ring
  have hminor : atomPairMinor tetraFrame (tetraFrameScale gap) 0 1
      = ((2 + gap) ^ 2 - 1) / 16 := by
    simp [atomPairMinor, atomShiftedDiag, atomGram, tetraFrame, tetraFrameScale, dotProduct,
      Fin.sum_univ_three]
    ring
  have hdet := (tetraFrame_tripleDet gap).1
  have hdeflate := atomTripleDet_deflate tetraFrame (tetraFrameScale gap) 0 1 2
  rw [hdet, hdiag] at hdeflate
  have hslack : 0 < (2 + gap) / 4 * (gap * (3 + gap) ^ 2 / 64) := by
    refine mul_pos (by linarith) (div_pos (mul_pos hlow (pow_pos (by linarith) 2)) (by norm_num))
  refine ⟨by rw [hdiag]; linarith, by rw [hminor]; nlinarith [hlow], ?_⟩
  linarith [hdeflate, hslack]

/-- **THE THIRD RUNG IS TIGHT.**  For every positive margin there is an
explicit rational tight frame of six atoms in three dimensions whose
positive scales total less than one but more than one minus the margin,
whose two zero atoms carry a negative shifted diagonal, and whose four
tetrahedral triples all carry a POSITIVE determinant BELOW the margin.

Thus every proof of the third rung must consume the strict scale bound,
and the regular tetrahedron shows that the bound is consumed with no
slack at all. -/
theorem exists_tight_frame_with_small_margin (margin : ℝ) (hmargin : 0 < margin) :
    ∃ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
      (∀ slot, 0 < scale slot)
        ∧ (∑ slot, scale slot) < 1
        ∧ 1 - margin < ∑ slot, scale slot
        ∧ (∀ probe direction : Fin 3 → ℝ,
            (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
        ∧ atomShiftedDiag atom scale 4 < 0
        ∧ atomShiftedDiag atom scale 5 < 0
        ∧ 0 < atomTripleDet atom scale 0 1 2 ∧ atomTripleDet atom scale 0 1 2 < margin
        ∧ 0 < atomTripleDet atom scale 0 1 3 ∧ atomTripleDet atom scale 0 1 3 < margin
        ∧ 0 < atomTripleDet atom scale 0 2 3 ∧ atomTripleDet atom scale 0 2 3 < margin
        ∧ 0 < atomTripleDet atom scale 1 2 3 ∧ atomTripleDet atom scale 1 2 3 < margin := by
  classical
  set gap : ℝ := min (1 / 2) margin with hgap
  have hlow : 0 < gap := lt_min (by norm_num) hmargin
  have hcapHalf : gap ≤ 1 / 2 := min_le_left _ _
  have hcapMargin : gap ≤ margin := min_le_right _ _
  have hhigh : gap < 1 := by linarith
  have hmass := tetraFrameScale_sum gap
  have hdet := tetraFrame_tripleDet gap
  have hbound : (3 + gap) ^ 2 ≤ 13 := by nlinarith [hlow, hcapHalf]
  have hstep : gap * (3 + gap) ^ 2 / 64 ≤ gap * 13 / 64 := by nlinarith [hlow, hbound]
  have hsmallDet : gap * (3 + gap) ^ 2 / 64 < margin := by
    have : gap * 13 / 64 < margin := by linarith [hcapMargin, hmargin]
    linarith [hstep]
  have hposDet : 0 < gap * (3 + gap) ^ 2 / 64 := by positivity
  obtain ⟨haxisFour, haxisFive⟩ := tetraFrame_shiftedDiag_axis hlow
  exact ⟨tetraFrame, tetraFrameScale gap, tetraFrameScale_pos hlow hhigh, by rw [hmass]; linarith,
    by rw [hmass]; linarith, tetraFrame_frame_law, haxisFour, haxisFive,
    by rw [hdet.1]; exact hposDet, by rw [hdet.1]; exact hsmallDet,
    by rw [hdet.2.1]; exact hposDet, by rw [hdet.2.1]; exact hsmallDet,
    by rw [hdet.2.2.1]; exact hposDet, by rw [hdet.2.2.1]; exact hsmallDet,
    by rw [hdet.2.2.2]; exact hposDet, by rw [hdet.2.2.2]; exact hsmallDet⟩

/-! ## Layer 8 — the third rung in dual form -/

/-- **THE THIRD RUNG IN DUAL FORM.**  At every rank-three frame on six
slots whose deflated pairs all fail at one pivot of positive shifted
diagonal there is a deflated witness of the deflated budget.

This residue is strictly smaller than the pivot pair residue.  It carries
seven real unknowns — one bulk value and six weights — its constraints
are linear in those unknowns at fixed data, and it carries no
combinatorial search, no eigenvalue and no square root. -/
def AtomPivotWitnessClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) (pivot : Fin 6),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    0 < atomShiftedDiag atom scale pivot →
    (∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot → slotOne ≠ slotTwo →
      0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2) →
    ∃ (weight : Fin 6 → ℝ) (bulk : ℝ),
      (bulk * atomPivotTrace atom scale pivot
          + (∑ index ∈ Finset.univ.erase pivot,
              weight index
                * (atomShiftedDiag atom scale pivot
                    * atomPivotCross atom scale pivot index index
                  + scale pivot * (1 - scale pivot) * atomGram atom pivot index ^ 2))
        ≤ atomPivotTrace atom scale pivot
          - atomShiftedDiag atom scale pivot * (1 - scale pivot))
      ∧ ∀ slot, slot ≠ pivot →
          atomPairMinor atom scale pivot slot
            ≤ bulk * atomPivotCross atom scale pivot slot slot
              + ∑ index ∈ Finset.univ.erase pivot,
                  weight index * atomPivotCross atom scale pivot slot index ^ 2

/-- **THE DUAL RESIDUE IS THE PIVOT PAIR RESIDUE.**  The light pivot
supplies the pivot, the failure of every deflated pair supplies the
hypothesis of the residue, and the deflated kill closes the loop. -/
theorem atomPivotPairClosed_of_pivotWitness
    (hresidue : AtomPivotWitnessClosed) : AtomPivotPairClosed := by
  classical
  intro atom scale hpos hsmall hframe
  by_contra hnone
  obtain ⟨pivot, hpivot⟩ :=
    exists_pivot_shiftedDiag_pos hframe hpos ⟨0, Finset.mem_univ 0⟩ hsmall
  have hfail : ∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot → slotOne ≠ slotTwo →
      0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2 := by
    intro slotOne slotTwo hone htwo hne hminor
    by_contra hlt
    exact hnone ⟨pivot, slotOne, slotTwo, Ne.symm hone, Ne.symm htwo, hne, hpivot, hminor,
      lt_of_not_ge hlt⟩
  obtain ⟨weight, bulk, hbudget, hdominate⟩ :=
    hresidue atom scale pivot hpos hsmall hframe hpivot hfail
  exact false_of_pivot_witness hframe hsmall hpivot bulk weight hbudget
    fun slot hslot => hdominate slot (Finset.mem_erase.mp hslot).1

/-- The polynomial residue of the third rung, from the dual residue. -/
theorem atomTripleSylvesterClosed_of_pivotWitness
    (hresidue : AtomPivotWitnessClosed) : AtomTripleSylvesterClosed :=
  atomTripleSylvesterClosed_of_pivotPair (atomPivotPairClosed_of_pivotWitness hresidue)

/-- The atom triple ceiling from the dual residue. -/
theorem atomTripleCeilingClosed_of_pivotWitness
    (hresidue : AtomPivotWitnessClosed) : AtomTripleCeilingClosed :=
  atomTripleCeilingClosed_of_pivotPair (atomPivotPairClosed_of_pivotWitness hresidue)

/-- **THE `(6,3)` CELL FROM THE DUAL RESIDUE.**  No interiority, no
stationarity, no eigenvalue and no combinatorial search: one bulk value
and six weights close the cell. -/
theorem gtzWeighted_six_three_of_pivotWitness
    (hresidue : AtomPivotWitnessClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_pivotPair (atomPivotPairClosed_of_pivotWitness hresidue)

/-- **ALL OF RANK THREE FROM THE DUAL RESIDUE.** -/
theorem gtzWeightedAll_three_of_pivotWitness
    (hresidue : AtomPivotWitnessClosed) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_pivotPair (atomPivotPairClosed_of_pivotWitness hresidue)

/-- The crux type is empty under the dual residue. -/
theorem isEmpty_sixThreeCrux_of_pivotWitness
    (hresidue : AtomPivotWitnessClosed) : IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_pivotPair (atomPivotPairClosed_of_pivotWitness hresidue)

/-- The rank-five dense branch from the dual residue. -/
theorem rankFiveDenseClosed_of_pivotWitness
    (hresidue : AtomPivotWitnessClosed) : RankFiveDenseClosed :=
  rankFiveDenseClosed_of_pivotPair (atomPivotPairClosed_of_pivotWitness hresidue)

/-- The rank-six dense branch from the dual residue. -/
theorem rankSixDenseClosed_of_pivotWitness
    (hresidue : AtomPivotWitnessClosed) : RankSixDenseClosed :=
  rankSixDenseClosed_of_pivotPair (atomPivotPairClosed_of_pivotWitness hresidue)

/-- The rank-six support-two closure from the dual residue. -/
theorem rankSixSupportTwoClosed_of_pivotWitness
    (hresidue : AtomPivotWitnessClosed) : RankSixSupportTwoClosed :=
  rankSixSupportTwoClosed_of_pivotPair (atomPivotPairClosed_of_pivotWitness hresidue)

/-- The rank-five support-two closure from the dual residue. -/
theorem rankFiveSupportTwoClosed_of_pivotWitness
    (hresidue : AtomPivotWitnessClosed) : RankFiveSupportTwoClosed :=
  rankFiveSupportTwoClosed_of_pivotPair (atomPivotPairClosed_of_pivotWitness hresidue)

/-- The rank-four support-two closure from the dual residue. -/
theorem rankFourSupportTwoClosed_of_pivotWitness
    (hresidue : AtomPivotWitnessClosed) : RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_pivotPair (atomPivotPairClosed_of_pivotWitness hresidue)

/-! ## Layer 9 — the residue at the light pivot -/

/-- **THE THIRD RUNG IN DUAL FORM AT THE LIGHT PIVOT.**  The launch pad
makes four properties of the pivot free: the pivot is heavy against its
own scale, its deflated trace is positive, its deflated gap total beats
the scale gap, and one slot outside it carries a positive pivot minor.

This residue may use all four, thus it is strictly smaller than
`Gtz.AtomPivotWitnessClosed`, and it closes the same cell. -/
def AtomLightPivotWitnessClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) (pivot : Fin 6),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) < 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    0 < atomShiftedDiag atom scale pivot →
    2 * scale pivot < atomShiftedDiag atom scale pivot →
    0 < atomPivotTrace atom scale pivot →
    (atomShiftedDiag atom scale pivot * (1 - ∑ slot, scale slot)
      < ∑ slot ∈ Finset.univ.erase pivot, atomPairMinor atom scale pivot slot) →
    (∃ heavy : Fin 6, heavy ≠ pivot ∧ 0 < atomPairMinor atom scale pivot heavy) →
    (∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot → slotOne ≠ slotTwo →
      0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2) →
    ∃ (weight : Fin 6 → ℝ) (bulk : ℝ),
      (bulk * atomPivotTrace atom scale pivot
          + (∑ index ∈ Finset.univ.erase pivot,
              weight index
                * (atomShiftedDiag atom scale pivot
                    * atomPivotCross atom scale pivot index index
                  + scale pivot * (1 - scale pivot) * atomGram atom pivot index ^ 2))
        ≤ atomPivotTrace atom scale pivot
          - atomShiftedDiag atom scale pivot * (1 - scale pivot))
      ∧ ∀ slot, slot ≠ pivot →
          atomPairMinor atom scale pivot slot
            ≤ bulk * atomPivotCross atom scale pivot slot slot
              + ∑ index ∈ Finset.univ.erase pivot,
                  weight index * atomPivotCross atom scale pivot slot index ^ 2

/-- **THE LIGHT-PIVOT RESIDUE IS THE PIVOT PAIR RESIDUE.**  The launch
pad discharges the four extra hypotheses at no cost. -/
theorem atomPivotPairClosed_of_lightPivotWitness
    (hresidue : AtomLightPivotWitnessClosed) : AtomPivotPairClosed := by
  classical
  intro atom scale hpos hsmall hframe
  by_contra hnone
  obtain ⟨pivot, hpivot, hheavy, htrace, htotal, hminor⟩ :=
    exists_light_pivot_launch hframe hpos hsmall
  have hfail : ∀ slotOne slotTwo : Fin 6, slotOne ≠ pivot → slotTwo ≠ pivot → slotOne ≠ slotTwo →
      0 < atomPairMinor atom scale pivot slotOne →
      atomPairMinor atom scale pivot slotOne * atomPairMinor atom scale pivot slotTwo
        ≤ atomPivotCross atom scale pivot slotOne slotTwo ^ 2 := by
    intro slotOne slotTwo hone htwo hne hpair
    by_contra hlt
    exact hnone ⟨pivot, slotOne, slotTwo, Ne.symm hone, Ne.symm htwo, hne, hpivot, hpair,
      lt_of_not_ge hlt⟩
  obtain ⟨weight, bulk, hbudget, hdominate⟩ :=
    hresidue atom scale pivot hpos hsmall hframe hpivot hheavy htrace htotal hminor hfail
  exact false_of_pivot_witness hframe hsmall hpivot bulk weight hbudget
    fun slot hslot => hdominate slot (Finset.mem_erase.mp hslot).1

/-- The polynomial residue of the third rung, from the light-pivot
residue. -/
theorem atomTripleSylvesterClosed_of_lightPivotWitness
    (hresidue : AtomLightPivotWitnessClosed) : AtomTripleSylvesterClosed :=
  atomTripleSylvesterClosed_of_pivotPair (atomPivotPairClosed_of_lightPivotWitness hresidue)

/-- The atom triple ceiling from the light-pivot residue. -/
theorem atomTripleCeilingClosed_of_lightPivotWitness
    (hresidue : AtomLightPivotWitnessClosed) : AtomTripleCeilingClosed :=
  atomTripleCeilingClosed_of_pivotPair (atomPivotPairClosed_of_lightPivotWitness hresidue)

/-- **THE `(6,3)` CELL FROM THE LIGHT-PIVOT RESIDUE.** -/
theorem gtzWeighted_six_three_of_lightPivotWitness
    (hresidue : AtomLightPivotWitnessClosed) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_pivotPair (atomPivotPairClosed_of_lightPivotWitness hresidue)

/-- **ALL OF RANK THREE FROM THE LIGHT-PIVOT RESIDUE.** -/
theorem gtzWeightedAll_three_of_lightPivotWitness
    (hresidue : AtomLightPivotWitnessClosed) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_pivotPair (atomPivotPairClosed_of_lightPivotWitness hresidue)

/-- The crux type is empty under the light-pivot residue. -/
theorem isEmpty_sixThreeCrux_of_lightPivotWitness
    (hresidue : AtomLightPivotWitnessClosed) : IsEmpty SixThreeCrux :=
  isEmpty_sixThreeCrux_of_pivotPair (atomPivotPairClosed_of_lightPivotWitness hresidue)

/-- The rank-five dense branch from the light-pivot residue. -/
theorem rankFiveDenseClosed_of_lightPivotWitness
    (hresidue : AtomLightPivotWitnessClosed) : RankFiveDenseClosed :=
  rankFiveDenseClosed_of_pivotPair (atomPivotPairClosed_of_lightPivotWitness hresidue)

/-- The rank-six dense branch from the light-pivot residue. -/
theorem rankSixDenseClosed_of_lightPivotWitness
    (hresidue : AtomLightPivotWitnessClosed) : RankSixDenseClosed :=
  rankSixDenseClosed_of_pivotPair (atomPivotPairClosed_of_lightPivotWitness hresidue)

/-- The rank-six support-two closure from the light-pivot residue. -/
theorem rankSixSupportTwoClosed_of_lightPivotWitness
    (hresidue : AtomLightPivotWitnessClosed) : RankSixSupportTwoClosed :=
  rankSixSupportTwoClosed_of_pivotPair (atomPivotPairClosed_of_lightPivotWitness hresidue)

/-- The rank-five support-two closure from the light-pivot residue. -/
theorem rankFiveSupportTwoClosed_of_lightPivotWitness
    (hresidue : AtomLightPivotWitnessClosed) : RankFiveSupportTwoClosed :=
  rankFiveSupportTwoClosed_of_pivotPair (atomPivotPairClosed_of_lightPivotWitness hresidue)

/-- The rank-four support-two closure from the light-pivot residue. -/
theorem rankFourSupportTwoClosed_of_lightPivotWitness
    (hresidue : AtomLightPivotWitnessClosed) : RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_pivotPair (atomPivotPairClosed_of_lightPivotWitness hresidue)

end Gtz
