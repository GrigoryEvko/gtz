import Gtz.Wave.SharedPrivateResidualLine
import Gtz.Wave.SharedPrivateCaptureLeak
import Gtz.Wave.SharedPrivateCircuitRankOne
import Gtz.Wave.SharedPrivateCircuitSaturation
import Gtz.Wave.SharedPrivateComplementLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The diagonal kill — a shared-private datum never has a diagonal Gram core

The trace of a shared-private datum is two or three, and the Gram core is
diagonal or it is not.  Three of those four cells are now closed with no
hypothesis.

* The trace-two boundary residue is a theorem, because the residual line
  refuses the interior triple.
* The trace-three deficit residue is a theorem, because the capture leak
  prices the profile mass.
* The refined budget joins the two, thus **THE WHOLE DIAGONAL CELL IS
  EMPTY.**

The one cell that stays open is the extras cell: a datum whose Gram core is
not diagonal.  This module reads the diagonal kill in three ways.

**THE OFF-DIAGONAL WITNESS.**  Every shared-private datum carries a slot
pair whose Gram entry does not vanish.  A datum with no such pair has a
diagonal Gram core, and the diagonal cell is empty.

**THE EQUIVALENCE.**  The extras residue and the generic kill are the same
statement.  The kill gives the residue at once, and the residue gives the
kill because the Gram core of a datum is never diagonal.  Thus closure two
of the three rungs carries ONE residue, not three.

**THE BOUNDARY-FREE DISPATCHES.**  Every landed producer of the extras
residue now produces the generic kill and the three rung closures with no
boundary hypothesis: the circuit residue, the width pair, the fine circuit
lattice, the saturated lattice and the ledger lattice.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.SharedPrivateData.false_of_diagonal_gram` — **THE DIAGONAL KILL.**
* `Gtz.SharedPrivateData.exists_offDiagonal_gram` — **THE OFF-DIAGONAL
  WITNESS** of every datum.
* `Gtz.sharedPrivateExtrasClosed_of_killed`,
  `Gtz.sharedPrivateKilled_iff_extrasClosed` — **THE EQUIVALENCE.**
* `Gtz.sharedPrivateKilled_of_circuitClosed` and the three rung closures.
* `Gtz.sharedPrivateKilled_of_widthPair` and the three rung closures.
* `Gtz.sharedPrivateKilled_of_fineCircuitLattice` and the three rung
  closures.
* `Gtz.sharedPrivateKilled_of_saturatedLattice` and the three rung
  closures.
* `Gtz.sharedPrivateKilled_of_ledgerLattice` and the three rung closures.

## Vacuity

Every statement quantifies over shared-private data, and no datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the diagonal cell is empty -/

set_option maxHeartbeats 1600000 in
/-- **THE DIAGONAL KILL.**  A shared-private datum never has a diagonal
Gram core.  The refined budget splits on the trace: at trace two the
boundary residue forbids an atom of three or more carriers at the
shifted-weight boundary, and at trace three the deficit residue forces the
profile mass past three. -/
theorem SharedPrivateData.false_of_diagonal_gram {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) : False := by
  classical
  refine data.false_of_diagonal_gram_refined hdiag ?_ ?_
  · intro htraceTwo atomIndex hmult
    rcases (capture_diagonal_nonneg_of_isChartStationaryData data.hdata
      atomIndex).lt_or_eq with hpos | heq
    · exact hpos
    · exact absurd heq.symm fun hzero =>
        sharedPrivateBoundaryClosed crux data gramDiag hdiag htraceTwo atomIndex
          hmult hzero
  · intro htraceThree
    by_contra hnot
    exact sharedPrivateDeficitClosed_holds crux data gramDiag hdiag htraceThree
      (by omega)

/-- **THE OFF-DIAGONAL WITNESS.**  Every shared-private datum carries a
slot pair whose Gram entry does not vanish.  A datum with no such pair has
a diagonal Gram core, and the diagonal cell is empty. -/
theorem SharedPrivateData.exists_offDiagonal_gram {crux : SixThreeCrux}
    (data : SharedPrivateData crux) :
    ∃ slotOne slotTwo : Fin data.basisCount,
      slotOne ≠ slotTwo ∧ data.gram slotOne slotTwo ≠ 0 := by
  classical
  by_contra hnone
  simp only [not_exists, not_and, not_not] at hnone
  refine data.false_of_diagonal_gram (gramDiag := fun slot => data.gram slot slot) ?_
  funext rowSlot colSlot
  by_cases hsame : rowSlot = colSlot
  · rw [hsame, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hsame]
    exact hnone rowSlot colSlot hsame

/-! ## Layer 2 — the extras residue IS the generic kill -/

/-- The generic kill gives the extras residue at once. -/
theorem sharedPrivateExtrasClosed_of_killed (hkilled : SharedPrivateKilled) :
    SharedPrivateExtrasClosed := fun crux data _hnotDiag => hkilled crux data

/-- **THE EQUIVALENCE.**  The extras residue and the generic shared-private
kill are the same statement.  Thus closure two of the three rungs carries
ONE residue. -/
theorem sharedPrivateKilled_iff_extrasClosed :
    SharedPrivateKilled ↔ SharedPrivateExtrasClosed :=
  ⟨sharedPrivateExtrasClosed_of_killed, sharedPrivateKilled_of_extras⟩

/-! ## Layer 3 — the circuit residue, with no boundary hypothesis -/

/-- The circuit residue alone closes the generic shared-private kill. -/
theorem sharedPrivateKilled_of_circuitClosed
    (hcircuit : SharedPrivateCircuitClosed) : SharedPrivateKilled :=
  sharedPrivateKilled_of_extras (sharedPrivateExtrasClosed_of_circuit hcircuit)

/-- The circuit residue alone discharges closure two of the rank-four
rung. -/
theorem rankFourSharedPrivateClosed_of_circuitClosed
    (hcircuit : SharedPrivateCircuitClosed) : RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_extras (sharedPrivateExtrasClosed_of_circuit hcircuit)

/-- The circuit residue alone discharges the shared-private closure of the
rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_circuitClosed
    (hcircuit : SharedPrivateCircuitClosed) : RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_extras (sharedPrivateExtrasClosed_of_circuit hcircuit)

/-- The circuit residue alone discharges the shared-private closure of the
rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_circuitClosed
    (hcircuit : SharedPrivateCircuitClosed) : RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_extras (sharedPrivateExtrasClosed_of_circuit hcircuit)

/-! ## Layer 4 — the width pair, with no boundary hypothesis -/

/-- The width pair closes the generic shared-private kill. -/
theorem sharedPrivateKilled_of_widthPair
    (hpair : SharedPrivateCircuitPairClosed)
    (hwide : SharedPrivateCircuitWideClosed) : SharedPrivateKilled :=
  sharedPrivateKilled_of_extras (sharedPrivateExtrasClosed_of_width hpair hwide)

/-- The width pair discharges closure two of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_widthPair
    (hpair : SharedPrivateCircuitPairClosed)
    (hwide : SharedPrivateCircuitWideClosed) : RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_extras (sharedPrivateExtrasClosed_of_width hpair hwide)

/-- The width pair discharges the shared-private closure of the rank-five
rung. -/
theorem rankFiveSharedPrivateClosed_of_widthPair
    (hpair : SharedPrivateCircuitPairClosed)
    (hwide : SharedPrivateCircuitWideClosed) : RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_extras (sharedPrivateExtrasClosed_of_width hpair hwide)

/-- The width pair discharges the shared-private closure of the rank-six
rung. -/
theorem rankSixSharedPrivateClosed_of_widthPair
    (hpair : SharedPrivateCircuitPairClosed)
    (hwide : SharedPrivateCircuitWideClosed) : RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_extras (sharedPrivateExtrasClosed_of_width hpair hwide)

/-! ## Layer 5 — the fine circuit lattice, with no boundary hypothesis -/

/-- The four fine circuit residues close the generic shared-private
kill. -/
theorem sharedPrivateKilled_of_fineCircuitLattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : SharedPrivateKilled :=
  sharedPrivateKilled_of_extras
    (sharedPrivateExtrasClosed_of_circuit_lattice hidentical hwedgeLive hwedgeDead hwide)

/-- The four fine circuit residues discharge closure two of the rank-four
rung. -/
theorem rankFourSharedPrivateClosed_of_fineCircuitLattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_circuit_lattice hidentical hwedgeLive hwedgeDead hwide)

/-- The four fine circuit residues discharge the shared-private closure of
the rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_fineCircuitLattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_circuit_lattice hidentical hwedgeLive hwedgeDead hwide)

/-- The four fine circuit residues discharge the shared-private closure of
the rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_fineCircuitLattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_circuit_lattice hidentical hwedgeLive hwedgeDead hwide)

/-! ## Layer 6 — the saturated lattice, with no boundary hypothesis -/

/-- The saturated lattice closes the generic shared-private kill. -/
theorem sharedPrivateKilled_of_saturatedLattice
    (hidentical : SharedPrivateCircuitPairIdenticalSaturatedClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : SharedPrivateKilled :=
  sharedPrivateKilled_of_extras
    (sharedPrivateExtrasClosed_of_saturated_lattice hidentical hwedgeLive hwedgeDead hwide)

/-- The saturated lattice discharges closure two of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_saturatedLattice
    (hidentical : SharedPrivateCircuitPairIdenticalSaturatedClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_saturated_lattice hidentical hwedgeLive hwedgeDead hwide)

/-- The saturated lattice discharges the shared-private closure of the
rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_saturatedLattice
    (hidentical : SharedPrivateCircuitPairIdenticalSaturatedClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_saturated_lattice hidentical hwedgeLive hwedgeDead hwide)

/-- The saturated lattice discharges the shared-private closure of the
rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_saturatedLattice
    (hidentical : SharedPrivateCircuitPairIdenticalSaturatedClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_saturated_lattice hidentical hwedgeLive hwedgeDead hwide)

/-! ## Layer 7 — the ledger lattice, with no boundary hypothesis -/

/-- The ledger lattice closes the generic shared-private kill. -/
theorem sharedPrivateKilled_of_ledgerLattice
    (hidentical : SharedPrivateCircuitPairIdenticalLedgerClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : SharedPrivateKilled :=
  sharedPrivateKilled_of_extras
    (sharedPrivateExtrasClosed_of_ledger_lattice hidentical hwedgeLive hwedgeDead hwide)

/-- The ledger lattice discharges closure two of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_ledgerLattice
    (hidentical : SharedPrivateCircuitPairIdenticalLedgerClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_ledger_lattice hidentical hwedgeLive hwedgeDead hwide)

/-- The ledger lattice discharges the shared-private closure of the
rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_ledgerLattice
    (hidentical : SharedPrivateCircuitPairIdenticalLedgerClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_ledger_lattice hidentical hwedgeLive hwedgeDead hwide)

/-- The ledger lattice discharges the shared-private closure of the
rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_ledgerLattice
    (hidentical : SharedPrivateCircuitPairIdenticalLedgerClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) : RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_extras
    (sharedPrivateExtrasClosed_of_ledger_lattice hidentical hwedgeLive hwedgeDead hwide)

end Gtz
