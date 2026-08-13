import Gtz.Wave.OuterCofactorSpanForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The outer residue collapse — the four residues are two kills

The outer cofactor reduction names two residues per rank: the extras
cap and the det-zero stratum kill.  This file shows that the residue
pair collapses.  The balance prices the determinant as the weighted sum
of the extras caps, because the basis caps vanish.  Thus the capped
inequality, multiplied by the determinant and summed, squares the
determinant against zero.  The extras residue is therefore EQUIVALENT
to the det-vanishing law, and the residue pair is EQUIVALENT to the
direct kill of the reified outer datum.  Any direct kill discharges
the four residues at once.

The label-level scan of this session supplies the target of that kill.
The extras-free honest system is infeasible at every rank, the leak and
capture rows are droppable, and the commutation rows are essential.
Thus the direct kill is a commutation argument on the diagonal-Gram
frame, and the extras fold in through the parallel-or-circuit
trichotomy.  This file also reifies the rank-six outer datum, so the
three ranks consume one kill interface.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.RankFourOuterData.det_eq_zero_of_extrasCapped` — the extras cap
  forces the determinant to zero at every rank-four outer datum.
* `Gtz.rankFourOuterExtrasCapped_iff_detVanishes` — **THE RANK-FOUR
  COLLAPSE.**
* `Gtz.rankFourOuterKilled_iff_residues` — **THE RANK-FOUR KILL
  LATTICE.**
* `Gtz.rankFourSupportTwoClosed_of_outer_killed` — the direct rank-four
  bridge.
* `Gtz.RankFiveOuterData.det_eq_zero_of_extrasCapped`,
  `Gtz.rankFiveOuterExtrasCapped_iff_detVanishes`,
  `Gtz.rankFiveOuterKilled_iff_residues`,
  `Gtz.rankFiveSupportTwoClosed_of_outer_killed` — the rank-five
  mirrors.
* `Gtz.rankSixSupportTwoClosed_of_outer_killed` — the direct rank-six
  bridge over the reified `RankSixOuterData`.

## Vacuity

The statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no crux
exists, thus no frame exists.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the rank-four collapse -/

/-- **THE RANK-FOUR DIRECT KILL.**  No rank-four outer datum exists. -/
def RankFourOuterKilled : Prop :=
  ∀ (crux : SixThreeCrux), RankFourOuterData crux → False

/-- **THE RANK-FOUR DET LAW.**  Every rank-four outer datum sits on the
det-zero stratum. -/
def RankFourOuterDetVanishes : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux),
    data.squareMatrix.det = 0

/-- The extras cap forces the determinant to zero at every rank-four
outer datum: the basis caps vanish, and the capped extras collapse the
balance. -/
theorem RankFourOuterData.det_eq_zero_of_extrasCapped
    (hextras : RankFourOuterExtrasCapped)
    {crux : SixThreeCrux} (data : RankFourOuterData crux) :
    data.squareMatrix.det = 0 := by
  classical
  apply det_eq_zero_of_capped_certificate data.frame.hdata data.squareMatrix
    (fun atomIndex => data.squareMatrix_ones atomIndex)
  intro label hmem hpos
  by_cases hbasis : ∃ colIndex : Fin 4, label = data.frame.basisLabel colIndex
  · obtain ⟨colIndex, rfl⟩ := hbasis
    have hzero := data.dualRow_annihilates_basis colIndex
    show (∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2)
      * data.squareMatrix.det ≤ 0
    rw [hzero, zero_mul]
  · push Not at hbasis
    exact hextras crux data label hmem hpos hbasis

/-- **THE RANK-FOUR COLLAPSE.**  The extras residue is equivalent to
the det-vanishing law.  The forward direction squares the determinant
through the balance.  The backward direction caps with zero. -/
theorem rankFourOuterExtrasCapped_iff_detVanishes :
    RankFourOuterExtrasCapped ↔ RankFourOuterDetVanishes := by
  constructor
  · intro hextras crux data
    exact data.det_eq_zero_of_extrasCapped hextras
  · intro hdet crux data label _ _ _
    rw [hdet crux data, mul_zero]

/-- **THE RANK-FOUR KILL LATTICE.**  The residue pair is equivalent to
the direct kill.  Thus one kill discharges the two rank-four residues
at once. -/
theorem rankFourOuterKilled_iff_residues :
    RankFourOuterKilled
      ↔ (RankFourOuterExtrasCapped ∧ RankFourOuterStratumKilled) := by
  constructor
  · intro hkill
    exact ⟨fun crux data _ _ _ _ => (hkill crux data).elim,
      fun crux data _ => hkill crux data⟩
  · intro hpair crux data
    exact RankFourOuterData.killed_of_residues hpair.1 hpair.2 data

/-- The direct kill also factors through the det law: the det law and
the stratum kill together kill every rank-four outer datum. -/
theorem rankFourOuterKilled_of_detVanishes
    (hdet : RankFourOuterDetVanishes)
    (hstratum : RankFourOuterStratumKilled) : RankFourOuterKilled :=
  fun crux data => hstratum crux data (hdet crux data)

/-- **THE DIRECT RANK-FOUR BRIDGE.**  The direct kill closes the
rank-four support-two closure. -/
theorem rankFourSupportTwoClosed_of_outer_killed
    (hkill : RankFourOuterKilled) : RankFourSupportTwoClosed := by
  refine rankFourSupportTwoClosed_of_outer_shared_kill ?_
  intro crux frame columnIndex otherIndex atomU atomV atomT hcard hUV hneU
    hneV hsupp hneCol hTU hTV hneT
  exact hkill crux ⟨frame, columnIndex, otherIndex, atomU, atomV, atomT,
    hcard, hUV, hneU, hneV, hsupp, hneCol, hTU, hTV, hneT⟩

/-! ## Layer 2 — the rank-five collapse -/

/-- **THE RANK-FIVE DIRECT KILL.**  No rank-five outer datum exists. -/
def RankFiveOuterKilled : Prop :=
  ∀ (crux : SixThreeCrux), RankFiveOuterData crux → False

/-- **THE RANK-FIVE DET LAW.**  Every rank-five outer datum sits on the
det-zero stratum. -/
def RankFiveOuterDetVanishes : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFiveOuterData crux),
    data.squareMatrix.det = 0

/-- The extras cap forces the determinant to zero at every rank-five
outer datum. -/
theorem RankFiveOuterData.det_eq_zero_of_extrasCapped
    (hextras : RankFiveOuterExtrasCapped)
    {crux : SixThreeCrux} (data : RankFiveOuterData crux) :
    data.squareMatrix.det = 0 := by
  classical
  apply det_eq_zero_of_capped_certificate data.frame.hdata data.squareMatrix
    (fun atomIndex => data.squareMatrix_ones atomIndex)
  intro label hmem hpos
  by_cases hbasis : ∃ colIndex : Fin 5, label = data.frame.basisLabel colIndex
  · obtain ⟨colIndex, rfl⟩ := hbasis
    have hzero := data.dualRow_annihilates_basis colIndex
    show (∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex ^ 2)
      * data.squareMatrix.det ≤ 0
    rw [hzero, zero_mul]
  · push Not at hbasis
    exact hextras crux data label hmem hpos hbasis

/-- **THE RANK-FIVE COLLAPSE.**  The extras residue is equivalent to
the det-vanishing law. -/
theorem rankFiveOuterExtrasCapped_iff_detVanishes :
    RankFiveOuterExtrasCapped ↔ RankFiveOuterDetVanishes := by
  constructor
  · intro hextras crux data
    exact data.det_eq_zero_of_extrasCapped hextras
  · intro hdet crux data label _ _ _
    rw [hdet crux data, mul_zero]

/-- **THE RANK-FIVE KILL LATTICE.**  The residue pair is equivalent to
the direct kill. -/
theorem rankFiveOuterKilled_iff_residues :
    RankFiveOuterKilled
      ↔ (RankFiveOuterExtrasCapped ∧ RankFiveOuterStratumKilled) := by
  constructor
  · intro hkill
    exact ⟨fun crux data _ _ _ _ => (hkill crux data).elim,
      fun crux data _ => hkill crux data⟩
  · intro hpair crux data
    exact RankFiveOuterData.killed_of_residues hpair.1 hpair.2 data

/-- The det law and the stratum kill together kill every rank-five
outer datum. -/
theorem rankFiveOuterKilled_of_detVanishes
    (hdet : RankFiveOuterDetVanishes)
    (hstratum : RankFiveOuterStratumKilled) : RankFiveOuterKilled :=
  fun crux data => hstratum crux data (hdet crux data)

/-- **THE DIRECT RANK-FIVE BRIDGE.**  The direct kill closes the
rank-five support-two closure. -/
theorem rankFiveSupportTwoClosed_of_outer_killed
    (hkill : RankFiveOuterKilled) : RankFiveSupportTwoClosed := by
  refine rankFiveSupportTwoClosed_of_outer_shared_kill ?_
  intro crux frame columnIndex otherIndex atomU atomV atomT hcard hUV hneU
    hneV hsupp hneCol hTU hTV hneT
  exact hkill crux ⟨frame, columnIndex, otherIndex, atomU, atomV, atomT,
    hcard, hUV, hneU, hneV, hsupp, hneCol, hTU, hTV, hneT⟩

/-! ## Layer 3 — the rank-six outer datum -/

/-- **THE RANK-SIX OUTER DATUM.**  The reified killOuter tuple of the
rank-six bridge.  The diagonal certificate dies at rank six, thus no
cofactor reduction exists here.  The direct kill is the one exit, and
this structure gives the three ranks one kill interface. -/
structure RankSixOuterData (crux : SixThreeCrux) where
  /-- The rank-six frame. -/
  frame : RankSixFrame crux
  /-- The pair column index. -/
  columnIndex : Fin 6
  /-- The outer sharer index. -/
  otherIndex : Fin 6
  /-- The left pair atom. -/
  atomU : Fin 6
  /-- The right pair atom. -/
  atomV : Fin 6
  /-- The outside sharer atom. -/
  atomT : Fin 6
  /-- The pair column has support two. -/
  hcard : (datumTightSupport frame.tightDir
    (frame.basisLabel columnIndex)).card = 2
  /-- The pair atoms are distinct. -/
  hUV : atomU ≠ atomV
  /-- The pair column is alive at the left atom. -/
  hneU : frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0
  /-- The pair column is alive at the right atom. -/
  hneV : frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0
  /-- The pair column vanishes off the pair. -/
  hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
    frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0
  /-- The sharer is a different column. -/
  hneCol : otherIndex ≠ columnIndex
  /-- The sharer atom is not the left pair atom. -/
  hTU : atomT ≠ atomU
  /-- The sharer atom is not the right pair atom. -/
  hTV : atomT ≠ atomV
  /-- The sharer is alive outside the pair. -/
  hneT : frame.tightDir (frame.basisLabel otherIndex) atomT ≠ 0

/-- **THE RANK-SIX DIRECT KILL.**  No rank-six outer datum exists. -/
def RankSixOuterKilled : Prop :=
  ∀ (crux : SixThreeCrux), RankSixOuterData crux → False

/-- **THE DIRECT RANK-SIX BRIDGE.**  The direct kill closes the
rank-six support-two closure. -/
theorem rankSixSupportTwoClosed_of_outer_killed
    (hkill : RankSixOuterKilled) : RankSixSupportTwoClosed := by
  refine rankSixSupportTwoClosed_of_outer_shared_kill ?_
  intro crux frame columnIndex otherIndex atomU atomV atomT hcard hUV hneU
    hneV hsupp hneCol hTU hTV hneT
  exact hkill crux ⟨frame, columnIndex, otherIndex, atomU, atomV, atomT,
    hcard, hUV, hneU, hneV, hsupp, hneCol, hTU, hTV, hneT⟩

end Gtz
