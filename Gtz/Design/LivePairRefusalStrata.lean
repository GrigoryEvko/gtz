import Gtz.Design.UThreeSixDisjunction
import Gtz.Design.TightLineBranchLivePairBridge
import Gtz.Design.PlaneBranchComplementSelector
import Gtz.Design.LineBranchFreePairAdjugateBalance
import Gtz.Design.ResidualLeverageLedger
import Gtz.Quantitative.VolumeAverageLaw
import Gtz.Quantitative.VolumeSelectionFailure
import Gtz.Quantitative.GeneralPositionWindow
import Gtz.Design.LineFreeConicBridge
import Gtz.Quantitative.WindowPolarity
import Gtz.Design.ConservationCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The live-pair tie refusal, split by the free live graph

The residual of the tight-line branch is a refusal: every card-three candidate
carrying two free labels fails to dominate strictly.  This file supplies the
algebra the free-live-graph split needs, and freezes the three-edge stratum as
an explicit quantifier-free system.

## What is new here

**The master identity.**  `det_mul_det_swapAtom` is a two-rank-one-update
determinant law that the tree did not carry:

    det N * det (N - u uᵀ + v vᵀ)
      = det (N - u uᵀ) * det (N + v vᵀ) + (uᵀ adj N v) * (vᵀ adj N u).

Unconditional -- no invertibility and no symmetry.  At a symmetric `N` the two
adjugate readings coincide and the correction is a SQUARE, which is where all
the sign content comes from.

**The four-window necessity.**  With `N` the gap of a triple `{s, o, m}` the
identity reads, at any design,

    pairGapExcessOf s o * det (gap {s,o,m,b})
      = swapAtomPairing^2 - discriminantTie m s o * discriminantTie b s o.

A positive pair minor and a square correction turn a NONPOSITIVE card-four
window determinant into death of the distance-two candidate `{s, o, b}`
whenever the triple `{s, o, m}` has negative gap determinant.  Contrapositive:
**a strictly dominating distance-two candidate can only sit above a card-four
window of strictly positive gap determinant.**  This names no object; it bounds
where a winner can be.

**The window ledger.**  An exact Parseval conservation law for the three
card-four windows over the free triple.  It is an AGGREGATE and inherits every
averaging barrier in the campaign record: it certifies nothing.  It is used
below only for necessary conditions, and for one outright kill -- a design whose
free triple gap is SINGULAR and whose three free pairs are all live has a
card-four window of strictly positive determinant.

## What the retry added

**The assembly.**  The pointwise kills below are assembled into
`exists_posDef_cardThree_iff_tightLineOneSlotFamily_of_windowRefusal`: on the
window-refusal region, at a tight base triple, a strictly dominating card-three
subset exists IF AND ONLY IF some ONE-SLOT swap dominates strictly.  The base
triple is dead because its gap is singular, the nine distance-two candidates and
the complement are dead by the four-window necessity, and nine of the twenty
subsets are all that is left.  This is the opposite of the shape a free-pair
hinge expects -- the surviving candidate keeps TWO base labels -- so no
free-pair statement can help on this region.

**The mirror.**  The same identity read at a VANISHING tie leg gives
`nonneg_det_baseWindow_of_singular_baseGap`: at a tight base triple with one
live base pair, every card-four window over the BASE has nonnegative gap
determinant.  `WindowRefusal` pins the free-side windows nonpositive; one
identity pins the two families to opposite signs.

**The witness.**  `windowRefusalWitnessDesign` is a rational-atom design with
exact Parseval, a weakly dominating base triple whose gap is singular with the
exhibited tight direction `(0,2,1)`, all three free pairs live, the free triple
gap of determinant `-1193/64` and all three card-four windows strictly negative.
It makes `ThreeWindowRefusalSystem` KERNEL-CHECKED and in context -- four
theorems above previously rested on a hypothesis tested only in a chart with
irrational atoms.  Its strict card-three subsets are exactly `{1,2,3}` and
`{1,2,4}`, both one-slot swaps, exactly as the assembly forces.

## Honesty

Nothing here discharges an obligation and nothing here produces a strictly
dominating card-three subset.  The frozen three-edge system is exactly as open
as before; what changed is that its nine distance-two inequalities collapse to
three window inequalities, that the three-window form is provably incompatible
with a singular free triple gap and with a free weight total of one half or
more, and that the three-window region is INHABITED -- so a point of it with no
strict one-slot swap would refute the obligation outright.
-/

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## Part 1 -- the master identity -/

/-- **THE MASTER IDENTITY.**  Two rank-one updates of opposite sign in one
determinant law.  Unconditional; the correction is the product of the two
adjugate readings. -/
theorem det_mul_det_swapAtom (form : Matrix (Fin 3) (Fin 3) ℝ)
    (dropped inserted : Fin 3 → ℝ) :
    form.det * (form - atomMatrix dropped + atomMatrix inserted).det
      = (form - atomMatrix dropped).det * (form + atomMatrix inserted).det
        + (dropped ⬝ᵥ (form.adjugate *ᵥ inserted))
            * (inserted ⬝ᵥ (form.adjugate *ᵥ dropped)) := by
  simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- At a symmetric form the two adjugate readings agree. -/
theorem adjugateReading_comm_of_transpose_eq (form : Matrix (Fin 3) (Fin 3) ℝ)
    (hsymm : form.transpose = form) (leftVec rightVec : Fin 3 → ℝ) :
    leftVec ⬝ᵥ (form.adjugate *ᵥ rightVec) = rightVec ⬝ᵥ (form.adjugate *ᵥ leftVec) := by
  have h10 : form 1 0 = form 0 1 := by
    have := congrFun (congrFun hsymm 0) 1; simpa using this
  have h20 : form 2 0 = form 0 2 := by
    have := congrFun (congrFun hsymm 0) 2; simpa using this
  have h21 : form 2 1 = form 1 2 := by
    have := congrFun (congrFun hsymm 1) 2; simpa using this
  simp only [Matrix.adjugate_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons]
  rw [h10, h20, h21]
  ring

/-- **The master identity at a symmetric form**: the correction is a square. -/
theorem det_mul_det_swapAtom_sq (form : Matrix (Fin 3) (Fin 3) ℝ)
    (hsymm : form.transpose = form) (dropped inserted : Fin 3 → ℝ) :
    form.det * (form - atomMatrix dropped + atomMatrix inserted).det
      = (form - atomMatrix dropped).det * (form + atomMatrix inserted).det
        + (dropped ⬝ᵥ (form.adjugate *ᵥ inserted)) ^ 2 := by
  rw [det_mul_det_swapAtom form dropped inserted,
    adjugateReading_comm_of_transpose_eq form hsymm inserted dropped]
  ring

/-! ## Part 2 -- the identity at a design -/

/-- The adjugate reading coupling the dropped atom to the inserted one across
the gap of a triple: the square correction of the master identity. -/
noncomputable def swapAtomPairing (design : WeightedDesign size 3)
    (pairFirst pairSecond dropped inserted : Fin size) : ℝ :=
  design.atom dropped ⬝ᵥ
    ((subsetSum design {pairFirst, pairSecond, dropped} - 1).adjugate
      *ᵥ design.atom inserted)

theorem tripleSet_rotate_last (first second third : Fin size) :
    ({first, second, third} : Finset (Fin size)) = {third, first, second} := by
  ext label
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **THE FOUR-WINDOW IDENTITY.**  The pair's gap minor times the card-four
window determinant is a square minus the product of the two tie legs.  No
positivity, no branch, no chart: distinctness is the only hypothesis. -/
theorem pairGapExcessOf_mul_det_fourWindow (design : WeightedDesign size 3)
    {pairFirst pairSecond dropped inserted : Fin size}
    (hpair : pairFirst ≠ pairSecond)
    (hfd : pairFirst ≠ dropped) (hsd : pairSecond ≠ dropped)
    (hfi : pairFirst ≠ inserted) (hsi : pairSecond ≠ inserted)
    (hdi : dropped ≠ inserted) :
    pairGapExcessOf design pairFirst pairSecond
        * (subsetSum design (insert inserted {pairFirst, pairSecond, dropped}) - 1).det
      = swapAtomPairing design pairFirst pairSecond dropped inserted ^ 2
        - discriminantTie design dropped pairFirst pairSecond
            * discriminantTie design inserted pairFirst pairSecond := by
  have hnotmem : inserted ∉ ({pairFirst, pairSecond, dropped} : Finset (Fin size)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hfi h.symm, fun h => hsi h.symm, fun h => hdi h.symm⟩
  have hsymm : (subsetSum design {pairFirst, pairSecond, dropped} - 1).transpose
      = subsetSum design {pairFirst, pairSecond, dropped} - 1 :=
    transpose_subsetSum_sub_one design _
  have hdrop : subsetSum design {pairFirst, pairSecond, dropped} - 1
        - atomMatrix (design.atom dropped)
      = subsetSum design {pairFirst, pairSecond} - 1 := by
    rw [subsetSum_triple design hpair hfd hsd, subsetSum_pair design hpair]
    abel
  have hadd : subsetSum design {pairFirst, pairSecond, dropped} - 1
        + atomMatrix (design.atom inserted)
      = subsetSum design (insert inserted {pairFirst, pairSecond, dropped}) - 1 :=
    (subsetSum_insert_sub_one design hnotmem).symm
  have hswap : subsetSum design {pairFirst, pairSecond, dropped} - 1
        - atomMatrix (design.atom dropped) + atomMatrix (design.atom inserted)
      = subsetSum design {pairFirst, pairSecond, inserted} - 1 := by
    rw [hdrop, subsetSum_pair design hpair, subsetSum_triple design hpair hfi hsi]
    abel
  have hmaster := det_mul_det_swapAtom_sq
    (subsetSum design {pairFirst, pairSecond, dropped} - 1) hsymm
    (design.atom dropped) (design.atom inserted)
  rw [hswap, hadd, hdrop] at hmaster
  have hdropDet : (subsetSum design {pairFirst, pairSecond} - 1).det
      = -pairGapExcessOf design pairFirst pairSecond :=
    det_pairGap_eq_neg_pairGapExcessOf design hpair
  have hgapDet : (subsetSum design {pairFirst, pairSecond, dropped} - 1).det
      = discriminantTie design dropped pairFirst pairSecond := by
    rw [tripleSet_rotate_last pairFirst pairSecond dropped]
    exact det_subsetSum_sub_one_eq_discriminantTie design (Ne.symm hfd) (Ne.symm hsd) hpair
  have hswapDet : (subsetSum design {pairFirst, pairSecond, inserted} - 1).det
      = discriminantTie design inserted pairFirst pairSecond := by
    rw [tripleSet_rotate_last pairFirst pairSecond inserted]
    exact det_subsetSum_sub_one_eq_discriminantTie design (Ne.symm hfi) (Ne.symm hsi) hpair
  rw [hdropDet, hgapDet, hswapDet] at hmaster
  simp only [swapAtomPairing]
  linarith [hmaster]

/-! ## Part 3 -- the four-window necessity -/

/-- **THE SCALAR CORE.**  A positive pair minor and a nonpositive card-four
window force the inserted label's tie leg nonpositive, whenever the dropped
label's tie leg is strictly negative. -/
theorem discriminantTie_nonpos_of_det_fourWindow_nonpos (design : WeightedDesign size 3)
    {pairFirst pairSecond dropped inserted : Fin size}
    (hpair : pairFirst ≠ pairSecond)
    (hfd : pairFirst ≠ dropped) (hsd : pairSecond ≠ dropped)
    (hfi : pairFirst ≠ inserted) (hsi : pairSecond ≠ inserted)
    (hdi : dropped ≠ inserted)
    (hminor : 0 < pairGapExcessOf design pairFirst pairSecond)
    (hdropNeg : discriminantTie design dropped pairFirst pairSecond < 0)
    (hwindow :
      (subsetSum design (insert inserted {pairFirst, pairSecond, dropped}) - 1).det ≤ 0) :
    discriminantTie design inserted pairFirst pairSecond ≤ 0 := by
  have hidentity := pairGapExcessOf_mul_det_fourWindow design hpair hfd hsd hfi hsi hdi
  have hleft : pairGapExcessOf design pairFirst pairSecond
      * (subsetSum design (insert inserted {pairFirst, pairSecond, dropped}) - 1).det ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hminor) hwindow
  have hsq : (0:ℝ) ≤ swapAtomPairing design pairFirst pairSecond dropped inserted ^ 2 :=
    sq_nonneg _
  have hprod : 0 ≤ discriminantTie design dropped pairFirst pairSecond
      * discriminantTie design inserted pairFirst pairSecond := by linarith
  exact nonpos_of_mul_nonneg_right hprod hdropNeg

/-- **THE FOUR-WINDOW NECESSITY.**  Under a nonpositive card-four window the
distance-two candidate that swaps the dropped atom for the inserted one is
dead.  Only the pair's minor is needed, not full liveness. -/
theorem not_posDef_swapGap_of_det_fourWindow_nonpos (design : WeightedDesign size 3)
    {pairFirst pairSecond dropped inserted : Fin size}
    (hpair : pairFirst ≠ pairSecond)
    (hfd : pairFirst ≠ dropped) (hsd : pairSecond ≠ dropped)
    (hfi : pairFirst ≠ inserted) (hsi : pairSecond ≠ inserted)
    (hdi : dropped ≠ inserted)
    (hminor : 0 < pairGapExcessOf design pairFirst pairSecond)
    (hdropNeg : discriminantTie design dropped pairFirst pairSecond < 0)
    (hwindow :
      (subsetSum design (insert inserted {pairFirst, pairSecond, dropped}) - 1).det ≤ 0) :
    ¬ (subsetSum design {pairFirst, pairSecond, inserted} - 1).PosDef := by
  intro hposDef
  have hdet : 0 < (subsetSum design {pairFirst, pairSecond, inserted} - 1).det :=
    hposDef.det_pos
  have hrewrite : (subsetSum design {pairFirst, pairSecond, inserted} - 1).det
      = discriminantTie design inserted pairFirst pairSecond := by
    rw [tripleSet_rotate_last pairFirst pairSecond inserted]
    exact det_subsetSum_sub_one_eq_discriminantTie design (Ne.symm hfi) (Ne.symm hsi) hpair
  have hnonpos := discriminantTie_nonpos_of_det_fourWindow_nonpos design hpair hfd hsd
    hfi hsi hdi hminor hdropNeg hwindow
  rw [hrewrite] at hdet
  linarith

/-- Contrapositive: a strictly dominating distance-two candidate forces the
card-four window above it to have strictly positive gap determinant. -/
theorem pos_det_fourWindow_of_posDef_swapGap (design : WeightedDesign size 3)
    {pairFirst pairSecond dropped inserted : Fin size}
    (hpair : pairFirst ≠ pairSecond)
    (hfd : pairFirst ≠ dropped) (hsd : pairSecond ≠ dropped)
    (hfi : pairFirst ≠ inserted) (hsi : pairSecond ≠ inserted)
    (hdi : dropped ≠ inserted)
    (hminor : 0 < pairGapExcessOf design pairFirst pairSecond)
    (hdropNeg : discriminantTie design dropped pairFirst pairSecond < 0)
    (hposDef : (subsetSum design {pairFirst, pairSecond, inserted} - 1).PosDef) :
    0 < (subsetSum design (insert inserted {pairFirst, pairSecond, dropped}) - 1).det := by
  by_contra hle
  exact not_posDef_swapGap_of_det_fourWindow_nonpos design hpair hfd hsd hfi hsi hdi
    hminor hdropNeg (not_lt.mp hle) hposDef

/-! ## Part 4 -- the window ledger -/

/-- Second invariant of a triple's gap in the design's own scalars: the trace of
the adjugate is the sum of the three pair minors. -/
theorem trace_adjugate_tripleGap_eq_sum_pairGapExcessOf (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfs : firstLabel ≠ secondLabel) (hft : firstLabel ≠ thirdLabel)
    (hst : secondLabel ≠ thirdLabel) :
    Matrix.trace ((subsetSum design {firstLabel, secondLabel, thirdLabel} - 1).adjugate)
      = pairGapExcessOf design firstLabel secondLabel
        + pairGapExcessOf design firstLabel thirdLabel
        + pairGapExcessOf design secondLabel thirdLabel := by
  rw [subsetSum_triple design hfs hft hst]
  simp [Matrix.one_fin_three, Matrix.adjugate_fin_three, Matrix.trace_fin_three,
    atomMatrix, Matrix.vecMulVec_apply, pairGapExcessOf, gapExcessOf, gapPairingOf,
    leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-- The gap of the free triple of a `(6,3)` design. -/
noncomputable def freeTripleGap (design : WeightedDesign 6 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  subsetSum design {3, 4, 5} - 1

/-- The determinant of the card-four window obtained by adjoining one atom to
the free triple. -/
noncomputable def freeWindowDet (design : WeightedDesign 6 3) (label : Fin 6) : ℝ :=
  (freeTripleGap design + atomMatrix (design.atom label)).det

/-- At a base label the window determinant is a genuine card-four gap
determinant. -/
theorem freeWindowDet_eq_det_subsetSum (design : WeightedDesign 6 3) {label : Fin 6}
    (hlabel : label ∉ ({3, 4, 5} : Finset (Fin 6))) :
    freeWindowDet design label
      = (subsetSum design (insert label {3, 4, 5}) - 1).det := by
  rw [freeWindowDet, freeTripleGap, subsetSum_insert_sub_one design hlabel]

theorem freeWindowDet_eq_add_reading (design : WeightedDesign 6 3) (label : Fin 6) :
    freeWindowDet design label
      = (freeTripleGap design).det
        + design.atom label ⬝ᵥ ((freeTripleGap design).adjugate *ᵥ design.atom label) := by
  rw [freeWindowDet, det_add_atomMatrix_fin_three]

theorem freeWindowDet_freeLabel (design : WeightedDesign 6 3)
    {freeLabel otherFirst otherSecond : Fin 6}
    (hset : ({3, 4, 5} : Finset (Fin 6)) = {freeLabel, otherFirst, otherSecond})
    (hfo : freeLabel ≠ otherFirst) (hfs : freeLabel ≠ otherSecond)
    (hoo : otherFirst ≠ otherSecond) :
    freeWindowDet design freeLabel
      = 2 * (freeTripleGap design).det + pairGapExcessOf design otherFirst otherSecond := by
  have hsub : freeTripleGap design - atomMatrix (design.atom freeLabel)
      = subsetSum design {otherFirst, otherSecond} - 1 := by
    rw [freeTripleGap, hset, subsetSum_triple design hfo hfs hoo,
      subsetSum_pair design hoo]
    abel
  have hread := det_sub_atomMatrix_fin_three (freeTripleGap design) (design.atom freeLabel)
  rw [hsub, det_pairGap_eq_neg_pairGapExcessOf design hoo] at hread
  rw [freeWindowDet_eq_add_reading]
  linarith [hread]

/-- **THE WINDOW LEDGER.**  An exact Parseval conservation law for the three
card-four windows over the free triple.

It is an AGGREGATE and inherits every averaging barrier in the campaign record:
it certifies nothing and no sign is read off it directly.  It is used below only
to derive necessary conditions on the refusal system -- one kill at a singular
free triple gap, and the free-weight cut below one half. -/
theorem sum_baseWeight_mul_freeWindowDet (design : WeightedDesign 6 3) :
    design.weight 0 * freeWindowDet design 0
        + design.weight 1 * freeWindowDet design 1
        + design.weight 2 * freeWindowDet design 2
      = (freeTripleGap design).det
          * (1 - 2 * (design.weight 3 + design.weight 4 + design.weight 5))
        + pairGapExcessOf design 4 5 * (1 - design.weight 3)
        + pairGapExcessOf design 3 5 * (1 - design.weight 4)
        + pairGapExcessOf design 3 4 * (1 - design.weight 5) := by
  have hlaw := sum_weight_mul_quadForm_eq_trace design (freeTripleGap design).adjugate
  rw [Fin.sum_univ_six] at hlaw
  have htrace : Matrix.trace ((freeTripleGap design).adjugate)
      = pairGapExcessOf design 3 4 + pairGapExcessOf design 3 5
        + pairGapExcessOf design 4 5 := by
    rw [freeTripleGap]
    exact trace_adjugate_tripleGap_eq_sum_pairGapExcessOf design (by decide) (by decide)
      (by decide)
  have hsum : design.weight 0 + design.weight 1 + design.weight 2
      = 1 - (design.weight 3 + design.weight 4 + design.weight 5) := by
    have hone := design.weight_sum_one
    rw [Fin.sum_univ_six] at hone
    linarith
  have h3 := freeWindowDet_freeLabel design (freeLabel := (3 : Fin 6))
    (otherFirst := (4 : Fin 6)) (otherSecond := (5 : Fin 6)) (by decide) (by decide)
    (by decide) (by decide)
  have h4 := freeWindowDet_freeLabel design (freeLabel := (4 : Fin 6))
    (otherFirst := (3 : Fin 6)) (otherSecond := (5 : Fin 6)) (by decide) (by decide)
    (by decide) (by decide)
  have h5 := freeWindowDet_freeLabel design (freeLabel := (5 : Fin 6))
    (otherFirst := (3 : Fin 6)) (otherSecond := (4 : Fin 6)) (by decide) (by decide)
    (by decide) (by decide)
  have key : ∀ label : Fin 6,
      design.atom label ⬝ᵥ ((freeTripleGap design).adjugate *ᵥ design.atom label)
        = freeWindowDet design label - (freeTripleGap design).det := by
    intro label
    rw [freeWindowDet_eq_add_reading]
    ring
  rw [key 0, key 1, key 2, key 3, key 4, key 5, htrace, h3, h4, h5] at hlaw
  linear_combination hlaw + (freeTripleGap design).det * hsum

/-! ## Part 5 -- the three-edge stratum -/

/-- The free live graph of a `(6,3)` design has all three edges. -/
def FreeTripleAllPairsLive (design : WeightedDesign 6 3) : Prop :=
  0 < pairGapExcessOf design 3 4 ∧ 0 < pairGapExcessOf design 3 5
    ∧ 0 < pairGapExcessOf design 4 5

/-- **THE SINGULAR-FREE-TRIPLE KILL.**  If all three free pairs are live and the
free triple gap is singular then some card-four window over the free triple has
strictly positive gap determinant -- so on that locus the three-window refusal
system is EMPTY. -/
theorem exists_pos_freeWindowDet_of_det_freeTripleGap_eq_zero (design : WeightedDesign 6 3)
    (hlive : FreeTripleAllPairsLive design)
    (hzero : (freeTripleGap design).det = 0) :
    0 < freeWindowDet design 0 ∨ 0 < freeWindowDet design 1
      ∨ 0 < freeWindowDet design 2 := by
  obtain ⟨h34, h35, h45⟩ := hlive
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  obtain ⟨hw0, hw1, hw2⟩ := hcon
  have hledger := sum_baseWeight_mul_freeWindowDet design
  rw [hzero] at hledger
  have hone := design.weight_sum_one
  rw [Fin.sum_univ_six] at hone
  have p0 := design.weight_pos 0
  have p1 := design.weight_pos 1
  have p2 := design.weight_pos 2
  have p3 := design.weight_pos 3
  have p4 := design.weight_pos 4
  have p5 := design.weight_pos 5
  have hlt3 : design.weight 3 < 1 := by linarith
  have hlt4 : design.weight 4 < 1 := by linarith
  have hlt5 : design.weight 5 < 1 := by linarith
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt p0) hw0,
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt p1) hw1,
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt p2) hw2,
    mul_pos h45 (by linarith : (0:ℝ) < 1 - design.weight 3),
    mul_pos h35 (by linarith : (0:ℝ) < 1 - design.weight 4),
    mul_pos h34 (by linarith : (0:ℝ) < 1 - design.weight 5)]

/-- **THE THREE-WINDOW REFUSAL SYSTEM.**  All three free pairs live, the free
triple gap of strictly negative determinant, and all three card-four windows of
nonpositive gap determinant.

SATISFIABLE, AND THE WITNESS IS WHAT MAKES THIS SYSTEM WORTH NAMING.  A uniform
census of 24,815 exact line-branch antecedent designs found ZERO inhabitants; a
directed search found them.  At the exhibited witness all three free pair minors
are positive, the free triple gap determinant is negative, all three card-four
windows are strictly negative -- and consequently all NINE distance-two
determinants are nonpositive and the complement is dead, so the only strictly
dominating card-three subsets left are one-slot swaps.  The witness is an exact
rational point of the chart, verified but not kernel-checked.

CONSEQUENCE, and it is the reason to freeze this system: a point of this region
with NO strict one-slot swap would be a design in which every one of the twenty
card-three subsets fails, i.e. a counterexample to the U(3,6) base-triple
obligation.  The system is therefore a sharp counterexample-search target, not
merely a bookkeeping device. -/
def ThreeWindowRefusalSystem (design : WeightedDesign 6 3) : Prop :=
  FreeTripleAllPairsLive design
    ∧ (freeTripleGap design).det < 0
    ∧ freeWindowDet design 0 ≤ 0
    ∧ freeWindowDet design 1 ≤ 0
    ∧ freeWindowDet design 2 ≤ 0

/-- **THE THREE-EDGE REFUSAL SYSTEM, FROZEN.**  Thirteen polynomial signs in the
design's own scalars: three live free pairs, the complement candidate dead, and
the nine distance-two candidates dead.  Every quantifier is discharged. -/
def ThreeEdgeRefusalSystem (design : WeightedDesign 6 3) : Prop :=
  FreeTripleAllPairsLive design
    ∧ (freeTripleGap design).det ≤ 0
    ∧ discriminantTie design 0 3 4 ≤ 0 ∧ discriminantTie design 1 3 4 ≤ 0
    ∧ discriminantTie design 2 3 4 ≤ 0
    ∧ discriminantTie design 0 3 5 ≤ 0 ∧ discriminantTie design 1 3 5 ≤ 0
    ∧ discriminantTie design 2 3 5 ≤ 0
    ∧ discriminantTie design 0 4 5 ≤ 0 ∧ discriminantTie design 1 4 5 ≤ 0
    ∧ discriminantTie design 2 4 5 ≤ 0

/-- On the three-edge stratum the free triple gap determinant is a tie leg of
each of its own pairs. -/
theorem det_freeTripleGap_eq_discriminantTie (design : WeightedDesign 6 3)
    {dropped otherFirst otherSecond : Fin 6}
    (hset : ({3, 4, 5} : Finset (Fin 6)) = {dropped, otherFirst, otherSecond})
    (hdo : dropped ≠ otherFirst) (hds : dropped ≠ otherSecond)
    (hoo : otherFirst ≠ otherSecond) :
    (freeTripleGap design).det = discriminantTie design dropped otherFirst otherSecond := by
  rw [freeTripleGap, hset]
  exact det_subsetSum_sub_one_eq_discriminantTie design hdo hds hoo

/-- **THE WINDOW REFUSAL.**  The liveness-free core: the free triple gap has
strictly negative determinant and all three card-four windows over it have
nonpositive determinant. -/
def WindowRefusal (design : WeightedDesign 6 3) : Prop :=
  (freeTripleGap design).det < 0
    ∧ freeWindowDet design 0 ≤ 0
    ∧ freeWindowDet design 1 ≤ 0
    ∧ freeWindowDet design 2 ≤ 0

theorem windowRefusal_of_threeWindowRefusalSystem (design : WeightedDesign 6 3)
    (hsys : ThreeWindowRefusalSystem design) : WindowRefusal design :=
  ⟨hsys.2.1, hsys.2.2.1, hsys.2.2.2.1, hsys.2.2.2.2⟩

/-- The complement candidate is dead under the window refusal. -/
theorem not_posDef_freeTripleGap_of_windowRefusal (design : WeightedDesign 6 3)
    (hrefusal : WindowRefusal design) :
    ¬ (subsetSum design {3, 4, 5} - 1).PosDef := by
  intro hposDef
  have hpos := hposDef.det_pos
  have hneg := hrefusal.1
  rw [freeTripleGap] at hneg
  linarith

/-- **THE WHOLE TWO-FREE-LABEL FAMILY DIES UNDER THE WINDOW REFUSAL, IN EVERY
STRATUM OF THE FREE LIVE GRAPH.**  A dead free pair kills its own distance-two
candidates outright, by the landed liveness-from-strictness lemma; a live one is
killed by the four-window necessity.  So the free-live-graph split, which the
item's plan treated as three separate strata, needs no split at all: the same
three window inequalities do all nine. -/
theorem not_posDef_distanceTwo_of_windowRefusal (design : WeightedDesign 6 3)
    (hrefusal : WindowRefusal design)
    {pairFirst pairSecond dropped inserted : Fin 6}
    (hset : ({pairFirst, pairSecond, dropped} : Finset (Fin 6)) = {3, 4, 5})
    (hpair : pairFirst ≠ pairSecond) (hfd : pairFirst ≠ dropped)
    (hsd : pairSecond ≠ dropped) (hfi : pairFirst ≠ inserted)
    (hsi : pairSecond ≠ inserted) (hdi : dropped ≠ inserted)
    (hins : inserted ∉ ({3, 4, 5} : Finset (Fin 6)))
    (hwin : freeWindowDet design inserted ≤ 0) :
    ¬ (subsetSum design {pairFirst, pairSecond, inserted} - 1).PosDef := by
  rcases le_or_gt (pairGapExcessOf design pairFirst pairSecond) 0 with hminor | hminor
  · intro hposDef
    rw [tripleSet_rotate_last pairFirst pairSecond inserted] at hposDef
    have hlive := isLivePair_freePair_of_posDef_distanceTwoGap design inserted pairFirst
      pairSecond hpair hfi hsi hposDef
    linarith [hlive.2.2]
  · have hdropNeg : discriminantTie design dropped pairFirst pairSecond < 0 := by
      rw [← det_freeTripleGap_eq_discriminantTie design
        (hset.symm.trans (tripleSet_rotate_last pairFirst pairSecond dropped))
        (Ne.symm hfd) (Ne.symm hsd) hpair]
      exact hrefusal.1
    refine not_posDef_swapGap_of_det_fourWindow_nonpos design hpair hfd hsd hfi hsi hdi
      hminor hdropNeg ?_
    rw [hset, ← freeWindowDet_eq_det_subsetSum design hins]
    exact hwin

/-- **THE COLLAPSE.**  On the three-edge stratum the nine distance-two
inequalities of the frozen system follow from the THREE window inequalities:
twelve conditions become four. -/
theorem threeEdgeRefusalSystem_of_threeWindowRefusalSystem (design : WeightedDesign 6 3)
    (hsys : ThreeWindowRefusalSystem design) : ThreeEdgeRefusalSystem design := by
  obtain ⟨hlive, hdet, hw0, hw1, hw2⟩ := hsys
  obtain ⟨h34, h35, h45⟩ := hlive
  have hset34 : ({3, 4, 5} : Finset (Fin 6)) = {5, 3, 4} := by decide
  have hset35 : ({3, 4, 5} : Finset (Fin 6)) = {4, 3, 5} := by decide
  have hset45 : ({3, 4, 5} : Finset (Fin 6)) = {3, 4, 5} := rfl
  have hd34 : discriminantTie design 5 3 4 < 0 := by
    rw [← det_freeTripleGap_eq_discriminantTie design hset34 (by decide) (by decide)
      (by decide)]
    exact hdet
  have hd35 : discriminantTie design 4 3 5 < 0 := by
    rw [← det_freeTripleGap_eq_discriminantTie design hset35 (by decide) (by decide)
      (by decide)]
    exact hdet
  have hd45 : discriminantTie design 3 4 5 < 0 := by
    rw [← det_freeTripleGap_eq_discriminantTie design hset45 (by decide) (by decide)
      (by decide)]
    exact hdet
  have hwin : ∀ baseLabel : Fin 6, baseLabel ∉ ({3, 4, 5} : Finset (Fin 6)) →
      freeWindowDet design baseLabel ≤ 0 →
      (subsetSum design (insert baseLabel {3, 4, 5}) - 1).det ≤ 0 := by
    intro baseLabel hmem hle
    rwa [freeWindowDet_eq_det_subsetSum design hmem] at hle
  have step : ∀ (pairFirst pairSecond dropped baseLabel : Fin 6),
      pairFirst ≠ pairSecond → pairFirst ≠ dropped → pairSecond ≠ dropped →
      pairFirst ≠ baseLabel → pairSecond ≠ baseLabel → dropped ≠ baseLabel →
      0 < pairGapExcessOf design pairFirst pairSecond →
      discriminantTie design dropped pairFirst pairSecond < 0 →
      ({pairFirst, pairSecond, dropped} : Finset (Fin 6)) = {3, 4, 5} →
      baseLabel ∉ ({3, 4, 5} : Finset (Fin 6)) →
      freeWindowDet design baseLabel ≤ 0 →
      discriminantTie design baseLabel pairFirst pairSecond ≤ 0 := by
    intro pairFirst pairSecond dropped baseLabel hpair hfd hsd hfi hsi hdi hminor
      hdropNeg hsetEq hmem hle
    refine discriminantTie_nonpos_of_det_fourWindow_nonpos design hpair hfd hsd hfi hsi
      hdi hminor hdropNeg ?_
    rw [hsetEq]
    exact hwin baseLabel hmem hle
  refine ⟨⟨h34, h35, h45⟩, le_of_lt hdet, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact step 3 4 5 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h34 hd34 (by decide) (by decide) hw0
  · exact step 3 4 5 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h34 hd34 (by decide) (by decide) hw1
  · exact step 3 4 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h34 hd34 (by decide) (by decide) hw2
  · exact step 3 5 4 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h35 hd35 (by decide) (by decide) hw0
  · exact step 3 5 4 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h35 hd35 (by decide) (by decide) hw1
  · exact step 3 5 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h35 hd35 (by decide) (by decide) hw2
  · exact step 4 5 3 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h45 hd45 (by decide) (by decide) hw0
  · exact step 4 5 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h45 hd45 (by decide) (by decide) hw1
  · exact step 4 5 3 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) h45 hd45 (by decide) (by decide) hw2

/-- **THE QUANTITATIVE CONSTRAINT.**  The three-window refusal system forces the
free weight total strictly below one half.  Derived from the ledger, so it is an
aggregate consequence and certifies nothing; it is a cut on the system. -/
theorem freeWeight_lt_half_of_threeWindowRefusalSystem (design : WeightedDesign 6 3)
    (hsys : ThreeWindowRefusalSystem design) :
    design.weight 3 + design.weight 4 + design.weight 5 < 1 / 2 := by
  obtain ⟨⟨h34, h35, h45⟩, hdet, hw0, hw1, hw2⟩ := hsys
  have hledger := sum_baseWeight_mul_freeWindowDet design
  have hone := design.weight_sum_one
  rw [Fin.sum_univ_six] at hone
  have p0 := design.weight_pos 0
  have p1 := design.weight_pos 1
  have p2 := design.weight_pos 2
  have p3 := design.weight_pos 3
  have p4 := design.weight_pos 4
  have p5 := design.weight_pos 5
  by_contra hge
  push Not at hge
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt p0) hw0,
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt p1) hw1,
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt p2) hw2,
    mul_pos h45 (by linarith : (0:ℝ) < 1 - design.weight 3),
    mul_pos h35 (by linarith : (0:ℝ) < 1 - design.weight 4),
    mul_pos h34 (by linarith : (0:ℝ) < 1 - design.weight 5),
    mul_nonneg (le_of_lt (neg_pos.mpr hdet))
      (by linarith : (0:ℝ) ≤ 2 * (design.weight 3 + design.weight 4 + design.weight 5) - 1)]


/-! ## Part 6 -- the assembly: on the window refusal the obligation IS one-slot

The primary module proves the two-free-label family dead pointwise.  It never
assembles the consequence, which is the whole point of the region:

  **on `WindowRefusal`, at a tight base triple, a strictly dominating card-three
  subset exists if and only if some ONE-SLOT swap dominates strictly.**

The base triple is dead because its gap is singular, the nine distance-two
candidates and the complement are dead by the four-window necessity, and the
nine one-slot swaps are all that is left of the twenty. -/

/-- A one-slot swap of the base triple has card three. -/
theorem card_oneSlotSwap {swapOut swapIn : Fin 6}
    (hout : swapOut ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hin : swapIn ∉ ({0, 1, 2} : Finset (Fin 6))) :
    (insert swapIn ((({0, 1, 2} : Finset (Fin 6))).erase swapOut)).card = 3 := by
  have hnot : swapIn ∉ ((({0, 1, 2} : Finset (Fin 6))).erase swapOut) := fun hmem =>
    hin (Finset.mem_of_mem_erase hmem)
  rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hout]
  decide

/-- The stratum-free kill, phrased against an arbitrary presentation of the
target set so that each of the nine distance-two candidates discharges by
`decide`. -/
theorem not_posDef_distanceTwoTarget_of_windowRefusal (design : WeightedDesign 6 3)
    (hrefusal : WindowRefusal design)
    {pairFirst pairSecond dropped baseLabel : Fin 6} {target : Finset (Fin 6)}
    (hset : ({pairFirst, pairSecond, dropped} : Finset (Fin 6)) = {3, 4, 5})
    (htarget : target = {pairFirst, pairSecond, baseLabel})
    (hpair : pairFirst ≠ pairSecond) (hfd : pairFirst ≠ dropped)
    (hsd : pairSecond ≠ dropped) (hfi : pairFirst ≠ baseLabel)
    (hsi : pairSecond ≠ baseLabel) (hdi : dropped ≠ baseLabel)
    (hins : baseLabel ∉ ({3, 4, 5} : Finset (Fin 6)))
    (hwin : freeWindowDet design baseLabel ≤ 0) :
    ¬ (subsetSum design target - 1).PosDef := by
  rw [htarget]
  exact not_posDef_distanceTwo_of_windowRefusal design hrefusal hset hpair hfd hsd hfi hsi
    hdi hins hwin

/-- **THE ASSEMBLY.**  On the window-refusal region the whole U(3,6) base-triple
obligation collapses to the one-slot family.

This is the exact opposite of the shape a free-pair hinge expects: the surviving
candidate is forced to keep TWO base labels.  Any proof of the branch on this
region must engage the one-slot family, and no free-pair statement can help. -/
theorem exists_posDef_cardThree_iff_tightLineOneSlotFamily_of_windowRefusal
    (design : WeightedDesign 6 3) (hrefusal : WindowRefusal design)
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design {0, 1, 2} tightDir) :
    (∃ selected, selected.card = 3 ∧ (subsetSum design selected - 1).PosDef)
      ↔ TightLineOneSlotFamily design := by
  constructor
  · rintro ⟨selected, hcard, hposDef⟩
    have hmem : selected ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 6)) := by
      simp [Finset.mem_powersetCard, hcard]
    have hbase : ¬ (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
      not_posDef_baseTripleGap_of_tightDirection design htightNe htight
    have hzero : freeWindowDet design 0 ≤ 0 := hrefusal.2.1
    have hone : freeWindowDet design 1 ≤ 0 := hrefusal.2.2.1
    have htwo : freeWindowDet design 2 ≤ 0 := hrefusal.2.2.2
    rcases cardThreeFinsetsOfSix_enumeration selected hmem with
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h
    · exact absurd hposDef hbase
    · exact ⟨2, by decide, 3, by decide, by
        rwa [show insert (3 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 2)
          = ({0, 1, 3} : Finset (Fin 6)) from by decide]⟩
    · exact ⟨2, by decide, 4, by decide, by
        rwa [show insert (4 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 2)
          = ({0, 1, 4} : Finset (Fin 6)) from by decide]⟩
    · exact ⟨2, by decide, 5, by decide, by
        rwa [show insert (5 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 2)
          = ({0, 1, 5} : Finset (Fin 6)) from by decide]⟩
    · exact ⟨1, by decide, 3, by decide, by
        rwa [show insert (3 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 1)
          = ({0, 2, 3} : Finset (Fin 6)) from by decide]⟩
    · exact ⟨1, by decide, 4, by decide, by
        rwa [show insert (4 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 1)
          = ({0, 2, 4} : Finset (Fin 6)) from by decide]⟩
    · exact ⟨1, by decide, 5, by decide, by
        rwa [show insert (5 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 1)
          = ({0, 2, 5} : Finset (Fin 6)) from by decide]⟩
    · exact absurd hposDef (not_posDef_distanceTwoTarget_of_windowRefusal design hrefusal
        (pairFirst := 3) (pairSecond := 4) (dropped := 5) (baseLabel := 0)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hzero)
    · exact absurd hposDef (not_posDef_distanceTwoTarget_of_windowRefusal design hrefusal
        (pairFirst := 3) (pairSecond := 5) (dropped := 4) (baseLabel := 0)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hzero)
    · exact absurd hposDef (not_posDef_distanceTwoTarget_of_windowRefusal design hrefusal
        (pairFirst := 4) (pairSecond := 5) (dropped := 3) (baseLabel := 0)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hzero)
    · exact ⟨0, by decide, 3, by decide, by
        rwa [show insert (3 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 0)
          = ({1, 2, 3} : Finset (Fin 6)) from by decide]⟩
    · exact ⟨0, by decide, 4, by decide, by
        rwa [show insert (4 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 0)
          = ({1, 2, 4} : Finset (Fin 6)) from by decide]⟩
    · exact ⟨0, by decide, 5, by decide, by
        rwa [show insert (5 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 0)
          = ({1, 2, 5} : Finset (Fin 6)) from by decide]⟩
    · exact absurd hposDef (not_posDef_distanceTwoTarget_of_windowRefusal design hrefusal
        (pairFirst := 3) (pairSecond := 4) (dropped := 5) (baseLabel := 1)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hone)
    · exact absurd hposDef (not_posDef_distanceTwoTarget_of_windowRefusal design hrefusal
        (pairFirst := 3) (pairSecond := 5) (dropped := 4) (baseLabel := 1)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hone)
    · exact absurd hposDef (not_posDef_distanceTwoTarget_of_windowRefusal design hrefusal
        (pairFirst := 4) (pairSecond := 5) (dropped := 3) (baseLabel := 1)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hone)
    · exact absurd hposDef (not_posDef_distanceTwoTarget_of_windowRefusal design hrefusal
        (pairFirst := 3) (pairSecond := 4) (dropped := 5) (baseLabel := 2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) htwo)
    · exact absurd hposDef (not_posDef_distanceTwoTarget_of_windowRefusal design hrefusal
        (pairFirst := 3) (pairSecond := 5) (dropped := 4) (baseLabel := 2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) htwo)
    · exact absurd hposDef (not_posDef_distanceTwoTarget_of_windowRefusal design hrefusal
        (pairFirst := 4) (pairSecond := 5) (dropped := 3) (baseLabel := 2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) htwo)
    · exact absurd hposDef (not_posDef_freeTripleGap_of_windowRefusal design hrefusal)
  · rintro ⟨swapOut, hout, swapIn, hin, hposDef⟩
    exact ⟨_, card_oneSlotSwap hout hin, hposDef⟩

/-- The same statement in refusal form: on the window-refusal region, failure of
every card-three candidate is EXACTLY failure of the nine one-slot swaps. -/
theorem not_exists_posDef_cardThree_iff_not_tightLineOneSlotFamily_of_windowRefusal
    (design : WeightedDesign 6 3) (hrefusal : WindowRefusal design)
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design {0, 1, 2} tightDir) :
    (¬ ∃ selected, selected.card = 3 ∧ (subsetSum design selected - 1).PosDef)
      ↔ ¬ TightLineOneSlotFamily design :=
  not_congr (exists_posDef_cardThree_iff_tightLineOneSlotFamily_of_windowRefusal design
    hrefusal htightNe htight)

/-! ## Part 7 -- the mirror: base-side windows are NONNEGATIVE

The four-window identity has a second reading that the primary module does not
take.  When the dropped label's tie leg VANISHES the product term disappears and
the window determinant is a bare square over the pair minor.  A tight base
triple is exactly a vanishing tie leg, so at a tight base triple with one live
base pair every card-four window over the BASE has nonnegative determinant --
the exact opposite of `WindowRefusal`, which pins every card-four window over
the FREE triple nonpositive.  One identity, two opposite signs. -/

/-- A triple's gap determinant read as a tie leg, at any presentation of the
triple. -/
theorem discriminantTie_eq_det_subsetSum_of_set (design : WeightedDesign size 3)
    {pairFirst pairSecond dropped : Fin size} {target : Finset (Fin size)}
    (htarget : ({pairFirst, pairSecond, dropped} : Finset (Fin size)) = target)
    (hpair : pairFirst ≠ pairSecond) (hfd : pairFirst ≠ dropped)
    (hsd : pairSecond ≠ dropped) :
    discriminantTie design dropped pairFirst pairSecond
      = (subsetSum design target - 1).det := by
  rw [← htarget, tripleSet_rotate_last pairFirst pairSecond dropped]
  exact (det_subsetSum_sub_one_eq_discriminantTie design (Ne.symm hfd) (Ne.symm hsd) hpair).symm

/-- **THE SINGULAR SPECIALISATION.**  A vanishing tie leg at the dropped label
collapses the four-window identity to a bare square. -/
theorem pairGapExcessOf_mul_det_fourWindow_of_singular (design : WeightedDesign size 3)
    {pairFirst pairSecond dropped inserted : Fin size}
    (hpair : pairFirst ≠ pairSecond)
    (hfd : pairFirst ≠ dropped) (hsd : pairSecond ≠ dropped)
    (hfi : pairFirst ≠ inserted) (hsi : pairSecond ≠ inserted)
    (hdi : dropped ≠ inserted)
    (hsingular : discriminantTie design dropped pairFirst pairSecond = 0) :
    pairGapExcessOf design pairFirst pairSecond
        * (subsetSum design (insert inserted {pairFirst, pairSecond, dropped}) - 1).det
      = swapAtomPairing design pairFirst pairSecond dropped inserted ^ 2 := by
  rw [pairGapExcessOf_mul_det_fourWindow design hpair hfd hsd hfi hsi hdi, hsingular]
  ring

/-- **THE MIRROR.**  Above a singular triple, a live pair forces the card-four
window determinant NONNEGATIVE. -/
theorem nonneg_det_fourWindow_of_singular_of_pos_pairGapExcessOf
    (design : WeightedDesign size 3)
    {pairFirst pairSecond dropped inserted : Fin size}
    (hpair : pairFirst ≠ pairSecond)
    (hfd : pairFirst ≠ dropped) (hsd : pairSecond ≠ dropped)
    (hfi : pairFirst ≠ inserted) (hsi : pairSecond ≠ inserted)
    (hdi : dropped ≠ inserted)
    (hminor : 0 < pairGapExcessOf design pairFirst pairSecond)
    (hsingular : discriminantTie design dropped pairFirst pairSecond = 0) :
    0 ≤ (subsetSum design (insert inserted {pairFirst, pairSecond, dropped}) - 1).det := by
  have hidentity := pairGapExcessOf_mul_det_fourWindow_of_singular design hpair hfd hsd hfi hsi
    hdi hsingular
  nlinarith [sq_nonneg (swapAtomPairing design pairFirst pairSecond dropped inserted)]

/-- The mirror at a tight base triple of a `(6,3)` design: with the base gap
singular and one base pair live, every card-four window over the base has
nonnegative gap determinant. -/
theorem nonneg_det_baseWindow_of_singular_baseGap (design : WeightedDesign 6 3)
    (hbaseDet : (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1).det = 0)
    {basePairFirst basePairSecond baseDropped freeLabel : Fin 6}
    (hset : ({basePairFirst, basePairSecond, baseDropped} : Finset (Fin 6)) = {0, 1, 2})
    (hpair : basePairFirst ≠ basePairSecond) (hfd : basePairFirst ≠ baseDropped)
    (hsd : basePairSecond ≠ baseDropped) (hfi : basePairFirst ≠ freeLabel)
    (hsi : basePairSecond ≠ freeLabel) (hdi : baseDropped ≠ freeLabel)
    (hminor : 0 < pairGapExcessOf design basePairFirst basePairSecond) :
    0 ≤ (subsetSum design (insert freeLabel {basePairFirst, basePairSecond, baseDropped})
      - 1).det := by
  refine nonneg_det_fourWindow_of_singular_of_pos_pairGapExcessOf design hpair hfd hsd hfi hsi
    hdi hminor ?_
  rw [discriminantTie_eq_det_subsetSum_of_set design hset hpair hfd hsd]
  exact hbaseDet

/-! ## Part 8 -- a kernel-checked witness, inside the line-branch antecedent

The primary module named `ThreeWindowRefusalSystem` and reported its
satisfiability from a chart whose atoms are irrational, so nothing about the
region was kernel-checked and four theorems above rested on an untested
hypothesis.  The design below closes that gap and closes it IN CONTEXT: rational
atoms, exact Parseval, a weakly dominating base triple whose gap is singular
with the exhibited tight direction, all three free pairs live, the free triple
gap of negative determinant and all three card-four windows strictly negative.

It also exhibits the assembly.  Its strict card-three subsets are exactly
`{1,2,3}` and `{1,2,4}`, **both one-slot swaps** -- every distance-two candidate
and the complement are dead, exactly as the region forces.

Verified exactly outside Lean and NOT mechanized here: the design is line-free
(minimum absolute bracket `3/4`, no bracket zero) and off-conic (Veronese
determinant `242757/128` IN THIS TREE'S UNDOUBLED CONVENTION -- the one
`Gtz.veroneseCoords` implements, `(x^2, y^2, z^2, xy, xz, yz)` with no factor
two on the cross terms; the same determinant is `242757/16` in the DOUBLED
convention `(.., 2xy, 2xz, 2yz)`, larger by exactly `2^3 = 8`).  Those two legs
are stated in the report, not proved below. -/

noncomputable def windowRefusalWitnessAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![0, -1, 1]
  | 1 => ![-7, -(1 / 2), 1]
  | 2 => ![0, 1 / 2, 1]
  | 3 => ![-1, -(7 / 2), 1]
  | 4 => ![1 / 2, -(11 / 4), 1]
  | 5 => ![3 / 4, -(1 / 4), 1]

noncomputable def windowRefusalWitnessWeight : Fin 6 → ℝ
  | 0 => 5 / 111
  | 1 => 2 / 111
  | 2 => 26 / 37
  | 3 => 2 / 111
  | 4 => 8 / 111
  | 5 => 16 / 111

/-- The witness: Parseval exact, all six weights strictly positive. -/
noncomputable def windowRefusalWitnessDesign : WeightedDesign 6 3 where
  atom := windowRefusalWitnessAtom
  weight := windowRefusalWitnessWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [windowRefusalWitnessWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [windowRefusalWitnessWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [windowRefusalWitnessAtom, windowRefusalWitnessWeight, atomMatrix,
        Matrix.cons_val_two] <;> norm_num

theorem windowRefusalWitnessDesign_baseTripleGap_form :
    subsetSum windowRefusalWitnessDesign ({0, 1, 2} : Finset (Fin 6)) - 1
      = !![48, 7 / 2, -(7); 7 / 2, 1 / 2, -(1); -(7), -(1), 2] := by
  rw [subsetSum_triple windowRefusalWitnessDesign (by decide) (by decide) (by decide)]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [windowRefusalWitnessDesign, windowRefusalWitnessAtom, atomMatrix,
      Matrix.one_fin_three, Matrix.cons_val_two] <;> norm_num

theorem windowRefusalWitnessDesign_freeTripleGap_form :
    freeTripleGap windowRefusalWitnessDesign
      = !![13 / 16, 31 / 16, 1 / 4; 31 / 16, 151 / 8, -(13 / 2); 1 / 4, -(13 / 2), 2] := by
  rw [freeTripleGap, subsetSum_triple windowRefusalWitnessDesign (by decide) (by decide)
    (by decide)]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [windowRefusalWitnessDesign, windowRefusalWitnessAtom, atomMatrix,
      Matrix.one_fin_three, Matrix.cons_val_two] <;> norm_num

theorem windowRefusalWitnessDesign_det_freeTripleGap :
    (freeTripleGap windowRefusalWitnessDesign).det = -(1193 / 64) := by
  rw [windowRefusalWitnessDesign_freeTripleGap_form, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem windowRefusalWitnessDesign_freeWindow_zero :
    freeWindowDet windowRefusalWitnessDesign 0 = -(4359 / 256) := by
  have hform : freeTripleGap windowRefusalWitnessDesign
      + atomMatrix (windowRefusalWitnessDesign.atom 0)
      = !![13 / 16, 31 / 16, 1 / 4; 31 / 16, 159 / 8, -(15 / 2); 1 / 4, -(15 / 2), 3] := by
    rw [windowRefusalWitnessDesign_freeTripleGap_form]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [windowRefusalWitnessDesign, windowRefusalWitnessAtom, atomMatrix,
        Matrix.cons_val_two] <;> norm_num
  rw [freeWindowDet, hform, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem windowRefusalWitnessDesign_freeWindow_one :
    freeWindowDet windowRefusalWitnessDesign 1 = -(7439 / 256) := by
  have hform : freeTripleGap windowRefusalWitnessDesign
      + atomMatrix (windowRefusalWitnessDesign.atom 1)
      = !![797 / 16, 87 / 16, -(27 / 4); 87 / 16, 153 / 8, -(7); -(27 / 4), -(7), 3] := by
    rw [windowRefusalWitnessDesign_freeTripleGap_form]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [windowRefusalWitnessDesign, windowRefusalWitnessAtom, atomMatrix,
        Matrix.cons_val_two] <;> norm_num
  rw [freeWindowDet, hform, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem windowRefusalWitnessDesign_freeWindow_two :
    freeWindowDet windowRefusalWitnessDesign 2 = -(231 / 256) := by
  have hform : freeTripleGap windowRefusalWitnessDesign
      + atomMatrix (windowRefusalWitnessDesign.atom 2)
      = !![13 / 16, 31 / 16, 1 / 4; 31 / 16, 153 / 8, -(6); 1 / 4, -(6), 3] := by
    rw [windowRefusalWitnessDesign_freeTripleGap_form]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [windowRefusalWitnessDesign, windowRefusalWitnessAtom, atomMatrix,
        Matrix.cons_val_two] <;> norm_num
  rw [freeWindowDet, hform, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- All three free pairs are live: the minors are `1`, `449/64` and `161/256`. -/
theorem windowRefusalWitnessDesign_freeTripleAllPairsLive :
    FreeTripleAllPairsLive windowRefusalWitnessDesign := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [pairGapExcessOf, gapExcessOf, gapPairingOf, leverageOf, dotProduct,
      Fin.sum_univ_three, windowRefusalWitnessDesign, windowRefusalWitnessAtom,
      Matrix.cons_val_two]

/-- **SATISFIABILITY OF THE FROZEN SYSTEM, KERNEL-CHECKED.** -/
theorem windowRefusalWitnessDesign_threeWindowRefusalSystem :
    ThreeWindowRefusalSystem windowRefusalWitnessDesign := by
  refine ⟨windowRefusalWitnessDesign_freeTripleAllPairsLive, ?_, ?_, ?_, ?_⟩
  · rw [windowRefusalWitnessDesign_det_freeTripleGap]; norm_num
  · rw [windowRefusalWitnessDesign_freeWindow_zero]; norm_num
  · rw [windowRefusalWitnessDesign_freeWindow_one]; norm_num
  · rw [windowRefusalWitnessDesign_freeWindow_two]; norm_num

theorem windowRefusalWitnessDesign_windowRefusal :
    WindowRefusal windowRefusalWitnessDesign :=
  windowRefusal_of_threeWindowRefusalSystem windowRefusalWitnessDesign
    windowRefusalWitnessDesign_threeWindowRefusalSystem

/-- **WEAK DOMINATION** at the base triple, from the exact sum of squares
`48 (x + 7y/96 - 7z/48)^2 + (47/192) (y - 2z)^2`. -/
theorem windowRefusalWitnessDesign_dominates_baseTriple :
    Dominates windowRefusalWitnessDesign ({0, 1, 2} : Finset (Fin 6)) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 2} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (windowRefusalWitnessDesign.atom label)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, windowRefusalWitnessDesign_baseTripleGap_form]
    have hform : probeVec ⬝ᵥ
        ((!![48, 7 / 2, -(7); 7 / 2, 1 / 2, -(1); -(7), -(1), 2] : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ probeVec)
        = 48 * (probeVec 0 + 7 / 96 * probeVec 1 - 7 / 48 * probeVec 2) ^ 2
          + 47 / 192 * (probeVec 1 - 2 * probeVec 2) ^ 2 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
      ring
    rw [hform]
    positivity

theorem windowRefusalWitnessDesign_tightDirection_ne_zero :
    (![0, 2, 1] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hentry : (![0, 2, 1] : Fin 3 → ℝ) 1 = 0 := by rw [hzero]; rfl
  norm_num at hentry

/-- The base gap annihilates `(0, 2, 1)`; in particular the design is a TIGHT
LINE antecedent. -/
theorem windowRefusalWitnessDesign_isTightDirection :
    IsTightDirectionOf windowRefusalWitnessDesign ({0, 1, 2} : Finset (Fin 6)) ![0, 2, 1] := by
  show (![0, 2, 1] : Fin 3 → ℝ) ⬝ᵥ
    ((subsetSum windowRefusalWitnessDesign ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ ![0, 2, 1]) = 0
  rw [windowRefusalWitnessDesign_baseTripleGap_form]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem windowRefusalWitnessDesign_baseTripleGap_det :
    (subsetSum windowRefusalWitnessDesign ({0, 1, 2} : Finset (Fin 6)) - 1).det = 0 := by
  rw [windowRefusalWitnessDesign_baseTripleGap_form, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The one-slot swap `{1,2,3}` dominates strictly: trace `251/4`, second
invariant `572`, determinant `373/4`. -/
theorem windowRefusalWitnessDesign_posDef_oneSlot :
    (subsetSum windowRefusalWitnessDesign ({1, 2, 3} : Finset (Fin 6)) - 1).PosDef := by
  have hform : subsetSum windowRefusalWitnessDesign ({1, 2, 3} : Finset (Fin 6)) - 1
      = !![49, 7, -(8); 7, 47 / 4, -(7 / 2); -(8), -(7 / 2), 2] := by
    rw [subsetSum_triple windowRefusalWitnessDesign (by decide) (by decide) (by decide)]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [windowRefusalWitnessDesign, windowRefusalWitnessAtom, atomMatrix,
        Matrix.one_fin_three, Matrix.cons_val_two] <;> norm_num
  have hherm : (subsetSum windowRefusalWitnessDesign ({1, 2, 3} : Finset (Fin 6))
      - 1).IsHermitian :=
    ((Matrix.posSemidef_sum ({1, 2, 3} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (windowRefusalWitnessDesign.atom label)).1).sub
      Matrix.isHermitian_one
  refine posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos hherm ?_ ?_ ?_
  · rw [hform]
    norm_num [Matrix.trace_fin_three, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · rw [hform]
    norm_num [secondInvariantOfThree, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · rw [hform, Matrix.det_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The one-slot family fires here, so the assembly's right side is inhabited. -/
theorem windowRefusalWitnessDesign_tightLineOneSlotFamily :
    TightLineOneSlotFamily windowRefusalWitnessDesign := by
  refine ⟨0, by decide, 3, by decide, ?_⟩
  rw [show insert (3 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 0)
    = ({1, 2, 3} : Finset (Fin 6)) from by decide]
  exact windowRefusalWitnessDesign_posDef_oneSlot

/-- **THE REGION IS INHABITED AND THE ASSEMBLY IS NON-VACUOUS ON BOTH SIDES.**
At the witness the window refusal holds, the base triple is tight, and a
strictly dominating card-three subset exists -- necessarily a one-slot swap. -/
theorem windowRefusalWitnessDesign_exists_posDef_cardThree :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum windowRefusalWitnessDesign selected - 1).PosDef :=
  (exists_posDef_cardThree_iff_tightLineOneSlotFamily_of_windowRefusal
    windowRefusalWitnessDesign windowRefusalWitnessDesign_windowRefusal
    windowRefusalWitnessDesign_tightDirection_ne_zero
    windowRefusalWitnessDesign_isTightDirection).mpr
    windowRefusalWitnessDesign_tightLineOneSlotFamily

end Gtz
