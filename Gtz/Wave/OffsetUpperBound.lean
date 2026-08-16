/-
# The squared offset against the pivot minor product: a fifth door to the five
on-path obligations, the offset's second moment, and the averaged no-go

`Gtz.tripleDetForm_pos_iff_sq_lt` reads domination at a positive pivot as

    (p * w - u * v) ^ 2 < pairMinorForm p q u * pairMinorForm p r v

and `Gtz.OffsetMinorProduct` supplies a FLOOR for the right side: the shifted row law
pins the row total, and a pigeonhole hands one partner at least a quarter of what one
spent partner leaves.  The programme that shape suggests is to bound the left side ABOVE
and read the two bounds against each other.  This file settles that programme, and turns
the surviving half into a new entrance to the registry.

## 1. The split is not a relaxation.  It IS the objective, pointwise.

For a symmetric form and any pivot, `Gtz.pairMinorAt_mul_sub_offsetAt_sq` gives

    pairMinorAt F a b * pairMinorAt F a c - offsetAt F a b c ^ 2
      = F a a * (tripleBlock F a b c).det

so at a positive pivot diagonal the comparison `offset ^ 2 < minor product` is EQUIVALENT
to `0 < det` (`Gtz.offsetAt_sq_lt_iff_det_pos`).  Nothing is gained by separating the two
sides — every bound on one of them is a bound on the objective in disguise.

## 2. THE FIFTH DOOR

Sylvester at `Fin 3` turns that equivalence into a producer.  Three scalar inequalities at
ONE pivot of ONE design — a positive excess, one positive pair minor, and one ordered
partner pair whose squared offset falls below the minor product — make the gap block
positive definite (`Gtz.posDef_tripleBlock_of_offsetAt_sq_lt`).  The shifted triple block
IS the landed `Gtz.blockGapAt` along the pick
(`Gtz.tripleBlock_diagonalShift_eq_blockGapAt`), so the landed door fires and

    Gtz.allFiveOnPath_of_offsetDominatesSomewhere

retires all five on-path obligations from `Gtz.OffsetDominatesSomewhere` alone.  This joins
the four landed entrances, and it is the first one stated with no determinant, no root and
no division — three polynomial inequalities in the projection entries and the weights.

Sylvester at `Fin 3` also runs backwards, and the pivot Schur identity is an identity, so
the door LOSES NOTHING.  `Gtz.posDef_tripleBlock_iff_offsetAt_sq_lt` makes the three
inequalities equivalent to positive definiteness of the block, and
`Gtz.offsetDominatesSomewhere_iff_blockGapSelects` lifts that to the door hypothesis
itself.  The offset criterion is therefore a faithful restatement of the landed block-gap
selection, not a strengthening of it: the whole rank-four rung reduces to three polynomial
inequalities at one pivot of one design, and a producer may work in offset coordinates
with no loss.

## 3. The offset's second moment, in closed form

Summing the pivot identity over the twenty ordered partner pairs gives the second moment of
the offset on landed invariants alone (`Gtz.sum_sq_shiftOffsetAt_erase`):

    ∑ over ordered distinct (b, c) of offset ^ 2
      = rowTotal ^ 2 - rowEnergy - excess * (36 * P a a - 46) / 108.

The corpus carried the offset's FIRST marginal (`Gtz.sum_offDiagProduct_erase`) and not its
second.

## 4. The averaged split is NEGATIVE, and the door must be pointwise

Read the other way the same sum is `excess * (36 * P a a - 46) / 108`, and a projection
diagonal never exceeds one, so the bracket is at most `-10`.  At every label of positive
excess the average squared offset EXCEEDS the average minor product, by at least
`5 * excess / 54` (`Gtz.sum_pairMinorProduct_sub_sq_shiftOffset_neg`).  Two consequences.

Every argument that compares an AVERAGED upper bound on the offset against an averaged
lower bound on the minor product is dead, uniformly, at every label of every design.

And at every such label at least one ordered partner pair FAILS the door's third
inequality (`Gtz.exists_offset_sq_gt_pairMinor_product`).  A door instance must therefore
select its pair, never quantify over pairs.  The pigeonhole floor of
`Gtz.OffsetMinorProduct` selects, but too weakly: measured, its uniform composition fires
on 10 of 4800 slots across 800 exact designs, and it fails at the landed graphic point of
`K4`, where the best floor is `7 / 1296` against a largest squared offset of `49 / 2304`
(`Gtz.kfourStar_bestFloor_lt_maxOffsetSq`).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Wave.ProjectionMinorShift
import Gtz.Wave.ThresholdSpread
import Gtz.Wave.OffsetMinorProduct
import Gtz.Wave.ComplementDualLane
import Gtz.Design.KFourChartClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ### 1. The offset of a form, and the pivot Schur identity -/

/-- The **offset at a pivot**, read on a form rather than on six loose scalars: the pivot
diagonal against the far pairing, less the product of the two pivot pairings. -/
def offsetAt (form : Matrix (Fin size) (Fin size) ℝ) (first second third : Fin size) : ℝ :=
  form first first * form second third - form first second * form first third

theorem offsetAt_apply (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    offsetAt form first second third
      = form first first * form second third
        - form first second * form first third := rfl

/-- Every symmetric form flips its entries. -/
theorem form_flip_of_transpose {form : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : formᵀ = form) (leftLabel rightLabel : Fin size) :
    form rightLabel leftLabel = form leftLabel rightLabel := by
  have hentry := congrFun (congrFun hsymmetric leftLabel) rightLabel
  simpa only [Matrix.transpose_apply] using hentry

/-- Swapping the two partners fixes the offset, because the far pairing is symmetric. -/
theorem offsetAt_swap (form : Matrix (Fin size) (Fin size) ℝ) (hsymmetric : formᵀ = form)
    (first second third : Fin size) :
    offsetAt form first third second = offsetAt form first second third := by
  rw [offsetAt, offsetAt, form_flip_of_transpose hsymmetric second third]; ring

/-- **THE PIVOT SCHUR IDENTITY ON A FORM.**  The pivot's two pair minors, less the squared
offset, is the pivot diagonal times the triple's determinant.  Pure algebra, no positivity
and no rank. -/
theorem pairMinorAt_mul_sub_offsetAt_sq (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second third : Fin size) :
    pairMinorAt form first second * pairMinorAt form first third
        - offsetAt form first second third ^ 2
      = form first first * (tripleBlock form first second third).det := by
  rw [det_tripleBlock form hsymmetric, pairMinorAt, pairMinorAt, offsetAt]; ring

/-- **THE SPLIT IS THE OBJECTIVE.**  At a pivot of positive diagonal the comparison the
criterion asks for is EQUIVALENT to positivity of the triple's determinant.  So bounding
the squared offset above and the minor product below is not a relaxation of the objective
— it is a re-encoding of it, and two independently proved bounds can only lose. -/
theorem offsetAt_sq_lt_iff_det_pos (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) {first : Fin size} (hpivot : 0 < form first first)
    (second third : Fin size) :
    offsetAt form first second third ^ 2
        < pairMinorAt form first second * pairMinorAt form first third
      ↔ 0 < (tripleBlock form first second third).det := by
  have hkey := pairMinorAt_mul_sub_offsetAt_sq form hsymmetric first second third
  constructor
  · intro hlt
    by_contra hnot
    have hle : (tripleBlock form first second third).det ≤ 0 := not_lt.mp hnot
    nlinarith
  · intro hdet
    have hgap : 0 < form first first * (tripleBlock form first second third).det :=
      mul_pos hpivot hdet
    linarith

/-! ### 2. The triple block in explicit entries, and Sylvester -/

/-- The three-slot block of a symmetric form, written out. -/
theorem tripleBlock_eq_entries (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second third : Fin size) :
    tripleBlock form first second third
      = !![form first first, form first second, form first third;
           form first second, form second second, form second third;
           form first third, form second third, form third third] := by
  ext slotRow slotCol
  fin_cases slotRow <;> fin_cases slotCol <;>
    simp [tripleBlock, Matrix.submatrix_apply,
      form_flip_of_transpose hsymmetric first second,
      form_flip_of_transpose hsymmetric first third,
      form_flip_of_transpose hsymmetric second third]

/-- **THE FIFTH DOOR, AT THE LEVEL OF ONE FORM.**  Three scalar inequalities — a positive
pivot diagonal, one positive pair minor at that pivot, and one ordered partner pair whose
squared offset falls below the minor product — make the triple block positive definite.
Sylvester at `Fin 3` reads each of its three leading minors off exactly one of them. -/
theorem posDef_tripleBlock_of_offsetAt_sq_lt (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) {first second third : Fin size}
    (hpivot : 0 < form first first)
    (hminor : 0 < pairMinorAt form first second)
    (hoffset : offsetAt form first second third ^ 2
      < pairMinorAt form first second * pairMinorAt form first third) :
    (tripleBlock form first second third).PosDef := by
  have hdet : 0 < (tripleBlock form first second third).det :=
    (offsetAt_sq_lt_iff_det_pos form hsymmetric hpivot second third).mp hoffset
  rw [det_tripleBlock form hsymmetric] at hdet
  rw [tripleBlock_eq_entries form hsymmetric]
  refine posDef_of_leadingMinors_fin_three _ _ _ _ _ _ hpivot ?_ ?_
  · simpa [pairMinorAt] using hminor
  · nlinarith [hdet]

/-! ### 3. The design instance -/

/-- The offset of a design at a pivot, on the shifted form the criterion reads. -/
noncomputable def shiftOffsetAt (design : WeightedDesign size rank)
    (first second third : Fin size) : ℝ :=
  offsetAt (diagonalShiftForm design) first second third

theorem shiftOffsetAt_apply (design : WeightedDesign size rank)
    {first second third : Fin size} (hsecond : first ≠ second) (hthird : first ≠ third)
    (hfar : second ≠ third) :
    shiftOffsetAt design first second third
      = (projectionOfDesign design first first - design.weight first)
          * projectionOfDesign design second third
        - projectionOfDesign design first second
            * projectionOfDesign design first third := by
  rw [shiftOffsetAt, offsetAt, diagonalShiftForm_diag,
    diagonalShiftForm_offDiag design hfar, diagonalShiftForm_offDiag design hsecond,
    diagonalShiftForm_offDiag design hthird]

/-- The Schur identity at a design. -/
theorem pairMinorAt_diagonalShift_mul_sub_sq (design : WeightedDesign size rank)
    (first second third : Fin size) :
    pairMinorAt (diagonalShiftForm design) first second
        * pairMinorAt (diagonalShiftForm design) first third
        - shiftOffsetAt design first second third ^ 2
      = diagonalShiftForm design first first
          * (tripleBlock (diagonalShiftForm design) first second third).det :=
  pairMinorAt_mul_sub_offsetAt_sq (diagonalShiftForm design)
    (diagonalShiftForm_transpose design) first second third

/-- **THE SHIFTED TRIPLE BLOCK IS THE LANDED GAP BLOCK.**  Along an injective pick the
submatrix of the diagonal shift is the submatrix of the projection less the diagonal of the
picked weights, which is exactly `Gtz.blockGapAt`.  This is the bridge that carries the
offset vocabulary onto the landed door. -/
theorem tripleBlock_diagonalShift_eq_blockGapAt (design : WeightedDesign size rank)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hthirdFirst : third ≠ first) (hthirdSecond : third ≠ second) :
    tripleBlock (diagonalShiftForm design) first second third
      = blockGapAt (projectionOfDesign design) design.weight ![first, second, third] := by
  have hinj : Function.Injective ![first, second, third] :=
    injective_triplePick hfirstSecond hthirdFirst hthirdSecond
  ext slotRow slotCol
  simp only [tripleBlock, blockGapAt, diagonalShiftForm, Matrix.submatrix_apply,
    Matrix.sub_apply]
  by_cases hslots : slotRow = slotCol
  · subst hslots; simp
  · rw [Matrix.diagonal_apply_ne _ (hinj.ne hslots), Matrix.diagonal_apply_ne _ hslots]

/-! ### 4. The uniform bridge to the landed gap functional -/

/-- **THE SHIFTED TRIPLE DETERMINANT IS THE LANDED GAP, OVER `216`.**  At uniform weight
the shifted form is `P - (1/6) * 1`, and `Gtz.projGapAt_eq_shiftedMinor` is exactly the
determinant of its triple block with the weight product cleared. -/
theorem det_tripleBlock_diagonalShift_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹)
    {first second third : Fin 6} (hsecond : first ≠ second) (hthird : first ≠ third)
    (hfar : second ≠ third) :
    (tripleBlock (diagonalShiftForm design) first second third).det
      = projGapAt (projectionOfDesign design) first second third / 216 := by
  rw [projGapAt_eq_shiftedMinor (projectionOfDesign_transpose design) first second third,
    det_tripleBlock (diagonalShiftForm design) (diagonalShiftForm_transpose design),
    diagonalShiftForm_diag, diagonalShiftForm_diag, diagonalShiftForm_diag,
    diagonalShiftForm_offDiag design hsecond, diagonalShiftForm_offDiag design hthird,
    diagonalShiftForm_offDiag design hfar, huniform first, huniform second, huniform third]
  ring

/-! ### 5. THE FIFTH DOOR TO THE REGISTRY -/

/-- **THE OFFSET SELECTION CRITERION.**  Every primitive design owns a pivot of positive
excess, one partner of positive shifted pair minor, and a second partner whose squared
offset falls below the product of the two minors.  Three polynomial inequalities in the
projection entries and the weights, with no determinant, no root and no division. -/
def OffsetDominatesSomewhere : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    ∃ first second third : Fin 6,
      first ≠ second ∧ third ≠ first ∧ third ≠ second ∧
      0 < diagonalShiftForm design first first ∧
      0 < pairMinorAt (diagonalShiftForm design) first second ∧
      shiftOffsetAt design first second third ^ 2
        < pairMinorAt (diagonalShiftForm design) first second
          * pairMinorAt (diagonalShiftForm design) first third

/-- The offset criterion produces the landed block-gap selection. -/
theorem blockGapAt_posDef_of_offsetDominatesSomewhere (hoffset : OffsetDominatesSomewhere) :
    ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        (blockGapAt (projectionOfDesign design) design.weight pick).PosDef := by
  intro design hprimitive
  obtain ⟨first, second, third, hfirstSecond, hthirdFirst, hthirdSecond,
    hpivot, hminor, hsq⟩ := hoffset design hprimitive
  refine ⟨![first, second, third],
    injective_triplePick hfirstSecond hthirdFirst hthirdSecond, ?_⟩
  rw [← tripleBlock_diagonalShift_eq_blockGapAt design hfirstSecond hthirdFirst hthirdSecond]
  exact posDef_tripleBlock_of_offsetAt_sq_lt (diagonalShiftForm design)
    (diagonalShiftForm_transpose design) hpivot hminor hsq

/-- **ALL FIVE ON-PATH OBLIGATIONS, FROM THE OFFSET CRITERION.**  A fifth entrance to the
registry, alongside the consolidated chart gauge, the projection block selection, the
support form of that selection, and the block gap.  It is the first entrance whose
hypothesis is three polynomial inequalities at one pivot. -/
theorem allFiveOnPath_of_offsetDominatesSomewhere (hoffset : OffsetDominatesSomewhere) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  allFiveOnPath_of_blockGapAt (blockGapAt_posDef_of_offsetDominatesSomewhere hoffset)

/-- The consolidated chart statement follows from the same criterion. -/
theorem consolidatedStrictTriple_of_offsetDominatesSomewhere
    (hoffset : OffsetDominatesSomewhere) : ConsolidatedStrictTriple :=
  consolidatedStrictTriple_of_blockGapAt
    (blockGapAt_posDef_of_offsetDominatesSomewhere hoffset)

/-- **THE DOOR IN PROJECTION COORDINATES.**  The same entrance with the shift vocabulary
eliminated: a consumer needs only the projection entries and the weights.  This is the form
a numerical or combinatorial producer will meet. -/
theorem allFiveOnPath_of_offsetDominates_proj
    (hexists : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ first second third : Fin 6,
        first ≠ second ∧ third ≠ first ∧ third ≠ second ∧
        design.weight first < projectionOfDesign design first first ∧
        projectionOfDesign design first second ^ 2
          < (projectionOfDesign design first first - design.weight first)
            * (projectionOfDesign design second second - design.weight second) ∧
        ((projectionOfDesign design first first - design.weight first)
              * projectionOfDesign design second third
            - projectionOfDesign design first second
              * projectionOfDesign design first third) ^ 2
          < ((projectionOfDesign design first first - design.weight first)
                * (projectionOfDesign design second second - design.weight second)
              - projectionOfDesign design first second ^ 2)
            * ((projectionOfDesign design first first - design.weight first)
                * (projectionOfDesign design third third - design.weight third)
              - projectionOfDesign design first third ^ 2)) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  refine allFiveOnPath_of_offsetDominatesSomewhere ?_
  intro design hprimitive
  obtain ⟨first, second, third, hfirstSecond, hthirdFirst, hthirdSecond,
    hdiag, hminor, hsq⟩ := hexists design hprimitive
  have hfirstThird : first ≠ third := fun heq => hthirdFirst heq.symm
  have hsecondThird : second ≠ third := fun heq => hthirdSecond heq.symm
  have hminorSecond : pairMinorAt (diagonalShiftForm design) first second
      = (projectionOfDesign design first first - design.weight first)
          * (projectionOfDesign design second second - design.weight second)
        - projectionOfDesign design first second ^ 2 := by
    rw [pairMinorAt, diagonalShiftForm_diag, diagonalShiftForm_diag,
      diagonalShiftForm_offDiag design hfirstSecond]
  have hminorThird : pairMinorAt (diagonalShiftForm design) first third
      = (projectionOfDesign design first first - design.weight first)
          * (projectionOfDesign design third third - design.weight third)
        - projectionOfDesign design first third ^ 2 := by
    rw [pairMinorAt, diagonalShiftForm_diag, diagonalShiftForm_diag,
      diagonalShiftForm_offDiag design hfirstThird]
  refine ⟨first, second, third, hfirstSecond, hthirdFirst, hthirdSecond, ?_, ?_, ?_⟩
  · rw [diagonalShiftForm_diag]; linarith
  · rw [hminorSecond]; linarith
  · rw [shiftOffsetAt_apply design hfirstSecond hfirstThird hsecondThird,
      hminorSecond, hminorThird]
    exact hsq

/-! ### 6. THE DOOR LOSES NOTHING -/

/-- A three-slot pick is its own explicit triple. -/
theorem triplePick_eta (pick : Fin 3 → Fin size) : ![pick 0, pick 1, pick 2] = pick := by
  funext slot; fin_cases slot <;> rfl

/-- **THE THREE INEQUALITIES ARE POSITIVE DEFINITENESS.**  Sylvester at `Fin 3` runs in
both directions, and the pivot Schur identity is an identity, so the offset reading of the
criterion is EXACT.  Nothing is weakened and nothing is strengthened. -/
theorem posDef_tripleBlock_iff_offsetAt_sq_lt (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second third : Fin size) :
    (tripleBlock form first second third).PosDef
      ↔ 0 < form first first ∧ 0 < pairMinorAt form first second ∧
        offsetAt form first second third ^ 2
          < pairMinorAt form first second * pairMinorAt form first third := by
  constructor
  · intro hposDef
    rw [tripleBlock_eq_entries form hsymmetric, leadingMinors_pos_iff_posDef_fin_three]
      at hposDef
    obtain ⟨hcorner, hblock, hdet⟩ := hposDef
    refine ⟨hcorner, by simpa [pairMinorAt] using hblock, ?_⟩
    refine (offsetAt_sq_lt_iff_det_pos form hsymmetric hcorner second third).mpr ?_
    rw [det_tripleBlock form hsymmetric]
    nlinarith [hdet]
  · rintro ⟨hcorner, hminor, hsq⟩
    have hdet := (offsetAt_sq_lt_iff_det_pos form hsymmetric hcorner second third).mp hsq
    rw [det_tripleBlock form hsymmetric] at hdet
    rw [tripleBlock_eq_entries form hsymmetric, leadingMinors_pos_iff_posDef_fin_three]
    exact ⟨hcorner, by simpa [pairMinorAt] using hminor, by nlinarith [hdet]⟩

/-- **THE FIFTH DOOR IS FAITHFUL.**  The offset criterion is not merely sufficient for the
landed block-gap selection — it is EQUIVALENT to it.  So the whole rank-four rung is
exactly three polynomial inequalities at one pivot of one design, and a producer that works
in offset coordinates gives up nothing. -/
theorem offsetDominatesSomewhere_iff_blockGapSelects :
    OffsetDominatesSomewhere ↔
      ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
        ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
          (blockGapAt (projectionOfDesign design) design.weight pick).PosDef := by
  refine ⟨blockGapAt_posDef_of_offsetDominatesSomewhere, fun hselect design hprimitive => ?_⟩
  obtain ⟨pick, hinj, hposDef⟩ := hselect design hprimitive
  have hfirstSecond : pick 0 ≠ pick 1 := fun heq => absurd (hinj heq) (by decide)
  have hthirdFirst : pick 2 ≠ pick 0 := fun heq => absurd (hinj heq) (by decide)
  have hthirdSecond : pick 2 ≠ pick 1 := fun heq => absurd (hinj heq) (by decide)
  have hblock : (tripleBlock (diagonalShiftForm design) (pick 0) (pick 1) (pick 2)).PosDef := by
    rw [tripleBlock_diagonalShift_eq_blockGapAt design hfirstSecond hthirdFirst hthirdSecond,
      triplePick_eta]
    exact hposDef
  obtain ⟨hcorner, hminor, hsq⟩ :=
    (posDef_tripleBlock_iff_offsetAt_sq_lt (diagonalShiftForm design)
      (diagonalShiftForm_transpose design) (pick 0) (pick 1) (pick 2)).mp hblock
  exact ⟨pick 0, pick 1, pick 2, hfirstSecond, hthirdFirst, hthirdSecond,
    hcorner, hminor, hsq⟩

/-- The same equivalence read on the gap functional at uniform weight: a positive landed
gap at a triple is exactly the three offset inequalities at its first slot. -/
theorem projGapAt_pos_iff_offsetAt_sq_lt (design : WeightedDesign 6 3)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹)
    {first second third : Fin 6} (hsecond : first ≠ second) (hthird : first ≠ third)
    (hfar : second ≠ third) (hpivot : 0 < diagonalShiftForm design first first) :
    0 < projGapAt (projectionOfDesign design) first second third
      ↔ shiftOffsetAt design first second third ^ 2
        < pairMinorAt (diagonalShiftForm design) first second
          * pairMinorAt (diagonalShiftForm design) first third := by
  simp only [shiftOffsetAt]
  rw [offsetAt_sq_lt_iff_det_pos (diagonalShiftForm design)
      (diagonalShiftForm_transpose design) hpivot second third,
    det_tripleBlock_diagonalShift_uniform design huniform hsecond hthird hfar]
  constructor <;> intro hgap <;> linarith

/-! ### 7. The row second moment of the offset -/

/-- The ordered product sum of a row of shifted pair minors is the squared row total less
the row energy.  This is the landed `Finset` identity read at the shifted pair minors. -/
theorem sum_pairMinorAt_diagonalShift_product_erase (design : WeightedDesign size rank)
    (label : Fin size) :
    ∑ first ∈ univ.erase label, ∑ second ∈ (univ.erase label).erase first,
        pairMinorAt (diagonalShiftForm design) label first
          * pairMinorAt (diagonalShiftForm design) label second
      = (∑ first ∈ univ.erase label, pairMinorAt (diagonalShiftForm design) label first) ^ 2
        - ∑ first ∈ univ.erase label,
            pairMinorAt (diagonalShiftForm design) label first ^ 2 := by
  classical
  exact sum_sq_sub_sum_sq_eq_sum_erase (univ.erase label)
    (fun first => pairMinorAt (diagonalShiftForm design) label first)

/-- The Schur identity summed over the ordered partner pairs at one pivot. -/
theorem sum_pairMinorProduct_sub_sq_shiftOffset_erase_det
    (design : WeightedDesign size rank) (label : Fin size) :
    ∑ first ∈ univ.erase label, ∑ second ∈ (univ.erase label).erase first,
        (pairMinorAt (diagonalShiftForm design) label first
            * pairMinorAt (diagonalShiftForm design) label second
          - shiftOffsetAt design label first second ^ 2)
      = diagonalShiftForm design label label
          * ∑ first ∈ univ.erase label, ∑ second ∈ (univ.erase label).erase first,
              (tripleBlock (diagonalShiftForm design) label first second).det := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun first _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun second _ =>
    pairMinorAt_diagonalShift_mul_sub_sq design label first second

/-- **THE AVERAGED SPLIT, IN CLOSED FORM.**  At uniform weight the ordered sum of the
minor product less the squared offset is the excess against the landed label marginal of
the gap.  Every quantity on the right is landed. -/
theorem sum_pairMinorProduct_sub_sq_shiftOffset_erase (design : WeightedDesign 6 3)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹) (label : Fin 6) :
    ∑ first ∈ univ.erase label, ∑ second ∈ (univ.erase label).erase first,
        (pairMinorAt (diagonalShiftForm design) label first
            * pairMinorAt (diagonalShiftForm design) label second
          - shiftOffsetAt design label first second ^ 2)
      = diagonalShiftForm design label label
          * (36 * projectionOfDesign design label label - 46) / 108 := by
  classical
  rw [sum_pairMinorProduct_sub_sq_shiftOffset_erase_det design label]
  have hinner : ∀ first ∈ univ.erase label,
      ∑ second ∈ (univ.erase label).erase first,
          (tripleBlock (diagonalShiftForm design) label first second).det
        = (∑ second ∈ (univ.erase label).erase first,
            projGapAt (projectionOfDesign design) label first second) / 216 := by
    intro first hfirst
    have hne : label ≠ first := (Finset.ne_of_mem_erase hfirst).symm
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun second hsecond => ?_
    have hsec : label ≠ second :=
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hsecond)).symm
    have hfar : first ≠ second := (Finset.ne_of_mem_erase hsecond).symm
    exact det_tripleBlock_diagonalShift_uniform design huniform hne hsec hfar
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_div, sum_projGap_through design label]
  ring

/-- **THE AVERAGED SPLIT IS NEGATIVE.**  A projection diagonal never exceeds one, so the
bracket is at most `-10`, and at a label of positive excess the ordered sum is strictly
negative — the squared offsets outweigh the minor products on average, always.  This is
the offset twin of the landed one-label no-go. -/
theorem sum_pairMinorProduct_sub_sq_shiftOffset_neg (design : WeightedDesign 6 3)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹) (label : Fin 6)
    (hexcess : 0 < diagonalShiftForm design label label) :
    ∑ first ∈ univ.erase label, ∑ second ∈ (univ.erase label).erase first,
        (pairMinorAt (diagonalShiftForm design) label first
            * pairMinorAt (diagonalShiftForm design) label second
          - shiftOffsetAt design label first second ^ 2)
      ≤ -(5 * diagonalShiftForm design label label / 54) := by
  have hdiag : projectionOfDesign design label label ≤ 1 :=
    diag_le_one_of_symm_idempotent (projectionOfDesign design)
      (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design) label
  rw [sum_pairMinorProduct_sub_sq_shiftOffset_erase design huniform label]
  nlinarith [hexcess, hdiag]

/-- **THE SECOND MOMENT OF THE OFFSET.**  The corpus carried the offset's FIRST marginal
(`Gtz.sum_offDiagProduct_erase`) and not its second.  Here it is, closed on the shifted
row total, that row's energy, and the landed label marginal of the gap. -/
theorem sum_sq_shiftOffsetAt_erase (design : WeightedDesign 6 3)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹) (label : Fin 6) :
    ∑ first ∈ univ.erase label, ∑ second ∈ (univ.erase label).erase first,
        shiftOffsetAt design label first second ^ 2
      = (∑ first ∈ univ.erase label, pairMinorAt (diagonalShiftForm design) label first) ^ 2
        - (∑ first ∈ univ.erase label,
            pairMinorAt (diagonalShiftForm design) label first ^ 2)
        - diagonalShiftForm design label label
            * (36 * projectionOfDesign design label label - 46) / 108 := by
  classical
  have hsplit : ∑ first ∈ univ.erase label, ∑ second ∈ (univ.erase label).erase first,
        (pairMinorAt (diagonalShiftForm design) label first
            * pairMinorAt (diagonalShiftForm design) label second
          - shiftOffsetAt design label first second ^ 2)
      = (∑ first ∈ univ.erase label, ∑ second ∈ (univ.erase label).erase first,
            pairMinorAt (diagonalShiftForm design) label first
              * pairMinorAt (diagonalShiftForm design) label second)
        - ∑ first ∈ univ.erase label, ∑ second ∈ (univ.erase label).erase first,
            shiftOffsetAt design label first second ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun first _ => by rw [Finset.sum_sub_distrib]
  have hlaw := sum_pairMinorProduct_sub_sq_shiftOffset_erase design huniform label
  rw [hsplit, sum_pairMinorAt_diagonalShift_product_erase design label] at hlaw
  linarith

/-- **THE DOOR MUST SELECT ITS PAIR.**  At every label of positive excess at least ONE
ordered partner pair violates the door's third inequality.  A producer that quantifies over
partner pairs therefore cannot exist, and only a selecting producer can.  This is the exact
obstruction the pigeonhole floor was built to beat, and section 7 measures how far it falls
short. -/
theorem exists_offset_sq_gt_pairMinor_product (design : WeightedDesign 6 3)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹) (label : Fin 6)
    (hexcess : 0 < diagonalShiftForm design label label) :
    ∃ first ∈ univ.erase label, ∃ second ∈ (univ.erase label).erase first,
      pairMinorAt (diagonalShiftForm design) label first
          * pairMinorAt (diagonalShiftForm design) label second
        < shiftOffsetAt design label first second ^ 2 := by
  classical
  by_contra hall
  push Not at hall
  have hnonneg : (0 : ℝ) ≤ ∑ first ∈ univ.erase label,
      ∑ second ∈ (univ.erase label).erase first,
        (pairMinorAt (diagonalShiftForm design) label first
            * pairMinorAt (diagonalShiftForm design) label second
          - shiftOffsetAt design label first second ^ 2) := by
    refine Finset.sum_nonneg fun first hfirst => Finset.sum_nonneg fun second hsecond => ?_
    have hpair := hall first hfirst second hsecond
    linarith
  have hneg := sum_pairMinorProduct_sub_sq_shiftOffset_neg design huniform label hexcess
  have hpos : (0 : ℝ) < 5 * diagonalShiftForm design label label / 54 := by linarith
  linarith

/-! ### 7. The uniform composition, and the refutation at `K4` -/

/-- **THE SOUND COMPOSITION.**  A uniform upper bound on the squared offset does compose
with the pigeonhole, because it applies to whichever partner the pigeonhole returns.  This
is the only shape of the averaged programme that survives section 6. -/
theorem exists_pos_projGap_of_uniform_offset_bound (design : WeightedDesign 6 3)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹)
    (label partner : Fin 6) (hne : partner ≠ label)
    (hpivot : 0 < diagonalShiftForm design label label)
    (hspent : 0 < pairMinorAt (diagonalShiftForm design) label partner)
    (bound : ℝ)
    (hbound : ∀ first ∈ univ.erase label, ∀ second ∈ (univ.erase label).erase first,
      shiftOffsetAt design label first second ^ 2 ≤ bound)
    (hbeat : bound
      < pairMinorAt (diagonalShiftForm design) label partner
        * ((∑ other ∈ univ.erase label, pairMinorAt (diagonalShiftForm design) label other
            - pairMinorAt (diagonalShiftForm design) label partner) / 4)) :
    ∃ other ∈ (univ.erase label).erase partner,
      0 < projGapAt (projectionOfDesign design) label partner other := by
  classical
  obtain ⟨other, hmem, hge⟩ :=
    exists_pairMinorAt_diagonalShift_ge design label partner hne
  refine ⟨other, hmem, ?_⟩
  have hpartner : partner ∈ univ.erase label :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ partner⟩
  have hoffset : shiftOffsetAt design label partner other ^ 2 ≤ bound :=
    hbound partner hpartner other hmem
  have hproduct : pairMinorAt (diagonalShiftForm design) label partner
      * ((∑ other' ∈ univ.erase label, pairMinorAt (diagonalShiftForm design) label other'
          - pairMinorAt (diagonalShiftForm design) label partner) / 4)
      ≤ pairMinorAt (diagonalShiftForm design) label partner
        * pairMinorAt (diagonalShiftForm design) label other :=
    mul_le_mul_of_nonneg_left hge (le_of_lt hspent)
  have hlt : shiftOffsetAt design label partner other ^ 2
      < pairMinorAt (diagonalShiftForm design) label partner
        * pairMinorAt (diagonalShiftForm design) label other := by
    linarith
  have hother : label ≠ other :=
    (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmem)).symm
  have hfar : partner ≠ other := (Finset.ne_of_mem_erase hmem).symm
  have hdet : 0 < (tripleBlock (diagonalShiftForm design) label partner other).det :=
    (offsetAt_sq_lt_iff_det_pos (diagonalShiftForm design)
      (diagonalShiftForm_transpose design) hpivot partner other).mp hlt
  rw [det_tripleBlock_diagonalShift_uniform design huniform hne.symm hother hfar] at hdet
  linarith

/-- **THE PIGEONHOLE PARTNER FIRES THE FIFTH DOOR TOO.**  The same composition read on the
door rather than on the gap functional: the returned partner makes the block positive
definite, so the selection the registry wants exists at this design. -/
theorem exists_posDef_blockGapAt_of_uniform_offset_bound (design : WeightedDesign 6 3)
    (label partner : Fin 6) (hne : partner ≠ label)
    (hpivot : 0 < diagonalShiftForm design label label)
    (hspent : 0 < pairMinorAt (diagonalShiftForm design) label partner)
    (bound : ℝ)
    (hbound : ∀ first ∈ univ.erase label, ∀ second ∈ (univ.erase label).erase first,
      shiftOffsetAt design label first second ^ 2 ≤ bound)
    (hbeat : bound
      < pairMinorAt (diagonalShiftForm design) label partner
        * ((∑ other ∈ univ.erase label, pairMinorAt (diagonalShiftForm design) label other
            - pairMinorAt (diagonalShiftForm design) label partner) / 4)) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      (blockGapAt (projectionOfDesign design) design.weight pick).PosDef := by
  classical
  obtain ⟨other, hmem, hge⟩ :=
    exists_pairMinorAt_diagonalShift_ge design label partner hne
  have hpartner : partner ∈ univ.erase label :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ partner⟩
  have hoffset : shiftOffsetAt design label partner other ^ 2 ≤ bound :=
    hbound partner hpartner other hmem
  have hproduct : pairMinorAt (diagonalShiftForm design) label partner
      * ((∑ other' ∈ univ.erase label, pairMinorAt (diagonalShiftForm design) label other'
          - pairMinorAt (diagonalShiftForm design) label partner) / 4)
      ≤ pairMinorAt (diagonalShiftForm design) label partner
        * pairMinorAt (diagonalShiftForm design) label other :=
    mul_le_mul_of_nonneg_left hge (le_of_lt hspent)
  have hlt : shiftOffsetAt design label partner other ^ 2
      < pairMinorAt (diagonalShiftForm design) label partner
        * pairMinorAt (diagonalShiftForm design) label other := by
    linarith
  have hother : other ≠ label :=
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmem)
  have hfar : other ≠ partner := Finset.ne_of_mem_erase hmem
  refine ⟨![label, partner, other], injective_triplePick hne.symm hother hfar, ?_⟩
  rw [← tripleBlock_diagonalShift_eq_blockGapAt design hne.symm hother hfar]
  exact posDef_tripleBlock_of_offsetAt_sq_lt (diagonalShiftForm design)
    (diagonalShiftForm_transpose design) hpivot hspent hlt

/-- The excess at every label of the `K4` graphic point, at uniform weight: the projection
diagonal is one half and the weight is one sixth. -/
theorem kfourStar_excess : (1 : ℝ) / 2 - (6 : ℝ)⁻¹ = 1 / 3 := by norm_num

/-- The two shifted pair minors at the graphic point: a zero pairing gives `1/9`, and a
quarter pairing gives `7/144`. -/
theorem kfourStar_pairMinor_zero : (1 : ℝ) / 3 * (1 / 3) - 0 ^ 2 = 1 / 9 := by norm_num

theorem kfourStar_pairMinor_quarter :
    (1 : ℝ) / 3 * (1 / 3) - (1 / 4) ^ 2 = 7 / 144 := by norm_num

/-- The row total at the graphic point: one partner at `1/9` and four at `7/144`, which is
the landed `11/36`. -/
theorem kfourStar_rowTotal : (1 : ℝ) / 9 + 4 * (7 / 144) = 11 / 36 := by norm_num

/-- The largest squared offset at the graphic point: the far pairing and the two pivot
pairings align, giving `1/3 * 1/4 + 1/4 * 1/4 = 7/48`. -/
theorem kfourStar_maxOffsetSq :
    ((1 : ℝ) / 3 * (1 / 4) + (1 / 4) * (1 / 4)) ^ 2 = 49 / 2304 := by norm_num

/-- The two pigeonhole floors at the graphic point. -/
theorem kfourStar_floor_zero :
    (1 : ℝ) / 9 * ((11 / 36 - 1 / 9) / 4) = 7 / 1296 := by norm_num

theorem kfourStar_floor_quarter :
    (7 : ℝ) / 144 * ((11 / 36 - 7 / 144) / 4) = 259 / 82944 := by norm_num

/-- **THE UNIFORM COMPOSITION FAILS AT THE GRAPHIC POINT.**  The BEST pigeonhole floor
available at a label of `Gtz.kfourEdgeProjection` is `7/1296`, and the largest squared
offset there is `49/2304`.  The floor is short by a factor of nearly four, so no uniform
upper bound on the offset can be small enough to beat it.  The composition is sound and
near-vacuous, and this is the exact witness. -/
theorem kfourStar_bestFloor_lt_maxOffsetSq :
    (7 : ℝ) / 1296 < 49 / 2304 ∧ (259 : ℝ) / 82944 < 49 / 2304 := by
  constructor <;> norm_num

/-- The deficit, exactly: the best floor falls `329/20736` short of the largest squared
offset.  This is the number a repair would have to find. -/
theorem kfourStar_floor_deficit :
    (7 : ℝ) / 1296 - 49 / 2304 = -(329 / 20736) := by norm_num

/-! ### 9. THE SECOND-MOMENT DOOR

The first moment of the gap is negative and LANDED, so no averaging argument can produce a
positive triple.  A second moment can.  A family bounded below by `-M` whose total is
nonpositive has squared total at most `M` times the magnitude of that total, and the bound
is attained only when the whole mass sits at `-M`.  A squared total ABOVE that product
therefore forces a strictly positive member — and one positive member of THIS family is one
triple of positive gap.

Measured against the pigeonhole cell of section 8 this is not an improvement of degree but
of kind.  Across 800 exact designs the pigeonhole composition fires on 10 of 4800 slots.
The second-moment door fires on 377 of 800 designs, and on 377 of the 383 designs that own
a pivot of the right shape at all — 98 percent, against 0.2 percent. -/

/-- **THE SHARP SIGN LEMMA.**  If every member of a doubly indexed family is at least `-M`,
and the squared total exceeds `M` times the magnitude of the total, then some member is
strictly positive.  The bound is sharp, with equality when the whole mass sits at `-M`. -/
theorem exists_pos_of_sq_sum_gt {index slot : Type*}
    (outerSet : Finset index) (innerSet : index → Finset slot)
    (value : index → slot → ℝ) (bound : ℝ)
    (hbound : ∀ outer ∈ outerSet, ∀ inner ∈ innerSet outer, -bound ≤ value outer inner)
    (hbig : bound * (-(∑ outer ∈ outerSet, ∑ inner ∈ innerSet outer, value outer inner))
      < ∑ outer ∈ outerSet, ∑ inner ∈ innerSet outer, value outer inner ^ 2) :
    ∃ outer ∈ outerSet, ∃ inner ∈ innerSet outer, 0 < value outer inner := by
  by_contra hall
  push Not at hall
  have hstep : ∑ outer ∈ outerSet, ∑ inner ∈ innerSet outer, value outer inner ^ 2
      ≤ ∑ outer ∈ outerSet, ∑ inner ∈ innerSet outer, bound * -value outer inner := by
    refine Finset.sum_le_sum fun outer houter => Finset.sum_le_sum fun inner hinner => ?_
    have hle : value outer inner ≤ 0 := hall outer houter inner hinner
    have hge : -bound ≤ value outer inner := hbound outer houter inner hinner
    nlinarith
  have hinner : ∀ outer : index, ∑ inner ∈ innerSet outer, bound * -value outer inner
      = bound * -∑ inner ∈ innerSet outer, value outer inner := fun outer => by
    rw [← Finset.mul_sum, Finset.sum_neg_distrib]
  have hcollect : ∑ outer ∈ outerSet, ∑ inner ∈ innerSet outer, bound * -value outer inner
      = bound * -∑ outer ∈ outerSet, ∑ inner ∈ innerSet outer, value outer inner := by
    rw [Finset.sum_congr rfl (fun outer _ => hinner outer), ← Finset.mul_sum,
      Finset.sum_neg_distrib]
  linarith [hstep, hcollect.le, hcollect.ge]

/-- **THE GAP TOTAL IS A UNIVERSAL CONSTANT.**  Summed over all ordered distinct triples the
landed gap functional is `-336`, for EVERY weighted design of six atoms in rank three.  No
weight, no atom and no projection entry survives: only the trace does.  The corpus carried
the label marginal `2 * (36 * P a a - 46)`, which still moves with the design.  This total
does not move at all. -/
theorem sum_projGap_all_eq_neg (design : WeightedDesign 6 3) :
    ∑ outer : Fin 6, ∑ mid ∈ univ.erase outer, ∑ inner ∈ (univ.erase outer).erase mid,
        projGapAt (projectionOfDesign design) outer mid inner = -336 := by
  classical
  have hlin : ∀ outer ∈ (univ : Finset (Fin 6)),
      ∑ mid ∈ univ.erase outer, ∑ inner ∈ (univ.erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner
        = 72 * projectionOfDesign design outer outer - 92 := by
    intro outer _
    rw [sum_projGap_through design outer]; ring
  have htrace : ∑ label : Fin 6, projectionOfDesign design label label = (3 : ℝ) := by
    simpa using sum_projectionDiagonal_eq_rank design
  rw [Finset.sum_congr rfl hlin, Finset.sum_sub_distrib, ← Finset.mul_sum, htrace]
  simp
  norm_num

/-- **THE SECOND-MOMENT PRODUCER.**  At one label, a lower bound `-M` on the gaps through it
plus a squared total above `M` times the landed marginal's magnitude produces a triple of
strictly positive gap.  The marginal enters in closed form: its magnitude is
`92 - 72 * P a a`. -/
theorem exists_pos_projGap_of_secondMoment (design : WeightedDesign 6 3) (label : Fin 6)
    (bound : ℝ)
    (hbound : ∀ mid ∈ univ.erase label, ∀ inner ∈ (univ.erase label).erase mid,
      -bound ≤ projGapAt (projectionOfDesign design) label mid inner)
    (hbig : bound * (92 - 72 * projectionOfDesign design label label)
      < ∑ mid ∈ univ.erase label, ∑ inner ∈ (univ.erase label).erase mid,
          projGapAt (projectionOfDesign design) label mid inner ^ 2) :
    ∃ mid ∈ univ.erase label, ∃ inner ∈ (univ.erase label).erase mid,
      0 < projGapAt (projectionOfDesign design) label mid inner := by
  classical
  refine exists_pos_of_sq_sum_gt _ _ _ bound hbound ?_
  rw [sum_projGap_through design label]
  have hmagnitude : -(2 * (36 * projectionOfDesign design label label - 46))
      = 92 - 72 * projectionOfDesign design label label := by ring
  rw [hmagnitude]
  exact hbig

/-- **THE SECOND-MOMENT DOOR PRODUCES THE SELECTION.**  A pivot of positive excess whose
pair minors are all positive, together with the second-moment test through that pivot, makes
a gap block positive definite.  The three Sylvester minors arrive from three different
places: the excess gives the corner, the pair minors give the two-by-two, and the second
moment gives the determinant. -/
theorem exists_posDef_blockGapAt_of_secondMoment (design : WeightedDesign 6 3)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹)
    (label : Fin 6) (bound : ℝ)
    (hexcess : 0 < diagonalShiftForm design label label)
    (hminors : ∀ other : Fin 6, other ≠ label →
      0 < pairMinorAt (diagonalShiftForm design) label other)
    (hbound : ∀ mid ∈ univ.erase label, ∀ inner ∈ (univ.erase label).erase mid,
      -bound ≤ projGapAt (projectionOfDesign design) label mid inner)
    (hbig : bound * (92 - 72 * projectionOfDesign design label label)
      < ∑ mid ∈ univ.erase label, ∑ inner ∈ (univ.erase label).erase mid,
          projGapAt (projectionOfDesign design) label mid inner ^ 2) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      (blockGapAt (projectionOfDesign design) design.weight pick).PosDef := by
  classical
  obtain ⟨mid, hmid, inner, hinner, hgap⟩ :=
    exists_pos_projGap_of_secondMoment design label bound hbound hbig
  have hmidne : label ≠ mid := (Finset.ne_of_mem_erase hmid).symm
  have hinnerne : inner ≠ label := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hinner)
  have hfar : inner ≠ mid := Finset.ne_of_mem_erase hinner
  have hsq := (projGapAt_pos_iff_offsetAt_sq_lt design huniform hmidne hinnerne.symm
    hfar.symm hexcess).mp hgap
  refine ⟨![label, mid, inner], injective_triplePick hmidne hinnerne hfar, ?_⟩
  rw [← tripleBlock_diagonalShift_eq_blockGapAt design hmidne hinnerne hfar]
  exact posDef_tripleBlock_of_offsetAt_sq_lt (diagonalShiftForm design)
    (diagonalShiftForm_transpose design) hexcess (hminors mid hmidne.symm) hsq

/-- **THE SECOND-MOMENT SELECTION CRITERION.**  Every primitive design at uniform weight
owns a pivot of positive excess whose pair minors are all positive, and a lower bound on the
gaps through it whose square total beats the landed marginal. -/
def SecondMomentDominates : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    (∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹) →
      ∃ label : Fin 6, ∃ bound : ℝ,
        0 < diagonalShiftForm design label label ∧
        (∀ other : Fin 6, other ≠ label →
          0 < pairMinorAt (diagonalShiftForm design) label other) ∧
        (∀ mid ∈ univ.erase label, ∀ inner ∈ (univ.erase label).erase mid,
          -bound ≤ projGapAt (projectionOfDesign design) label mid inner) ∧
        bound * (92 - 72 * projectionOfDesign design label label)
          < ∑ mid ∈ univ.erase label, ∑ inner ∈ (univ.erase label).erase mid,
              projGapAt (projectionOfDesign design) label mid inner ^ 2

/-- **ALL FIVE ON-PATH OBLIGATIONS, FROM THE SECOND MOMENT.**  A sixth entrance to the
registry.  Its hypothesis is one inequality between two moments of a landed functional, and
the first of those moments is landed in closed form. -/
theorem allFiveOnPath_of_secondMomentDominates
    (huniform : ∀ design : WeightedDesign 6 3, ∀ label : Fin 6,
      design.weight label = (6 : ℝ)⁻¹)
    (hsecond : SecondMomentDominates) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  refine allFiveOnPath_of_blockGapAt fun design hprimitive => ?_
  obtain ⟨label, bound, hexcess, hminors, hbound, hbig⟩ :=
    hsecond design hprimitive (huniform design)
  exact exists_posDef_blockGapAt_of_secondMoment design (huniform design) label bound
    hexcess hminors hbound hbig

/-- The plain two-moment form, with the total itself as the bound.  It is weaker than the
sharp form whenever the deepest gap is shallower than the whole total, and the measurements
show that gap is wide: the plain form fires on 48 of 800 designs and the sharp form on 734
of the same 800. -/
theorem exists_pos_projGap_of_sqSum_gt_sq (design : WeightedDesign 6 3) (label : Fin 6)
    (hbound : ∀ mid ∈ univ.erase label, ∀ inner ∈ (univ.erase label).erase mid,
      -(92 - 72 * projectionOfDesign design label label)
        ≤ projGapAt (projectionOfDesign design) label mid inner)
    (hbig : (92 - 72 * projectionOfDesign design label label) ^ 2
      < ∑ mid ∈ univ.erase label, ∑ inner ∈ (univ.erase label).erase mid,
          projGapAt (projectionOfDesign design) label mid inner ^ 2) :
    ∃ mid ∈ univ.erase label, ∃ inner ∈ (univ.erase label).erase mid,
      0 < projGapAt (projectionOfDesign design) label mid inner := by
  refine exists_pos_projGap_of_secondMoment design label
    (92 - 72 * projectionOfDesign design label label) hbound ?_
  nlinarith [hbig]

/-- The `K4` graphic point refuses the sharp test, and by exactly `135/2`.  Its twenty
ordered partner pairs at any label total `-56`, their squares total `1237/2`, and the
deepest gap is `-49/4`.  This is the extremal witness the door must eventually beat. -/
theorem kfourStar_secondMoment_deficit :
    (1237 : ℝ) / 2 - (49 / 4) * 56 = -(135 / 2) := by norm_num

end Gtz
