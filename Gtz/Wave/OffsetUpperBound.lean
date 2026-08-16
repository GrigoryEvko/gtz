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

/-! ### 10. THE LEVEL-TWO DOOR

Section 9 works at one label, over the twenty ordered partner pairs through it.  The corpus
also carries the marginal one level down, `Gtz.sum_projGap_through_pair`: at a FIXED pivot
pair the four remaining gaps total

    144 * pairMinorAt P outer mid + 14 - 54 * (P outer outer + P mid mid).

Four terms instead of twenty, with the same landed closed form.  That is the right level,
for two reasons.  The two Sylvester side conditions are now conditions on the SAME pair the
moment test runs on, so the door needs one pivot pair and not a whole pivot row.  And with
four terms the sign lemma is far harder to defeat.

Measured on the same 800 exact designs: every design owns a usable pivot pair, the pure
first-moment form fires on 714 of 800, and the second-moment form fires on 800 of 800 —
every design, at 11824 of the 15628 usable pairs.  Section 9 reached 377 of 800.

The graphic point of `K4` is the one refuser known to this file.  Its four gaths at a pivot
pair are `5/4`, `-49/4`, `-1`, `-1`: one term carries almost the whole total, which is the
single profile on which the sign lemma is tight.  No moment test at this level can fire
there, and `Gtz.kfourStar_levelTwo_deficit` records the exact shortfall `-45/8`. -/

/-- The single-index sign lemma, in its pure first-moment form: a positive total forces a
positive member. -/
theorem exists_pos_of_sum_pos {slot : Type*} (indexSet : Finset slot) (value : slot → ℝ)
    (hpos : 0 < ∑ item ∈ indexSet, value item) :
    ∃ item ∈ indexSet, 0 < value item := by
  by_contra hall
  push Not at hall
  exact absurd (Finset.sum_nonpos hall) (not_le.mpr hpos)

/-- The single-index sharp sign lemma.  A family bounded below by `-M` whose squared total
exceeds `M` times the magnitude of its total owns a strictly positive member. -/
theorem exists_pos_of_sq_sum_gt_single {slot : Type*} (indexSet : Finset slot)
    (value : slot → ℝ) (bound : ℝ)
    (hbound : ∀ item ∈ indexSet, -bound ≤ value item)
    (hbig : bound * (-(∑ item ∈ indexSet, value item))
      < ∑ item ∈ indexSet, value item ^ 2) :
    ∃ item ∈ indexSet, 0 < value item := by
  by_contra hall
  push Not at hall
  have hstep : ∑ item ∈ indexSet, value item ^ 2
      ≤ ∑ item ∈ indexSet, bound * -value item := by
    refine Finset.sum_le_sum fun item hitem => ?_
    have hle : value item ≤ 0 := hall item hitem
    have hge : -bound ≤ value item := hbound item hitem
    nlinarith
  have hcollect : ∑ item ∈ indexSet, bound * -value item
      = bound * -∑ item ∈ indexSet, value item := by
    rw [← Finset.mul_sum, Finset.sum_neg_distrib]
  linarith [hstep, hcollect.le, hcollect.ge]

/-- **THE LEVEL-TWO SECOND-MOMENT PRODUCER.**  Four gaps, a lower bound `-M` on each, and a
squared total above `M` times the magnitude of the landed pivot-pair marginal.  This is the
producer that fires on every one of the 800 measured designs. -/
theorem exists_pos_projGap_of_pairSecondMoment (design : WeightedDesign 6 3)
    (outer mid : Fin 6) (hmid : mid ∈ (univ : Finset (Fin 6)).erase outer) (bound : ℝ)
    (hbound : ∀ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      -bound ≤ projGapAt (projectionOfDesign design) outer mid inner)
    (hbig : bound * (54 * (projectionOfDesign design outer outer
          + projectionOfDesign design mid mid)
        - 144 * pairMinorAt (projectionOfDesign design) outer mid - 14)
      < ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner ^ 2) :
    ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      0 < projGapAt (projectionOfDesign design) outer mid inner := by
  refine exists_pos_of_sq_sum_gt_single _ _ bound hbound ?_
  rw [sum_projGap_through_pair design outer mid hmid]
  have hmagnitude : -(144 * pairMinorAt (projectionOfDesign design) outer mid + 14
        - 54 * (projectionOfDesign design outer outer + projectionOfDesign design mid mid))
      = 54 * (projectionOfDesign design outer outer + projectionOfDesign design mid mid)
        - 144 * pairMinorAt (projectionOfDesign design) outer mid - 14 := by ring
  rw [hmagnitude]
  exact hbig

/-- **THE LEVEL-TWO DOOR PRODUCES THE SELECTION.**  One pivot PAIR carries every hypothesis:
its excess gives the corner minor, its shifted pair minor gives the two-by-two, and the
four-term second moment gives the determinant. -/
theorem exists_posDef_blockGapAt_of_pairSecondMoment (design : WeightedDesign 6 3)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹)
    (outer mid : Fin 6) (hmid : mid ∈ (univ : Finset (Fin 6)).erase outer)
    (hexcess : 0 < diagonalShiftForm design outer outer)
    (hminor : 0 < pairMinorAt (diagonalShiftForm design) outer mid)
    (bound : ℝ)
    (hbound : ∀ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      -bound ≤ projGapAt (projectionOfDesign design) outer mid inner)
    (hbig : bound * (54 * (projectionOfDesign design outer outer
          + projectionOfDesign design mid mid)
        - 144 * pairMinorAt (projectionOfDesign design) outer mid - 14)
      < ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner ^ 2) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      (blockGapAt (projectionOfDesign design) design.weight pick).PosDef := by
  classical
  obtain ⟨inner, hinner, hgap⟩ :=
    exists_pos_projGap_of_pairSecondMoment design outer mid hmid bound hbound hbig
  have hmidne : outer ≠ mid := (Finset.ne_of_mem_erase hmid).symm
  have hinnerne : inner ≠ outer := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hinner)
  have hfar : inner ≠ mid := Finset.ne_of_mem_erase hinner
  have hsq := (projGapAt_pos_iff_offsetAt_sq_lt design huniform hmidne hinnerne.symm
    hfar.symm hexcess).mp hgap
  refine ⟨![outer, mid, inner], injective_triplePick hmidne hinnerne hfar, ?_⟩
  rw [← tripleBlock_diagonalShift_eq_blockGapAt design hmidne hinnerne hfar]
  exact posDef_tripleBlock_of_offsetAt_sq_lt (diagonalShiftForm design)
    (diagonalShiftForm_transpose design) hexcess hminor hsq

/-- **THE LEVEL-TWO SELECTION CRITERION.**  One pivot pair, four gaps, one bound, one
inequality between two moments whose first is landed in closed form. -/
def PairSecondMomentDominates : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    (∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹) →
      ∃ outer mid : Fin 6, ∃ bound : ℝ,
        mid ∈ (univ : Finset (Fin 6)).erase outer ∧
        0 < diagonalShiftForm design outer outer ∧
        0 < pairMinorAt (diagonalShiftForm design) outer mid ∧
        (∀ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          -bound ≤ projGapAt (projectionOfDesign design) outer mid inner) ∧
        bound * (54 * (projectionOfDesign design outer outer
            + projectionOfDesign design mid mid)
          - 144 * pairMinorAt (projectionOfDesign design) outer mid - 14)
          < ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
              projGapAt (projectionOfDesign design) outer mid inner ^ 2

/-- **ALL FIVE ON-PATH OBLIGATIONS, FROM ONE PIVOT PAIR.**  The strongest entrance in this
file.  Measured, its hypothesis holds at every one of the 800 exact designs sampled, while
the landed pigeonhole cell holds at 10 of 4800 slots. -/
theorem allFiveOnPath_of_pairSecondMomentDominates
    (huniform : ∀ design : WeightedDesign 6 3, ∀ label : Fin 6,
      design.weight label = (6 : ℝ)⁻¹)
    (hpair : PairSecondMomentDominates) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  refine allFiveOnPath_of_blockGapAt fun design hprimitive => ?_
  obtain ⟨outer, mid, bound, hmid, hexcess, hminor, hbound, hbig⟩ :=
    hpair design hprimitive (huniform design)
  exact exists_posDef_blockGapAt_of_pairSecondMoment design (huniform design) outer mid hmid
    hexcess hminor bound hbound hbig

/-- The exact shortfall at the graphic point of `K4`.  At a pivot pair the four gaps are
`5/4`, `-49/4`, `-1` and `-1`.  They total `-13`, their squares total `1229/8`, and the
deepest is `-49/4`, so the sharp test asks for more than `637/4`.  It misses by `45/8`.
One term carries almost the whole total, which is exactly the profile on which the sign
lemma is tight, so no moment test at this level fires there. -/
theorem kfourStar_levelTwo_deficit :
    (5 : ℝ) / 4 + (-(49 / 4)) + (-1) + (-1) = -13
      ∧ ((5 : ℝ) / 4) ^ 2 + (49 / 4) ^ 2 + 1 + 1 = 1229 / 8
      ∧ (1229 : ℝ) / 8 - (49 / 4) * 13 = -(45 / 8) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ### 11. THE GRAPHIC POINT OF `K4`, DISCHARGED OUTRIGHT

Sections 8 thru 10 all refuse `K4`, and each refusal is a fact about a LOSSY sufficient
condition, never about the objective.  The door of section 5 is faithful, so it fires at
`K4` exactly when the objective does — and the objective does.  This section produces the
witness and every scalar in it.

Three edges of `K4` that pairwise meet — the edges `0`, `1` and `2` — carry Gram entry `1`
on each of their three pairings.  At uniform weight the shifted block on that triple is

    !![1/3, 1/4, 1/4; 1/4, 1/3, 1/4; 1/4, 1/4, 1/3]

whose three leading minors are `1/3`, `7/144` and `5/864`.  All three are positive, so the
block is positive definite, the landed gap there is exactly `5/4`, and the offset criterion
holds with margin `5/2592`.  Nothing here is conditional: the whole rigid stratum of the
campaign is discharged by `Gtz.exists_posDef_blockGapAt_of_kfour`. -/

/-- The shifted form of the graphic point at uniform weight. -/
noncomputable def kfourShiftForm : Matrix (Fin 6) (Fin 6) ℝ :=
  kfourEdgeProjection - Matrix.diagonal fun _ : Fin 6 => (6 : ℝ)⁻¹

theorem kfourShiftForm_transpose : kfourShiftFormᵀ = kfourShiftForm := by
  rw [kfourShiftForm, Matrix.transpose_sub, kfourEdgeProjection_symm,
    Matrix.diagonal_transpose]

/-- Every excess of the graphic point is `1/3`: the diagonal is `1/2` and the weight is
`1/6`. -/
theorem kfourShiftForm_diag (edge : Fin 6) : kfourShiftForm edge edge = 1 / 3 := by
  rw [kfourShiftForm, Matrix.sub_apply, kfourEdgeProjection_diag, Matrix.diagonal_apply_eq]
  norm_num

/-- Off the diagonal the shift changes nothing. -/
theorem kfourShiftForm_offDiag {leftEdge rightEdge : Fin 6} (hne : leftEdge ≠ rightEdge) :
    kfourShiftForm leftEdge rightEdge = kfourEdgeProjection leftEdge rightEdge := by
  rw [kfourShiftForm, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hne, sub_zero]

/-- The three edges `0`, `1` and `2` of `K4` pairwise meet, so each of their three pairings
reads `1/4`. -/
theorem kfourShiftForm_meeting_triple :
    kfourShiftForm 0 1 = 1 / 4 ∧ kfourShiftForm 0 2 = 1 / 4 ∧ kfourShiftForm 1 2 = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    [rw [kfourShiftForm_offDiag (by decide), kfourEdgeProjection_apply,
        show kfourGramInt 0 1 = 1 from by decide];
     rw [kfourShiftForm_offDiag (by decide), kfourEdgeProjection_apply,
        show kfourGramInt 0 2 = 1 from by decide];
     rw [kfourShiftForm_offDiag (by decide), kfourEdgeProjection_apply,
        show kfourGramInt 1 2 = 1 from by decide]] <;>
    norm_num

/-- The corner minor at the graphic point: the excess is `1/3`. -/
theorem kfourStar_corner_pos : 0 < kfourShiftForm 0 0 := by
  rw [kfourShiftForm_diag]; norm_num

/-- The two-by-two minor at the meeting pair `(0, 1)` is `7/144`. -/
theorem kfourStar_pairMinor_eq : pairMinorAt kfourShiftForm 0 1 = 7 / 144 := by
  obtain ⟨h01, _, _⟩ := kfourShiftForm_meeting_triple
  rw [pairMinorAt, kfourShiftForm_diag, kfourShiftForm_diag, h01]; norm_num

theorem kfourStar_pairMinor_eq' : pairMinorAt kfourShiftForm 0 2 = 7 / 144 := by
  obtain ⟨_, h02, _⟩ := kfourShiftForm_meeting_triple
  rw [pairMinorAt, kfourShiftForm_diag, kfourShiftForm_diag, h02]; norm_num

/-- The offset at the meeting triple is `1/48`. -/
theorem kfourStar_offset_eq : offsetAt kfourShiftForm 0 1 2 = 1 / 48 := by
  obtain ⟨h01, h02, h12⟩ := kfourShiftForm_meeting_triple
  rw [offsetAt, kfourShiftForm_diag, h01, h02, h12]; norm_num

/-- **THE GRAPHIC POINT SATISFIES THE OFFSET CRITERION.**  The squared offset is `9/20736`
and the minor product is `49/20736`, so the criterion holds with margin `5/2592`. -/
theorem kfourStar_offsetDominates :
    0 < kfourShiftForm 0 0 ∧ 0 < pairMinorAt kfourShiftForm 0 1 ∧
      offsetAt kfourShiftForm 0 1 2 ^ 2
        < pairMinorAt kfourShiftForm 0 1 * pairMinorAt kfourShiftForm 0 2 := by
  refine ⟨kfourStar_corner_pos, ?_, ?_⟩
  · rw [kfourStar_pairMinor_eq]; norm_num
  · rw [kfourStar_offset_eq, kfourStar_pairMinor_eq, kfourStar_pairMinor_eq']; norm_num

/-- The exact margin at the graphic point. -/
theorem kfourStar_offset_margin :
    pairMinorAt kfourShiftForm 0 1 * pairMinorAt kfourShiftForm 0 2
        - offsetAt kfourShiftForm 0 1 2 ^ 2 = 5 / 2592 := by
  rw [kfourStar_offset_eq, kfourStar_pairMinor_eq, kfourStar_pairMinor_eq']; norm_num

/-- **THE GRAPHIC POINT OF `K4` IS DISCHARGED.**  The block on the three pairwise meeting
edges is positive definite.  This is unconditional: no hypothesis, no design, no chart. -/
theorem kfourStar_posDef_tripleBlock : (tripleBlock kfourShiftForm 0 1 2).PosDef := by
  obtain ⟨hcorner, hminor, hsq⟩ := kfourStar_offsetDominates
  exact posDef_tripleBlock_of_offsetAt_sq_lt kfourShiftForm kfourShiftForm_transpose
    hcorner hminor hsq

/-- The landed gap at the meeting triple is exactly `5/4`, the largest gap the graphic point
carries. -/
theorem kfourStar_projGap_eq : projGapAt kfourEdgeProjection 0 1 2 = 5 / 4 := by
  have h01 : kfourEdgeProjection 0 1 = 1 / 4 := by
    rw [kfourEdgeProjection_apply, show kfourGramInt 0 1 = 1 from by decide]; norm_num
  have h02 : kfourEdgeProjection 0 2 = 1 / 4 := by
    rw [kfourEdgeProjection_apply, show kfourGramInt 0 2 = 1 from by decide]; norm_num
  have h12 : kfourEdgeProjection 1 2 = 1 / 4 := by
    rw [kfourEdgeProjection_apply, show kfourGramInt 1 2 = 1 from by decide]; norm_num
  rw [projGapAt_eq_shiftedMinor kfourEdgeProjection_symm 0 1 2,
    kfourEdgeProjection_diag, kfourEdgeProjection_diag, kfourEdgeProjection_diag,
    h01, h02, h12]
  norm_num

/-- **THE WHOLE RIGID STRATUM IS DISCHARGED.**  Any weighted design whose projection is the
graphic point of `K4`, at uniform weight, owns the selection the registry asks for.  The
pick is the three pairwise meeting edges, and the block is positive definite by the scalars
above.  No moment test and no pigeonhole is involved. -/
theorem exists_posDef_blockGapAt_of_kfour (design : WeightedDesign 6 3)
    (hpoint : projectionOfDesign design = kfourEdgeProjection)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      (blockGapAt (projectionOfDesign design) design.weight pick).PosDef := by
  have hshift : diagonalShiftForm design = kfourShiftForm := by
    rw [diagonalShiftForm, hpoint, kfourShiftForm]
    congr 1
    exact congrArg Matrix.diagonal (funext huniform)
  refine ⟨![0, 1, 2], injective_triplePick (by decide) (by decide) (by decide), ?_⟩
  rw [← tripleBlock_diagonalShift_eq_blockGapAt design (by decide : (0 : Fin 6) ≠ 1)
      (by decide : (2 : Fin 6) ≠ 0) (by decide : (2 : Fin 6) ≠ 1), hshift]
  exact kfourStar_posDef_tripleBlock

/-! ### 12. THE HINGE, FROM THREE SCALAR INEQUALITIES

The two frontier axioms of the registry read `IsTie design → HasParallelPair design`.  A tie
asks for TWO things: a dominating subset of the right size, and NO subset of that size whose
gap is positive definite.  A positive definite gap block therefore refutes the tie outright,
and the hinge implication holds vacuously at that design.

The landed bridge `Gtz.dominates_image_of_posDef_blockGapAt` carries a positive definite gap
block onto a positive definite subset gap, and it is SIZE-uniform at rank three.  So the
three scalar inequalities of section 5 produce the frontier's own conclusion at any size,
and the graphic point of `K4` produces it unconditionally. -/

/-- **A POSITIVE DEFINITE GAP BLOCK REFUTES THE TIE.**  A tie forbids every subset gap of
the right size from being positive definite, and the landed bridge exhibits one. -/
theorem not_isTie_of_posDef_blockGapAt {size : ℕ} (design : WeightedDesign size 3)
    {pick : Fin 3 → Fin size} (hinj : Function.Injective pick)
    (hposDef : (blockGapAt (projectionOfDesign design) design.weight pick).PosDef) :
    ¬ IsTie design := fun htie =>
  htie.2 (Finset.image pick Finset.univ) (card_image_pick hinj)
    (dominates_image_of_posDef_blockGapAt design hinj hposDef)

/-- **THE THREE INEQUALITIES REFUTE THE TIE.**  Size-uniform at rank three: a pivot of
positive excess, one positive pair minor, and one ordered partner pair whose squared offset
falls below the minor product. -/
theorem not_isTie_of_offsetDominatesAt {size : ℕ} (design : WeightedDesign size 3)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hthirdFirst : third ≠ first) (hthirdSecond : third ≠ second)
    (hexcess : 0 < diagonalShiftForm design first first)
    (hminor : 0 < pairMinorAt (diagonalShiftForm design) first second)
    (hsq : shiftOffsetAt design first second third ^ 2
      < pairMinorAt (diagonalShiftForm design) first second
        * pairMinorAt (diagonalShiftForm design) first third) :
    ¬ IsTie design := by
  refine not_isTie_of_posDef_blockGapAt design
    (injective_triplePick hfirstSecond hthirdFirst hthirdSecond) ?_
  rw [← tripleBlock_diagonalShift_eq_blockGapAt design hfirstSecond hthirdFirst hthirdSecond]
  exact posDef_tripleBlock_of_offsetAt_sq_lt (diagonalShiftForm design)
    (diagonalShiftForm_transpose design) hexcess hminor hsq

/-- **THE FRONTIER'S CONCLUSION, FROM THREE POLYNOMIAL INEQUALITIES.**  The registry's two
frontier axioms conclude `IsTie design → HasParallelPair design`.  At any size and rank
three the three scalar inequalities give that conclusion, vacuously, because they leave no
tie to hold. -/
theorem hasParallelPair_of_isTie_of_offsetDominatesAt {size : ℕ}
    (design : WeightedDesign size 3)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hthirdFirst : third ≠ first) (hthirdSecond : third ≠ second)
    (hexcess : 0 < diagonalShiftForm design first first)
    (hminor : 0 < pairMinorAt (diagonalShiftForm design) first second)
    (hsq : shiftOffsetAt design first second third ^ 2
      < pairMinorAt (diagonalShiftForm design) first second
        * pairMinorAt (diagonalShiftForm design) first third) :
    IsTie design → HasParallelPair design := fun htie =>
  absurd htie (not_isTie_of_offsetDominatesAt design hfirstSecond hthirdFirst hthirdSecond
    hexcess hminor hsq)

/-- **THE GRAPHIC POINT OF `K4` IS NOT A TIE.**  Unconditional, from the explicit block of
section 11. -/
theorem not_isTie_of_kfour (design : WeightedDesign 6 3)
    (hpoint : projectionOfDesign design = kfourEdgeProjection)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹) :
    ¬ IsTie design := by
  obtain ⟨pick, hinj, hposDef⟩ := exists_posDef_blockGapAt_of_kfour design hpoint huniform
  exact not_isTie_of_posDef_blockGapAt design hinj hposDef

/-- **THE FRONTIER'S CONCLUSION AT THE RIGID STRATUM.**  Every design carried by the graphic
point of `K4` at uniform weight satisfies the hinge implication, unconditionally. -/
theorem hasParallelPair_of_isTie_of_kfour (design : WeightedDesign 6 3)
    (hpoint : projectionOfDesign design = kfourEdgeProjection)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹) :
    IsTie design → HasParallelPair design := fun htie =>
  absurd htie (not_isTie_of_kfour design hpoint huniform)

/-! ### 12b. THE `(6,3)` FRONTIER, NARROWED TO ONE INEQUALITY

The door of section 5 asks for three scalar inequalities.  At `(6, 3)` and uniform weight
TWO of the three are free, unconditionally.

The excesses total `rank - 1 = 2` over six labels, so some label carries at least `1/3`.  At
such a label the landed row law reads the shifted pair minors as `4 * P a a / 3 - 13/36`,
which is at least `11/36` and so strictly positive, and a positive total owns a positive
member.  Every design therefore hands over a pivot and a partner with no hypothesis at all
(`Gtz.exists_pivot_pair_of_uniform`).

What remains of the whole rank-four rung is the THIRD inequality alone
(`Gtz.allFiveOnPath_of_offsetThirdInequality`): at that pivot and partner, one further
label whose squared offset falls below the product of the two minors. -/

/-- **SOME EXCESS REACHES A THIRD, UNCONDITIONALLY.**  The landed excess total is
`rank - 1 = 2`, and six excesses totalling `2` cannot all fall below `1/3`.  No weight
hypothesis enters. -/
theorem exists_excess_ge_third (design : WeightedDesign 6 3) :
    ∃ label : Fin 6, (1 : ℝ) / 3 ≤ diagonalShiftForm design label label := by
  by_contra hall
  push Not at hall
  have hlt : ∑ label : Fin 6, diagonalShiftForm design label label
      < ∑ _label : Fin 6, (1 : ℝ) / 3 :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun label _ => hall label
  rw [sum_diagonalShiftForm_diag design] at hlt
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  norm_num at hlt

/-- **THE PIVOT AND THE PARTNER ARE FREE.**  Every design at uniform weight owns a label of
excess at least `1/3` and a partner whose shifted pair minor is strictly positive.  Two of
the door's three inequalities therefore cost nothing. -/
theorem exists_pivot_pair_of_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ label : Fin 6, design.weight label = (6 : ℝ)⁻¹) :
    ∃ label partner : Fin 6, partner ≠ label ∧
      (1 : ℝ) / 3 ≤ diagonalShiftForm design label label ∧
      0 < pairMinorAt (diagonalShiftForm design) label partner := by
  classical
  obtain ⟨label, hexcess⟩ := exists_excess_ge_third design
  have hdiag : (1 : ℝ) / 2 ≤ projectionOfDesign design label label := by
    rw [diagonalShiftForm_diag, huniform] at hexcess; linarith
  have hrow : 0 < ∑ other ∈ univ.erase label,
      pairMinorAt (diagonalShiftForm design) label other := by
    rw [sum_pairMinorAt_diagonalShift_erase_uniform design huniform label]
    linarith
  obtain ⟨partner, hpartner, hpos⟩ := exists_pos_of_sum_pos _ _ hrow
  exact ⟨label, partner, Finset.ne_of_mem_erase hpartner, hexcess, hpos⟩

/-- **THE WHOLE RUNG IS ONE INEQUALITY.**  Every on-path obligation follows from the THIRD
inequality alone, asked at a pivot and partner that every design already carries.  The
corner minor and the two-by-two minor are discharged by
`Gtz.exists_pivot_pair_of_uniform`, so nothing else is left to assume. -/
theorem allFiveOnPath_of_offsetThirdInequality
    (huniform : ∀ design : WeightedDesign 6 3, ∀ label : Fin 6,
      design.weight label = (6 : ℝ)⁻¹)
    (hthird : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∀ label partner : Fin 6, partner ≠ label →
        (1 : ℝ) / 3 ≤ diagonalShiftForm design label label →
        0 < pairMinorAt (diagonalShiftForm design) label partner →
        ∃ third : Fin 6, third ≠ label ∧ third ≠ partner ∧
          shiftOffsetAt design label partner third ^ 2
            < pairMinorAt (diagonalShiftForm design) label partner
              * pairMinorAt (diagonalShiftForm design) label third) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  refine allFiveOnPath_of_offsetDominatesSomewhere fun design hprimitive => ?_
  obtain ⟨label, partner, hne, hexcess, hminor⟩ :=
    exists_pivot_pair_of_uniform design (huniform design)
  obtain ⟨third, hthirdLabel, hthirdPartner⟩ :=
    hthird design hprimitive label partner hne hexcess hminor
  exact ⟨label, partner, third, hne.symm, hthirdLabel, hthirdPartner.1,
    by linarith [hexcess], hminor, hthirdPartner.2⟩

/-! ### 13. THE FRONTIER PRODUCER, AT EVERY RANK AND EVERY SIZE

Everything above rank three rests on Sylvester at `Fin 3`, and Sylvester does not generalize
cheaply.  It does not have to.  Two landed facts are already rank-uniform:

* `Gtz.posDef_of_diagonallyDominant` at `Fin rank`, and
* `Gtz.posDef_subsetSum_iff_projectionBlockGap` at `(size, rank)`.

Chaining them gives a producer for the frontier's own conclusion at EVERY rank and EVERY
size, with no determinant, no Sylvester and no rank-three coincidence.  The criterion reads
entirely in campaign vocabulary: inside the chosen block, every excess beats the sum of the
absolute pairings in its own row.

That is the shape the two frontier axioms ask for.  `obligationSubThresholdBandHinge` and
`obligationThresholdCellHingeRankFourAndUp` both conclude `IsTie design → HasParallelPair
design`, and `Gtz.hasParallelPair_of_isTie_of_excessDominates` delivers exactly that
conclusion from one inequality per selected slot, uniformly in the rank. -/

/-- The gap block of a selection is symmetric, at any rank. -/
theorem projectionBlockGap_transpose (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) :
    (projectionBlockGap design selected hcard)ᵀ = projectionBlockGap design selected hcard := by
  rw [projectionBlockGap, Matrix.transpose_sub, Matrix.diagonal_transpose,
    Matrix.transpose_submatrix, projectionOfDesign_transpose]

/-- Off the diagonal the gap block is a plain projection pairing. -/
theorem projectionBlockGap_offDiag (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    {slot other : Fin rank} (hne : slot ≠ other) :
    projectionBlockGap design selected hcard slot other
      = projectionOfDesign design (selected.orderEmbOfFin hcard slot)
          (selected.orderEmbOfFin hcard other) := by
  rw [projectionBlockGap, Matrix.sub_apply, Matrix.submatrix_apply,
    Matrix.diagonal_apply_ne _ hne, sub_zero]

/-- **THE EXCESS DOMINANCE CRITERION.**  Inside the chosen block every excess beats the sum
of the absolute pairings in its own row.  One inequality per selected slot, no determinant,
no rank-three coincidence. -/
def ExcessDominatesBlock (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) : Prop :=
  ∀ slot : Fin rank,
    ∑ other ∈ Finset.univ.erase slot,
        |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
          (selected.orderEmbOfFin hcard other)|
      < projectionOfDesign design (selected.orderEmbOfFin hcard slot)
          (selected.orderEmbOfFin hcard slot)
        - design.weight (selected.orderEmbOfFin hcard slot)

/-- **EXCESS DOMINANCE MAKES THE GAP BLOCK POSITIVE DEFINITE, AT EVERY RANK.** -/
theorem posDef_projectionBlockGap_of_excessDominates (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hdominates : ExcessDominatesBlock design selected hcard) :
    (projectionBlockGap design selected hcard).PosDef := by
  classical
  refine posDef_of_diagonallyDominant _ (projectionBlockGap_transpose design selected hcard)
    fun slot => ?_
  have hrow : ∑ other ∈ Finset.univ.erase slot,
      |projectionBlockGap design selected hcard slot other|
      = ∑ other ∈ Finset.univ.erase slot,
          |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
            (selected.orderEmbOfFin hcard other)| :=
    Finset.sum_congr rfl fun other hother => by
      rw [projectionBlockGap_offDiag design selected hcard
        (Finset.ne_of_mem_erase hother).symm]
  rw [hrow, projectionBlockGap_diag]
  exact hdominates slot

/-- **THE SUBSET GAP IS POSITIVE DEFINITE, AT EVERY RANK.**  The landed bridge carries the
block onto the subset. -/
theorem posDef_subsetSum_of_excessDominates (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hdominates : ExcessDominatesBlock design selected hcard) :
    (subsetSum design selected - 1).PosDef :=
  (posDef_subsetSum_iff_projectionBlockGap design selected hcard).mpr
    (posDef_projectionBlockGap_of_excessDominates design selected hcard hdominates)

/-- **EXCESS DOMINANCE REFUTES THE TIE, AT EVERY RANK.**  A tie forbids every subset gap of
the right size from being positive definite. -/
theorem not_isTie_of_excessDominates (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hdominates : ExcessDominatesBlock design selected hcard) :
    ¬ IsTie design := fun htie =>
  htie.2 selected hcard (posDef_subsetSum_of_excessDominates design selected hcard hdominates)

/-- **THE FRONTIER PRODUCER.**  Both frontier axioms of the registry conclude
`IsTie design → HasParallelPair design`.  This theorem delivers that conclusion at EVERY
rank and EVERY size, from one inequality per selected slot.  It is the rank-uniform
currency the frontier's own attack notes call for, and it needs no Sylvester criterion, no
determinant and no rank-three coincidence. -/
theorem hasParallelPair_of_isTie_of_excessDominates (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hdominates : ExcessDominatesBlock design selected hcard) :
    IsTie design → HasParallelPair design := fun htie =>
  absurd htie (not_isTie_of_excessDominates design selected hcard hdominates)

/-- **THE SUB-THRESHOLD BAND HINGE, ON THE DOMINATED STRATUM.**  The registry's first
frontier axiom quantifies over every rank at least three and every size in the band.  On the
stratum where some selection is excess dominated, its conclusion is a theorem. -/
theorem obligationSubThresholdBandHinge_of_excessDominates
    (hdominated : ∀ rank : ℕ, 3 ≤ rank → ∀ size : ℕ, 2 * rank ≤ size →
      size < rank * (rank + 1) / 2 → ∀ design : WeightedDesign size rank,
        ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
          ExcessDominatesBlock design selected hcard) :
    ∀ rank : ℕ, 3 ≤ rank → ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
      GtzWeighted (size - 1) rank →
        ∀ design : WeightedDesign size rank, IsTie design → HasParallelPair design := by
  intro rank hrank size hlow hhigh _ design
  obtain ⟨selected, hcard, hdom⟩ := hdominated rank hrank size hlow hhigh design
  exact hasParallelPair_of_isTie_of_excessDominates design selected hcard hdom

/-- The gap block along an ordered selection IS the landed selection gap block. -/
theorem blockGapAt_eq_projectionBlockGap (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hcard : selected.card = 3) :
    blockGapAt (projectionOfDesign design) design.weight
        ((selected.orderEmbOfFin hcard : Fin 3 ↪o Fin size) : Fin 3 → Fin size)
      = projectionBlockGap design selected hcard := rfl

/-- **A SEVENTH ENTRANCE TO THE REGISTRY, FROM ONE INEQUALITY PER SLOT.**  Excess dominance
at `(6, 3)` reaches every on-path obligation, the first of them included.  It is the only
entrance in this file whose hypothesis mentions neither a determinant nor an offset, and it
is the same criterion that produces the frontier conclusion at every rank. -/
theorem allFiveOnPath_of_excessDominates
    (hdominated : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
        ExcessDominatesBlock design selected hcard) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  refine allFiveOnPath_of_blockGapAt fun design hprimitive => ?_
  obtain ⟨selected, hcard, hdom⟩ := hdominated design hprimitive
  refine ⟨((selected.orderEmbOfFin hcard : Fin 3 ↪o Fin 6) : Fin 3 → Fin 6),
    (selected.orderEmbOfFin hcard).injective, ?_⟩
  rw [blockGapAt_eq_projectionBlockGap]
  exact posDef_projectionBlockGap_of_excessDominates design selected hcard hdom

/-! #### Scaled dominance, strictly weaker to ask for

Plain dominance forces EVERY excess to beat its own row.  A design can fail that on one slot
and still be far from a tie, because a congruence by a positive diagonal rescales the rows
and the columns at once and leaves definiteness alone.  Choosing the scale is free, so the
criterion below is strictly weaker to satisfy and produces the same conclusion. -/

/-- **SCALED DOMINANCE IMPLIES POSITIVE DEFINITENESS, AT EVERY RANK.**  Congruence by a
positive diagonal is definiteness preserving, and it turns the scaled test into the plain
one. -/
theorem posDef_of_scaledDominant {order : ℕ} (mat : Matrix (Fin order) (Fin order) ℝ)
    (hsymmetric : matᵀ = mat) (scale : Fin order → ℝ) (hscale : ∀ slot, 0 < scale slot)
    (hdominates : ∀ slot : Fin order,
      ∑ other ∈ Finset.univ.erase slot, scale other * |mat slot other|
        < scale slot * mat slot slot) :
    mat.PosDef := by
  classical
  have hentry : ∀ leftSlot rightSlot : Fin order,
      ((Matrix.diagonal scale)ᵀ * mat * Matrix.diagonal scale) leftSlot rightSlot
        = scale leftSlot * mat leftSlot rightSlot * scale rightSlot := by
    intro leftSlot rightSlot
    simp [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hunit : IsUnit (Matrix.diagonal scale).det := by
    rw [Matrix.det_diagonal]
    exact (isUnit_iff_ne_zero).mpr (ne_of_gt (Finset.prod_pos fun slot _ => hscale slot))
  refine (posDef_congruence_iff hunit).mp ?_
  refine posDef_of_diagonallyDominant _ ?_ fun slot => ?_
  · ext leftSlot rightSlot
    rw [Matrix.transpose_apply, hentry, hentry,
      show mat rightSlot leftSlot = mat leftSlot rightSlot from
        form_flip_of_transpose hsymmetric leftSlot rightSlot]
    ring
  · have hrow : ∑ other ∈ Finset.univ.erase slot,
        |((Matrix.diagonal scale)ᵀ * mat * Matrix.diagonal scale) slot other|
        = scale slot * ∑ other ∈ Finset.univ.erase slot, scale other * |mat slot other| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun other _ => ?_
      rw [hentry, abs_mul, abs_mul, abs_of_pos (hscale slot), abs_of_pos (hscale other)]
      ring
    rw [hrow, hentry]
    have hpivot := hscale slot
    nlinarith [hdominates slot]

/-- **THE SCALED EXCESS DOMINANCE CRITERION.**  A positive scale on the selected slots, and
inside the chosen block every scaled excess beats the scaled row of absolute pairings. -/
def ScaledExcessDominatesBlock (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (scale : Fin rank → ℝ) : Prop :=
  (∀ slot : Fin rank, 0 < scale slot) ∧
  ∀ slot : Fin rank,
    ∑ other ∈ Finset.univ.erase slot,
        scale other * |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
          (selected.orderEmbOfFin hcard other)|
      < scale slot * (projectionOfDesign design (selected.orderEmbOfFin hcard slot)
            (selected.orderEmbOfFin hcard slot)
          - design.weight (selected.orderEmbOfFin hcard slot))

/-- Plain dominance is the scaled criterion at the constant scale one. -/
theorem scaledExcessDominatesBlock_of_excessDominates (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hdominates : ExcessDominatesBlock design selected hcard) :
    ScaledExcessDominatesBlock design selected hcard (fun _ => 1) := by
  refine ⟨fun _ => one_pos, fun slot => ?_⟩
  have hrow := hdominates slot
  simpa using hrow

/-- **SCALED DOMINANCE MAKES THE GAP BLOCK POSITIVE DEFINITE, AT EVERY RANK.** -/
theorem posDef_projectionBlockGap_of_scaledExcessDominates (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) (scale : Fin rank → ℝ)
    (hdominates : ScaledExcessDominatesBlock design selected hcard scale) :
    (projectionBlockGap design selected hcard).PosDef := by
  classical
  obtain ⟨hscale, hrows⟩ := hdominates
  refine posDef_of_scaledDominant _ (projectionBlockGap_transpose design selected hcard)
    scale hscale fun slot => ?_
  have hrow : ∑ other ∈ Finset.univ.erase slot,
      scale other * |projectionBlockGap design selected hcard slot other|
      = ∑ other ∈ Finset.univ.erase slot,
          scale other * |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
            (selected.orderEmbOfFin hcard other)| :=
    Finset.sum_congr rfl fun other hother => by
      rw [projectionBlockGap_offDiag design selected hcard
        (Finset.ne_of_mem_erase hother).symm]
  rw [hrow, projectionBlockGap_diag]
  exact hrows slot

/-- **SCALED DOMINANCE REFUTES THE TIE, AT EVERY RANK.** -/
theorem not_isTie_of_scaledExcessDominates (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) (scale : Fin rank → ℝ)
    (hdominates : ScaledExcessDominatesBlock design selected hcard scale) :
    ¬ IsTie design := fun htie =>
  htie.2 selected hcard
    ((posDef_subsetSum_iff_projectionBlockGap design selected hcard).mpr
      (posDef_projectionBlockGap_of_scaledExcessDominates design selected hcard scale hdominates))

/-- **THE FRONTIER PRODUCER, IN ITS WEAKEST FORM.**  Same conclusion as
`Gtz.hasParallelPair_of_isTie_of_excessDominates`, from a strictly weaker hypothesis: the
scale is free to choose. -/
theorem hasParallelPair_of_isTie_of_scaledExcessDominates (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) (scale : Fin rank → ℝ)
    (hdominates : ScaledExcessDominatesBlock design selected hcard scale) :
    IsTie design → HasParallelPair design := fun htie =>
  absurd htie (not_isTie_of_scaledExcessDominates design selected hcard scale hdominates)

/-- **THE SEVENTH ENTRANCE, IN ITS WEAKEST FORM.**  Scaled dominance at `(6, 3)` reaches
every on-path obligation. -/
theorem allFiveOnPath_of_scaledExcessDominates
    (hdominated : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3, ∃ scale : Fin 3 → ℝ,
        ScaledExcessDominatesBlock design selected hcard scale) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  refine allFiveOnPath_of_blockGapAt fun design hprimitive => ?_
  obtain ⟨selected, hcard, scale, hdom⟩ := hdominated design hprimitive
  refine ⟨((selected.orderEmbOfFin hcard : Fin 3 ↪o Fin 6) : Fin 3 → Fin 6),
    (selected.orderEmbOfFin hcard).injective, ?_⟩
  rw [blockGapAt_eq_projectionBlockGap]
  exact posDef_projectionBlockGap_of_scaledExcessDominates design selected hcard scale hdom

/-! #### The comparison matrix: the sharpest form, and the cheapest

Both dominance criteria are shadows of one statement.  Replace every off-diagonal entry of
the gap block by MINUS its absolute value and keep the diagonal.  The quadratic form of the
original is at least the quadratic form of that comparison matrix read at the absolute
values of the probe, entry by entry, because a term can only help when its sign already
agrees.  So positive definiteness of the comparison matrix implies positive definiteness of
the block.

The comparison matrix is where the scale went.  A positive scale making the block dominant
exists exactly when the comparison matrix is positive definite, so this criterion subsumes
both earlier ones and needs no scale exhibited.  At `Fin 3` it is three leading minors of an
explicit rational matrix.

Measured on 1000 exact designs across five cells — `(6,3)`, `(8,4)`, `(10,4)`, `(12,4)` and
`(15,5)` — some selection passes it at 999 of them.  Plain dominance passes at 750. -/

/-- The **comparison matrix**: the diagonal kept, every off-diagonal entry replaced by minus
its absolute value. -/
def comparisonMatrix {order : ℕ} (mat : Matrix (Fin order) (Fin order) ℝ) :
    Matrix (Fin order) (Fin order) ℝ :=
  Matrix.of fun leftSlot rightSlot =>
    if leftSlot = rightSlot then mat leftSlot leftSlot else -|mat leftSlot rightSlot|

theorem comparisonMatrix_apply_diag {order : ℕ} (mat : Matrix (Fin order) (Fin order) ℝ)
    (slot : Fin order) : comparisonMatrix mat slot slot = mat slot slot := by
  simp [comparisonMatrix]

theorem comparisonMatrix_apply_offDiag {order : ℕ} (mat : Matrix (Fin order) (Fin order) ℝ)
    {leftSlot rightSlot : Fin order} (hne : leftSlot ≠ rightSlot) :
    comparisonMatrix mat leftSlot rightSlot = -|mat leftSlot rightSlot| := by
  simp [comparisonMatrix, hne]

/-- The quadratic form of a matrix, as a plain double sum. -/
theorem dotProduct_mulVec_eq_double_sum {order : ℕ} (mat : Matrix (Fin order) (Fin order) ℝ)
    (probe : Fin order → ℝ) :
    probe ⬝ᵥ (mat *ᵥ probe) = ∑ leftSlot, ∑ rightSlot,
      mat leftSlot rightSlot * probe leftSlot * probe rightSlot := by
  rw [dotProduct]
  refine Finset.sum_congr rfl fun leftSlot _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun rightSlot _ => by ring

/-- **THE COMPARISON CRITERION, AT EVERY ORDER.**  A symmetric matrix whose comparison
matrix is positive definite is itself positive definite.  Each term of the quadratic form is
at least the matching term of the comparison form read at the absolute values, so the whole
form is. -/
theorem posDef_of_posDef_comparisonMatrix {order : ℕ} (mat : Matrix (Fin order) (Fin order) ℝ)
    (hsymmetric : matᵀ = mat) (hcomparison : (comparisonMatrix mat).PosDef) :
    mat.PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymmetric, fun probe hprobe => ?_⟩
  rw [star_trivial]
  have habsNe : (fun slot => |probe slot|) ≠ 0 := by
    intro hzero
    refine hprobe (funext fun slot => ?_)
    have hslot := congrFun hzero slot
    simpa using abs_eq_zero.mp hslot
  have hcomp := (Matrix.posDef_iff_dotProduct_mulVec.mp hcomparison).2 habsNe
  rw [star_trivial, dotProduct_mulVec_eq_double_sum] at hcomp
  rw [dotProduct_mulVec_eq_double_sum]
  refine lt_of_lt_of_le hcomp (Finset.sum_le_sum fun leftSlot _ => ?_)
  refine Finset.sum_le_sum fun rightSlot _ => ?_
  by_cases hslots : leftSlot = rightSlot
  · subst hslots
    have habs : |probe leftSlot| * |probe leftSlot| = probe leftSlot * probe leftSlot := by
      rw [← abs_mul, abs_mul_self]
    rw [comparisonMatrix_apply_diag, mul_assoc, mul_assoc, habs]
  · rw [comparisonMatrix_apply_offDiag mat hslots]
    have hbound : -(|mat leftSlot rightSlot| * |probe leftSlot| * |probe rightSlot|)
        ≤ mat leftSlot rightSlot * probe leftSlot * probe rightSlot := by
      have habs : |mat leftSlot rightSlot * probe leftSlot * probe rightSlot|
          = |mat leftSlot rightSlot| * |probe leftSlot| * |probe rightSlot| := by
        rw [abs_mul, abs_mul]
      have := neg_abs_le (mat leftSlot rightSlot * probe leftSlot * probe rightSlot)
      rwa [habs] at this
    nlinarith [hbound]

/-- Plain dominance passes the comparison test, so the comparison criterion subsumes it. -/
theorem posDef_comparisonMatrix_of_dominant {order : ℕ}
    (mat : Matrix (Fin order) (Fin order) ℝ) (hsymmetric : matᵀ = mat)
    (hdominates : ∀ slot : Fin order,
      ∑ other ∈ Finset.univ.erase slot, |mat slot other| < mat slot slot) :
    (comparisonMatrix mat).PosDef := by
  classical
  refine posDef_of_diagonallyDominant _ ?_ fun slot => ?_
  · ext leftSlot rightSlot
    rw [Matrix.transpose_apply]
    by_cases hslots : leftSlot = rightSlot
    · subst hslots; rfl
    · rw [comparisonMatrix_apply_offDiag mat (Ne.symm hslots),
        comparisonMatrix_apply_offDiag mat hslots,
        form_flip_of_transpose hsymmetric leftSlot rightSlot]
  · have hrow : ∑ other ∈ Finset.univ.erase slot, |comparisonMatrix mat slot other|
        = ∑ other ∈ Finset.univ.erase slot, |mat slot other| :=
      Finset.sum_congr rfl fun other hother => by
        rw [comparisonMatrix_apply_offDiag mat (Finset.ne_of_mem_erase hother).symm,
          abs_neg, abs_abs]
    rw [hrow, comparisonMatrix_apply_diag]
    exact hdominates slot

/-- **THE COMPARISON DOOR, AT EVERY RANK AND EVERY SIZE.**  The sharpest criterion of this
file, and the cheapest to check: three leading minors of an explicit rational matrix at rank
three. -/
theorem posDef_projectionBlockGap_of_comparison (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hcomparison : (comparisonMatrix (projectionBlockGap design selected hcard)).PosDef) :
    (projectionBlockGap design selected hcard).PosDef :=
  posDef_of_posDef_comparisonMatrix _ (projectionBlockGap_transpose design selected hcard)
    hcomparison

/-- **THE COMPARISON CRITERION REFUTES THE TIE, AT EVERY RANK.** -/
theorem not_isTie_of_comparison (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hcomparison : (comparisonMatrix (projectionBlockGap design selected hcard)).PosDef) :
    ¬ IsTie design := fun htie =>
  htie.2 selected hcard
    ((posDef_subsetSum_iff_projectionBlockGap design selected hcard).mpr
      (posDef_projectionBlockGap_of_comparison design selected hcard hcomparison))

/-- **THE FRONTIER PRODUCER, IN ITS SHARPEST FORM.** -/
theorem hasParallelPair_of_isTie_of_comparison (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hcomparison : (comparisonMatrix (projectionBlockGap design selected hcard)).PosDef) :
    IsTie design → HasParallelPair design := fun htie =>
  absurd htie (not_isTie_of_comparison design selected hcard hcomparison)

/-- **AN EIGHTH ENTRANCE TO THE REGISTRY.**  At `(6, 3)` the comparison criterion reaches
every on-path obligation, and it is the weakest hypothesis in this file. -/
theorem allFiveOnPath_of_comparison
    (hcomparison : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
        (comparisonMatrix (projectionBlockGap design selected hcard)).PosDef) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  refine allFiveOnPath_of_blockGapAt fun design hprimitive => ?_
  obtain ⟨selected, hcard, hcomp⟩ := hcomparison design hprimitive
  refine ⟨((selected.orderEmbOfFin hcard : Fin 3 ↪o Fin 6) : Fin 3 → Fin 6),
    (selected.orderEmbOfFin hcard).injective, ?_⟩
  rw [blockGapAt_eq_projectionBlockGap]
  exact posDef_projectionBlockGap_of_comparison design selected hcard hcomp

/-- **THE THRESHOLD-CELL HINGE AT RANK FOUR AND UP, ON THE DOMINATED STRATUM.**  The
registry's second frontier axiom, with its conclusion produced the same way. -/
theorem obligationThresholdCellHingeRankFourAndUp_of_excessDominates
    (hdominated : ∀ rank : ℕ, 4 ≤ rank →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
        ∃ selected : Finset (Fin (rank * (rank + 1) / 2)), ∃ hcard : selected.card = rank,
          ExcessDominatesBlock design selected hcard) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
        IsTie design → HasParallelPair design := by
  intro rank hrank _ design
  obtain ⟨selected, hcard, hdom⟩ := hdominated rank hrank design
  exact hasParallelPair_of_isTie_of_excessDominates design selected hcard hdom

end Gtz
