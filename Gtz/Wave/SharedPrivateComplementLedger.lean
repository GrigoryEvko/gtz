import Gtz.Wave.SharedPrivateCircuitSaturation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The complement ledger — the cover budget at every family size, the
dominated corner budget, and the off-block leak law

The two-set cover kill prices a partition of the atoms by two rank-one
shifted gap blocks.  This module measures how far that ledger reaches,
supplies the two budgets that go beyond a rank-one block, and reads the
energy that a rank-one block sends to its complement.

## The ledger

A family of rank-one shifted gap sets whose union is every atom pays one
unit for each member, thus `rank - 1 - size * value ≤ card family`.  At a
shared-private datum the total is `2 - 6 * value` and the value is
negative, thus **EVERY such family has at least three members**.  Two
members are refused, three members reproduce the known window bound
`value ≥ -1/6` and nothing more.  The ledger is exhausted at three.

That measurement retires a named target.  A rank-one shifted gap block on
the complement of the shared triple would give a two-member family, thus
the datum REFUSES it: `not_gapBlockRankOne_complement_of_identical_support`
is a theorem, not an open obligation.  The complement of a paying triple
carries a shifted gap sum of more than one unit, and a rank-one block
never carries more than one.

## The dominated corner budget

The rank-one law is not necessary for a budget.  The corner column of a
block, divided by the captured defect, is an extremal probe whenever the
block form DOMINATES the square of the corner reading.  Then the corner
row energy obeys `Σ (gap U y)^2 / (1 - d y) ≤ gap U U - value`.  A
rank-one block satisfies the domination with equality, thus the set
budget is the special case.

## The off-block leak

The row energy of a chart row splits at a rank-one block.  Inside the
block every square is a product of shifted diagonals, thus the energy
that the row sends OUT of the block is exact:

  `Σ_{z ∉ S} P y z ^ 2 = A y y * (1 - 2 * d y - σ) + d y * (1 - d y)`

with `σ` the shifted gap sum of the block.  The left side is a sum of
squares, thus `A y y * (σ + 2 * d y - 1) ≤ d y * (1 - d y)`.  At an atom
of zero capture that reads `σ ≤ 1` — the budget again, with no
contraction.

## The tight leak

The same split holds for a tight direction, with no rank-one law.  The
chart acts on a tight direction as the captured diagonal inside the
block, thus the direction's image has energy `Σ d y * v y ^ 2` and its
leak out of the block is `Σ d y * (1 - d y) * v y ^ 2`.  A block of zero
capture therefore annihilates its own tight direction.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.sum_union_le_of_nonneg`, `Gtz.shiftedGapDiag_sum_biUnion_le` — the
  cover arithmetic.
* `Gtz.rank_le_card_of_shiftedGap_rankOne_cover` — **THE COVER LEDGER AT
  EVERY FAMILY SIZE.**
* `Gtz.SharedPrivateData.three_le_card_of_shiftedGap_rankOne_cover` —
  **THE LEDGER IS EXHAUSTED AT THREE.**
* `Gtz.SharedPrivateData.not_gapSet_rankOne_of_complement` — a paying set
  and its complement never both pay.
* `Gtz.SharedPrivateData.identical_support_complement_sum`,
  `Gtz.SharedPrivateData.not_gapBlockRankOne_complement_of_identical_support`
  — **THE COMPLEMENT OF THE SHARED TRIPLE IS NEVER RANK ONE.**
* `Gtz.shiftedGap_set_form_le` — the shifted gap form at a set probe.
* `Gtz.gapCorner_saturation`, `Gtz.gapCorner_row_energy_le` — **THE
  DOMINATED CORNER BUDGET.**
* `Gtz.gapCorner_dominates_of_rankOne` — a rank-one block dominates with
  equality.
* `Gtz.gapSet_offDiag_sq` — every off-diagonal square of a rank-one block
  is a product of shifted diagonals.
* `Gtz.gapSet_offSet_energy` — **THE OFF-BLOCK LEAK LAW.**
* `Gtz.gapSet_leak_floor`, `Gtz.gapSet_sum_le_one_of_zero_capture` — the
  leak floor and the contraction-free budget.
* `Gtz.chart_mulVec_tightDir_apply`, `Gtz.chart_tightDir_energy`,
  `Gtz.chart_tightDir_offBlock_leak` — **THE TIGHT LEAK IDENTITY.**
* `Gtz.chart_mulVec_tightDir_eq_zero_of_zero_capture` — a block of zero
  capture annihilates its tight direction.
* `Gtz.SharedPrivateData.identical_support_leak_floor` — the leak floor at
  the shared triple.
* `Gtz.SharedPrivateCircuitPairIdenticalLedgerClosed` — the re-cut
  identical residue, with the complement floor and the three leak floors
  paid.
* `Gtz.sharedPrivateCircuitPairIdenticalClosed_of_ledger`,
  `Gtz.sharedPrivateExtrasClosed_of_ledger_lattice`,
  `Gtz.sharedPrivateKilled_of_ledger_lattice`,
  `Gtz.rankFourSharedPrivateClosed_of_ledger_lattice`,
  `Gtz.rankFiveSharedPrivateClosed_of_ledger_lattice`,
  `Gtz.rankSixSharedPrivateClosed_of_ledger_lattice` — **CLOSURE TWO ON
  THE RE-CUT LATTICE.**

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no such datum exists if `Gtz.GtzWeighted 6 3`
holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the cover arithmetic -/

section CoverArithmetic

variable {size : ℕ}

/-- A union pays no more than the two parts, when the summand is
nonnegative. -/
theorem sum_union_le_of_nonneg {summand : Fin size → ℝ}
    (hnonneg : ∀ atomIndex : Fin size, 0 ≤ summand atomIndex)
    (setOne setTwo : Finset (Fin size)) :
    ∑ atomIndex ∈ setOne ∪ setTwo, summand atomIndex
      ≤ (∑ atomIndex ∈ setOne, summand atomIndex)
        + ∑ atomIndex ∈ setTwo, summand atomIndex := by
  classical
  have hsplit : ∑ atomIndex ∈ setOne ∪ setTwo, summand atomIndex
      = (∑ atomIndex ∈ setOne, summand atomIndex)
        + ∑ atomIndex ∈ setTwo \ setOne, summand atomIndex := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
  have hrest : ∑ atomIndex ∈ setTwo \ setOne, summand atomIndex
      ≤ ∑ atomIndex ∈ setTwo, summand atomIndex :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun atomIndex _ _ => hnonneg atomIndex)
  rw [hsplit]; linarith

/-- **THE COVER ARITHMETIC.**  A nonnegative summand over an indexed union
never exceeds the sum of the summands over the parts. -/
theorem shiftedGapDiag_sum_biUnion_le {summand : Fin size → ℝ}
    (hnonneg : ∀ atomIndex : Fin size, 0 ≤ summand atomIndex)
    {familyIndex : Type} [DecidableEq familyIndex]
    (coverSet : familyIndex → Finset (Fin size)) (family : Finset familyIndex) :
    ∑ atomIndex ∈ family.biUnion coverSet, summand atomIndex
      ≤ ∑ memberIndex ∈ family, ∑ atomIndex ∈ coverSet memberIndex, summand atomIndex := by
  classical
  induction family using Finset.induction_on with
  | empty => simp
  | insert memberIndex restFamily hnotMem ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hnotMem]
      refine le_trans (sum_union_le_of_nonneg hnonneg _ _) ?_
      linarith [ih]

end CoverArithmetic

/-! ## Layer 2 — the cover ledger at every family size -/

section CoverLedger

variable {size rank : ℕ} {activeIndex : Type}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE COVER LEDGER.**  A family of rank-one shifted gap sets whose
union is every atom pays one unit for each member.  The shifted gap total
is `rank - 1 - size * value`, thus the family cardinality bounds it. -/
theorem rank_le_card_of_shiftedGap_rankOne_cover
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {familyIndex : Type} [DecidableEq familyIndex] {family : Finset familyIndex}
    {coverSet : familyIndex → Finset (Fin size)} {corner : familyIndex → Fin size}
    (hcover : family.biUnion coverSet = Finset.univ)
    (hcorner : ∀ memberIndex ∈ family, corner memberIndex ∈ coverSet memberIndex)
    (hpos : ∀ atomIndex : Fin size,
      0 < shiftedGapDiag projection weight value atomIndex)
    (hrankOne : ∀ memberIndex ∈ family, ∀ rowIndex ∈ coverSet memberIndex,
      ∀ colIndex ∈ coverSet memberIndex,
      shiftedGap projection weight value rowIndex colIndex
          * shiftedGapDiag projection weight value (corner memberIndex)
        = shiftedGap projection weight value (corner memberIndex) rowIndex
          * shiftedGap projection weight value (corner memberIndex) colIndex)
    (hvalue : value < 0) :
    (rank : ℝ) - 1 - (size : ℝ) * value ≤ (family.card : ℝ) := by
  classical
  have hfloor : ∀ atomIndex : Fin size, 0 ≤ value + weight atomIndex :=
    fun atomIndex => capture_diagonal_nonneg_of_isChartStationaryData hdata atomIndex
  have hcap : ∀ atomIndex : Fin size, value + weight atomIndex < 1 :=
    fun atomIndex => capture_diagonal_lt_one_of_negative_value hdata hvalue atomIndex
  have hpiece : ∀ memberIndex ∈ family,
      ∑ atomIndex ∈ coverSet memberIndex,
        shiftedGapDiag projection weight value atomIndex ≤ 1 := by
    intro memberIndex hmem
    exact gapSet_shifted_sum_le_one hdata.isSymmetric hdata.isIdempotent
      (hcorner memberIndex hmem) (fun atomIndex _ => hfloor atomIndex)
      (fun atomIndex _ => hcap atomIndex) (fun atomIndex _ => hpos atomIndex)
      (hrankOne memberIndex hmem)
  have hunion := shiftedGapDiag_sum_biUnion_le
    (summand := fun atomIndex => shiftedGapDiag projection weight value atomIndex)
    (fun atomIndex => le_of_lt (hpos atomIndex)) coverSet family
  rw [hcover] at hunion
  have htotal := shiftedGapDiag_sum_eq hdata
  rw [htotal] at hunion
  have hcount : ∑ memberIndex ∈ family,
      ∑ atomIndex ∈ coverSet memberIndex,
        shiftedGapDiag projection weight value atomIndex ≤ (family.card : ℝ) := by
    refine le_trans (Finset.sum_le_sum hpiece) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

end CoverLedger

/-! ## Layer 3 — the ledger at the datum, and the retirement of the
complement target -/

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-- **THE LEDGER IS EXHAUSTED AT THREE.**  Every family of rank-one
shifted gap sets that covers the six atoms of a shared-private datum has
at least three members.  Two members are refused outright, and three
members reproduce the window bound and nothing more. -/
theorem three_le_card_of_shiftedGap_rankOne_cover (data : SharedPrivateData crux)
    {familyIndex : Type} [DecidableEq familyIndex] {family : Finset familyIndex}
    {coverSet : familyIndex → Finset (Fin 6)} {corner : familyIndex → Fin 6}
    (hcover : family.biUnion coverSet = Finset.univ)
    (hcorner : ∀ memberIndex ∈ family, corner memberIndex ∈ coverSet memberIndex)
    (hrankOne : ∀ memberIndex ∈ family, ∀ rowIndex ∈ coverSet memberIndex,
      ∀ colIndex ∈ coverSet memberIndex,
      shiftedGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) rowIndex colIndex
          * shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) (corner memberIndex)
        = shiftedGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) (corner memberIndex) rowIndex
          * shiftedGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design))
            (corner memberIndex) colIndex) :
    3 ≤ family.card := by
  have hbound := rank_le_card_of_shiftedGap_rankOne_cover data.hdata hcover hcorner
    (fun atomIndex => data.shiftedGapDiag_pos atomIndex) hrankOne data.hvalueNeg
  have hvalue := data.hvalueNeg
  norm_num at hbound
  have hcast : (2 : ℝ) < (family.card : ℝ) := by linarith
  have hnat : 2 < family.card := by exact_mod_cast hcast
  omega

/-- **THE COMPLEMENT OF THE SHARED TRIPLE IS NEVER RANK ONE.**  The shared
triple of an identical-support pair already pays one unit.  A rank-one
shifted gap block on the other three atoms would make a two-member cover,
and the ledger refuses two members.  Thus the named complement target is
a THEOREM against the branch, not an open obligation for it. -/
theorem not_gapBlockRankOne_complement_of_identical_support
    (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS atomP atomQ atomR : Fin 6}
    (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS) (hVS : atomV ≠ atomS)
    (hPQ : atomP ≠ atomQ) (hPR : atomP ≠ atomR) (hQR : atomQ ≠ atomR)
    (hcover : ({atomU, atomV, atomS} : Finset (Fin 6)) ∪ {atomP, atomQ, atomR}
      = Finset.univ)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS}) :
    ¬ GapBlockRankOne (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) atomP atomQ atomR :=
  fun hcomplement =>
    data.false_of_identical_support_complement_rankOne hne hUV hUS hVS hPQ hPR hQR
      hcover hsupportOne hsupportTwo hcomplement

/-- **THE COMPLEMENT FLOOR.**  The shifted gap total of the six atoms is
`2 - 6 * value` and the shared triple pays at most one, thus the other
three atoms carry more than one unit.  A rank-one block never carries
more than one, which is the ledger reading of the previous theorem. -/
theorem identical_support_complement_sum (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS}) :
    1 - 6 * chartObjective (chartPointOfDesign crux.design)
      ≤ ∑ atomIndex ∈ Finset.univ \ ({atomU, atomV, atomS} : Finset (Fin 6)),
          shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomIndex := by
  classical
  have htriple : ∑ atomIndex ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
      shiftedGapDiag (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomIndex
      = shiftedGapDiag (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomU
        + shiftedGapDiag (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomV
        + shiftedGapDiag (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomS := by
    rw [Finset.sum_insert (by simp [hUV, hUS]), Finset.sum_insert (by simp [hVS]),
      Finset.sum_singleton, add_assoc]
  have hbudget := data.identical_support_shifted_sum_le_one hne hUV hUS hVS
    hsupportOne hsupportTwo
  have hsplit := Finset.sum_sdiff (f := fun atomIndex =>
      shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomIndex)
    (Finset.subset_univ ({atomU, atomV, atomS} : Finset (Fin 6)))
  have htotal := data.shiftedGapDiag_sum
  rw [htriple] at hsplit
  rw [← hsplit] at htotal
  linarith

end SharedPrivateData

/-! ## Layer 4 — the shifted gap form and the dominated corner budget -/

section CornerBudget

variable {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}

/-- **THE SHIFTED GAP FORM AT A SET PROBE.**  The chart contraction, read
through the gap dictionary: the shifted gap form of a probe supported on a
set never exceeds the defect-weighted energy of that probe. -/
theorem shiftedGap_set_form_le (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) (setS : Finset (Fin size))
    (val : Fin size → ℝ) :
    ∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
        shiftedGap projection weight value rowIndex colIndex
          * (val rowIndex * val colIndex)
      ≤ ∑ atomIndex ∈ setS,
          (1 - (value + weight atomIndex)) * (val atomIndex * val atomIndex) := by
  classical
  have hcontract := projection_set_contraction hsymm hidem setS val
  have hsplit : ∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
        projection rowIndex colIndex * (val rowIndex * val colIndex)
      = (∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
          shiftedGap projection weight value rowIndex colIndex
            * (val rowIndex * val colIndex))
        + ∑ atomIndex ∈ setS,
          (value + weight atomIndex) * (val atomIndex * val atomIndex) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun rowIndex hrow => ?_
    have hterm : ∀ colIndex ∈ setS,
        projection rowIndex colIndex * (val rowIndex * val colIndex)
        = shiftedGap projection weight value rowIndex colIndex
            * (val rowIndex * val colIndex)
          + (if rowIndex = colIndex then value + weight rowIndex else 0)
            * (val rowIndex * val colIndex) := by
      intro colIndex _
      rw [projection_eq_shiftedGap_add (projection := projection) (weight := weight)
        (value := value) rowIndex colIndex]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single rowIndex
      (fun colIndex _ hne => by rw [if_neg (Ne.symm hne), zero_mul])
      (fun hnot => absurd hrow hnot), if_pos rfl]
  rw [hsplit] at hcontract
  have hdefect : ∑ atomIndex ∈ setS, val atomIndex * val atomIndex
      - ∑ atomIndex ∈ setS, (value + weight atomIndex) * (val atomIndex * val atomIndex)
      = ∑ atomIndex ∈ setS,
        (1 - (value + weight atomIndex)) * (val atomIndex * val atomIndex) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  linarith [hcontract, hdefect.symm.le, hdefect.le]

/-- **THE DOMINATED CORNER BUDGET.**  If the shifted gap form of a set
dominates the square of the corner reading, then the corner row energy,
weighted by the captured defect, never exceeds the corner itself.

The extremal probe is the corner column divided by the defect.  At that
probe the corner reading and the defect energy are the SAME number `W`,
thus the domination reads `W * W ≤ corner * W` and `W` is positive. -/
theorem gapCorner_saturation (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) {setS : Finset (Fin size)}
    {atomU : Fin size} (hmemU : atomU ∈ setS)
    (hcap : ∀ atomIndex ∈ setS, value + weight atomIndex < 1)
    (hcornerPos : 0 < shiftedGapDiag projection weight value atomU)
    (hdominate : ∀ val : Fin size → ℝ,
      (∑ atomIndex ∈ setS, shiftedGap projection weight value atomU atomIndex
          * val atomIndex)
        * (∑ atomIndex ∈ setS, shiftedGap projection weight value atomU atomIndex
          * val atomIndex)
      ≤ shiftedGapDiag projection weight value atomU
        * ∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
          shiftedGap projection weight value rowIndex colIndex
            * (val rowIndex * val colIndex)) :
    ∑ atomIndex ∈ setS, shiftedGap projection weight value atomU atomIndex
        * shiftedGap projection weight value atomU atomIndex
        / (1 - (value + weight atomIndex))
      ≤ shiftedGapDiag projection weight value atomU := by
  classical
  set val : Fin size → ℝ := fun atomIndex =>
    shiftedGap projection weight value atomU atomIndex
      / (1 - (value + weight atomIndex)) with hval
  have hvalApply : ∀ atomIndex : Fin size, val atomIndex
      = shiftedGap projection weight value atomU atomIndex
        / (1 - (value + weight atomIndex)) := fun _ => rfl
  have hdef : ∀ atomIndex ∈ setS, (0 : ℝ) < 1 - (value + weight atomIndex) :=
    fun atomIndex hmem => by linarith [hcap atomIndex hmem]
  set energy := ∑ atomIndex ∈ setS,
    shiftedGap projection weight value atomU atomIndex
      * shiftedGap projection weight value atomU atomIndex
      / (1 - (value + weight atomIndex)) with henergy
  have hreading : ∑ atomIndex ∈ setS,
      shiftedGap projection weight value atomU atomIndex * val atomIndex = energy := by
    rw [henergy]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [hvalApply atomIndex, mul_div_assoc]
  have hdefectEnergy : ∑ atomIndex ∈ setS,
      (1 - (value + weight atomIndex)) * (val atomIndex * val atomIndex) = energy := by
    rw [henergy]
    refine Finset.sum_congr rfl fun atomIndex hmem => ?_
    have hne : (1 : ℝ) - (value + weight atomIndex) ≠ 0 :=
      ne_of_gt (hdef atomIndex hmem)
    rw [hvalApply atomIndex]
    field_simp
  have hcornerEntry : shiftedGap projection weight value atomU atomU
      = shiftedGapDiag projection weight value atomU :=
    shiftedGap_apply_diag (projection := projection) (weight := weight)
      (value := value) atomU
  have hpositive : 0 < energy := by
    rw [henergy]
    refine Finset.sum_pos' (fun atomIndex hmem =>
      div_nonneg (mul_self_nonneg _) (le_of_lt (hdef atomIndex hmem)))
      ⟨atomU, hmemU, ?_⟩
    refine div_pos ?_ (hdef atomU hmemU)
    rw [hcornerEntry]
    exact mul_pos hcornerPos hcornerPos
  have hform := shiftedGap_set_form_le (projection := projection) (weight := weight)
    (value := value) hsymm hidem setS val
  rw [hdefectEnergy] at hform
  have hdom := hdominate val
  rw [hreading] at hdom
  have hchain : energy * energy
      ≤ shiftedGapDiag projection weight value atomU * energy := by
    refine le_trans hdom ?_
    exact mul_le_mul_of_nonneg_left hform (le_of_lt hcornerPos)
  nlinarith [hchain, hpositive]

/-- A rank-one shifted gap block dominates with EQUALITY, thus the set
budget is the special case of the dominated corner budget. -/
theorem gapCorner_dominates_of_rankOne {setS : Finset (Fin size)} {atomU : Fin size}
    (hrankOne : ∀ rowIndex ∈ setS, ∀ colIndex ∈ setS,
      shiftedGap projection weight value rowIndex colIndex
          * shiftedGapDiag projection weight value atomU
        = shiftedGap projection weight value atomU rowIndex
          * shiftedGap projection weight value atomU colIndex)
    (val : Fin size → ℝ) :
    (∑ atomIndex ∈ setS, shiftedGap projection weight value atomU atomIndex
        * val atomIndex)
      * (∑ atomIndex ∈ setS, shiftedGap projection weight value atomU atomIndex
        * val atomIndex)
    ≤ shiftedGapDiag projection weight value atomU
      * ∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
        shiftedGap projection weight value rowIndex colIndex
          * (val rowIndex * val colIndex) := by
  classical
  refine le_of_eq (Eq.symm ?_)
  rw [Finset.mul_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun rowIndex hrow => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun colIndex hcol => ?_
  linear_combination (val rowIndex * val colIndex) * hrankOne rowIndex hrow colIndex hcol

/-- **THE CORNER ROW ENERGY CAP.**  Drop the captured defect: the plain
corner row energy of a dominated block never exceeds the corner. -/
theorem gapCorner_row_energy_le (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) {setS : Finset (Fin size)}
    {atomU : Fin size} (hmemU : atomU ∈ setS)
    (hfloor : ∀ atomIndex ∈ setS, 0 ≤ value + weight atomIndex)
    (hcap : ∀ atomIndex ∈ setS, value + weight atomIndex < 1)
    (hcornerPos : 0 < shiftedGapDiag projection weight value atomU)
    (hdominate : ∀ val : Fin size → ℝ,
      (∑ atomIndex ∈ setS, shiftedGap projection weight value atomU atomIndex
          * val atomIndex)
        * (∑ atomIndex ∈ setS, shiftedGap projection weight value atomU atomIndex
          * val atomIndex)
      ≤ shiftedGapDiag projection weight value atomU
        * ∑ rowIndex ∈ setS, ∑ colIndex ∈ setS,
          shiftedGap projection weight value rowIndex colIndex
            * (val rowIndex * val colIndex)) :
    ∑ atomIndex ∈ setS, shiftedGap projection weight value atomU atomIndex
        * shiftedGap projection weight value atomU atomIndex
      ≤ shiftedGapDiag projection weight value atomU := by
  refine le_trans (Finset.sum_le_sum ?_)
    (gapCorner_saturation hsymm hidem hmemU hcap hcornerPos hdominate)
  intro atomIndex hmem
  have hdef : (0 : ℝ) < 1 - (value + weight atomIndex) := by
    linarith [hcap atomIndex hmem]
  rw [le_div_iff₀ hdef]
  nlinarith [mul_self_nonneg (shiftedGap projection weight value atomU atomIndex),
    hfloor atomIndex hmem]

end CornerBudget

/-! ## Layer 5 — the off-block leak law of a rank-one block -/

section OffBlockLeak

variable {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}

/-- **THE OFF-DIAGONAL SQUARE.**  On a rank-one shifted gap block every
off-diagonal square is the product of the two shifted diagonals.  The
corner is positive, thus the Cramer cancellation is legal. -/
theorem gapSet_offDiag_sq {setS : Finset (Fin size)} {atomU : Fin size}
    (hcornerPos : 0 < shiftedGapDiag projection weight value atomU)
    (hrankOne : ∀ rowIndex ∈ setS, ∀ colIndex ∈ setS,
      shiftedGap projection weight value rowIndex colIndex
          * shiftedGapDiag projection weight value atomU
        = shiftedGap projection weight value atomU rowIndex
          * shiftedGap projection weight value atomU colIndex)
    {atomY atomZ : Fin size} (hmemY : atomY ∈ setS) (hmemZ : atomZ ∈ setS) :
    shiftedGap projection weight value atomY atomZ
        * shiftedGap projection weight value atomY atomZ
      = shiftedGapDiag projection weight value atomY
        * shiftedGapDiag projection weight value atomZ := by
  have hcross := hrankOne atomY hmemY atomZ hmemZ
  have hrowY := hrankOne atomY hmemY atomY hmemY
  have hrowZ := hrankOne atomZ hmemZ atomZ hmemZ
  rw [shiftedGap_apply_diag (projection := projection) (weight := weight)
    (value := value) atomY] at hrowY
  rw [shiftedGap_apply_diag (projection := projection) (weight := weight)
    (value := value) atomZ] at hrowZ
  have hne : shiftedGapDiag projection weight value atomU ≠ 0 := ne_of_gt hcornerPos
  have hsquare : (shiftedGapDiag projection weight value atomU
        * shiftedGapDiag projection weight value atomU)
      * (shiftedGap projection weight value atomY atomZ
          * shiftedGap projection weight value atomY atomZ
        - shiftedGapDiag projection weight value atomY
          * shiftedGapDiag projection weight value atomZ) = 0 := by
    linear_combination (shiftedGap projection weight value atomY atomZ
        * shiftedGapDiag projection weight value atomU
      + shiftedGap projection weight value atomU atomY
        * shiftedGap projection weight value atomU atomZ) * hcross
      - shiftedGapDiag projection weight value atomZ
        * shiftedGapDiag projection weight value atomU * hrowY
      - shiftedGap projection weight value atomU atomY
        * shiftedGap projection weight value atomU atomY * hrowZ
  have hfactor := (mul_eq_zero.mp hsquare).resolve_left (mul_ne_zero hne hne)
  linarith

/-- **THE OFF-BLOCK LEAK LAW.**  The row energy of a chart row splits at a
rank-one shifted gap block.  Inside the block every square is a product of
shifted diagonals, thus the energy that the row sends OUT of the block is
exact. -/
theorem gapSet_offSet_energy (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) {setS : Finset (Fin size)}
    {atomU : Fin size} (hcornerPos : 0 < shiftedGapDiag projection weight value atomU)
    (hrankOne : ∀ rowIndex ∈ setS, ∀ colIndex ∈ setS,
      shiftedGap projection weight value rowIndex colIndex
          * shiftedGapDiag projection weight value atomU
        = shiftedGap projection weight value atomU rowIndex
          * shiftedGap projection weight value atomU colIndex)
    {atomY : Fin size} (hmemY : atomY ∈ setS) :
    ∑ colIndex ∈ Finset.univ \ setS,
        projection atomY colIndex * projection atomY colIndex
      = shiftedGapDiag projection weight value atomY
          * (1 - 2 * (value + weight atomY)
            - ∑ atomIndex ∈ setS, shiftedGapDiag projection weight value atomIndex)
        + (value + weight atomY) * (1 - (value + weight atomY)) := by
  classical
  have hrow := projection_row_energy hsymm hidem atomY
  have hsplitSet : Finset.univ.erase atomY
      = (setS.erase atomY) ∪ (Finset.univ \ setS) := by
    ext atomIndex
    constructor
    · intro hmem
      have hne : atomIndex ≠ atomY := Finset.ne_of_mem_erase hmem
      by_cases hin : atomIndex ∈ setS
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hin⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hin⟩)
    · intro hmem
      rcases Finset.mem_union.mp hmem with hleft | hright
      · exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hleft, Finset.mem_univ _⟩
      · refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro heq
        exact (Finset.mem_sdiff.mp hright).2 (heq ▸ hmemY)
  have hdisjoint : Disjoint (setS.erase atomY) (Finset.univ \ setS) := by
    refine Finset.disjoint_left.mpr fun atomIndex hleft hright => ?_
    exact (Finset.mem_sdiff.mp hright).2 (Finset.mem_of_mem_erase hleft)
  rw [hsplitSet, Finset.sum_union hdisjoint] at hrow
  have hinner : ∑ colIndex ∈ setS.erase atomY,
      projection atomY colIndex * projection atomY colIndex
      = shiftedGapDiag projection weight value atomY
        * ((∑ atomIndex ∈ setS, shiftedGapDiag projection weight value atomIndex)
          - shiftedGapDiag projection weight value atomY) := by
    have hterm : ∀ colIndex ∈ setS.erase atomY,
        projection atomY colIndex * projection atomY colIndex
        = shiftedGapDiag projection weight value atomY
          * shiftedGapDiag projection weight value colIndex := by
      intro colIndex hmem
      have hne : atomY ≠ colIndex := Ne.symm (Finset.ne_of_mem_erase hmem)
      have hentry : projection atomY colIndex
          = shiftedGap projection weight value atomY colIndex := by
        rw [shiftedGap_apply_offDiag (projection := projection) (weight := weight)
          (value := value) hne,
          projection_offDiag_eq_gap (projection := projection) (weight := weight) hne]
      rw [hentry]
      exact gapSet_offDiag_sq hcornerPos hrankOne hmemY (Finset.mem_of_mem_erase hmem)
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    have hpeel := Finset.add_sum_erase setS
      (fun atomIndex => shiftedGapDiag projection weight value atomIndex) hmemY
    linarith
  have hdiag := projection_diag_eq_shift (projection := projection) (weight := weight)
    (value := value) atomY
  rw [hinner, hdiag] at hrow
  linear_combination hrow

/-- **THE LEAK FLOOR.**  The off-block energy is a sum of squares, thus a
rank-one block caps every one of its shifted diagonals against the block
total and the captured diagonal. -/
theorem gapSet_leak_floor (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) {setS : Finset (Fin size)}
    {atomU : Fin size} (hcornerPos : 0 < shiftedGapDiag projection weight value atomU)
    (hrankOne : ∀ rowIndex ∈ setS, ∀ colIndex ∈ setS,
      shiftedGap projection weight value rowIndex colIndex
          * shiftedGapDiag projection weight value atomU
        = shiftedGap projection weight value atomU rowIndex
          * shiftedGap projection weight value atomU colIndex)
    {atomY : Fin size} (hmemY : atomY ∈ setS) :
    shiftedGapDiag projection weight value atomY
        * ((∑ atomIndex ∈ setS, shiftedGapDiag projection weight value atomIndex)
          + 2 * (value + weight atomY) - 1)
      ≤ (value + weight atomY) * (1 - (value + weight atomY)) := by
  classical
  have henergy := gapSet_offSet_energy hsymm hidem hcornerPos hrankOne hmemY
  have hnonneg : (0 : ℝ) ≤ ∑ colIndex ∈ Finset.univ \ setS,
      projection atomY colIndex * projection atomY colIndex :=
    Finset.sum_nonneg fun colIndex _ => mul_self_nonneg _
  rw [henergy] at hnonneg
  nlinarith [hnonneg]

/-- **THE CONTRACTION-FREE BUDGET.**  At an atom of ZERO capture inside a
rank-one block, the leak floor alone gives the unit budget.  No
contraction and no probe are used. -/
theorem gapSet_sum_le_one_of_zero_capture (hsymm : projectionᵀ = projection)
    (hidem : projection * projection = projection) {setS : Finset (Fin size)}
    {atomU : Fin size} (hcornerPos : 0 < shiftedGapDiag projection weight value atomU)
    (hrankOne : ∀ rowIndex ∈ setS, ∀ colIndex ∈ setS,
      shiftedGap projection weight value rowIndex colIndex
          * shiftedGapDiag projection weight value atomU
        = shiftedGap projection weight value atomU rowIndex
          * shiftedGap projection weight value atomU colIndex)
    {atomY : Fin size} (hmemY : atomY ∈ setS)
    (hposY : 0 < shiftedGapDiag projection weight value atomY)
    (hzero : value + weight atomY = 0) :
    ∑ atomIndex ∈ setS, shiftedGapDiag projection weight value atomIndex ≤ 1 := by
  have hfloor := gapSet_leak_floor hsymm hidem hcornerPos hrankOne hmemY
  rw [hzero] at hfloor
  nlinarith [hfloor, hposY]

end OffBlockLeak

/-! ## Layer 6 — the tight leak identity -/

section TightLeak

variable {size rank : ℕ} {activeIndex : Type}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE CHART ACTS AS THE CAPTURED DIAGONAL.**  Inside its own block a
tight direction is scaled by the captured diagonal.  The gap dictionary
turns the tight equation into this reading. -/
theorem chart_mulVec_tightDir_apply
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomIndex : Fin size} (hblock : atomIndex ∈ activeSubset label) :
    (projection *ᵥ tightDir label) atomIndex
      = (value + weight atomIndex) * tightDir label atomIndex := by
  have htight := hdata.tightDir_isTight label hmem atomIndex hblock
  rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply,
    Matrix.mulVec_diagonal] at htight
  linarith

/-- **THE TIGHT ENERGY.**  The chart energy of a tight direction is the
captured diagonal, weighted by the direction's own squares. -/
theorem chart_tightDir_energy
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet) :
    tightDir label ⬝ᵥ (projection *ᵥ tightDir label)
      = ∑ atomIndex ∈ activeSubset label,
          (value + weight atomIndex) * (tightDir label atomIndex * tightDir label atomIndex) := by
  classical
  rw [dotProduct]
  refine (Finset.sum_subset (Finset.subset_univ (activeSubset label)) ?_).symm.trans ?_
  · intro atomIndex _ hnot
    rw [hdata.tightDir_support label hmem atomIndex hnot, zero_mul]
  · refine Finset.sum_congr rfl fun atomIndex hblock => ?_
    rw [chart_mulVec_tightDir_apply hdata hmem hblock]
    ring

/-- **THE TIGHT LEAK IDENTITY.**  The image of a tight direction has its
carrier energy inside the block, thus the energy that leaks OUT of the
block is the captured diagonal times its own defect.  No rank-one law and
no support hypothesis beyond the block are used. -/
theorem chart_tightDir_offBlock_leak
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet) :
    ∑ atomIndex ∈ Finset.univ \ activeSubset label,
        (projection *ᵥ tightDir label) atomIndex * (projection *ᵥ tightDir label) atomIndex
      = ∑ atomIndex ∈ activeSubset label,
          (value + weight atomIndex) * (1 - (value + weight atomIndex))
            * (tightDir label atomIndex * tightDir label atomIndex) := by
  classical
  have hnorm := dotProduct_mulVec_eq_image_dotProduct_self hdata.isSymmetric
    hdata.isIdempotent (tightDir label)
  have henergy := chart_tightDir_energy hdata hmem
  have hsplit := Finset.sum_sdiff (f := fun atomIndex =>
      (projection *ᵥ tightDir label) atomIndex * (projection *ᵥ tightDir label) atomIndex)
    (Finset.subset_univ (activeSubset label))
  have hcarrier : ∑ atomIndex ∈ activeSubset label,
      (projection *ᵥ tightDir label) atomIndex * (projection *ᵥ tightDir label) atomIndex
      = ∑ atomIndex ∈ activeSubset label,
        ((value + weight atomIndex) * (value + weight atomIndex))
          * (tightDir label atomIndex * tightDir label atomIndex) := by
    refine Finset.sum_congr rfl fun atomIndex hblock => ?_
    rw [chart_mulVec_tightDir_apply hdata hmem hblock]
    ring
  have himage : ∑ atomIndex : Fin size,
      (projection *ᵥ tightDir label) atomIndex * (projection *ᵥ tightDir label) atomIndex
      = ∑ atomIndex ∈ activeSubset label,
        (value + weight atomIndex) * (tightDir label atomIndex * tightDir label atomIndex) := by
    rw [← henergy, hnorm, dotProduct]
  rw [hcarrier, himage] at hsplit
  have hcombine : ∑ atomIndex ∈ activeSubset label,
      (value + weight atomIndex) * (1 - (value + weight atomIndex))
        * (tightDir label atomIndex * tightDir label atomIndex)
      = (∑ atomIndex ∈ activeSubset label,
          (value + weight atomIndex) * (tightDir label atomIndex * tightDir label atomIndex))
        - ∑ atomIndex ∈ activeSubset label,
          ((value + weight atomIndex) * (value + weight atomIndex))
            * (tightDir label atomIndex * tightDir label atomIndex) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  rw [hcombine]
  linarith [hsplit]

/-- **A BLOCK OF ZERO CAPTURE ANNIHILATES ITS TIGHT DIRECTION.**  Both the
carrier part and the leak vanish, thus the chart kills the direction. -/
theorem chart_mulVec_tightDir_eq_zero_of_zero_capture
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    (hzero : ∀ atomIndex ∈ activeSubset label, value + weight atomIndex = 0) :
    projection *ᵥ tightDir label = 0 := by
  classical
  have hleak := chart_tightDir_offBlock_leak hdata hmem
  have hright : ∑ atomIndex ∈ activeSubset label,
      (value + weight atomIndex) * (1 - (value + weight atomIndex))
        * (tightDir label atomIndex * tightDir label atomIndex) = 0 := by
    refine Finset.sum_eq_zero fun atomIndex hblock => ?_
    rw [hzero atomIndex hblock]
    ring
  rw [hright] at hleak
  funext atomIndex
  by_cases hblock : atomIndex ∈ activeSubset label
  · rw [chart_mulVec_tightDir_apply hdata hmem hblock, hzero atomIndex hblock,
      zero_mul]
    rfl
  · have hmemSdiff : atomIndex ∈ Finset.univ \ activeSubset label :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hblock⟩
    have hterm : (projection *ᵥ tightDir label) atomIndex
        * (projection *ᵥ tightDir label) atomIndex = 0 := by
      by_contra hne
      have hpos : 0 < (projection *ᵥ tightDir label) atomIndex
          * (projection *ᵥ tightDir label) atomIndex :=
        lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm hne)
      have hbound : (projection *ᵥ tightDir label) atomIndex
          * (projection *ᵥ tightDir label) atomIndex
          ≤ ∑ colIndex ∈ Finset.univ \ activeSubset label,
            (projection *ᵥ tightDir label) colIndex
              * (projection *ᵥ tightDir label) colIndex :=
        Finset.single_le_sum (fun colIndex _ => mul_self_nonneg _) hmemSdiff
      rw [hleak] at hbound
      linarith
    have := mul_self_eq_zero.mp hterm
    rw [this]
    rfl

end TightLeak

/-! ## Layer 7 — the datum payments of the re-cut identical residue -/

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-- **THE LEAK FLOOR AT THE SHARED TRIPLE.**  Each atom of the shared
triple pays the leak floor of its rank-one block. -/
theorem identical_support_leak_floor (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS})
    {atomY : Fin 6} (hmemY : atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6))) :
    shiftedGapDiag (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) atomY
        * ((∑ atomIndex ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
              shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomIndex)
          + 2 * (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomY) - 1)
      ≤ (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomY)
        * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomY)) :=
  gapSet_leak_floor data.hdata.isSymmetric data.hdata.isIdempotent
    (data.shiftedGapDiag_pos atomU)
    (shiftedGap_rankOne_of_gapBlockRankOne data.hdata.isSymmetric hUV hUS hVS
      (data.gapBlockRankOne_of_identical_support hne hUV hUS hVS hsupportOne hsupportTwo))
    hmemY

end SharedPrivateData

/-! ## Layer 8 — the re-cut identical residue and closure two -/

/-- **THE LEDGER-PAID IDENTICAL RESIDUE.**  The identical-support branch,
with every payment of the saturated residue AND the three new ones: the
complement floor, the leak floor at each atom of the shared triple, and
the refusal of a rank-one complement. -/
def SharedPrivateCircuitPairIdenticalLedgerClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomU atomV atomS : Fin 6, atomU ≠ atomV → atomU ≠ atomS → atomV ≠ atomS →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomU, atomV, atomS} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomU, atomV, atomS} →
        GapBlockRankOne (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomU atomV atomS →
        data.pinAtom ∉ datumTightSupport data.tightDir (data.basisLabel slotOne) →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomU
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomV
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomS ≤ 1 →
        1 - 6 * chartObjective (chartPointOfDesign crux.design)
          ≤ ∑ atomIndex ∈ Finset.univ \ ({atomU, atomV, atomS} : Finset (Fin 6)),
              shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomIndex →
        (∀ atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
          shiftedGapDiag (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight
              (chartObjective (chartPointOfDesign crux.design)) atomY
              * ((∑ atomIndex ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
                    shiftedGapDiag (chartPointOfDesign crux.design).chart
                      (chartPointOfDesign crux.design).weight
                      (chartObjective (chartPointOfDesign crux.design)) atomIndex)
                + 2 * (chartObjective (chartPointOfDesign crux.design)
                  + (chartPointOfDesign crux.design).weight atomY) - 1)
            ≤ (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomY)
              * (1 - (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomY))) →
        (∀ atomP atomQ atomR : Fin 6, atomP ≠ atomQ → atomP ≠ atomR → atomQ ≠ atomR →
          ({atomU, atomV, atomS} : Finset (Fin 6)) ∪ {atomP, atomQ, atomR}
              = Finset.univ →
          ¬ GapBlockRankOne (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomP atomQ atomR) →
        False

/-- **THE LEDGER PAYMENT BRIDGE.**  Every hypothesis that the re-cut
residue adds is a theorem at the datum, thus the re-cut residue closes the
plain one. -/
theorem sharedPrivateCircuitPairIdenticalClosed_of_ledger
    (hpaid : SharedPrivateCircuitPairIdenticalLedgerClosed) :
    SharedPrivateCircuitPairIdenticalClosed := by
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape
  exact hpaid crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape
    (data.pinAtom_notMem_of_identical_support hne (hsupportTwo.trans hsupportOne.symm))
    (data.identical_support_shifted_sum_le_one hne hUV hUS hVS hsupportOne hsupportTwo)
    (data.identical_support_complement_sum hne hUV hUS hVS hsupportOne hsupportTwo)
    (fun atomY hmemY => data.identical_support_leak_floor hne hUV hUS hVS hsupportOne
      hsupportTwo hmemY)
    (fun atomP atomQ atomR hPQ hPR hQR hcover =>
      data.not_gapBlockRankOne_complement_of_identical_support hne hUV hUS hVS hPQ hPR
        hQR hcover hsupportOne hsupportTwo)

/-- **THE EXTRAS FROM THE RE-CUT LATTICE.** -/
theorem sharedPrivateExtrasClosed_of_ledger_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalLedgerClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateExtrasClosed :=
  sharedPrivateExtrasClosed_of_circuit_lattice
    (sharedPrivateCircuitPairIdenticalClosed_of_ledger hidentical) hwedgeLive
    (sharedPrivateCircuitSplitPairClosed_of_saturated hwedgeDead) hwide

/-- **THE WHOLE OF CLOSURE TWO ON THE RE-CUT LATTICE.** -/
theorem sharedPrivateKilled_of_ledger_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalLedgerClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_sharedPrivate_lattice
    (sharedPrivateCircuitPairIdenticalClosed_of_ledger hidentical) hwedgeLive
    (sharedPrivateCircuitSplitPairClosed_of_saturated hwedgeDead) hwide hconfined

/-- Closure two of the rank-four rung on the re-cut lattice. -/
theorem rankFourSharedPrivateClosed_of_ledger_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalLedgerClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_sharedPrivate_lattice
    (sharedPrivateCircuitPairIdenticalClosed_of_ledger hidentical) hwedgeLive
    (sharedPrivateCircuitSplitPairClosed_of_saturated hwedgeDead) hwide hconfined

/-- The shared-private closure of the rank-five rung on the re-cut
lattice. -/
theorem rankFiveSharedPrivateClosed_of_ledger_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalLedgerClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_sharedPrivate_lattice
    (sharedPrivateCircuitPairIdenticalClosed_of_ledger hidentical) hwedgeLive
    (sharedPrivateCircuitSplitPairClosed_of_saturated hwedgeDead) hwide hconfined

/-- The shared-private closure of the rank-six rung on the re-cut
lattice. -/
theorem rankSixSharedPrivateClosed_of_ledger_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalLedgerClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_sharedPrivate_lattice
    (sharedPrivateCircuitPairIdenticalClosed_of_ledger hidentical) hwedgeLive
    (sharedPrivateCircuitSplitPairClosed_of_saturated hwedgeDead) hwide hconfined

end Gtz
