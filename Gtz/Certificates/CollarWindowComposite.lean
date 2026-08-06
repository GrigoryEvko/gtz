import Mathlib
import Gtz.Certificates.CollarChartReplay
import Gtz.Certificates.CollarWindowCriterion

/-!
# The composite: kernel-replay acceptance to `rho_star < rho_G*` at a point

This file chains the committed checker's exported sign package
(`Gtz.CollarReplay.ThresholdIsValidAt`, `CandidateWinsAt`, `FreeWinHoldsAt`)
onto the ordered-field window criterion of bridge (i), over the reals.

The chain consumes exactly two DICTIONARY facts that the Int-valued
certificate cannot carry, both of them bridge-(iii) obligations and both
stated here as explicit hypotheses rather than assumed silently:

  * `marginIsCross` -- the recorded margin IS the cross-difference
    `RN * thrDen - thrNum * RD`.  The certificate stores the margin as an
    independent factored triple; that it equals the cross-difference is a
    ring identity of the dictionary.
  * `IsGordanAggregate` -- `RN` is the plain slot sum and `RD` the
    coupling-weighted slot sum with nonnegative couplings.  This is what
    makes the ratio positive and lets the checker's `RN`-indexed margin sign
    be read as a statement about `RD`.

Everything else -- validity, the directed boundary ray, the strict margin
chain -- comes straight from `checkChart_sound` through the chart
certificates.
-/

namespace GtzCollarWindowComposite

open Gtz.CollarReplay GtzCollarWindow

/-- The through-tree record of a threshold index, read over the reals from
the certificate's integer triple values at a point. -/
def realThresholdRecord (data : ChartData) (thrIndex : Nat)
    (den one two three four : Int) : ThroughTreeRecord ℝ :=
  ⟨((tripleValueAt data (thresholdAt data thrIndex).spanNum den one two three
      four : Int) : ℝ),
   ((tripleValueAt data (thresholdAt data thrIndex).spanDen den one two three
      four : Int) : ℝ),
   ((tripleValueAt data (thresholdAt data thrIndex).massNum den one two three
      four : Int) : ℝ),
   ((tripleValueAt data (thresholdAt data thrIndex).massDen den one two three
      four : Int) : ℝ),
   ((tripleValueAt data (thresholdAt data thrIndex).thrNum den one two three
      four : Int) : ℝ),
   ((tripleValueAt data (thresholdAt data thrIndex).thrDen den one two three
      four : Int) : ℝ)⟩

/-- The beta slot values of a candidate, read over the reals. -/
def realCandidateSlots (data : ChartData) (candIndex : Nat)
    (den one two three four : Int) : List ℝ :=
  (candidateAt data candIndex).betas.map fun slot =>
    ((tripleValueAt data slot den one two three four : Int) : ℝ)

theorem realThresholdRecordIsValid {data : ChartData} {thrIndex : Nat}
    {den one two three four : Int}
    (valid : ThresholdIsValidAt data thrIndex den one two three four) :
    (realThresholdRecord data thrIndex den one two three four).IsValidAt := by
  obtain ⟨spanPositive, massPositive⟩ := valid
  constructor
  · show (0 : ℝ) < _ * _
    have castPositive : (0 : ℝ)
        < ((tripleValueAt data (thresholdAt data thrIndex).spanNum den one two
            three four
          * tripleValueAt data (thresholdAt data thrIndex).spanDen den one two
            three four : Int) : ℝ) := by exact_mod_cast spanPositive
    simpa [realThresholdRecord] using castPositive
  · show (0 : ℝ) < _ * _
    have castPositive : (0 : ℝ)
        < ((tripleValueAt data (thresholdAt data thrIndex).massNum den one two
            three four
          * tripleValueAt data (thresholdAt data thrIndex).massDen den one two
            three four : Int) : ℝ) := by exact_mod_cast massPositive
    simpa [realThresholdRecord] using castPositive

/-- THE COMPOSITE, guarded-candidate form.  The checker's integer sign
package at a point, plus the two dictionary facts, gives the collar window
inequality `rho_star < rho_G*` at that point over the reals. -/
theorem windowIsOpenOfCandidateWinsAt
    {data : ChartData} {candIndex thrIndex : Nat}
    {den one two three four : Int}
    {aggregate : GordanAggregateRecord ℝ}
    {headAggregate : GordanAggregateRecord ℝ}
    {restAggregates : List (GordanAggregateRecord ℝ)}
    {headRecord : ThroughTreeRecord ℝ}
    {restRecords : List (ThroughTreeRecord ℝ)}
    (valid : ThresholdIsValidAt data thrIndex den one two three four)
    (wins : CandidateWinsAt data candIndex thrIndex den one two three four)
    (aggregateSlotsAreCertificateSlots :
      aggregate.slots = realCandidateSlots data candIndex den one two three four)
    (aggregateRatioNumIsCertificateRatioNum :
      aggregate.ratioNum
        = ((tripleValueAt data (candidateAt data candIndex).ratioNum den one
            two three four : Int) : ℝ))
    (isAggregate : IsGordanAggregate aggregate)
    (ratioDenIsNonzero : aggregate.ratioDen ≠ 0)
    (marginIsCross :
      ((tripleValueAt data (marginAt data candIndex thrIndex) den one two
          three four : Int) : ℝ)
        = aggregate.ratioNum
            * (realThresholdRecord data thrIndex den one two three four).thrDen
          - (realThresholdRecord data thrIndex den one two three four).thrNum
            * aggregate.ratioDen)
    (aggregateMem : aggregate ∈ headAggregate :: restAggregates)
    (recordMem : realThresholdRecord data thrIndex den one two three four
      ∈ headRecord :: restRecords) :
    rhoStar headRecord restRecords < rhoGStar headAggregate restAggregates := by
  obtain ⟨⟨commonDir, commonDirIsUnit, slotsDirected⟩, marginChain⟩ := wins
  have marginSignInt : 0 <
      tripleValueAt data (candidateAt data candIndex).ratioNum den one two
          three four
        * tripleValueAt data (thresholdAt data thrIndex).thrDen den one two
          three four
        * tripleValueAt data (marginAt data candIndex thrIndex) den one two
          three four := marginChain
  have marginSignReal : (0 : ℝ) < aggregate.ratioNum
      * (realThresholdRecord data thrIndex den one two three four).thrDen
      * ((tripleValueAt data (marginAt data candIndex thrIndex) den one two
          three four : Int) : ℝ) := by
    rw [aggregateRatioNumIsCertificateRatioNum]
    have castPositive : (0 : ℝ) < ((tripleValueAt data
        (candidateAt data candIndex).ratioNum den one two three four
      * tripleValueAt data (thresholdAt data thrIndex).thrDen den one two
        three four
      * tripleValueAt data (marginAt data candIndex thrIndex) den one two
        three four : Int) : ℝ) := by exact_mod_cast marginSignInt
    simpa [realThresholdRecord] using castPositive
  have ratioNumIsNonzero : aggregate.ratioNum ≠ 0 := by
    intro isZero
    rw [isZero, zero_mul, zero_mul] at marginSignReal
    exact lt_irrefl 0 marginSignReal
  have directed : SlotsAreDirected aggregate.slots ((commonDir : Int) : ℝ) := by
    refine ⟨?_, ?_⟩
    · rcases commonDirIsUnit with isOne | isNegOne
      · exact Or.inl (by rw [isOne]; norm_num)
      · exact Or.inr (by rw [isNegOne]; norm_num)
    · intro slotValue slotMem
      rw [aggregateSlotsAreCertificateSlots] at slotMem
      obtain ⟨slot, slotInBetas, slotValueForm⟩ := List.mem_map.mp slotMem
      rw [← slotValueForm]
      have directedInt : 0 ≤ commonDir
          * tripleValueAt data slot den one two three four :=
        slotsDirected slot slotInBetas
      have castNonneg : (0 : ℝ) ≤ ((commonDir
          * tripleValueAt data slot den one two three four : Int) : ℝ) := by
        exact_mod_cast directedInt
      simpa using castNonneg
  exact windowIsOpenOfCandidate aggregateMem recordMem
    (realThresholdRecordIsValid valid) isAggregate directed ratioNumIsNonzero
    ratioDenIsNonzero marginIsCross marginSignReal

/-- THE COMPOSITE, free-win form: a valid through-tree with a negative
threshold opens the window against any in-cone aggregate. -/
theorem windowIsOpenOfFreeWinAt
    {data : ChartData} {thrIndex : Nat} {den one two three four : Int}
    {aggregate : GordanAggregateRecord ℝ}
    {headAggregate : GordanAggregateRecord ℝ}
    {restAggregates : List (GordanAggregateRecord ℝ)}
    {headRecord : ThroughTreeRecord ℝ}
    {restRecords : List (ThroughTreeRecord ℝ)} {direction : ℝ}
    (valid : ThresholdIsValidAt data thrIndex den one two three four)
    (freeWin : FreeWinHoldsAt data thrIndex den one two three four)
    (isAggregate : IsGordanAggregate aggregate)
    (directed : SlotsAreDirected aggregate.slots direction)
    (ratioNumIsNonzero : aggregate.ratioNum ≠ 0)
    (ratioDenIsNonzero : aggregate.ratioDen ≠ 0)
    (aggregateMem : aggregate ∈ headAggregate :: restAggregates)
    (recordMem : realThresholdRecord data thrIndex den one two three four
      ∈ headRecord :: restRecords) :
    rhoStar headRecord restRecords < rhoGStar headAggregate restAggregates := by
  have freeWinReal :
      (realThresholdRecord data thrIndex den one two three four).thrNum
        * (realThresholdRecord data thrIndex den one two three four).thrDen
        < 0 := by
    have castNegative : ((tripleValueAt data (thresholdAt data thrIndex).thrNum
        den one two three four
      * tripleValueAt data (thresholdAt data thrIndex).thrDen den one two
        three four : Int) : ℝ) < 0 := by exact_mod_cast freeWin
    simpa [realThresholdRecord] using castNegative
  exact windowIsOpenOfFreeWin aggregateMem recordMem
    (realThresholdRecordIsValid valid) freeWinReal isAggregate directed
    ratioNumIsNonzero ratioDenIsNonzero

end GtzCollarWindowComposite
