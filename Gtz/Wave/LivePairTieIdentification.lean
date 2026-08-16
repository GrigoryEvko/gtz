import Gtz.Wave.LivePairTieRefuter
import Gtz.Design.OneDeterminantReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The live-pair tie statement is the design lane restated

`Gtz.ExistsLivePairTieDesign` reads as a reduction: a live pair is free, so only
one determinant sign remains.  This file shows the reading is wrong.  The
statement is kernel-equivalent to strict domination itself, through the landed
one-determinant equivalence `Gtz.hasLivePairPositiveTie_iff_exists_posDef_cardThree`.

Three steps.

* The second label's heaviness is not an extra demand.  A positive corner and a
  positive two by two minor force it.
* Hence the live-pair tie witness IS `Gtz.HasLivePairPositiveTie`, whose
  equivalence with strict domination is landed.
* So `Gtz.ExistsLivePairTieDesign` is strict domination at every design of size
  six, with no primitivity hypothesis.  It is at least as strong as
  `Gtz.ConsolidatedStrictTripleDesign`, not weaker.

The corrected statement in this vocabulary carries the primitivity hypothesis,
and that one is an equivalence.
-/

namespace Gtz

variable {m : ℕ}

/-! ## 1. The second heaviness is free -/

/-- **A live pair needs only one heaviness hypothesis.**  A positive corner and a
positive two by two minor force the second corner, because the minor is the
product of the two corners minus a square. -/
theorem gapExcessOf_pos_of_pairGapExcessOf_pos (design : WeightedDesign m 3)
    {firstLabel secondLabel : Fin m} (hfirst : 0 < gapExcessOf design firstLabel)
    (hpair : 0 < pairGapExcessOf design firstLabel secondLabel) :
    0 < gapExcessOf design secondLabel := by
  have hexpand : gapExcessOf design firstLabel * gapExcessOf design secondLabel
      - gapPairingOf design firstLabel secondLabel ^ 2
      = pairGapExcessOf design firstLabel secondLabel := rfl
  have hsq : 0 ≤ gapPairingOf design firstLabel secondLabel ^ 2 := sq_nonneg _
  have hprod : 0 < gapExcessOf design firstLabel * gapExcessOf design secondLabel := by
    nlinarith [hpair, hsq, hexpand]
  by_contra hcontra
  push Not at hcontra
  nlinarith [hprod, hfirst, hcontra]

/-- The same reading in the discriminant system's vocabulary. -/
theorem heavyExcess_pos_of_pairGapExcessOf_pos (design : WeightedDesign m 3)
    {firstLabel secondLabel : Fin m} (hfirst : 0 < heavyExcess design firstLabel)
    (hpair : 0 < pairGapExcessOf design firstLabel secondLabel) :
    0 < heavyExcess design secondLabel :=
  gapExcessOf_pos_of_pairGapExcessOf_pos design hfirst hpair

/-- A live pair is exactly a positive corner together with a positive minor. -/
theorem isLivePair_iff_corner_and_minor (design : WeightedDesign m 3)
    (firstLabel secondLabel : Fin m) :
    IsLivePair design firstLabel secondLabel
      ↔ 0 < heavyExcess design firstLabel
        ∧ 0 < pairGapExcessOf design firstLabel secondLabel := by
  constructor
  · rintro ⟨hfirst, -, hminor⟩
    exact ⟨hfirst, hminor⟩
  · rintro ⟨hfirst, hminor⟩
    exact ⟨hfirst, gapExcessOf_pos_of_pairGapExcessOf_pos design hfirst hminor, hminor⟩

/-! ## 2. The witness shape is `HasLivePairPositiveTie` -/

/-- **The two witness shapes agree.**  The live-pair tie witness of
`Gtz.ExistsLivePairTieDesign` is `Gtz.HasLivePairPositiveTie`, with the second
heaviness supplied by step one rather than assumed. -/
theorem hasLivePairPositiveTie_iff_livePairTieWitness (design : WeightedDesign m 3) :
    HasLivePairPositiveTie design
      ↔ ∃ pivotLabel pairFirst pairSecond : Fin m,
          pivotLabel ≠ pairFirst ∧ pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ 0 < heavyExcess design pivotLabel
            ∧ 0 < pairGapExcessOf design pivotLabel pairFirst
            ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond := by
  constructor
  · rintro ⟨pivotLabel, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      hlive, hdeterminant⟩
    obtain ⟨hcorner, hminor⟩ := (isLivePair_iff_corner_and_minor design pivotLabel pairFirst).mp hlive
    exact ⟨pivotLabel, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      hcorner, hminor, hdeterminant⟩
  · rintro ⟨pivotLabel, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      hcorner, hminor, hdeterminant⟩
    exact ⟨pivotLabel, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      (isLivePair_iff_corner_and_minor design pivotLabel pairFirst).mpr ⟨hcorner, hminor⟩,
      hdeterminant⟩

/-- **The witness is strict domination.**  Composing step two with the landed
one-determinant equivalence. -/
theorem livePairTieWitness_iff_exists_posDef_cardThree (design : WeightedDesign m 3) :
    (∃ pivotLabel pairFirst pairSecond : Fin m,
        pivotLabel ≠ pairFirst ∧ pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ 0 < heavyExcess design pivotLabel
          ∧ 0 < pairGapExcessOf design pivotLabel pairFirst
          ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond)
      ↔ ∃ selected : Finset (Fin m), selected.card = 3
          ∧ (subsetSum design selected - 1).PosDef :=
  (hasLivePairPositiveTie_iff_livePairTieWitness design).symm.trans
    (hasLivePairPositiveTie_iff_exists_posDef_cardThree design)

/-! ## 3. The verdict -/

/-- **`Gtz.ExistsLivePairTieDesign` IS strict domination at every design of size
six.**  No primitivity hypothesis survives on either side, so the statement is
not a reduction of the design consolidation: it is that statement with the
primitivity hypothesis DROPPED. -/
theorem existsLivePairTieDesign_iff_forall_exists_posDef :
    ExistsLivePairTieDesign
      ↔ ∀ design : WeightedDesign 6 3, ∃ selected : Finset (Fin 6), selected.card = 3
          ∧ (subsetSum design selected - 1).PosDef := by
  constructor
  · intro hexists design
    exact (livePairTieWitness_iff_exists_posDef_cardThree design).mp (hexists design)
  · intro hforall design
    exact (livePairTieWitness_iff_exists_posDef_cardThree design).mpr (hforall design)

/-- The live-pair tie statement restricted to primitive designs. -/
def ExistsLivePairTiePrimitiveDesign : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    ∃ pivotLabel pairFirst pairSecond : Fin 6,
      pivotLabel ≠ pairFirst ∧ pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ 0 < heavyExcess design pivotLabel
        ∧ 0 < pairGapExcessOf design pivotLabel pairFirst
        ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond

/-- **THE CORRECTED STATEMENT IS AN EQUIVALENCE.**  With the primitivity
hypothesis restored, the live-pair tie vocabulary and the design consolidation
are the same statement.  So nothing is gained by changing vocabulary, and
nothing is lost. -/
theorem existsLivePairTiePrimitiveDesign_iff_consolidatedStrictTripleDesign :
    ExistsLivePairTiePrimitiveDesign ↔ ConsolidatedStrictTripleDesign := by
  constructor
  · intro hexists design hprimitive
    exact (livePairTieWitness_iff_exists_posDef_cardThree design).mp (hexists design hprimitive)
  · intro hconsolidated design hprimitive
    exact (livePairTieWitness_iff_exists_posDef_cardThree design).mpr
      (hconsolidated design hprimitive)

/-- **The unrestricted statement implies the restricted one**, so the route
FORK-125 landed is at least as strong as the design lane and never weaker. -/
theorem existsLivePairTiePrimitiveDesign_of_existsLivePairTieDesign
    (hexists : ExistsLivePairTieDesign) : ExistsLivePairTiePrimitiveDesign :=
  fun design _hprimitive => hexists design

/-- **THE VERDICT.**  The live-pair tie statement is not a reduction of the
design consolidation.  Its primitive restriction is kernel-equivalent to it, and
the unrestricted form implies that restriction.  The apparent saving -- that the
live pair is free and only one determinant sign remains -- is
`Gtz.hasLivePairPositiveTie_iff_exists_posDef_cardThree` read forwards, and that
equivalence prices the saving at zero. -/
theorem livePairTie_is_not_a_reduction :
    (ExistsLivePairTiePrimitiveDesign ↔ ConsolidatedStrictTripleDesign)
      ∧ (ExistsLivePairTieDesign → ExistsLivePairTiePrimitiveDesign) :=
  ⟨existsLivePairTiePrimitiveDesign_iff_consolidatedStrictTripleDesign,
    existsLivePairTiePrimitiveDesign_of_existsLivePairTieDesign⟩

end Gtz
