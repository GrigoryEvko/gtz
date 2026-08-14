/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Reduction.SignClashParityNarrowing
import Gtz.Quantitative.PairRungRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The sign-clash lattice is a faithful restatement of the cell

`Gtz/Reduction/SignClashCoverage.lean` names four open propositions —
`Gtz.GenericExceptionalSignClash`, `Gtz.OwnSignForcedClash`,
`Gtz.OwnSignForcedClashOnClean` and `Gtz.EraseConsistentForcedClashOnClean` —
and `Gtz/Reduction/SignClashParityNarrowing.lean` adds a fifth,
`Gtz.TraceParityTieClash`.  Each reaches `Gtz.GtzWeighted 6 3` through a landed
one-way theorem, and both modules say in their headers that NO converse is
claimed.

**THIS MODULE PROVES THE FIVE CONVERSES.  ALL FIVE PROPOSITIONS ARE EQUIVALENT
TO `Gtz.GtzWeighted 6 3`.**  The lattice bought a change of vocabulary, not a
reduction of content, and no better bound on any of the five can close the cell.

## The mechanism, in one paragraph

`Gtz.dominates_triple_iff_discriminantSystem` says that a triple of an all-heavy
design dominates exactly when its trace leg at a pivot and its tie leg are
nonnegative.  `Gtz.discriminantTie_eq_excessGap_add_tripleProduct` says the tie
leg is `excessGap + 2·product`.  The first clause of
`Gtz.PhaseFreeData.IsExceptional` says that every trace-leg triple has
`excessGap < 2·|product|`.  Put the three together at a NEGATIVE product: the
modulus is `−product`, the exceptional clause reads `excessGap + 2·product < 0`,
and that IS the tie leg, so the triple does not dominate.  Contrapositive: **at
an exceptional design every dominating triple has a nonnegative pairing
product.**  The extra clause that each of the five propositions carries over
bare domination is therefore free, and the converse of each reduction follows.

This is an equality-plus-sign argument with no margin anywhere, which explains
the exact tightness the external adversary measured on this route: slack in any
of the five would be slack in domination itself, and the tie boundary forbids
that.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.nonneg_atomPairingProduct_of_isExceptional_of_dominates` — **THE
  EXCEPTIONAL SIGN LAW**, the core of the module.
* `Gtz.isForcedMinusTriple_of_isExceptional_of_dominates`,
  `Gtz.isSignClashTriple_of_isExceptional_of_dominates` — the two packaged
  readings.
* `Gtz.dominates_iff_traceParityTie_of_isExceptional` — **THE SHARP POINTWISE
  FORM**: at an exceptional design the three positive conjuncts of
  `Gtz.TraceParityTieClash` characterize domination of that triple.
* `Gtz.traceParityTieClash_of_gtzWeighted_six_three`,
  `Gtz.ownSignForcedClash_of_gtzWeighted_six_three`,
  `Gtz.ownSignForcedClashOnClean_of_gtzWeighted_six_three`,
  `Gtz.eraseConsistentForcedClashOnClean_of_gtzWeighted_six_three`,
  `Gtz.genericExceptionalSignClash_of_gtzWeighted_six_three` — the five
  converses.
* The five equivalences `Gtz.*_iff_gtzWeighted_six_three`, and
  `Gtz.signClashLattice_iff` collecting them.
* `Gtz.sum_weight_mul_weight_mul_pairMinor_erase`,
  `Gtz.exists_pairMinor_gt_one` — the unconditional edge supply, sharpened from
  the shipped `Gtz.exists_pos_pairMinor_of_allHeavy`.

## MEASURED, and recorded here so that no successor repeats it

The narrowing header of `Gtz/Reduction/SignClashParityNarrowing.lean` records a
random-sweep observation that at least `8` of the `20` triples carry a
nonnegative pairing product and at least `16` carry a nonnegative trace leg,
from which `8 + 16 > 20` would make the trace-leg conjunct free by pigeonhole.
**THE TRACE-LEG FLOOR IS FALSE AND THE PIGEONHOLE FAILS.**  An adversarial
search over the parametrization `N = H Hᵀ − diag(weight)` with `Hᵀ H = 1`
reaches `10` trace-leg triples, and reaches all-heavy designs at which NO triple
carries both a nonnegative trace leg and a nonnegative pairing product.  Two
such points were rebuilt over the rationals and recomputed at zero residual: the
projection onto the column space of a rational matrix is rational, so the
refutation needs no square root and no floating point.  At both points exactly
`3` of the `15` pair minors are positive and exactly `1` of the `20` triples
dominates.  The parity floor `8` was not refuted.  Nothing in this paragraph is
kernel fact.

## Vacuity

Nothing here is vacuous.  The pointwise laws are statements about every
exceptional design and every ordered triple of it, and the equivalences are
statements between propositions, both sides of which are open.
-/

namespace Gtz

variable {sizeIndex : ℕ}

/-! ## The exceptional sign law -/

/-- **THE EXCEPTIONAL SIGN LAW.**  At an exceptional all-heavy design every
dominating triple has a NONNEGATIVE pairing product.

Domination hands the trace leg at the pivot and the tie leg
(`Gtz.dominates_triple_iff_discriminantSystem`).  The trace leg feeds the first
clause of exceptionality through the landed
`Gtz.adverseTie_neg_of_isExceptional_of_traceLeg`, which returns
`excessGap − 2·radius < 0`.  At a negative product the radius is `−product`, so
that reads `excessGap + 2·product < 0`, and the split identity
`Gtz.discriminantTie_eq_excessGap_add_tripleProduct` says the left side IS the
tie leg — which domination made nonnegative. -/
theorem nonneg_atomPairingProduct_of_isExceptional_of_dominates
    (D : WeightedDesign sizeIndex 3) (hheavy : AllHeavy D)
    (hexceptional : (phaseFreeOfDesign D).IsExceptional)
    {first second third : Fin sizeIndex}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hdominates : Dominates D {first, second, third}) :
    0 ≤ atomPairing D first second * atomPairing D first third
      * atomPairing D second third := by
  obtain ⟨htrace, htie⟩ :=
    (dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird
      hsecondThird (hheavy first)).mp hdominates
  have hadverse := adverseTie_neg_of_isExceptional_of_traceLeg D hexceptional
    hfirstSecond hfirstThird hsecondThird (Or.inl htrace)
  rw [discriminantTie_eq_excessGap_add_tripleProduct] at htie
  rcases le_or_gt 0 (atomPairing D first second * atomPairing D first third
      * atomPairing D second third) with hnonneg | hnegative
  · exact hnonneg
  · exfalso
    have hradius : tripleRadius D first second third
        = -(atomPairing D first second * atomPairing D first third
            * atomPairing D second third) := by
      show |atomPairing D first second * atomPairing D first third
          * atomPairing D second third| = _
      exact abs_of_neg hnegative
    rw [hradius] at hadverse
    linarith

/-- **A DOMINATING TRIPLE OF AN EXCEPTIONAL DESIGN IS FORCED-MINUS.**  The three
clauses of `Gtz.IsForcedMinusTriple` are the trace leg, the tie leg read at the
plus torsion sign, and the strict adverse band.  Domination supplies the first
two through the sign law above, and the third is free. -/
theorem isForcedMinusTriple_of_isExceptional_of_dominates
    (D : WeightedDesign sizeIndex 3) (hheavy : AllHeavy D)
    (hexceptional : (phaseFreeOfDesign D).IsExceptional)
    {first second third : Fin sizeIndex}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hdominates : Dominates D {first, second, third}) :
    IsForcedMinusTriple D first second third := by
  obtain ⟨htrace, htie⟩ :=
    (dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird
      hsecondThird (hheavy first)).mp hdominates
  refine isForcedMinusTriple_of_isExceptional_of_parity D hexceptional
    hfirstSecond hfirstThird hsecondThird (Or.inl htrace)
    (nonneg_atomPairingProduct_of_isExceptional_of_dominates D hheavy
      hexceptional hfirstSecond hfirstThird hsecondThird hdominates) ?_
  rw [← discriminantTie_eq_excessGap_add_tripleProduct]
  exact htie

/-- **A DOMINATING TRIPLE OF AN EXCEPTIONAL DESIGN IS A SIGN-CLASH TRIPLE.**
The band clause is the squeeze: the product is nonnegative, the tie leg pins
`−2·product ≤ excessGap`, and exceptionality pins `excessGap < 2·product`, so on
the negative branch the square bound is the product of two nonnegative
factors. -/
theorem isSignClashTriple_of_isExceptional_of_dominates
    (D : WeightedDesign sizeIndex 3) (hheavy : AllHeavy D)
    (hexceptional : (phaseFreeOfDesign D).IsExceptional)
    {first second third : Fin sizeIndex}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hdominates : Dominates D {first, second, third}) :
    IsSignClashTriple D first second third := by
  obtain ⟨htrace, htie⟩ :=
    (dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird
      hsecondThird (hheavy first)).mp hdominates
  have hproduct := nonneg_atomPairingProduct_of_isExceptional_of_dominates D
    hheavy hexceptional hfirstSecond hfirstThird hsecondThird hdominates
  rw [discriminantTie_eq_excessGap_add_tripleProduct] at htie
  refine ⟨htrace, hproduct, ?_⟩
  rcases le_or_gt 0 (excessGap D first second third) with hgap | hgap
  · exact Or.inl hgap
  · right
    nlinarith [htie, hgap, hproduct]

/-- **THE SHARP POINTWISE FORM.**  At an exceptional all-heavy design a triple
of distinct atoms dominates EXACTLY when it carries the three positive conjuncts
of `Gtz.TraceParityTieClash`: a nonnegative trace leg, a nonnegative pairing
product and a nonnegative tie leg.  The forward direction is the sign law; the
backward direction is the discriminant system read at the pivot that carries the
trace leg. -/
theorem dominates_iff_traceParityTie_of_isExceptional
    (D : WeightedDesign sizeIndex 3) (hheavy : AllHeavy D)
    (hexceptional : (phaseFreeOfDesign D).IsExceptional)
    {first second third : Fin sizeIndex}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Dominates D {first, second, third}
      ↔ (0 ≤ discriminantTrace D first second third
          ∧ 0 ≤ atomPairing D first second * atomPairing D first third
              * atomPairing D second third
          ∧ 0 ≤ excessGap D first second third
              + 2 * (atomPairing D first second * atomPairing D first third
                * atomPairing D second third)) := by
  rw [dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird
    hsecondThird (hheavy first), discriminantTie_eq_excessGap_add_tripleProduct]
  refine ⟨fun hsystem => ⟨hsystem.1, ?_, hsystem.2⟩, fun hthree => ⟨hthree.1, hthree.2.2⟩⟩
  refine nonneg_atomPairingProduct_of_isExceptional_of_dominates D hheavy
    hexceptional hfirstSecond hfirstThird hsecondThird ?_
  rw [dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird
    hsecondThird (hheavy first), discriminantTie_eq_excessGap_add_tripleProduct]
  exact hsystem

/-! ## The ordered dominating triple -/

/-- The cell hands an UNORDERED dominating three-set; every statement of the
lattice wants three distinct ordered atoms.  `Finset.card_eq_three` converts. -/
theorem exists_ordered_dominates_of_gtzWeighted_six_three
    (hcell : GtzWeighted 6 3) (D : WeightedDesign 6 3) :
    ∃ first second third : Fin 6,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ Dominates D {first, second, third} := by
  obtain ⟨carrier, hcard, hdominates⟩ := hcell D
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcarrier⟩ :=
    Finset.card_eq_three.mp hcard
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hcarrier ▸ hdominates⟩

/-! ## The five converses -/

/-- **CONVERSE ONE.**  The cell gives the narrowed proposition: its dominating
triple carries the trace leg and the tie leg by the discriminant system, and the
pairing product by the exceptional sign law. -/
theorem traceParityTieClash_of_gtzWeighted_six_three (hcell : GtzWeighted 6 3) :
    TraceParityTieClash := by
  intro D hheavy _hgeneric hexceptional
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hdominates⟩ := exists_ordered_dominates_of_gtzWeighted_six_three hcell D
  obtain ⟨htrace, hparity, htie⟩ :=
    (dominates_iff_traceParityTie_of_isExceptional D hheavy hexceptional
      hfirstSecond hfirstThird hsecondThird).mp hdominates
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    Or.inl htrace, hparity, htie⟩

/-- **CONVERSE TWO.**  The cell gives the sigma form. -/
theorem ownSignForcedClash_of_gtzWeighted_six_three (hcell : GtzWeighted 6 3) :
    OwnSignForcedClash := by
  intro D hheavy _hgeneric hexceptional
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hdominates⟩ := exists_ordered_dominates_of_gtzWeighted_six_three hcell D
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    isForcedMinusTriple_of_isExceptional_of_dominates D hheavy hexceptional
      hfirstSecond hfirstThird hsecondThird hdominates,
    nonneg_atomPairingProduct_of_isExceptional_of_dominates D hheavy hexceptional
      hfirstSecond hfirstThird hsecondThird hdominates⟩

/-- **CONVERSE THREE.**  The cell gives the clean sigma form, which only adds a
hypothesis to the sigma form. -/
theorem ownSignForcedClashOnClean_of_gtzWeighted_six_three
    (hcell : GtzWeighted 6 3) : OwnSignForcedClashOnClean :=
  fun D hheavy hgeneric hexceptional _hclean =>
    ownSignForcedClash_of_gtzWeighted_six_three hcell D hheavy hgeneric hexceptional

/-- **CONVERSE FOUR.**  The cell gives the CSP form.  On the flip-clean locus
every erase-consistent reading IS the design's own
(`Gtz.eraseConsistentAssignment_eq_own`), so the sigma witness transfers to the
quantified reading through the torsion bridge. -/
theorem eraseConsistentForcedClashOnClean_of_gtzWeighted_six_three
    (hcell : GtzWeighted 6 3) : EraseConsistentForcedClashOnClean := by
  intro D hheavy hgeneric hexceptional hclean assignment hconsistent
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hforced, hproduct⟩ :=
    ownSignForcedClash_of_gtzWeighted_six_three hcell D hheavy hgeneric hexceptional
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hforced, ?_⟩
  have hthirdMember : third ∈ (Finset.univ.erase first).erase second :=
    Finset.mem_erase.mpr ⟨hsecondThird.symm,
      Finset.mem_erase.mpr ⟨hfirstThird.symm, Finset.mem_univ third⟩⟩
  rw [eraseConsistentAssignment_eq_own D hclean assignment hconsistent
    first second third hfirstSecond hthirdMember,
    edgeTripleValue_eq_atomPairingProduct]
  exact hproduct

/-- **CONVERSE FIVE.**  The cell gives the Phase-2 closing shape. -/
theorem genericExceptionalSignClash_of_gtzWeighted_six_three
    (hcell : GtzWeighted 6 3) : GenericExceptionalSignClash := by
  intro D hheavy _hgeneric hexceptional
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hdominates⟩ := exists_ordered_dominates_of_gtzWeighted_six_three hcell D
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    isSignClashTriple_of_isExceptional_of_dominates D hheavy hexceptional
      hfirstSecond hfirstThird hsecondThird hdominates⟩

/-! ## The five equivalences — THE VERDICT -/

/-- **THE NARROWED PROPOSITION IS THE CELL.** -/
theorem traceParityTieClash_iff_gtzWeighted_six_three :
    TraceParityTieClash ↔ GtzWeighted 6 3 :=
  ⟨gtzWeighted_six_three_of_traceParityTieClash,
    traceParityTieClash_of_gtzWeighted_six_three⟩

/-- **THE SIGMA FORM IS THE CELL.** -/
theorem ownSignForcedClash_iff_gtzWeighted_six_three :
    OwnSignForcedClash ↔ GtzWeighted 6 3 :=
  ⟨gtzWeighted_six_three_of_ownSignForcedClash,
    ownSignForcedClash_of_gtzWeighted_six_three⟩

/-- **THE CLEAN SIGMA FORM IS THE CELL** — so the flip-clean restriction buys
nothing either. -/
theorem ownSignForcedClashOnClean_iff_gtzWeighted_six_three :
    OwnSignForcedClashOnClean ↔ GtzWeighted 6 3 :=
  ⟨gtzWeighted_six_three_of_ownSignForcedClashOnClean,
    ownSignForcedClashOnClean_of_gtzWeighted_six_three⟩

/-- **THE CSP FORM IS THE CELL** — so the parametric-LP attack on the forced
system is not a reduction of the cell but a restatement of it. -/
theorem eraseConsistentForcedClashOnClean_iff_gtzWeighted_six_three :
    EraseConsistentForcedClashOnClean ↔ GtzWeighted 6 3 :=
  ⟨gtzWeighted_six_three_of_eraseConsistentForcedClashOnClean,
    eraseConsistentForcedClashOnClean_of_gtzWeighted_six_three⟩

/-- **THE PHASE-2 CLOSING SHAPE IS THE CELL.** -/
theorem genericExceptionalSignClash_iff_gtzWeighted_six_three :
    GenericExceptionalSignClash ↔ GtzWeighted 6 3 :=
  ⟨gtzWeighted_six_three_of_genericExceptionalSignClash,
    genericExceptionalSignClash_of_gtzWeighted_six_three⟩

/-- **THE WHOLE LATTICE COLLAPSES.**  The five named propositions of the
sign-clash route and the weighted cell at `(6,3)` are one proposition in five
vocabularies.  A successor must not staff a "narrowing" inside this lattice: any
such statement is either strictly stronger than the cell, and thus not a
reduction, or equivalent to it, and thus not progress. -/
theorem signClashLattice_iff :
    (TraceParityTieClash ↔ GtzWeighted 6 3)
      ∧ (OwnSignForcedClash ↔ GtzWeighted 6 3)
      ∧ (OwnSignForcedClashOnClean ↔ GtzWeighted 6 3)
      ∧ (EraseConsistentForcedClashOnClean ↔ GtzWeighted 6 3)
      ∧ (GenericExceptionalSignClash ↔ GtzWeighted 6 3) :=
  ⟨traceParityTieClash_iff_gtzWeighted_six_three,
    ownSignForcedClash_iff_gtzWeighted_six_three,
    ownSignForcedClashOnClean_iff_gtzWeighted_six_three,
    eraseConsistentForcedClashOnClean_iff_gtzWeighted_six_three,
    genericExceptionalSignClash_iff_gtzWeighted_six_three⟩

/-- The deficit-free residue of `Gtz.SignClashCoverage` is the cell too: the
deficit-witnessed designs are covered by a kernel bridge, so the residue carries
all of the content. -/
theorem deficitFreeResidue_iff_gtzWeighted_six_three :
    (∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
        (phaseFreeOfDesign D).IsExceptional → ¬ HasForcedBoxDeficitEdge D →
        ∃ pivot pairFirst pairSecond : Fin 6,
          pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ IsSignClashTriple D pivot pairFirst pairSecond)
      ↔ GtzWeighted 6 3 := by
  refine ⟨fun hresidue => gtzWeighted_six_three_of_genericExceptionalSignClash
    (genericExceptionalSignClash_of_forall_without_deficit_signClash hresidue),
    fun hcell D hheavy hgeneric hexceptional _hdeficit =>
      genericExceptionalSignClash_of_gtzWeighted_six_three hcell D hheavy hgeneric
        hexceptional⟩

/-! ## The unconditional edge supply, sharpened -/

/-- **THE PAIR RUNG IN ROW-AGGREGATE FORM.**  The doubly weighted total of the
`2×2` gap minors over ordered pairs of distinct atoms is `1` plus the correction
`Σ w² (2·leverage − 1)`.  This is the shipped row law
`Gtz.sum_erase_weight_mul_pairMinor_row` averaged against the weights, in the
erase index shape the corollary below consumes. -/
theorem sum_weight_mul_weight_mul_pairMinor_erase (D : WeightedDesign sizeIndex 3) :
    (∑ center, ∑ other ∈ Finset.univ.erase center,
        D.weight center * (D.weight other * pairMinor D center other))
      = 1 + ∑ center, D.weight center ^ 2
          * (2 * leverageOf (D.atom center) - 1) := by
  have hstep : ∀ center : Fin sizeIndex,
      (∑ other ∈ Finset.univ.erase center,
          D.weight center * (D.weight other * pairMinor D center other))
        = D.weight center * leverageOf (D.atom center) - 2 * D.weight center
          + D.weight center ^ 2 * (2 * leverageOf (D.atom center) - 1) := by
    intro center
    rw [← Finset.mul_sum, sum_erase_weight_mul_pairMinor_row D center]
    ring
  rw [Finset.sum_congr rfl fun center _ => hstep center, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_weight_mul_leverage D, ← Finset.mul_sum,
    D.weight_sum_one]
  norm_num

/-- The same total with the minors replaced by one: the off-diagonal weight
mass is `1` minus the diagonal square mass. -/
theorem sum_weight_mul_weight_erase (D : WeightedDesign sizeIndex 3) :
    (∑ center, ∑ other ∈ Finset.univ.erase center,
        D.weight center * D.weight other)
      = 1 - ∑ center, D.weight center ^ 2 := by
  have hstep : ∀ center : Fin sizeIndex,
      (∑ other ∈ Finset.univ.erase center, D.weight center * D.weight other)
        = D.weight center - D.weight center ^ 2 := by
    intro center
    rw [← Finset.mul_sum]
    have hsplit : (∑ other ∈ Finset.univ.erase center, D.weight other)
        + D.weight center = ∑ other, D.weight other :=
      Finset.sum_erase_add _ _ (Finset.mem_univ center)
    rw [D.weight_sum_one] at hsplit
    have : (∑ other ∈ Finset.univ.erase center, D.weight other)
        = 1 - D.weight center := by linarith
    rw [this]
    ring
  rw [Finset.sum_congr rfl fun center _ => hstep center, Finset.sum_sub_distrib,
    D.weight_sum_one]

/-- **THE EDGE SUPPLY EXCEEDS ONE.**  Every all-heavy rank-three design owns two
distinct atoms whose `2×2` gap minor is STRICTLY GREATER THAN ONE.  This sharpens
the shipped `Gtz.exists_pos_pairMinor_of_allHeavy`, which only reaches a positive
minor: the pair rung totals `1 + Σ w²(2·leverage − 1)` while the weight mass it
is measured against totals only `1 − Σ w²`, and the two square masses have the
same sign, so a ceiling of one on every minor is arithmetically impossible.

This is the strongest unconditional edge statement the route supplies.  It does
NOT extend to a trace-leg triple: the trace leg needs two minors at a shared
pivot, and the module header records an all-heavy design at which only three of
the fifteen minors are positive. -/
theorem exists_pairMinor_gt_one {D : WeightedDesign sizeIndex 3}
    (hheavy : AllHeavy D) :
    ∃ center other : Fin sizeIndex, center ≠ other ∧ 1 < pairMinor D center other := by
  by_contra hnone
  have hbound : ∀ center : Fin sizeIndex, ∀ other ∈ Finset.univ.erase center,
      D.weight center * (D.weight other * pairMinor D center other)
        ≤ D.weight center * D.weight other := by
    intro center other hother
    have hdistinct : center ≠ other := ((Finset.mem_erase.mp hother).1).symm
    have hle : pairMinor D center other ≤ 1 := by
      by_contra hgreater
      exact hnone ⟨center, other, hdistinct, not_le.mp hgreater⟩
    have houter := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hle (D.weight_pos other).le)
      (D.weight_pos center).le
    calc D.weight center * (D.weight other * pairMinor D center other)
        ≤ D.weight center * (D.weight other * 1) := houter
      _ = D.weight center * D.weight other := by ring
  have hsum := Finset.sum_le_sum (fun center (_ : center ∈ Finset.univ) =>
    Finset.sum_le_sum (hbound center))
  rw [sum_weight_mul_weight_mul_pairMinor_erase D, sum_weight_mul_weight_erase D] at hsum
  have hsquare : (0 : ℝ) < ∑ center, D.weight center ^ 2
      * (2 * leverageOf (D.atom center))
      := by
    have hsize : 0 < sizeIndex := by
      by_contra hzero
      have hempty : sizeIndex = 0 := by omega
      subst hempty
      have hone := D.weight_sum_one
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hone
      exact absurd hone (by norm_num)
    have hne : (Finset.univ : Finset (Fin sizeIndex)).Nonempty :=
      ⟨⟨0, hsize⟩, Finset.mem_univ _⟩
    refine Finset.sum_pos (fun center _ => ?_) hne
    have hleverage := hheavy center
    have hweight := D.weight_pos center
    nlinarith [hweight, hleverage]
  have hsplit : (∑ center, D.weight center ^ 2 * (2 * leverageOf (D.atom center) - 1))
      + ∑ center, D.weight center ^ 2
      = ∑ center, D.weight center ^ 2 * (2 * leverageOf (D.atom center)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun center _ => by ring
  linarith

end Gtz
