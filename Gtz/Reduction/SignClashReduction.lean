/-
# The sign-clash reduction: the Phase-2 closing shape as one named proposition

The Phase-2 measurement campaign (gtz-p2, exact arithmetic throughout) ran four
independent lanes against the `(6,3)` residue and joined their data sets for the
first time.  The joined verdict singles out ONE closing shape: at every generic
all-heavy design whose phase-free image is exceptional, some ordered triple was
measured to carry a nonnegative trace leg, a nonnegative (coherent) pairing
product, and a sign-blind gap that is either nonnegative or middle-band.  Such a
triple DOMINATES — that implication is a kernel theorem, proved below — so the
measured shape, if proved, closes the cell.

This module lands the shape as a named open proposition in shipped vocabulary
(`Gtz.GenericExceptionalSignClash`), the reduction lemma that makes each witness
dominate (`Gtz.dominates_of_isSignClashTriple`), and the composition down to the
open cell (`Gtz.gtzWeighted_six_three_of_genericExceptionalSignClash`).  It
follows the precedent of `Gtz/Quantitative/ResidueReduction.lean`: the named
proposition is OPEN; only the reductions around it are theorems.

## The reduction chain

`Gtz.gtzWeighted_six_three_of_genericExceptionalSignClash` composes three
shipped mechanisms:

* off the residue, `Gtz.exists_dominates_of_not_isExceptional` produces a
  dominating triple unconditionally;
* on the residue, the hypothesis supplies a sign-clash triple, and
  `Gtz.dominates_of_isSignClashTriple` turns it into domination: the split
  identity `Gtz.discriminantTie_eq_excessGap_add_tripleProduct` writes the tie
  leg as the gap plus twice the pairing product, either branch of the band
  clause forces the tie leg nonnegative, and
  `Gtz.dominates_triple_iff_discriminantSystem` fires at the heavy pivot;
* the genericity reduction `Gtz.gtzWeighted_of_forall_generic_dominates`
  discharges the non-generic designs.

## What the evidence is, and what it is NOT

The evidence for `Gtz.GenericExceptionalSignClash` is EXTERNAL MEASUREMENT, not
proof, and none of it is kernel-checked here:

* at all `118` exceptional points examined (the `112` exact rational datum-level
  residue points and the `6` design-image witnesses of the residue-reduction
  campaign), the total-failure forced sign system is infeasible in exact
  rational arithmetic, and `9651` exact admissible data showed zero violations
  of the equivalent forced-pattern reading;
* the quantifier domain is measured to be INHABITED — exact rational all-heavy
  generic designs with exceptional phase-free image exist (four were found among
  three hundred balanced-window samples) — so the proposition is not made true
  by an empty hypothesis so far as measurement can tell, and no emptiness claim
  is made or used;
* THE HARD-CORE CAVEAT, binding on any attempt to prove the proposition: at ten
  of the `112` datum-level residue points the measured infeasibility is
  MAGNITUDE-carried — it dies under in-sector perturbation of the moduli — so a
  purely sector-combinatorial argument cannot prove this proposition; any proof
  must consume the actual erase magnitudes.

Scope honesty, per the genericity-reduction module header: genericity narrows
quantifiers only — it manufactures no margin, and the failing set may hug the
tie boundaries arbitrarily closely.  No equivalence is claimed anywhere in this
module: the composition is one-way sufficiency, and whether the proposition is
strictly weaker than the cell is not addressed.
-/
import Mathlib
import Gtz.Quantitative.GoodTripleGraph
import Gtz.Quantitative.SixThreeCruxSigns
import Gtz.Quantitative.VertexExclusion
import Gtz.Reduction.GenericityReduction

namespace Gtz

/-! ## The witness shape -/

/-- **A sign-clash triple**: an ordered triple whose trace leg is nonnegative,
whose pairing product is nonnegative (coherent), and whose sign-blind gap
either is nonnegative or is middle-band (gap squared at most four times the
pairing product squared).

The first band branch together with coherence is the territory of the shipped
cell `Gtz.dominates_of_coherentPairings`; the second branch is the genuinely
new content — the middle band, where the tie leg still closes because the
coherent product term wins, and the trace leg is a genuine extra hypothesis
rather than a consequence of the gap.  Unlike `Gtz.IsSignBlindGoodTriple`,
this shape READS the sign of the pairing product: it is exactly the
"forced-minus triple whose actual sign is plus" object of the Phase-2
measurement, written in polynomial vocabulary. -/
def IsSignClashTriple {m : ℕ} (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) : Prop :=
  0 ≤ discriminantTrace D pivot pairFirst pairSecond
    ∧ 0 ≤ atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
        * atomPairing D pairFirst pairSecond
    ∧ (0 ≤ excessGap D pivot pairFirst pairSecond
        ∨ excessGap D pivot pairFirst pairSecond ^ 2
            ≤ 4 * (atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
                * atomPairing D pairFirst pairSecond) ^ 2)

/-- **THE REDUCTION LEMMA.**  On an all-heavy design, a sign-clash triple of
distinct atoms dominates.  The tie leg is the split identity
`Gtz.discriminantTie_eq_excessGap_add_tripleProduct`: on the first band branch
it is a sum of two nonnegatives; on the middle-band branch, a negative tie leg
would make both `-gap - 2 * product` and `-gap + 2 * product` positive, whose
product contradicts the band bound.  The trace leg is the first clause, and
`Gtz.dominates_triple_iff_discriminantSystem` finishes at the heavy pivot. -/
theorem dominates_of_isSignClashTriple {m : ℕ} {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) {pivot pairFirst pairSecond : Fin m}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond)
    (hclash : IsSignClashTriple D pivot pairFirst pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  obtain ⟨htrace, hcoherent, hband⟩ := hclash
  have htie : 0 ≤ discriminantTie D pivot pairFirst pairSecond := by
    rw [discriminantTie_eq_excessGap_add_tripleProduct]
    rcases hband with hgapNonneg | hbandSq
    · linarith
    · by_contra hnegTie
      push Not at hnegTie
      have hdiffPos : 0 < -excessGap D pivot pairFirst pairSecond
          - 2 * (atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
              * atomPairing D pairFirst pairSecond) := by linarith
      have hsumPos : 0 < -excessGap D pivot pairFirst pairSecond
          + 2 * (atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
              * atomPairing D pairFirst pairSecond) := by linarith
      nlinarith [mul_pos hdiffPos hsumPos]
  exact (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
    hpairDistinct (hheavy pivot)).mpr ⟨htrace, htie⟩

/-! ## The named proposition -/

/-- **THE PHASE-2 CLOSING SHAPE — OPEN.**  Every generic all-heavy design whose
phase-free image is exceptional carries a sign-clash triple.

This proposition is NOT proved here and no equivalence with the cell is
claimed.  Its evidence is external exact-arithmetic measurement (module
header): the forced sign system is infeasible at all `118` exceptional points
examined, which by the sign dictionary is the same event as some trace-class
triple carrying a nonnegative pairing product in the forced band.  The
hypothesis set is measured inhabited, so the proposition is not vacuous so far
as measurement can tell — but no design-level exceptional witness is
kernel-checked, exactly as in the residue-reduction module header.  The
hard-core caveat binds any proof attempt: ten of the datum-level residue
points are magnitude-carried, so the erase magnitudes must enter. -/
def GenericExceptionalSignClash : Prop :=
  ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
    (phaseFreeOfDesign D).IsExceptional →
    ∃ pivot pairFirst pairSecond : Fin 6,
      pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ IsSignClashTriple D pivot pairFirst pairSecond

/-! ## The composition down to the open cell -/

/-- **THE SUFFICIENCY.**  The Phase-2 closing shape implies the open cell:
generic designs split on exceptionality of their phase-free image — on the
residue the sign-clash witness dominates by the reduction lemma, off it
`Gtz.exists_dominates_of_not_isExceptional` dominates unconditionally — and
`Gtz.gtzWeighted_of_forall_generic_dominates` discharges the rest.  Through
the shipped hub (`Gtz.forall_gtzOriginal_rank_three_iff_exceptionalDesignsDominate`
and its siblings), proving `Gtz.GenericExceptionalSignClash` would settle
rank-three GTZ at every ambient size.  One-way only: no converse is claimed. -/
theorem gtzWeighted_six_three_of_genericExceptionalSignClash
    (hclash : GenericExceptionalSignClash) : GtzWeighted 6 3 := by
  apply gtzWeighted_of_forall_generic_dominates
  intro D hheavy hgeneric
  by_cases hexceptional : (phaseFreeOfDesign D).IsExceptional
  · obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      hwitness⟩ := hclash D hheavy hgeneric hexceptional
    exact ⟨{pivot, pairFirst, pairSecond},
      card_triple_eq_three hpivotFirst hpivotSecond hpairDistinct,
      dominates_of_isSignClashTriple hheavy hpivotFirst hpivotSecond hpairDistinct
        hwitness⟩
  · exact exists_dominates_of_not_isExceptional D hheavy (by norm_num) hexceptional

end Gtz
