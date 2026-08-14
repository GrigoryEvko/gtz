import Gtz.Reduction.SignClashCoverage
import Gtz.Quantitative.SwitchingTwoGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The parity narrowing of the sign-clash route — one clause of three is free

`Gtz.OwnSignForcedClash` asks every generic all-heavy exceptional design for a
forced-minus triple whose own pairing product is nonnegative.  A forced-minus
triple carries THREE clauses: a nonnegative trace leg, the lower tie band
`0 ≤ excessGap + 2·radius`, and the strict adverse band
`excessGap − 2·radius < 0`.

**THE THIRD CLAUSE IS FREE.**  The first clause of
`Gtz.PhaseFreeData.IsExceptional` says that no trace-leg triple is sign-blind
good, and `Gtz.isSignBlindGoodTriple_iff_adverseTie_nonneg` says that sign-blind
good IS `0 ≤ excessGap − 2·radius`.  Thus at an exceptional design every
trace-leg triple already satisfies the strict adverse band, and the third clause
costs a prover nothing.

**THE SECOND CLAUSE COLLAPSES ON THE PARITY SET.**  At a triple of nonnegative
parity the radius IS the product, thus the lower tie band is the tie leg
`0 ≤ excessGap + 2·product`.

Together the route narrows to ONE proposition with three positive conjuncts and
no negation: some triple carries a nonnegative trace leg, a nonnegative pairing
product, and a nonnegative tie leg.  The middle conjunct alone is the landed
unconditional `Gtz.exists_positiveParity_triple`, thus the open content of the
whole sign-clash route is exactly the INTERSECTION of the parity set with the
trace-and-tie set.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.isSignBlindGoodTriple_phaseFreeOfDesign_iff` — the sign-blind bridge
  between the phase-free reading and the design.
* `Gtz.adverseTie_neg_of_isExceptional_of_traceLeg` — **THE THIRD CLAUSE IS
  FREE** at an exceptional design.
* `Gtz.isForcedMinusTriple_of_isExceptional_of_parity` — a trace-leg triple of
  nonnegative parity and nonnegative tie leg IS forced-minus.
* `Gtz.TraceParityTieClash` — **THE NARROWED PROPOSITION.**
* `Gtz.ownSignForcedClash_of_traceParityTieClash`,
  `Gtz.gtzWeighted_six_three_of_traceParityTieClash` — the narrowing and its
  composition to the cell.

## Vacuity

Nothing here is vacuous: the bridges are unconditional statements about every
weighted design.  The narrowed proposition quantifies over generic all-heavy
exceptional designs, of which none is known to exist.
-/

namespace Gtz

variable {sizeIndex : ℕ}

/-! ## The sign-blind bridge -/

/-- **THE SIGN-BLIND BRIDGE.**  The phase-free sign-blind cell at a design's
image is the design's own sign-blind cell.  The phase-free form squares the
Bargmann triangle against the squared pairings, and the torsion identity
`Gtz.phaseFreeOfDesign_triangle_sq` turns that square back into the modulus. -/
theorem isSignBlindGoodTriple_phaseFreeOfDesign_iff (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    (phaseFreeOfDesign D).IsSignBlindGoodTriple first second third
      ↔ IsSignBlindGoodTriple D first second third := by
  have hradius := abs_triangle_phaseFreeOfDesign D first second third
  have hnonneg : 0 ≤ tripleRadius D first second third :=
    tripleRadius_nonneg D first second third
  have hsquare : (phaseFreeOfDesign D).triangle first second third ^ 2
      = tripleRadius D first second third ^ 2 := by
    rw [← hradius, sq_abs]
  have hval : tripleRadius D first second third
      = |atomPairing D first second * atomPairing D first third
          * atomPairing D second third| := rfl
  rw [PhaseFreeData.IsSignBlindGoodTriple,
    isSignBlindGoodTriple_iff_adverseTie_nonneg,
    ← phaseFreeOfDesign_triangle_sq D first second third,
    excessGap_phaseFreeOfDesign, hsquare, ← hval]
  constructor
  · rintro ⟨hgap, hsq⟩
    nlinarith [hnonneg, hgap, hsq]
  · intro hadverse
    exact ⟨by linarith, by nlinarith [hnonneg, hadverse]⟩

/-! ## The third clause is free -/

/-- **THE THIRD FORCED-MINUS CLAUSE IS FREE.**  At an exceptional design every
triple with a nonnegative trace leg sits strictly inside the adverse band, thus
it already satisfies the strict clause of `Gtz.IsForcedMinusTriple`. -/
theorem adverseTie_neg_of_isExceptional_of_traceLeg (D : WeightedDesign sizeIndex 3)
    (hexceptional : (phaseFreeOfDesign D).IsExceptional)
    {first second third : Fin sizeIndex}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (htrace : 0 ≤ discriminantTrace D first second third
      ∨ 0 ≤ discriminantTrace D second first third
      ∨ 0 ≤ discriminantTrace D third first second) :
    excessGap D first second third
      - 2 * tripleRadius D first second third < 0 := by
  have hleg : (phaseFreeOfDesign D).HasNonnegTraceLeg first second third :=
    (hasNonnegTraceLeg_phaseFreeOfDesign_iff D first second third).mpr htrace
  have hnot := hexceptional.1 first second third hfirstSecond hfirstThird
    hsecondThird hleg
  rw [isSignBlindGoodTriple_phaseFreeOfDesign_iff,
    isSignBlindGoodTriple_iff_adverseTie_nonneg] at hnot
  have hval : tripleRadius D first second third
      = |atomPairing D first second * atomPairing D first third
          * atomPairing D second third| := rfl
  rw [hval]
  linarith [not_le.mp hnot]

/-- **THE FORCED-MINUS READING OF A PARITY TRIPLE.**  At an exceptional design a
triple with a nonnegative trace leg, a nonnegative pairing product and a
nonnegative tie leg is a forced-minus triple: the radius is the product, thus
the lower band IS the tie leg, and the strict band is free. -/
theorem isForcedMinusTriple_of_isExceptional_of_parity (D : WeightedDesign sizeIndex 3)
    (hexceptional : (phaseFreeOfDesign D).IsExceptional)
    {first second third : Fin sizeIndex}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (htrace : 0 ≤ discriminantTrace D first second third
      ∨ 0 ≤ discriminantTrace D second first third
      ∨ 0 ≤ discriminantTrace D third first second)
    (hparity : 0 ≤ atomPairing D first second * atomPairing D first third
      * atomPairing D second third)
    (htie : 0 ≤ excessGap D first second third
      + 2 * (atomPairing D first second * atomPairing D first third
        * atomPairing D second third)) :
    IsForcedMinusTriple D first second third := by
  have hradius : tripleRadius D first second third
      = atomPairing D first second * atomPairing D first third
        * atomPairing D second third := by
    show |atomPairing D first second * atomPairing D first third
        * atomPairing D second third| = _
    exact abs_of_nonneg hparity
  refine ⟨htrace, ?_, ?_⟩
  · rw [hradius]; exact htie
  · exact adverseTie_neg_of_isExceptional_of_traceLeg D hexceptional
      hfirstSecond hfirstThird hsecondThird htrace

/-! ## The narrowed proposition -/

/-- **THE NARROWED PROPOSITION — OPEN.**  Every generic all-heavy exceptional
design carries a triple with a nonnegative trace leg, a nonnegative pairing
product and a nonnegative tie leg.  Three positive conjuncts, no negation, and
the middle one is the landed unconditional `Gtz.exists_positiveParity_triple`:
the open content of the sign-clash route is exactly the intersection of the
parity set with the trace-and-tie set. -/
def TraceParityTieClash : Prop :=
  ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
    (phaseFreeOfDesign D).IsExceptional →
    ∃ first second third : Fin 6,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ (0 ≤ discriminantTrace D first second third
            ∨ 0 ≤ discriminantTrace D second first third
            ∨ 0 ≤ discriminantTrace D third first second)
        ∧ 0 ≤ atomPairing D first second * atomPairing D first third
            * atomPairing D second third
        ∧ 0 ≤ excessGap D first second third
            + 2 * (atomPairing D first second * atomPairing D first third
              * atomPairing D second third)

/-- **THE NARROWING.**  The narrowed proposition gives the sigma form: the
third forced-minus clause is free at an exceptional design, and the lower band
collapses to the tie leg on the parity set. -/
theorem ownSignForcedClash_of_traceParityTieClash
    (hnarrow : TraceParityTieClash) : OwnSignForcedClash := by
  intro D hheavy hgeneric hexceptional
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    htrace, hparity, htie⟩ := hnarrow D hheavy hgeneric hexceptional
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    isForcedMinusTriple_of_isExceptional_of_parity D hexceptional hfirstSecond
      hfirstThird hsecondThird htrace hparity htie, hparity⟩

/-- **THE COMPOSITION TO THE CELL.**  The narrowed proposition closes the
weighted cell through the landed sigma chain. -/
theorem gtzWeighted_six_three_of_traceParityTieClash
    (hnarrow : TraceParityTieClash) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_ownSignForcedClash
    (ownSignForcedClash_of_traceParityTieClash hnarrow)

end Gtz
