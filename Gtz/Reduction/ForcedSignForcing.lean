/-
# Forced-minus triples and the sign forcing layer

The Phase-2 landing (`Gtz/Reduction/SignClashReduction.lean`) reduced the open
cell to `Gtz.GenericExceptionalSignClash`: every generic all-heavy exceptional
design carries a sign-clash triple.  This module lands the FORCING layer under
that proposition — the dictionary steps that turn TOTAL FAILURE into sign
information, in shipped vocabulary.

* `Gtz.IsForcedMinusTriple` is the canonical FORCED_MINUS predicate: some
  pivot of the triple carries a nonnegative trace leg, the PLUS reading of
  the tie is admissible (`0 ≤ excessGap + 2·tripleRadius`), and the MINUS
  reading fails (`excessGap − 2·tripleRadius < 0`).  Through the split
  identity `Gtz.discriminantTie_eq_excessGap_add_tripleProduct` the two
  readings are exactly the tie leg at the two torsion signs of the pairing
  product, so a forced-minus triple dominates when its product is
  nonnegative and fails when it is negative.  This is the `failsAt`
  semantics of the external Phase-2/Phase-3 measurement campaign,
  reproduced there at all `431` exact corpus points (external evidence,
  not kernel-checked).  The phase-free trace clause bridges definitionally:
  `Gtz.hasNonnegTraceLeg_phaseFreeOfDesign_iff`.

* THE FORCING BRIDGE
  (`Gtz.exists_isSignClashTriple_of_forcedMinus_of_nonneg_product`): a
  forced-minus triple whose pairing product is NONNEGATIVE yields an ordered
  sign-clash triple on the same three atoms, pivoted at whichever leg
  carries the nonnegative trace.  Pure arithmetic on the two tie readings
  plus the shipped `S₃` symmetry of the gap.

* THE FORCING LEMMA (`Gtz.neg_atomPairingProduct_of_isForcedMinusTriple`):
  on an all-heavy design with NO dominating triple, every forced-minus
  triple has a strictly NEGATIVE pairing product — total failure forces the
  design's own two-graph to read `−1` on the whole forced set.  The
  hypotheses are minimal: failure and heaviness only; no genericity, no
  exceptionality.  Realness enters through torsion: the product IS
  `±tripleRadius` at a real design, so "not `−`" and "`≥ 0`" coincide;
  over `ℂ` the free Bargmann phase voids the dichotomy.

* THE EXCEPTIONALITY CONSTRAINT
  (`Gtz.exists_not_isForcedMinusTriple_of_lightEdge_of_isExceptional`): at
  an exceptional phase-free image, no light edge's star is fully
  forced-minus — clause two of `Gtz.PhaseFreeData.IsExceptional` hands every
  light edge a star triple that either leaves the nonnegative-trace class
  or breaks the plus band, and either disjunct contradicts
  `Gtz.IsForcedMinusTriple` outright.  The witness triple need NOT be free
  in the forced/free sense of the measurement campaign: it may fail at both
  signs; the lemma says only that it is not forced-minus.

Together with the erase substrate (`Gtz/Design/EraseSystem.lean`) this puts
steps three and four of the five-step closing argument in the kernel: a
total failure pins the forced set to `−1`, while the design's own values
solve the erase system — the open step five is exactly the claim that those
two constraints collide on the exceptional locus, and its pointwise capacity
mechanism is `Gtz.exists_nonneg_edgeTripleValue_of_boxDeficit`.

Scope honesty: nothing here touches the open proposition itself; every
statement is unconditional arithmetic around it, and no equivalence with
`Gtz.GenericExceptionalSignClash` is claimed anywhere.

Provenance: gtz-p3 land-substrate; the bridge and its band arithmetic were
compiled first as free-standing probes by the derive-farkas and
derive-rigidity lanes against the same anchors.
-/
import Mathlib
import Gtz.Reduction.SignClashReduction
import Gtz.Design.EraseSystem

namespace Gtz

variable {sizeIndex : ℕ}

/-! ## Permutation lemmas for the pairing product -/

/-- Exchanging the first two atoms fixes the pairing product: the three
unordered pairs are the same.  Companion to the shipped
`Gtz.excessGap_swap`. -/
theorem atomPairingProduct_swap (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    atomPairing D second first * atomPairing D second third
        * atomPairing D first third
      = atomPairing D first second * atomPairing D first third
        * atomPairing D second third := by
  rw [atomPairing_comm D second first]
  ring

/-- Bringing the last atom to the front fixes the pairing product.
Companion to the shipped `Gtz.excessGap_rotate`. -/
theorem atomPairingProduct_rotate (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    atomPairing D third first * atomPairing D third second
        * atomPairing D first second
      = atomPairing D first second * atomPairing D first third
        * atomPairing D second third := by
  rw [atomPairing_comm D third first, atomPairing_comm D third second]
  ring

/-- The edge-oriented triple value in pivot order: `T_abx` is the pairing
product of the ordered triple `(a, b, x)`.  The connective between the erase
substrate's conclusions and the sign-clash clauses. -/
theorem edgeTripleValue_eq_atomPairingProduct (D : WeightedDesign sizeIndex 3)
    (edgeFirst edgeSecond other : Fin sizeIndex) :
    edgeTripleValue D edgeFirst edgeSecond other
      = atomPairing D edgeFirst edgeSecond * atomPairing D edgeFirst other
        * atomPairing D edgeSecond other := by
  simp only [edgeTripleValue, atomPairing_comm D other edgeSecond]

/-! ## The canonical forced-minus predicate and its phase-free bridges -/

/-- **FORCED_MINUS.**  The triple has a pivot with nonnegative trace leg, its
tie leg is nonnegative at the PLUS torsion sign of the pairing product, and
strictly negative at the MINUS sign — so, through
`Gtz.dominates_triple_iff_discriminantSystem` and the split identity, the
triple dominates exactly when its product is nonnegative.  On a failing
design the product is therefore forced strictly negative
(`Gtz.neg_atomPairingProduct_of_isForcedMinusTriple`).

This is the `failsAt` convention of the external measurement campaign: NOT
every middle-band triple is forced (a triple outside the trace class is free
to fail at both signs), and the boundary case `excessGap + 2·radius = 0` IS
forced (the plus reading ties at zero and dominates). -/
def IsForcedMinusTriple (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) : Prop :=
  (0 ≤ discriminantTrace D first second third
      ∨ 0 ≤ discriminantTrace D second first third
      ∨ 0 ≤ discriminantTrace D third first second)
    ∧ 0 ≤ excessGap D first second third
        + 2 * tripleRadius D first second third
    ∧ excessGap D first second third
        - 2 * tripleRadius D first second third < 0

/-- The trace clause of `Gtz.IsForcedMinusTriple` IS the phase-free
`Gtz.PhaseFreeData.HasNonnegTraceLeg` at the design's image — the trace legs
agree definitionally (`Gtz.discriminantTrace_eq_traceLeg`).  This is the
reconciliation lemma between the design-vocabulary predicate landed here and
its phase-free reading. -/
theorem hasNonnegTraceLeg_phaseFreeOfDesign_iff (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    (phaseFreeOfDesign D).HasNonnegTraceLeg first second third
      ↔ (0 ≤ discriminantTrace D first second third
        ∨ 0 ≤ discriminantTrace D second first third
        ∨ 0 ≤ discriminantTrace D third first second) := by
  simp only [PhaseFreeData.HasNonnegTraceLeg, discriminantTrace_eq_traceLeg]

/-- The phase-free share at a design's image is the design share. -/
theorem atomShare_phaseFreeOfDesign (D : WeightedDesign sizeIndex 3)
    (atomIndex : Fin sizeIndex) :
    (phaseFreeOfDesign D).atomShare atomIndex = atomShare D atomIndex := by
  simp only [PhaseFreeData.atomShare, phaseFreeOfDesign_weight,
    phaseFreeOfDesign_excess, heavyExcess, atomShare]
  ring

/-- The phase-free sign-blind gap at a design's image is the design gap. -/
theorem excessGap_phaseFreeOfDesign (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    (phaseFreeOfDesign D).excessGap first second third
      = excessGap D first second third := rfl

/-- The modulus of the phase-free Bargmann triangle at a design's image is
the shipped `Gtz.tripleRadius` — torsion in bridge form. -/
theorem abs_triangle_phaseFreeOfDesign (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    |(phaseFreeOfDesign D).triangle first second third|
      = tripleRadius D first second third := by
  rw [phaseFreeOfDesign_triangle]
  simp only [tripleRadius]
  congr 1
  ring

/-! ## The forcing bridge -/

/-- The middle-band arithmetic core: between the two tie readings, a
negative gap is squeezed into the band square. -/
private theorem band_clause_of_tie_readings {gapValue productValue : ℝ}
    (hplus : 0 ≤ gapValue + 2 * productValue)
    (_hminus : gapValue - 2 * productValue < 0) :
    0 ≤ gapValue ∨ gapValue ^ 2 ≤ 4 * productValue ^ 2 := by
  rcases le_total 0 gapValue with hnonneg | hnonpos
  · exact Or.inl hnonneg
  · right
    nlinarith

/-- **THE FORCING BRIDGE.**  A forced-minus triple whose pairing product is
NONNEGATIVE yields an ordered sign-clash triple on the same three atoms —
the pivot is whichever leg carries the nonnegative trace, and the shipped
`S₃` symmetries of the gap and the product carry the band clause to it.
Composed with `Gtz.dominates_of_isSignClashTriple`, such a triple dominates
on an all-heavy design; the conclusion shape is exactly the one
`Gtz.GenericExceptionalSignClash` asks for. -/
theorem exists_isSignClashTriple_of_forcedMinus_of_nonneg_product
    (D : WeightedDesign sizeIndex 3) {first second third : Fin sizeIndex}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hforced : IsForcedMinusTriple D first second third)
    (hproduct : 0 ≤ atomPairing D first second * atomPairing D first third
        * atomPairing D second third) :
    ∃ pivot pairFirst pairSecond : Fin sizeIndex,
      pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ IsSignClashTriple D pivot pairFirst pairSecond := by
  obtain ⟨hlegs, hplus, hminus⟩ := hforced
  have hradius : tripleRadius D first second third
      = atomPairing D first second * atomPairing D first third
        * atomPairing D second third := by
    simp only [tripleRadius]
    exact abs_of_nonneg hproduct
  rw [hradius] at hplus hminus
  have hband := band_clause_of_tie_readings hplus hminus
  rcases hlegs with htrace | htrace | htrace
  · exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
      htrace, hproduct, hband⟩
  · refine ⟨second, first, third, hfirstSecond.symm, hsecondThird, hfirstThird,
      htrace, ?_, ?_⟩
    · rw [atomPairingProduct_swap]
      exact hproduct
    · rw [← excessGap_swap D first second third, atomPairingProduct_swap]
      exact hband
  · refine ⟨third, first, second, hfirstThird.symm, hsecondThird.symm,
      hfirstSecond, htrace, ?_, ?_⟩
    · rw [atomPairingProduct_rotate]
      exact hproduct
    · rw [← excessGap_rotate D first second third, atomPairingProduct_rotate]
      exact hband

/-! ## The forcing lemma -/

/-- **THE FORCING LEMMA.**  On an all-heavy design with no dominating
triple, every forced-minus triple has a strictly NEGATIVE pairing product:
at a nonnegative product the forcing bridge would produce a sign-clash
triple, `Gtz.dominates_of_isSignClashTriple` would make it dominate, and
`Gtz.card_triple_eq_three` contradicts the failure hypothesis.  So total
failure pins the design's own two-graph to `−1` on the whole forced set —
step three of the closing argument, with MINIMAL hypotheses: failure and
heaviness only. -/
theorem neg_atomPairingProduct_of_isForcedMinusTriple
    {D : WeightedDesign sizeIndex 3} (hheavy : AllHeavy D)
    (hfail : ∀ C : Finset (Fin sizeIndex), C.card = 3 → ¬ Dominates D C)
    {first second third : Fin sizeIndex}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hforced : IsForcedMinusTriple D first second third) :
    atomPairing D first second * atomPairing D first third
      * atomPairing D second third < 0 := by
  by_contra hnonneg
  push Not at hnonneg
  obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond,
    hpairDistinct, hclash⟩ :=
    exists_isSignClashTriple_of_forcedMinus_of_nonneg_product D
      hfirstSecond hfirstThird hsecondThird hforced hnonneg
  exact hfail {pivot, pairFirst, pairSecond}
    (card_triple_eq_three hpivotFirst hpivotSecond hpairDistinct)
    (dominates_of_isSignClashTriple hheavy hpivotFirst hpivotSecond
      hpairDistinct hclash)

/-! ## The exceptionality constraint on forced sets -/

/-- **NO LIGHT STAR IS FULLY FORCED at an exceptional image.**  Clause two of
`Gtz.PhaseFreeData.IsExceptional` hands every light edge a star triple that
either leaves the nonnegative-trace class — contradicting the trace clause
of `Gtz.IsForcedMinusTriple` through the definitional bridge — or breaks
the plus band, contradicting its second clause through the torsion bridge
`Gtz.abs_triangle_phaseFreeOfDesign`.  The witness is only NOT FORCED-MINUS:
it may still fail at both torsion signs, so nothing here says the light
star carries a dominating triple. -/
theorem exists_not_isForcedMinusTriple_of_lightEdge_of_isExceptional
    (D : WeightedDesign sizeIndex 3)
    (hexceptional : (phaseFreeOfDesign D).IsExceptional)
    {edgeFirst edgeSecond : Fin sizeIndex} (hedge : edgeFirst ≠ edgeSecond)
    (hlight : atomShare D edgeFirst + atomShare D edgeSecond ≤ 1) :
    ∃ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      ¬ IsForcedMinusTriple D edgeFirst edgeSecond other := by
  obtain ⟨_, hclauseTwo⟩ := hexceptional
  have hlightPoint : (phaseFreeOfDesign D).atomShare edgeFirst
      + (phaseFreeOfDesign D).atomShare edgeSecond ≤ 1 := by
    rw [atomShare_phaseFreeOfDesign, atomShare_phaseFreeOfDesign]
    exact hlight
  obtain ⟨other, hother, hwitness⟩ := hclauseTwo edgeFirst edgeSecond hedge
    hlightPoint
  refine ⟨other, hother, fun hforced => ?_⟩
  obtain ⟨htrace, hplus, _⟩ := hforced
  rcases hwitness with hnoTrace | hbandBreak
  · exact hnoTrace ((hasNonnegTraceLeg_phaseFreeOfDesign_iff D edgeFirst
      edgeSecond other).mpr htrace)
  · rw [excessGap_phaseFreeOfDesign, abs_triangle_phaseFreeOfDesign]
      at hbandBreak
    linarith

end Gtz
