/-
# The sign-clash coverage layer: the box-deficit bridge and the reduction lattice

The Phase-2 landing (`Gtz/Reduction/SignClashReduction.lean`) named the open
cell's closing shape `Gtz.GenericExceptionalSignClash`; the Phase-3 substrate
(`Gtz/Design/EraseSystem.lean`, `Gtz/Reduction/ForcedSignForcing.lean`) landed
the erase system, the capacity lemma, the canonical forced-minus predicate and
the forcing bridge.  This module composes them into the run's attack layer:

* **THE POINTWISE BOX-DEFICIT CLASH BRIDGE**
  (`Gtz.exists_isSignClashTriple_of_forcedBoxDeficit`): if some forced-minus
  subset of an edge star carries a box-deficit — the free star mass cannot
  cover the erase requirement once the forced mass is pinned to the minus
  side — then an ordered sign-clash triple exists.  NO genericity, heaviness,
  exceptionality, or failure hypotheses, at every ambient size: the capacity
  lemma hands a forced triple whose value is nonnegative, and the forcing
  bridge pivots it into the clash shape.

* **THE COVERAGE FRAGMENT**
  (`Gtz.exists_isSignClashTriple_of_isExceptional_of_hasForcedBoxDeficitEdge`
  and the residue split
  `Gtz.genericExceptionalSignClash_of_forall_without_deficit_signClash`):
  the first kernel-proved fragment of `Gtz.GenericExceptionalSignClash` —
  on the deficit-witnessed subregion the open proposition IS a theorem, and
  the full proposition reduces to its deficit-free residue.  The reach of the
  fragment is EXTERNAL MEASUREMENT, not kernel fact: in the Phase-3 exact
  corpus the deficit condition holds at `224` of the `307` infeasible points
  (all `184` capacity-class kills, all ten hard-core points, `95` of the
  `118` exceptional points); the measured residue is `78` points certified
  by exact multi-edge rational Farkas duals not yet in kernel form plus `5`
  discrete points killed only beyond the box relaxation.  Nothing here
  claims the fragment covers the whole region.

* **THE REFORMULATION LATTICE** (derive-rigidity's consequence analysis):
  three named OPEN propositions — `Gtz.OwnSignForcedClash` (the sigma form:
  the design's own two-graph is not all-minus on the forced set),
  `Gtz.OwnSignForcedClashOnClean` (its flip-clean restriction), and
  `Gtz.EraseConsistentForcedClashOnClean` (the CSP form: EVERY
  erase-consistent reading, not only the design's own, reads some forced
  triple nonnegative on the flip-clean locus) — with the one-way reductions
  between them and down to the landed proposition:
  CSP ⟹ clean sigma (instantiate at the design's own reading),
  sigma ⟹ `Gtz.GenericExceptionalSignClash` (the forcing bridge), and
  both sigma ⟹ CSP and clean sigma ⟹ CSP (rigidity: on the flip-clean
  locus the erase system has no reading other than the design's own, so
  the CSP form is NOT stronger — the parametric-LP attack on the forced
  system is complete relative to the theorem).  The clean pair
  (`Gtz.ownSignForcedClashOnClean_of_eraseConsistentForcedClashOnClean`
  and `Gtz.eraseConsistentForcedClashOnClean_of_ownSignForcedClashOnClean`)
  runs BOTH ways, so the CSP form and the clean sigma form are
  interderivable; each still reaches the open cell one-way, through
  `Gtz.genericExceptionalSignClash_of_ownSignForcedClashOnClean` and its
  CSP sibling, both of which carry the flip-dirty residue as an explicit
  hypothesis.  The flip-clean qualifier on the CSP form is MANDATORY: at
  a flip-dirty datum a phantom erase reading could sit all-minus on the
  forced set even when the design's own reading does not.  All reductions
  are one-way theorems; NO equivalence with the open cell is claimed
  anywhere in this module.

Realness enters exactly where the substrate modules consume it: the capacity
lemma's box pinning exists because the design's own values solve the erase
law over the reals, and the forced dichotomy "not minus = nonneg" is the
torsion `|T| = tripleRadius`; over the complex field the free Bargmann phase
voids both, and GTZ itself is false there.

Provenance: gtz-p3 land-attack; the composed bridge and the lattice were
compiled first as free-standing probes by the derive-farkas and
derive-rigidity lanes and certified by the verify-adversarial lane.
-/
import Mathlib
import Gtz.Reduction.SignClashReduction
import Gtz.Design.EraseSystem
import Gtz.Reduction.ForcedSignForcing

namespace Gtz

variable {sizeIndex : ℕ}

/-! ## The pointwise box-deficit clash bridge -/

/-- **THE POINTWISE BOX-DEFICIT CLASH BRIDGE.**  A forced-minus subset of an
edge star whose box-deficit inequality holds — the free star mass is strictly
short of the erase requirement plus the pinned forced mass — yields an ordered
sign-clash triple.  Composition of three landed pieces: the capacity lemma
`Gtz.exists_nonneg_edgeTripleValue_of_boxDeficit` hands a forced star member
with nonnegative triple value, the torsion bridge
`Gtz.edgeTripleValue_eq_atomPairingProduct` reads it as a nonnegative pairing
product, and the forcing bridge
`Gtz.exists_isSignClashTriple_of_forcedMinus_of_nonneg_product` pivots the
triple into the clash shape.  No genericity, no heaviness, no exceptionality,
no failure hypothesis, at every ambient size. -/
theorem exists_isSignClashTriple_of_forcedBoxDeficit
    (D : WeightedDesign sizeIndex 3) {edgeFirst edgeSecond : Fin sizeIndex}
    (hedge : edgeFirst ≠ edgeSecond) (forcedStar : Finset (Fin sizeIndex))
    (hsubset : forcedStar ⊆ (Finset.univ.erase edgeFirst).erase edgeSecond)
    (hforced : ∀ other ∈ forcedStar,
      IsForcedMinusTriple D edgeFirst edgeSecond other)
    (hdeficit :
      ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond \ forcedStar,
          D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|
        < atomPairing D edgeFirst edgeSecond ^ 2
              * (1 - atomShare D edgeFirst - atomShare D edgeSecond)
          + ∑ other ∈ forcedStar,
              D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|) :
    ∃ pivot pairFirst pairSecond : Fin sizeIndex,
      pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ IsSignClashTriple D pivot pairFirst pairSecond := by
  obtain ⟨other, hmember, hnonneg⟩ :=
    exists_nonneg_edgeTripleValue_of_boxDeficit D hedge forcedStar hsubset
      hdeficit
  have hstar := hsubset hmember
  have hotherSecond : other ≠ edgeSecond := (Finset.mem_erase.mp hstar).1
  have hotherFirst : other ≠ edgeFirst :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hstar).2).1
  rw [edgeTripleValue_eq_atomPairingProduct] at hnonneg
  exact exists_isSignClashTriple_of_forcedMinus_of_nonneg_product D hedge
    hotherFirst.symm hotherSecond.symm (hforced other hmember) hnonneg

/-! ## The deficit condition as a named region -/

/-- **The forced-box-deficit condition**: some edge carries a forced-minus
star subset whose box-deficit inequality holds.  This is the semialgebraic
sufficient condition of the coverage fragment, in shipped vocabulary: an
absolute-value polynomial inequality over a Boolean combination of
forced-minus clauses.  External exact measurement (not kernel fact): the
condition holds at `224` of the `307` box-infeasible Phase-2 corpus points —
every capacity-class kill, every hard-core point — and at `95` of the `118`
exceptional points, with zero false positives on the `124` feasible
controls. -/
def HasForcedBoxDeficitEdge (D : WeightedDesign sizeIndex 3) : Prop :=
  ∃ edgeFirst edgeSecond : Fin sizeIndex, edgeFirst ≠ edgeSecond
    ∧ ∃ forcedStar ⊆ (Finset.univ.erase edgeFirst).erase edgeSecond,
        (∀ other ∈ forcedStar,
          IsForcedMinusTriple D edgeFirst edgeSecond other)
        ∧ ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond \ forcedStar,
              D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|
            < atomPairing D edgeFirst edgeSecond ^ 2
                  * (1 - atomShare D edgeFirst - atomShare D edgeSecond)
              + ∑ other ∈ forcedStar,
                  D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|

/-- The bridge, packaged over the named region: a design with a forced-box-
deficit edge carries an ordered sign-clash triple. -/
theorem exists_isSignClashTriple_of_hasForcedBoxDeficitEdge
    (D : WeightedDesign sizeIndex 3) (hdeficit : HasForcedBoxDeficitEdge D) :
    ∃ pivot pairFirst pairSecond : Fin sizeIndex,
      pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ IsSignClashTriple D pivot pairFirst pairSecond := by
  obtain ⟨edgeFirst, edgeSecond, hedge, forcedStar, hsubset, hforced, hbox⟩ :=
    hdeficit
  exact exists_isSignClashTriple_of_forcedBoxDeficit D hedge forcedStar
    hsubset hforced hbox

/-! ## The coverage fragment of the open proposition -/

/-- **THE COVERAGE FRAGMENT.**  On the deficit-witnessed subregion, the open
proposition `Gtz.GenericExceptionalSignClash` is a THEOREM: every generic
all-heavy exceptional design with a forced-box-deficit edge carries the
sign-clash triple the proposition asks for.  The three quantifier-domain
hypotheses are carried to make the statement visibly a restriction of the
open proposition; the proof consumes only the deficit witness — the bridge
needs none of them.  The uncovered residue is named honestly in the module
header: `78` multi-edge-certified points and `5` discrete points of the
measured corpus lie outside this fragment. -/
theorem exists_isSignClashTriple_of_isExceptional_of_hasForcedBoxDeficitEdge
    (D : WeightedDesign 6 3) (_hheavy : AllHeavy D)
    (_hgeneric : IsGenericDesign D)
    (_hexceptional : (phaseFreeOfDesign D).IsExceptional)
    (hdeficit : HasForcedBoxDeficitEdge D) :
    ∃ pivot pairFirst pairSecond : Fin 6,
      pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ IsSignClashTriple D pivot pairFirst pairSecond :=
  exists_isSignClashTriple_of_hasForcedBoxDeficitEdge D hdeficit

/-- **THE RESIDUE SPLIT.**  The open proposition reduces to its deficit-free
residue: if every generic all-heavy exceptional design WITHOUT a forced-box-
deficit edge carries a sign-clash triple, then
`Gtz.GenericExceptionalSignClash` holds outright — the deficit-witnessed
designs are covered by the kernel bridge.  One-way only; nothing is claimed
about the residue itself, which external measurement sizes at `83` of the
`307` corpus kills (`78` with exact rational multi-edge Farkas certificates
on disk, `5` discrete). -/
theorem genericExceptionalSignClash_of_forall_without_deficit_signClash
    (hresidue : ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
      (phaseFreeOfDesign D).IsExceptional → ¬ HasForcedBoxDeficitEdge D →
      ∃ pivot pairFirst pairSecond : Fin 6,
        pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ IsSignClashTriple D pivot pairFirst pairSecond) :
    GenericExceptionalSignClash := by
  intro D hheavy hgeneric hexceptional
  by_cases hdeficit : HasForcedBoxDeficitEdge D
  · exact exists_isSignClashTriple_of_hasForcedBoxDeficitEdge D hdeficit
  · exact hresidue D hheavy hgeneric hexceptional hdeficit

/-! ## The reformulation lattice: three named open propositions -/

/-- **THE SIGMA FORM — OPEN.**  Every generic all-heavy exceptional design has
a forced-minus triple whose OWN pairing product is nonnegative: the design's
own two-graph is not all-minus on the forced set.  Same quantifier domain as
`Gtz.GenericExceptionalSignClash`; reduces to it through the forcing bridge
(`Gtz.genericExceptionalSignClash_of_ownSignForcedClash` below).  Evidence is
EXTERNAL MEASUREMENT only: zero violations at `9651` Phase-2 exact points and
at the `619` Phase-3 rigidity-lane points; nothing here is kernel-checked
about the proposition itself. -/
def OwnSignForcedClash : Prop :=
  ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
    (phaseFreeOfDesign D).IsExceptional →
    ∃ first second third : Fin 6,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ IsForcedMinusTriple D first second third
        ∧ 0 ≤ atomPairing D first second * atomPairing D first third
            * atomPairing D second third

/-- **THE CLEAN SIGMA FORM — OPEN.**  The sigma form restricted to the
flip-clean locus (`Gtz.AllEdgesFlipClean`): the version the CSP form below
reaches.  The restriction loses nothing on the generic locus so far as
measurement can tell (zero flip-dirty generic points in `619` + `9651` exact
samples, external), and the flip-dirty locus is a polynomial locus
dissolvable through `Gtz.gtzWeighted_of_forall_generic_flipClean_dominates`
at the price of the witness flip certificate. -/
def OwnSignForcedClashOnClean : Prop :=
  ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
    (phaseFreeOfDesign D).IsExceptional → AllEdgesFlipClean D →
    ∃ first second third : Fin 6,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ IsForcedMinusTriple D first second third
        ∧ 0 ≤ atomPairing D first second * atomPairing D first third
            * atomPairing D second third

/-- **THE CSP FORM — OPEN.**  On the flip-clean locus, EVERY erase-consistent
reading (`Gtz.IsEraseConsistentAssignment`) — not only the design's own —
reads some forced-minus triple nonnegative.  This is the parametric-LP
statement: the forced system {erase equations + all-minus on the forced set}
is infeasible over every admissible datum.  The flip-clean hypothesis is
MANDATORY: at a flip-dirty datum a phantom erase reading could sit all-minus
on the forced set even when the design's own reading does not, so the
unqualified CSP form could be false while the theorem is true.  Rigidity
(`Gtz.eraseConsistentForcedClashOnClean_of_ownSignForcedClashOnClean`
below) makes the qualified form exactly as strong as the clean sigma form
— that reduction and its converse
`Gtz.ownSignForcedClashOnClean_of_eraseConsistentForcedClashOnClean` are
the two halves of the interderivability. -/
def EraseConsistentForcedClashOnClean : Prop :=
  ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
    (phaseFreeOfDesign D).IsExceptional → AllEdgesFlipClean D →
    ∀ assignment : Fin 6 → Fin 6 → Fin 6 → ℝ,
      IsEraseConsistentAssignment D assignment →
      ∃ first second third : Fin 6,
        first ≠ second ∧ first ≠ third ∧ second ≠ third
          ∧ IsForcedMinusTriple D first second third
          ∧ 0 ≤ assignment first second third

/-! ## The one-way reductions -/

/-- **CSP form ⟹ clean sigma form**: instantiate the CSP quantifier at the
design's own reading, which is erase-consistent by
`Gtz.own_isEraseConsistentAssignment`; the torsion bridge
`Gtz.edgeTripleValue_eq_atomPairingProduct` converts the conclusion. -/
theorem ownSignForcedClashOnClean_of_eraseConsistentForcedClashOnClean
    (hcsp : EraseConsistentForcedClashOnClean) : OwnSignForcedClashOnClean := by
  intro D hheavy hgeneric hexceptional hclean
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hforced, hnonneg⟩ := hcsp D hheavy hgeneric hexceptional hclean
    (fun edgeFirst edgeSecond other => edgeTripleValue D edgeFirst edgeSecond other)
    (own_isEraseConsistentAssignment D)
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hforced, ?_⟩
  rw [← edgeTripleValue_eq_atomPairingProduct]
  exact hnonneg

/-- **Sigma form ⟹ the landed open proposition**: the forcing bridge turns
each own-sign witness into the sign-clash triple
`Gtz.GenericExceptionalSignClash` asks for.  One-way only. -/
theorem genericExceptionalSignClash_of_ownSignForcedClash
    (hsigma : OwnSignForcedClash) : GenericExceptionalSignClash := by
  intro D hheavy hgeneric hexceptional
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hforced, hproduct⟩ := hsigma D hheavy hgeneric hexceptional
  exact exists_isSignClashTriple_of_forcedMinus_of_nonneg_product D
    hfirstSecond hfirstThird hsecondThird hforced hproduct

/-- **Sigma form ⟹ CSP form — the rigidity content.**  On the flip-clean
locus the erase system is rigid: any erase-consistent reading IS the design's
own (`Gtz.eraseConsistentAssignment_eq_own`), so the sigma witness transfers
to every reading.  Together with the converse reduction above, the CSP form
is exactly as strong as the clean sigma form: proving forced-system
infeasibility over the clean locus is NOT more than the theorem demands —
the parametric-LP attack is complete relative to it. -/
theorem eraseConsistentForcedClashOnClean_of_ownSignForcedClash
    (hsigma : OwnSignForcedClash) : EraseConsistentForcedClashOnClean := by
  intro D hheavy hgeneric hexceptional hclean assignment hconsistent
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hforced, hproduct⟩ := hsigma D hheavy hgeneric hexceptional
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hforced, ?_⟩
  have hthirdMember : third ∈ (Finset.univ.erase first).erase second :=
    Finset.mem_erase.mpr ⟨hsecondThird.symm,
      Finset.mem_erase.mpr ⟨hfirstThird.symm, Finset.mem_univ third⟩⟩
  rw [eraseConsistentAssignment_eq_own D hclean assignment hconsistent
    first second third hfirstSecond hthirdMember,
    edgeTripleValue_eq_atomPairingProduct]
  exact hproduct

/-- **Clean sigma form ⟹ CSP form** — the same rigidity argument with the
flip-clean hypothesis supplied to the sigma quantifier instead of being
consumed only by the rewrite.  Together with
`Gtz.ownSignForcedClashOnClean_of_eraseConsistentForcedClashOnClean` this
CLOSES the interderivability of the two clean forms, which the reduction
from the unqualified sigma form above does not establish on its own: that
one starts from a strictly stronger proposition. -/
theorem eraseConsistentForcedClashOnClean_of_ownSignForcedClashOnClean
    (hsigma : OwnSignForcedClashOnClean) : EraseConsistentForcedClashOnClean := by
  intro D hheavy hgeneric hexceptional hclean assignment hconsistent
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hforced, hproduct⟩ := hsigma D hheavy hgeneric hexceptional hclean
  refine ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hforced, ?_⟩
  have hthirdMember : third ∈ (Finset.univ.erase first).erase second :=
    Finset.mem_erase.mpr ⟨hsecondThird.symm,
      Finset.mem_erase.mpr ⟨hfirstThird.symm, Finset.mem_univ third⟩⟩
  rw [eraseConsistentAssignment_eq_own D hclean assignment hconsistent
    first second third hfirstSecond hthirdMember,
    edgeTripleValue_eq_atomPairingProduct]
  exact hproduct

/-- **Clean sigma form ⟹ the landed open proposition**, modulo the flip-dirty
residue: on the clean locus the forcing bridge turns each own-sign witness
into a sign-clash triple, and the dirty locus is carried as an explicit
hypothesis.  This is the payoff edge of the clean sigma form — without it
that proposition is a sink in the lattice, reachable but never usable. -/
theorem genericExceptionalSignClash_of_ownSignForcedClashOnClean
    (hsigma : OwnSignForcedClashOnClean)
    (hdirty : ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
      (phaseFreeOfDesign D).IsExceptional → ¬ AllEdgesFlipClean D →
      ∃ pivot pairFirst pairSecond : Fin 6,
        pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ IsSignClashTriple D pivot pairFirst pairSecond) :
    GenericExceptionalSignClash := by
  intro D hheavy hgeneric hexceptional
  by_cases hclean : AllEdgesFlipClean D
  · obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
      hforced, hproduct⟩ := hsigma D hheavy hgeneric hexceptional hclean
    exact exists_isSignClashTriple_of_forcedMinus_of_nonneg_product D
      hfirstSecond hfirstThird hsecondThird hforced hproduct
  · exact hdirty D hheavy hgeneric hexceptional hclean

/-- **The composed reduction**: the CSP form on the clean locus PLUS clash on
the flip-dirty generic exceptional residue give the landed open proposition.
The dirty residue is a measured-empty polynomial locus (zero flip-dirty
generic points in `619` + `9651` exact samples, external); it dissolves by
one polynomial multiplication through the avoidance template at the price of
the witness flip certificate, exactly as the module header of
`Gtz/Design/EraseSystem.lean` prices it. -/
theorem genericExceptionalSignClash_of_eraseConsistentForcedClashOnClean
    (hcsp : EraseConsistentForcedClashOnClean)
    (hdirty : ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
      (phaseFreeOfDesign D).IsExceptional → ¬ AllEdgesFlipClean D →
      ∃ pivot pairFirst pairSecond : Fin 6,
        pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ IsSignClashTriple D pivot pairFirst pairSecond) :
    GenericExceptionalSignClash :=
  genericExceptionalSignClash_of_ownSignForcedClashOnClean
    (ownSignForcedClashOnClean_of_eraseConsistentForcedClashOnClean hcsp) hdirty

/-! ## The clean forms reach the open cell with NO flip-dirty hypothesis

The two theorems above route through `Gtz.GenericExceptionalSignClash`, and every
route into that Prop pays for the flip-dirty designs with an extra residue
hypothesis `hdirty`.  With the witness flip certificate
(`Gtz.eval_flipDegeneracyPoly_genericWitnessDesign_ne_zero`) landed, that price is no
longer necessary: the genericity template dissolves the flip-dirty locus outright, so
the clean forms reach `Gtz.GtzWeighted 6 3` directly.

The docstring of `Gtz.OwnSignForcedClashOnClean` priced this exactly — "dissolvable
through `Gtz.gtzWeighted_of_forall_generic_flipClean_dominates` at the price of the
witness flip certificate".  The price is paid; here is the collection. -/

/-- **THE CLEAN SIGMA FORM REACHES THE OPEN CELL.**  No flip-dirty residue, no
`Gtz.GenericExceptionalSignClash` detour: on the flip-clean locus the forced-minus
triple with nonnegative pairing product IS a sign-clash triple, and off the
exceptional locus the shipped vertex exclusion dominates outright. -/
theorem gtzWeighted_six_three_of_ownSignForcedClashOnClean
    (hsigma : OwnSignForcedClashOnClean) : GtzWeighted 6 3 := by
  refine gtzWeighted_of_forall_generic_flipClean_dominates ?_
  intro D hheavy hgeneric hclean
  by_cases hexceptional : (phaseFreeOfDesign D).IsExceptional
  · obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
      hforced, hproduct⟩ := hsigma D hheavy hgeneric hexceptional hclean
    obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond,
      hpairDistinct, hclash⟩ :=
      exists_isSignClashTriple_of_forcedMinus_of_nonneg_product D
        hfirstSecond hfirstThird hsecondThird hforced hproduct
    exact ⟨{pivot, pairFirst, pairSecond},
      card_triple_eq_three hpivotFirst hpivotSecond hpairDistinct,
      dominates_of_isSignClashTriple hheavy hpivotFirst hpivotSecond hpairDistinct hclash⟩
  · exact exists_dominates_of_not_isExceptional D hheavy (by norm_num) hexceptional

/-- The CSP reading of the same obligation reaches the cell too, through the shipped
clean pair. -/
theorem gtzWeighted_six_three_of_eraseConsistentForcedClashOnClean
    (hcsp : EraseConsistentForcedClashOnClean) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_ownSignForcedClashOnClean
    (ownSignForcedClashOnClean_of_eraseConsistentForcedClashOnClean hcsp)

/-- And so does the unqualified sigma form, which was already the strongest of the
three — so it is never the right target: it implies the clean form by weakening, and
the clean form already suffices. -/
theorem gtzWeighted_six_three_of_ownSignForcedClash (hsigma : OwnSignForcedClash) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_ownSignForcedClashOnClean
    (fun D hheavy hgeneric hexceptional _ => hsigma D hheavy hgeneric hexceptional)

end Gtz
