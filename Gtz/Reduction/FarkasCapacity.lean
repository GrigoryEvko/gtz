/-
# The multi-edge capacity lemma: Farkas certificates over the forced box system

`Gtz/Design/EraseSystem.lean` landed the SINGLE-EDGE capacity lemma
`Gtz.exists_nonneg_edgeTripleValue_of_boxDeficit`: when one edge's free star
mass falls short of its erase requirement plus its pinned forced mass, the
all-negative reading of that edge's forced slots is impossible.
`Gtz/Reduction/SignClashCoverage.lean` composed it with the forcing bridge into
`Gtz.exists_isSignClashTriple_of_forcedBoxDeficit` and named the region
`Gtz.HasForcedBoxDeficitEdge`.

This module lands the MULTI-EDGE generalization the Phase-3 derivation lane
stated but never wrote.  A certificate is now a vector of real multipliers, one
per ordered pair of atoms; the certified quantity is the multiplier-weighted
combination of the erase right-hand sides, and the obstruction is the AGGREGATE
coefficient each triple receives from the three edges it lies on.  The point of
the generalization is CANCELLATION: a triple sits in three edge equations, so
multipliers can be chosen to make its aggregate coefficient small or zero, and
the sharpest certificates in the external corpus do exactly that.

## Contents

* **THE ABSTRACT LEMMA** `Gtz.exists_nonneg_of_farkasCertificate`, over an
  arbitrary index type: if the coefficient-weighted values sum to the
  certificate value, and the free part's absolute mass minus the forced part's
  signed mass falls strictly short of that value, then some forced member's
  value is nonnegative.  One `linarith` over the split sum — the same skeleton
  as the landed single-edge lemma, which is recovered as the instance
  `coefficient = weight` on one edge star
  (`Gtz.exists_nonneg_edgeTripleValue_of_boxDeficit_of_farkasCertificate`).

* **THE AGGREGATION IDENTITY**
  `Gtz.sum_orderedDistinctTriples_farkasAggregate_mul_edgeTripleValue`: the
  multiplier-weighted sum of erase right-hand sides IS the aggregate-weighted
  sum of triple values.  This is the whole content of the multi-edge form and
  it is a THEOREM, not a definition — see the honesty note below.

* **THE CONCRETE LEMMA**
  `Gtz.exists_nonneg_edgeTripleValue_of_farkasCertificate`, the multi-edge
  capacity lemma at general ambient size, and the region
  `Gtz.HasFarkasCertificate` with its clash bridge
  `Gtz.exists_isSignClashTriple_of_hasFarkasCertificate` — no genericity,
  heaviness, exceptionality or failure hypothesis, exactly as in the
  single-edge layer.

* **THE RESIDUE SPLITS**
  `Gtz.genericExceptionalSignClash_of_forall_without_farkasCertificate_signClash`
  and the joint form
  `Gtz.genericExceptionalSignClash_of_forall_without_certificate_signClash`,
  which reduces the open proposition to the designs carrying NEITHER a
  forced-box-deficit edge NOR a Farkas certificate, and
  `Gtz.gtzWeighted_six_three_of_forall_without_certificate_signClash` down to
  the open cell.

## Why the multiplier form, and not an arbitrary coefficient function

A certificate must be computable from the DATUM.  Were the region defined by an
arbitrary coefficient function together with "its weighted sum equals the
certificate value", the value could be read off the unknown triple values
themselves and the region would collapse to a restatement of its own
conclusion — the iff-trap.  Here `Gtz.farkasCertificateValue` is built from the
multipliers and the erase right-hand sides ALONE, and that it agrees with the
aggregate-weighted sum of triple values is the aggregation identity above.  So
`Gtz.HasFarkasCertificate` is a genuine semialgebraic condition on the design:
an absolute-value polynomial inequality over a Boolean combination of
forced-minus clauses, existentially quantified over the multipliers.

## The ordered index and the factor six

Triples are indexed by ORDERED triples of pairwise-distinct atoms
(`Gtz.orderedDistinctTriples`, the general-size sibling of the shipped size-six
`Gtz.distinctTriples`; they agree at size six, see
`Gtz.orderedDistinctTriples_six_eq_distinctTriples`).  Each unordered triple
therefore appears six times.  The aggregate
`Gtz.farkasAggregate` is symmetric under all six orderings by construction and
the triple value is symmetric by `Gtz.edgeTripleValue_eq_atomPairingProduct`,
so both sides of every inequality below are exactly six times their unordered
readings and the constant `6` on the certificate value is bookkeeping, not a
loss: the hypothesis is EQUIVALENT to the unordered one, term by term.  The
ordered index buys the coordinate-permutation reindexings
(`Gtz.sum_orderedDistinctTriples_swapFirstSecond` and its four siblings) that
prove the aggregation identity at every ambient size, with no canonical
representative and no sorting.

## Realness

Exactly where the single-edge layer consumes it: the design's own values solve
every erase equation over the reals, which pins the certified combination
inside the box, and `|edgeTripleValue| = Gtz.tripleRadius` is torsion
(`Gtz.abs_edgeTripleValue`).  Over the complex field the Bargmann phase is free,
the values only satisfy `|t| <= r`, and nothing below survives.

## Reach — EXTERNAL MEASUREMENT, not kernel fact

In the Phase-3 exact corpus of `307` box-infeasible points, `224` carry a
single-edge certificate (the landed deficit region), `78` carry an exact
rational multi-edge certificate and `5` are infeasible only beyond the box
relaxation.  So the joint region of this module and the deficit region covers
`302` of the `307`, and on the exceptional locus it covers `118` of `118`:
every measured exceptional point is continuous-infeasible.  The multi-edge
certificates were re-verified in this campaign against a from-scratch
reconstruction of each design from its raw frame and weights: `296` of them on
raw-reconstructible points, every one with a strictly positive violation, and
the `23` exceptional-locus points among them all confirmed to have NO
single-edge deficit edge — they genuinely need this lemma.  Support sizes run
from `2` to `15`; the `16` two-edge certificates are shared-triple
cancellations (the two edges meet in an atom and the multipliers zero the
shared triple's aggregate coefficient), and the extreme instances are two
nine-edge integer certificates with twenty-one-digit entries.

INDEPENDENT RECOMPUTATION — ALSO AN EXTERNAL MEASUREMENT.  The reach above was
recomputed a second time from the raw frames alone, by a separate lane sharing
no code with the first, and it decomposes as follows.  Of the `300` corpus
points whose frame is on disk, `221` carry a single-edge deficit edge and a
further `75` carry only a multi-edge certificate, so the two regions jointly
reach `296` and leave `4`; the remaining `2` of the ledger's `302` sit on the
`7` shipped datums stored without a frame.  On the exceptional locus the split
is `95` single-edge and `23` certificate-only, reaching `118` of `118` with
none left over.  The recomputation carries its own firing control: the `5`
box-feasible points must be reached by NEITHER region, and none of them is
reached by either, so the count is a measurement rather than a saturating
instrument.  The forced sets were recomputed from `Gtz.IsForcedMinusTriple`
rather than read from the corpus, and agree with it at every point; every
verdict is exact rational arithmetic, so no float enters the reach figure.

NOT PROVED HERE, and stated so that nobody assumes it: that
`Gtz.HasForcedBoxDeficitEdge` implies `Gtz.HasFarkasCertificate`.  It is true —
the single-edge certificate is the multiplier supported on one ordered pair —
but the region-level inclusion needs the six-fold orbit of the forced star and
a partition of the triple index by "contains this edge", which is a separate
Finset computation.  Until it is written the two regions are incomparable IN
KERNEL, which is why the joint residue split above assumes the absence of both.

Provenance: gtz-p5 cheap-farkas; the multi-edge layer was stated by the gtz-p3
derive-farkas lane, its certificates constructed there and re-verified by the
verify-adversarial lane, and independently re-derived from raw frames here.
-/
import Mathlib
import Gtz.Reduction.SignClashCoverage

namespace Gtz

variable {sizeIndex : ℕ}

/-! ## The abstract capacity lemma -/

/-- **THE FARKAS CAPACITY LEMMA** (abstract, any index type).  Suppose the
coefficient-weighted values over the support sum to the certificate value, and
the free part's ABSOLUTE mass minus the forced part's SIGNED mass falls
strictly short of it.  Then the all-negative reading of the forced part is
impossible: some forced member carries a nonnegative value.

The proof is the single-edge argument verbatim.  If every forced value were
negative, each forced term `coefficient * value` would equal
`-(coefficient * |value|)`, so the forced block would contribute exactly minus
the forced mass; the free block is bounded by its absolute mass; and the two
together would have to reach the certificate value, contradicting the
hypothesis.  No positivity is assumed of the coefficients — that is what makes
the multi-edge instance possible, where an aggregate coefficient may have
either sign or vanish. -/
theorem exists_nonneg_of_farkasCertificate {indexType : Type*} [DecidableEq indexType]
    (support forcedSet : Finset indexType) (hforcedSubset : forcedSet ⊆ support)
    (coefficient value : indexType → ℝ) (certificateValue : ℝ)
    (hlaw : ∑ member ∈ support, coefficient member * value member = certificateValue)
    (hviolation :
      ∑ member ∈ support \ forcedSet, |coefficient member| * |value member|
          - ∑ member ∈ forcedSet, coefficient member * |value member|
        < certificateValue) :
    ∃ member ∈ forcedSet, 0 ≤ value member := by
  by_contra hall
  push Not at hall
  have hsplit :
      ∑ member ∈ support \ forcedSet, coefficient member * value member
        + ∑ member ∈ forcedSet, coefficient member * value member
      = ∑ member ∈ support, coefficient member * value member :=
    Finset.sum_sdiff hforcedSubset
  have hfreeBound :
      ∑ member ∈ support \ forcedSet, coefficient member * value member
        ≤ ∑ member ∈ support \ forcedSet, |coefficient member| * |value member| :=
    Finset.sum_le_sum fun member _ => by
      rw [← abs_mul]
      exact le_abs_self _
  have hforcedEq :
      ∑ member ∈ forcedSet, coefficient member * value member
        = -∑ member ∈ forcedSet, coefficient member * |value member| := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun member hmember => ?_
    rw [abs_of_neg (hall member hmember)]
    ring
  linarith

/-- **THE LANDED SINGLE-EDGE LEMMA IS THE ONE-EDGE INSTANCE.**  Taking the
support to be one edge star, the coefficients to be the weights and the
certificate value to be that edge's erase right-hand side recovers
`Gtz.exists_nonneg_edgeTripleValue_of_boxDeficit` from the abstract lemma.  The
weights are positive, so their absolute values are themselves and the abstract
inequality is the box-deficit inequality rearranged.  This is the soundness
check on the generalization: the multi-edge layer is not a different
mechanism. -/
theorem exists_nonneg_edgeTripleValue_of_boxDeficit_of_farkasCertificate
    (D : WeightedDesign sizeIndex 3) {edgeFirst edgeSecond : Fin sizeIndex}
    (hedge : edgeFirst ≠ edgeSecond) (forcedStar : Finset (Fin sizeIndex))
    (hsubset : forcedStar ⊆ (Finset.univ.erase edgeFirst).erase edgeSecond)
    (hdeficit :
      ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond) \ forcedStar,
          D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|
        < atomPairing D edgeFirst edgeSecond ^ 2
              * (1 - atomShare D edgeFirst - atomShare D edgeSecond)
          + ∑ other ∈ forcedStar,
              D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|) :
    ∃ other ∈ forcedStar,
      0 ≤ edgeTripleValue D edgeFirst edgeSecond other := by
  refine exists_nonneg_of_farkasCertificate
    ((Finset.univ.erase edgeFirst).erase edgeSecond) forcedStar hsubset
    (fun other => D.weight other)
    (fun other => edgeTripleValue D edgeFirst edgeSecond other)
    (atomPairing D edgeFirst edgeSecond ^ 2
      * (1 - atomShare D edgeFirst - atomShare D edgeSecond))
    (sum_erasePair_weight_mul_edgeTripleValue D hedge) ?_
  have habsWeight : ∀ other : Fin sizeIndex, |D.weight other| = D.weight other :=
    fun other => abs_of_pos (D.weight_pos other)
  simp only [habsWeight]
  linarith

/-! ## The ordered index sets -/

/-- Ordered pairs of distinct atoms, at every ambient size: the certificate's
index set.  A multiplier lives on ORDERED pairs, so a certificate may put its
mass on either orientation or split it — the aggregate below symmetrizes, so
only the sum of the two orientations is ever read. -/
def orderedDistinctPairs (sizeIndex : ℕ) : Finset (Fin sizeIndex × Fin sizeIndex) :=
  Finset.univ.filter fun pair => pair.1 ≠ pair.2

/-- Ordered triples of pairwise-distinct atoms, at every ambient size: the
index set of the erase system's unknowns, six times over.  The general-size
sibling of the shipped size-six `Gtz.distinctTriples`. -/
def orderedDistinctTriples (sizeIndex : ℕ) :
    Finset (Fin sizeIndex × Fin sizeIndex × Fin sizeIndex) :=
  Finset.univ.filter fun triple =>
    triple.1 ≠ triple.2.1 ∧ triple.1 ≠ triple.2.2 ∧ triple.2.1 ≠ triple.2.2

theorem mem_orderedDistinctPairs {pair : Fin sizeIndex × Fin sizeIndex} :
    pair ∈ orderedDistinctPairs sizeIndex ↔ pair.1 ≠ pair.2 := by
  simp only [orderedDistinctPairs, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_orderedDistinctTriples
    {triple : Fin sizeIndex × Fin sizeIndex × Fin sizeIndex} :
    triple ∈ orderedDistinctTriples sizeIndex
      ↔ triple.1 ≠ triple.2.1 ∧ triple.1 ≠ triple.2.2 ∧ triple.2.1 ≠ triple.2.2 := by
  simp only [orderedDistinctTriples, Finset.mem_filter, Finset.mem_univ, true_and]

/-- At size six this IS the shipped `Gtz.distinctTriples` of
`Gtz/Quantitative/EqualShareSixThree.lean` — same filter, same predicate.  The
two are kept apart only because that one is hardwired to `Fin 6` and the
certificates below are stated at every size. -/
theorem orderedDistinctTriples_six_eq_distinctTriples :
    orderedDistinctTriples 6 = distinctTriples := rfl

/-! ## Coordinate permutations of the triple index -/

private def swapFirstSecondEquiv (sizeIndex : ℕ) :
    (Fin sizeIndex × Fin sizeIndex × Fin sizeIndex)
      ≃ (Fin sizeIndex × Fin sizeIndex × Fin sizeIndex) where
  toFun triple := (triple.2.1, triple.1, triple.2.2)
  invFun triple := (triple.2.1, triple.1, triple.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def swapSecondThirdEquiv (sizeIndex : ℕ) :
    (Fin sizeIndex × Fin sizeIndex × Fin sizeIndex)
      ≃ (Fin sizeIndex × Fin sizeIndex × Fin sizeIndex) where
  toFun triple := (triple.1, triple.2.2, triple.2.1)
  invFun triple := (triple.1, triple.2.2, triple.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindexing the ordered-triple sum by the transposition of the first two
coordinates.  The index set is defined by a symmetric distinctness condition,
so the transposition is a bijection of it. -/
theorem sum_orderedDistinctTriples_swapFirstSecond
    (summand : Fin sizeIndex × Fin sizeIndex × Fin sizeIndex → ℝ) :
    ∑ triple ∈ orderedDistinctTriples sizeIndex, summand triple
      = ∑ triple ∈ orderedDistinctTriples sizeIndex,
          summand (triple.2.1, triple.1, triple.2.2) := by
  refine Finset.sum_equiv (swapFirstSecondEquiv sizeIndex) (fun triple => ?_)
    (fun _ _ => rfl)
  simp only [mem_orderedDistinctTriples, swapFirstSecondEquiv, Equiv.coe_fn_mk]
  tauto

/-- Reindexing by the transposition of the last two coordinates. -/
theorem sum_orderedDistinctTriples_swapSecondThird
    (summand : Fin sizeIndex × Fin sizeIndex × Fin sizeIndex → ℝ) :
    ∑ triple ∈ orderedDistinctTriples sizeIndex, summand triple
      = ∑ triple ∈ orderedDistinctTriples sizeIndex,
          summand (triple.1, triple.2.2, triple.2.1) := by
  refine Finset.sum_equiv (swapSecondThirdEquiv sizeIndex) (fun triple => ?_)
    (fun _ _ => rfl)
  simp only [mem_orderedDistinctTriples, swapSecondThirdEquiv, Equiv.coe_fn_mk]
  tauto

/-- Reindexing by the three-cycle `(a, b, x) ↦ (x, a, b)`. -/
theorem sum_orderedDistinctTriples_rotateRight
    (summand : Fin sizeIndex × Fin sizeIndex × Fin sizeIndex → ℝ) :
    ∑ triple ∈ orderedDistinctTriples sizeIndex, summand triple
      = ∑ triple ∈ orderedDistinctTriples sizeIndex,
          summand (triple.2.2, triple.1, triple.2.1) := by
  rw [sum_orderedDistinctTriples_swapFirstSecond summand,
    sum_orderedDistinctTriples_swapSecondThird
      (fun triple => summand (triple.2.1, triple.1, triple.2.2))]

/-- Reindexing by the three-cycle `(a, b, x) ↦ (b, x, a)`. -/
theorem sum_orderedDistinctTriples_rotateLeft
    (summand : Fin sizeIndex × Fin sizeIndex × Fin sizeIndex → ℝ) :
    ∑ triple ∈ orderedDistinctTriples sizeIndex, summand triple
      = ∑ triple ∈ orderedDistinctTriples sizeIndex,
          summand (triple.2.1, triple.2.2, triple.1) := by
  rw [sum_orderedDistinctTriples_swapSecondThird summand,
    sum_orderedDistinctTriples_swapFirstSecond
      (fun triple => summand (triple.1, triple.2.2, triple.2.1))]

/-- Reindexing by the transposition of the outer coordinates. -/
theorem sum_orderedDistinctTriples_swapFirstThird
    (summand : Fin sizeIndex × Fin sizeIndex × Fin sizeIndex → ℝ) :
    ∑ triple ∈ orderedDistinctTriples sizeIndex, summand triple
      = ∑ triple ∈ orderedDistinctTriples sizeIndex,
          summand (triple.2.2, triple.2.1, triple.1) := by
  rw [sum_orderedDistinctTriples_swapFirstSecond summand,
    sum_orderedDistinctTriples_swapSecondThird
      (fun triple => summand (triple.2.1, triple.1, triple.2.2)),
    sum_orderedDistinctTriples_swapFirstSecond
      (fun triple => summand (triple.2.2, triple.1, triple.2.1))]

/-! ## The triple value is a function of the unordered triple

The shipped `Gtz.edgeTripleValue_edge_comm` gives the endpoint transposition;
the remaining four permutations follow the same way, by reading the value as
the symmetric pairing product `Gtz.edgeTripleValue_eq_atomPairingProduct` and
commuting pairings. -/

theorem edgeTripleValue_rotateRight (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    edgeTripleValue D first second third = edgeTripleValue D third first second := by
  rw [edgeTripleValue_eq_atomPairingProduct, edgeTripleValue_eq_atomPairingProduct,
    atomPairing_comm D third first, atomPairing_comm D third second]
  ring

theorem edgeTripleValue_rotateLeft (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    edgeTripleValue D first second third = edgeTripleValue D second third first := by
  rw [edgeTripleValue_eq_atomPairingProduct, edgeTripleValue_eq_atomPairingProduct,
    atomPairing_comm D second first, atomPairing_comm D third first]
  ring

theorem edgeTripleValue_swapSecondThird (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    edgeTripleValue D first second third = edgeTripleValue D first third second := by
  rw [edgeTripleValue_eq_atomPairingProduct, edgeTripleValue_eq_atomPairingProduct,
    atomPairing_comm D third second]
  ring

theorem edgeTripleValue_swapFirstThird (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    edgeTripleValue D first second third = edgeTripleValue D third second first := by
  rw [edgeTripleValue_eq_atomPairingProduct, edgeTripleValue_eq_atomPairingProduct,
    atomPairing_comm D third second, atomPairing_comm D third first,
    atomPairing_comm D second first]
  ring

/-! ## The certificate: multipliers, aggregate, certified value -/

/-- **THE AGGREGATE COEFFICIENT** a triple receives from a multiplier vector:
the multiplier of each of its three edges times the weight of the opposite
atom, summed, with both orientations of every edge counted.  Manifestly
symmetric in the three atoms, which is what lets the certificate be stated over
ordered triples with no canonical representative.

Cancellation lives here: a triple lying on two edges of opposite multiplier
sign can receive aggregate coefficient ZERO, and the sharpest certificates in
the measured corpus — the sixteen two-edge ones — are exactly that. -/
noncomputable def farkasAggregate (D : WeightedDesign sizeIndex 3)
    (multiplier : Fin sizeIndex → Fin sizeIndex → ℝ)
    (first second third : Fin sizeIndex) : ℝ :=
  (multiplier first second + multiplier second first) * D.weight third
    + (multiplier first third + multiplier third first) * D.weight second
    + (multiplier second third + multiplier third second) * D.weight first

/-- **THE CERTIFIED VALUE**: the multiplier-weighted combination of the erase
right-hand sides.  Built from the DATUM alone — the pairings, the shares and
the multipliers — with no reference to the triple values.  That is what makes
the region below a condition on the design rather than a restatement of its
own conclusion. -/
noncomputable def farkasCertificateValue (D : WeightedDesign sizeIndex 3)
    (multiplier : Fin sizeIndex → Fin sizeIndex → ℝ) : ℝ :=
  ∑ pair ∈ orderedDistinctPairs sizeIndex,
    multiplier pair.1 pair.2
      * (atomPairing D pair.1 pair.2 ^ 2
          * (1 - atomShare D pair.1 - atomShare D pair.2))

/-- One ordered slot's contribution: the multiplier of the leading pair times
the trailing atom's weighted triple value.  Private scaffolding for the
aggregation identity. -/
private noncomputable def farkasBaseSummand (D : WeightedDesign sizeIndex 3)
    (multiplier : Fin sizeIndex → Fin sizeIndex → ℝ)
    (triple : Fin sizeIndex × Fin sizeIndex × Fin sizeIndex) : ℝ :=
  multiplier triple.1 triple.2.1
    * (D.weight triple.2.2 * edgeTripleValue D triple.1 triple.2.1 triple.2.2)

/-- The certified value expands, edge law by edge law, into the ordered-slot
sum: each edge's right-hand side is replaced by its star sum, and the pairs
with their stars are exactly the ordered distinct triples. -/
theorem farkasCertificateValue_eq_sum_orderedDistinctTriples
    (D : WeightedDesign sizeIndex 3) (multiplier : Fin sizeIndex → Fin sizeIndex → ℝ) :
    farkasCertificateValue D multiplier
      = ∑ triple ∈ orderedDistinctTriples sizeIndex,
          farkasBaseSummand D multiplier triple := by
  classical
  rw [farkasCertificateValue, orderedDistinctPairs, orderedDistinctTriples,
    Finset.sum_filter, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, farkasBaseSummand]
  refine Finset.sum_congr rfl fun edgeFirst _ => ?_
  refine Finset.sum_congr rfl fun edgeSecond _ => ?_
  by_cases hedge : edgeFirst = edgeSecond
  · subst hedge
    simp
  · have hstar :
        (Finset.univ.filter fun other => edgeFirst ≠ other ∧ edgeSecond ≠ other)
          = (Finset.univ.erase edgeFirst).erase edgeSecond := by
      ext other
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        and_true]
      exact ⟨fun hpair => ⟨hpair.2.symm, hpair.1.symm⟩,
        fun hpair => ⟨hpair.2.symm, hpair.1.symm⟩⟩
    have hinner : ∀ other : Fin sizeIndex,
        (if edgeFirst ≠ edgeSecond ∧ edgeFirst ≠ other ∧ edgeSecond ≠ other then
            multiplier edgeFirst edgeSecond
              * (D.weight other * edgeTripleValue D edgeFirst edgeSecond other)
          else 0)
        = multiplier edgeFirst edgeSecond
            * (if edgeFirst ≠ other ∧ edgeSecond ≠ other then
                D.weight other * edgeTripleValue D edgeFirst edgeSecond other
              else 0) := by
      intro other
      by_cases hother : edgeFirst ≠ other ∧ edgeSecond ≠ other
      · rw [if_pos ⟨hedge, hother⟩, if_pos hother]
      · rw [if_neg (fun hall => hother ⟨hall.2.1, hall.2.2⟩), if_neg hother,
          mul_zero]
    rw [if_pos hedge, Finset.sum_congr rfl fun other _ => hinner other,
      ← Finset.mul_sum, ← Finset.sum_filter, hstar,
      sum_erasePair_weight_mul_edgeTripleValue D hedge]

/-- **THE AGGREGATION IDENTITY.**  Six times the certified value is the
aggregate-weighted sum of the triple values over ordered distinct triples.

This is the whole content of the multi-edge form.  The proof is symmetrization:
the aggregate is the sum of the six ordered slot coefficients of the triple, the
triple value is invariant under all six coordinate permutations, and each of the
six resulting sums is the slot sum reindexed by a permutation of the index set.
The factor six counts the orderings and appears identically on both sides of
every inequality below. -/
theorem sum_orderedDistinctTriples_farkasAggregate_mul_edgeTripleValue
    (D : WeightedDesign sizeIndex 3) (multiplier : Fin sizeIndex → Fin sizeIndex → ℝ) :
    ∑ triple ∈ orderedDistinctTriples sizeIndex,
        farkasAggregate D multiplier triple.1 triple.2.1 triple.2.2
          * edgeTripleValue D triple.1 triple.2.1 triple.2.2
      = 6 * farkasCertificateValue D multiplier := by
  have hexpand : ∑ triple ∈ orderedDistinctTriples sizeIndex,
        farkasAggregate D multiplier triple.1 triple.2.1 triple.2.2
          * edgeTripleValue D triple.1 triple.2.1 triple.2.2
      = (∑ triple ∈ orderedDistinctTriples sizeIndex,
          farkasBaseSummand D multiplier triple)
        + (∑ triple ∈ orderedDistinctTriples sizeIndex,
            farkasBaseSummand D multiplier (triple.2.1, triple.1, triple.2.2))
        + (∑ triple ∈ orderedDistinctTriples sizeIndex,
            farkasBaseSummand D multiplier (triple.1, triple.2.2, triple.2.1))
        + (∑ triple ∈ orderedDistinctTriples sizeIndex,
            farkasBaseSummand D multiplier (triple.2.2, triple.1, triple.2.1))
        + (∑ triple ∈ orderedDistinctTriples sizeIndex,
            farkasBaseSummand D multiplier (triple.2.1, triple.2.2, triple.1))
        + (∑ triple ∈ orderedDistinctTriples sizeIndex,
            farkasBaseSummand D multiplier (triple.2.2, triple.2.1, triple.1)) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun triple _ => ?_
    simp only [farkasBaseSummand, farkasAggregate]
    rw [← edgeTripleValue_edge_comm D triple.1 triple.2.1 triple.2.2,
      ← edgeTripleValue_swapSecondThird D triple.1 triple.2.1 triple.2.2,
      ← edgeTripleValue_rotateRight D triple.1 triple.2.1 triple.2.2,
      ← edgeTripleValue_rotateLeft D triple.1 triple.2.1 triple.2.2,
      ← edgeTripleValue_swapFirstThird D triple.1 triple.2.1 triple.2.2]
    ring
  rw [hexpand, farkasCertificateValue_eq_sum_orderedDistinctTriples,
    ← sum_orderedDistinctTriples_swapFirstSecond (farkasBaseSummand D multiplier),
    ← sum_orderedDistinctTriples_swapSecondThird (farkasBaseSummand D multiplier),
    ← sum_orderedDistinctTriples_rotateRight (farkasBaseSummand D multiplier),
    ← sum_orderedDistinctTriples_rotateLeft (farkasBaseSummand D multiplier),
    ← sum_orderedDistinctTriples_swapFirstThird (farkasBaseSummand D multiplier)]
  ring

/-! ## The multi-edge capacity lemma -/

/-- **THE MULTI-EDGE CAPACITY LEMMA** at every ambient size.  Given real
multipliers on the ordered pairs and a set of triples slated to read minus, if
the free triples' absolute aggregate mass minus the forced triples' signed
aggregate mass falls strictly short of six times the certified value, then some
forced triple carries a nonnegative value.

The single-edge lemma is the instance where the multiplier is supported on one
ordered pair; the gain is that a triple lying on several supported edges is
charged only its AGGREGATE coefficient, which the certificate can drive to zero.
No genericity, heaviness, exceptionality or failure hypothesis, exactly as in
the single-edge layer.  The magnitudes enter as `Gtz.tripleRadius` through
torsion (`Gtz.abs_edgeTripleValue`). -/
theorem exists_nonneg_edgeTripleValue_of_farkasCertificate
    (D : WeightedDesign sizeIndex 3)
    (multiplier : Fin sizeIndex → Fin sizeIndex → ℝ)
    (forcedTriples : Finset (Fin sizeIndex × Fin sizeIndex × Fin sizeIndex))
    (hforcedSubset : forcedTriples ⊆ orderedDistinctTriples sizeIndex)
    (hviolation :
      ∑ triple ∈ orderedDistinctTriples sizeIndex \ forcedTriples,
          |farkasAggregate D multiplier triple.1 triple.2.1 triple.2.2|
            * tripleRadius D triple.1 triple.2.1 triple.2.2
        - ∑ triple ∈ forcedTriples,
            farkasAggregate D multiplier triple.1 triple.2.1 triple.2.2
              * tripleRadius D triple.1 triple.2.1 triple.2.2
      < 6 * farkasCertificateValue D multiplier) :
    ∃ triple ∈ forcedTriples,
      0 ≤ edgeTripleValue D triple.1 triple.2.1 triple.2.2 := by
  refine exists_nonneg_of_farkasCertificate (orderedDistinctTriples sizeIndex)
    forcedTriples hforcedSubset
    (fun triple => farkasAggregate D multiplier triple.1 triple.2.1 triple.2.2)
    (fun triple => edgeTripleValue D triple.1 triple.2.1 triple.2.2)
    (6 * farkasCertificateValue D multiplier)
    (sum_orderedDistinctTriples_farkasAggregate_mul_edgeTripleValue D multiplier) ?_
  simpa only [abs_edgeTripleValue] using hviolation

/-! ## The forced-minus predicate is a property of the unordered triple

A certificate's forced set must be closed under the six orderings — the
aggregation identity counts every triple six times, so a forced set holding only
some orderings would charge the free side for the rest.  Closing it requires
knowing that `Gtz.IsForcedMinusTriple` does not see the ordering.  It does not:
the trace clause is a disjunction over the three pivots, and the sign-blind gap
and the radius are symmetric.  The gap's `S₃` invariance ships
(`Gtz.excessGap_swap`, `Gtz.excessGap_rotate`, `Gtz.excessGap_swapPair`); the
radius inherits it from the triple value through `Gtz.abs_edgeTripleValue`, and
the trace's own symmetry in its two non-pivot slots is one `ring`. -/

/-- The trace leg does not see the order of its two non-pivot atoms. -/
theorem discriminantTrace_swapPair (D : WeightedDesign sizeIndex 3)
    (pivot pairFirst pairSecond : Fin sizeIndex) :
    discriminantTrace D pivot pairFirst pairSecond
      = discriminantTrace D pivot pairSecond pairFirst := by
  simp only [discriminantTrace]
  ring

theorem tripleRadius_edge_comm (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    tripleRadius D first second third = tripleRadius D second first third := by
  rw [← abs_edgeTripleValue, ← abs_edgeTripleValue, edgeTripleValue_edge_comm]

theorem tripleRadius_rotateRight (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    tripleRadius D first second third = tripleRadius D third first second := by
  rw [← abs_edgeTripleValue, ← abs_edgeTripleValue, edgeTripleValue_rotateRight]

theorem tripleRadius_rotateLeft (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    tripleRadius D first second third = tripleRadius D second third first := by
  rw [← abs_edgeTripleValue, ← abs_edgeTripleValue, edgeTripleValue_rotateLeft]

theorem tripleRadius_swapSecondThird (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    tripleRadius D first second third = tripleRadius D first third second := by
  rw [← abs_edgeTripleValue, ← abs_edgeTripleValue, edgeTripleValue_swapSecondThird]

theorem tripleRadius_swapFirstThird (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    tripleRadius D first second third = tripleRadius D third second first := by
  rw [← abs_edgeTripleValue, ← abs_edgeTripleValue, edgeTripleValue_swapFirstThird]

/-- Forced-minus survives the transposition of the first two atoms. -/
theorem isForcedMinusTriple_edge_comm (D : WeightedDesign sizeIndex 3)
    {first second third : Fin sizeIndex}
    (hforced : IsForcedMinusTriple D first second third) :
    IsForcedMinusTriple D second first third := by
  obtain ⟨htrace, hplus, hminus⟩ := hforced
  refine ⟨?_, ?_, ?_⟩
  · rw [← discriminantTrace_swapPair D third first second]
    tauto
  · rw [← excessGap_swap D first second third,
      ← tripleRadius_edge_comm D first second third]
    exact hplus
  · rw [← excessGap_swap D first second third,
      ← tripleRadius_edge_comm D first second third]
    exact hminus

/-- Forced-minus survives the three-cycle `(a, b, c) ↦ (c, a, b)`. -/
theorem isForcedMinusTriple_rotateRight (D : WeightedDesign sizeIndex 3)
    {first second third : Fin sizeIndex}
    (hforced : IsForcedMinusTriple D first second third) :
    IsForcedMinusTriple D third first second := by
  obtain ⟨htrace, hplus, hminus⟩ := hforced
  refine ⟨?_, ?_, ?_⟩
  · rw [← discriminantTrace_swapPair D first second third,
      ← discriminantTrace_swapPair D second first third]
    tauto
  · rw [← excessGap_rotate D first second third,
      ← tripleRadius_rotateRight D first second third]
    exact hplus
  · rw [← excessGap_rotate D first second third,
      ← tripleRadius_rotateRight D first second third]
    exact hminus

/-- Forced-minus survives the three-cycle `(a, b, c) ↦ (b, c, a)`. -/
theorem isForcedMinusTriple_rotateLeft (D : WeightedDesign sizeIndex 3)
    {first second third : Fin sizeIndex}
    (hforced : IsForcedMinusTriple D first second third) :
    IsForcedMinusTriple D second third first :=
  isForcedMinusTriple_rotateRight D (isForcedMinusTriple_rotateRight D hforced)

/-- Forced-minus survives the transposition of the last two atoms. -/
theorem isForcedMinusTriple_swapSecondThird (D : WeightedDesign sizeIndex 3)
    {first second third : Fin sizeIndex}
    (hforced : IsForcedMinusTriple D first second third) :
    IsForcedMinusTriple D first third second :=
  isForcedMinusTriple_edge_comm D
    (isForcedMinusTriple_rotateRight D hforced)

/-- Forced-minus survives the transposition of the outer atoms. -/
theorem isForcedMinusTriple_swapFirstThird (D : WeightedDesign sizeIndex 3)
    {first second third : Fin sizeIndex}
    (hforced : IsForcedMinusTriple D first second third) :
    IsForcedMinusTriple D third second first :=
  isForcedMinusTriple_edge_comm D
    (isForcedMinusTriple_rotateLeft D hforced)

/-! ## The certificate region and its clash bridge -/

/-- **THE FARKAS-CERTIFICATE REGION**: some multiplier vector and some
forced-minus set of ordered triples satisfy the violation inequality.  The
semialgebraic sufficient condition of the multi-edge layer, in shipped
vocabulary — an absolute-value polynomial inequality over a Boolean combination
of `Gtz.IsForcedMinusTriple` clauses, existentially quantified over the
multipliers.

External exact measurement (not kernel fact): in the Phase-3 corpus of `307`
box-infeasible points, `78` carry a certificate here and no forced-box-deficit
edge, and `23` of those `78` are exceptional-locus points.  The `5` remaining
points are infeasible only beyond the box relaxation and no certificate of this
shape can reach them. -/
def HasFarkasCertificate (D : WeightedDesign sizeIndex 3) : Prop :=
  ∃ multiplier : Fin sizeIndex → Fin sizeIndex → ℝ,
    ∃ forcedTriples ⊆ orderedDistinctTriples sizeIndex,
      (∀ triple ∈ forcedTriples,
          IsForcedMinusTriple D triple.1 triple.2.1 triple.2.2)
        ∧ ∑ triple ∈ orderedDistinctTriples sizeIndex \ forcedTriples,
              |farkasAggregate D multiplier triple.1 triple.2.1 triple.2.2|
                * tripleRadius D triple.1 triple.2.1 triple.2.2
            - ∑ triple ∈ forcedTriples,
                farkasAggregate D multiplier triple.1 triple.2.1 triple.2.2
                  * tripleRadius D triple.1 triple.2.1 triple.2.2
          < 6 * farkasCertificateValue D multiplier

/-- **THE MULTI-EDGE CLASH BRIDGE**: a design carrying a Farkas certificate
carries an ordered sign-clash triple.  Composition of the multi-edge capacity
lemma, the torsion bridge `Gtz.edgeTripleValue_eq_atomPairingProduct` and the
shipped forcing bridge — the same three steps as
`Gtz.exists_isSignClashTriple_of_forcedBoxDeficit`, one level up.  No
genericity, no heaviness, no exceptionality, no failure hypothesis, at every
ambient size. -/
theorem exists_isSignClashTriple_of_hasFarkasCertificate
    (D : WeightedDesign sizeIndex 3) (hcertificate : HasFarkasCertificate D) :
    ∃ pivot pairFirst pairSecond : Fin sizeIndex,
      pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ IsSignClashTriple D pivot pairFirst pairSecond := by
  obtain ⟨multiplier, forcedTriples, hforcedSubset, hforced, hviolation⟩ :=
    hcertificate
  obtain ⟨triple, hmember, hnonneg⟩ :=
    exists_nonneg_edgeTripleValue_of_farkasCertificate D multiplier forcedTriples
      hforcedSubset hviolation
  obtain ⟨hfirstSecond, hfirstThird, hsecondThird⟩ :=
    mem_orderedDistinctTriples.mp (hforcedSubset hmember)
  rw [edgeTripleValue_eq_atomPairingProduct] at hnonneg
  exact exists_isSignClashTriple_of_forcedMinus_of_nonneg_product D
    hfirstSecond hfirstThird hsecondThird (hforced triple hmember) hnonneg

/-! ## The residue splits -/

/-- **THE MULTI-EDGE RESIDUE SPLIT.**  The open proposition reduces to its
certificate-free residue: designs carrying a Farkas certificate are covered by
the bridge above.  One-way only; nothing is claimed about the residue. -/
theorem genericExceptionalSignClash_of_forall_without_farkasCertificate_signClash
    (hresidue : ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
      (phaseFreeOfDesign D).IsExceptional → ¬ HasFarkasCertificate D →
      ∃ pivot pairFirst pairSecond : Fin 6,
        pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ IsSignClashTriple D pivot pairFirst pairSecond) :
    GenericExceptionalSignClash := by
  intro D hheavy hgeneric hexceptional
  by_cases hcertificate : HasFarkasCertificate D
  · exact exists_isSignClashTriple_of_hasFarkasCertificate D hcertificate
  · exact hresidue D hheavy hgeneric hexceptional hcertificate

/-- **THE JOINT RESIDUE SPLIT** — the sharpest reduction the two capacity
layers give together.  It is enough to clash on the designs carrying NEITHER a
forced-box-deficit edge NOR a Farkas certificate: everything else is covered,
by the single-edge bridge
`Gtz.exists_isSignClashTriple_of_hasForcedBoxDeficitEdge` on one side and by
`Gtz.exists_isSignClashTriple_of_hasFarkasCertificate` on the other.

The hypothesis is strictly weaker than either single split's, so this is the
strictly stronger theorem, and it needs NO inclusion between the two regions —
which is why it is stated this way rather than by subsuming the deficit region
into the certificate region.  External measurement sizes the joint residue at
`5` of the `307` corpus kills, with no exceptional point among them. -/
theorem genericExceptionalSignClash_of_forall_without_certificate_signClash
    (hresidue : ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
      (phaseFreeOfDesign D).IsExceptional → ¬ HasForcedBoxDeficitEdge D →
      ¬ HasFarkasCertificate D →
      ∃ pivot pairFirst pairSecond : Fin 6,
        pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ IsSignClashTriple D pivot pairFirst pairSecond) :
    GenericExceptionalSignClash := by
  intro D hheavy hgeneric hexceptional
  by_cases hdeficit : HasForcedBoxDeficitEdge D
  · exact exists_isSignClashTriple_of_hasForcedBoxDeficitEdge D hdeficit
  · by_cases hcertificate : HasFarkasCertificate D
    · exact exists_isSignClashTriple_of_hasFarkasCertificate D hcertificate
    · exact hresidue D hheavy hgeneric hexceptional hdeficit hcertificate

/-- The joint residue statement reaches the open cell, through the shipped
sufficiency `Gtz.gtzWeighted_six_three_of_genericExceptionalSignClash`. -/
theorem gtzWeighted_six_three_of_forall_without_certificate_signClash
    (hresidue : ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
      (phaseFreeOfDesign D).IsExceptional → ¬ HasForcedBoxDeficitEdge D →
      ¬ HasFarkasCertificate D →
      ∃ pivot pairFirst pairSecond : Fin 6,
        pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ IsSignClashTriple D pivot pairFirst pairSecond) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_genericExceptionalSignClash
    (genericExceptionalSignClash_of_forall_without_certificate_signClash hresidue)

end Gtz
