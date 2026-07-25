/-
# Why no Positivstellensatz certificate of the CLOSED kind can exist at `(7,3)`

`Gtz.Quantitative.DiscriminantSystem` reduces all of rank three to one sentence,
`DiscriminantCovering 7`: every all-heavy weighted `(7,3)` design has a triple
with `discriminantTrace ≥ 0` and `discriminantTie ≥ 0`.  Emptiness of the
failure set of a semialgebraic sentence has a Stengle certificate, and finding
one in rational arithmetic would be a kernel-checkable proof.  This file records
the structural obstruction that every such attempt has to route around, and it is
DEGREE-FREE: it rules out the entire Putinar/Schmuedgen half of the
Positivstellensatz at every degree, for every weight class, polynomial or not.

**The mechanism.**  Write `g_T := - discriminantTie D T`, so the failure of the
tie leg at `T` is `g_T > 0`.  A Putinar (or Schmuedgen) certificate proves
emptiness of the CLOSED system `{g_T ≥ 0 for every T} ∩ {region}` by an identity
`-1 = sos + Σ_T sos_T · g_T + (region multipliers) + (ideal)`.  Rearranged on the
region that identity says exactly

  `Σ_T sos_T(D) · discriminantTie D T ≥ 1`  for every all-heavy design `D`,

i.e. it produces a nonnegatively weighted aggregate of the tie leg with a uniform
POSITIVE floor.  `not_hasUniformTieAggregate_seven` shows no such aggregate
exists — at the split tetrahedron every one of the 35 tie legs is `≤ 0`, so every
nonnegatively weighted aggregate there is `≤ 0`.  The hypothesis is on the
WEIGHTS ONLY (arbitrary real-valued functions of the design, no degree bound, no
polynomiality, no symmetry), so the conclusion holds at every degree.

Equivalently and more directly: `closedTieFailure_inhabited_seven` exhibits a
point of the closed failure system.  A closed basic semialgebraic set that is
INHABITED has no emptiness certificate of any kind.  What is empty is the STRICT
system `{g_T > 0 for every T}`, and separating the two is precisely Stengle's
multiplicative monoid — a certificate must carry a factor `∏_T g_T^{e_T}` with at
least one `e_T ≥ 1`.

**The degree consequence, computed, not mechanised.**  That multiplier has to
vanish at every design of the tie locus.  The split-tetrahedron orbit is indexed
by the 105 colourings of the seven atoms with multiplicity profile `(2,2,2,1)`,
and at each of them the tie leg vanishes exactly on the 20 RAINBOW triples and
equals `-8` on the other 15 (`splitSevenDesign_discriminantTie_of_rainbowDirections`
and `..._of_repeatedDirection`).  So the support `{T : e_T ≥ 1}` must be a hitting
set for the 105 rainbow families.  Exhaustive search over all 35 triples gives
minimum hitting-set size 4 (sizes 1, 2 and 3 all fail; 5355 hitting sets of size 4
exist, one being `{012, 013, 024, 034}`).  Since `discriminantTie` has degree 3 in
the Gram entries and 6 in the atom coordinates,

  every Stengle certificate for `DiscriminantCovering 7` has degree at least
  `12` in the 28 Gram entries and at least `24` in the 21 atom coordinates,

and this uses only the ONE tie orbit that is mechanised here; the further orbits
the numerics report can only raise it.  For calibration: no machine-checked
Positivstellensatz certificate above roughly six variables and degree eight
exists in any proof assistant, and the sum-of-squares Gram matrix for degree 12
in 35 variables has monomial basis `C(41,6) = 4 496 388`.

**Two further routes measured and refuted, recorded here but not mechanised.**

* The VOLUME-WEIGHTED aggregate.  At the split tetrahedron the weights of any
  aggregate must vanish on the 15 direction-repeating triples, and
  `det(P_TT) = t_a t_b t_c · det(Gram_T)` is the natural — essentially the only
  natural — weight that does, being the square of the triple's volume form and
  hence nonnegative for free.  It FAILS, exactly, at the integer-atom design

    `(-1,1,0)  (0,2,2)  (0,1,-1)  (-1,0,1)  (-1,-2,0)  (1,-2,2)  (-2,-1,-1)`
    with weights `77/342, 7/114, 67/228, 31/114, 2/171, 1/57, 9/76`,

  which is exactly Parseval, all-heavy with leverages `2, 8, 2, 2, 5, 9, 6`, has
  11 dominating triples — and carries
  `Σ_T det(P_TT) · det(M_TT) = -3986716709/3292458935904 < 0`.  Sampling puts the
  failure rate at 702 of 6181 all-heavy designs, and the second and third powers
  of the weight fail at 386 and 353 of the same 6181.  Scope: this refutes the
  volume weight and its powers, NOT every weight.  A linear program over a
  30-dimensional class of `S_7`-equivariant weights is infeasible only once
  designs approaching the boundary `t_c → 0` or leverage `→ 1` are admitted, and
  is feasible on interior-conditioned pools, so it is reported as inconclusive.

* The TIE-MAXIMAL selection rule "the triple maximising `discriminantTie`
  dominates" — the rule that would collapse the two-leg disjunction into the
  single leg `max_T discriminantTie ≥ 0` and thereby remove the disjunction from
  the failure set entirely.  It is FALSE.  An exact rational all-heavy `(7,3)`
  design refuting it has atoms with denominator 50 and leverages
  `683/250, 8181/1250, 15217/1250, 169/20, 1713/625, 619/250, 2533/1250`; at it
  the unique tie-maximal triple `(1,2,3)` has
  `discriminantTie = 28010214717/1953125000 > 0` but
  `discriminantMinorSum`-style second symmetric function `-123467447/3125000 < 0`,
  so it carries signature `(+,-,-)` and does not dominate, while eight other
  triples do.  This upgrades the repo's measured `maxResidualDet 0.95634` from a
  statistic to a refutation.

**Complex sanity check.**  Over `C` the single-leg statement is FALSE, as it must
be: at the shared-axis trine of `Gtz.Complex.SharpConstantLedger` every triple has
`max_T det(M_TT) = -1/108` at `(6,3)` and `-1/216` at its `(7,3)` split, with the
second symmetric function `+7` at every triple.  So realness is consumed entirely
by the determinant leg, and any candidate certificate that survives replacing the
triangle monomial `G_ab G_bc G_ca` by a free variable is wrong.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.DecisionAtlasSevenThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

/-! ### The certificate shape a Putinar identity would produce -/

/-- **A uniformly positive nonnegatively weighted tie aggregate at `(7,3)`**: a
strictly positive floor together with, at every all-heavy design, nonnegative
weights on the 35 triples whose weighted sum of tie legs clears that floor.

This is exactly what a Putinar or Schmuedgen certificate for the emptiness of the
closed tie-failure system delivers after rearranging the certifying identity: the
sum-of-squares multipliers of the generators `- discriminantTie` are the weights,
they are nonnegative because they are sums of squares, and the floor is `1`.  The
weights here are arbitrary real-valued functions of the design — no degree bound,
no polynomiality, no equivariance — so refuting this shape refutes the whole
Putinar half of the Positivstellensatz at every degree. -/
def HasUniformTieAggregateSeven : Prop :=
  ∃ floor : ℝ, 0 < floor ∧
    ∀ design : WeightedDesign 7 3, AllHeavy design →
      ∃ weight : Fin 7 × Fin 7 × Fin 7 → ℝ, (∀ triple, 0 ≤ weight triple) ∧
        floor ≤ ∑ triple ∈ increasingTriplesSeven,
          weight triple * discriminantTie design triple.1 triple.2.1 triple.2.2

/-- **Every nonnegatively weighted tie aggregate at the split tetrahedron is
nonpositive.**  Each of the 35 tie legs is `≤ 0` there
(`splitSevenDesign_discriminantTie_nonpos`), so multiplying by a nonnegative
weight and summing cannot escape `≤ 0`.  The weights are unconstrained: this is a
statement about the design, not about any weight class. -/
theorem splitSevenDesign_weightedTieAggregate_nonpos
    (weight : Fin 7 × Fin 7 × Fin 7 → ℝ) (hweightNonneg : ∀ triple, 0 ≤ weight triple) :
    ∑ triple ∈ increasingTriplesSeven,
        weight triple
          * discriminantTie splitSevenDesign triple.1 triple.2.1 triple.2.2 ≤ 0 := by
  refine Finset.sum_nonpos fun triple hmem => ?_
  obtain ⟨hpivotFirst, hpivotSecond, hpairDistinct⟩ :=
    increasingTriplesSeven_distinct hmem
  exact mul_nonpos_of_nonneg_of_nonpos (hweightNonneg triple)
    (splitSevenDesign_discriminantTie_nonpos hpivotFirst hpivotSecond hpairDistinct)

/-- **THE DEGREE-FREE OBSTRUCTION.**  No uniformly positive nonnegatively
weighted tie aggregate exists at `(7,3)`.  Consequently no Putinar and no
Schmuedgen certificate for the covering exists AT ANY DEGREE: every such
certificate would rearrange into one, with the sum-of-squares multipliers of the
tie generators as its weights and floor `1`.  Any Positivstellensatz certificate
must therefore be of the strict Stengle kind, carrying a nonempty product of the
strict generators in its multiplicative monoid part. -/
theorem not_hasUniformTieAggregateSeven : ¬ HasUniformTieAggregateSeven := by
  rintro ⟨floor, hfloorPos, hcertificate⟩
  obtain ⟨weight, hweightNonneg, hfloorLe⟩ :=
    hcertificate splitSevenDesign splitSevenDesign_allHeavy
  exact absurd (hfloorLe.trans
    (splitSevenDesign_weightedTieAggregate_nonpos weight hweightNonneg))
    (not_le.mpr hfloorPos)

/-! ### The closed failure system is inhabited -/

/-- **The closed relaxation of the tie-failure system has a point.**  Replacing
each strict failure `discriminantTie < 0` by its non-strict form produces a basic
closed semialgebraic system that the split tetrahedron satisfies.  An inhabited
closed system has no emptiness certificate of any kind, which is the geometric
form of `not_hasUniformTieAggregateSeven`. -/
theorem closedTieFailure_inhabited_seven :
    ∃ design : WeightedDesign 7 3, AllHeavy design ∧
      ∀ triple ∈ increasingTriplesSeven,
        discriminantTie design triple.1 triple.2.1 triple.2.2 ≤ 0 := by
  refine ⟨splitSevenDesign, splitSevenDesign_allHeavy, fun triple hmem => ?_⟩
  obtain ⟨hpivotFirst, hpivotSecond, hpairDistinct⟩ :=
    increasingTriplesSeven_distinct hmem
  exact splitSevenDesign_discriminantTie_nonpos hpivotFirst hpivotSecond hpairDistinct

/-- **The same for the covering's own two-leg failure system.**  The covering
fails at a triple when one of its legs is negative; relaxing both legs to
non-strict form gives a system the split tetrahedron satisfies through its tie
leg alone.  So the obstruction survives the disjunctive encoding as well: it is
not an artefact of dropping the trace leg. -/
theorem closedCoveringFailure_inhabited_seven :
    ∃ design : WeightedDesign 7 3, AllHeavy design ∧
      ∀ triple ∈ increasingTriplesSeven,
        discriminantTrace design triple.1 triple.2.1 triple.2.2 ≤ 0
          ∨ discriminantTie design triple.1 triple.2.1 triple.2.2 ≤ 0 := by
  obtain ⟨design, hheavy, htie⟩ := closedTieFailure_inhabited_seven
  exact ⟨design, hheavy, fun triple hmem => Or.inr (htie triple hmem)⟩

/-! ### The strict system is what is actually empty

`DiscriminantCovering 7` says exactly that the STRICT failure system is empty,
and `discriminantCovering_seven_iff_rank_three` says that sentence is rank three
for every `n`.  Put beside `closedCoveringFailure_inhabited_seven`, the whole
difficulty of the certificate problem is located precisely in the gap between the
strict system and its closure — the tie locus. -/

/-- **The covering is the emptiness of the STRICT failure system**, spelled out
so the contrast with `closedCoveringFailure_inhabited_seven` is a theorem rather
than a remark: what has to be certified empty is inhabited the moment any one of
the strict inequalities is relaxed at the split tetrahedron. -/
theorem discriminantCovering_seven_iff_strictFailure_empty :
    DiscriminantCovering 7 ↔
      ¬ ∃ design : WeightedDesign 7 3, AllHeavy design ∧
          ∀ pivot pairFirst pairSecond : Fin 7, pivot ≠ pairFirst → pivot ≠ pairSecond →
            pairFirst ≠ pairSecond →
              discriminantTrace design pivot pairFirst pairSecond < 0
                ∨ discriminantTie design pivot pairFirst pairSecond < 0 := by
  constructor
  · rintro hcover ⟨design, hheavy, hfails⟩
    obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      htrace, htie⟩ := hcover design hheavy
    rcases hfails pivot pairFirst pairSecond hpivotFirst hpivotSecond hpairDistinct with
      hfail | hfail
    · exact absurd htrace (not_le.mpr hfail)
    · exact absurd htie (not_le.mpr hfail)
  · intro hempty design hheavy
    by_contra hnone
    refine hempty ⟨design, hheavy, fun pivot pairFirst pairSecond hpivotFirst
      hpivotSecond hpairDistinct => ?_⟩
    by_contra hboth
    push Not at hboth
    exact hnone ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      hboth.1, hboth.2⟩

end Gtz
