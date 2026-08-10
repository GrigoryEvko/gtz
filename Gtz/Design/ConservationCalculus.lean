/-
# The conservation calculus: Parseval read against an arbitrary metric

**This module is PACKAGING, not leverage.**  Every statement here is an exact
identity or an immediate sign consequence of one.  None of them decides a branch,
and the weighted ones sit squarely inside the barriered averaging family (the
six recorded barriers: `Gtz.TieRowLaw` pair averaging, the split-tetrahedron
surplus barrier, `sum_weight_mul_liftMargin_eq_neg`,
`sum_offPair_weight_mul_liftMargin_eq_capExcess`, the open-slab aggregate
refutation, and the weighted pivot average).  Their value is that they eliminate
free coordinates and expose the active set, so a later argument can be phrased on
the surviving unknowns instead of on all of them.

Six groups.

**1.  The master law and the two pivot conservation laws.**
`sum_weight_mul_quadForm_eq_trace`: for EVERY square matrix `M` and every weighted
design at any size and rank,

    `sum_y w_y * (a_y . (M a_y))  =  trace M` .

Parseval says the weighted average of any quadratic form over the design is that
form's trace.  The landed mass identity `Gtz.sum_weight_mul_leverage` is this at
`M = 1`.  It is a two-line composition of `Gtz.trace_mul_weightedSubsetMass` and
`Gtz.weightedSubsetMass_univ`, both landed since before this wave and neither
cited by any brief.

Read at the metric `(subsetSum D Q - 1)⁻¹` it becomes
`sum_weight_mul_pivot_eq_trace_inv`: the WEIGHTED pivot average at any base is the
trace of that base's inverse gap, with no hypothesis whatever.  Reading the same
metric against the base's own unweighted atom sum gives the independent
`sum_insider_pivot_eq_rank_add_trace_inv`.  The landed `Gtz.trace_identity` is
exactly the DIFFERENCE of those two laws, which is how it is proved here.

**2.  The insertion pivot law.**  `det_insert_eq_det_mul_one_add_pivot`: adjoining
one atom to a base set with invertible gap multiplies the gap determinant by
`1 + q`, where `q` is that atom's pivot at the base.  This is the INSERT twin of
the landed `Gtz.det_erase_eq_det_mul_pivot_gap` (which carries `1 - q`), and the
tree had only the erase direction.  Two consequences:

  * `pivot_eq_neg_one_of_det_insert_eq_zero` -- if the enlarged gap is singular
    and the base gap is not, the adjoined atom's pivot is EXACTLY `-1`.  On the
    tight-line branch, applied at a base pair with the omitted base axis, this is
    the "omitted axis has pivot minus one" rigidity: it is a boundary anchor, not
    an inequality to budget.
  * `discriminantTie_eq_neg_pairGapExcessOf_mul_one_add_pivot` -- THE BRIDGE
    between the campaign's two vocabularies.  The erasure calculus (`Gtz.pivot`,
    `trace_identity`, `pigeonhole`) and the scalar alphabet (`gapExcessOf`,
    `pairGapExcessOf`, `discriminantTie`) have been carried separately for the
    whole campaign.  They are one identity apart.

**3.  The weighted insertion ledger** (the rank-three conservation law with every
free coordinate eliminated).  `sum_weight_mul_det_add_atomMatrix_fin_three`: for
EVERY `3 x 3` real matrix `N`, with NO hypothesis at all,

    `sum_y w_y * det(N + a_y a_yᵀ)  =  det N + e_2(N)` .

Before Parseval enters at all,
`sum_subset_weight_mul_det_add_atomMatrix_eq_trace_adjugate` gives the same ledger on
any label subset with `trace(adj N * weightedSubsetMass D S)` on the right; the landed
`Gtz.three_weighted_det_add_atomMatrix_eq` is that law written out for three
free-standing vectors.  With Parseval it becomes
`sum_subset_weight_mul_det_add_atomMatrix` and then
`sum_weight_mul_det_insert_fin_three`, the chart-free form of the one-slot collapse:
the free coordinates vanish and only the complement's adjugate readings survive.  The
transported chart version of that collapse, with the refusal consequence attached, is
already landed as `Gtz.unitAxisHiddenOneSlot_weighted_det_sum_eq` and
`Gtz.unitAxisHiddenOneSlot_scalar_nonpos_of_refusal`.

**4.  The erasure collapse, at every cardinality.**
`sum_det_erase_eq_card_sub_three_mul_det`: dropping one label at a time from ANY label
set and totalling the gap determinants gives `(|S| - 3) det - e_2`.  At `|S| = 3` this
is `sum_det_pairGap_eq_neg_secondInvariantOfThree` and hence
`secondInvariantOfThree_tripleGap_eq_sum_pairGapExcessOf`: the UNWEIGHTED flat pair
aggregate of a triple IS minus the second invariant of that triple's gap, which settles
as a theorem the lead the campaign had only conjectured.  At `|S| = 2` it gives
`secondInvariantOfThree_pairGap_eq`, and at `|S| = 4` the card-four statement the plane
branch's windows are phrased in.

**5.  The live-pair averaging barrier, in determinant and pivot coordinates.**  ** THE
DETERMINANT FORM IS NOT NEW: `sum_weight_mul_det_pairGap_add_atomMatrix` IS THE LANDED
`Gtz.sum_weight_mul_discriminantTie` -- the campaign's FIRST recorded barrier,
`TieRowLaw` pair averaging -- and it is derived from it here, not reproved. **  What is
new is the bridge `det_pairGap_add_atomMatrix_eq_discriminantTie`, which identifies the
tie polynomial with the enlarged pair-gap determinant at EVERY third label including the
two endpoints, where the landed card-three reading degenerates and says nothing.

The PIVOT form is the campaign's SIXTH recorded barrier, which was measured and never
mechanized.  `pairGapExcessOf_mul_one_add_trace_inv_pairGap` puts the trace of an inverse
pair gap in design scalars, and `neg_one_lt_sum_weight_mul_pivot_of_isLivePair` then says
the weighted pivot average at a live pair is strictly ABOVE `-1`, while
`det_tripleGap_pos_iff_pivot_lt_neg_one` says a strict completion is a pivot strictly
BELOW `-1`.  ** THE AVERAGE IS ON THE WRONG SIDE OF THE THRESHOLD AT EVERY LIVE PAIR OF
EVERY DESIGN. **  `sum_weight_mul_det_tripleGap_add_atomMatrix` is the same law one
cardinality up, which is the shape the plane branch's card-four windows want.

**6.  Off positive definiteness.**  The trace identity and the excess balance without
the positive definite hypothesis.  The landed proofs spend `PosDef` at exactly one line,
to produce `IsUnit` of the determinant; every hard-side base set in this campaign has an
INDEFINITE gap, where the landed forms simply do not apply.
`isUnit_det_pairGap_of_isLivePair` witnesses that the generalised hypothesis is
satisfiable and strictly weaker: a live pair's gap is invertible with NEGATIVE
determinant, so it is never positive definite.
-/
import Gtz.Design.CapSlack
import Gtz.Quantitative.GeneralPositionWindow
import Gtz.Design.ResidualLeverageLedger
import Gtz.Quantitative.WindowPolarity
import Gtz.Quantitative.VolumeAverageLaw
import Gtz.Design.StressFreeNormalizer
import Gtz.Design.PlaneBranchComplementSelector
import Gtz.Design.LineBranchFreePairAdjugateBalance
import Gtz.Design.TightLineBranchLivePairBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## Part 1 -- the master conservation law -/

/-- **THE MASTER LAW.**  The weighted average over a design of ANY quadratic form
is that form's trace.  No symmetry, no positivity, no invertibility, no rank or
size hypothesis: this is Parseval contracted against an arbitrary metric.

Every conservation identity in this module is this law at a particular metric --
`M = 1` gives the landed mass identity `Gtz.sum_weight_mul_leverage`, `M = N⁻¹`
gives the determinant ratio law, `M = N.adjugate` gives the insertion ledger. -/
theorem sum_weight_mul_quadForm_eq_trace (design : WeightedDesign size rank)
    (multiplier : Matrix (Fin rank) (Fin rank) ℝ) :
    ∑ label, design.weight label
        * (design.atom label ⬝ᵥ (multiplier *ᵥ design.atom label))
      = Matrix.trace multiplier := by
  rw [← trace_mul_weightedSubsetMass design Finset.univ multiplier,
    weightedSubsetMass_univ design, Matrix.mul_one]

/-- The master law on a label subset: the subset's share of the trace is the whole
trace minus the complement's.  The point of the shape is that the COMPLEMENT is what
survives -- the subset's own coordinates are gone. -/
theorem sum_subset_weight_mul_quadForm_eq_trace_sub (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) (multiplier : Matrix (Fin rank) (Fin rank) ℝ) :
    ∑ label ∈ labelSet, design.weight label
        * (design.atom label ⬝ᵥ (multiplier *ᵥ design.atom label))
      = Matrix.trace multiplier
        - ∑ label ∈ labelSetᶜ, design.weight label
            * (design.atom label ⬝ᵥ (multiplier *ᵥ design.atom label)) := by
  have hsplit := Finset.sum_add_sum_compl labelSet
    (fun label => design.weight label
      * (design.atom label ⬝ᵥ (multiplier *ᵥ design.atom label)))
  rw [sum_weight_mul_quadForm_eq_trace design multiplier] at hsplit
  linarith [hsplit]

/-! ### The two pivot conservation laws

The master law at the metric `(subsetSum D Q - 1)⁻¹` is the WEIGHTED pivot average;
reading the same metric against the base's own unweighted atom sum is the UNWEIGHTED
insider pivot sum.  The landed `Gtz.trace_identity` is exactly the difference of the
two, which is why it needs no separate argument. -/

/-- **THE WEIGHTED PIVOT CONSERVATION LAW.**  The design-weighted average of the pivots
at ANY base set is the trace of that base's inverse gap.  No hypothesis at all: at a
singular gap Lean's inverse is zero, every pivot is zero and both sides vanish.

This is the identity behind the sixth recorded averaging barrier, which the campaign had
only ever measured.  Together with `neg_one_lt_sum_weight_mul_pivot_of_isLivePair` below
it says the weighted pivot average can never certify a strict completion. -/
theorem sum_weight_mul_pivot_eq_trace_inv (design : WeightedDesign size rank)
    (base : Finset (Fin size)) :
    ∑ label, design.weight label * pivot design base label
      = Matrix.trace (subsetSum design base - 1)⁻¹ := by
  have hterm : ∀ label : Fin size,
      design.weight label * pivot design base label
        = design.weight label
            * (design.atom label ⬝ᵥ ((subsetSum design base - 1)⁻¹ *ᵥ design.atom label)) := by
    intro label
    rw [pivot_eq_dot]
  rw [Finset.sum_congr rfl fun label _ => hterm label,
    sum_weight_mul_quadForm_eq_trace design (subsetSum design base - 1)⁻¹]

/-- **THE UNWEIGHTED INSIDER PIVOT LAW.**  The insiders' pivots total `rank` plus the
trace of the inverse gap.  This one uses no Parseval -- only that the base's atom sum is
its gap plus the identity -- so it is independent of the weighted law above.

This is the landed `Gtz.sum_pivot_eq_rank_add_trace_inverse` with `PosDef` weakened to
`IsUnit`.  The landed proof spends positive definiteness at exactly one line, to produce
`IsUnit` of the determinant, and every hard-side base in this campaign has an INDEFINITE
gap; this is the third place in this module where that same single substitution widens a
landed statement onto the region the campaign actually works in. -/
theorem sum_insider_pivot_eq_rank_add_trace_inv (design : WeightedDesign size rank)
    (base : Finset (Fin size)) (hunit : IsUnit (subsetSum design base - 1).det) :
    ∑ insider ∈ base, pivot design base insider
      = rank + Matrix.trace (subsetSum design base - 1)⁻¹ := by
  have hterm : ∀ insider ∈ base, pivot design base insider
      = Matrix.trace ((subsetSum design base - 1)⁻¹ * atomMatrix (design.atom insider)) := by
    intro insider _
    rw [trace_mul_atomMatrix, pivot_eq_dot]
  have hunfold : subsetSum design base
      = ∑ insider ∈ base, atomMatrix (design.atom insider) := rfl
  have hsum : ∑ insider ∈ base, atomMatrix (design.atom insider)
      = (subsetSum design base - 1) + 1 := by
    rw [← hunfold]
    abel
  rw [Finset.sum_congr rfl hterm, ← Matrix.trace_sum, ← Matrix.mul_sum, hsum, Matrix.mul_add,
    Matrix.trace_add, Matrix.mul_one, Matrix.nonsing_inv_mul _ hunit, Matrix.trace_one,
    Fintype.card_fin]

/-! ## Part 2 -- the insertion pivot law -/

/-- **THE INSERTION PIVOT LAW**, general size and rank.  Adjoining one atom to a
base set whose gap is invertible multiplies that gap's determinant by `1 + q`,
with `q` the adjoined atom's pivot at the base.

This is the INSERT twin of the landed `Gtz.det_erase_eq_det_mul_pivot_gap`, whose
factor is `1 - q`.  The tree carried only the erase direction. -/
theorem det_insert_eq_det_mul_one_add_pivot (design : WeightedDesign size rank)
    (base : Finset (Fin size)) {added : Fin size} (hadded : added ∉ base)
    (hunit : IsUnit (subsetSum design base - 1).det) :
    (subsetSum design (insert added base) - 1).det
      = (subsetSum design base - 1).det * (1 + pivot design base added) := by
  rw [subsetSum_insert_sub_one design hadded, det_add_atomMatrix hunit, pivot_eq_dot]

/-- **THE MINUS ONE RIGIDITY.**  If the enlarged gap is singular while the base gap
is not, the adjoined atom's pivot at the base is EXACTLY `-1`.

Read on the tight-line branch at a base pair, with the omitted base axis adjoined:
the base triple's gap is singular (that is what "tight" means) and the base pair's
gap is invertible whenever the pair is live, so the omitted axis reads exactly `-1`
and reinserting it reconstitutes the tie.  This is a boundary ANCHOR -- an identity
pinning one coordinate -- and not an inequality that a budget can spend. -/
theorem pivot_eq_neg_one_of_det_insert_eq_zero (design : WeightedDesign size rank)
    (base : Finset (Fin size)) {added : Fin size} (hadded : added ∉ base)
    (hunit : IsUnit (subsetSum design base - 1).det)
    (hsingular : (subsetSum design (insert added base) - 1).det = 0) :
    pivot design base added = -1 := by
  have hbase : (subsetSum design base - 1).det ≠ 0 := isUnit_iff_ne_zero.mp hunit
  have hproduct := det_insert_eq_det_mul_one_add_pivot design base hadded hunit
  rw [hsingular] at hproduct
  have hfactor : 1 + pivot design base added = 0 := by
    rcases mul_eq_zero.mp hproduct.symm with hzero | hzero
    · exact absurd hzero hbase
    · exact hzero
  linarith

/-! ### The bridge between the erasure calculus and the scalar alphabet -/

/-- A live pair's gap is INVERTIBLE and is NEVER positive definite: its determinant
is minus the pair's two by two minor, hence strictly negative.

This is the satisfiability witness for every `IsUnit`-hypothesised statement in this
module.  It also says the hypothesis is strictly weaker than the landed `PosDef` one:
the live pairs are exactly the base sets the landed trace identity cannot see. -/
theorem isUnit_det_pairGap_of_isLivePair (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (hdistinct : pairFirst ≠ pairSecond)
    (hlive : IsLivePair design pairFirst pairSecond) :
    (subsetSum design {pairFirst, pairSecond} - 1).det < 0
      ∧ IsUnit (subsetSum design {pairFirst, pairSecond} - 1).det
      ∧ ¬ (subsetSum design {pairFirst, pairSecond} - 1).PosDef := by
  have hdet : (subsetSum design {pairFirst, pairSecond} - 1).det
      = -pairGapExcessOf design pairFirst pairSecond :=
    det_pairGap_eq_neg_pairGapExcessOf design hdistinct
  have hneg : (subsetSum design {pairFirst, pairSecond} - 1).det < 0 := by
    rw [hdet]
    linarith [hlive.2.2]
  refine ⟨hneg, isUnit_iff_ne_zero.mpr (ne_of_lt hneg), fun hposDef => ?_⟩
  exact absurd hposDef.det_pos (not_lt.mpr hneg.le)

/-- **THE VOCABULARY BRIDGE.**  The tie discriminant of a triple is the pair's two by
two minor times `-(1 + q)`, with `q` the third atom's pivot at the pair.

The campaign has carried two disjoint scalar languages: the erasure calculus
(`Gtz.pivot`, `trace_identity`, `excess_balance`, `pigeonhole`, all at general
`(m, k)`) and the rank-three alphabet (`gapExcessOf`, `pairGapExcessOf`,
`discriminantTie`, `IsLivePair`).  This identity is the whole translation between
them, and the only hypothesis beyond distinctness is that the pair's minor does not
vanish -- which for a LIVE pair is automatic. -/
theorem discriminantTie_eq_neg_pairGapExcessOf_mul_one_add_pivot
    (design : WeightedDesign size 3) {pivotLabel pairFirst pairSecond : Fin size}
    (hpivotFirst : pivotLabel ≠ pairFirst) (hpivotSecond : pivotLabel ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond)
    (hminor : pairGapExcessOf design pairFirst pairSecond ≠ 0) :
    discriminantTie design pivotLabel pairFirst pairSecond
      = -pairGapExcessOf design pairFirst pairSecond
          * (1 + pivot design {pairFirst, pairSecond} pivotLabel) := by
  have hdetPair : (subsetSum design {pairFirst, pairSecond} - 1).det
      = -pairGapExcessOf design pairFirst pairSecond :=
    det_pairGap_eq_neg_pairGapExcessOf design hpairDistinct
  have hunit : IsUnit (subsetSum design {pairFirst, pairSecond} - 1).det := by
    rw [hdetPair]
    exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hminor)
  have hnotMem : pivotLabel ∉ ({pairFirst, pairSecond} : Finset (Fin size)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun hcase => hcase.elim hpivotFirst hpivotSecond
  have hinsert := det_insert_eq_det_mul_one_add_pivot design {pairFirst, pairSecond}
    hnotMem hunit
  rw [hdetPair] at hinsert
  rw [← det_subsetSum_sub_one_eq_discriminantTie design hpivotFirst hpivotSecond hpairDistinct]
  exact hinsert

/-- **The strictness test in pivot language.**  Against a live pair, a completing
atom's triple is strictly dominating exactly when its pivot at the pair is below
`-1`.  The landed `Gtz.cap_fires_iff_det_nonneg` is the same flip of the inequality
at a negative determinant base; this is that flip named in the design's own
scalars. -/
theorem det_tripleGap_pos_iff_pivot_lt_neg_one (design : WeightedDesign size 3)
    {pivotLabel pairFirst pairSecond : Fin size}
    (hpivotFirst : pivotLabel ≠ pairFirst) (hpivotSecond : pivotLabel ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond)
    (hlive : IsLivePair design pairFirst pairSecond) :
    0 < (subsetSum design {pivotLabel, pairFirst, pairSecond} - 1).det
      ↔ pivot design {pairFirst, pairSecond} pivotLabel < -1 := by
  have hminor : (0 : ℝ) < pairGapExcessOf design pairFirst pairSecond := hlive.2.2
  have hbridge := discriminantTie_eq_neg_pairGapExcessOf_mul_one_add_pivot design
    hpivotFirst hpivotSecond hpairDistinct (ne_of_gt hminor)
  rw [det_subsetSum_sub_one_eq_discriminantTie design hpivotFirst hpivotSecond hpairDistinct,
    hbridge]
  constructor
  · intro hpos
    nlinarith [hpos, hminor]
  · intro hlow
    nlinarith [hlow, hminor]

/-! ## Part 3 -- the weighted insertion ledger at rank three -/

/-- The trace of a `3 x 3` adjugate is the matrix's second invariant. -/
theorem trace_adjugate_eq_secondInvariantOfThree (form : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace form.adjugate = secondInvariantOfThree form := by
  simp only [Matrix.trace_fin_three, Matrix.adjugate_fin_three, secondInvariantOfThree,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **THE INSERTION LEDGER, UNCONDITIONAL.**  For EVERY real `3 x 3` matrix `N` and
every weighted design of rank three,

    `sum_y w_y * det(N + a_y a_yᵀ)  =  det N + e_2(N)` .

No invertibility, no symmetry, no positivity, no relation between `N` and the
design.  The whole weight dependence cancels: the answer is a function of `N`
alone.

This is the coordinate-free form of the one-slot collapse.  In the transported
chart it is the identity that eliminates every free atom coordinate from a weighted
determinant sum, leaving only the base data -- which is what makes an active-set
analysis possible.  It is ALSO a weighted average over the design and therefore
inherits all six averaging barriers: reading a sign off it has failed six times and
will fail a seventh. -/
theorem sum_weight_mul_det_add_atomMatrix_fin_three (design : WeightedDesign size 3)
    (form : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ label, design.weight label * (form + atomMatrix (design.atom label)).det
      = form.det + secondInvariantOfThree form := by
  have hterm : ∀ label : Fin size,
      design.weight label * (form + atomMatrix (design.atom label)).det
        = design.weight label * form.det
          + design.weight label
              * (design.atom label ⬝ᵥ (form.adjugate *ᵥ design.atom label)) := by
    intro label
    rw [det_add_atomMatrix_fin_three]
    ring
  rw [Finset.sum_congr rfl fun label _ => hterm label, Finset.sum_add_distrib,
    ← Finset.sum_mul, design.weight_sum_one, one_mul,
    sum_weight_mul_quadForm_eq_trace design form.adjugate,
    trace_adjugate_eq_secondInvariantOfThree]

/-- **THE INSERTION LEDGER ON A SUBSET, WITHOUT PARSEVAL.**  For every label subset and
every `3 x 3` matrix `N`,

    `sum_{y in S} w_y * det(N + a_y a_yᵀ)  =  (sum_{y in S} w_y) * det N
                                              + trace(adj N * weightedSubsetMass D S)` .

Nothing here uses the design's Parseval identity, so the statement holds for any weighted
atom family whatever; the full-design ledger above is this at `S = univ`, where Parseval
turns the mass into the identity and the trace into `e_2`.  The landed
`Gtz.three_weighted_det_add_atomMatrix_eq` is the same law written out for three
free-standing vectors; this is the Finset form on a design. -/
theorem sum_subset_weight_mul_det_add_atomMatrix_eq_trace_adjugate
    (design : WeightedDesign size 3) (labelSet : Finset (Fin size))
    (form : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ label ∈ labelSet, design.weight label * (form + atomMatrix (design.atom label)).det
      = (∑ label ∈ labelSet, design.weight label) * form.det
        + Matrix.trace (form.adjugate * weightedSubsetMass design labelSet) := by
  have hterm : ∀ label ∈ labelSet,
      design.weight label * (form + atomMatrix (design.atom label)).det
        = design.weight label * form.det
          + design.weight label
              * (design.atom label ⬝ᵥ (form.adjugate *ᵥ design.atom label)) := by
    intro label _
    rw [det_add_atomMatrix_fin_three]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul,
    trace_mul_weightedSubsetMass design labelSet form.adjugate]

/-- **THE INSERTION LEDGER ON A SUBSET.**  Restricting the ledger to a label subset
leaves the subset's weight total against `det N`, the full second invariant, and the
COMPLEMENT's adjugate readings.  The subset's own atom coordinates are gone. -/
theorem sum_subset_weight_mul_det_add_atomMatrix (design : WeightedDesign size 3)
    (labelSet : Finset (Fin size)) (form : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ label ∈ labelSet, design.weight label * (form + atomMatrix (design.atom label)).det
      = (∑ label ∈ labelSet, design.weight label) * form.det
        + secondInvariantOfThree form
        - ∑ label ∈ labelSetᶜ, design.weight label
            * (design.atom label ⬝ᵥ (form.adjugate *ᵥ design.atom label)) := by
  have hterm : ∀ label : Fin size,
      design.weight label * (form + atomMatrix (design.atom label)).det
        = design.weight label * form.det
          + design.weight label
              * (design.atom label ⬝ᵥ (form.adjugate *ᵥ design.atom label)) := by
    intro label
    rw [det_add_atomMatrix_fin_three]
    ring
  have hreadings := sum_subset_weight_mul_quadForm_eq_trace_sub design labelSet form.adjugate
  rw [trace_adjugate_eq_secondInvariantOfThree] at hreadings
  rw [Finset.sum_congr rfl fun label _ => hterm label, Finset.sum_add_distrib,
    ← Finset.sum_mul, hreadings]
  ring

/-- **THE ONE-SLOT COLLAPSE, CHART-FREE.**  Summing the enlarged gap determinant
over every atom OUTSIDE a base set, weighted, eliminates every outside coordinate:
what survives is the outside weight total against the base gap determinant, that
gap's second invariant, and the BASE atoms' own adjugate readings.

In the transported line-branch chart, with the base set a two-element slot of the
base triple, this is exactly the identity that turns a weighted one-slot
determinant sum into base data alone. -/
theorem sum_weight_mul_det_insert_fin_three (design : WeightedDesign size 3)
    (base : Finset (Fin size)) :
    ∑ label ∈ baseᶜ, design.weight label * (subsetSum design (insert label base) - 1).det
      = (∑ label ∈ baseᶜ, design.weight label) * (subsetSum design base - 1).det
        + secondInvariantOfThree (subsetSum design base - 1)
        - ∑ label ∈ base, design.weight label
            * (design.atom label
                ⬝ᵥ ((subsetSum design base - 1).adjugate *ᵥ design.atom label)) := by
  have hterm : ∀ label ∈ baseᶜ,
      design.weight label * (subsetSum design (insert label base) - 1).det
        = design.weight label
            * ((subsetSum design base - 1) + atomMatrix (design.atom label)).det := by
    intro label hlabel
    rw [subsetSum_insert_sub_one design (Finset.mem_compl.mp hlabel)]
  rw [Finset.sum_congr rfl hterm,
    sum_subset_weight_mul_det_add_atomMatrix design baseᶜ (subsetSum design base - 1),
    compl_compl]

/-! ## Part 4 -- the erasure collapse at every cardinality -/

/-- **THE ERASURE COLLAPSE, AT EVERY CARDINALITY.**  Dropping one label at a time from a
label set and totalling the resulting gap determinants gives

    `sum_{y in S} det(gap of S minus y)  =  (|S| - 3) det(gap of S) - e_2(gap of S)` .

No hypothesis, no distinctness bookkeeping, any cardinality.  At `|S| = 3` it is the
pair-sum collapse below; at `|S| = 2` it identifies the second invariant of a pair gap
(`secondInvariantOfThree_pairGap_eq`); at `|S| = 4` it is the card-four statement the
plane branch's windows are phrased in, and nothing in the campaign had it. -/
theorem sum_det_erase_eq_card_sub_three_mul_det (design : WeightedDesign size 3)
    (labelSet : Finset (Fin size)) :
    ∑ dropped ∈ labelSet, (subsetSum design (labelSet.erase dropped) - 1).det
      = ((labelSet.card : ℝ) - 3) * (subsetSum design labelSet - 1).det
        - secondInvariantOfThree (subsetSum design labelSet - 1) := by
  have hterm : ∀ dropped ∈ labelSet,
      (subsetSum design (labelSet.erase dropped) - 1).det
        = (subsetSum design labelSet - 1).det
          - design.atom dropped
              ⬝ᵥ ((subsetSum design labelSet - 1).adjugate *ᵥ design.atom dropped) := by
    intro dropped hdropped
    have hgap : subsetSum design (labelSet.erase dropped) - 1
        = (subsetSum design labelSet - 1) - atomMatrix (design.atom dropped) := by
      rw [subsetSum_erase design hdropped]
      abel
    rw [hgap, det_sub_atomMatrix_fin_three]
  have hunfold : subsetSum design labelSet
      = ∑ dropped ∈ labelSet, atomMatrix (design.atom dropped) := rfl
  have hreadings : ∑ dropped ∈ labelSet,
        design.atom dropped
          ⬝ᵥ ((subsetSum design labelSet - 1).adjugate *ᵥ design.atom dropped)
      = 3 * (subsetSum design labelSet - 1).det
        + secondInvariantOfThree (subsetSum design labelSet - 1) := by
    have hstep : ∀ dropped ∈ labelSet,
        design.atom dropped
            ⬝ᵥ ((subsetSum design labelSet - 1).adjugate *ᵥ design.atom dropped)
          = Matrix.trace ((subsetSum design labelSet - 1).adjugate
              * atomMatrix (design.atom dropped)) := by
      intro dropped _
      rw [trace_mul_atomMatrix]
    have hsum : ∑ dropped ∈ labelSet, atomMatrix (design.atom dropped)
        = (subsetSum design labelSet - 1) + 1 := by
      rw [← hunfold]
      abel
    rw [Finset.sum_congr rfl hstep, ← Matrix.trace_sum, ← Matrix.mul_sum, hsum,
      Matrix.mul_add, Matrix.trace_add, Matrix.mul_one,
      trace_adjugate_mul_self_fin_three, trace_adjugate_eq_secondInvariantOfThree]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    hreadings]
  ring

/-- The matrix determinant lemma in ADJUGATE form at general rank, from the landed ratio
form `Gtz.det_sub_atomMatrix`.  Rank three has this unconditionally as
`Gtz.det_sub_atomMatrix_fin_three`; at general rank the tree carries only the ratio form,
which needs the determinant to be a unit. -/
theorem det_sub_atomMatrix_adjugate_of_isUnit {form : Matrix (Fin rank) (Fin rank) ℝ}
    (hunit : IsUnit form.det) (vector : Fin rank → ℝ) :
    (form - atomMatrix vector).det
      = form.det - vector ⬝ᵥ (form.adjugate *ᵥ vector) := by
  have hdet : form.det ≠ 0 := isUnit_iff_ne_zero.mp hunit
  have hinverse : vector ⬝ᵥ (form⁻¹ *ᵥ vector)
      = (form.det)⁻¹ * (vector ⬝ᵥ (form.adjugate *ᵥ vector)) := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [det_sub_atomMatrix hunit vector, hinverse]
  field_simp

/-- **THE ERASURE COLLAPSE AT GENERAL RANK.**  The same law as
`sum_det_erase_eq_card_sub_three_mul_det` at every rank, at the price of the set's gap
being invertible: the second invariant is replaced by the trace of the adjugate, which is
the correct general-rank invariant. -/
theorem sum_det_erase_eq_card_sub_rank_mul_det (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) (hunit : IsUnit (subsetSum design labelSet - 1).det) :
    ∑ dropped ∈ labelSet, (subsetSum design (labelSet.erase dropped) - 1).det
      = ((labelSet.card : ℝ) - rank) * (subsetSum design labelSet - 1).det
        - Matrix.trace (subsetSum design labelSet - 1).adjugate := by
  have hterm : ∀ dropped ∈ labelSet,
      (subsetSum design (labelSet.erase dropped) - 1).det
        = (subsetSum design labelSet - 1).det
          - design.atom dropped
              ⬝ᵥ ((subsetSum design labelSet - 1).adjugate *ᵥ design.atom dropped) := by
    intro dropped hdropped
    have hgap : subsetSum design (labelSet.erase dropped) - 1
        = (subsetSum design labelSet - 1) - atomMatrix (design.atom dropped) := by
      rw [subsetSum_erase design hdropped]
      abel
    rw [hgap, det_sub_atomMatrix_adjugate_of_isUnit hunit]
  have hunfold : subsetSum design labelSet
      = ∑ dropped ∈ labelSet, atomMatrix (design.atom dropped) := rfl
  have hreadings : ∑ dropped ∈ labelSet,
        design.atom dropped
          ⬝ᵥ ((subsetSum design labelSet - 1).adjugate *ᵥ design.atom dropped)
      = rank * (subsetSum design labelSet - 1).det
        + Matrix.trace (subsetSum design labelSet - 1).adjugate := by
    have hstep : ∀ dropped ∈ labelSet,
        design.atom dropped
            ⬝ᵥ ((subsetSum design labelSet - 1).adjugate *ᵥ design.atom dropped)
          = Matrix.trace ((subsetSum design labelSet - 1).adjugate
              * atomMatrix (design.atom dropped)) := by
      intro dropped _
      rw [trace_mul_atomMatrix]
    have hsum : ∑ dropped ∈ labelSet, atomMatrix (design.atom dropped)
        = (subsetSum design labelSet - 1) + 1 := by
      rw [← hunfold]
      abel
    rw [Finset.sum_congr rfl hstep, ← Matrix.trace_sum, ← Matrix.mul_sum, hsum,
      Matrix.mul_add, Matrix.trace_add, Matrix.mul_one, Matrix.adjugate_mul,
      Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    hreadings]
  ring

/-- A single atom's gap determinant is that atom's heaviness.  Immediate, and the base
case the erasure collapse is read against. -/
theorem det_singletonGap_eq_gapExcessOf (design : WeightedDesign size 3) (label : Fin size) :
    (subsetSum design {label} - 1).det = gapExcessOf design label := by
  have hsingleton : subsetSum design {label} = atomMatrix (design.atom label) :=
    Finset.sum_singleton _ _
  rw [hsingleton, gapExcessOf, leverageOf]
  simp only [Matrix.det_fin_three, Matrix.sub_apply, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.one_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Fin.sum_univ_three]
  ring

/-- **THE SECOND INVARIANT OF A PAIR GAP, IN THE SCALAR ALPHABET.**  For any two distinct
labels of a rank-three design,

    `e_2(pair gap)  =  pairGapExcessOf a b  -  gapExcessOf a  -  gapExcessOf b` .

This is the erasure collapse at cardinality two, and it is what turns the trace of an
inverse pair gap into design scalars. -/
theorem secondInvariantOfThree_pairGap_eq (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (hdistinct : pairFirst ≠ pairSecond) :
    secondInvariantOfThree (subsetSum design {pairFirst, pairSecond} - 1)
      = pairGapExcessOf design pairFirst pairSecond
        - gapExcessOf design pairFirst - gapExcessOf design pairSecond := by
  rw [subsetSum_pair design hdistinct, pairGapExcessOf, gapPairingOf, gapExcessOf, gapExcessOf,
    leverageOf, leverageOf]
  simp only [secondInvariantOfThree, Matrix.sub_apply, Matrix.add_apply, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.one_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
    dotProduct, Fin.sum_univ_three]
  ring

/-- **THE PAIR-SUM COLLAPSE.**  The three pair gaps of a triple have determinants
totalling minus the second invariant of the triple's own gap.  No hypothesis beyond
distinctness. -/
theorem sum_det_pairGap_eq_neg_secondInvariantOfThree (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    (subsetSum design {secondLabel, thirdLabel} - 1).det
        + (subsetSum design {firstLabel, thirdLabel} - 1).det
        + (subsetSum design {firstLabel, secondLabel} - 1).det
      = -secondInvariantOfThree (subsetSum design {firstLabel, secondLabel, thirdLabel} - 1) := by
  set tripleGap := subsetSum design {firstLabel, secondLabel, thirdLabel} - 1 with htripleGap
  have hexpand : subsetSum design {firstLabel, secondLabel, thirdLabel}
      = atomMatrix (design.atom firstLabel) + atomMatrix (design.atom secondLabel)
        + atomMatrix (design.atom thirdLabel) :=
    subsetSum_triple design hfirstSecond hfirstThird hsecondThird
  have hdropFirst : subsetSum design {secondLabel, thirdLabel} - 1
      = tripleGap - atomMatrix (design.atom firstLabel) := by
    rw [htripleGap, hexpand, subsetSum, Finset.sum_pair hsecondThird]
    abel
  have hdropSecond : subsetSum design {firstLabel, thirdLabel} - 1
      = tripleGap - atomMatrix (design.atom secondLabel) := by
    rw [htripleGap, hexpand, subsetSum, Finset.sum_pair hfirstThird]
    abel
  have hdropThird : subsetSum design {firstLabel, secondLabel} - 1
      = tripleGap - atomMatrix (design.atom thirdLabel) := by
    rw [htripleGap, hexpand, subsetSum, Finset.sum_pair hfirstSecond]
    abel
  have hreadings : design.atom firstLabel ⬝ᵥ (tripleGap.adjugate *ᵥ design.atom firstLabel)
      + design.atom secondLabel ⬝ᵥ (tripleGap.adjugate *ᵥ design.atom secondLabel)
      + design.atom thirdLabel ⬝ᵥ (tripleGap.adjugate *ᵥ design.atom thirdLabel)
      = 3 * tripleGap.det + secondInvariantOfThree tripleGap := by
    have hsumAtoms : atomMatrix (design.atom firstLabel) + atomMatrix (design.atom secondLabel)
        + atomMatrix (design.atom thirdLabel) = tripleGap + 1 := by
      rw [htripleGap, hexpand]
      abel
    have htrace : Matrix.trace (tripleGap.adjugate
          * (atomMatrix (design.atom firstLabel) + atomMatrix (design.atom secondLabel)
              + atomMatrix (design.atom thirdLabel)))
        = design.atom firstLabel ⬝ᵥ (tripleGap.adjugate *ᵥ design.atom firstLabel)
          + design.atom secondLabel ⬝ᵥ (tripleGap.adjugate *ᵥ design.atom secondLabel)
          + design.atom thirdLabel ⬝ᵥ (tripleGap.adjugate *ᵥ design.atom thirdLabel) := by
      rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
        trace_mul_atomMatrix, trace_mul_atomMatrix, trace_mul_atomMatrix]
    rw [← htrace, hsumAtoms, Matrix.mul_add, Matrix.trace_add, Matrix.mul_one,
      trace_adjugate_mul_self_fin_three, trace_adjugate_eq_secondInvariantOfThree]
  rw [hdropFirst, hdropSecond, hdropThird, det_sub_atomMatrix_fin_three,
    det_sub_atomMatrix_fin_three, det_sub_atomMatrix_fin_three]
  linarith [hreadings]

/-- **THE FLAT PAIR AGGREGATE IS THE SECOND INVARIANT.**  The three two by two
minors of a triple's Gram gap total the second invariant of that triple's ambient
gap.

This settles as a theorem what the campaign carried as an unverified lead: the
unweighted flat free-pair aggregate of a triple is `e_2` of the triple's gap, so
the landed inertia bridge
`Gtz.posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos` consumes it directly.
It is the UNWEIGHTED aggregate; the weighted one, which is what the refuted
ingredient (b) was about, is not this and is not positive. -/
theorem secondInvariantOfThree_tripleGap_eq_sum_pairGapExcessOf (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    secondInvariantOfThree (subsetSum design {firstLabel, secondLabel, thirdLabel} - 1)
      = pairGapExcessOf design secondLabel thirdLabel
        + pairGapExcessOf design firstLabel thirdLabel
        + pairGapExcessOf design firstLabel secondLabel := by
  have hcollapse := sum_det_pairGap_eq_neg_secondInvariantOfThree design hfirstSecond
    hfirstThird hsecondThird
  rw [det_pairGap_eq_neg_pairGapExcessOf design hsecondThird,
    det_pairGap_eq_neg_pairGapExcessOf design hfirstThird,
    det_pairGap_eq_neg_pairGapExcessOf design hfirstSecond] at hcollapse
  linarith [hcollapse]

/-! ## Part 5 -- the live-pair averaging barrier

The campaign's sixth recorded barrier says a weighted pivot average over the design is
negative on every live pair and so can never witness a strict completion.  It was found
by measurement.  Here it is as an identity with an exact right-hand side, and the sign is
then two heaviness inequalities. -/

/-- **THE TIE POLYNOMIAL IS THE ENLARGED PAIR-GAP DETERMINANT, WITH NO DISTINCTNESS ON
THE THIRD LABEL.**  The landed `Gtz.det_subsetSum_sub_one_eq_discriminantTie` reads the
tie polynomial off a card-three subset and therefore needs all three labels distinct.
Written against the enlarged pair gap instead, the same identity holds for EVERY third
label, including `pairFirst` and `pairSecond` themselves, where the card-three subset
degenerates and the landed form says nothing.

That is exactly what makes the landed averaging law `Gtz.sum_weight_mul_discriminantTie`
a statement about determinants: the two insider terms of that sum are enlarged pair-gap
determinants too. -/
theorem det_pairGap_add_atomMatrix_eq_discriminantTie (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (hdistinct : pairFirst ≠ pairSecond)
    (thirdLabel : Fin size) :
    ((subsetSum design {pairFirst, pairSecond} - 1)
        + atomMatrix (design.atom thirdLabel)).det
      = discriminantTie design pairFirst pairSecond thirdLabel := by
  rw [subsetSum_pair design hdistinct, discriminantTie, heavyExcess, heavyExcess, heavyExcess,
    atomPairing, atomPairing, atomPairing, leverageOf, leverageOf, leverageOf]
  simp only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.add_apply, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.one_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
    dotProduct, Fin.sum_univ_three]
  ring

/-- **THE PAIR-COMPLETION AVERAGE.**  For any two distinct labels of a rank-three design,
the design-weighted average of the determinant of the pair gap enlarged by one atom is
EXACTLY minus the two endpoints' heaviness:

    `sum_y w_y * det(pairGap(a,b) + a_y a_yᵀ)  =  -(gapExcessOf a + gapExcessOf b)` .

**THIS IS THE LANDED `Gtz.sum_weight_mul_discriminantTie` -- the campaign's FIRST recorded
barrier, `TieRowLaw` pair averaging -- in determinant coordinates, and it is derived from
it here rather than reproved.**  What the determinant form buys is that the summand is a
gap determinant at every label, so the law composes directly with the insertion ledger and
the erasure collapse above; what the tie-polynomial form buys is the scalar alphabet.  The
two coordinate systems were carried separately; the bridge is the lemma just above.

Independently, the ledger route
`sum_weight_mul_det_add_atomMatrix_fin_three` + `secondInvariantOfThree_pairGap_eq` proves
the same identity, so the two derivations cross-check each other. -/
theorem sum_weight_mul_det_pairGap_add_atomMatrix (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (hdistinct : pairFirst ≠ pairSecond) :
    ∑ label, design.weight label
        * ((subsetSum design {pairFirst, pairSecond} - 1)
            + atomMatrix (design.atom label)).det
      = -(gapExcessOf design pairFirst + gapExcessOf design pairSecond) := by
  rw [Finset.sum_congr rfl fun label _ => congrArg (design.weight label * ·)
      (det_pairGap_add_atomMatrix_eq_discriminantTie design hdistinct label),
    sum_weight_mul_discriminantTie design pairFirst pairSecond,
    gapExcessOf_eq_heavyExcess, gapExcessOf_eq_heavyExcess]

/-- **THE BARRIER, SIGN FORM.**  At a LIVE pair both endpoints are heavy, so the weighted
average of the enlarged pair-gap determinant is strictly NEGATIVE.  No averaging over
completions, with these weights, can exhibit a strictly dominating triple through a live
pair -- the average is on the wrong side before any completion is chosen. -/
theorem sum_weight_mul_det_pairGap_add_atomMatrix_neg_of_isLivePair
    (design : WeightedDesign size 3) {pairFirst pairSecond : Fin size}
    (hdistinct : pairFirst ≠ pairSecond) (hlive : IsLivePair design pairFirst pairSecond) :
    ∑ label, design.weight label
        * ((subsetSum design {pairFirst, pairSecond} - 1)
            + atomMatrix (design.atom label)).det < 0 := by
  rw [sum_weight_mul_det_pairGap_add_atomMatrix design hdistinct]
  linarith [hlive.1, hlive.2.1]

/-- **THE INVERSE PAIR GAP IN DESIGN SCALARS.**  Whenever the pair's minor does not
vanish,

    `pairGapExcessOf a b * (1 + trace (pairGap(a,b))⁻¹)  =  gapExcessOf a + gapExcessOf b` .

The inverse of a pair gap is therefore not new data: its trace is `-1` plus the ratio of
the endpoints' total heaviness to the pair's minor. -/
theorem pairGapExcessOf_mul_one_add_trace_inv_pairGap (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (hdistinct : pairFirst ≠ pairSecond)
    (hminor : pairGapExcessOf design pairFirst pairSecond ≠ 0) :
    pairGapExcessOf design pairFirst pairSecond
        * (1 + Matrix.trace (subsetSum design {pairFirst, pairSecond} - 1)⁻¹)
      = gapExcessOf design pairFirst + gapExcessOf design pairSecond := by
  have hdet : (subsetSum design {pairFirst, pairSecond} - 1).det
      = -pairGapExcessOf design pairFirst pairSecond :=
    det_pairGap_eq_neg_pairGapExcessOf design hdistinct
  have htrace : Matrix.trace (subsetSum design {pairFirst, pairSecond} - 1)⁻¹
      = ((subsetSum design {pairFirst, pairSecond} - 1).det)⁻¹
        * secondInvariantOfThree (subsetSum design {pairFirst, pairSecond} - 1) := by
    rw [Matrix.inv_def, Matrix.trace_smul, Ring.inverse_eq_inv, smul_eq_mul,
      trace_adjugate_eq_secondInvariantOfThree]
  rw [htrace, hdet, secondInvariantOfThree_pairGap_eq design hdistinct]
  field_simp
  ring

/-- **THE BARRIER, PIVOT FORM.**  At a live pair the design-weighted pivot average is
strictly ABOVE `-1`, while `det_tripleGap_pos_iff_pivot_lt_neg_one` says a strict
completion is a pivot strictly BELOW `-1`.  So the weighted pivot average is on the wrong
side of the threshold at every live pair, for every design, with no hypothesis beyond
liveness: this is the sixth recorded averaging barrier, as a theorem. -/
theorem neg_one_lt_sum_weight_mul_pivot_of_isLivePair (design : WeightedDesign size 3)
    {pairFirst pairSecond : Fin size} (hdistinct : pairFirst ≠ pairSecond)
    (hlive : IsLivePair design pairFirst pairSecond) :
    -1 < ∑ label, design.weight label * pivot design {pairFirst, pairSecond} label := by
  rw [sum_weight_mul_pivot_eq_trace_inv design {pairFirst, pairSecond}]
  have hclosed := pairGapExcessOf_mul_one_add_trace_inv_pairGap design hdistinct
    (ne_of_gt hlive.2.2)
  nlinarith [hlive.1, hlive.2.1, hlive.2.2, hclosed]

/-- **THE CARD-FOUR AVERAGING LAW.**  The same ledger one cardinality up: the weighted
average of a triple's gap determinant enlarged by one atom is the triple's own gap
determinant plus its flat pair aggregate.  This is the shape the plane branch's card-four
windows are phrased in. -/
theorem sum_weight_mul_det_tripleGap_add_atomMatrix (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    ∑ label, design.weight label
        * ((subsetSum design {firstLabel, secondLabel, thirdLabel} - 1)
            + atomMatrix (design.atom label)).det
      = (subsetSum design {firstLabel, secondLabel, thirdLabel} - 1).det
        + (pairGapExcessOf design secondLabel thirdLabel
          + pairGapExcessOf design firstLabel thirdLabel
          + pairGapExcessOf design firstLabel secondLabel) := by
  rw [sum_weight_mul_det_add_atomMatrix_fin_three design
      (subsetSum design {firstLabel, secondLabel, thirdLabel} - 1),
    secondInvariantOfThree_tripleGap_eq_sum_pairGapExcessOf design hfirstSecond hfirstThird
      hsecondThird]

/-! ## Part 6 -- the trace identity off positive definiteness -/

/-- **THE TRACE IDENTITY AT AN INVERTIBLE GAP.**  The landed `Gtz.trace_identity`
carries `(subsetSum D Q - 1).PosDef` and spends it at exactly one line, to produce
`IsUnit` of the determinant.  Every hard-side base set in this campaign has an
INDEFINITE gap, so the landed form does not apply there; this one does.

`Gtz.isUnit_det_pairGap_of_isLivePair` witnesses that the hypothesis is satisfiable
and strictly weaker -- a live pair's gap is invertible and never positive
definite. -/
theorem trace_identity_of_isUnit (design : WeightedDesign size rank)
    (base : Finset (Fin size)) (hunit : IsUnit (subsetSum design base - 1).det) :
    ∑ insider ∈ base, (1 - design.weight insider) * pivot design base insider
      = rank + ∑ outsider ∈ baseᶜ, design.weight outsider * pivot design base outsider := by
  have hunweighted := sum_insider_pivot_eq_rank_add_trace_inv design base hunit
  have hweighted := sum_weight_mul_pivot_eq_trace_inv design base
  have hsplitWeighted := Finset.sum_add_sum_compl base
    (fun label => design.weight label * pivot design base label)
  have hpeel : ∑ insider ∈ base, (1 - design.weight insider) * pivot design base insider
      = (∑ insider ∈ base, pivot design base insider)
        - ∑ insider ∈ base, design.weight insider * pivot design base insider := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun insider _ => by ring
  rw [hpeel, hunweighted]
  rw [hweighted] at hsplitWeighted
  linarith [hsplitWeighted]

/-- **EXCESS BALANCE AT AN INVERTIBLE GAP.**  The landed `Gtz.excess_balance` off
its positive definite hypothesis, by the same single substitution. -/
theorem excess_balance_of_isUnit (design : WeightedDesign size rank)
    (base : Finset (Fin size)) (hunit : IsUnit (subsetSum design base - 1).det)
    (hcard : base.card = rank + 1) :
    ∑ insider ∈ base, (1 - design.weight insider) * (pivot design base insider - 1)
      = ∑ outsider ∈ baseᶜ, design.weight outsider * (pivot design base outsider - 1) := by
  have htrace := trace_identity_of_isUnit design base hunit
  have hweightPeel : ∑ insider ∈ base, (1 - design.weight insider)
      = (rank + 1 : ℝ) - ∑ insider ∈ base, design.weight insider := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    push_cast
    ring
  have hweightTotal : ∑ insider ∈ base, design.weight insider
      + ∑ outsider ∈ baseᶜ, design.weight outsider = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact design.weight_sum_one
  have hinside : ∑ insider ∈ base, (1 - design.weight insider) * (pivot design base insider - 1)
      = (∑ insider ∈ base, (1 - design.weight insider) * pivot design base insider)
        - ∑ insider ∈ base, (1 - design.weight insider) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun insider _ => by ring
  have houtside : ∑ outsider ∈ baseᶜ,
        design.weight outsider * (pivot design base outsider - 1)
      = (∑ outsider ∈ baseᶜ, design.weight outsider * pivot design base outsider)
        - ∑ outsider ∈ baseᶜ, design.weight outsider := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun outsider _ => by ring
  rw [hinside, houtside, hweightPeel]
  linarith [htrace, hweightTotal]

end Gtz
