/-
# The sharpened `(6,3)` exclusion frontier

**THE HEADLINE: RANK THREE OF THE 1997 CONJECTURE NOW RESTS ON A SINGLE OPEN
HYPOTHESIS ABOUT `(6,3)` DESIGNS.**

`Gtz.gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidateSharp` takes
one antecedent -- that no `(6,3)` weighted design satisfies an explicit design-level
predicate -- and returns `Gtz.GtzOriginal atomCount 3` for every positive
`atomCount`.  The shipped
`Gtz.gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidate` needed that
same search AND `IsEmpty Gtz.SevenThreeCrux`; the stress walk
(`Gtz.gtzWeighted_seven_three_of_six_three`) deleted the second one, and
`Gtz.rank_three_iff_six_three` states the resulting collapse as an iff: `GtzWeightedAll
3` holds if and only if `GtzWeighted 6 3` does.  There is no longer a second cell.

Read plainly, the terminus quantifies over ALL rank-three configurations of ANY size:
if the `(6,3)` box is empty then for every positive `n` and every `n`-atom
configuration in `R^3` the Goreinov-Tyrtyshnikov-Zamarashkin conclusion holds.  What
is NOT proved anywhere in this file or this tree is that the box IS empty.
`Gtz.GtzWeighted 6 3` and `IsEmpty Gtz.SixThreeCrux` remain OPEN, and everything
below is a necessary condition on a hypothetical counterexample, never an exclusion
of one.

## What this module adds

`Gtz.SixThreeCrux.frontierSharp` is the layer the previous frontier did not have.  It
EXTENDS `Gtz.SixThreeCrux.frontier` (Gtz/Quantitative/SixThreeExclusionFrontier.lean:432),
which is left exactly as it was; the full picture is the two theorems together.  The
new layer is:

* **THE STRESS LAYER.**  `Gtz.SixThreeCrux.stress_eq_zero` -- a crux carries no
  stress, so its six Veronese images are a BASIS of `Sym_3(R)`.  This is a genuinely
  new crux field, it SUBSUMES the shipped `hasNoParallelPair`
  (`Gtz.SixThreeCrux.not_hasParallelPair_via_stress`), and it is STRICTLY stronger
  (`Gtz.SixThreeCrux.not_twoPlanes` excludes six atoms splitting into two coplanar
  triples, which no parallel-pair condition sees).  Its algebraic face
  `Gtz.SixThreeCrux.det_hadamardSquareGram_ne_zero` is a single polynomial
  NONVANISHING, hence a legitimate saturation variable; its geometric face
  `Gtz.SixThreeCrux.no_commonQuadric` says the six directions lie on no conic of
  `RP^2`.
* **THE QUADRATIC FLOOR.**  `Gtz.SixThreeCrux.pairingMassFloor` -- at every atom the
  squared pairings to the other five outweigh the atom's own leverage.  Degree two in
  the Gram entries, and strictly stronger than what Parseval alone gives.
* **THE CHART GAP LAYER.**  All-heaviness read as a strictly positive gap diagonal,
  and the first characteristic coefficient strictly positive at every one of the
  twenty triples -- two admissibility branches per triple rather than three.

`Gtz.IsSixThreeRefutationCandidateSharp` carries the new DESIGN-LEVEL conjuncts (no
chart appears in any of them) on top of the shipped
`Gtz.IsSixThreeRefutationCandidate`, which is untouched.

**THE TWO BOXES ARE THE SAME BOX**, and `Gtz.isSixThreeRefutationCandidateSharp_iff`
proves it, so that nobody reads the sharpened frontier as a reduction of the search
space.  Every new conjunct is a CONSEQUENCE of the shipped box rather than a new
constraint on it: a nonzero stress and a common conic each produce a dominating triple,
which the box's own no-domination clause forbids, and the quadratic floor follows from
all-heaviness with the strictly dominating co-singletons.  What the sharp predicate
buys is therefore a reduction of the WORK at each point of an unchanged box -- four
extra facts made explicit, one of them a single polynomial nonvanishing an algebraic
search can saturate by -- and nothing more.

## The frontier ledger, route by route

**ROUTE A -- THE STRESS WALK.  LANDED; CLOSED AS A REDUCTION, NOT AS AN EXCLUSION.**
`Gtz.exists_rescaledReducedDesign`, `Gtz.gtzWeighted_seven_three_of_six_three`,
`Gtz.gtzWeighted_six_three_iff_seven_three`, `Gtz.rank_three_iff_six_three`,
`Gtz.crystallizationSharp` (the Veronese cap drops from `k(k+1)/2 + 1` to `k(k+1)/2`
at EVERY rank), `Gtz.rank_three_of_heavy_six_three` (the all-heavy window drops with
it, so the whole rank sits on ALL-HEAVY `(6,3)`), `Gtz.gtzWeightedAll_two_of_walk`,
`Gtz.gtzWeightedAll_four_of_ten`, and the propagation
`Gtz.exists_allHeavy_minimiser_of_not_rank_three_sharp`,
`Gtz.gtzWeighted_six_three_iff_seven_four`.  This route deleted a cell.  It did not
touch the surviving one.

**ROUTE B -- KKT-VARIETY EMPTINESS.  WALLED, AND THE FIRST OBSTRUCTION IS
STRUCTURAL.**  The chart stationarity variety is POSITIVE-DIMENSIONAL, so the planned
workflow -- take msolve's finite real solution list, test admissibility pointwise --
never starts.  Measured three independent ways and agreeing: Krull dimension 3 at
`(4,3)` and 5 at the `(6,3)` two-block class; exact Jacobian corank 3 at the
tetrahedron and 1 at the window witness.  Saturating the adjugate traces AND the
weights leaves the `(4,3)` dimension at 3.  Cost of the sweep even if it were
zero-dimensional: 2068 chart-side classes at roughly 0.37 decades per variable, with
memory binding before time -- only some 55 to 143 classes fit in 503 GiB.  One
untested repair exists, a multiplier-free encoding at 28 variables and 44 equations
CONSTANT in the active-family size; it is built and validated at two cells but not
benchmarked.  [All of this is measured outside Lean.]  Separately, the route's
central question was answered NO for the stationarity-only system by the shipped
`Gtz.windowChartProjection_isChartStationaryData`, whose value lies inside the sharp
window: only stationarity PLUS admissibility can be empty, and admissibility is a
disjunction of strict sign conditions that cannot enter an ideal.

**ROUTE C -- THE VALUE-ZERO CLASSIFICATION.  LANDED IN PART; ONE LEAF OPEN.**
`Gtz.not_saturatedAtom_of_chartValueZero` (a new exclusion that fires at value zero
and NOT at a crux, whose value is strictly negative),
`Gtz.not_posDef_subsetSum_sub_one_of_chartValueZeroAdmissible`,
`Gtz.IsChartValueZeroLimit` and the two leaves
`Gtz.isEmpty_sixThreeCrux_of_chartValueZeroLimit`,
`Gtz.hasNoChartValueZeroLimit_of_hingeHoldsAtSize`.  Leaf two is the SHIPPED hinge
`Gtz.HingeHoldsAtSize 6 3` plus two extra fields, so it is not a new question.  Leaf
one is open and is NOT a compactness extraction: every crux is a global minimiser of
the same objective over the same domain, so all cruxes carry one value in
`[-4/27, 0)` and no minimising sequence has values tending to zero.  A deformation is
needed.  The route's own obstruction is located:
`Gtz.exists_isTie_allHeavy_not_hasParallelPair_fiveThree` shows the class "exact tie,
all-heavy, no parallel pair" is INHABITED one size down, so leaf two's strength must
come from the two fields the `(5,3)` diamond is not known to carry.

**ROUTE D -- THE `(7,3)` STRESS AND THE RADON SPLIT.  CELL REFUTED, TOOL LANDED.**
Route A made `(7,3)` the derived side, so a `(7,3)` proof buys nothing.  Of the three
handles: the Radon split fires in 1 of 38 exact splits [measured outside Lean],
because whitening replaces the target `1` by `R / mass` and the pullback needs
`lambda_min(R) >= mass`; line-saturation IS the walk; and the syzygy handle was
refuted outright -- there is ONE dependency space, not two, now closed in both
directions by `Gtz.hadamardSquareGram_mulVec_eq_zero_iff`.  What survived is the tool,
and it became the stress layer above.

**ROUTE E -- MOMENT-SURFACE TOPOLOGY.  KILLED, AND THE KILL GENERALISES.**
`Gtz.dominates_iff_forall_moment_ge` exhibits every domination condition as the
minimum of a LINEAR functional over the moment image, so it sees only the CONVEX HULL
-- a contractible body whose affine dimension is `dim span of the Veronese images`
minus one, capped at five by the SIX ATOMS over `R` and over `C` alike.  No invariant
of the surface (Euler characteristic, homology, degree, covering) can obstruct a
condition that factors through a contractible object.  The domain dimension is free
too: for a real design the real and complex hulls COINCIDE.

**ROUTE F -- SECOND-ORDER MINIMALITY.  LANDED IN PART; OPEN, AND FIELD-BLIND.**
`Gtz.SixThreeCrux.exists_tight_annihilated_of_flatDirection` is the first consequence
of `isChartMinimiser` in the tree that is not first-order, and its active half is
margin-free in mechanism -- exact algebraic non-definiteness at every step size and
on both sides, which is what the zero-margin boundary condition demands.  Its
inactive half takes the step condition as a HYPOTHESIS rather than deriving it, and
turning that into an existential is the cheapest remaining step in the route.  The
index theorem `5 <= |A|` needs two further ingredients, the union-of-subspaces step
and the multiplier layer, and it degrades to `4 <= |A|` if an active tight vector has
support two, which is only a codimension-one condition.  Tie rigidity in the weight
directions IS discharged, as the rank check
`Gtz.eq_zero_of_flatDirection_of_span_top`, but only for simple minimal eigenvalues
and only in the weight slice -- the nine Grassmannian directions carry curvature that
nothing here bounds.  DECISIVE CAVEAT: the whole second-order derivation runs verbatim
over `C`, so route F cannot close the cell alone and must be combined with a realness
consumer.

## Boundary conditions the surviving routes still have to meet

Any proof of `IsEmpty Gtz.SixThreeCrux` must be (i) GLOBAL across triples -- all
twenty of the complex witness's triples die field-blind; (ii) REAL THROUGH STRUCTURE,
since `Gtz.complexGtzWeighted_six_three_fails` makes the statement false over `C`;
(iii) MARGIN-FREE in mechanism or explicitly two-regime, since the constrained
infimum of the domination margin is exactly one; (iv) sensitive to MAGNITUDES, since
the sign layer is sharp at 842 of 1024 two-graphs in eight realisable classes; (v)
equality cases EXACTLY the ties; (vi) carrying a stated zero-pairing branch, where the
strict-obtuse levers fail rather than merely resist; and (vii) if computational,
spending the stationarity equations -- which, per route B, is now known to be
insufficient by itself.

## The updated single next question

The previous run's answer was: **a positive lower bound on `|chartObjective|` at a
crux.**  THIS RUN DID NOT CHANGE IT, and one measurement this run sharpens why.

The margin law -- domination margin growing like `C * eps^2` with `C` in `[0.60, 3.75]`
across all eight surviving sign classes, `eps = |value|` [measured outside Lean] --
still says that ANY positive lower bound on `|chartObjective|` at a crux closes the
cell, and nothing landed this run bounds it.  What this run adds is evidence about
where NOT to look for one.  The newest field, stress-freeness, is SLACK AT THE WALL:
the all-heavy configuration that comes closest to being a crux (it fails only one of
the twenty triples, with slack 0.569) is stress-free with a healthy margin, its
Hadamard-square Gram having smallest-to-largest singular value ratio about `5.5e-3`
and determinant about `1.0e3`; and across four thousand random all-heavy
configurations there is NO systematic decline in that ratio as the number of failing
triples rises from nine toward twenty.  The exact TIES are the stress-carrying
objects -- the split tetrahedra and both diamonds have Hadamard-square determinant
exactly zero, because each has a parallel pair.  So the stress layer excludes the tie
stratum, a codimension-one locus that near-wall configurations are nowhere near.  It
is a real algebraic handle and a real strengthening of the box, but it is NOT the
mechanism that will close the cell, and neither is any further field of the same
shape.  [Measured outside Lean at 60 digits, on double-precision optimiser output;
the SPREAD across configurations is the signal, not any individual digit.]
-/

import Mathlib
import Gtz.Core.Basic
import Gtz.Design.DiamondLeverage
import Gtz.Quantitative.ChartSecondOrder
import Gtz.Quantitative.DesignQuadraticFloors
import Gtz.Quantitative.SixThreeCruxPropagation
import Gtz.Quantitative.SixThreeExclusionFrontier
import Gtz.Quantitative.SixThreeStressExclusion

namespace Gtz

open Matrix

open scoped BigOperators

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-! ## The quadratic floor at a crux -/

/-- **THE PAIRING-MASS FLOOR AT EVERY ATOM OF A CRUX.**  The squared pairings from an
atom to the other five outweigh its own leverage.  A crux carries
`hasStrictlyDominatingCoSingletons`, which is exactly the hypothesis the general floor
needs, and `isAllHeavy` supplies the nonzero atom. -/
theorem pairingMassFloor (atomIndex : Fin 6) :
    leverageOf (crux.design.atom atomIndex)
      < ∑ otherIndex ∈ ({atomIndex}ᶜ : Finset (Fin 6)),
          (crux.design.atom atomIndex ⬝ᵥ crux.design.atom otherIndex) ^ 2 :=
  leverage_lt_sum_sq_atomPairing_compl crux.design atomIndex
    (crux.hasStrictlyDominatingCoSingletons atomIndex)
    (atom_ne_zero_of_allHeavy crux.isAllHeavy atomIndex)

/-! ## The sharpened frontier

The layer `Gtz.SixThreeCrux.frontier` did not have.  Hypothesis-free, like its
predecessor, and like its predecessor not contradictory -- that remains the honest
state of the wall cell. -/

/-- **THE SHARPENED `(6,3)` EXCLUSION FRONTIER.**  Everything this run landed about a
crux, in one hypothesis-free statement.  It EXTENDS `Gtz.SixThreeCrux.frontier`
rather than replacing it: the full frontier is the two theorems conjoined. -/
theorem frontierSharp :
    -- THE STRESS LAYER: the six Veronese images are a BASIS of `Sym_3(R)`
    (∀ stress : Fin 6 → ℝ,
        (∑ c, stress c • atomMatrix (crux.design.atom c)) = 0 → stress = 0)
    -- its algebraic face: a single polynomial nonvanishing
    ∧ (hadamardSquareGram crux.design).det ≠ 0
    -- its geometric face: the six directions lie on NO conic of `RP^2`
    ∧ (∀ form : Matrix (Fin 3) (Fin 3) ℝ, formᵀ = form →
        (∀ atomIndex, crux.design.atom atomIndex ⬝ᵥ (form *ᵥ crux.design.atom atomIndex) = 0) →
        form = 0)
    -- and it excludes splittings no parallel-pair condition can see
    ∧ (∀ firstNormal secondNormal : Fin 3 → ℝ, firstNormal ≠ 0 → secondNormal ≠ 0 →
        ¬ (∀ atomIndex, firstNormal ⬝ᵥ crux.design.atom atomIndex = 0
          ∨ secondNormal ⬝ᵥ crux.design.atom atomIndex = 0))
    -- THE QUADRATIC FLOOR: squared pairing mass outweighs leverage at every atom
    ∧ (∀ atomIndex : Fin 6, leverageOf (crux.design.atom atomIndex)
        < ∑ otherIndex ∈ ({atomIndex}ᶜ : Finset (Fin 6)),
            (crux.design.atom atomIndex ⬝ᵥ crux.design.atom otherIndex) ^ 2)
    -- THE CHART GAP LAYER: all-heaviness as a strictly positive gap diagonal
    ∧ (∀ atomIndex : Fin 6, 0 < chartStationaryGap (projectionOfDesign crux.design)
        crux.design.weight atomIndex atomIndex)
    -- and the first characteristic coefficient, strictly positive at every triple
    ∧ (∀ triple : Finset (Fin 6), triple.card = 3 →
        0 < (∑ atomIndex ∈ triple, chartStationaryGap (projectionOfDesign crux.design)
              crux.design.weight atomIndex atomIndex)
            - 3 * chartObjective (chartPointOfDesign crux.design)) :=
  ⟨fun _ hstress => crux.stress_eq_zero hstress,
    crux.det_hadamardSquareGram_ne_zero,
    fun _ hsymmetric hquadric => crux.no_commonQuadric hsymmetric hquadric,
    fun _ _ hfirst hsecond => crux.not_twoPlanes hfirst hsecond,
    crux.pairingMassFloor,
    fun atomIndex =>
      pos_chartStationaryGap_diagonal_of_allHeavy crux.design crux.isAllHeavy atomIndex,
    fun triple hcard => crux.pos_firstCharacteristicCoefficient triple hcard⟩

end SixThreeCrux

/-! ## The sharpened refutation target

The shipped `Gtz.IsSixThreeRefutationCandidate` is untouched.  The sharp predicate
adds the DESIGN-LEVEL conjuncts of the new layer -- no chart appears in any of them,
so a search can still evaluate every one from the atoms and weights alone. -/

/-- **THE SHARPENED `(6,3)` REFUTATION TARGET.**  The shipped box with the new
design-level layer made explicit.  It is EQUIVALENT to `Gtz.IsSixThreeRefutationCandidate`
-- see `Gtz.isSixThreeRefutationCandidateSharp_iff` -- so it does not shrink the search
space; it hands a searcher four extra usable facts at every point of it.  The stress
conjunct and its determinant form are the same fact twice, stated both ways on purpose:
the quantified form is what a proof consumes, the determinant is a single polynomial
nonvanishing and hence what an algebraic search can saturate by. -/
def IsSixThreeRefutationCandidateSharp (design : WeightedDesign 6 3) : Prop :=
  IsSixThreeRefutationCandidate design
    ∧ (∀ stress : Fin 6 → ℝ,
        (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0)
    ∧ (hadamardSquareGram design).det ≠ 0
    ∧ (∀ form : Matrix (Fin 3) (Fin 3) ℝ, formᵀ = form →
        (∀ atomIndex, design.atom atomIndex ⬝ᵥ (form *ᵥ design.atom atomIndex) = 0) →
        form = 0)
    ∧ (∀ atomIndex : Fin 6, leverageOf (design.atom atomIndex)
        < ∑ otherIndex ∈ ({atomIndex}ᶜ : Finset (Fin 6)),
            (design.atom atomIndex ⬝ᵥ design.atom otherIndex) ^ 2)

/-- The sharp box sits inside the shipped one. -/
theorem isSixThreeRefutationCandidate_of_sharp {design : WeightedDesign 6 3}
    (hsharp : IsSixThreeRefutationCandidateSharp design) :
    IsSixThreeRefutationCandidate design := hsharp.1

/-- The design-level determinant law behind the stress layer: an all-heavy design whose
Veronese images are independent has a nonsingular Hadamard-square Gram.  A kernel vector
becomes a syzygy by the Frobenius identity, and the leverages -- positive by
all-heaviness -- rescale it into a genuine stress. -/
theorem det_hadamardSquareGram_ne_zero_of_allHeavy (design : WeightedDesign 6 3)
    (hallHeavy : AllHeavy design)
    (hstressFree : ∀ stress : Fin 6 → ℝ,
      (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0) :
    (hadamardSquareGram design).det ≠ 0 := by
  intro hdet
  obtain ⟨coefficient, hnonzero, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hleverage : ∀ c, 0 < leverageOf (design.atom c) := fun c =>
    lt_trans zero_lt_one (hallHeavy c)
  have hraw : (∑ c, (coefficient c / leverageOf (design.atom c))
      • atomMatrix (design.atom c)) = 0 := by
    rw [← momentCombination_eq_smul_sum design coefficient]
    exact momentCombination_eq_zero_of_mulVec_eq_zero design hkernel
  have hzero := hstressFree _ hraw
  refine hnonzero (funext fun c => ?_)
  have hentry : coefficient c / leverageOf (design.atom c) = 0 := congrFun hzero c
  rw [Pi.zero_apply]
  exact (div_eq_zero_iff.mp hentry).resolve_right (ne_of_gt (hleverage c))

/-- **AND THE SHIPPED BOX SITS INSIDE THE SHARP ONE.**  Every new conjunct is a
CONSEQUENCE of the box, not a new constraint on it: a nonzero stress and a common conic
each produce a dominating triple, which the box's own no-domination clause forbids, and
the quadratic floor follows from all-heaviness together with the strictly dominating
co-singletons.  So the sharp predicate does NOT shrink the search space -- what it buys
is four extra facts made explicit at every point of it, one of them a single polynomial
nonvanishing an algebraic search can saturate by. -/
theorem isSixThreeRefutationCandidateSharp_of_candidate {design : WeightedDesign 6 3}
    (hcandidate : IsSixThreeRefutationCandidate design) :
    IsSixThreeRefutationCandidateSharp design := by
  have hfields := hcandidate
  obtain ⟨hallHeavy, hcoSingletons, -, -, hnoDominating, -⟩ := hfields
  have hstressFree : ∀ stress : Fin 6 → ℝ,
      (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0 := by
    intro stress hstress
    by_contra hnonzero
    obtain ⟨selected, hcard, hdominates⟩ :=
      exists_dominating_sixThree_of_stress design hnonzero hstress
    exact hnoDominating selected hcard hdominates
  refine ⟨hcandidate, hstressFree,
    det_hadamardSquareGram_ne_zero_of_allHeavy design hallHeavy hstressFree, ?_,
    fun atomIndex => leverage_lt_sum_sq_atomPairing_compl design atomIndex
      (hcoSingletons atomIndex) (atom_ne_zero_of_allHeavy hallHeavy atomIndex)⟩
  intro form hsymmetric hquadric
  by_contra hnonzero
  obtain ⟨selected, hcard, hdominates⟩ :=
    exists_dominating_of_commonQuadric design hsymmetric hnonzero hquadric
  exact hnoDominating selected hcard hdominates

/-- **THE TWO BOXES ARE THE SAME BOX.**  Stated so that no reader takes the sharpened
frontier for a reduction of the search space: it is a reduction of the WORK at each
point, and nothing more. -/
theorem isSixThreeRefutationCandidateSharp_iff (design : WeightedDesign 6 3) :
    IsSixThreeRefutationCandidateSharp design ↔ IsSixThreeRefutationCandidate design :=
  ⟨isSixThreeRefutationCandidate_of_sharp, isSixThreeRefutationCandidateSharp_of_candidate⟩

/-- Every crux's design is a SHARP refutation candidate. -/
theorem isSixThreeRefutationCandidateSharp_of_sixThreeCrux (crux : SixThreeCrux) :
    IsSixThreeRefutationCandidateSharp crux.design := by
  obtain ⟨hstress, hdet, hconic, _, hfloor, _, _⟩ := crux.frontierSharp
  exact ⟨isSixThreeRefutationCandidate_of_sixThreeCrux crux, hstress, hdet, hconic, hfloor⟩

/-- **THE SHARP TARGET IS REACHED BY EVERY FAILURE.** -/
theorem exists_isSixThreeRefutationCandidateSharp_of_not_gtzWeighted_six_three
    (hfail : ¬ GtzWeighted 6 3) :
    ∃ design : WeightedDesign 6 3, IsSixThreeRefutationCandidateSharp design := by
  obtain ⟨crux⟩ := nonempty_sixThreeCrux_of_not_gtzWeighted_six_three hfail
  exact ⟨crux.design, isSixThreeRefutationCandidateSharp_of_sixThreeCrux crux⟩

/-- **THE SHARP SEARCH CRITERION.**  Emptying the box still suffices. -/
theorem gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidateSharp
    (hnone : ∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidateSharp design) :
    GtzWeighted 6 3 := by
  by_contra hfail
  obtain ⟨design, hcandidate⟩ :=
    exists_isSixThreeRefutationCandidateSharp_of_not_gtzWeighted_six_three hfail
  exact hnone design hcandidate

/-- **THE WHOLE RANK, ON THE SHARP BOX ALONE.**  No `(7,3)` antecedent: the stress
walk deleted it. -/
theorem gtzWeightedAll_three_of_forall_not_isSixThreeRefutationCandidateSharp
    (hnone : ∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidateSharp design) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidateSharp hnone)

/-- **THE ONE-ANTECEDENT TERMINUS.**  A single open hypothesis about `(6,3)` weighted
designs -- that none of them satisfies `Gtz.IsSixThreeRefutationCandidateSharp` --
settles rank three of the 1997 Goreinov-Tyrtyshnikov-Zamarashkin conjecture for EVERY
positive atom count.

To be exact about what is and is not claimed: this is an IMPLICATION.  Its antecedent
is open, and this tree contains no proof of it and no evidence that it is within
reach.  What the campaign established is that the antecedent is the ONLY thing
missing at rank three. -/
theorem gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidateSharp
    (hnone : ∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidateSharp design)
    (atomCount : ℕ) (hpos : 0 < atomCount) : GtzOriginal atomCount 3 :=
  gtz_original_rank_three_of_six_three
    (gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidateSharp hnone)
    atomCount hpos

end Gtz
