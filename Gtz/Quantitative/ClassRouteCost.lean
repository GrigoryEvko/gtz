/-
# THE CLASS-BY-CLASS ELIMINATION ROUTE — a second eliminant, and the proof that the
# route cannot be finished

`Gtz.Quantitative.ChartEmptinessCertificate` closed ONE class of the `(6,3)` covering
census — the two complementary triples — under a named elimination hypothesis, and
`Gtz.Quantitative.TwoBlockEliminationCertificate` discharged that hypothesis outright.
The obvious next question is whether the same machine reaches the other 2068 classes.

IT DOES NOT, and this file mechanizes both halves of the answer.

* The MACHINE STILL WORKS on the next classes up.  `threeMemberEliminant` is the
  elimination ideal generator of the three-member classes in the value variable, a
  degree-seven polynomial whose seven roots are exactly the seven sixths
  `-1/6, 0, 1/6, 1/3, 1/2, 2/3, 5/6`, none of which lies in the current window
  `[-4/27, 0)`.  Two census-surviving classes are closed by it, each conditional on
  its own instance of `EliminatesThreeMemberValue`.
* The MACHINE CANNOT FINISH.  `windowChartProjection_isChartStationaryData` is an
  EXACT chart stationarity datum over `Q(sqrt 5)` at
  `value = (2 - sqrt 5)/6 = -0.0393446629...`, STRICTLY INSIDE `[-4/27, 0)`, on the
  census-surviving class `{{0,3,5},{0,4,5},{1,2,3},{1,2,4}}`.
  `not_exists_windowRootFree_eliminatesWindowChartFamilyValue` is the consequence:
  NO function can be both an eliminant for that class and nonvanishing on the window.
  The route fails there at any cost, and it is a theorem rather than a timing
  measurement.

## What is proved here, unconditionally

* `threeMemberEliminant_eq_prod` and `threeMemberEliminant_eq_sixthProduct` — the
  factorisation `E3(g) = g(2g-1)(3g-2)(3g-1)(6g-5)(6g-1)(6g+1)`, equivalently
  `E3(g) = (1/72) prod_{j=-1}^{5} (6g - j)`, by `ring`.
* `threeMemberEliminant_pos_of_mem_flooredWindow` — `E3 > 0` on `[-4/27, 0)`, read
  off the rewriting `E3(g) = (-g)(1-2g)(2-3g)(1-3g)(5-6g)(1-6g)(6g+1)` in which all
  seven factors are strictly positive there.  No case analysis and no Handelman
  search: six factors are positive because `g < 0`, and the seventh, `6g + 1`, is
  positive because `-4/27 > -1/6`.  THAT LAST INEQUALITY IS THE WHOLE REASON EVERY
  ELIMINANT COMPUTED SO FAR CLOSES: there is no sixth in `[-4/27, 0)`, the largest
  negative sixth being `-1/6 < -4/27`.
* `threeMemberEliminant_eq_zero_iff` — the root set is EXACTLY the seven sixths.
* `sum_activeFamilyDegree_eq_rank_mul_card` and
  `forall_activeFamilyDegree_eq_one_iff_card_eq_two` — the double count
  `sum_c deg(c) = rank * |family|`, and its `(6,3)` reading: a covering family of
  triples has every atom of degree one IF AND ONLY IF it has exactly two members.
  The class the project has closed unconditionally was not merely the cheapest; it
  was the only one of its structural kind, and nothing about its cost extrapolates.
* `one_le_value_of_hasSaturatedAtom_of_isActiveFamily` — the SATURATED-ATOM FILTER,
  lifted from the shipped leg-side `Gtz.one_le_value_of_saturatedAtom` to the
  family-level vocabulary used here, together with the five `decide` audits below.
* The window witness, its inadmissibility, and the non-existence of a window-root-free
  eliminant for its class.

## The two new class closures, and what they cost in citable holes

`EliminatesThreeMemberValue` is a HYPOTHESIS, in the same sense and with the same
firewall as `Gtz.EliminatesChartTwoBlockValue`.  It is stated once, parameterized by
the family, and instantiated at exactly two families:

    `chartTripleSharedEdgeFamily    = {{0,1,2}, {0,4,5}, {1,2,3}}` ,
    `chartTriplePairwiseMeetFamily  = {{0,1,5}, {0,2,4}, {1,2,3}}` .

Each instance is a separate undischarged assumption.  TWO NEW CITABLE HOLES BOUGHT
TWO NEW CONDITIONAL CLOSURES; nothing here is unconditional, and neither closure has
the strength of
`Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_design_of_negativeValue`,
which carries no such hypothesis at all.

Three antecedents of the hypothesis are load-bearing and none is decoration.

* THE RANK-ONE BRANCH, `HasSimpleActiveSubsets`: at most one active label per subset,
  hence a rank-one multiplier block on each.  This is what the outside computation
  actually covered, and it is IN THE STATEMENT rather than in prose.  The bundle
  permits several labels sharing a subset; those branches are covered by nothing here.
* THE FAMILY, `IsActiveFamily`: the active subsets are exactly the three triples
  named, as a set.  A class, never a cell.
* NEGATIVITY.  The elimination is an elimination of the stationarity ideal; the sign
  is what the closure consumes, through the floor.

ADMISSIBILITY IS DELIBERATELY ABSENT from `EliminatesThreeMemberValue`, and that is a
difference from `Gtz.EliminatesChartTwoBlockValue`, which carries
`Gtz.IsChartArgmaxValue`.  The reason is honesty about what an elimination ideal is:
the outside computation eliminated the STATIONARITY system, in which admissibility
does not appear, so the hypothesis matching it is the admissibility-free one.  It is
the stronger assumption of the two, and the window witness below refutes the same
admissibility-free shape at a third family — one hypothesis shape, satisfied as far as
computed at two families and REFUTED at a third.

## Where the floor enters, and where it does not

`Gtz.combinedValueFloor 6 3 = -(4/27)` (`Gtz.combinedValueFloor_sixThree`, shipped), so
the two closures need no floor hypothesis: the design and the argmax field they already
carry supply it through `Gtz.combinedValueFloor_le_value_of_isChartStationaryData`.  The
floor is class-INDEPENDENT.  It narrows the window for all 2069 classes and excludes
NONE of them; what it does here is make the seven-sixths root set miss the window, which
the older `-1/6` window did not.

## THE COSTED IMPOSSIBILITY — measurements, quoted as measurements

None of the following is inside Lean and none of it is a proof.  Instrument: msolve
0.10.1 over the rationals, two blocks each graded reverse lexicographic, the value
variable alone surviving; 2 x AMD EPYC 9655, 503 GiB.

    vars   family                                    wall        memory
      12   {{0,4,5},{1,2,3}}                        0.018 s      —
      20   {{0,1,4},{0,1,5},{0,2,3}}                0.78  s      —
      21   {{0,1,5},{0,2,4},{1,2,3}}                3.24  s      —
      21   {{0,1,2},{0,4,5},{1,2,3}}               13.4   s      —
      26   {{0,1,2},{0,1,3},{0,1,4},{0,1,5}}      750     s     19.7 GiB
      27   (cheapest surviving four-member class)  INCOMPLETE at 3976 s, 57.7 GiB

Growth over the completed runs is 0.319 decades per variable on `12 -> 21` and 0.350 on
`21 -> 26`; 0.33, a factor 2.14 per variable, is the figure to quote.  Variable counts
over the 2069 classes give cumulative reach 5 at `<= 26`, 19 at `<= 30`, 56 at `<= 36`,
144 at `<= 42`, with 1925 classes (93%) needing at least 47.  The modal class is
`|A| = 10` with 351 members at 65-66 variables, which extrapolates to `1e8`-`1e9` years
each.  The memory wall on 503 GiB lands between 28 and 30 variables, independently of
time.

TWO OF THE SIX RUNS WERE WASTED, and that is the part of the measurement worth carrying
forward.  The 20-variable class and the 26-variable, 750-second, 19.7-GiB double star
both carry a SATURATED ATOM — an index lying in every member — and the shipped
`Gtz.one_le_value_of_saturatedAtom` kills such a family combinatorially, in one line,
with no Groebner basis.  Exactly 23 of the 2069 classes are saturated [computed outside
Lean; the shipped census note in the header of `Gtz.Quantitative.InteriorExclusion`
records the same filter as taking the covering `p >= 3` orbit count from 2101 to 2078,
which is the same 23].  ANY FUTURE CLASS SELECTION MUST APPLY THAT FILTER FIRST.
Re-selecting after it, the cheapest surviving four-member class needs 27 variables,
which is exactly where the tool did not finish; so the honest reach of the route at four
members and beyond is nil, and its total reach is the three surviving classes at
`|A| <= 3`.  [The census has ONE class at `|A| = 2` and THREE at `|A| = 3`; the star is
one of the three and is saturated, so three of those four survive.  The size
distribution over the 2102 covering orbits is
`1, 3, 15, 37, 88, 157, 247, 311, 351, 312, 249, 161, 94, 43, 21, 7, 3, 1, 1` for
`|A| = 2..20`, and the last five entries are the 33 orbits Caratheodory discards.]

READ THE FILTER'S SIDE CORRECTLY.  `Gtz.one_le_value_of_saturatedAtom` is a LEG-side
theorem, about `Gtz.IsQuadricStationaryData`, and the eliminants above are CHART-side.
The two systems are two coordinate systems on one problem and the census of active
families is common to both, which is why the filter belongs in class selection; but no
chart-side analogue of the saturated-atom exclusion is shipped, and none is claimed
here.  `one_le_value_of_hasSaturatedAtom_of_isActiveFamily` is stated on the side where
it is true.

`hasSaturatedAtom_chartTripleStarFamily` and
`hasSaturatedAtom_chartTripleDoubleStarFamily` mechanize the two audits;
`not_hasSaturatedAtom_chartTripleSharedEdgeFamily`,
`not_hasSaturatedAtom_chartTriplePairwiseMeetFamily` and
`not_hasSaturatedAtom_windowChartFamily` mechanize the three that survive it.

## The window witness — the obstruction cost does not touch

`windowChartProjection` is `(1/2) I + (sqrt 5 / 10) B` with `B` an explicit symmetric
integer matrix of trace zero satisfying `B^2 = 5 I` — which is the whole reason the
chart is a projection, and the reason nothing in this file needs a spectral
decomposition.  Its weights are `1/6 - sqrt 5/30` at four atoms and `1/6 + sqrt 5/15`
at two, its four tight directions are the normalised sign patterns of the four triples
with multiplier `1/4` each, and its assembly is `1/12` times an integer matrix of
constant diagonal two, hence `1/6`.  Every field of the bundle is discharged.  The
`sqrt 5` relation is used in exactly two places, idempotence and the inadmissibility
margin; tightness, the trace, the weight sum and the commutation are all linear in
`sqrt 5` and need no relation at all.

The datum is INADMISSIBLE (`not_windowChartProjection_isChartArgmaxValue`): on the
triple `{1,3,4}` the gap's quadratic form is positive semidefinite, by one completed
square, so no probe supported there reaches a negative Rayleigh quotient, let alone
`(2 - sqrt 5)/6`.  THAT IS WHY IT CONTRADICTS NOTHING SHIPPED — every value floor in
the repository carries `Gtz.IsChartArgmaxValue` — and it is also exactly why it is
fatal to the route.  An eliminant is a consequence of the STATIONARITY ideal;
admissibility is `lambda_min(W[C]) <= value` at each of twenty triples, a disjunction of
three characteristic-coefficient sign conditions apiece, hence `3^20` branches, and it
is not in the ideal.  The obstruction the header of
`Gtz.Quantitative.ChartEmptinessCertificate` records in prose is here a witness.

## What this file does NOT claim

* NOT that five classes are closed.  Two of the four new eliminants are on saturated
  families that were already dead; the honest tally after this pass is ONE class closed
  unconditionally (elsewhere) and TWO more closed conditionally (here).
* NOT that the eliminants lie in their elimination ideals in a `ring`-checkable sense.
  No cofactor list was produced for `threeMemberEliminant`; it is msolve output
  cross-checked over five primes and by a reversed variable order, which is exactly the
  standing the two-block cubic had before it was discharged by a trace argument rather
  than by cofactors.
* NOT a universal "all chart-stationary values at `(6,3)` are sixths" law.  That is
  FALSE, and `windowChartProjection_isChartStationaryData` is the refutation.
* NOT any correction to the census counts 2102, 2069, 2068.  They are right.
* NOT that the window witness refutes anything.  It is inadmissible; it refutes the
  ROUTE, not the conjecture, and `GtzWeighted 6 3` is untouched by everything here.

## Inherited honesty

Everything below is conditional on `Gtz.IsChartStationaryData`, which is a HYPOTHESIS:
the variational derivation that would produce it is not formalized, the system is
NECESSARY only, and it is satisfied at admissible non-minima.  Read the header of
`Gtz.Quantitative.ChartStationary` first.  Three classes of 2069 is three classes, and
`(6,3)` is not closed.
-/
import Mathlib
import Gtz.Quantitative.TwoBlockEliminationCertificate
import Gtz.Quantitative.ElementaryValueFloor
import Gtz.Quantitative.InteriorExclusion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The three-member eliminant -/

/-- **THE THREE-MEMBER ELIMINANT**
`E3(g) = 3888 g^7 - 9072 g^6 + 7560 g^5 - 2520 g^4 + 147 g^3 + 77 g^2 - 10 g`.

The generator of the elimination ideal of the rank-one branch of a THREE-MEMBER `(6,3)`
chart stationarity system in the value variable.  The census has exactly three classes
with three members, and the outside computation returned this same polynomial at all
three.  A DEFINITION of a degree seven polynomial and nothing more: that it IS that
generator is outside arithmetic, recorded in the file header, and is used below only
through the named hypothesis `EliminatesThreeMemberValue`. -/
def threeMemberEliminant (value : ℝ) : ℝ :=
  3888 * value ^ 7 - 9072 * value ^ 6 + 7560 * value ^ 5 - 2520 * value ^ 4 + 147 * value ^ 3
    + 77 * value ^ 2 - 10 * value

/-- **The eliminant factors over the rationals**, with all seven roots visible:
`E3 = g(2g-1)(3g-2)(3g-1)(6g-5)(6g-1)(6g+1)`. -/
theorem threeMemberEliminant_eq_prod (value : ℝ) :
    threeMemberEliminant value
      = value * (2 * value - 1) * (3 * value - 2) * (3 * value - 1) * (6 * value - 5)
        * (6 * value - 1) * (6 * value + 1) := by
  unfold threeMemberEliminant
  ring

/-- **The eliminant is the seven consecutive sixths**,
`E3(g) = (1/72) prod_{j=-1}^{5} (6g - j)`. -/
theorem threeMemberEliminant_eq_sixthProduct (value : ℝ) :
    threeMemberEliminant value
      = (6 * value + 1) * (6 * value) * (6 * value - 1) * (6 * value - 2) * (6 * value - 3)
          * (6 * value - 4) * (6 * value - 5) / 72 := by
  unfold threeMemberEliminant
  ring

/-- **The eliminant with every factor positive on the window**: pairing off the six
negative factors of the root form,

    `E3(g) = (-g)(1 - 2g)(2 - 3g)(1 - 3g)(5 - 6g)(1 - 6g)(6g + 1)` .

On `-4/27 <= g < 0` the first six factors are positive because `g < 0`, and the seventh
because `g > -1/6`. -/
theorem threeMemberEliminant_eq_windowPositiveProduct (value : ℝ) :
    threeMemberEliminant value
      = -value * (1 - 2 * value) * (2 - 3 * value) * (1 - 3 * value) * (5 - 6 * value)
        * (1 - 6 * value) * (6 * value + 1) := by
  unfold threeMemberEliminant
  ring

/-- **THE ARITHMETIC FACT THE WHOLE CLOSURE TURNS ON**: the largest negative sixth is
`-1/6`, and `-1/6 < -4/27`.  Every eliminant computed at `(6,3)` so far has all its
roots in `(1/6) Z`, and there is no sixth in `[-4/27, 0)` — which is why they close, and
why the improvement of the floor from `-1/6` to `-4/27` is what makes them close.  The
pattern is NOT a law: `windowChartValue` below is an irrational chart-stationary
value. -/
theorem neg_inv_six_lt_neg_four_div_twentySeven : -(1 / 6 : ℝ) < -(4 / 27 : ℝ) := by
  norm_num

/-- **THE ELIMINANT IS STRICTLY POSITIVE ON THE FLOORED WINDOW** `[-4/27, 0)`, straight
off the positive-factor form: seven strictly positive factors. -/
theorem threeMemberEliminant_pos_of_mem_flooredWindow (value : ℝ)
    (hfloor : -(4 / 27 : ℝ) ≤ value) (hnegative : value < 0) :
    0 < threeMemberEliminant value := by
  rw [threeMemberEliminant_eq_windowPositiveProduct]
  have hdescending : (0 : ℝ) < -value := by linarith
  have hfirstFactor : (0 : ℝ) < 1 - 2 * value := by linarith
  have hsecondFactor : (0 : ℝ) < 2 - 3 * value := by linarith
  have hthirdFactor : (0 : ℝ) < 1 - 3 * value := by linarith
  have hfourthFactor : (0 : ℝ) < 5 - 6 * value := by linarith
  have hfifthFactor : (0 : ℝ) < 1 - 6 * value := by linarith
  have hascending : (0 : ℝ) < 6 * value + 1 := by linarith
  positivity

/-- **THE EMPTINESS CERTIFICATE FOR THE THREE-MEMBER CLASSES.**  The one-variable system
`E3(value) = 0`, `-4/27 <= value`, `value < 0` has NO real solution. -/
theorem threeMemberEliminant_ne_zero_of_flooredNegativeValue (value : ℝ)
    (hfloor : -(4 / 27 : ℝ) ≤ value) (hnegative : value < 0) :
    threeMemberEliminant value ≠ 0 :=
  ne_of_gt (threeMemberEliminant_pos_of_mem_flooredWindow value hfloor hnegative)

/-- The emptiness result in existential form. -/
theorem not_exists_flooredNegativeValue_root_threeMemberEliminant :
    ¬ ∃ value : ℝ, -(4 / 27 : ℝ) ≤ value ∧ value < 0 ∧ threeMemberEliminant value = 0 := by
  rintro ⟨value, hfloor, hnegative, hroot⟩
  exact threeMemberEliminant_ne_zero_of_flooredNegativeValue value hfloor hnegative hroot

/-- **The root set is EXACTLY the seven sixths.** -/
theorem threeMemberEliminant_eq_zero_iff (value : ℝ) :
    threeMemberEliminant value = 0 ↔
      value = -(1 / 6) ∨ value = 0 ∨ value = 1 / 6 ∨ value = 1 / 3 ∨ value = 1 / 2
        ∨ value = 2 / 3 ∨ value = 5 / 6 := by
  rw [threeMemberEliminant_eq_prod]
  constructor
  · intro hroot
    rcases mul_eq_zero.mp hroot with hleadingSix | hlastFactor
    · rcases mul_eq_zero.mp hleadingSix with hleadingFive | hsixthFactor
      · rcases mul_eq_zero.mp hleadingFive with hleadingFour | hfifthFactor
        · rcases mul_eq_zero.mp hleadingFour with hleadingThree | hfourthFactor
          · rcases mul_eq_zero.mp hleadingThree with hleadingPair | hthirdFactor
            · rcases mul_eq_zero.mp hleadingPair with hfirstFactor | hsecondFactor
              · exact Or.inr (Or.inl hfirstFactor)
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inl (by linarith)
  · rintro (hroot | hroot | hroot | hroot | hroot | hroot | hroot) <;> rw [hroot] <;> ring

/-! ## The vocabulary a class carries -/

variable {size : ℕ} {activeIndex : Type*}

/-- **THE ACTIVE FAMILY OF A DATUM IS A NAMED CLASS**: the image of the active set under
the subset map is exactly `family`, as a set of subsets.  A class, never a cell: nothing
is said about which label carries which subset. -/
def IsActiveFamily (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin size))
    (family : Finset (Finset (Fin size))) : Prop :=
  activeSet.image activeSubset = family

/-- **THE RANK-ONE BRANCH**: at most one active label per subset, so each subset carries
a single tight direction and its multiplier block has rank one.  This is the branch the
outside elimination covered, and the bundle does NOT force it. -/
def HasSimpleActiveSubsets (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin size)) : Prop :=
  ∀ firstLabel ∈ activeSet, ∀ secondLabel ∈ activeSet,
    activeSubset firstLabel = activeSubset secondLabel → firstLabel = secondLabel

/-- **A SATURATED ATOM** of a family: an index lying in every member.  A purely
combinatorial property of the class, decidable at `(6,3)` in one `decide`. -/
def HasSaturatedAtom (family : Finset (Finset (Fin size))) : Prop :=
  ∃ atomIndex : Fin size, ∀ chosenSubset ∈ family, atomIndex ∈ chosenSubset

/-- Every active subset of a datum whose family is `family` is a member of `family`. -/
theorem mem_of_isActiveFamily {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {family : Finset (Finset (Fin size))}
    (hfamily : IsActiveFamily activeSet activeSubset family) {activeLabel : activeIndex}
    (hactive : activeLabel ∈ activeSet) :
    activeSubset activeLabel ∈ family := by
  rw [← hfamily]
  exact Finset.mem_image_of_mem activeSubset hactive

/-! ## The saturated-atom filter, at the level of the family -/

/-- **THE SATURATED-ATOM FILTER, IN FAMILY VOCABULARY.**  A leg-side stationarity datum
whose active family carries a saturated atom has `1 <= value`, so it is not a below-one
counterexample at all.

This is the shipped `Gtz.one_le_value_of_saturatedAtom` with the hypothesis restated at
the class rather than at the labels — which is the form a census filter is applied in,
and the form in which the audits below are `decide`-able.  It is the exclusion that two
of the six measured elimination runs of the file header should have been tested against
before the runs were started. -/
theorem one_le_value_of_hasSaturatedAtom_of_isActiveFamily {atomCount rank : ℕ}
    {design : WeightedDesign atomCount rank} {value : ℝ}
    {multiplierMatrix : Matrix (Fin rank) (Fin rank) ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin atomCount)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin rank → ℝ)} {family : Finset (Finset (Fin atomCount))}
    (hdata : IsQuadricStationaryData design value multiplierMatrix activeSet activeSubset
      activeWeight tightDir)
    (hvalueNe : value ≠ 0) (hfamily : IsActiveFamily activeSet activeSubset family)
    (hsaturated : HasSaturatedAtom family) :
    1 ≤ value := by
  obtain ⟨atomIndex, hmemAll⟩ := hsaturated
  exact one_le_value_of_saturatedAtom hdata hvalueNe fun activeLabel hactive =>
    hmemAll (activeSubset activeLabel) (mem_of_isActiveFamily hfamily hactive)

/-! ## The double count, and why the closed class was the only one of its kind -/

/-- The DEGREE of an atom in a family: how many members contain it. -/
def activeFamilyDegree (family : Finset (Finset (Fin size))) (atomIndex : Fin size) : ℕ :=
  (family.filter fun chosenSubset => atomIndex ∈ chosenSubset).card

/-- **THE DOUBLE COUNT** `sum_c deg(c) = rank * |family|`, for a family all of whose
members have exactly `rank` atoms.  Counting the incidence pairs by atom and by
member. -/
theorem sum_activeFamilyDegree_eq_rank_mul_card {rank : ℕ}
    (family : Finset (Finset (Fin size)))
    (hcard : ∀ chosenSubset ∈ family, chosenSubset.card = rank) :
    ∑ atomIndex : Fin size, activeFamilyDegree family atomIndex = rank * family.card := by
  have hbyAtom : ∀ atomIndex : Fin size, activeFamilyDegree family atomIndex
      = ∑ chosenSubset ∈ family, if atomIndex ∈ chosenSubset then 1 else 0 := by
    intro atomIndex
    rw [activeFamilyDegree, Finset.card_filter]
  have hbySubset : ∀ chosenSubset ∈ family,
      (∑ atomIndex : Fin size, if atomIndex ∈ chosenSubset then 1 else 0) = rank := by
    intro chosenSubset hmember
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
    exact hcard chosenSubset hmember
  calc ∑ atomIndex : Fin size, activeFamilyDegree family atomIndex
      = ∑ atomIndex : Fin size, ∑ chosenSubset ∈ family,
          if atomIndex ∈ chosenSubset then 1 else 0 :=
        Finset.sum_congr rfl fun atomIndex _ => hbyAtom atomIndex
    _ = ∑ chosenSubset ∈ family, ∑ atomIndex : Fin size,
          if atomIndex ∈ chosenSubset then 1 else 0 := Finset.sum_comm
    _ = ∑ _chosenSubset ∈ family, rank := Finset.sum_congr rfl hbySubset
    _ = rank * family.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **THE TWO-BLOCK CLASS IS THE UNIQUE ONE OF ITS KIND AT `(6,3)`.**  A covering family
of triples of six atoms has every atom of degree ONE if and only if it has exactly TWO
members, because the degrees sum to `3 |family|`.

The single class this project has closed unconditionally is that one, and the statement
here is what says its cheapness does not generalise: it is the only class whose
multiplier assembly has no continuous freedom, so its 0.018-second elimination
extrapolates to nothing. -/
theorem forall_activeFamilyDegree_eq_one_iff_card_eq_two
    (family : Finset (Finset (Fin 6))) (hcard : ∀ chosenSubset ∈ family, chosenSubset.card = 3)
    (hcovering : ∀ atomIndex : Fin 6, ∃ chosenSubset ∈ family, atomIndex ∈ chosenSubset) :
    (∀ atomIndex : Fin 6, activeFamilyDegree family atomIndex = 1) ↔ family.card = 2 := by
  have hdouble := sum_activeFamilyDegree_eq_rank_mul_card (rank := 3) family hcard
  constructor
  · intro hdegreeOne
    rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hdegreeOne atomIndex,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hdouble
    omega
  · intro hcardTwo
    rw [hcardTwo] at hdouble
    have hpositive : ∀ atomIndex : Fin 6, 1 ≤ activeFamilyDegree family atomIndex := by
      intro atomIndex
      obtain ⟨chosenSubset, hmember, hmemAtom⟩ := hcovering atomIndex
      rw [activeFamilyDegree, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
      exact ⟨chosenSubset, Finset.mem_filter.mpr ⟨hmember, hmemAtom⟩⟩
    by_contra hnotAllOne
    obtain ⟨witnessAtom, hwitness⟩ : ∃ atomIndex : Fin 6,
        activeFamilyDegree family atomIndex ≠ 1 := by
      by_contra hallOne
      simp only [not_exists, not_not] at hallOne
      exact hnotAllOne hallOne
    have hstrict : (∑ _atomIndex : Fin 6, 1) < ∑ atomIndex : Fin 6,
        activeFamilyDegree family atomIndex :=
      Finset.sum_lt_sum (fun atomIndex _ => hpositive atomIndex)
        ⟨witnessAtom, Finset.mem_univ witnessAtom, by
          have hlower := hpositive witnessAtom
          omega⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
      hdouble] at hstrict
    omega

/-! ## The four measured three-member and four-member classes -/

/-- The three-member class `{{0,1,2}, {0,4,5}, {1,2,3}}`: two of its members share the
EDGE `{1,2}`, and one pair of members is disjoint.  21 variables, 13.4 s. -/
def chartTripleSharedEdgeFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 4, 5}, {1, 2, 3}}

/-- The three-member class `{{0,1,5}, {0,2,4}, {1,2,3}}`: every two members meet in
exactly ONE atom.  21 variables, 3.24 s. -/
def chartTriplePairwiseMeetFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 5}, {0, 2, 4}, {1, 2, 3}}

/-- The three-member class `{{0,1,4}, {0,1,5}, {0,2,3}}` — the STAR at atom `0`, the
cheapest three-member elimination at 20 variables and 0.78 s, AND ALREADY DEAD before it
was run. -/
def chartTripleStarFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 4}, {0, 1, 5}, {0, 2, 3}}

/-- The four-member class `{{0,1,2}, {0,1,3}, {0,1,4}, {0,1,5}}` — the DOUBLE STAR at
`{0,1}`, the most expensive completed elimination at 26 variables, 750 s and 19.7 GiB,
AND ALREADY DEAD before it was run. -/
def chartTripleDoubleStarFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5}}

/-- **THE STAR CLASS IS SATURATED AT ATOM `0`** — so `Gtz.one_le_value_of_saturatedAtom`
excludes it in one line, and its 0.78-second elimination bought nothing. -/
theorem hasSaturatedAtom_chartTripleStarFamily : HasSaturatedAtom chartTripleStarFamily := by
  unfold HasSaturatedAtom chartTripleStarFamily
  decide

/-- **THE DOUBLE STAR IS SATURATED** — at atoms `0` and `1` both.  Its 750-second,
19.7-GiB elimination bought nothing either. -/
theorem hasSaturatedAtom_chartTripleDoubleStarFamily :
    HasSaturatedAtom chartTripleDoubleStarFamily := by
  unfold HasSaturatedAtom chartTripleDoubleStarFamily
  decide

/-- The shared-edge class survives the saturated-atom filter. -/
theorem not_hasSaturatedAtom_chartTripleSharedEdgeFamily :
    ¬ HasSaturatedAtom chartTripleSharedEdgeFamily := by
  unfold HasSaturatedAtom chartTripleSharedEdgeFamily
  decide

/-- The pairwise-meet class survives the saturated-atom filter. -/
theorem not_hasSaturatedAtom_chartTriplePairwiseMeetFamily :
    ¬ HasSaturatedAtom chartTriplePairwiseMeetFamily := by
  unfold HasSaturatedAtom chartTriplePairwiseMeetFamily
  decide

/-! ## The two conditional class closures -/

/-- **THE THREE-MEMBER ELIMINATION STEP, AS A HYPOTHESIS**, parameterized by the class.

It says: a chart stationarity datum on the RANK-ONE BRANCH whose active family is
`family` and whose value is negative satisfies `E3(value) = 0`.

Named and defined separately rather than baked into a theorem, exactly as
`Gtz.EliminatesChartTwoBlockValue` is, so that each instance is a citable hole.  It is
NOT proved here at any family.  Outside Lean it is asserted at exactly two families,
`chartTripleSharedEdgeFamily` and `chartTriplePairwiseMeetFamily`, on the evidence of an
msolve elimination cross-checked over five primes and by a reversed variable order; no
cofactor list exists for either, so neither is `ring`-checkable.

ADMISSIBILITY IS ABSENT ON PURPOSE.  What was eliminated is the stationarity ideal, in
which `Gtz.IsChartArgmaxValue` does not appear; the hypothesis matching the computation
is therefore the admissibility-free one, which is the STRONGER assumption.
`not_exists_windowRootFree_eliminatesWindowChartFamilyValue` refutes this same shape at a
third family, so the shape is not vacuous in either direction.

Instantiating it at any other family is possible and meaningless: nothing supplies it
there, and a hypothesis nobody can discharge proves nothing. -/
def EliminatesThreeMemberValue (family : Finset (Finset (Fin 6))) : Prop :=
  ∀ (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ) (value : ℝ)
    (activeSet : Finset activeIndex) (activeSubset : activeIndex → Finset (Fin 6))
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin 6 → ℝ)),
    IsChartStationaryData 3 projection weight value activeSet activeSubset activeWeight
        tightDir →
      IsActiveFamily activeSet activeSubset family →
        HasSimpleActiveSubsets activeSet activeSubset →
          value < 0 → threeMemberEliminant value = 0

/-- **THE CLOSURE OF A THREE-MEMBER CLASS, GIVEN ITS ELIMINATION STEP.**  A chart
stationarity datum on the rank-one branch, whose chart is a design's, which is
admissible, and whose active family is a class the elimination step covers, has a
NONNEGATIVE value.

The floor is NOT a hypothesis: `Gtz.combinedValueFloor_le_value_of_isChartStationaryData`
supplies `-4/27 <= value` from the design and the admissibility already present, and the
seven roots of `E3` avoid `[-4/27, 0)` for the arithmetic reason that no sixth lies
there. -/
theorem zero_le_value_of_eliminatesThreeMemberValue
    {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ} {value : ℝ}
    {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)}
    {family : Finset (Finset (Fin 6))}
    (heliminates : EliminatesThreeMemberValue (activeIndex := activeIndex) family)
    (design : WeightedDesign 6 3) (hchart : projection = projectionOfDesign design)
    (hdata : IsChartStationaryData 3 projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hargmax : IsChartArgmaxValue 3 projection weight value)
    (hfamily : IsActiveFamily activeSet activeSubset family)
    (hsimple : HasSimpleActiveSubsets activeSet activeSubset) :
    0 ≤ value := by
  by_contra hnegative
  rw [not_le] at hnegative
  have hfloor := combinedValueFloor_le_value_of_isChartStationaryData design hchart hargmax hdata
  rw [combinedValueFloor_sixThree] at hfloor
  exact threeMemberEliminant_ne_zero_of_flooredNegativeValue value hfloor hnegative
    (heliminates projection weight value activeSet activeSubset activeWeight tightDir hdata
      hfamily hsimple hnegative)

/-- **THE NON-EXISTENCE FORM.**  Given its elimination step, a class carries NO
admissible rank-one-branch chart stationarity datum behind a design at a negative
value. -/
theorem not_isChartStationaryData_of_eliminatesThreeMemberValue_of_negativeValue
    {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ} {value : ℝ}
    {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)}
    {family : Finset (Finset (Fin 6))}
    (heliminates : EliminatesThreeMemberValue (activeIndex := activeIndex) family)
    (design : WeightedDesign 6 3) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue 3 projection weight value)
    (hfamily : IsActiveFamily activeSet activeSubset family)
    (hsimple : HasSimpleActiveSubsets activeSet activeSubset) (hnegative : value < 0) :
    ¬ IsChartStationaryData 3 projection weight value activeSet activeSubset activeWeight
        tightDir := by
  intro hdata
  exact absurd (zero_le_value_of_eliminatesThreeMemberValue heliminates design hchart hdata
    hargmax hfamily hsimple) (not_le.mpr hnegative)

/-- **THE SHARED-EDGE CLASS IS CLOSED, conditionally on its own elimination step.**  One
of the two census-surviving classes this pass adds; the hypothesis is undischarged and
is a new citable hole. -/
theorem zero_le_value_of_chartTripleSharedEdgeFamily_of_eliminates
    {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ} {value : ℝ}
    {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)}
    (heliminates : EliminatesThreeMemberValue (activeIndex := activeIndex)
      chartTripleSharedEdgeFamily)
    (design : WeightedDesign 6 3) (hchart : projection = projectionOfDesign design)
    (hdata : IsChartStationaryData 3 projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hargmax : IsChartArgmaxValue 3 projection weight value)
    (hfamily : IsActiveFamily activeSet activeSubset chartTripleSharedEdgeFamily)
    (hsimple : HasSimpleActiveSubsets activeSet activeSubset) :
    0 ≤ value :=
  zero_le_value_of_eliminatesThreeMemberValue heliminates design hchart hdata hargmax hfamily
    hsimple

/-- **THE PAIRWISE-MEET CLASS IS CLOSED, conditionally on its own elimination step.**
The other census-surviving class this pass adds. -/
theorem zero_le_value_of_chartTriplePairwiseMeetFamily_of_eliminates
    {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ} {value : ℝ}
    {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)}
    (heliminates : EliminatesThreeMemberValue (activeIndex := activeIndex)
      chartTriplePairwiseMeetFamily)
    (design : WeightedDesign 6 3) (hchart : projection = projectionOfDesign design)
    (hdata : IsChartStationaryData 3 projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hargmax : IsChartArgmaxValue 3 projection weight value)
    (hfamily : IsActiveFamily activeSet activeSubset chartTriplePairwiseMeetFamily)
    (hsimple : HasSimpleActiveSubsets activeSet activeSubset) :
    0 ≤ value :=
  zero_le_value_of_eliminatesThreeMemberValue heliminates design hchart hdata hargmax hfamily
    hsimple

/-! ## A half-shifted integer core, and when it is a projection

The window chart is `(1/2) I + scale * B`.  Everything the bundle asks of it follows
from three facts about `B` — symmetry, trace zero, and `B^2 = 5 I` — together with
`scale^2 = 1/20`, and none of the four needs a spectral decomposition. -/

/-- **HALF THE IDENTITY PLUS A SCALED CORE.** -/
noncomputable def halfCoreShift {dimension : ℕ} (scale : ℝ)
    (core : Matrix (Fin dimension) (Fin dimension) ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  (2 : ℝ)⁻¹ • (1 : Matrix (Fin dimension) (Fin dimension) ℝ) + scale • core

theorem halfCoreShift_transpose {dimension : ℕ} (scale : ℝ)
    (core : Matrix (Fin dimension) (Fin dimension) ℝ) (hsymmetric : coreᵀ = core) :
    (halfCoreShift scale core)ᵀ = halfCoreShift scale core := by
  rw [halfCoreShift, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_one, hsymmetric]

theorem halfCoreShift_trace {dimension : ℕ} (scale : ℝ)
    (core : Matrix (Fin dimension) (Fin dimension) ℝ) :
    Matrix.trace (halfCoreShift scale core)
      = (2 : ℝ)⁻¹ * (dimension : ℝ) + scale * Matrix.trace core := by
  rw [halfCoreShift, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one]
  simp

/-- **THE HALF-SHIFT OF A SQUARE ROOT OF FIVE IS A PROJECTION.**  With `B^2 = 5 I` and
`scale^2 = 1/20`, the cross terms give `scale * B` back and the two identity terms give
`1/4 + 5/20 = 1/2`. -/
theorem halfCoreShift_mul_self {dimension : ℕ} (scale : ℝ)
    (core : Matrix (Fin dimension) (Fin dimension) ℝ)
    (hcore : core * core = (5 : ℝ) • (1 : Matrix (Fin dimension) (Fin dimension) ℝ))
    (hscale : scale * scale = (20 : ℝ)⁻¹) :
    halfCoreShift scale core * halfCoreShift scale core = halfCoreShift scale core := by
  have hexpand : halfCoreShift scale core * halfCoreShift scale core
      = ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) • (1 : Matrix (Fin dimension) (Fin dimension) ℝ)
        + ((2 : ℝ)⁻¹ * scale + scale * (2 : ℝ)⁻¹) • core + (scale * scale) • (core * core) := by
    simp only [halfCoreShift, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  rw [hexpand, hcore, hscale, smul_smul, halfCoreShift]
  module

theorem halfCoreShift_mulVec {dimension : ℕ} (scale : ℝ)
    (core : Matrix (Fin dimension) (Fin dimension) ℝ) (vec : Fin dimension → ℝ)
    (atomIndex : Fin dimension) :
    (halfCoreShift scale core *ᵥ vec) atomIndex
      = (2 : ℝ)⁻¹ * vec atomIndex + scale * (core *ᵥ vec) atomIndex := by
  rw [halfCoreShift, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]

/-- **THE HALF-SHIFT COMMUTES WITH WHATEVER ITS CORE COMMUTES WITH**, scaled.  This is
the chart-side stationarity field of the window witness, reduced to one integer matrix
identity. -/
theorem halfCoreShift_mul_smul_comm {dimension : ℕ} (scale otherScale : ℝ)
    (core other : Matrix (Fin dimension) (Fin dimension) ℝ)
    (hcommute : core * other = other * core) :
    halfCoreShift scale core * (otherScale • other)
      = (otherScale • other) * halfCoreShift scale core := by
  simp only [halfCoreShift, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, hcommute]
  module

/-! ## The window witness — an exact chart datum strictly inside `[-4/27, 0)`

The class is `{{0,3,5}, {0,4,5}, {1,2,3}, {1,2,4}}`, a four-member covering family in
which every atom has degree two.  It survives the saturated-atom filter and it is a
genuine member of the census. -/

/-- `sqrt 5` squared. -/
theorem sqrt_five_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- `2 < sqrt 5`, which is what makes the window value NEGATIVE. -/
theorem two_lt_sqrt_five : (2 : ℝ) < Real.sqrt 5 := by
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

/-- `sqrt 5 < 9/4`, which is what keeps the window value ABOVE the floor `-4/27` and the
weights strictly positive. -/
theorem sqrt_five_lt_nine_div_four : Real.sqrt 5 < 9 / 4 := by
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

/-- **THE INTEGER CORE OF THE WINDOW CHART**: a symmetric matrix with entries in
`{-1,0,1}`, trace zero, and `B^2 = 5 I`. -/
def windowChartCore : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of ![![-1, -1, 1, 1, 1, 0], ![-1, 0, -1, -1, 1, -1], ![1, -1, 0, -1, 1, 1],
    ![1, -1, -1, 1, 0, -1], ![1, 1, 1, 0, 1, -1], ![0, -1, 1, -1, -1, -1]]

theorem windowChartCore_transpose : windowChartCoreᵀ = windowChartCore := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [windowChartCore]

/-- **`B^2 = 5 I`** — the identity the chart's idempotence rests on. -/
theorem windowChartCore_mul_self :
    windowChartCore * windowChartCore = (5 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, Fin.sum_univ_six]
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [windowChartCore] <;> norm_num

theorem windowChartCore_trace : Matrix.trace windowChartCore = 0 := by
  rw [Matrix.trace, Fin.sum_univ_six]
  simp [windowChartCore, Matrix.diag]

/-- **THE WINDOW CHART** `P = (1/2) I + (sqrt 5/10) B`. -/
noncomputable def windowChartProjection : Matrix (Fin 6) (Fin 6) ℝ :=
  halfCoreShift (Real.sqrt 5 / 10) windowChartCore

theorem windowChartProjection_transpose :
    windowChartProjectionᵀ = windowChartProjection :=
  halfCoreShift_transpose _ _ windowChartCore_transpose

theorem windowChartProjection_mul_self :
    windowChartProjection * windowChartProjection = windowChartProjection :=
  halfCoreShift_mul_self _ _ windowChartCore_mul_self (by
    have hsquare := sqrt_five_sq
    nlinarith [hsquare])

theorem windowChartProjection_trace : Matrix.trace windowChartProjection = 3 := by
  rw [windowChartProjection, halfCoreShift_trace, windowChartCore_trace]
  norm_num

/-- The window weights: `1/6 - sqrt 5/30` at atoms `0,1,2,5` and `1/6 + sqrt 5/15` at
atoms `3` and `4`. -/
noncomputable def windowChartWeight : Fin 6 → ℝ :=
  ![1 / 6 - Real.sqrt 5 / 30, 1 / 6 - Real.sqrt 5 / 30, 1 / 6 - Real.sqrt 5 / 30,
    1 / 6 + Real.sqrt 5 / 15, 1 / 6 + Real.sqrt 5 / 15, 1 / 6 - Real.sqrt 5 / 30]

/-- **THE WINDOW VALUE** `(2 - sqrt 5)/6 = -0.0393446629...`, strictly inside
`[-4/27, 0)`. -/
noncomputable def windowChartValue : ℝ := 1 / 3 - Real.sqrt 5 / 6

theorem windowChartValue_neg : windowChartValue < 0 := by
  rw [windowChartValue]
  linarith [two_lt_sqrt_five]

theorem neg_four_div_twentySeven_lt_windowChartValue : -(4 / 27 : ℝ) < windowChartValue := by
  rw [windowChartValue]
  linarith [sqrt_five_lt_nine_div_four]

/-- **THE WINDOW VALUE IS STRICTLY INSIDE THE CURRENT WINDOW.**  The combined floor at
`(6,3)` is `-4/27`, and `-4/27 < (2 - sqrt 5)/6 < 0`. -/
theorem windowChartValue_mem_flooredWindow :
    combinedValueFloor 6 3 < windowChartValue ∧ windowChartValue < 0 := by
  rw [combinedValueFloor_sixThree]
  exact ⟨neg_four_div_twentySeven_lt_windowChartValue, windowChartValue_neg⟩

/-- The four triples of the window class. -/
def windowChartSubset : Fin 4 → Finset (Fin 6)
  | 0 => {0, 3, 5}
  | 1 => {0, 4, 5}
  | 2 => {1, 2, 3}
  | 3 => {1, 2, 4}

/-- The window class as a family. -/
def windowChartFamily : Finset (Finset (Fin 6)) :=
  {{0, 3, 5}, {0, 4, 5}, {1, 2, 3}, {1, 2, 4}}

/-- The UNNORMALISED tight directions: the four sign patterns, of squared length three
each. -/
def windowChartSign : Fin 4 → Fin 6 → ℝ :=
  ![![-1, 0, 0, 1, 0, 1], ![1, 0, 0, 0, -1, -1], ![0, -1, -1, -1, 0, 0], ![0, 1, 1, 0, -1, 0]]

/-- The tight directions, normalised. -/
noncomputable def windowChartTightDir : Fin 4 → Fin 6 → ℝ :=
  fun blockLabel => (Real.sqrt 3)⁻¹ • windowChartSign blockLabel

/-- The uniform multipliers, one quarter on each of the four triples. -/
noncomputable def windowChartMultiplierWeight : Fin 4 → ℝ := fun _ => (4 : ℝ)⁻¹

/-- The integer core of the assembly, `sum_i s_i s_i^T`, with constant diagonal two
because every atom of the class has degree two. -/
def windowChartMultiplierCore : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of ![![2, 0, 0, -1, -1, -2], ![0, 2, 2, 1, -1, 0], ![0, 2, 2, 1, -1, 0],
    ![-1, 1, 1, 2, 0, 1], ![-1, -1, -1, 0, 2, 1], ![-2, 0, 0, 1, 1, 2]]

/-- **THE INTEGER COMMUTATION** `B Xi' = Xi' B`, which is the whole content of the
chart-side stationarity field at this witness. -/
theorem windowChartCore_mul_multiplierCore_comm :
    windowChartCore * windowChartMultiplierCore
      = windowChartMultiplierCore * windowChartCore := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_six]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [windowChartCore, windowChartMultiplierCore] <;> norm_num

/-- **THE LEVELS** the integer core acts by on the sign patterns inside their own
triples: `-2` at the four atoms of weight `1/6 - sqrt 5/30`, `-1` at atoms `3` and
`4`. -/
def windowChartLevel : Fin 6 → ℝ := ![-2, -2, -2, -1, -1, -2]

/-- **THE INTEGER EIGEN-RELATION.**  Inside its own triple, the integer core sends a
sign pattern to the level times itself. -/
theorem windowChartCore_mulVec_sign (blockLabel : Fin 4) (atomIndex : Fin 6)
    (hmem : atomIndex ∈ windowChartSubset blockLabel) :
    (windowChartCore *ᵥ windowChartSign blockLabel) atomIndex
      = windowChartLevel atomIndex * windowChartSign blockLabel atomIndex := by
  revert hmem
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  fin_cases blockLabel <;> fin_cases atomIndex <;>
    simp [windowChartSubset, windowChartCore, windowChartSign, windowChartLevel, Fin.ext_iff] <;>
    norm_num

/-- **THE WEIGHT-LEVEL IDENTITY**: at every atom, `1/2 + (sqrt 5/10) * level - weight` is
the window value.  Two lines of `Q(sqrt 5)` arithmetic, and the reason the chart's
integer eigen-relation is exactly tightness. -/
theorem windowChartWeight_level_eq_value (atomIndex : Fin 6) :
    (2 : ℝ)⁻¹ + Real.sqrt 5 / 10 * windowChartLevel atomIndex - windowChartWeight atomIndex
      = windowChartValue := by
  fin_cases atomIndex <;>
    simp [windowChartLevel, windowChartWeight, windowChartValue] <;> ring

/-- The gap of the window chart, applied to a vector. -/
theorem windowChartGap_mulVec (vec : Fin 6 → ℝ) (atomIndex : Fin 6) :
    (chartStationaryGap windowChartProjection windowChartWeight *ᵥ vec) atomIndex
      = (2 : ℝ)⁻¹ * vec atomIndex + Real.sqrt 5 / 10 * (windowChartCore *ᵥ vec) atomIndex
        - windowChartWeight atomIndex * vec atomIndex := by
  rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply, windowChartProjection,
    halfCoreShift_mulVec, Matrix.mulVec_diagonal]

/-- **TIGHTNESS ON THE SIGN PATTERNS**: the gap sends each sign pattern to the window
value times itself, at every atom of its own triple. -/
theorem windowChartGap_mulVec_sign (blockLabel : Fin 4) (atomIndex : Fin 6)
    (hmem : atomIndex ∈ windowChartSubset blockLabel) :
    (chartStationaryGap windowChartProjection windowChartWeight
        *ᵥ windowChartSign blockLabel) atomIndex
      = windowChartValue * windowChartSign blockLabel atomIndex := by
  rw [windowChartGap_mulVec, windowChartCore_mulVec_sign blockLabel atomIndex hmem]
  linear_combination
    (windowChartSign blockLabel atomIndex) * windowChartWeight_level_eq_value atomIndex

/-- The assembly of the four normalised sign patterns at multiplier `1/4` is `1/12` times
the integer core. -/
theorem windowChartMultiplierAssembly_eq :
    chartMultiplierAssembly (Finset.univ : Finset (Fin 4)) windowChartMultiplierWeight
        windowChartTightDir
      = (12 : ℝ)⁻¹ • windowChartMultiplierCore := by
  have hscale : ∀ blockLabel : Fin 4,
      windowChartMultiplierWeight blockLabel • atomMatrix (windowChartTightDir blockLabel)
        = (12 : ℝ)⁻¹ • atomMatrix (windowChartSign blockLabel) := by
    intro blockLabel
    rw [windowChartTightDir, atomMatrix_smul, inv_pow, sqrt_three_sq, smul_smul,
      windowChartMultiplierWeight]
    norm_num
  rw [chartMultiplierAssembly, Finset.sum_congr rfl fun blockLabel _ => hscale blockLabel]
  ext rowIndex colIndex
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply,
    Fin.sum_univ_four]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [windowChartSign, windowChartMultiplierCore] <;> norm_num

/-- **THE WINDOW DATUM.**  Rank three, six atoms, the four-member class
`{{0,3,5},{0,4,5},{1,2,3},{1,2,4}}`, and `value = (2 - sqrt 5)/6` strictly inside
`[-4/27, 0)`. -/
theorem windowChartProjection_isChartStationaryData :
    IsChartStationaryData 3 windowChartProjection windowChartWeight windowChartValue
      (Finset.univ : Finset (Fin 4)) windowChartSubset windowChartMultiplierWeight
      windowChartTightDir where
  isSymmetric := windowChartProjection_transpose
  isIdempotent := windowChartProjection_mul_self
  hasTraceRank := by
    rw [windowChartProjection_trace]
    norm_num
  weight_pos := by
    intro atomIndex
    have hbound := sqrt_five_lt_nine_div_four
    have hnonneg := Real.sqrt_nonneg 5
    fin_cases atomIndex <;> simp [windowChartWeight] <;> linarith
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    simp [windowChartWeight]
    ring
  activeWeight_nonneg := by intro blockLabel _; norm_num [windowChartMultiplierWeight]
  activeWeight_sum_one := by norm_num [windowChartMultiplierWeight, Fin.sum_univ_four]
  activeSubset_card := by intro blockLabel _; fin_cases blockLabel <;> decide
  tightDir_unit := by
    intro blockLabel _
    have hinvRoot : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = (3 : ℝ)⁻¹ := by
      rw [← mul_inv, ← pow_two, sqrt_three_sq]
    have hlength : windowChartSign blockLabel ⬝ᵥ windowChartSign blockLabel = 3 := by
      simp only [dotProduct, Fin.sum_univ_six]
      fin_cases blockLabel <;> simp [windowChartSign] <;> norm_num
    rw [windowChartTightDir, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hinvRoot, hlength]
    norm_num
  tightDir_support := by
    intro blockLabel _ atomIndex hnotMem
    have hsign : windowChartSign blockLabel atomIndex = 0 := by
      revert hnotMem
      fin_cases blockLabel <;> fin_cases atomIndex <;>
        simp [windowChartSubset, windowChartSign, Fin.ext_iff]
    rw [windowChartTightDir, Pi.smul_apply, hsign, smul_zero]
  tightDir_isTight := by
    intro blockLabel _ atomIndex hmem
    rw [windowChartTightDir, Matrix.mulVec_smul, Pi.smul_apply,
      windowChartGap_mulVec_sign blockLabel atomIndex hmem, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  assembly_diagonal := by
    intro atomIndex
    rw [windowChartMultiplierAssembly_eq, Matrix.smul_apply, smul_eq_mul]
    fin_cases atomIndex <;> simp [windowChartMultiplierCore] <;> norm_num
  assembly_commutes := by
    rw [windowChartMultiplierAssembly_eq, windowChartProjection]
    exact halfCoreShift_mul_smul_comm _ _ _ _ windowChartCore_mul_multiplierCore_comm

/-- The window datum's active family is the window class. -/
theorem windowChart_isActiveFamily :
    IsActiveFamily (Finset.univ : Finset (Fin 4)) windowChartSubset windowChartFamily := by
  unfold IsActiveFamily windowChartSubset windowChartFamily
  decide

/-- The window datum is on the rank-one branch: its four labels carry four distinct
triples. -/
theorem windowChart_hasSimpleActiveSubsets :
    HasSimpleActiveSubsets (Finset.univ : Finset (Fin 4)) windowChartSubset := by
  unfold HasSimpleActiveSubsets windowChartSubset
  decide

/-- The window class survives the saturated-atom filter, so it is a genuine census
member and not one the shipped combinatorial exclusion already kills. -/
theorem not_hasSaturatedAtom_windowChartFamily : ¬ HasSaturatedAtom windowChartFamily := by
  unfold HasSaturatedAtom windowChartFamily
  decide

/-- Every atom of the window class has degree TWO, so by
`forall_activeFamilyDegree_eq_one_iff_card_eq_two` it is not the two-member class in
disguise. -/
theorem windowChartFamily_activeFamilyDegree_eq_two (atomIndex : Fin 6) :
    activeFamilyDegree windowChartFamily atomIndex = 2 := by
  revert atomIndex
  unfold activeFamilyDegree windowChartFamily
  decide

/-! ## The window datum is inadmissible, and why that is the point -/

/-- The gap's quadratic form on a probe supported inside the triple `{1,3,4}`. -/
theorem windowChartQuadraticForm (probe : Fin 6 → ℝ) (hzeroFirst : probe 0 = 0)
    (hzeroThird : probe 2 = 0) (hzeroLast : probe 5 = 0) :
    probe ⬝ᵥ (chartStationaryGap windowChartProjection windowChartWeight *ᵥ probe)
      = (1 / 3 + Real.sqrt 5 / 30) * (probe 1 ^ 2 + probe 3 ^ 2 + probe 4 ^ 2)
        - 2 * (Real.sqrt 5 / 10) * (probe 1 * probe 3)
        + 2 * (Real.sqrt 5 / 10) * (probe 1 * probe 4) := by
  simp only [dotProduct, Fin.sum_univ_six]
  simp only [windowChartGap_mulVec]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  rw [hzeroFirst, hzeroThird, hzeroLast]
  simp [windowChartCore, windowChartWeight]
  ring

/-- **THE WINDOW DATUM IS INADMISSIBLE.**  On the triple `{1,3,4}` the gap's quadratic
form is

    `Q(x) = a (x_1^2 + x_3^2 + x_4^2) - 2 b x_1 x_3 + 2 b x_1 x_4` ,
    `a = 1/3 + sqrt 5/30` ,   `b = sqrt 5/10` ,

and `a Q(x) = (a x_1 - b(x_3 - x_4))^2 + (a^2 - 2 b^2)(x_3^2 + x_4^2) + b^2 (x_3 + x_4)^2`
with `a > 0` and `a^2 - 2 b^2 = 1/60 + sqrt 5/45 > 0`.  So `Q >= 0` on that triple and no
probe supported there reaches the negative window value.

THIS IS WHY THE WITNESS CONTRADICTS NOTHING SHIPPED — every value floor in the repository
carries `Gtz.IsChartArgmaxValue` — and it is also exactly why it is fatal to the
elimination route, which cannot see admissibility at all. -/
theorem not_windowChartProjection_isChartArgmaxValue :
    ¬ IsChartArgmaxValue 3 windowChartProjection windowChartWeight windowChartValue := by
  intro hargmax
  obtain ⟨probe, hunit, hsupport, hquotient⟩ := hargmax ({1, 3, 4} : Finset (Fin 6)) (by decide)
  have hzeroFirst : probe 0 = 0 := hsupport 0 (by decide)
  have hzeroThird : probe 2 = 0 := hsupport 2 (by decide)
  have hzeroLast : probe 5 = 0 := hsupport 5 (by decide)
  have hdiagonalPos : (0 : ℝ) < 1 / 3 + Real.sqrt 5 / 30 := by
    linarith [Real.sqrt_nonneg 5]
  have hgapPos : (0 : ℝ) < (1 / 3 + Real.sqrt 5 / 30) ^ 2 - 2 * (Real.sqrt 5 / 10) ^ 2 := by
    have hexpand : (1 / 3 + Real.sqrt 5 / 30) ^ 2 - 2 * (Real.sqrt 5 / 10) ^ 2
        = 1 / 60 + Real.sqrt 5 / 45 := by
      linear_combination (-17 / 900 : ℝ) * sqrt_five_sq
    rw [hexpand]
    linarith [Real.sqrt_nonneg 5]
  have hcompleted : (1 / 3 + Real.sqrt 5 / 30)
      * ((1 / 3 + Real.sqrt 5 / 30) * (probe 1 ^ 2 + probe 3 ^ 2 + probe 4 ^ 2)
        - 2 * (Real.sqrt 5 / 10) * (probe 1 * probe 3)
        + 2 * (Real.sqrt 5 / 10) * (probe 1 * probe 4))
      = ((1 / 3 + Real.sqrt 5 / 30) * probe 1
            - (Real.sqrt 5 / 10) * (probe 3 - probe 4)) ^ 2
        + ((1 / 3 + Real.sqrt 5 / 30) ^ 2 - 2 * (Real.sqrt 5 / 10) ^ 2)
            * (probe 3 ^ 2 + probe 4 ^ 2)
        + (Real.sqrt 5 / 10) ^ 2 * (probe 3 + probe 4) ^ 2 := by ring
  have hformNonneg : (0 : ℝ)
      ≤ (1 / 3 + Real.sqrt 5 / 30) * (probe 1 ^ 2 + probe 3 ^ 2 + probe 4 ^ 2)
        - 2 * (Real.sqrt 5 / 10) * (probe 1 * probe 3)
        + 2 * (Real.sqrt 5 / 10) * (probe 1 * probe 4) := by
    nlinarith [hcompleted, hdiagonalPos, hgapPos,
      sq_nonneg ((1 / 3 + Real.sqrt 5 / 30) * probe 1 - (Real.sqrt 5 / 10) * (probe 3 - probe 4)),
      mul_nonneg (le_of_lt hgapPos) (add_nonneg (sq_nonneg (probe 3)) (sq_nonneg (probe 4))),
      mul_nonneg (sq_nonneg (Real.sqrt 5 / 10)) (sq_nonneg (probe 3 + probe 4))]
  rw [windowChartQuadraticForm probe hzeroFirst hzeroThird hzeroLast] at hquotient
  linarith [windowChartValue_neg]

/-! ## The route cannot be finished -/

/-- **THE WINDOW CLASS ADMITS NO WINDOW-ROOT-FREE ELIMINANT.**  For ANY real function
`valuePolynomial`, if it satisfies the elimination hypothesis at the window class — that
a rank-one-branch chart stationarity datum on that class at a negative value is a root of
it — then it VANISHES at `(2 - sqrt 5)/6`, which lies strictly inside `[-4/27, 0)`.

The instantiation is the witness itself.  Nothing about the function is assumed: degree,
rationality and provenance are all irrelevant, because the obstruction is a point of the
variety and not a property of the generator. -/
theorem eq_zero_at_windowChartValue_of_eliminatesWindowChartFamilyValue
    (valuePolynomial : ℝ → ℝ)
    (heliminates : ∀ (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ) (value : ℝ)
      (activeSet : Finset (Fin 4)) (activeSubset : Fin 4 → Finset (Fin 6))
      (activeWeight : Fin 4 → ℝ) (tightDir : Fin 4 → (Fin 6 → ℝ)),
      IsChartStationaryData 3 projection weight value activeSet activeSubset activeWeight
          tightDir →
        IsActiveFamily activeSet activeSubset windowChartFamily →
          HasSimpleActiveSubsets activeSet activeSubset →
            value < 0 → valuePolynomial value = 0) :
    valuePolynomial windowChartValue = 0 :=
  heliminates windowChartProjection windowChartWeight windowChartValue Finset.univ
    windowChartSubset windowChartMultiplierWeight windowChartTightDir
    windowChartProjection_isChartStationaryData windowChart_isActiveFamily
    windowChart_hasSimpleActiveSubsets windowChartValue_neg

/-- **THE ELIMINATION ROUTE PROVABLY DOES NOT FINISH.**  There is NO real function that is
both an eliminant for the window class and nonvanishing on the floored window.  So the
certificate shape that closed the two-block class and the two three-member classes is
UNAVAILABLE at that class, at any cost, for any generator, and by a reason no amount of
computation removes.

The class is a genuine census member: four triples, covering, every atom of degree two,
and not saturated. -/
theorem not_exists_windowRootFree_eliminatesWindowChartFamilyValue :
    ¬ ∃ valuePolynomial : ℝ → ℝ,
      (∀ (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ) (value : ℝ)
        (activeSet : Finset (Fin 4)) (activeSubset : Fin 4 → Finset (Fin 6))
        (activeWeight : Fin 4 → ℝ) (tightDir : Fin 4 → (Fin 6 → ℝ)),
        IsChartStationaryData 3 projection weight value activeSet activeSubset activeWeight
            tightDir →
          IsActiveFamily activeSet activeSubset windowChartFamily →
            HasSimpleActiveSubsets activeSet activeSubset →
              value < 0 → valuePolynomial value = 0) ∧
      ∀ value : ℝ, combinedValueFloor 6 3 ≤ value → value < 0 → valuePolynomial value ≠ 0 := by
  rintro ⟨valuePolynomial, heliminates, hrootFree⟩
  exact hrootFree windowChartValue (le_of_lt windowChartValue_mem_flooredWindow.1)
    windowChartValue_mem_flooredWindow.2
    (eq_zero_at_windowChartValue_of_eliminatesWindowChartFamilyValue valuePolynomial heliminates)

/-- **THE SIXTHS ARE NOT A LAW.**  There is a `(6,3)` chart stationarity datum on a
census-surviving class whose value lies strictly inside the floored window — so no
argument may assume that the elimination ideal of every class has its roots in
`(1/6) Z`.  This is the statement that kills the pattern the first five eliminants
suggested. -/
theorem exists_isChartStationaryData_value_mem_flooredWindow :
    ∃ (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ) (value : ℝ)
      (activeSubset : Fin 4 → Finset (Fin 6)) (activeWeight : Fin 4 → ℝ)
      (tightDir : Fin 4 → (Fin 6 → ℝ)),
      IsChartStationaryData 3 projection weight value (Finset.univ : Finset (Fin 4))
          activeSubset activeWeight tightDir ∧
        IsActiveFamily (Finset.univ : Finset (Fin 4)) activeSubset windowChartFamily ∧
          HasSimpleActiveSubsets (Finset.univ : Finset (Fin 4)) activeSubset ∧
            combinedValueFloor 6 3 < value ∧ value < 0 :=
  ⟨windowChartProjection, windowChartWeight, windowChartValue, windowChartSubset,
    windowChartMultiplierWeight, windowChartTightDir,
    windowChartProjection_isChartStationaryData, windowChart_isActiveFamily,
    windowChart_hasSimpleActiveSubsets, windowChartValue_mem_flooredWindow.1,
    windowChartValue_mem_flooredWindow.2⟩

end Gtz
