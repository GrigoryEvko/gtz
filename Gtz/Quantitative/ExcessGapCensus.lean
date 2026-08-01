/-
# The excess-gap census at the `(6,3)` crux

`Gtz.excessGap D a b c = u_a u_b u_c − (u_c p_ab² + u_b p_ac² + u_a p_bc²)` is the
SIGN-BLIND half of `Gtz.discriminantTie`: it reads only the three heavy excesses and
the three SQUARED pairings, never an orientation.  The **census** of a design is the
number of its triples whose sign-blind gap is nonnegative, collected here as
`Gtz.censusTripleSets`.

## THE CENSUS HAS NO POSITIVE FLOOR, AND THAT IS A THEOREM HERE

This file was written to land a lower bound `N₀ ≥ 1` on the census of a crux.  **NO
SUCH BOUND EXISTS**, and the obstruction is structural rather than a gap in the
search.  `Gtz.censusTripleSets_icosaDesign_eq_empty` proves the census of
`Gtz.icosaDesign` is EMPTY — every one of its twenty triples has gap exactly `−14/5`
(`Gtz.icosaDesign_excessGap`) — while `Gtz.icosaDesign_allHeavy` and
`Gtz.icosaDesign_hasNoParallelPair` give it two of the crux's sign-blind fields
outright.  Since `excessGap` reads only sign-blind data, no hypothesis expressible in
that data can force a census triple to exist.

Two further facts, MEASURED OUTSIDE LEAN and quoted so no successor re-runs the
search (exact arithmetic, /tmp/gtz-x/x3-census/perturb.out and abstract_class15.out):

* the icosahedral LINES with weights moved off uniform keep census zero on an OPEN
  ball — the census leaves zero exactly at `delta* = sqrt 15/10 − 1/3 =
  0.05396500128740835518459…`, and the fully generic weight vector
  `(3/20, 4/25, 17/100, 9/50, 7/50, 1/5)` gives leverages `(10/3, 25/8, 50/17, 25/9,
  25/7, 5/2)`, census `0`, and satisfies all-heaviness, co-singleton strictness,
  no-parallel-pair AND non-equal-share simultaneously.  So
  `Gtz.SixThreeCrux.avoidsEqualShareStratum` does not rescue the bound either;
* nor does `Gtz.SixThreeCrux.hasNoDominatingTriple`: the icosahedron's sign-blind data
  taken verbatim with the sign pattern of the two-graph `Delta(K5)` satisfies the row
  law, all-heaviness, co-singleton strictness, no-parallel-pair and non-domination at
  every triple, still at census zero.  That configuration is refuted only by rank-three
  realizability of its SIGN pattern.

**CONSEQUENCE FOR THE LADDER.**  A census floor is available only to an argument that
consumes the two-graph realizability layer.  A sector table keyed on the census
therefore runs at threshold `T = 0` and gains nothing.

## WHAT IS PROVED HERE INSTEAD

1. **The set-level invariance** `Gtz.tripleParity_congr_of_eq_triple` and
   `Gtz.excessGap_congr_of_eq_triple`: both scalars are functions of the three-element
   SET, not of an ordering.  Twenty-seven membership branches, all closed by one
   rewrite — orient every edge to the fixed representative of its unordered pair, then
   `ring`.  These are the bricks `Gtz.coherentTripleSets` was stated existentially to
   avoid.
2. **The quarter window** `Gtz.SixThreeCrux.excessGap_lt_quarter_mul_heavyExcess_prod`:
   at a crux `excessGap < u_a u_b u_c / 4` at EVERY triple, no hypothesis.  Writing
   `q_cd := p_cd²/(u_c u_d)` this says `q_ab + q_ac + q_bc > 3/4` everywhere, so the
   twenty triangles all sit above the tetrahedral threshold and the census triples are
   pinned into the thin shell `(3/4, 1]`.  SHARP: the chain closes with equality
   throughout at `q = 1/4` on all three edges, which is exactly the split-tetrahedron
   tie (`u = 2`, `p² = 1`, gap `2 = u³/4`, tie `0`).
3. **The census ceiling** `Gtz.SixThreeCrux.card_censusTripleSets_le_sixteen` and its
   per-atom form: at most sixteen of the twenty triples, at most eight of the ten
   through any atom.  The missing four are the coherent floor, and coherence forces a
   strictly negative gap.
4. **The two-sided sign band** — the upper half is new.  For ANY `(6,3)` design with
   nonvanishing pairings the coherent triples number between four and sixteen, and
   between two and eight through every atom.  The lower halves are the shipped
   `Gtz.four_le_card_coherentTripleSets_sixThree`; the upper halves come from running
   them on the ANTI-PARITY PARTNER `Gtz.exists_antiParityPartner_sixThree`, whose
   coherent triples are exactly this design's incoherent ones.
5. **The dual census** `Gtz.censusTripleSets_subset_coherentTripleSets_chartDual`: a
   census triple of a crux is COHERENT in the chart dual.
6. **The D6 cap** `Gtz.SixThreeCrux.not_posSemidef_coSingleton_sub_five`, UNCONDITIONAL:
   no co-singleton of a crux reaches five times the identity.  Its input
   `Gtz.IsCoSingletonSpreadLemma` is discharged here by whitening the co-singleton scaled
   by the uniform weight `1/5` — positive definite, so `Gtz.exists_congruence_to_one`
   supplies the congruence and no square root appears — re-indexing the five surviving
   atoms and reading them as a `Gtz.WeightedDesign 5 3`, where
   `Gtz.gtzWeighted_corank_two 3` applies.  With the crux field
   `hasStrictlyDominatingCoSingletons` this is the two-sided window
   `Gtz.SixThreeCrux.coSingletonWindow`, whose upper end is ATTAINED at the `(6,3)`
   diamond ties (exactly `5` at two of their six atoms) and so is not slack.

## TIGHTNESS, MEASURED (exact; /tmp/gtz-x/x3-census/census.py)

Census of the reference designs, out of twenty triples at `(6,3)` and thirty-five at
`(7,3)`: split tetrahedron `(6,3)` `12` at each of the three splits; diamond `(6,3)`
spine split `4` and rim split `7`; icosahedron `0`; regular tetrahedron `(4,3)` `4` of
`4`; diamond `(5,3)` `4` of `10`; split seven `20` of `35`; diamond seven `7` of `35`.
The census is therefore NOT a tie invariant — it varies by a factor of three across
the `(6,3)` tie stratum.  The minimum of `sigma` is exactly `3/4` at every tetrahedral
tie (the equality case of the quarter window), `67/81` at every diamond, and `27/20`
at the icosahedron.

## WHAT THIS FILE DOES NOT CLOSE

NO CENSUS FLOOR, at any threshold, and the icosahedral theorem below says none is
available from sign-blind data.  NO EXCLUSION of any two-graph class: the band `[2,8]`
is SHARP at both ends and leaves twelve of the sixteen isomorphism classes standing.
NOTHING about `IsEmpty` for either crux.  AND THE CO-SINGLETON WINDOW EXCLUDES NOTHING BY
ITSELF: `(1, 5)` is a two-sided constraint on each of the six co-singletons separately,
consistent with every weight vector a crux could carry.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.Reductions
import Gtz.Reduction.NaimarkLeverage
import Gtz.Reduction.SplitTransfer
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.GoodTripleGraph
import Gtz.Quantitative.SwitchingTwoGraph
import Gtz.Quantitative.SevenThreeSyzygy
import Gtz.Quantitative.SixThreeCrux
import Gtz.Quantitative.SixThreeCruxSigns
import Gtz.Quantitative.CoherentCountFloor
import Gtz.Quantitative.ChartDuality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The two sign-blind triple scalars are functions of the SET -/

/-- **THE PARITY IS A FUNCTION OF THE THREE-ELEMENT SET.**  Two orderings of the same
three atoms carry the same `Gtz.tripleParity`.  Each of the twenty-seven membership
branches closes from one rewrite: orient every `Gtz.edgeSign` to the fixed
representative of its unordered pair, then `ring`.  The left-hand distinctness is NOT
needed — it follows from the right-hand distinctness through the set equality. -/
theorem tripleParity_congr_of_eq_triple (design : WeightedDesign m 3)
    {firstLeft secondLeft thirdLeft firstRight secondRight thirdRight : Fin m}
    (hrightOne : firstRight ≠ secondRight) (hrightTwo : firstRight ≠ thirdRight)
    (hrightThree : secondRight ≠ thirdRight)
    (hsame : ({firstLeft, secondLeft, thirdLeft} : Finset (Fin m))
      = {firstRight, secondRight, thirdRight}) :
    tripleParity design firstRight secondRight thirdRight
      = tripleParity design firstLeft secondLeft thirdLeft := by
  classical
  have hfirstMem : firstRight = firstLeft ∨ firstRight = secondLeft
      ∨ firstRight = thirdLeft := by
    have hmem : firstRight ∈ ({firstLeft, secondLeft, thirdLeft} : Finset (Fin m)) := by
      rw [hsame]; simp
    simpa using hmem
  have hsecondMem : secondRight = firstLeft ∨ secondRight = secondLeft
      ∨ secondRight = thirdLeft := by
    have hmem : secondRight ∈ ({firstLeft, secondLeft, thirdLeft} : Finset (Fin m)) := by
      rw [hsame]; simp
    simpa using hmem
  have hthirdMem : thirdRight = firstLeft ∨ thirdRight = secondLeft
      ∨ thirdRight = thirdLeft := by
    have hmem : thirdRight ∈ ({firstLeft, secondLeft, thirdLeft} : Finset (Fin m)) := by
      rw [hsame]; simp
    simpa using hmem
  rcases hfirstMem with hfirst | hfirst | hfirst <;>
    rcases hsecondMem with hsecond | hsecond | hsecond <;>
      rcases hthirdMem with hthird | hthird | hthird <;>
        first
          | exact absurd (hfirst.trans hsecond.symm) hrightOne
          | exact absurd (hfirst.trans hthird.symm) hrightTwo
          | exact absurd (hsecond.trans hthird.symm) hrightThree
          | (rw [hfirst, hsecond, hthird] <;>
             (simp only [tripleParity, edgeSign_comm design secondLeft firstLeft,
               edgeSign_comm design thirdLeft firstLeft,
               edgeSign_comm design thirdLeft secondLeft];
              ring))

/-- **THE SIGN-BLIND GAP IS A FUNCTION OF THE THREE-ELEMENT SET.**  The same bash with
`Gtz.atomPairing` oriented in place of `Gtz.edgeSign`. -/
theorem excessGap_congr_of_eq_triple (design : WeightedDesign m 3)
    {firstLeft secondLeft thirdLeft firstRight secondRight thirdRight : Fin m}
    (hrightOne : firstRight ≠ secondRight) (hrightTwo : firstRight ≠ thirdRight)
    (hrightThree : secondRight ≠ thirdRight)
    (hsame : ({firstLeft, secondLeft, thirdLeft} : Finset (Fin m))
      = {firstRight, secondRight, thirdRight}) :
    excessGap design firstRight secondRight thirdRight
      = excessGap design firstLeft secondLeft thirdLeft := by
  classical
  have hfirstMem : firstRight = firstLeft ∨ firstRight = secondLeft
      ∨ firstRight = thirdLeft := by
    have hmem : firstRight ∈ ({firstLeft, secondLeft, thirdLeft} : Finset (Fin m)) := by
      rw [hsame]; simp
    simpa using hmem
  have hsecondMem : secondRight = firstLeft ∨ secondRight = secondLeft
      ∨ secondRight = thirdLeft := by
    have hmem : secondRight ∈ ({firstLeft, secondLeft, thirdLeft} : Finset (Fin m)) := by
      rw [hsame]; simp
    simpa using hmem
  have hthirdMem : thirdRight = firstLeft ∨ thirdRight = secondLeft
      ∨ thirdRight = thirdLeft := by
    have hmem : thirdRight ∈ ({firstLeft, secondLeft, thirdLeft} : Finset (Fin m)) := by
      rw [hsame]; simp
    simpa using hmem
  rcases hfirstMem with hfirst | hfirst | hfirst <;>
    rcases hsecondMem with hsecond | hsecond | hsecond <;>
      rcases hthirdMem with hthird | hthird | hthird <;>
        first
          | exact absurd (hfirst.trans hsecond.symm) hrightOne
          | exact absurd (hfirst.trans hthird.symm) hrightTwo
          | exact absurd (hsecond.trans hthird.symm) hrightThree
          | (rw [hfirst, hsecond, hthird] <;>
             (simp only [excessGap, atomPairing_comm design secondLeft firstLeft,
               atomPairing_comm design thirdLeft firstLeft,
               atomPairing_comm design thirdLeft secondLeft];
              ring))

/-! ## 2. The census set -/

/-- The **census triples**: the three-element subsets carrying an ordering whose
sign-blind gap is nonnegative.  Stated with an existential ordering to match the
shipped `Gtz.coherentTripleSets`; by `Gtz.excessGap_congr_of_eq_triple` the choice of
ordering is immaterial. -/
noncomputable def censusTripleSets (design : WeightedDesign m 3) : Finset (Finset (Fin m)) :=
  @Finset.filter _ (fun selected => ∃ first second third : Fin m,
      selected = {first, second, third} ∧ first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 ≤ excessGap design first second third) (Classical.decPred _) Finset.univ

theorem mem_censusTripleSets_iff (design : WeightedDesign m 3) (selected : Finset (Fin m)) :
    selected ∈ censusTripleSets design ↔ ∃ first second third : Fin m,
      selected = {first, second, third} ∧ first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 ≤ excessGap design first second third := by
  classical
  simp only [censusTripleSets, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_eq_three_of_mem_censusTripleSets (design : WeightedDesign m 3)
    {selected : Finset (Fin m)} (hmem : selected ∈ censusTripleSets design) :
    selected.card = 3 := by
  obtain ⟨first, second, third, hset, hone, htwo, hthree, _⟩ :=
    (mem_censusTripleSets_iff design selected).mp hmem
  rw [hset]
  exact card_triple_eq_three hone htwo hthree

theorem card_eq_three_of_mem_coherentTripleSets (design : WeightedDesign m 3)
    {selected : Finset (Fin m)} (hmem : selected ∈ coherentTripleSets design) :
    selected.card = 3 := by
  obtain ⟨first, second, third, hset, hone, htwo, hthree, _⟩ :=
    (mem_coherentTripleSets_iff design selected).mp hmem
  rw [hset]
  exact card_triple_eq_three hone htwo hthree

/-! ## 3. The quarter window -/

/-- **The pairing product against the sign-blind gap at a general all-heavy triple.**
`27 (u_a u_b u_c) (p_ab p_ac p_bc)² ≤ (u_a u_b u_c − excessGap)³`, by three-variable
AM-GM on `(u_c p_ab², u_b p_ac², u_a p_bc²)` — whose sum is exactly the subtracted
term.  No crux hypothesis. -/
theorem twentySeven_mul_heavyExcess_prod_mul_sq_atomPairingProduct_le
    (design : WeightedDesign m 3) (hheavy : AllHeavy design) (first second third : Fin m) :
    27 * ((heavyExcess design first * heavyExcess design second * heavyExcess design third)
        * (atomPairing design first second * atomPairing design first third
            * atomPairing design second third) ^ 2)
      ≤ (heavyExcess design first * heavyExcess design second * heavyExcess design third
          - excessGap design first second third) ^ 3 := by
  have hfirst : 0 < heavyExcess design first := by
    rw [heavyExcess]; linarith [hheavy first]
  have hsecond : 0 < heavyExcess design second := by
    rw [heavyExcess]; linarith [hheavy second]
  have hthird : 0 < heavyExcess design third := by
    rw [heavyExcess]; linarith [hheavy third]
  have hamgm := twentySeven_mul_prod_le_cube_sum
    (firstValue := heavyExcess design third * atomPairing design first second ^ 2)
    (secondValue := heavyExcess design second * atomPairing design first third ^ 2)
    (thirdValue := heavyExcess design first * atomPairing design second third ^ 2)
    (by positivity) (by positivity) (by positivity)
  rw [excessGap]
  nlinarith [hamgm, hfirst.le, hsecond.le, hthird.le]

namespace SixThreeCrux

/-- **THE QUARTER WINDOW.**  At a `(6,3)` crux every triple has its sign-blind gap
strictly below a quarter of the product of its three heavy excesses.  Equivalently
`q_ab + q_ac + q_bc > 3/4` with `q_cd = p_cd²/(u_c u_d)`.

The chain: the substrate squeeze gives `E < 2|p_ab p_ac p_bc|`, AM-GM gives
`27 G (ppp)² ≤ (G − E)³`, and `E ≥ G/4` makes the two sides collide at `27G³/16`.
Equality throughout at `q = 1/4` on every edge, i.e. the tetrahedral tie. -/
theorem excessGap_lt_quarter_mul_heavyExcess_prod (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    excessGap crux.design first second third
      < heavyExcess crux.design first * heavyExcess crux.design second
          * heavyExcess crux.design third / 4 := by
  have hfirst : 0 < heavyExcess crux.design first := by
    rw [heavyExcess]; linarith [crux.isAllHeavy first]
  have hsecond : 0 < heavyExcess crux.design second := by
    rw [heavyExcess]; linarith [crux.isAllHeavy second]
  have hthird : 0 < heavyExcess crux.design third := by
    rw [heavyExcess]; linarith [crux.isAllHeavy third]
  rcases lt_or_ge (excessGap crux.design first second third) 0 with hgap | hgap
  · have : 0 < heavyExcess crux.design first * heavyExcess crux.design second
        * heavyExcess crux.design third / 4 := by positivity
    linarith
  · by_contra hcontra
    push Not at hcontra
    have hbound := excessGap_lt_two_mul_abs_atomPairingProduct crux hfirstSecond
      hfirstThird hsecondThird
    have hsquare : excessGap crux.design first second third ^ 2
        < 4 * (atomPairing crux.design first second * atomPairing crux.design first third
            * atomPairing crux.design second third) ^ 2 := by
      have habs : |atomPairing crux.design first second * atomPairing crux.design first third
          * atomPairing crux.design second third| ^ 2
          = (atomPairing crux.design first second * atomPairing crux.design first third
              * atomPairing crux.design second third) ^ 2 := sq_abs _
      nlinarith [hbound, hgap, abs_nonneg (atomPairing crux.design first second
        * atomPairing crux.design first third * atomPairing crux.design second third)]
    have hamgm := twentySeven_mul_heavyExcess_prod_mul_sq_atomPairingProduct_le
      crux.design crux.isAllHeavy first second third
    set product := heavyExcess crux.design first * heavyExcess crux.design second
      * heavyExcess crux.design third with hproduct
    set gap := excessGap crux.design first second third with hgapDef
    have hproductPos : 0 < product := by rw [hproduct]; positivity
    have hstrict : 27 * product * gap ^ 2 / 4 < (product - gap) ^ 3 := by
      nlinarith [hamgm, mul_pos hproductPos (by linarith [hsquare] :
        (0:ℝ) < 4 * (atomPairing crux.design first second
            * atomPairing crux.design first third
            * atomPairing crux.design second third) ^ 2 - gap ^ 2)]
    have hcubeLe : (product - gap) ^ 3 ≤ (3 * product / 4) ^ 3 :=
      (Odd.strictMono_pow (by decide : Odd 3)).monotone (by linarith)
    have hcubeForm : (3 * product / 4) ^ 3 = 27 * product ^ 3 / 64 := by ring
    have hsquareLower : product ^ 2 / 16 ≤ gap ^ 2 := by nlinarith [hcontra, hgap, hproductPos]
    have hscaled : 27 * product ^ 3 / 64 ≤ 27 * product * gap ^ 2 / 4 := by
      nlinarith [mul_le_mul_of_nonneg_left hsquareLower hproductPos.le]
    linarith [hstrict, hcubeLe, hcubeForm, hscaled]

/-- The window cleared of its denominator: the tetrahedral value `q = 1/4` on every
edge is unattainable at a crux. -/
theorem four_mul_excessGap_lt_heavyExcess_prod (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    4 * excessGap crux.design first second third
      < heavyExcess crux.design first * heavyExcess crux.design second
          * heavyExcess crux.design third := by
  have hwindow := excessGap_lt_quarter_mul_heavyExcess_prod crux hfirstSecond
    hfirstThird hsecondThird
  linarith

/-- **THE PAIRING FORM.**  The window as a strict floor on the excess-weighted squared
pairing mass of the triple: three quarters of the excess product, never reached from
below. -/
theorem three_quarters_mul_heavyExcess_prod_lt_weighted_pairing_mass (crux : SixThreeCrux)
    {first second third : Fin 6} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    3 * (heavyExcess crux.design first * heavyExcess crux.design second
        * heavyExcess crux.design third) / 4
      < heavyExcess crux.design third * atomPairing crux.design first second ^ 2
        + heavyExcess crux.design second * atomPairing crux.design first third ^ 2
        + heavyExcess crux.design first * atomPairing crux.design second third ^ 2 := by
  have hwindow := excessGap_lt_quarter_mul_heavyExcess_prod crux hfirstSecond
    hfirstThird hsecondThird
  rw [excessGap] at hwindow
  linarith

end SixThreeCrux

/-! ## 4. Counting scaffolding at `(6,3)` -/

/-- The twenty triples of `Fin 6`. -/
theorem card_powersetCard_three_sixThree :
    (Finset.univ.powersetCard 3 : Finset (Finset (Fin 6))).card = 20 := by
  rw [Finset.card_powersetCard, Finset.card_univ]
  decide

/-- The ten triples of `Fin 6` through a fixed atom. -/
theorem card_powersetCard_three_through_atom (base : Fin 6) :
    ((Finset.univ.powersetCard 3 : Finset (Finset (Fin 6))).filter
      (fun selected => base ∈ selected)).card = 10 := by
  revert base
  decide

/-- The ten ordered pairs of `Fin 6` avoiding a fixed atom — the index set that
`Gtz.coherentPairsThroughBase` filters. -/
def pairsThroughBase (base : Fin 6) : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter (fun pair => pair.1 ≠ base ∧ pair.2 ≠ base ∧ pair.1 < pair.2)

theorem card_pairsThroughBase (base : Fin 6) : (pairsThroughBase base).card = 10 := by
  revert base
  decide

theorem coherentPairsThroughBase_subset_pairsThroughBase (design : WeightedDesign 6 3)
    (base : Fin 6) : coherentPairsThroughBase design base ⊆ pairsThroughBase base := by
  intro pair hmem
  obtain ⟨hone, htwo, horder, _⟩ :=
    (mem_coherentPairsThroughBase_iff design base pair).mp hmem
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hone, htwo, horder⟩

/-- The triple map is injective on the coherent pairs through a base: those pairs carry
`pair.1 < pair.2`, so the two non-base atoms are recovered in order. -/
theorem tripleSet_injOn_coherentPairsThroughBase (design : WeightedDesign m 3) (base : Fin m) :
    Set.InjOn (fun pair : Fin m × Fin m => ({base, pair.1, pair.2} : Finset (Fin m)))
      (coherentPairsThroughBase design base) := by
  classical
  intro firstPair hfirstMem secondPair hsecondMem hsame
  obtain ⟨hfirstOne, hfirstTwo, hfirstOrder, _⟩ :=
    (mem_coherentPairsThroughBase_iff design base firstPair).mp hfirstMem
  obtain ⟨hsecondOne, hsecondTwo, hsecondOrder, _⟩ :=
    (mem_coherentPairsThroughBase_iff design base secondPair).mp hsecondMem
  simp only at hsame
  have hforward : ∀ atomIndex : Fin m, atomIndex ≠ base →
      atomIndex ∈ ({base, firstPair.1, firstPair.2} : Finset (Fin m)) →
      atomIndex = secondPair.1 ∨ atomIndex = secondPair.2 := by
    intro atomIndex hne hmem
    rw [hsame] at hmem
    rcases Finset.mem_insert.mp hmem with heq | hrest
    · exact absurd heq hne
    · rcases Finset.mem_insert.mp hrest with heq | heq
      · exact Or.inl heq
      · exact Or.inr (Finset.mem_singleton.mp heq)
  have hbackward : ∀ atomIndex : Fin m, atomIndex ≠ base →
      atomIndex ∈ ({base, secondPair.1, secondPair.2} : Finset (Fin m)) →
      atomIndex = firstPair.1 ∨ atomIndex = firstPair.2 := by
    intro atomIndex hne hmem
    rw [← hsame] at hmem
    rcases Finset.mem_insert.mp hmem with heq | hrest
    · exact absurd heq hne
    · rcases Finset.mem_insert.mp hrest with heq | heq
      · exact Or.inl heq
      · exact Or.inr (Finset.mem_singleton.mp heq)
  have hfirstOneImage := hforward firstPair.1 hfirstOne (by simp)
  have hfirstTwoImage := hforward firstPair.2 hfirstTwo (by simp)
  have hsecondOneImage := hbackward secondPair.1 hsecondOne (by simp)
  have hone : firstPair.1 = secondPair.1 := by
    rcases hfirstOneImage with heq | heq
    · exact heq
    · exfalso
      rcases hsecondOneImage with hback | hback
      · rw [← hback] at heq
        exact absurd heq (ne_of_lt hsecondOrder)
      · rw [hback] at hsecondOrder
        rw [heq] at hfirstOrder
        exact absurd hfirstOrder (asymm hsecondOrder)
  have htwo : firstPair.2 = secondPair.2 := by
    rcases hfirstTwoImage with heq | heq
    · exfalso
      rw [← hone] at heq
      exact absurd heq (ne_of_gt hfirstOrder)
    · exact heq
  exact Prod.ext hone htwo

/-- The coherent triples through a base, as a family of SUBSETS. -/
theorem coherentPairsThroughBase_image_subset (design : WeightedDesign m 3) (base : Fin m) :
    (coherentPairsThroughBase design base).image
      (fun pair => ({base, pair.1, pair.2} : Finset (Fin m)))
      ⊆ coherentTripleSets design := by
  classical
  intro selected hmem
  obtain ⟨pair, hpair, hselected⟩ := Finset.mem_image.mp hmem
  obtain ⟨hone, htwo, horder, hparity⟩ :=
    (mem_coherentPairsThroughBase_iff design base pair).mp hpair
  subst hselected
  exact (mem_coherentTripleSets_iff design _).mpr
    ⟨base, pair.1, pair.2, rfl, Ne.symm hone, Ne.symm htwo, ne_of_lt horder, hparity⟩

/-! ## 5. The census ceiling at a crux -/

namespace SixThreeCrux

/-- **NO CENSUS TRIPLE IS COHERENT.**  The set-level form of the substrate squeeze: the
two families are disjoint as families of SUBSETS, not merely as families of ordered
triples. -/
theorem disjoint_censusTripleSets_coherentTripleSets (crux : SixThreeCrux) :
    Disjoint (censusTripleSets crux.design) (coherentTripleSets crux.design) := by
  classical
  rw [Finset.disjoint_left]
  intro selected hcensus hcoherent
  obtain ⟨gapFirst, gapSecond, gapThird, hgapSet, hgapOne, hgapTwo, hgapThree, hgap⟩ :=
    (mem_censusTripleSets_iff crux.design selected).mp hcensus
  obtain ⟨parFirst, parSecond, parThird, hparSet, hparOne, hparTwo, hparThree, hparity⟩ :=
    (mem_coherentTripleSets_iff crux.design selected).mp hcoherent
  have hsame : ({gapFirst, gapSecond, gapThird} : Finset (Fin 6))
      = {parFirst, parSecond, parThird} := by rw [← hgapSet, ← hparSet]
  have htransport := tripleParity_congr_of_eq_triple crux.design
    hparOne hparTwo hparThree hsame
  have hincoherent := tripleParity_eq_neg_one_of_excessGap_nonneg crux hgapOne hgapTwo
    hgapThree hgap
  rw [hparity, hincoherent] at htransport
  norm_num at htransport

/-- **THE CENSUS CEILING.**  At a `(6,3)` crux with nonvanishing pairings at most
SIXTEEN of the twenty triples carry a nonnegative sign-blind gap.  The missing four are
the coherent floor, and coherence forces a strictly negative gap. -/
theorem card_censusTripleSets_le_sixteen (crux : SixThreeCrux)
    (hnonzero : ∀ first second : Fin 6, first ≠ second →
      atomPairing crux.design first second ≠ 0) :
    (censusTripleSets crux.design).card ≤ 16 := by
  classical
  have hcoherentFloor : 4 ≤ (coherentTripleSets crux.design).card :=
    four_le_card_coherentTripleSets_sixThree crux.design hnonzero
  have hunion : censusTripleSets crux.design ∪ coherentTripleSets crux.design
      ⊆ Finset.univ.powersetCard 3 := by
    intro selected hmem
    rcases Finset.mem_union.mp hmem with hcensus | hcoherent
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, card_eq_three_of_mem_censusTripleSets crux.design hcensus⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, card_eq_three_of_mem_coherentTripleSets crux.design hcoherent⟩
  have hcardUnion : (censusTripleSets crux.design).card
      + (coherentTripleSets crux.design).card
      = (censusTripleSets crux.design ∪ coherentTripleSets crux.design).card :=
    (Finset.card_union_of_disjoint (disjoint_censusTripleSets_coherentTripleSets crux)).symm
  have hcardBound : (censusTripleSets crux.design ∪ coherentTripleSets crux.design).card
      ≤ (Finset.univ.powersetCard 3 : Finset (Finset (Fin 6))).card :=
    Finset.card_le_card hunion
  rw [card_powersetCard_three_sixThree] at hcardBound
  omega

/-- **THE PER-ATOM CENSUS CEILING.**  Through every atom of a crux with nonvanishing
pairings at most EIGHT of the ten triangles carry a nonnegative sign-blind gap, because
at least two of them are coherent and coherence forces a negative gap. -/
theorem card_censusTripleSets_through_atom_le_eight (crux : SixThreeCrux)
    (hnonzero : ∀ first second : Fin 6, first ≠ second →
      atomPairing crux.design first second ≠ 0) (base : Fin 6) :
    ((censusTripleSets crux.design).filter (fun selected => base ∈ selected)).card ≤ 8 := by
  classical
  set triangles : Finset (Finset (Fin 6)) :=
    (Finset.univ.powersetCard 3).filter (fun selected => base ∈ selected) with htriangles
  set coherentThrough : Finset (Finset (Fin 6)) :=
    (coherentPairsThroughBase crux.design base).image
      (fun pair => ({base, pair.1, pair.2} : Finset (Fin 6))) with hcoherentThrough
  have hcoherentCard : 2 ≤ coherentThrough.card := by
    rw [hcoherentThrough, Finset.card_image_of_injOn
      (tripleSet_injOn_coherentPairsThroughBase crux.design base)]
    exact two_le_card_coherentPairsThroughBase_sixThree crux.design base hnonzero
  have hcoherentSubset : coherentThrough ⊆ triangles := by
    intro selected hmem
    obtain ⟨pair, hpair, hselected⟩ := Finset.mem_image.mp hmem
    obtain ⟨hone, htwo, horder, _⟩ :=
      (mem_coherentPairsThroughBase_iff crux.design base pair).mp hpair
    subst hselected
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      card_triple_eq_three (Ne.symm hone) (Ne.symm htwo) (ne_of_lt horder)⟩, by simp⟩
  have hcensusSubset : ((censusTripleSets crux.design).filter (fun selected => base ∈ selected))
      ⊆ triangles := by
    intro selected hmem
    rcases Finset.mem_filter.mp hmem with ⟨hcensus, hbase⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, card_eq_three_of_mem_censusTripleSets crux.design hcensus⟩, hbase⟩
  have hdisjoint : Disjoint ((censusTripleSets crux.design).filter
      (fun selected => base ∈ selected)) coherentThrough :=
    Finset.disjoint_of_subset_right
      (hcoherentThrough ▸ coherentPairsThroughBase_image_subset crux.design base)
      (Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (disjoint_censusTripleSets_coherentTripleSets crux))
  have hunion : ((censusTripleSets crux.design).filter (fun selected => base ∈ selected))
      ∪ coherentThrough ⊆ triangles :=
    Finset.union_subset hcensusSubset hcoherentSubset
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisjoint, htriangles,
    card_powersetCard_three_through_atom base] at hcard
  omega

end SixThreeCrux

/-! ## 6. The two-sided sign band, from the anti-parity partner -/

/-- A design and an anti-parity partner have DISJOINT coherent triple families: the
partner's parity is the negation of this one's on every distinct triple, so no
three-element set can be coherent for both. -/
theorem disjoint_coherentTripleSets_of_antiParity (design partner : WeightedDesign 6 3)
    (hflip : ∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
      tripleParity partner first second third = -tripleParity design first second third) :
    Disjoint (coherentTripleSets design) (coherentTripleSets partner) := by
  classical
  rw [Finset.disjoint_left]
  intro selected hleft hright
  obtain ⟨leftFirst, leftSecond, leftThird, hleftSet, hleftOne, hleftTwo, hleftThree,
    hleftParity⟩ := (mem_coherentTripleSets_iff design selected).mp hleft
  obtain ⟨rightFirst, rightSecond, rightThird, hrightSet, hrightOne, hrightTwo, hrightThree,
    hrightParity⟩ := (mem_coherentTripleSets_iff partner selected).mp hright
  have hsame : ({leftFirst, leftSecond, leftThird} : Finset (Fin 6))
      = {rightFirst, rightSecond, rightThird} := by rw [← hleftSet, ← hrightSet]
  have hflipped := hflip rightFirst rightSecond rightThird hrightOne hrightTwo hrightThree
  have htransport : tripleParity design rightFirst rightSecond rightThird
      = tripleParity design leftFirst leftSecond leftThird :=
    tripleParity_congr_of_eq_triple design hrightOne hrightTwo hrightThree hsame
  rw [hrightParity, htransport, hleftParity] at hflipped
  norm_num at hflipped

/-- The same disjointness through a fixed base, at the level of ordered pairs. -/
theorem disjoint_coherentPairsThroughBase_of_antiParity (design partner : WeightedDesign 6 3)
    (hflip : ∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
      tripleParity partner first second third = -tripleParity design first second third)
    (base : Fin 6) :
    Disjoint (coherentPairsThroughBase design base) (coherentPairsThroughBase partner base) := by
  classical
  rw [Finset.disjoint_left]
  intro pair hleft hright
  obtain ⟨hleftOne, hleftTwo, hleftOrder, hleftParity⟩ :=
    (mem_coherentPairsThroughBase_iff design base pair).mp hleft
  obtain ⟨_, _, _, hrightParity⟩ :=
    (mem_coherentPairsThroughBase_iff partner base pair).mp hright
  have hflipped := hflip base pair.1 pair.2 (Ne.symm hleftOne) (Ne.symm hleftTwo)
    (ne_of_lt hleftOrder)
  rw [hrightParity, hleftParity] at hflipped
  norm_num at hflipped

/-- **THE COHERENT CEILING — the upper half of the sign band.**  At most SIXTEEN of the
twenty triples of a `(6,3)` design with nonvanishing pairings are coherent.  Proof: the
anti-parity partner is another such design, its coherent triples are exactly this one's
INCOHERENT triples, and the shipped floor gives it four of them. -/
theorem card_coherentTripleSets_le_sixteen_sixThree (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0) :
    (coherentTripleSets design).card ≤ 16 := by
  classical
  obtain ⟨partner, _, hpartnerNonzero, hflip⟩ := exists_antiParityPartner_sixThree design hnonzero
  have hpartnerFloor : 4 ≤ (coherentTripleSets partner).card :=
    four_le_card_coherentTripleSets_sixThree partner hpartnerNonzero
  have hunion : coherentTripleSets design ∪ coherentTripleSets partner
      ⊆ Finset.univ.powersetCard 3 := by
    intro selected hmem
    rcases Finset.mem_union.mp hmem with hleft | hright
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, card_eq_three_of_mem_coherentTripleSets design hleft⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, card_eq_three_of_mem_coherentTripleSets partner hright⟩
  have hcardBound := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint
    (disjoint_coherentTripleSets_of_antiParity design partner hflip),
    card_powersetCard_three_sixThree] at hcardBound
  omega

/-- **THE PER-ATOM COHERENT CEILING.**  At most EIGHT of the ten triangles through any
atom are coherent — equivalently at least TWO are incoherent.  This is the upper half of
the per-vertex band, and it closes the gap the coherent-count rung recorded as needing a
second design with the complementary two-graph. -/
theorem card_coherentPairsThroughBase_le_eight_sixThree (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
    (base : Fin 6) : (coherentPairsThroughBase design base).card ≤ 8 := by
  classical
  obtain ⟨partner, _, hpartnerNonzero, hflip⟩ := exists_antiParityPartner_sixThree design hnonzero
  have hpartnerFloor : 2 ≤ (coherentPairsThroughBase partner base).card :=
    two_le_card_coherentPairsThroughBase_sixThree partner base hpartnerNonzero
  have hunion : coherentPairsThroughBase design base ∪ coherentPairsThroughBase partner base
      ⊆ pairsThroughBase base :=
    Finset.union_subset (coherentPairsThroughBase_subset_pairsThroughBase design base)
      (coherentPairsThroughBase_subset_pairsThroughBase partner base)
  have hcardBound := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint
    (disjoint_coherentPairsThroughBase_of_antiParity design partner hflip base),
    card_pairsThroughBase base] at hcardBound
  omega

/-- **THE GLOBAL SIGN BAND.**  Between four and sixteen of the twenty triples of any
`(6,3)` design with nonvanishing pairings are coherent.  SHARP at neither end by
anything proved here: the band leaves twelve of the sixteen two-graph isomorphism
classes standing. -/
theorem card_coherentTripleSets_mem_band_sixThree (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0) :
    4 ≤ (coherentTripleSets design).card ∧ (coherentTripleSets design).card ≤ 16 :=
  ⟨four_le_card_coherentTripleSets_sixThree design hnonzero,
    card_coherentTripleSets_le_sixteen_sixThree design hnonzero⟩

/-- **THE PER-VERTEX SIGN BAND `[2,8]`.**  Through every atom, between two and eight of
the ten triangles are coherent. -/
theorem card_coherentPairsThroughBase_mem_band_sixThree (design : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing design first second ≠ 0)
    (base : Fin 6) :
    2 ≤ (coherentPairsThroughBase design base).card
      ∧ (coherentPairsThroughBase design base).card ≤ 8 :=
  ⟨two_le_card_coherentPairsThroughBase_sixThree design base hnonzero,
    card_coherentPairsThroughBase_le_eight_sixThree design hnonzero base⟩

/-! ## 7. The dual census -/

/-- **THE DUAL CENSUS.**  A census triple of a crux is COHERENT in the chart dual: the
substrate squeeze makes it incoherent here, and the chart dual negates every parity.
The census set therefore injects into the dual's coherent family, where the shipped
floor applies. -/
theorem censusTripleSets_subset_coherentTripleSets_chartDual (crux : SixThreeCrux)
    (hnonzero : ∀ first second : Fin 6, first ≠ second →
      atomPairing crux.design first second ≠ 0)
    {dual : WeightedDesign 6 3} (hdual : IsChartDual crux.design dual) :
    censusTripleSets crux.design ⊆ coherentTripleSets dual := by
  classical
  intro selected hmem
  obtain ⟨first, second, third, hset, hone, htwo, hthree, hgap⟩ :=
    (mem_censusTripleSets_iff crux.design selected).mp hmem
  have hincoherent := SixThreeCrux.tripleParity_eq_neg_one_of_excessGap_nonneg crux hone htwo
    hthree hgap
  have hflip := tripleParity_chartDual hdual hone htwo hthree (hnonzero first second hone)
    (hnonzero first third htwo) (hnonzero second third hthree)
  rw [hincoherent] at hflip
  exact (mem_coherentTripleSets_iff dual selected).mpr
    ⟨first, second, third, hset, hone, htwo, hthree, by rw [hflip]; norm_num⟩

/-! ## 8. The composed statement a sector table consumes -/

namespace SixThreeCrux

/-- **THE SIGN-PATTERN CONSTRAINTS OF A CRUX, IN ONE PLACE.**  Everything the census
and coherence rungs jointly deliver about the two-graph of a `(6,3)` crux with
nonvanishing pairings:

* globally, between four and sixteen of the twenty triples are coherent;
* through every atom, between two and eight of the ten triangles are coherent;
* at most sixteen triples carry a nonnegative sign-blind gap, at most eight through any
  atom;
* and every one of those is INCOHERENT.

**THE CENSUS FLOOR IS ZERO** and is deliberately absent from this list —
`Gtz.censusTripleSets_icosaDesign_eq_empty` shows no positive floor follows from
sign-blind data, so a sector table keyed on the census runs at threshold `T = 0`. -/
theorem signBandAndCensusCeiling (crux : SixThreeCrux)
    (hnonzero : ∀ first second : Fin 6, first ≠ second →
      atomPairing crux.design first second ≠ 0) :
    (4 ≤ (coherentTripleSets crux.design).card
        ∧ (coherentTripleSets crux.design).card ≤ 16)
      ∧ (∀ base : Fin 6, 2 ≤ (coherentPairsThroughBase crux.design base).card
        ∧ (coherentPairsThroughBase crux.design base).card ≤ 8)
      ∧ (censusTripleSets crux.design).card ≤ 16
      ∧ (∀ base : Fin 6, ((censusTripleSets crux.design).filter
          (fun selected => base ∈ selected)).card ≤ 8)
      ∧ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
          0 ≤ excessGap crux.design first second third →
          tripleParity crux.design first second third = -1) :=
  ⟨card_coherentTripleSets_mem_band_sixThree crux.design hnonzero,
    fun base => card_coherentPairsThroughBase_mem_band_sixThree crux.design hnonzero base,
    card_censusTripleSets_le_sixteen crux hnonzero,
    fun base => card_censusTripleSets_through_atom_le_eight crux hnonzero base,
    fun _ _ _ hone htwo hthree hgap =>
      tripleParity_eq_neg_one_of_excessGap_nonneg crux hone htwo hthree hgap⟩

end SixThreeCrux

/-! ## 9. THE WALL: no census floor is available from sign-blind data -/

/-- No two icosahedral atoms are parallel: a parallel pair has a vanishing pair Gram
minor, and every distinct icosahedral pair has `3 * 3 − 9/5 = 36/5 > 0`. -/
theorem icosaDesign_hasNoParallelPair : ¬ HasParallelPair icosaDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
  have hzero := pairGramMinor_eq_zero_of_smul icosaDesign hparallel
  rw [pairGramMinor, icosaDesign_leverage, icosaDesign_leverage,
    show icosaDesign.atom keptLabel ⬝ᵥ icosaDesign.atom dropLabel
      = atomPairing icosaDesign keptLabel dropLabel from rfl,
    icosaDesign_atomPairing_sq_of_ne hne] at hzero
  norm_num at hzero

/-- **THE CENSUS OF THE ICOSAHEDRON IS EMPTY.**  Every distinct icosahedral triple has
sign-blind gap exactly `−14/5`, so not one of the twenty carries a nonnegative gap.

This is the refutation of a census FLOOR.  `Gtz.icosaDesign` is `Gtz.AllHeavy` and has
no parallel pair, and `Gtz.excessGap` reads only sign-blind data, so no hypothesis
expressible in the three heavy excesses and the three squared pairings can force a
census triple to exist.  The icosahedron is not itself a crux — it dominates
`{0, 2, 4}` (`Gtz.icosaDesign_dominates`) — but the fields it does satisfy are exactly
the ones a sign-blind census argument would have consumed. -/
theorem censusTripleSets_icosaDesign_eq_empty : censusTripleSets icosaDesign = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro selected hmem
  obtain ⟨first, second, third, _, hone, htwo, hthree, hgap⟩ :=
    (mem_censusTripleSets_iff icosaDesign selected).mp hmem
  exact absurd hgap (not_le.mpr (icosaDesign_excessGap_neg hone htwo hthree))

/-! ## 10. D6 — the whitened co-singleton cap -/

/-- **THE D6 OUTPUT.**  Every co-singleton of a `(6,3)` design that is positive definite
is spread across its own triples at ratio `1/5`: some triple avoiding the deleted atom
carries five times as much mass as the whole co-singleton.

MEASURED CEILING, so no successor over-invests: as a DOMINATION floor this gives `1/5`,
strictly weaker than the shipped `Gtz.SixThreeCrux.exists_dominates_at_three_fifths`,
and non-uniform weights cannot improve it because the guarantee is a minimum over a
triple the theorem itself chooses.  Its value is the CONTRAPOSITIVE below. -/
def IsCoSingletonSpreadLemma : Prop :=
  ∀ (design : WeightedDesign 6 3) (atomIndex : Fin 6),
    (subsetSum design {atomIndex}ᶜ).PosDef →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ selected ⊆ {atomIndex}ᶜ ∧
      ((5 : ℝ) • subsetSum design selected - subsetSum design {atomIndex}ᶜ).PosSemidef

/-- **THE SPREAD LEMMA IS A THEOREM.**  Whiten the co-singleton scaled by the uniform
weight `1/5` — positive definite, so `Gtz.exists_congruence_to_one` supplies a congruence
to the identity and no square root is ever needed — re-index the five surviving atoms by
the order isomorphism of `{c}ᶜ`, and read the result as a genuine `Gtz.WeightedDesign 5 3`
through `Gtz.whitenedFamilyDesign`.  `Gtz.gtzWeighted_corank_two 3` then hands back a
triple, and `Gtz.posSemidef_congr_right` transports its floor back across the whitener. -/
theorem isCoSingletonSpreadLemma : IsCoSingletonSpreadLemma := by
  classical
  intro design atomIndex hposdef
  have hcard : ({atomIndex}ᶜ : Finset (Fin 6)).card = 5 := by
    rw [Finset.card_compl, Finset.card_singleton]
    decide
  set enum : Fin 5 → Fin 6 :=
    fun rank => (({atomIndex}ᶜ : Finset (Fin 6)).orderIsoOfFin hcard rank : Fin 6) with henum
  have henumMem : ∀ rank, enum rank ∈ ({atomIndex}ᶜ : Finset (Fin 6)) :=
    fun rank => (({atomIndex}ᶜ : Finset (Fin 6)).orderIsoOfFin hcard rank).2
  have henumInj : Function.Injective enum := by
    intro leftRank rightRank hsame
    exact (({atomIndex}ᶜ : Finset (Fin 6)).orderIsoOfFin hcard).injective (Subtype.ext hsame)
  have himage : Finset.image enum Finset.univ = ({atomIndex}ᶜ : Finset (Fin 6)) := by
    refine Finset.eq_of_subset_of_card_le (fun atomLabel hmem => ?_) ?_
    · obtain ⟨rank, _, hrank⟩ := Finset.mem_image.mp hmem
      exact hrank ▸ henumMem rank
    · rw [Finset.card_image_of_injective _ henumInj, Finset.card_univ, Fintype.card_fin, hcard]
  have hsum : ∀ selected : Finset (Fin 5),
      ∑ rank ∈ selected, atomMatrix (design.atom (enum rank))
        = subsetSum design (selected.image enum) := fun selected => by
    rw [show subsetSum design (selected.image enum)
        = ∑ atomLabel ∈ selected.image enum, atomMatrix (design.atom atomLabel) from rfl,
      Finset.sum_image (fun _ _ _ _ hsame => henumInj hsame)]
  have hfull : ∑ rank : Fin 5, atomMatrix (design.atom (enum rank))
      = subsetSum design {atomIndex}ᶜ := by rw [hsum Finset.univ, himage]
  have hposdefScaled : (((1 : ℝ) / 5) • subsetSum design {atomIndex}ᶜ).PosDef :=
    hposdef.smul (by norm_num)
  obtain ⟨whitener, hwhitenerUnit, hwhiten⟩ := exists_congruence_to_one hposdefScaled
  have hweightSum : ∑ _rank : Fin 5, ((1 : ℝ) / 5) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  have hwhitenAtoms : whitenerᵀ
      * (∑ rank : Fin 5, ((1 : ℝ) / 5) • atomMatrix (design.atom (enum rank))) * whitener = 1 := by
    rw [← Finset.smul_sum, hfull]
    exact hwhiten
  set whitened := whitenedFamilyDesign (fun rank => design.atom (enum rank))
    (fun _ => (1 : ℝ) / 5) (fun _ => by norm_num) hweightSum whitener hwhitenAtoms
    with hwhitened
  have hcongrSum : ∀ selected : Finset (Fin 5),
      whitenerᵀ * subsetSum design (selected.image enum) * whitener
        = subsetSum whitened selected := fun selected => by
    rw [← hsum selected, Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun rank _ => transpose_mul_atomMatrix_mul whitener _
  obtain ⟨blockFive, hblockCard, hblockPsd⟩ := gtzWeighted_corank_two 3 (by norm_num) whitened
  refine ⟨blockFive.image enum, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ henumInj, hblockCard]
  · intro atomLabel hmem
    obtain ⟨rank, _, hrank⟩ := Finset.mem_image.mp hmem
    exact hrank ▸ henumMem rank
  · set gap := subsetSum design (blockFive.image enum)
      - ((1 : ℝ) / 5) • subsetSum design {atomIndex}ᶜ with hgap
    have hgapSymm : gapᵀ = gap := by
      rw [hgap, Matrix.transpose_sub, Matrix.transpose_smul, subsetSum_transpose,
        subsetSum_transpose]
    have hconjugate : whitenerᵀ * gap * whitener = subsetSum whitened blockFive - 1 := by
      rw [hgap, Matrix.mul_sub, Matrix.sub_mul, hcongrSum blockFive, hwhiten]
    have hgapPsd : gap.PosSemidef :=
      (posSemidef_congr_right hgapSymm hwhitenerUnit).mpr (hconjugate ▸ hblockPsd)
    have hscaled := hgapPsd.smul (by norm_num : (0 : ℝ) ≤ 5)
    have hrewrite : (5 : ℝ) • gap
        = (5 : ℝ) • subsetSum design (blockFive.image enum)
          - subsetSum design {atomIndex}ᶜ := by
      rw [hgap, smul_sub, smul_smul]
      norm_num
    rwa [hrewrite] at hscaled

namespace SixThreeCrux

/-- **THE CO-SINGLETON CAP.**  At a `(6,3)` crux no co-singleton reaches five times the
identity.  With `Gtz.SixThreeCrux.hasStrictlyDominatingCoSingletons` this pins every
`lambda_min (subsetSum design {c}ᶜ)` into the open window `(1, 5)`.

SHARP at the upper end: the `(6,3)` diamond ties attain `lambda_min = 5` exactly at two
of their six atoms (measured exactly, /tmp/gtz-x/x3-census/whitened.out); the
icosahedron sits at `3`, where D6's floor `3/5` coincides with the shipped constant. -/
theorem not_posSemidef_coSingleton_sub_five (crux : SixThreeCrux) (atomIndex : Fin 6) :
    ¬ (subsetSum crux.design {atomIndex}ᶜ
        - (5 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  intro hbig
  have hspread : IsCoSingletonSpreadLemma := isCoSingletonSpreadLemma
  have hposdef : (subsetSum crux.design {atomIndex}ᶜ).PosDef := by
    have hstrict := crux.hasStrictlyDominatingCoSingletons atomIndex
    have hone : (1 : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := Matrix.PosSemidef.one
    have hsum := hstrict.add_posSemidef hone
    have hrewrite : subsetSum crux.design {atomIndex}ᶜ
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) + (1 : Matrix (Fin 3) (Fin 3) ℝ)
        = subsetSum crux.design {atomIndex}ᶜ := by abel
    rwa [hrewrite] at hsum
  obtain ⟨selected, hcard, _, hsplit⟩ := hspread crux.design atomIndex hposdef
  have hsum : ((5 : ℝ) • subsetSum crux.design selected
      - (5 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
    have hadd := hsplit.add hbig
    have hrewrite : ((5 : ℝ) • subsetSum crux.design selected
          - subsetSum crux.design {atomIndex}ᶜ)
        + (subsetSum crux.design {atomIndex}ᶜ - (5 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        = (5 : ℝ) • subsetSum crux.design selected
          - (5 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by abel
    rwa [hrewrite] at hadd
  have hscaled : (subsetSum crux.design selected
      - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
    have hsmul := hsum.smul (by norm_num : (0:ℝ) ≤ (5 : ℝ)⁻¹)
    have hrewrite : (5 : ℝ)⁻¹ • ((5 : ℝ) • subsetSum crux.design selected
          - (5 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        = subsetSum crux.design selected - (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [smul_sub, smul_smul, smul_smul]
      norm_num
    rwa [hrewrite] at hsmul
  exact crux.hasNoDominatingTriple selected hcard hscaled

/-- **THE CO-SINGLETON WINDOW `(1, 5)`.**  Every co-singleton of a `(6,3)` crux strictly
dominates the identity and strictly fails to dominate five times it.  The lower half is
the crux field itself; the upper half is D6.  Both ends are attained elsewhere in the
`(6,3)` landscape — the diamond ties reach exactly `5` at two of their six atoms — so the
window is not slack. -/
theorem coSingletonWindow (crux : SixThreeCrux) (atomIndex : Fin 6) :
    (subsetSum crux.design {atomIndex}ᶜ - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef
      ∧ ¬ (subsetSum crux.design {atomIndex}ᶜ
        - (5 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef :=
  ⟨crux.hasStrictlyDominatingCoSingletons atomIndex,
    not_posSemidef_coSingleton_sub_five crux atomIndex⟩

end SixThreeCrux

end Gtz
