/-
# The Brick: the heavy--light band of the weight polytope

`Gtz.Quantitative.WeightedTripleCriterion` reduces the free-weight `(6,3)`
statement to a covering question (Theorem A): twenty convex, closed, upward-closed
`3`-local cells `K_T` must cover the hypersimplex
`Sigma = {tau in [0,1]^6 : sum tau = 4}`.  The centre is covered by U6, the top
band by the shipped `16/25` margin, the cheap corners by the two-cheap-atom gate
and the merge boundary by planar rigidity.  What is left is the BAND where three
atoms are heavy -- near a coplanar triple -- and three are light.  This file
attacks it.

## What is landed here

**A sharp negative, exactly.**  `Gtz.sum_involSlackDeterminant_six` :

  `sum over the twenty triples of Delta_tau(T) = e_3(tau) - 2 sum_c tau_c`

for EVERY hollow symmetric involution on `Fin 6` and EVERY slack vector -- the
weighted generalisation of the six-set minor identity, which is its value `8` at
`tau = 1`.  On `Sigma` the right-hand side reads
`-(4 + 3 sum (1 - tau_c)^2 + sum (1 - tau_c)^3)/3`, so the aggregate is at most
`-4/3` (`Gtz.sum_involSlackDeterminant_le_of_mem_slackSimplex`).  Consequently NO
unweighted aggregation of determinant clauses can certify the covering, at any
point of the polytope -- and the pen's pair-sum gate is the four-term shadow of
this identity, which is why `Gtz.pairSumValue_nonpos` came out vacuous.  The
covering has to be carried entirely by the SPREAD of the twenty values, and the
identity says exactly how much spread is available.

**The mechanism that survives: STARVE-FEED.**  Fix a hub triple `{a,b,c}` and the
pair `{a,b}` inside it.  The four triples through `{a,b}` sum to
`Gtz.pairSumValue` (`Gtz.sum_involSlackDeterminant_through_pair`), so the three
triples through `{a,b}` OFF the hub sum to
`pairSumValue - Delta(a,b,c)` (`Gtz.sum_involSlackDeterminant_off_hub`).  Hence

> if the hub is STARVED -- `Delta(a,b,c) <= pairSumValue(tau_a, tau_b, w_ab)` --
> then one of the three off-hub triples has a nonnegative determinant clause.

That is `Gtz.exists_nonneg_involSlackDeterminant_of_starvedHub`, and with the
pairwise clauses it produces an actual cell membership
(`Gtz.exists_mem_tripleSlackCell_of_starvedHub`).  The pen proposed to run the
pair sum as an AVERAGE and select afterwards; the average is vacuous.  What is
not vacuous is the average taken RELATIVE TO A FAILING HUB: the hub's own deficit
is the budget the three mixed triples share.

**The band gate, in geometric constants.**  At a constant heavy slack `h` the
starvation condition is exactly a bound on the hub's Gram determinant
(`Gtz.starvedHub_of_hollowTripleBracket_le`):

  `det Gamma[H] <= (1 - h) (1 - h + 3 h^2 - sigma_H - 4 w_ab)`.

So the band splits on ONE scalar, `det Gamma[H]`, with an explicit window of width
`(1 - h)(2 h (1 - h) + 4 w_ab)` left open -- the region where the heavy triple
fails, but not by enough to feed a mixed triple.  This is the honest residual and
it is named as such below.

**The extremal candidate, and its band closed.**  The pen's V8 configuration --
a Mercedes triple in a plane plus three lights on the cone `cos^2 psi = 2/3` --
was absent from the repository.  It is landed here as an explicit hollow
symmetric involution (`Gtz.mercedesConeInvolution`,
`Gtz.isHollowInvolution_mercedesConeInvolution`) together with its exact data,
and its whole symmetric band is COVERED
(`Gtz.mercedesCone_covers_symmetricBand`): the light triple carries `h <= 5/6`,
because its determinant clause factors as `(l - 1/2)^2 (l + 1) >= 0`, and the
starve-feed gate carries `h >= 5/6`, because the gate condition factors as
`(h - 1)(12 h^2 - 4 h - 3) <= 0`.  The exact crossover of the gate is
`(1 + sqrt 10)/6` (`Gtz.mercedesCone_gateThreshold`), comfortably below `5/6`, so
the two mechanisms overlap and the band has no hole.  In particular the candidate
is not a counterexample, and the pen's reported margin `+0.009` at
`h = 9/10` is the value of a FRUSTRATED mixed triple, `7/750`; the coherent ones
carry `103/3000` (`Gtz.involSlackDeterminant_mercedesCone_at_nine_tenths`).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.CheapAtomGate
import Gtz.Quantitative.MinorSumIdentities
import Gtz.Quantitative.WeightedTripleCriterion

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {size : ℕ}

/-! ## 1. The determinant clause of a triple of an involution

`Gtz.slackDeterminantThree` reads six loose scalars.  Attached to an involution
and a slack vector it becomes the pen's `Delta(T)`, and that is the object every
identity below is about. -/

/-- **THE DETERMINANT CLAUSE** `Delta_tau(T) = det(diag(tau_T) + M[T])` of a triple
of a hollow symmetric involution, at an arbitrary slack vector. -/
noncomputable def involSlackDeterminant (invol : Matrix (Fin size) (Fin size) ℝ)
    (slack : Fin size → ℝ) (first second third : Fin size) : ℝ :=
  slackDeterminantThree (slack first) (slack second) (slack third)
    (invol first second) (invol first third) (invol second third)

/-- The clause is the determinant of the slack-shifted block. -/
theorem involSlackDeterminant_eq_det (invol : Matrix (Fin size) (Fin size) ℝ)
    (slack : Fin size → ℝ) (first second third : Fin size) :
    involSlackDeterminant invol slack first second third
      = (slackHollowThree (slack first) (slack second) (slack third)
          (invol first second) (invol first third) (invol second third)).det :=
  (det_slackHollowThree _ _ _ _ _ _).symm

/-- **THE CELL FROM THE SEVEN CLAUSES.**  Nonnegative slacks, three pairwise
clauses and the determinant clause put the slack vector in the triple's domination
cell.  This is `Gtz.posSemidef_slackHollowThree_iff` in the coordinates the band
argument uses. -/
theorem mem_tripleSlackCell_of_clauses {invol : Matrix (Fin size) (Fin size) ℝ}
    {slack : Fin size → ℝ} {first second third : Fin size}
    (hfirst : 0 ≤ slack first) (hsecond : 0 ≤ slack second) (hthird : 0 ≤ slack third)
    (hpairFirstSecond : invol first second ^ 2 ≤ slack first * slack second)
    (hpairFirstThird : invol first third ^ 2 ≤ slack first * slack third)
    (hpairSecondThird : invol second third ^ 2 ≤ slack second * slack third)
    (hdeterminant : 0 ≤ involSlackDeterminant invol slack first second third) :
    slack ∈ tripleSlackCell invol first second third := by
  rw [mem_tripleSlackCell_iff, posSemidef_slackHollowThree_iff]
  exact ⟨hfirst, hsecond, hthird, hpairFirstSecond, hpairFirstThird, hpairSecondThird,
    hdeterminant⟩

/-! ## 2. The pair identity on the abstract involution

The four triples through a pair sum to `Gtz.pairSumValue`.  The design-side twin
is `Gtz.sum_slackTripleDeterminant_through_pair_eq`; this one needs no design at
all, only the row law and the vanishing supply chain of the involution. -/

/-- **THE PAIR IDENTITY.**  At any slack vector of total four, the four
determinant clauses through a pair sum to `Gtz.pairSumValue` of the pair's two
slacks and its edge weight.  The row law supplies both copies of `1 - w`, the
supply chain supplies the `0`. -/
theorem sum_involSlackDeterminant_through_pair {invol : Matrix (Fin 6) (Fin 6) ℝ}
    (hinvol : IsHollowInvolution invol)
    {outerFirst outerSecond outerThird outerFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![outerFirst, outerSecond, outerThird, outerFourth, pairFirst, pairSecond])
    (slack : Fin 6 → ℝ) (hslackSum : ∑ index, slack index = 4) :
    involSlackDeterminant invol slack pairFirst pairSecond outerFirst
        + involSlackDeterminant invol slack pairFirst pairSecond outerSecond
        + involSlackDeterminant invol slack pairFirst pairSecond outerThird
        + involSlackDeterminant invol slack pairFirst pairSecond outerFourth
      = pairSumValue (slack pairFirst) (slack pairSecond) (invol pairFirst pairSecond ^ 2) := by
  have hdistinct : pairFirst ≠ pairSecond := by
    intro hvalue
    have hslot : (4 : Fin 6) = 5 := hbijective.1 (by simpa using hvalue)
    exact absurd hslot (by decide)
  rw [sum_eq_of_bijective_six hbijective slack] at hslackSum
  have hrowFirst := hinvol.sum_sq_row_six hbijective pairFirst
  rw [hinvol.diagonal_eq_zero pairFirst] at hrowFirst
  have hrowSecond := hinvol.sum_sq_row_six hbijective pairSecond
  rw [hinvol.diagonal_eq_zero pairSecond, hinvol.apply_comm pairFirst pairSecond] at hrowSecond
  have hchain : invol pairFirst outerFirst * invol pairSecond outerFirst
      + invol pairFirst outerSecond * invol pairSecond outerSecond
      + invol pairFirst outerThird * invol pairSecond outerThird
      + invol pairFirst outerFourth * invol pairSecond outerFourth = 0 := by
    have hentry := congrFun (congrFun hinvol.square_eq_one pairFirst) pairSecond
    rw [Matrix.mul_apply, Matrix.one_apply_ne hdistinct,
      sum_eq_of_bijective_six hbijective
        fun colIndex => invol pairFirst colIndex * invol colIndex pairSecond] at hentry
    rw [hinvol.diagonal_eq_zero pairFirst, hinvol.diagonal_eq_zero pairSecond,
      hinvol.apply_comm pairSecond outerFirst, hinvol.apply_comm pairSecond outerSecond,
      hinvol.apply_comm pairSecond outerThird, hinvol.apply_comm pairSecond outerFourth]
      at hentry
    linarith [hentry]
  simp only [involSlackDeterminant, slackDeterminantThree, pairSumValue]
  linear_combination
    (slack pairFirst * slack pairSecond - invol pairFirst pairSecond ^ 2) * hslackSum
      - slack pairSecond * hrowFirst - slack pairFirst * hrowSecond
      + 2 * invol pairFirst pairSecond * hchain

/-! ## 3. STARVE-FEED: the hub's deficit is the mixed triples' budget

The identity of section 2 is an EQUALITY, and `Gtz.pairSumValue` is nonpositive on
the whole polytope, so on its own it says only that the four clauses through a
pair cannot all hold.  Splitting off ONE of the four -- the hub -- turns the same
identity into a positive mechanism: whatever the hub loses, the other three
share. -/

/-- **THE STARVE-FEED IDENTITY.**  The three determinant clauses through a pair and
off a chosen hub sum to the pair functional minus the hub's own clause. -/
theorem sum_involSlackDeterminant_off_hub {invol : Matrix (Fin 6) (Fin 6) ℝ}
    (hinvol : IsHollowInvolution invol)
    {outerFirst outerSecond outerThird hubThird pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![outerFirst, outerSecond, outerThird, hubThird, pairFirst, pairSecond])
    (slack : Fin 6 → ℝ) (hslackSum : ∑ index, slack index = 4) :
    involSlackDeterminant invol slack pairFirst pairSecond outerFirst
        + involSlackDeterminant invol slack pairFirst pairSecond outerSecond
        + involSlackDeterminant invol slack pairFirst pairSecond outerThird
      = pairSumValue (slack pairFirst) (slack pairSecond) (invol pairFirst pairSecond ^ 2)
        - involSlackDeterminant invol slack pairFirst pairSecond hubThird := by
  have hpair := sum_involSlackDeterminant_through_pair hinvol hbijective slack hslackSum
  linarith

/-- **THE STARVE-FEED GATE.**  If the hub triple `{a, b, c}` is starved -- its own
determinant clause at most the pair functional of `{a, b}` -- then one of the three
triples `{a, b, k}` with `k` outside the hub has a nonnegative determinant clause.

Since `Gtz.pairSumValue` is at most zero, starvation asks the hub to FAIL, and to
fail by at least `(2 - tau_a - tau_b)(2 w_ab + 2 - tau_a - tau_b)` up to the
second-order term.  That deficit closes as the pair approaches the deletion
corner, which is why the gate is sharp exactly there. -/
theorem exists_nonneg_involSlackDeterminant_of_starvedHub {invol : Matrix (Fin 6) (Fin 6) ℝ}
    (hinvol : IsHollowInvolution invol)
    {outerFirst outerSecond outerThird hubThird pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![outerFirst, outerSecond, outerThird, hubThird, pairFirst, pairSecond])
    (slack : Fin 6 → ℝ) (hslackSum : ∑ index, slack index = 4)
    (hstarved : involSlackDeterminant invol slack pairFirst pairSecond hubThird
      ≤ pairSumValue (slack pairFirst) (slack pairSecond) (invol pairFirst pairSecond ^ 2)) :
    0 ≤ involSlackDeterminant invol slack pairFirst pairSecond outerFirst
      ∨ 0 ≤ involSlackDeterminant invol slack pairFirst pairSecond outerSecond
      ∨ 0 ≤ involSlackDeterminant invol slack pairFirst pairSecond outerThird := by
  by_contra hcontra
  simp only [not_or, not_le] at hcontra
  obtain ⟨hfirst, hsecond, hthird⟩ := hcontra
  have hsplit := sum_involSlackDeterminant_off_hub hinvol hbijective slack hslackSum
  linarith

/-- **THE STARVE-FEED GATE, AS A CELL MEMBERSHIP.**  With the pairwise clauses in
hand for all three candidates, the starved hub delivers an actual dominating
triple through the pair. -/
theorem exists_mem_tripleSlackCell_of_starvedHub {invol : Matrix (Fin 6) (Fin 6) ℝ}
    (hinvol : IsHollowInvolution invol)
    {outerFirst outerSecond outerThird hubThird pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![outerFirst, outerSecond, outerThird, hubThird, pairFirst, pairSecond])
    (slack : Fin 6 → ℝ) (hslackSum : ∑ index, slack index = 4)
    (hslackNonneg : ∀ index, 0 ≤ slack index)
    (hpair : invol pairFirst pairSecond ^ 2 ≤ slack pairFirst * slack pairSecond)
    (hcrossFirst : ∀ outer : Fin 6, invol pairFirst outer ^ 2 ≤ slack pairFirst * slack outer)
    (hcrossSecond : ∀ outer : Fin 6, invol pairSecond outer ^ 2 ≤ slack pairSecond * slack outer)
    (hstarved : involSlackDeterminant invol slack pairFirst pairSecond hubThird
      ≤ pairSumValue (slack pairFirst) (slack pairSecond) (invol pairFirst pairSecond ^ 2)) :
    ∃ outer : Fin 6, pairFirst ≠ pairSecond ∧ pairFirst ≠ outer ∧ pairSecond ≠ outer
      ∧ slack ∈ tripleSlackCell invol pairFirst pairSecond outer := by
  have hdistinctPair : pairFirst ≠ pairSecond := by
    intro hvalue
    have hslot : (4 : Fin 6) = 5 := hbijective.1 (by simpa using hvalue)
    exact absurd hslot (by decide)
  have houter : ∀ leftSlot rightSlot : Fin 6, leftSlot ≠ rightSlot →
      ![outerFirst, outerSecond, outerThird, hubThird, pairFirst, pairSecond] leftSlot
        ≠ ![outerFirst, outerSecond, outerThird, hubThird, pairFirst, pairSecond] rightSlot :=
    fun _ _ hslot hvalue => hslot (hbijective.1 hvalue)
  have hbuild : ∀ outer : Fin 6, pairFirst ≠ outer → pairSecond ≠ outer →
      0 ≤ involSlackDeterminant invol slack pairFirst pairSecond outer →
      slack ∈ tripleSlackCell invol pairFirst pairSecond outer := by
    intro outer _ _ hdeterminant
    exact mem_tripleSlackCell_of_clauses (hslackNonneg pairFirst) (hslackNonneg pairSecond)
      (hslackNonneg outer) hpair (hcrossFirst outer) (hcrossSecond outer) hdeterminant
  rcases exists_nonneg_involSlackDeterminant_of_starvedHub hinvol hbijective slack hslackSum
    hstarved with hfirst | hsecond | hthird
  · exact ⟨outerFirst, hdistinctPair, houter 4 0 (by decide), houter 5 0 (by decide),
      hbuild outerFirst (houter 4 0 (by decide)) (houter 5 0 (by decide)) hfirst⟩
  · exact ⟨outerSecond, hdistinctPair, houter 4 1 (by decide), houter 5 1 (by decide),
      hbuild outerSecond (houter 4 1 (by decide)) (houter 5 1 (by decide)) hsecond⟩
  · exact ⟨outerThird, hdistinctPair, houter 4 2 (by decide), houter 5 2 (by decide),
      hbuild outerThird (houter 4 2 (by decide)) (houter 5 2 (by decide)) hthird⟩

/-! ## 4. The band gate in geometric constants

Everything above is exact and weight-free.  Reading the starvation condition at a
CONSTANT heavy slack turns it into a bound on one scalar of the configuration: the
hub's Gram determinant. -/

/-- The pair functional at equal slacks, factored.  The two summands are the two
sources of the deficit: the second-order cost of leaving the deletion corner, and
the first-order cost of the pair's own edge. -/
theorem pairSumValue_self (level pairWeight : ℝ) :
    pairSumValue level level pairWeight
      = -(1 - level) * (2 * level * (1 - level) + 4 * pairWeight) := by
  rw [pairSumValue]; ring

/-- **THE HUB CLAUSE IN BRACKET COORDINATES.**  At a constant slack the hub's
determinant clause is its Gram determinant minus an explicit multiple of the
slack's distance from the deletion corner. -/
theorem involSlackDeterminant_self_eq_bracket_sub {invol : Matrix (Fin size) (Fin size) ℝ}
    {slack : Fin size → ℝ} {level : ℝ} {first second third : Fin size}
    (hfirst : slack first = level) (hsecond : slack second = level)
    (hthird : slack third = level) :
    involSlackDeterminant invol slack first second third
      = hollowTripleBracket invol first second third
        - (1 - level) * (1 + level + level ^ 2
          - hollowTripleSigma invol first second third) := by
  rw [involSlackDeterminant, hfirst, hsecond, hthird, slackDeterminantThree,
    hollowTripleBracket, hollowTripleSigma, elliptopeBracket]
  ring

/-- **THE BAND GATE.**  At a constant heavy slack `level`, starvation of the hub is
exactly the bound

  `det Gamma[H] <= (1 - level) (1 - level + 3 level^2 - sigma_H - 4 w_ab)`

on the hub's Gram determinant.  Everything on the right is explicit: the distance
from the deletion corner, the hub's total edge mass, and the chosen pair's edge.
The window the gate leaves open has width `(1 - level)(2 level (1 - level) + 4 w_ab)`
and closes at the corner. -/
theorem starvedHub_of_hollowTripleBracket_le {invol : Matrix (Fin size) (Fin size) ℝ}
    {slack : Fin size → ℝ} {level : ℝ} {first second third : Fin size}
    (hfirst : slack first = level) (hsecond : slack second = level)
    (hthird : slack third = level)
    (hbracket : hollowTripleBracket invol first second third
      ≤ (1 - level) * (1 - level + 3 * level ^ 2
        - hollowTripleSigma invol first second third - 4 * invol first second ^ 2)) :
    involSlackDeterminant invol slack first second third
      ≤ pairSumValue (slack first) (slack second) (invol first second ^ 2) := by
  rw [involSlackDeterminant_self_eq_bracket_sub hfirst hsecond hthird, hfirst, hsecond,
    pairSumValue_self]
  nlinarith [hbracket]

/-! ## 5. The conservation law, and why unweighted aggregation is dead

The pair identity of section 2 is the four-term shadow of a global one.  Summing
it over all fifteen pairs counts every triple three times, and what comes out is
free of the involution altogether. -/

/-- **THE WEIGHTED SIX-SET IDENTITY.**  For every hollow symmetric involution on
`Fin 6` and every slack vector, the twenty determinant clauses total

  `e_3(tau) - 2 sum_c tau_c`,

the elementary symmetric cubic of the slacks minus twice their total.  At the
constant slack `1` this is `20 - 12 = 8`, the shipped six-set minor identity
`Gtz.IsHollowInvolution.sum_det_principalMinors_one_add`; the content here is that
the involution drops out at EVERY slack vector, not only the constant one.  Six row
laws and the vanishing of the total oriented product are the whole proof. -/
theorem sum_involSlackDeterminant_six {invol : Matrix (Fin 6) (Fin 6) ℝ}
    (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    (slack : Fin 6 → ℝ) :
    involSlackDeterminant invol slack first second third
        + involSlackDeterminant invol slack first second fourth
        + involSlackDeterminant invol slack first second fifth
        + involSlackDeterminant invol slack first second sixth
        + involSlackDeterminant invol slack first third fourth
        + involSlackDeterminant invol slack first third fifth
        + involSlackDeterminant invol slack first third sixth
        + involSlackDeterminant invol slack first fourth fifth
        + involSlackDeterminant invol slack first fourth sixth
        + involSlackDeterminant invol slack first fifth sixth
        + involSlackDeterminant invol slack second third fourth
        + involSlackDeterminant invol slack second third fifth
        + involSlackDeterminant invol slack second third sixth
        + involSlackDeterminant invol slack second fourth fifth
        + involSlackDeterminant invol slack second fourth sixth
        + involSlackDeterminant invol slack second fifth sixth
        + involSlackDeterminant invol slack third fourth fifth
        + involSlackDeterminant invol slack third fourth sixth
        + involSlackDeterminant invol slack third fifth sixth
        + involSlackDeterminant invol slack fourth fifth sixth
      = ((∑ index, slack index) ^ 3 - 3 * (∑ index, slack index) * (∑ index, slack index ^ 2)
          + 2 * ∑ index, slack index ^ 3) / 6
        - 2 * ∑ index, slack index := by
  have hproduct := hinvol.sum_tripleProduct_six hbijective
  simp only [hollowTripleProduct] at hproduct
  have hrowOne := hinvol.sum_sq_row_six hbijective first
  have hrowTwo := hinvol.sum_sq_row_six hbijective second
  have hrowThree := hinvol.sum_sq_row_six hbijective third
  have hrowFour := hinvol.sum_sq_row_six hbijective fourth
  have hrowFive := hinvol.sum_sq_row_six hbijective fifth
  have hrowSix := hinvol.sum_sq_row_six hbijective sixth
  rw [hinvol.diagonal_eq_zero first] at hrowOne
  rw [hinvol.diagonal_eq_zero second, hinvol.apply_comm first second] at hrowTwo
  rw [hinvol.diagonal_eq_zero third, hinvol.apply_comm first third,
    hinvol.apply_comm second third] at hrowThree
  rw [hinvol.diagonal_eq_zero fourth, hinvol.apply_comm first fourth,
    hinvol.apply_comm second fourth, hinvol.apply_comm third fourth] at hrowFour
  rw [hinvol.diagonal_eq_zero fifth, hinvol.apply_comm first fifth,
    hinvol.apply_comm second fifth, hinvol.apply_comm third fifth,
    hinvol.apply_comm fourth fifth] at hrowFive
  rw [hinvol.diagonal_eq_zero sixth, hinvol.apply_comm first sixth,
    hinvol.apply_comm second sixth, hinvol.apply_comm third sixth,
    hinvol.apply_comm fourth sixth, hinvol.apply_comm fifth sixth] at hrowSix
  rw [sum_eq_of_bijective_six hbijective slack,
    sum_eq_of_bijective_six hbijective fun index => slack index ^ 2,
    sum_eq_of_bijective_six hbijective fun index => slack index ^ 3]
  simp only [involSlackDeterminant, slackDeterminantThree]
  linear_combination
    (slack first - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth) / 2) * hrowOne
      + (slack second - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth) / 2) * hrowTwo
      + (slack third - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth) / 2) * hrowThree
      + (slack fourth - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth) / 2) * hrowFour
      + (slack fifth - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth) / 2) * hrowFive
      + (slack sixth - (slack first + slack second + slack third + slack fourth + slack fifth
        + slack sixth) / 2) * hrowSix
      + 2 * hproduct

/-- **THE AGGREGATE IS BOUNDED AWAY FROM ZERO, EVERYWHERE ON THE POLYTOPE.**  On
`Gtz.slackSimplex` the twenty determinant clauses total

  `-(4 + 3 sum_c (1 - tau_c)^2 + sum_c (1 - tau_c)^3) / 3 <= -4/3`,

so their AVERAGE is at most `-1/15` at every point.  Hence no unweighted
aggregation of determinant clauses can certify the covering anywhere: the pen's
pair-sum gate (`Gtz.pairSumValue_nonpos`) is the four-term restriction of this,
and it is vacuous for the same reason.  The covering has to be carried by the
spread of the twenty values, and this identity says exactly how much spread there
has to be.

Substituting `tau = 1 - epsilon` with `sum epsilon = 2` makes it elementary:
`e_3(tau) - 2 sum tau = 4 e_2(epsilon) - e_3(epsilon) - 8` and
`e_2(epsilon) = (4 - sum epsilon^2)/2 <= 2`. -/
theorem sum_involSlackDeterminant_le_of_mem_slackSimplex {invol : Matrix (Fin 6) (Fin 6) ℝ}
    (hinvol : IsHollowInvolution invol)
    {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    {slack : Fin 6 → ℝ} (hmember : slack ∈ slackSimplex) :
    involSlackDeterminant invol slack first second third
        + involSlackDeterminant invol slack first second fourth
        + involSlackDeterminant invol slack first second fifth
        + involSlackDeterminant invol slack first second sixth
        + involSlackDeterminant invol slack first third fourth
        + involSlackDeterminant invol slack first third fifth
        + involSlackDeterminant invol slack first third sixth
        + involSlackDeterminant invol slack first fourth fifth
        + involSlackDeterminant invol slack first fourth sixth
        + involSlackDeterminant invol slack first fifth sixth
        + involSlackDeterminant invol slack second third fourth
        + involSlackDeterminant invol slack second third fifth
        + involSlackDeterminant invol slack second third sixth
        + involSlackDeterminant invol slack second fourth fifth
        + involSlackDeterminant invol slack second fourth sixth
        + involSlackDeterminant invol slack second fifth sixth
        + involSlackDeterminant invol slack third fourth fifth
        + involSlackDeterminant invol slack third fourth sixth
        + involSlackDeterminant invol slack third fifth sixth
        + involSlackDeterminant invol slack fourth fifth sixth
      ≤ -(4 / 3) := by
  obtain ⟨hbounds, hsum⟩ := hmember
  have hidentity := sum_involSlackDeterminant_six hinvol hbijective slack
  rw [hidentity, hsum]
  have hcube : ∀ index : Fin 6, slack index ^ 3 ≤ slack index ^ 2 := by
    intro index
    nlinarith [(hbounds index).1, (hbounds index).2, sq_nonneg (slack index)]
  have hcubeTotal : ∑ index, slack index ^ 3 ≤ ∑ index, slack index ^ 2 :=
    Finset.sum_le_sum fun index _ => hcube index
  have hsquareLower : ∀ index : Fin 6, (4 / 3) * slack index - 4 / 9 ≤ slack index ^ 2 := by
    intro index
    nlinarith [sq_nonneg (slack index - 2 / 3)]
  have hsquareFloor : (8 : ℝ) / 3 ≤ ∑ index, slack index ^ 2 := by
    have hbound : ∑ index : Fin 6, ((4 / 3) * slack index - 4 / 9)
        ≤ ∑ index : Fin 6, slack index ^ 2 :=
      Finset.sum_le_sum fun index _ => hsquareLower index
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hbound
    norm_num at hbound
    linarith
  linarith

/-! ### The residual window, named

The two branches of the band gate -- hub dominating, hub starved -- do not meet.
What separates them is exactly the pair functional, so the residual is an interval
in ONE scalar of the configuration, and its width closes at the deletion corner. -/

/-- **THE RESIDUAL WINDOW.**  At a constant slack on the hub, if the hub's own
determinant clause is negative but not negative enough to feed the mixed triples,
then the hub's Gram determinant lies strictly between the two explicit bounds.
This is the honest gap this file does not close: the heavy triple fails, and it
fails by less than `(1 - level)(2 level (1 - level) + 4 w_ab)`. -/
theorem hollowTripleBracket_mem_residualWindow {invol : Matrix (Fin size) (Fin size) ℝ}
    {slack : Fin size → ℝ} {level : ℝ} {first second third : Fin size}
    (hfirst : slack first = level) (hsecond : slack second = level)
    (hthird : slack third = level)
    (hfails : involSlackDeterminant invol slack first second third < 0)
    (hnotStarved : pairSumValue (slack first) (slack second) (invol first second ^ 2)
      < involSlackDeterminant invol slack first second third) :
    (1 - level) * (1 - level + 3 * level ^ 2 - hollowTripleSigma invol first second third
          - 4 * invol first second ^ 2)
        < hollowTripleBracket invol first second third
      ∧ hollowTripleBracket invol first second third
        < (1 - level) * (1 + level + level ^ 2
          - hollowTripleSigma invol first second third) := by
  rw [involSlackDeterminant_self_eq_bracket_sub hfirst hsecond hthird] at hfails hnotStarved
  rw [hfirst, hsecond, pairSumValue_self] at hnotStarved
  exact ⟨by nlinarith [hnotStarved], by linarith [hfails]⟩

/-- **THE WIDTH OF THE RESIDUAL WINDOW**, in closed form.  It is `O(1 - level)`, so
the window closes as the hub approaches the deletion corner -- which is why the
gate is exact there and why the deletion corners are the only zero-margin points
of the band. -/
theorem residualWindow_width (level pairWeight totalEdgeMass : ℝ) :
    (1 - level) * (1 + level + level ^ 2 - totalEdgeMass)
        - (1 - level) * (1 - level + 3 * level ^ 2 - totalEdgeMass - 4 * pairWeight)
      = (1 - level) * (2 * level * (1 - level) + 4 * pairWeight) := by
  ring

/-! ### The gate on a design

`Gtz.Quantitative.WeightedTripleCriterion` makes the involution-level statement
equivalent to the design-level one, so the gate above is already the theorem.  The
corollary below spells out the design reading for consumers that want
`Gtz.Dominates` directly. -/

/-- **THE STARVE-FEED GATE, ON A UNIFORM-SHARE ALL-HEAVY DESIGN.**  A starved hub
delivers a dominating triple through the pair. -/
theorem exists_dominates_of_starvedHub (D : WeightedDesign 6 3)
    (hshare : ∀ atomIndex, atomShare D atomIndex = 1 / 2) (hheavy : AllHeavy D)
    {outerFirst outerSecond outerThird hubThird pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![outerFirst, outerSecond, outerThird, hubThird, pairFirst, pairSecond])
    (hpair : correlationInvolution D pairFirst pairSecond ^ 2
      ≤ weightSlack D pairFirst * weightSlack D pairSecond)
    (hcrossFirst : ∀ outer : Fin 6, correlationInvolution D pairFirst outer ^ 2
      ≤ weightSlack D pairFirst * weightSlack D outer)
    (hcrossSecond : ∀ outer : Fin 6, correlationInvolution D pairSecond outer ^ 2
      ≤ weightSlack D pairSecond * weightSlack D outer)
    (hstarved : involSlackDeterminant (correlationInvolution D) (weightSlack D)
        pairFirst pairSecond hubThird
      ≤ pairSumValue (weightSlack D pairFirst) (weightSlack D pairSecond)
          (correlationInvolution D pairFirst pairSecond ^ 2)) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C := by
  have hpositive : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) :=
    fun atomIndex => lt_trans zero_lt_one (hheavy atomIndex)
  have hframe := isUnitTightFrameSix_unitAtomRows D hpositive hshare
  have hinvol : IsHollowInvolution (correlationInvolution D) := by
    have hbridge := isHollowInvolution_frameCorrelationInvolution hframe
    rwa [frameCorrelationInvolution_unitAtomRows] at hbridge
  obtain ⟨outer, hpairDistinct, hfirstOuter, hsecondOuter, hcell⟩ :=
    exists_mem_tripleSlackCell_of_starvedHub hinvol hbijective (weightSlack D)
      (sum_weightSlack_eq_four D hshare)
      (fun index => (weightSlack_pos D hheavy index).le) hpair hcrossFirst hcrossSecond hstarved
  refine ⟨{pairFirst, pairSecond, outer}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hpairDistinct, hfirstOuter]),
      Finset.card_insert_of_notMem (by simp [hsecondOuter]), Finset.card_singleton]
  · refine (dominates_triple_iff_posSemidef_slackHollowThree D (hpositive pairFirst)
      (hpositive pairSecond) (hpositive outer) hpairDistinct hfirstOuter hsecondOuter).mpr ?_
    rw [mem_tripleSlackCell_iff, correlationInvolution_apply_of_ne D hpairDistinct,
      correlationInvolution_apply_of_ne D hfirstOuter,
      correlationInvolution_apply_of_ne D hsecondOuter] at hcell
    exact hcell

/-! ## 6. The extremal candidate, and its band

The pen's V8 configuration -- a Mercedes triple in a plane together with three
lights on the cone `cos^2 psi = 2/3` at the same three azimuths -- is the hardest
known point of the band, and it was absent from the repository.  Only its
correlation matrix reaches the criterion, so it is landed here as an explicit
hollow symmetric involution; realizability is automatic, `(1 + M)/2` being a
rank-three projection of constant diagonal `1/2`. -/

/-- `1 / sqrt 3`, the cross-block magnitude of the extremal candidate: the cosine
between a plane direction and the cone direction of its own azimuth. -/
noncomputable def coneCross : ℝ := Real.sqrt 3 / 3

theorem coneCross_sq : coneCross ^ 2 = 1 / 3 := by
  rw [coneCross, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- **THE EXTREMAL CANDIDATE.**  Slots `0,1,2` carry the coplanar Mercedes triple
(all cosines `-1/2`), slots `3,4,5` the cone triple (all cosines `1/2`), and each
plane direction meets the cone direction of its own azimuth at `1/sqrt 3` and the
other two at `-1/(2 sqrt 3)`.  The row law reads
`1/4 + 1/4 + 1/3 + 1/12 + 1/12 = 1` at every atom. -/
noncomputable def mercedesConeInvolution : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, -1/2, -1/2, coneCross, -coneCross/2, -coneCross/2;
     -1/2, 0, -1/2, -coneCross/2, coneCross, -coneCross/2;
     -1/2, -1/2, 0, -coneCross/2, -coneCross/2, coneCross;
     coneCross, -coneCross/2, -coneCross/2, 0, 1/2, 1/2;
     -coneCross/2, coneCross, -coneCross/2, 1/2, 0, 1/2;
     -coneCross/2, -coneCross/2, coneCross, 1/2, 1/2, 0]

theorem isHollowInvolution_mercedesConeInvolution :
    IsHollowInvolution mercedesConeInvolution where
  symmetric := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [mercedesConeInvolution, Matrix.transpose_apply]
  square_eq_one := by
    have hsquare := coneCross_sq
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [mercedesConeInvolution, Matrix.mul_apply, Fin.sum_univ_six] <;>
      ring_nf <;>
      linarith [hsquare]
  diagonal_eq_zero := by
    intro index
    fin_cases index <;> simp [mercedesConeInvolution]

/-! ### The candidate's exact data -/

theorem mercedesConeInvolution_zeroOne : mercedesConeInvolution 0 1 = -(1 / 2) := by
  simp [mercedesConeInvolution]
  all_goals norm_num

theorem mercedesConeInvolution_zeroTwo : mercedesConeInvolution 0 2 = -(1 / 2) := by
  simp [mercedesConeInvolution]
  all_goals norm_num

theorem mercedesConeInvolution_oneTwo : mercedesConeInvolution 1 2 = -(1 / 2) := by
  simp [mercedesConeInvolution]
  all_goals norm_num

theorem mercedesConeInvolution_threeFour : mercedesConeInvolution 3 4 = 1 / 2 := by
  simp [mercedesConeInvolution]

theorem mercedesConeInvolution_threeFive : mercedesConeInvolution 3 5 = 1 / 2 := by
  simp [mercedesConeInvolution]

theorem mercedesConeInvolution_fourFive : mercedesConeInvolution 4 5 = 1 / 2 := by
  simp [mercedesConeInvolution]

/-- **THE MERCEDES TRIPLE IS COPLANAR.**  Its Gram determinant vanishes exactly --
this is what puts the candidate on the frontier of the band. -/
theorem hollowTripleBracket_mercedesCone_heavy :
    hollowTripleBracket mercedesConeInvolution 0 1 2 = 0 := by
  rw [hollowTripleBracket_eq_one_sub_sigma_add, hollowTripleSigma, hollowTripleProduct,
    mercedesConeInvolution_zeroOne, mercedesConeInvolution_zeroTwo,
    mercedesConeInvolution_oneTwo]
  norm_num

/-- The Mercedes triple's total edge mass is `3/4`. -/
theorem hollowTripleSigma_mercedesCone_heavy :
    hollowTripleSigma mercedesConeInvolution 0 1 2 = 3 / 4 := by
  rw [hollowTripleSigma, mercedesConeInvolution_zeroOne, mercedesConeInvolution_zeroTwo,
    mercedesConeInvolution_oneTwo]
  norm_num

theorem sq_mercedesConeInvolution_heavyEdge : mercedesConeInvolution 0 1 ^ 2 = 1 / 4 := by
  rw [mercedesConeInvolution_zeroOne]; norm_num

/-- Every entry out of a plane atom has square at most `1/3`, the cross-block
maximum.  This is the pairwise budget the band gate consumes. -/
theorem sq_mercedesConeInvolution_row_le (rowIndex colIndex : Fin 6) (hrow : rowIndex.val < 3) :
    mercedesConeInvolution rowIndex colIndex ^ 2 ≤ 1 / 3 := by
  have hsquare := coneCross_sq
  fin_cases rowIndex <;> [skip; skip; skip; (exact absurd hrow (by decide));
    (exact absurd hrow (by decide)); (exact absurd hrow (by decide))] <;>
    (fin_cases colIndex <;> simp [mercedesConeInvolution] <;> nlinarith [hsquare])

/-! ### The lower band: the light triple -/

/-- **THE LIGHT TRIPLE CARRIES THE LOWER BAND.**  Its determinant clause is
`tau_3 tau_4 tau_5 - (tau_3 + tau_4 + tau_5)/4 + 1/4`, which on `[1/2, infinity)^3`
equals `e_2(y)/2 + e_3(y)` in the shifted variables `y = tau - 1/2` and is
therefore nonnegative; the pairwise clauses read `1/4 <= tau tau`, the same
condition.  At a constant light slack `l` this factors as `(l - 1/2)^2 (l + 1)`, so
the light triple is exactly tied at `l = 1/2` and strictly dominating on either
side of it. -/
theorem mem_tripleSlackCell_mercedesCone_light {slack : Fin 6 → ℝ}
    (hthird : 1 / 2 ≤ slack 3) (hfourth : 1 / 2 ≤ slack 4) (hfifth : 1 / 2 ≤ slack 5) :
    slack ∈ tripleSlackCell mercedesConeInvolution 3 4 5 := by
  refine mem_tripleSlackCell_of_clauses (by linarith) (by linarith) (by linarith) ?_ ?_ ?_ ?_
  · rw [mercedesConeInvolution_threeFour]; nlinarith
  · rw [mercedesConeInvolution_threeFive]; nlinarith
  · rw [mercedesConeInvolution_fourFive]; nlinarith
  · rw [involSlackDeterminant, slackDeterminantThree, mercedesConeInvolution_threeFour,
      mercedesConeInvolution_threeFive, mercedesConeInvolution_fourFive]
    nlinarith [mul_nonneg (sub_nonneg.mpr hthird) (sub_nonneg.mpr hfourth),
      mul_nonneg (sub_nonneg.mpr hthird) (sub_nonneg.mpr hfifth),
      mul_nonneg (sub_nonneg.mpr hfourth) (sub_nonneg.mpr hfifth),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hthird) (sub_nonneg.mpr hfourth))
        (sub_nonneg.mpr hfifth)]

/-! ### The upper band: the starve-feed gate -/

/-- **THE EXACT GATE THRESHOLD.**  At a constant heavy slack `h` the candidate's
starvation condition is `0 <= (1 - h)(3 h^2 - h - 3/4)`, so the gate fires exactly
from the positive root `(1 + sqrt 10)/6` upward. -/
theorem mercedesCone_gateThreshold :
    3 * ((1 + Real.sqrt 10) / 6) ^ 2 - (1 + Real.sqrt 10) / 6 - 3 / 4 = 0 := by
  have hsquare : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  nlinarith [hsquare]

/-- The gate threshold sits strictly below `5/6`, so the two mechanisms overlap and
the candidate's band has no hole. -/
theorem mercedesCone_gateThreshold_lt_five_sixths : (1 + Real.sqrt 10) / 6 < 5 / 6 := by
  have hsquare : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  nlinarith [hsquare, Real.sqrt_nonneg 10]

/-- **THE CANDIDATE'S BAND IS COVERED.**  At every constant heavy slack in
`[2/3, 1]` -- the whole symmetric band, `2/3` being the U6 point and `1` the
three-atom deletion corner -- the twenty cells of the extremal candidate contain
the slack vector.  Two mechanisms, overlapping on `[(1 + sqrt 10)/6, 5/6]`:

* below `5/6` the light triple, whose clause factors as `(l - 1/2)^2 (l + 1)`;
* above `5/6` the starve-feed gate through a heavy pair, whose condition factors
  as `(h - 1)(12 h^2 - 4 h - 3) <= 0`.

So the pen's extremal configuration is NOT a counterexample; on its own band it is
covered with room to spare except at the deletion corner, where the light triple is
exactly tied. -/
theorem mercedesCone_covers_symmetricBand {slack : Fin 6 → ℝ} {heavyLevel : ℝ}
    (hfloor : 2 / 3 ≤ heavyLevel) (hcap : heavyLevel ≤ 1)
    (hheavy : ∀ index : Fin 6, index.val < 3 → slack index = heavyLevel)
    (hlight : ∀ index : Fin 6, 3 ≤ index.val → slack index = 4 / 3 - heavyLevel) :
    ∃ first second third : Fin 6, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ slack ∈ tripleSlackCell mercedesConeInvolution first second third := by
  have hzero : slack 0 = heavyLevel := hheavy 0 (by decide)
  have hone : slack 1 = heavyLevel := hheavy 1 (by decide)
  have htwo : slack 2 = heavyLevel := hheavy 2 (by decide)
  have hthree : slack 3 = 4 / 3 - heavyLevel := hlight 3 (by decide)
  have hfour : slack 4 = 4 / 3 - heavyLevel := hlight 4 (by decide)
  have hfive : slack 5 = 4 / 3 - heavyLevel := hlight 5 (by decide)
  rcases le_or_gt heavyLevel (5 / 6) with hlower | hupper
  · exact ⟨3, 4, 5, by decide, by decide, by decide,
      mem_tripleSlackCell_mercedesCone_light (by rw [hthree]; linarith)
        (by rw [hfour]; linarith) (by rw [hfive]; linarith)⟩
  · have hslackFloor : ∀ index : Fin 6, 4 / 3 - heavyLevel ≤ slack index := by
      intro index
      rcases lt_or_ge index.val 3 with hsmall | hlarge
      · rw [hheavy index hsmall]; linarith
      · rw [hlight index hlarge]
    have hslackNonneg : ∀ index : Fin 6, 0 ≤ slack index := by
      intro index
      have hbound := hslackFloor index
      linarith
    have hproductFloor : ∀ index : Fin 6, (1 : ℝ) / 3 ≤ heavyLevel * slack index := by
      intro index
      have hbound := hslackFloor index
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ heavyLevel)
          (by linarith : (0 : ℝ) ≤ slack index - (4 / 3 - heavyLevel)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - heavyLevel)
          (by linarith : (0 : ℝ) ≤ heavyLevel - 1 / 3)]
    have hslackSum : ∑ index, slack index = 4 := by
      rw [Fin.sum_univ_six, hzero, hone, htwo, hthree, hfour, hfive]
      ring
    have hbijective : Function.Bijective
        ![(3 : Fin 6), (4 : Fin 6), (5 : Fin 6), (2 : Fin 6), (0 : Fin 6), (1 : Fin 6)] := by
      decide
    have hstarved : involSlackDeterminant mercedesConeInvolution slack 0 1 2
        ≤ pairSumValue (slack 0) (slack 1) (mercedesConeInvolution 0 1 ^ 2) := by
      refine starvedHub_of_hollowTripleBracket_le hzero hone htwo ?_
      rw [hollowTripleBracket_mercedesCone_heavy, hollowTripleSigma_mercedesCone_heavy,
        sq_mercedesConeInvolution_heavyEdge]
      have hquadratic : (0 : ℝ) ≤ 3 * heavyLevel ^ 2 - heavyLevel - 3 / 4 := by
        nlinarith [sq_nonneg (heavyLevel - 5 / 6), hupper]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - heavyLevel) hquadratic]
    obtain ⟨outer, hpairDistinct, hfirstOuter, hsecondOuter, hcell⟩ :=
      exists_mem_tripleSlackCell_of_starvedHub isHollowInvolution_mercedesConeInvolution
        hbijective slack hslackSum hslackNonneg
        (by rw [sq_mercedesConeInvolution_heavyEdge, hzero, hone]; nlinarith)
        (fun outer => by
          rw [hzero]
          exact le_trans (sq_mercedesConeInvolution_row_le 0 outer (by decide))
            (hproductFloor outer))
        (fun outer => by
          rw [hone]
          exact le_trans (sq_mercedesConeInvolution_row_le 1 outer (by decide))
            (hproductFloor outer))
        hstarved
    exact ⟨0, 1, outer, hpairDistinct, hfirstOuter, hsecondOuter, hcell⟩

/-! ### The pen's reported frontier margin, corrected

The V8 brief reports a margin `+0.00915` at `tau = (9/10 x3, 13/30 x3)` and calls
it the frontier.  Both mixed species are exact rationals, and the reported figure
belongs to the FRUSTRATED one.  Neither is the frontier: the frontier of this
configuration is the deletion corner `h = 1`, where the light triple is tied. -/
theorem involSlackDeterminant_mercedesCone_at_nine_tenths {slack : Fin 6 → ℝ}
    (hheavy : ∀ index : Fin 6, index.val < 3 → slack index = 9 / 10)
    (hlight : ∀ index : Fin 6, 3 ≤ index.val → slack index = 13 / 30) :
    involSlackDeterminant mercedesConeInvolution slack 0 1 3 = 103 / 3000
      ∧ involSlackDeterminant mercedesConeInvolution slack 0 1 5 = 7 / 750 := by
  have hsquare := coneCross_sq
  have hzero : slack 0 = 9 / 10 := hheavy 0 (by decide)
  have hone : slack 1 = 9 / 10 := hheavy 1 (by decide)
  have hthree : slack 3 = 13 / 30 := hlight 3 (by decide)
  have hfive : slack 5 = 13 / 30 := hlight 5 (by decide)
  have hzeroThree : mercedesConeInvolution 0 3 = coneCross := by
    simp [mercedesConeInvolution]
  all_goals norm_num
  have honeThree : mercedesConeInvolution 1 3 = -coneCross / 2 := by
    simp [mercedesConeInvolution]
  have hzeroFive : mercedesConeInvolution 0 5 = -coneCross / 2 := by
    simp [mercedesConeInvolution]
  have honeFive : mercedesConeInvolution 1 5 = -coneCross / 2 := by
    simp [mercedesConeInvolution]
  constructor
  · rw [involSlackDeterminant, slackDeterminantThree, hzero, hone, hthree,
      mercedesConeInvolution_zeroOne, hzeroThree, honeThree]
    nlinarith [hsquare]
  · rw [involSlackDeterminant, slackDeterminantThree, hzero, hone, hfive,
      mercedesConeInvolution_zeroOne, hzeroFive, honeFive]
    nlinarith [hsquare]

end Gtz
