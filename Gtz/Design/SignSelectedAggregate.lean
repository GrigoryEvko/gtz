/-
# Sign-selected aggregation: the five-atom cell, and the exact reason counting stops

Lemma A (`Gtz.exists_nonneg_triangleProduct_of_card_ge`) forces a COHERENT triple
inside every five atoms of a rank-three design, and the sharpened taxonomy
(`Gtz.sum_sq_gt_one_of_coherentFailure_of_least`) says a coherent failure carries
two correlations whose squares sum above one.  Those two correlations are two
edges of a triangle, so THEY SHARE A VERTEX.  This file is the consequence of
that observation, in three layers.

## 1. The cell

The contrapositive of the sharpened taxonomy is a certificate strictly larger
than the shipped coherent half-box: a coherent triple dominates as soon as the
two largest squared correlations sum to at most one, whatever the third does.
Since any two edges of a triangle meet at a vertex, the honest quantifier is over
CHERRIES — paths `left - center - right` — and `IsLightCherry` names the
division-free form of `rho(center,left)^2 + rho(center,right)^2 <= 1`.

`dominates_of_coherentLightCherryTriangle` is that cell.  It contains
`dominates_of_coherentHalfBoxTriangle` strictly: `rho^2 <= 1/2` on all three
edges gives every cherry sum `<= 1`, and `exists_lightCherries_not_sq_le_half`
exhibits a coherent dominating point with an edge at `rho^2 = 16/25`.

Composing it with Lemma A gives the headline, and it is a NEW SPECIES of
certificate — a FIVE-ATOM cell rather than a per-triple one:

> **`exists_dominating_triple_of_five_lightCherries`.**  Five distinct atoms of an
> all-heavy rank-three design all of whose cherries are light contain a
> dominating triple.

Its hypothesis is a function of the squared correlations alone, so it looks
sign-blind; it is not reached by `not_signBlindGoodTripleCovering_seven`, because
that refutation is about per-TRIPLE sufficient conditions, and this one is an
existential over the triples of a five-set.  The check is concrete:
`icosaDesign` has every `rho^2 = 9/20`, so every five of its atoms satisfy the
hypothesis, and it does contain dominating triples.

The negative reading strengthens the shipped
`exists_normalizedPairing_sq_gt_half_of_five_atoms` on both sides — the
nonvanishing hypothesis is deleted (Lemma A's nonnegative form needs none, and
the cell only asks `0 <= product`), and the conclusion is upgraded from one edge
above `1/sqrt 2` to a whole heavy CHERRY:

> **`exists_heavyCherry_of_five_atoms`.**  If no triple dominates then any five
> distinct atoms carry a vertex with two incident correlations whose squares sum
> above one.

Graph form: the half-box graph `{2 p^2 <= u u}` of an all-failing design is
`K_5`-free, hence Turan-bounded — at most eighteen of the twenty-one pairs at
`m = 7`, so at least three pairs are heavy.

## 2. The conservation law the cherry has to be paid out of

A heavy cherry lives at one vertex, so the ROW LAW at that vertex caps it.  In
the excess-mass coordinate `w_c = t_c (l_c - 1)` — whose total is exactly `2` by
the budget law — the row law reads

> `x_b * sum_{d != b} w_d rho_bd^2 = l_b (1 - s_b)`

(`heavyExcess_mul_sum_excessMass_mul_normalizedPairing_sq`), and a heavy cherry
at `b` with legs `a, c` forces
`x_b * min(w_a, w_c) < l_b (1 - s_b)`
(`excessMass_min_lt_rowBudget_of_heavyCherry`).  Composed with Lemma A this is
`exists_heavyCherry_rowBudget_of_five_atoms` — the aggregation the campaign asked
for, written exactly.

## 3. Why it cannot close, with the number

The assembled bound is vacuous, and `rowBudget_heavyCherry_bound_at_uniform_iff`
measures the vacuity exactly: at the uniform equal-leverage stratum the charged
inequality reads `4/m < 3 - 9/m`, which holds **if and only if `m >= 5`** — which
is precisely the hypothesis Lemma A needed to produce the cherry.  The aggregation
returns its own antecedent.  No choice of which five atoms to feed it, and no
sharpening of the constants, changes that; the two thresholds are the same
inequality.  The reason is visible one level up.

It is vacuous, and the arithmetic says so to the digit.  At a uniform-weight
equal-leverage design — `t = 1/m`, `l = 3`, the stratum every classical witness
lives on — the row law gives

> `sum_{d != b} rho_bd^2 = 3 (m - 3) / 4`  over `m - 1` edges

(`sum_normalizedPairing_sq_of_uniform`), i.e. an average squared correlation of
`3(m-3) / (4(m-1))`, and

> that average equals the hinge threshold `1/2` EXACTLY at `m = 7`

(`rowAverage_eq_hinge_threshold_iff_seven`; at `m = 7` the six edges at every
atom carry squared correlations summing to exactly `3`, which is six times the
threshold — `sum_normalizedPairing_sq_uniform_seven`).  So at the frontier size
the row law permits EVERY edge to sit exactly at the hinge boundary: the counting
has zero slack, and for `m >= 7` it has none at all.  No count of the forced
heavy cherries against the row law can produce a contradiction at `(7,3)`.  This
is not a failure of bookkeeping; `1/2` and `(7,3)` are the same number.

Two honest riders.  The saturating configuration is not itself realisable — all
`rho^2 = 1/2` at leverage three means `gamma^2 = 2/9` on all twenty-one pairs,
i.e. seven equiangular lines in `R^3`, and the maximum is six (classical, cited
here and NOT mechanised) — so the exact saturation is a bound, not a design.  And the threshold in the five-atom cell
cannot be lowered from five to four by any argument local to the block:
`cherryWitnessDesign` is an all-heavy `(7,3)` design four of whose atoms are the
tetrahedron scaled by `4/5`, with all six correlations at `rho^2 = 256/529 < 1/2`
— every cherry light — and all four of their triples failing
(`cherryWitnessDesign_not_dominates_block`).  Five is exactly right.

## What this does NOT do

It closes no cell and produces no covering.  Section 1 certifies a region;
`icosaDesign` shows the region is nonempty where the box is empty, and nothing
here bounds the oriented product from below against the excess gap, which
`Gtz/Quantitative` records as the only remaining room.  Section 3 is a NO-GO for
one route, stated so it is not retried.  The five-atom cell's hypothesis is not
available at a hypothetical counterexample — that is exactly what section 1's
negative reading says — so the cell constrains, it does not decide.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.SignForcing
import Gtz.LinAlg.ElliptopeInterval
import Gtz.Quantitative.ChartHadamard
import Gtz.Reduction.BranchTransferConstants
import Gtz.Design.StressCertificate

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The pair-sum cell in scalars

The contrapositive of `sum_sq_gt_one_of_coherentFailure_of_least`, symmetrised
over the three ways of choosing which correlation is least in magnitude.  Any two
of the three correlations of a triple are two EDGES SHARING A VERTEX, so the
symmetric hypothesis is exactly "every cherry sum is at most one". -/

/-- **THE PAIR-SUM CELL.**  A coherent triple whose correlations sum in squares to
at most one over every pair has nonnegative bracket.  No compatibility hypothesis
is needed: each pair sum already bounds each square by one. -/
theorem elliptopeBracket_nonneg_of_coherent_of_pairSums_le_one
    {rhoFirst rhoSecond rhoThird : ℝ}
    (hcoherent : 0 ≤ rhoFirst * rhoSecond * rhoThird)
    (hpairFirstSecond : rhoFirst ^ 2 + rhoSecond ^ 2 ≤ 1)
    (hpairFirstThird : rhoFirst ^ 2 + rhoThird ^ 2 ≤ 1)
    (hpairSecondThird : rhoSecond ^ 2 + rhoThird ^ 2 ≤ 1) :
    0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird := by
  by_contra hnotNonneg
  have hfail : elliptopeBracket rhoFirst rhoSecond rhoThird < 0 := not_le.mp hnotNonneg
  have hcompatible : IsCompatibleTriple rhoFirst rhoSecond rhoThird := by
    refine ⟨?_, ?_, ?_⟩
    · linarith [sq_nonneg rhoSecond]
    · linarith [sq_nonneg rhoFirst]
    · linarith [sq_nonneg rhoFirst]
  rcases exists_pairSumSq_gt_one_of_isCoherentFailingTriple
    ⟨hcompatible, hcoherent, hfail⟩ with hpair | hpair | hpair
  · linarith
  · linarith
  · linarith

/-- The membership form: the pair-sum cell lands inside the elliptope, not merely
on the nonnegative side of the bracket. -/
theorem isElliptopePoint_of_coherent_of_pairSums_le_one
    {rhoFirst rhoSecond rhoThird : ℝ}
    (hcoherent : 0 ≤ rhoFirst * rhoSecond * rhoThird)
    (hpairFirstSecond : rhoFirst ^ 2 + rhoSecond ^ 2 ≤ 1)
    (hpairFirstThird : rhoFirst ^ 2 + rhoThird ^ 2 ≤ 1)
    (hpairSecondThird : rhoSecond ^ 2 + rhoThird ^ 2 ≤ 1) :
    IsElliptopePoint rhoFirst rhoSecond rhoThird := by
  refine ⟨⟨?_, ?_, ?_⟩, elliptopeBracket_nonneg_of_coherent_of_pairSums_le_one hcoherent
    hpairFirstSecond hpairFirstThird hpairSecondThird⟩
  · linarith [sq_nonneg rhoSecond]
  · linarith [sq_nonneg rhoFirst]
  · linarith [sq_nonneg rhoFirst]

/-- The pair-sum cell CONTAINS the coherent half-box cell: three squares at most
one half give every pair sum at most one. -/
theorem pairSums_le_one_of_sq_le_half {rhoFirst rhoSecond rhoThird : ℝ}
    (hfirst : rhoFirst ^ 2 ≤ 1 / 2) (hsecond : rhoSecond ^ 2 ≤ 1 / 2)
    (hthird : rhoThird ^ 2 ≤ 1 / 2) :
    rhoFirst ^ 2 + rhoSecond ^ 2 ≤ 1 ∧ rhoFirst ^ 2 + rhoThird ^ 2 ≤ 1
      ∧ rhoSecond ^ 2 + rhoThird ^ 2 ≤ 1 :=
  ⟨by linarith, by linarith, by linarith⟩

/-- **…and contains it STRICTLY.**  At `rho = (1/5, 1/5, 4/5)` the triple is
coherent, every pair sum is at most one (`2/25`, `17/25`, `17/25`), the bracket is
`43/125 > 0` — and the third square is `16/25`, well past the half-box threshold
`1/2`.  Exactly rational, as every constant in this campaign must be. -/
theorem exists_lightCherries_not_sq_le_half :
    ∃ rhoFirst rhoSecond rhoThird : ℝ,
      0 ≤ rhoFirst * rhoSecond * rhoThird
        ∧ rhoFirst ^ 2 + rhoSecond ^ 2 ≤ 1 ∧ rhoFirst ^ 2 + rhoThird ^ 2 ≤ 1
        ∧ rhoSecond ^ 2 + rhoThird ^ 2 ≤ 1
        ∧ ¬ rhoThird ^ 2 ≤ 1 / 2
        ∧ 0 ≤ elliptopeBracket rhoFirst rhoSecond rhoThird := by
  refine ⟨1 / 5, 1 / 5, 4 / 5, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_⟩
  rw [elliptopeBracket]; norm_num

/-! ## 2. Cherries at a design

`IsLightCherry D left center right` is the division-free reading of
`rho(center,left)^2 + rho(center,right)^2 <= 1`: the cherry centred at `center`
with legs `left` and `right` is light. -/

/-- A **light cherry**: the path `left - center - right` whose two normalized
correlations have squares summing to at most one, cleared of denominators. -/
def IsLightCherry (D : WeightedDesign m 3) (left center right : Fin m) : Prop :=
  atomPairing D center left ^ 2 * heavyExcess D right
      + atomPairing D center right ^ 2 * heavyExcess D left
    ≤ heavyExcess D left * heavyExcess D center * heavyExcess D right

/-- Lightness of a cherry does not depend on which leg is written first. -/
theorem isLightCherry_comm (D : WeightedDesign m 3) (left center right : Fin m) :
    IsLightCherry D left center right ↔ IsLightCherry D right center left := by
  rw [IsLightCherry, IsLightCherry]
  constructor <;> intro hlight <;> linarith [hlight,
    mul_comm (heavyExcess D left) (heavyExcess D right),
    mul_comm (heavyExcess D left * heavyExcess D center) (heavyExcess D right)]

/-- The cherry condition IS the normalized pair-sum bound. -/
theorem isLightCherry_iff_normalizedPairing_pairSum_le_one (D : WeightedDesign m 3)
    {left center right : Fin m} (hleftPos : 0 < heavyExcess D left)
    (hcenterPos : 0 < heavyExcess D center) (hrightPos : 0 < heavyExcess D right) :
    IsLightCherry D left center right
      ↔ normalizedPairing D center left ^ 2 + normalizedPairing D center right ^ 2 ≤ 1 := by
  rw [normalizedPairing_sq D hcenterPos hleftPos, normalizedPairing_sq D hcenterPos hrightPos,
    div_add_div _ _ (mul_pos hcenterPos hleftPos).ne' (mul_pos hcenterPos hrightPos).ne',
    div_le_one (by positivity), IsLightCherry]
  constructor <;> intro hbound <;> nlinarith [hbound, hcenterPos, hleftPos, hrightPos]

/-- A half-box edge pair gives a light cherry: `rho^2 <= 1/2` twice sums to one. -/
theorem isLightCherry_of_halfBoxPairs (D : WeightedDesign m 3) {left center right : Fin m}
    (hleftPos : 0 < heavyExcess D left) (hcenterPos : 0 < heavyExcess D center)
    (hrightPos : 0 < heavyExcess D right)
    (hleftEdge : 2 * atomPairing D center left ^ 2
      ≤ heavyExcess D center * heavyExcess D left)
    (hrightEdge : 2 * atomPairing D center right ^ 2
      ≤ heavyExcess D center * heavyExcess D right) :
    IsLightCherry D left center right := by
  rw [isLightCherry_iff_normalizedPairing_pairSum_le_one D hleftPos hcenterPos hrightPos]
  have hleftSq : normalizedPairing D center left ^ 2 ≤ 1 / 2 :=
    (normalizedPairing_sq_le_half_iff D hcenterPos hleftPos).mpr hleftEdge
  have hrightSq : normalizedPairing D center right ^ 2 ≤ 1 / 2 :=
    (normalizedPairing_sq_le_half_iff D hcenterPos hrightPos).mpr hrightEdge
  linarith

/-- **THE CHERRY CELL.**  A coherent triple of atoms with positive excess whose
three cherries are all light dominates.  The hypotheses are LOCAL — only the
three atoms need positive excess, not `AllHeavy D` — and the cell strictly
contains `dominates_of_coherentHalfBoxTriangle`, which is the special case where
every single square is at most one half. -/
theorem dominates_of_coherentLightCherryTriangle {D : WeightedDesign m 3}
    {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hfirstPos : 0 < heavyExcess D first) (hsecondPos : 0 < heavyExcess D second)
    (hthirdPos : 0 < heavyExcess D third)
    (hcoherent : 0 ≤ atomPairing D first second * atomPairing D first third
      * atomPairing D second third)
    (hcherryFirst : IsLightCherry D second first third)
    (hcherrySecond : IsLightCherry D first second third)
    (hcherryThird : IsLightCherry D first third second) :
    Dominates D {first, second, third} := by
  have hswap : ∀ atomFirst atomSecond : Fin m,
      normalizedPairing D atomFirst atomSecond ^ 2
        = normalizedPairing D atomSecond atomFirst ^ 2 := by
    intro atomFirst atomSecond
    rw [normalizedPairing, normalizedPairing, atomPairing_comm D atomFirst atomSecond,
      mul_comm (heavyExcess D atomFirst) (heavyExcess D atomSecond)]
  have hcoherentRho : 0 ≤ normalizedPairing D first second * normalizedPairing D first third
      * normalizedPairing D second third := by
    rw [normalizedPairing_product D hfirstPos hsecondPos hthirdPos]
    exact div_nonneg hcoherent (by positivity)
  have hpairFirst : normalizedPairing D first second ^ 2 + normalizedPairing D first third ^ 2
      ≤ 1 :=
    (isLightCherry_iff_normalizedPairing_pairSum_le_one D hsecondPos hfirstPos hthirdPos).mp
      hcherryFirst
  have hpairSecond : normalizedPairing D second first ^ 2
      + normalizedPairing D second third ^ 2 ≤ 1 :=
    (isLightCherry_iff_normalizedPairing_pairSum_le_one D hfirstPos hsecondPos hthirdPos).mp
      hcherrySecond
  have hpairThird : normalizedPairing D third first ^ 2
      + normalizedPairing D third second ^ 2 ≤ 1 :=
    (isLightCherry_iff_normalizedPairing_pairSum_le_one D hfirstPos hthirdPos hsecondPos).mp
      hcherryThird
  rw [hswap second first] at hpairSecond
  rw [hswap third first, hswap third second] at hpairThird
  refine (dominates_triple_iff_isElliptopePoint D hfirstSecond hfirstThird hsecondThird
    hfirstPos hsecondPos hthirdPos).mpr ?_
  exact isElliptopePoint_of_coherent_of_pairSums_le_one hcoherentRho hpairFirst hpairSecond
    hpairThird

/-! ## 3. The five-atom cell

Lemma A supplies the coherent triple; the cherry cell certifies it.  The
nonvanishing hypothesis of the shipped `exists_pos_atomPairingProduct_of_five_atoms`
is not needed here, because the hypothesis-free form of Lemma A gives a
NONNEGATIVE product and the cell asks for exactly that. -/

/-- **LEMMA A AT A DESIGN, WITHOUT THE NONVANISHING HYPOTHESIS.**  Any five atoms
of a rank-three design contain a triple of distinct indices whose oriented pairing
product is nonnegative.  Compare `exists_pos_atomPairingProduct_of_five_atoms`,
which gets a STRICT product but has to assume every pairing nonzero; every cell in
this file reads `0 <= product`, so the weaker conclusion costs nothing and the
hypothesis is deleted. -/
theorem exists_nonneg_atomPairingProduct_of_five_atoms (D : WeightedDesign m 3)
    (pick : Fin 5 → Fin m) :
    ∃ first second third : Fin 5, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 ≤ atomPairing D (pick first) (pick second)
          * atomPairing D (pick first) (pick third)
          * atomPairing D (pick second) (pick third) := by
  have hcard : Fintype.card (Fin 3) + 2 ≤ Fintype.card (Fin 5) := by simp
  have hthree : 3 ≤ Fintype.card (Fin 5) := by simp
  obtain ⟨first, second, third, hfs, hft, hst, hnonneg⟩ :=
    exists_nonneg_triangleProduct_of_card_ge (fun index => D.atom (pick index)) hcard hthree
  refine ⟨first, second, third, hfs, hft, hst, ?_⟩
  simpa only [triangleProduct, atomPairing] using hnonneg

/-- **THE FIVE-ATOM CELL.**  Five distinct atoms of positive excess, every cherry
among them light, contain a dominating triple.

This is a certificate of a new shape: its hypothesis is a condition on a FIVE-set
and its conclusion is an existential over that set's triples, where every shipped
cell is a per-triple sufficient condition.  That is why the sign-blind refutation
`not_signBlindGoodTripleCovering_seven` does not reach it even though the
hypothesis reads only squared pairings — the sign enters through Lemma A, in the
proof, not through the statement. -/
theorem exists_dominating_triple_of_five_lightCherries {D : WeightedDesign m 3}
    (pick : Fin 5 → Fin m) (hinjective : Function.Injective pick)
    (hexcess : ∀ index : Fin 5, 0 < heavyExcess D (pick index))
    (hcherry : ∀ left center right : Fin 5, left ≠ center → right ≠ center → left ≠ right →
      IsLightCherry D (pick left) (pick center) (pick right)) :
    ∃ first second third : Fin 5, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ Dominates D {pick first, pick second, pick third} := by
  obtain ⟨first, second, third, hfs, hft, hst, hcoherent⟩ :=
    exists_nonneg_atomPairingProduct_of_five_atoms D pick
  refine ⟨first, second, third, hfs, hft, hst, ?_⟩
  exact dominates_of_coherentLightCherryTriangle (fun heq => hfs (hinjective heq))
    (fun heq => hft (hinjective heq)) (fun heq => hst (hinjective heq))
    (hexcess first) (hexcess second) (hexcess third) hcoherent
    (hcherry second first third hfs.symm hft.symm hst)
    (hcherry first second third hfs hst.symm hft)
    (hcherry first third second hft hst hfs)

/-- The half-box reading of the five-atom cell: five distinct atoms with every
pair satisfying `2 p^2 <= u u` contain a dominating triple. -/
theorem exists_dominating_triple_of_five_halfBoxPairs {D : WeightedDesign m 3}
    (pick : Fin 5 → Fin m) (hinjective : Function.Injective pick)
    (hexcess : ∀ index : Fin 5, 0 < heavyExcess D (pick index))
    (hedge : ∀ left right : Fin 5, left ≠ right →
      2 * atomPairing D (pick left) (pick right) ^ 2
        ≤ heavyExcess D (pick left) * heavyExcess D (pick right)) :
    ∃ first second third : Fin 5, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ Dominates D {pick first, pick second, pick third} := by
  refine exists_dominating_triple_of_five_lightCherries pick hinjective hexcess ?_
  intro left center right hleftCenter hrightCenter _
  exact isLightCherry_of_halfBoxPairs D (hexcess left) (hexcess center) (hexcess right)
    (hedge center left hleftCenter.symm) (hedge center right hrightCenter.symm)

/-- **THE FIVE-ATOM CELL IS NOT VACUOUS**, and it fires exactly where every
sign-blind per-triple cell is empty.  At `icosaDesign` every cherry is light —
`p^2 x + p^2 x = 36/5` against `x x x = 8` — while the box graph is EMPTY
(`icosaDesign_no_isBoxGoodPair`), each of the fifteen pairs sitting at
`rho^2 = 9/20`, outside the box threshold `1/4`. -/
theorem icosaDesign_isLightCherry {left center right : Fin 6}
    (hleftCenter : left ≠ center) (hrightCenter : right ≠ center) :
    IsLightCherry icosaDesign left center right := by
  rw [IsLightCherry, icosaDesign_heavyExcess left, icosaDesign_heavyExcess center,
    icosaDesign_heavyExcess right, icosaDesign_atomPairing_sq_of_ne hleftCenter.symm,
    icosaDesign_atomPairing_sq_of_ne hrightCenter.symm]
  norm_num

/-- The five-atom cell applied at `icosaDesign`: any five of its six atoms contain
a dominating triple.  A non-vacuity control, in the sense of `Gtz/Core/Sanity`. -/
theorem exists_dominating_triple_icosaDesign_of_five (pick : Fin 5 → Fin 6)
    (hinjective : Function.Injective pick) :
    ∃ first second third : Fin 5, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ Dominates icosaDesign {pick first, pick second, pick third} := by
  refine exists_dominating_triple_of_five_lightCherries pick hinjective
    (fun index => icosaDesign_heavyExcess_pos (pick index)) ?_
  intro left center right hleftCenter hrightCenter _
  exact icosaDesign_isLightCherry (fun heq => hleftCenter (hinjective heq))
    (fun heq => hrightCenter (hinjective heq))

/-- **THE NEGATIVE READING.**  In an all-heavy rank-three design with no dominating
triple, any five distinct atoms carry a HEAVY CHERRY: a vertex with two incident
correlations whose squares sum above one.

Two strengthenings of `exists_normalizedPairing_sq_gt_half_of_five_atoms`: the
nonvanishing hypothesis on the ten pairings is deleted, and the conclusion locates
two edges at one vertex instead of one edge anywhere.  It is the second that
matters downstream — a heavy cherry is charged to a single row of the row law. -/
theorem exists_heavyCherry_of_five_atoms {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) (pick : Fin 5 → Fin m) (hinjective : Function.Injective pick)
    (hnoTriple : ∀ first second third : Fin m, first ≠ second → first ≠ third →
      second ≠ third → ¬ Dominates D {first, second, third}) :
    ∃ left center right : Fin 5, left ≠ center ∧ right ≠ center ∧ left ≠ right
      ∧ 1 < normalizedPairing D (pick center) (pick left) ^ 2
          + normalizedPairing D (pick center) (pick right) ^ 2 := by
  by_contra hnone
  push Not at hnone
  have hcherry : ∀ left center right : Fin 5, left ≠ center → right ≠ center → left ≠ right →
      IsLightCherry D (pick left) (pick center) (pick right) := by
    intro left center right hleftCenter hrightCenter hleftRight
    rw [isLightCherry_iff_normalizedPairing_pairSum_le_one D
      (allHeavy_heavyExcess_pos hheavy (pick left)) (allHeavy_heavyExcess_pos hheavy (pick center))
      (allHeavy_heavyExcess_pos hheavy (pick right))]
    exact hnone left center right hleftCenter hrightCenter hleftRight
  obtain ⟨first, second, third, hfs, hft, hst, hdominates⟩ :=
    exists_dominating_triple_of_five_lightCherries pick hinjective
      (fun index => allHeavy_heavyExcess_pos hheavy (pick index)) hcherry
  exact hnoTriple _ _ _ (fun heq => hfs (hinjective heq)) (fun heq => hft (hinjective heq))
    (fun heq => hst (hinjective heq)) hdominates

/-! ## 4. The half-box graph is `K_5`-free, and the Turan count

The graph form of the five-atom cell.  Compare `boxGoodGraph`, whose refutation
`not_boxGoodTriangleCovering_six` is triangle-level; here the threshold doubles
from `4 p^2 <= u u` to `2 p^2 <= u u` and the forbidden clique grows from three to
five.  The count is INFRASTRUCTURE, not progress: `icosaDesign` has all fifteen
pairs half-box-good and dominates, so nothing about a covering follows. -/

/-- A pair is **half-box good** when `2 p^2 <= u u`, equivalently `rho^2 <= 1/2` —
the edge condition of the coherent half-box cell. -/
def IsHalfBoxGoodPair (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) : Prop :=
  2 * atomPairing D atomFirst atomSecond ^ 2
    ≤ heavyExcess D atomFirst * heavyExcess D atomSecond

theorem isHalfBoxGoodPair_comm (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    IsHalfBoxGoodPair D atomFirst atomSecond ↔ IsHalfBoxGoodPair D atomSecond atomFirst := by
  rw [IsHalfBoxGoodPair, IsHalfBoxGoodPair, atomPairing_comm D atomFirst atomSecond,
    mul_comm (heavyExcess D atomSecond) (heavyExcess D atomFirst)]

/-- The **half-box graph** on the atoms. -/
def halfBoxGoodGraph (D : WeightedDesign m 3) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (IsHalfBoxGoodPair D)

@[simp] theorem halfBoxGoodGraph_adj (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    (halfBoxGoodGraph D).Adj atomFirst atomSecond
      ↔ atomFirst ≠ atomSecond ∧ IsHalfBoxGoodPair D atomFirst atomSecond := by
  rw [halfBoxGoodGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hgood | hgood⟩
    · exact ⟨hne, hgood⟩
    · exact ⟨hne, (isHalfBoxGoodPair_comm D atomSecond atomFirst).mp hgood⟩
  · rintro ⟨hne, hgood⟩
    exact ⟨hne, Or.inl hgood⟩

/-- **THE HALF-BOX GRAPH OF AN ALL-FAILING DESIGN HAS NO `K_5`.**  Five mutually
half-box-good atoms contain a dominating triple by the five-atom cell. -/
theorem cliqueFree_five_halfBoxGoodGraph_of_forall_not_dominates {D : WeightedDesign m 3}
    (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin m), triple.card = 3 → ¬ Dominates D triple) :
    (halfBoxGoodGraph D).CliqueFree 5 := by
  intro clique hclique
  have hcard : clique.card = 5 := hclique.2
  set pick : Fin 5 → Fin m := fun index => clique.orderEmbOfFin hcard index with hpick
  have hmem : ∀ index : Fin 5, pick index ∈ clique := fun index =>
    clique.orderEmbOfFin_mem hcard index
  have hinjective : Function.Injective pick := (clique.orderEmbOfFin hcard).injective
  have hedge : ∀ left right : Fin 5, left ≠ right →
      2 * atomPairing D (pick left) (pick right) ^ 2
        ≤ heavyExcess D (pick left) * heavyExcess D (pick right) := by
    intro left right hne
    have hadj : (halfBoxGoodGraph D).Adj (pick left) (pick right) :=
      hclique.1 (Finset.mem_coe.mpr (hmem left)) (Finset.mem_coe.mpr (hmem right))
        (fun heq => hne (hinjective heq))
    exact ((halfBoxGoodGraph_adj D _ _).mp hadj).2
  obtain ⟨first, second, third, hfs, hft, hst, hdominates⟩ :=
    exists_dominating_triple_of_five_halfBoxPairs pick hinjective
      (fun index => allHeavy_heavyExcess_pos hheavy (pick index)) hedge
  refine hnone {pick first, pick second, pick third} ?_ hdominates
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    exact fun heq => hst (hinjective heq)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (heq | heq)
    · exact hfs (hinjective heq)
    · exact hft (hinjective heq)

/-- **THE TURAN COUNT.**  A `K_5`-free graph on `m` vertices has at most
`(m^2 - (m % 4)^2) * 3 / 8 + (m % 4).choose 2` edges, so an all-failing all-heavy
design has at most that many half-box-good pairs. -/
theorem card_edgeFinset_halfBoxGoodGraph_le (D : WeightedDesign m 3)
    [DecidableRel (halfBoxGoodGraph D).Adj] (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin m), triple.card = 3 → ¬ Dominates D triple) :
    (halfBoxGoodGraph D).edgeFinset.card
      ≤ (m ^ 2 - (m % 4) ^ 2) * 3 / 8 + (m % 4).choose 2 := by
  have hfree : (halfBoxGoodGraph D).CliqueFree (4 + 1) :=
    cliqueFree_five_halfBoxGoodGraph_of_forall_not_dominates hheavy hnone
  have hbound := hfree.card_edgeFinset_le (r := 4)
  simpa only [Fintype.card_fin] using hbound

/-- At the frontier size: at most eighteen of the twenty-one pairs are half-box
good, so at least THREE pairs carry `rho^2 > 1/2`. -/
theorem card_edgeFinset_halfBoxGoodGraph_le_seven (D : WeightedDesign 7 3)
    [DecidableRel (halfBoxGoodGraph D).Adj] (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin 7), triple.card = 3 → ¬ Dominates D triple) :
    (halfBoxGoodGraph D).edgeFinset.card ≤ 18 := by
  have hbound := card_edgeFinset_halfBoxGoodGraph_le D hheavy hnone
  norm_num at hbound
  exact hbound

/-- At `m = 6`: at most thirteen of the fifteen pairs. -/
theorem card_edgeFinset_halfBoxGoodGraph_le_six (D : WeightedDesign 6 3)
    [DecidableRel (halfBoxGoodGraph D).Adj] (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin 6), triple.card = 3 → ¬ Dominates D triple) :
    (halfBoxGoodGraph D).edgeFinset.card ≤ 13 := by
  have hbound := card_edgeFinset_halfBoxGoodGraph_le D hheavy hnone
  norm_num at hbound
  exact hbound

/-- The complementary count: at least `C(m,2)` minus the Turan number of the pairs
are half-box BAD — at least three of the twenty-one at the frontier size. -/
theorem card_edgeFinset_compl_halfBoxGoodGraph_ge (D : WeightedDesign m 3)
    [DecidableRel (halfBoxGoodGraph D).Adj] [DecidableRel (halfBoxGoodGraph D)ᶜ.Adj]
    (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin m), triple.card = 3 → ¬ Dominates D triple) :
    m.choose 2 - ((m ^ 2 - (m % 4) ^ 2) * 3 / 8 + (m % 4).choose 2)
      ≤ (halfBoxGoodGraph D)ᶜ.edgeFinset.card := by
  classical
  have hbound := card_edgeFinset_halfBoxGoodGraph_le D hheavy hnone
  have hdisjoint : Disjoint (halfBoxGoodGraph D).edgeFinset (halfBoxGoodGraph D)ᶜ.edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
  have hunion : (halfBoxGoodGraph D).edgeFinset ∪ (halfBoxGoodGraph D)ᶜ.edgeFinset
      = (⊤ : SimpleGraph (Fin m)).edgeFinset := by
    ext edge
    simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset]
    induction edge using Sym2.ind with
    | _ leftVertex rightVertex =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj, SimpleGraph.top_adj]
      constructor
      · rintro (hadjacent | ⟨hne, _⟩)
        · exact (halfBoxGoodGraph D).ne_of_adj hadjacent
        · exact hne
      · intro hne
        by_cases hadjacent : (halfBoxGoodGraph D).Adj leftVertex rightVertex
        · exact Or.inl hadjacent
        · exact Or.inr ⟨hne, hadjacent⟩
  have htotal : (halfBoxGoodGraph D).edgeFinset.card + (halfBoxGoodGraph D)ᶜ.edgeFinset.card
      = m.choose 2 := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  omega

/-- The frontier instance: at least three of the twenty-one pairs are half-box bad. -/
theorem card_edgeFinset_compl_halfBoxGoodGraph_ge_seven (D : WeightedDesign 7 3)
    [DecidableRel (halfBoxGoodGraph D).Adj] [DecidableRel (halfBoxGoodGraph D)ᶜ.Adj]
    (hheavy : AllHeavy D)
    (hnone : ∀ triple : Finset (Fin 7), triple.card = 3 → ¬ Dominates D triple) :
    3 ≤ (halfBoxGoodGraph D)ᶜ.edgeFinset.card := by
  have hbound := card_edgeFinset_compl_halfBoxGoodGraph_ge D hheavy hnone
  have hchoose : Nat.choose 7 2 = 21 := by decide
  norm_num at hbound
  omega

/-! ## 5. The excess-mass coordinate and the row law it carries

`excessMass D c = t_c (l_c - 1)` is the weight the row law uses once the pairings
are normalized.  Its total is exactly `rank - 1 = 2` — the budget law — and in it
the row law becomes a statement about the squared correlations directly. -/

/-- The **excess mass** `w_c = t_c (l_c - 1)` of an atom. -/
def excessMass (D : WeightedDesign m 3) (atomIndex : Fin m) : ℝ :=
  D.weight atomIndex * heavyExcess D atomIndex

theorem excessMass_pos {D : WeightedDesign m 3} (hheavy : AllHeavy D) (atomIndex : Fin m) :
    0 < excessMass D atomIndex :=
  mul_pos (D.weight_pos atomIndex) (allHeavy_heavyExcess_pos hheavy atomIndex)

/-- **THE BUDGET LAW IN EXCESS MASS.**  The excess masses of a rank-three design
sum to exactly two.  Transported from the unconditional
`Gtz.sum_weight_mul_leverage_sub_one`. -/
theorem sum_excessMass_eq_two (D : WeightedDesign m 3) :
    ∑ atomIndex, excessMass D atomIndex = 2 := by
  have hbudget := sum_weight_mul_leverage_sub_one D
  simp only [excessMass, heavyExcess]
  rw [hbudget]
  norm_num

/-- The raw pairing square is the normalized one scaled by the two excesses. -/
theorem atomPairing_sq_eq_normalizedPairing_sq_mul (D : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirstPos : 0 < heavyExcess D atomFirst)
    (hsecondPos : 0 < heavyExcess D atomSecond) :
    atomPairing D atomFirst atomSecond ^ 2
      = normalizedPairing D atomFirst atomSecond ^ 2
        * (heavyExcess D atomFirst * heavyExcess D atomSecond) := by
  rw [normalizedPairing_sq D hfirstPos hsecondPos,
    div_mul_cancel₀ _ (mul_pos hfirstPos hsecondPos).ne']

/-- **THE ROW LAW IN NORMALIZED COORDINATES.**  The excess-mass-weighted sum of the
squared correlations at an atom is its leverage times its share deficit, divided by
its excess — written division-free.  With `sum_excessMass_eq_two` this is a genuine
averaging statement: the total weight available at every row is `2 - w_b`. -/
theorem heavyExcess_mul_sum_excessMass_mul_normalizedPairing_sq {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) (center : Fin m) :
    heavyExcess D center
        * ∑ other ∈ Finset.univ.erase center,
            excessMass D other * normalizedPairing D center other ^ 2
      = leverageOf (D.atom center) * (1 - atomShare D center) := by
  have hcenterPos := allHeavy_heavyExcess_pos hheavy center
  have hrow := sum_weight_mul_sq_atomPairing D center
  have hterm : ∀ other ∈ Finset.univ.erase center,
      heavyExcess D center * (excessMass D other * normalizedPairing D center other ^ 2)
        = D.weight other * atomPairing D center other ^ 2 := by
    intro other _
    have hotherPos := allHeavy_heavyExcess_pos hheavy other
    rw [atomPairing_sq_eq_normalizedPairing_sq_mul D hcenterPos hotherPos, excessMass]
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm]
  have hself : D.weight center * atomPairing D center center ^ 2
      = D.weight center * leverageOf (D.atom center) ^ 2 := by
    rw [atomPairing, leverageOf, dotProduct]
    congr 2
    exact Finset.sum_congr rfl fun coord _ => (sq (D.atom center coord)).symm
  have hsplit : (∑ other ∈ Finset.univ.erase center,
        D.weight other * atomPairing D center other ^ 2)
      + D.weight center * atomPairing D center center ^ 2
      = ∑ other, D.weight other * atomPairing D center other ^ 2 :=
    Finset.sum_erase_add _ _ (Finset.mem_univ center)
  have hfull : ∑ other, D.weight other * atomPairing D center other ^ 2
      = leverageOf (D.atom center) := by
    simpa only [atomPairing] using hrow
  rw [atomShare]
  nlinarith [hsplit, hfull, hself]

/-- **A HEAVY CHERRY IS CHARGED TO ONE ROW.**  Its two edges meet at the centre, so
the row law at the centre pays for both, and the lighter of the two legs is bounded
by the row budget outright. -/
theorem excessMass_min_lt_rowBudget_of_heavyCherry {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) {left center right : Fin m}
    (hleftCenter : left ≠ center) (hrightCenter : right ≠ center) (hleftRight : left ≠ right)
    (hheavyCherry : 1 < normalizedPairing D center left ^ 2
      + normalizedPairing D center right ^ 2) :
    heavyExcess D center * min (excessMass D left) (excessMass D right)
      < leverageOf (D.atom center) * (1 - atomShare D center) := by
  have hcenterPos := allHeavy_heavyExcess_pos hheavy center
  have hrowLaw := heavyExcess_mul_sum_excessMass_mul_normalizedPairing_sq hheavy center
  have hminPos : 0 < min (excessMass D left) (excessMass D right) :=
    lt_min (excessMass_pos hheavy left) (excessMass_pos hheavy right)
  have hsubset : ({left, right} : Finset (Fin m)) ⊆ Finset.univ.erase center := by
    intro index hindex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hindex
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ index⟩
    rcases hindex with rfl | rfl
    · exact hleftCenter
    · exact hrightCenter
  have hnonneg : ∀ other ∈ Finset.univ.erase center,
      other ∉ ({left, right} : Finset (Fin m)) →
      0 ≤ excessMass D other * normalizedPairing D center other ^ 2 := by
    intro other _ _
    exact mul_nonneg (excessMass_pos hheavy other).le (sq_nonneg _)
  have hpartial : (excessMass D left * normalizedPairing D center left ^ 2
        + excessMass D right * normalizedPairing D center right ^ 2)
      ≤ ∑ other ∈ Finset.univ.erase center,
          excessMass D other * normalizedPairing D center other ^ 2 := by
    have hpairSum := Finset.sum_pair hleftRight
      (f := fun other => excessMass D other * normalizedPairing D center other ^ 2)
    rw [← hpairSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have hminBound : min (excessMass D left) (excessMass D right)
      < excessMass D left * normalizedPairing D center left ^ 2
        + excessMass D right * normalizedPairing D center right ^ 2 := by
    nlinarith [min_le_left (excessMass D left) (excessMass D right),
      min_le_right (excessMass D left) (excessMass D right),
      sq_nonneg (normalizedPairing D center left), sq_nonneg (normalizedPairing D center right),
      hheavyCherry, hminPos]
  nlinarith [hrowLaw, hpartial, hminBound, hcenterPos]

/-! ## 6. The zero-slack identity: why the counting stops at `(7,3)`

Everything above is exact.  What follows is the reason it cannot be pushed: at the
uniform-weight equal-leverage stratum — the one `tetraDesign`, `icosaDesign`,
`splitSevenDesign` and every other classical witness lives on — the row law's
average squared correlation is `3(m-3) / (4(m-1))`, and that equals the hinge
threshold `1/2` EXACTLY at `m = 7`. -/

/-- **THE ROW SUM AT THE UNIFORM EQUAL-LEVERAGE STRATUM.**  With `t = 1/m` and every
leverage three, the squared correlations at any atom sum to `3(m-3)/4` over the
`m - 1` other atoms. -/
theorem sum_normalizedPairing_sq_of_uniform {D : WeightedDesign m 3}
    (huniform : ∀ atomIndex : Fin m, D.weight atomIndex = 1 / m)
    (hleverage : ∀ atomIndex : Fin m, leverageOf (D.atom atomIndex) = 3)
    (center : Fin m) :
    ∑ other ∈ Finset.univ.erase center, normalizedPairing D center other ^ 2
      = 3 * ((m : ℝ) - 3) / 4 := by
  have hheavy : AllHeavy D := fun atomIndex => by rw [hleverage atomIndex]; norm_num
  have hsizePos : 0 < m := Fin.pos center
  have hsizeCast : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hsizePos
  have hexcess : ∀ atomIndex : Fin m, heavyExcess D atomIndex = 2 := by
    intro atomIndex
    rw [heavyExcess, hleverage atomIndex]; norm_num
  have hmass : ∀ atomIndex : Fin m, excessMass D atomIndex = 2 / m := by
    intro atomIndex
    rw [excessMass, huniform atomIndex, hexcess atomIndex]; ring
  have hshare : atomShare D center = 3 / m := by
    rw [atomShare, huniform center, hleverage center]; ring
  have hrowLaw := heavyExcess_mul_sum_excessMass_mul_normalizedPairing_sq hheavy center
  rw [hexcess center, hleverage center, hshare] at hrowLaw
  have hrewrite : ∑ other ∈ Finset.univ.erase center,
      excessMass D other * normalizedPairing D center other ^ 2
      = (2 / (m : ℝ)) * ∑ other ∈ Finset.univ.erase center,
          normalizedPairing D center other ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun other _ => by rw [hmass other]
  rw [hrewrite] at hrowLaw
  field_simp at hrowLaw ⊢
  linarith

/-- **THE COINCIDENCE THAT STOPS THE ARGUMENT.**  The row sum `3(m-3)/4` equals
`m - 1` times the hinge threshold `1/2` exactly at `m = 7`.  Below seven the
counting has slack, above it there is none, and AT it there is exactly none: the
threshold that the sharpened taxonomy forces and the budget that the conservation
law supplies are the same number at the frontier size. -/
theorem rowAverage_eq_hinge_threshold_iff_seven (size : ℕ) :
    3 * ((size : ℝ) - 3) / 4 = ((size : ℝ) - 1) / 2 ↔ size = 7 := by
  constructor
  · intro hequal
    have hcast : ((size : ℝ)) = 7 := by linarith
    exact_mod_cast hcast
  · rintro rfl
    norm_num

/-- The frontier instance, spelled out: at a uniform equal-leverage `(7,3)` design
the six edges at every atom carry squared correlations summing to exactly `3` —
six times the hinge threshold, with zero slack.  Since `k` edge-disjoint heavy
cherries at one vertex consume more than `k` of that budget, a vertex supports at
most TWO of them — and nothing above forces even one at a prescribed vertex. -/
theorem sum_normalizedPairing_sq_uniform_seven {D : WeightedDesign 7 3}
    (huniform : ∀ atomIndex : Fin 7, D.weight atomIndex = 1 / 7)
    (hleverage : ∀ atomIndex : Fin 7, leverageOf (D.atom atomIndex) = 3)
    (center : Fin 7) :
    ∑ other ∈ Finset.univ.erase center, normalizedPairing D center other ^ 2 = 3 := by
  have hsum := sum_normalizedPairing_sq_of_uniform (D := D) (by simpa using huniform)
    hleverage center
  rw [hsum]
  norm_num

/-- The same identity at `m = 6`, where the icosahedron lives: the five edges at
every atom sum to `9/4`, an average of `9/20` — strictly below the threshold, which
is the slack `(6,3)` has and `(7,3)` does not. -/
theorem sum_normalizedPairing_sq_uniform_six {D : WeightedDesign 6 3}
    (huniform : ∀ atomIndex : Fin 6, D.weight atomIndex = 1 / 6)
    (hleverage : ∀ atomIndex : Fin 6, leverageOf (D.atom atomIndex) = 3)
    (center : Fin 6) :
    ∑ other ∈ Finset.univ.erase center, normalizedPairing D center other ^ 2 = 9 / 4 := by
  have hsum := sum_normalizedPairing_sq_of_uniform (D := D) (by simpa using huniform)
    hleverage center
  rw [hsum]
  norm_num

/-- **THE AGGREGATION, ASSEMBLED.**  This is the statement the campaign asked for:
in an all-heavy rank-three design with no dominating triple, every five distinct
atoms carry a centre `b` and two legs `a, c` at which the row law is charged,

> `x_b * min(w_a, w_c) < l_b (1 - s_b)`,

with `w` the excess mass.  It is the composite of Lemma A, the sharpened taxonomy
and the row law, and it is exact. -/
theorem exists_heavyCherry_rowBudget_of_five_atoms {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) (pick : Fin 5 → Fin m) (hinjective : Function.Injective pick)
    (hnoTriple : ∀ first second third : Fin m, first ≠ second → first ≠ third →
      second ≠ third → ¬ Dominates D {first, second, third}) :
    ∃ left center right : Fin 5, left ≠ center ∧ right ≠ center ∧ left ≠ right
      ∧ heavyExcess D (pick center)
            * min (excessMass D (pick left)) (excessMass D (pick right))
          < leverageOf (D.atom (pick center)) * (1 - atomShare D (pick center)) := by
  obtain ⟨left, center, right, hleftCenter, hrightCenter, hleftRight, hheavyCherry⟩ :=
    exists_heavyCherry_of_five_atoms hheavy pick hinjective hnoTriple
  refine ⟨left, center, right, hleftCenter, hrightCenter, hleftRight, ?_⟩
  exact excessMass_min_lt_rowBudget_of_heavyCherry hheavy
    (fun heq => hleftCenter (hinjective heq)) (fun heq => hrightCenter (hinjective heq))
    (fun heq => hleftRight (hinjective heq)) hheavyCherry

/-- **AND HERE IS EXACTLY HOW MUCH IT SAYS: NOTHING.**  At the uniform equal-leverage
stratum the charged inequality `x_b * min(w_a, w_c) < l_b (1 - s_b)` reads
`4/m < 3 - 9/m`, which holds if and only if `5 <= m` — precisely the hypothesis
Lemma A needed in order to produce the cherry at all.

So the aggregation returns its own antecedent.  That is the sharpest form of the
no-go: it is not that the bound is weak, it is that on the stratum where every
classical witness lives the bound is LOGICALLY EQUIVALENT to `m >= 5`, and no
choice of which five atoms to feed it can change that. -/
theorem rowBudget_heavyCherry_bound_at_uniform_iff {D : WeightedDesign m 3}
    (huniform : ∀ atomIndex : Fin m, D.weight atomIndex = 1 / m)
    (hleverage : ∀ atomIndex : Fin m, leverageOf (D.atom atomIndex) = 3)
    (left center right : Fin m) :
    heavyExcess D center * min (excessMass D left) (excessMass D right)
        < leverageOf (D.atom center) * (1 - atomShare D center)
      ↔ 5 ≤ m := by
  have hsizePos : 0 < m := Fin.pos center
  have hsizeCast : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hsizePos
  have hexcess : ∀ atomIndex : Fin m, heavyExcess D atomIndex = 2 := by
    intro atomIndex
    rw [heavyExcess, hleverage atomIndex]; norm_num
  have hmass : ∀ atomIndex : Fin m, excessMass D atomIndex = 2 / m := by
    intro atomIndex
    rw [excessMass, huniform atomIndex, hexcess atomIndex]; ring
  have hshare : atomShare D center = 3 / m := by
    rw [atomShare, huniform center, hleverage center]; ring
  rw [hexcess center, hleverage center, hshare, hmass left, hmass right, min_self]
  rw [show (2 : ℝ) * (2 / (m : ℝ)) = 4 / (m : ℝ) from by ring]
  rw [div_lt_iff₀ hsizeCast]
  constructor
  · intro hbound
    have hthirteen : (13 : ℝ) < 3 * (m : ℝ) := by
      have hclear : (3 : ℝ) * (1 - 3 / (m : ℝ)) * (m : ℝ) = 3 * (m : ℝ) - 9 := by
        field_simp
        ring
      nlinarith [hbound, hclear]
    have hcast : (13 : ℝ) < 3 * (m : ℝ) := hthirteen
    have hnat : 13 < 3 * m := by exact_mod_cast hcast
    omega
  · intro hfive
    have hcast : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hfive
    have hclear : (3 : ℝ) * (1 - 3 / (m : ℝ)) * (m : ℝ) = 3 * (m : ℝ) - 9 := by
      field_simp
      ring
    nlinarith [hcast, hclear]

/-! ## 7. The five in the five-atom cell is sharp

Four is not enough, and the obstruction is local: an all-heavy `(7,3)` design four
of whose atoms are the regular tetrahedron scaled by `4/5`, so that every one of
their six correlations sits at `rho^2 = 256/529 < 1/2` — every cherry light, every
pair half-box good — and yet all four of their triples fail, at tie leg exactly
`-13689/15625`.

The remaining three atoms are the coordinate axes at leverage four; they carry a
dominating triple of their own by `dominates_of_orthogonalTriple`, as they must,
since `(7,3)` is not refuted here and nothing in this file claims otherwise.  What
the witness settles is that no argument reading only a FOUR-atom block can raise
the cell's threshold: at four atoms the tetrahedral sign pattern is realisable
(`triangleProduct_tetraAtom_eq_neg_one` — all four triangle products negative), so
Lemma A has nothing to say there, and the scaling `4/5` inflates the correlations
past the frustrated-failure threshold `1/4` while keeping them under `1/2`. -/

/-- The witness atoms: the tetrahedron scaled by `4/5`, then the coordinate axes
scaled by `2`. -/
noncomputable def cherryWitnessAtom : Fin 7 → Fin 3 → ℝ :=
  ![![4 / 5, 4 / 5, 4 / 5], ![4 / 5, -(4 / 5), -(4 / 5)], ![-(4 / 5), 4 / 5, -(4 / 5)],
    ![-(4 / 5), -(4 / 5), 4 / 5], ![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]

/-- The witness weights, forced by Parseval once the atoms are fixed. -/
noncomputable def cherryWitnessWeight : Fin 7 → ℝ :=
  ![25 / 208, 25 / 208, 25 / 208, 25 / 208, 9 / 52, 9 / 52, 9 / 52]

/-- The witness design: an all-heavy weighted `(7,3)` design whose first four atoms
form a half-box-good block every one of whose triples fails. -/
noncomputable def cherryWitnessDesign : WeightedDesign 7 3 where
  atom := cherryWitnessAtom
  weight := cherryWitnessWeight
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;>
      simp only [cherryWitnessWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.cons_val, Matrix.tail_cons] <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_seven, cherryWitnessWeight, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_seven, smul_eq_mul, cherryWitnessAtom, cherryWitnessWeight,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

@[simp] theorem cherryWitnessDesign_atom (atomIndex : Fin 7) :
    cherryWitnessDesign.atom atomIndex = cherryWitnessAtom atomIndex :=
  rfl

/-- The four tetrahedral atoms of the witness. -/
def cherryWitnessBlock : Fin 4 → Fin 7 := ![0, 1, 2, 3]

theorem cherryWitnessBlock_injective : Function.Injective cherryWitnessBlock := by
  intro first second heq
  fin_cases first <;> fin_cases second <;> simp_all [cherryWitnessBlock]

theorem cherryWitnessDesign_leverage_block (index : Fin 4) :
    leverageOf (cherryWitnessDesign.atom (cherryWitnessBlock index)) = 48 / 25 := by
  fin_cases index <;>
    norm_num [cherryWitnessBlock, cherryWitnessDesign_atom, cherryWitnessAtom, leverageOf,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]

theorem cherryWitnessDesign_heavyExcess_block (index : Fin 4) :
    heavyExcess cherryWitnessDesign (cherryWitnessBlock index) = 23 / 25 := by
  rw [heavyExcess, cherryWitnessDesign_leverage_block index]
  norm_num

theorem cherryWitnessDesign_atomPairing_block {first second : Fin 4} (hne : first ≠ second) :
    atomPairing cherryWitnessDesign (cherryWitnessBlock first) (cherryWitnessBlock second)
      = -(16 / 25) := by
  fin_cases first <;> fin_cases second <;>
    first
      | exact absurd rfl hne
      | norm_num [cherryWitnessBlock, cherryWitnessDesign_atom, cherryWitnessAtom, atomPairing,
          dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_three,
          Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

theorem cherryWitnessDesign_allHeavy : AllHeavy cherryWitnessDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    norm_num [cherryWitnessDesign_atom, cherryWitnessAtom, leverageOf, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]

/-- Every pair of the block is half-box good: `2 p^2 = 512/625` against
`u u = 529/625`. -/
theorem cherryWitnessDesign_isHalfBoxGoodPair_block {first second : Fin 4} (hne : first ≠ second) :
    IsHalfBoxGoodPair cherryWitnessDesign (cherryWitnessBlock first)
      (cherryWitnessBlock second) := by
  rw [IsHalfBoxGoodPair, cherryWitnessDesign_atomPairing_block hne,
    cherryWitnessDesign_heavyExcess_block first, cherryWitnessDesign_heavyExcess_block second]
  norm_num

/-- Every cherry of the block is light. -/
theorem cherryWitnessDesign_isLightCherry_block {left center right : Fin 4}
    (hleftCenter : left ≠ center) (hrightCenter : right ≠ center) :
    IsLightCherry cherryWitnessDesign (cherryWitnessBlock left) (cherryWitnessBlock center)
      (cherryWitnessBlock right) := by
  rw [IsLightCherry, cherryWitnessDesign_atomPairing_block hleftCenter.symm,
    cherryWitnessDesign_atomPairing_block hrightCenter.symm,
    cherryWitnessDesign_heavyExcess_block left, cherryWitnessDesign_heavyExcess_block center,
    cherryWitnessDesign_heavyExcess_block right]
  norm_num

/-- **ALL FOUR TRIPLES OF THE BLOCK FAIL**, at tie leg exactly `-13689/15625`. -/
theorem cherryWitnessDesign_not_dominates_block {first second third : Fin 4}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    ¬ Dominates cherryWitnessDesign {cherryWitnessBlock first, cherryWitnessBlock second,
      cherryWitnessBlock third} := by
  have hpivotHeavy : 1 < leverageOf (cherryWitnessDesign.atom (cherryWitnessBlock first)) := by
    rw [cherryWitnessDesign_leverage_block first]; norm_num
  have htie : discriminantTie cherryWitnessDesign (cherryWitnessBlock first)
      (cherryWitnessBlock second) (cherryWitnessBlock third) = -(13689 / 15625) := by
    rw [discriminantTie, cherryWitnessDesign_atomPairing_block hfirstSecond,
      cherryWitnessDesign_atomPairing_block hfirstThird,
      cherryWitnessDesign_atomPairing_block hsecondThird,
      cherryWitnessDesign_heavyExcess_block first, cherryWitnessDesign_heavyExcess_block second,
      cherryWitnessDesign_heavyExcess_block third]
    norm_num
  rw [dominates_triple_iff_discriminantSystem cherryWitnessDesign
    (fun heq => hfirstSecond (cherryWitnessBlock_injective heq))
    (fun heq => hfirstThird (cherryWitnessBlock_injective heq))
    (fun heq => hsecondThird (cherryWitnessBlock_injective heq)) hpivotHeavy]
  rintro ⟨-, htieNonneg⟩
  rw [htie] at htieNonneg
  norm_num at htieNonneg

/-- **THE FIVE IN THE FIVE-ATOM CELL IS SHARP.**  There is an all-heavy weighted
`(7,3)` design carrying FOUR distinct atoms that are pairwise half-box good — so
every cherry among them is light — and yet every one of their four triples fails.
No strengthening of `exists_dominating_triple_of_five_lightCherries` from five
atoms to four is available, by any argument local to the block. -/
theorem exists_allHeavy_design_with_failing_lightCherry_fourBlock :
    ∃ (D : WeightedDesign 7 3) (pick : Fin 4 → Fin 7), AllHeavy D ∧ Function.Injective pick
      ∧ (∀ first second : Fin 4, first ≠ second → IsHalfBoxGoodPair D (pick first) (pick second))
      ∧ (∀ left center right : Fin 4, left ≠ center → right ≠ center →
          IsLightCherry D (pick left) (pick center) (pick right))
      ∧ (∀ first second third : Fin 4, first ≠ second → first ≠ third → second ≠ third →
          ¬ Dominates D {pick first, pick second, pick third}) :=
  ⟨cherryWitnessDesign, cherryWitnessBlock, cherryWitnessDesign_allHeavy,
    cherryWitnessBlock_injective,
    fun _ _ hne => cherryWitnessDesign_isHalfBoxGoodPair_block hne,
    fun _ _ _ hleftCenter hrightCenter =>
      cherryWitnessDesign_isLightCherry_block hleftCenter hrightCenter,
    fun _ _ _ hfirstSecond hfirstThird hsecondThird =>
      cherryWitnessDesign_not_dominates_block hfirstSecond hfirstThird hsecondThird⟩

end Gtz
