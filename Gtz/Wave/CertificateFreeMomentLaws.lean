import Gtz.Wave.NoStressResidualSwapBrackets
import Gtz.Wave.OneLineCombinedSharpDeterminant
import Gtz.Reduction.RankThreeFromStressFreeResidual
import Gtz.Ties.AllTied

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The Parseval moment ladder of the pair Gram determinant, and what it does to the
# certificate-free stratum

Two independent results live here.

## 1. The moment ladder

`Gtz.sum_weight_mul_sq_tripleBracket` is the two-point marginal of the squared bracket:
`Σ_a t_a [d, e, a]² = ⟨d, e⟩`.  It has a ladder above it that the tree did not carry.
Integrating one more slot against the weights collapses the pair Gram determinant onto
the leverage, and integrating a third collapses everything onto the rank:

    `Σ_e t_e ⟨d, e⟩ = 2 ℓ_d`                              (M1)
    `Σ_{d,e} t_d t_e ⟨d, e⟩ = 2 k`                        (M0)
    `Σ_{l,r} t_l t_r [p, l, r]² = 2 ℓ_p`                   (V)
    `Σ_{p,l,r} t_p t_l t_r [p, l, r]² = 2 k`               (CB)

`(CB)` is Cauchy-Binet at Parseval, reached WITHOUT Cauchy-Binet: three applications of
the marginal and the trace identity `Σ_c t_c ℓ_c = k`.  `(M1)` is the step that makes the
rest work, and its proof is one line of Parseval: `Σ_e t_e (g_d ⬝ᵥ g_e)² = ℓ_d`, so the
cross term of `⟨d, e⟩ = ℓ_d ℓ_e − (g_d ⬝ᵥ g_e)²` integrates to `ℓ_d` while the product
term integrates to `3 ℓ_d`.

## 2. The aggregation no-go for the weight-free certificate

`Gtz.posDef_gap_of_sum_pairBracketSq_lt` is the weight-free domination test: a spanning
triple whose three pair Gram determinants total less than its squared bracket dominates
strictly.  Its contrapositive is a constraint at every triple of a design with no strictly
dominating triple, and the marginal ladder integrates that constraint exactly.  Fix a pair
`l ≠ r`, sum the constraint over the third label against the weights, and every term
collapses:

    `(t_l + t_r) ⟨l, r⟩ ≤ ℓ_l + ℓ_r` .

That is the ENTIRE content of the weight-free test after aggregation, and this file proves
it is EMPTY: `Gtz.weight_add_weight_mul_pairBracketSq_le` derives the same inequality for
EVERY weighted design from the Parseval leverage cap `t_c ℓ_c ≤ 1` alone, in four lines,
with no hypothesis about domination.  `Gtz.pairAggregate_of_noStrictTriple_isVacuous`
records the collapse.  So the third-label moment of the weight-free arm is closed, and a
route through it is not worth opening.

The sharp arm survives the same treatment with content.  The swap mass carries three
different denominators `1 − t_c`, and `Gtz.pairSwapMass_eq_divisionFree` removes all three
at once: with `s_c = t_c / (1 − t_c)`,

    `pairSwapMass(C) = Σ_{c ∈ C} (1 + s_c) ⟨C ∖ c⟩ − (Σ_{c ∈ C} s_c) [C]²` ,

an identity with no division in it.  The domination test then reads

    `[C]² (1 + Σ_{c ∈ C} s_c) ≤ Σ_{c ∈ C} (1 + s_c) ⟨C ∖ c⟩` ,

and `Gtz.sharp_swapLaw_of_noStrictTriple` carries it to every triple of labels with NO
distinctness hypothesis, which is what makes it summable.

## 3. Why both no-goes have the same cause

`Gtz.sum_weight_mul_pairBracketSq` is the reason, and it is one line: the first moment of
the pair Gram determinant against the design is `2 l_d`, a quantity with NO ANGLE in it.
Every higher moment inherits that, so every functional built by integrating a certificate
against the Parseval weights sees only the weight-and-leverage profile.  A certificate-free
tie, if one exists, carries the same profile as `Gtz.kFourDesign`, which is certificate-free
and dominates strictly (`Gtz.strictCertificate_misses_a_strict_dominator`).  No angle-blind
functional separates them, so no moment of the certificate family can decide branch (i).

A future certificate has to be read at a SINGLE triple, or integrated against a measure
that is not the Parseval measure.

`Gtz.NoStressResidual 6` itself is equivalent to the arm it reduces.  That collapse is
`Gtz/Wave/WiringResidualEquivalence.lean`, and nothing here restates it.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## 1. Elementary shape lemmas for the bracket and the pair Gram determinant -/

/-- The squared bracket is invariant under a rotation of its three slots. -/
theorem sq_tripleBracket_rotate (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    tripleBracket firstVec secondVec thirdVec ^ 2
      = tripleBracket secondVec thirdVec firstVec ^ 2 := by
  simp only [tripleBracket_eq]; ring

/-- The pair Gram determinant is symmetric. -/
theorem pairBracketSq_comm (leftVec rightVec : Fin 3 → ℝ) :
    pairBracketSq leftVec rightVec = pairBracketSq rightVec leftVec := by
  rw [pairBracketSq, pairBracketSq, dotProduct_comm]; ring

/-- A repeated slot kills the pair Gram determinant. -/
theorem pairBracketSq_self (vec : Fin 3 → ℝ) : pairBracketSq vec vec = 0 := by
  rw [pairBracketSq, leverageOf_eq_dotProduct_self]; ring

/-- The pair Gram determinant never exceeds the product of the two leverages. -/
theorem pairBracketSq_le_mul_leverage (leftVec rightVec : Fin 3 → ℝ) :
    pairBracketSq leftVec rightVec ≤ leverageOf leftVec * leverageOf rightVec := by
  rw [pairBracketSq]
  nlinarith [sq_nonneg (leftVec ⬝ᵥ rightVec)]

/-! ## 2. The moment ladder

Four integrations of the squared bracket against the weights.  Each one removes a slot,
and the last one lands on the rank. -/

/-- **Parseval against an atom.**  The weighted second moment of the pairing of a fixed
atom against the design is that atom's own leverage. -/
theorem sum_weight_mul_sq_dotProduct_atom (design : WeightedDesign size rank)
    (label : Fin size) :
    ∑ other, design.weight other * (design.atom label ⬝ᵥ design.atom other) ^ 2
      = leverageOf (design.atom label) := by
  rw [← sum_weight_mul_sq_dotProduct_probe design (design.atom label)]
  exact Finset.sum_congr rfl fun other _ => by rw [dotProduct_comm]

/-- **(M1), THE ONE-POINT MARGINAL OF THE PAIR GRAM DETERMINANT.**  Integrating the pair
Gram determinant of a fixed atom against the design returns TWICE that atom's leverage.
The product term of `⟨d, e⟩ = ℓ_d ℓ_e − (g_d ⬝ᵥ g_e)²` integrates to `3 ℓ_d` by the trace
identity, and the cross term integrates to `ℓ_d` by Parseval, so the rank enters once and
leaves the constant `3 − 1 = 2`. -/
theorem sum_weight_mul_pairBracketSq (design : WeightedDesign size 3) (label : Fin size) :
    ∑ other, design.weight other * pairBracketSq (design.atom label) (design.atom other)
      = 2 * leverageOf (design.atom label) := by
  have hrank : ∑ other, design.weight other * leverageOf (design.atom other) = (3 : ℝ) := by
    have := sum_weight_mul_leverage design
    simpa using this
  have hquad := sum_weight_mul_sq_dotProduct_atom design label
  have hsplit : ∀ other : Fin size,
      design.weight other * pairBracketSq (design.atom label) (design.atom other)
        = leverageOf (design.atom label)
            * (design.weight other * leverageOf (design.atom other))
          - design.weight other * (design.atom label ⬝ᵥ design.atom other) ^ 2 := by
    intro other; rw [pairBracketSq]; ring
  rw [Finset.sum_congr rfl fun other _ => hsplit other, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hrank, hquad]
  ring

/-- **(M0), THE PAIR ENERGY OF A DESIGN.**  The doubly weighted total of the pair Gram
determinants is twice the rank, whatever the design. -/
theorem sum_weight_pair_mul_pairBracketSq (design : WeightedDesign size 3) :
    ∑ label, ∑ other, design.weight label * design.weight other
        * pairBracketSq (design.atom label) (design.atom other) = 6 := by
  have hinner : ∀ label : Fin size,
      ∑ other, design.weight label * design.weight other
          * pairBracketSq (design.atom label) (design.atom other)
        = design.weight label * (2 * leverageOf (design.atom label)) := by
    intro label
    rw [← sum_weight_mul_pairBracketSq design label, Finset.mul_sum]
    exact Finset.sum_congr rfl fun other _ => by ring
  have hrank : ∑ label, design.weight label * leverageOf (design.atom label) = (3 : ℝ) := by
    have := sum_weight_mul_leverage design
    simpa using this
  rw [Finset.sum_congr rfl fun label _ => hinner label]
  have hpull : ∀ label : Fin size,
      design.weight label * (2 * leverageOf (design.atom label))
        = 2 * (design.weight label * leverageOf (design.atom label)) := by
    intro label; ring
  rw [Finset.sum_congr rfl fun label _ => hpull label, ← Finset.mul_sum, hrank]
  norm_num

/-- **(V), THE TWO-SLOT MARGINAL OF THE SQUARED BRACKET.**  Integrating the squared bracket
of a fixed pivot against the design in BOTH remaining slots returns twice the pivot's
leverage.  The two-point marginal removes the third slot and lands on the pair Gram
determinant, and `(M1)` removes the second. -/
theorem sum_weight_pair_mul_sq_tripleBracket (design : WeightedDesign size 3)
    (pivot : Fin size) :
    ∑ leftLabel, ∑ rightLabel, design.weight leftLabel * design.weight rightLabel
        * tripleBracket (design.atom pivot) (design.atom leftLabel)
            (design.atom rightLabel) ^ 2
      = 2 * leverageOf (design.atom pivot) := by
  have hinner : ∀ leftLabel : Fin size,
      ∑ rightLabel, design.weight leftLabel * design.weight rightLabel
          * tripleBracket (design.atom pivot) (design.atom leftLabel)
              (design.atom rightLabel) ^ 2
        = design.weight leftLabel
            * pairBracketSq (design.atom pivot) (design.atom leftLabel) := by
    intro leftLabel
    rw [← sum_weight_mul_sq_tripleBracket design pivot leftLabel, Finset.mul_sum]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  rw [Finset.sum_congr rfl fun leftLabel _ => hinner leftLabel]
  have hcomm : ∀ leftLabel : Fin size,
      design.weight leftLabel * pairBracketSq (design.atom pivot) (design.atom leftLabel)
        = design.weight leftLabel
            * pairBracketSq (design.atom pivot) (design.atom leftLabel) := fun _ => rfl
  rw [Finset.sum_congr rfl fun leftLabel _ => hcomm leftLabel]
  exact sum_weight_mul_pairBracketSq design pivot

/-- **(CB), CAUCHY-BINET AT PARSEVAL, THROUGH THE MARGINALS.**  The triply weighted total
of the squared brackets of a rank-three design is twice the rank.  No determinant identity
and no cardinality bookkeeping enter: the three marginals do all the work, and the
degenerate index triples contribute nothing because a repeated slot kills the bracket. -/
theorem sum_weight_triple_mul_sq_tripleBracket (design : WeightedDesign size 3) :
    ∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * tripleBracket (design.atom pivot) (design.atom leftLabel)
              (design.atom rightLabel) ^ 2
      = 6 := by
  have hinner : ∀ pivot : Fin size,
      (∑ leftLabel, ∑ rightLabel,
          design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * tripleBracket (design.atom pivot) (design.atom leftLabel)
                (design.atom rightLabel) ^ 2)
        = design.weight pivot * (2 * leverageOf (design.atom pivot)) := by
    intro pivot
    rw [← sum_weight_pair_mul_sq_tripleBracket design pivot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun leftLabel _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  have hrank : ∑ pivot, design.weight pivot * leverageOf (design.atom pivot) = (3 : ℝ) := by
    have := sum_weight_mul_leverage design
    simpa using this
  rw [Finset.sum_congr rfl fun pivot _ => hinner pivot]
  have hpull : ∀ pivot : Fin size,
      design.weight pivot * (2 * leverageOf (design.atom pivot))
        = 2 * (design.weight pivot * leverageOf (design.atom pivot)) := by
    intro pivot; ring
  rw [Finset.sum_congr rfl fun pivot _ => hpull pivot, ← Finset.mul_sum, hrank]
  norm_num

/-! ## 3. The no-strict-domination hypothesis, and the pointwise laws it gives

Every statement below carries `NoStrictTriple`, the exact negation of the conclusion of
`Gtz.NoStressResidual`.  It is weaker than `Gtz.IsTie`, which also demands that some
triple dominates weakly. -/

/-- No three-element subset of the design dominates strictly.  This is the second conjunct
of `Gtz.IsTie` on its own, with no weak-domination demand attached. -/
def NoStrictTriple (design : WeightedDesign size 3) : Prop :=
  ∀ selected : Finset (Fin size), selected.card = 3 →
    ¬ (subsetSum design selected - 1).PosDef

/-- A tie has no strictly dominating triple. -/
theorem noStrictTriple_of_isTie {design : WeightedDesign size 3} (htie : IsTie design) :
    NoStrictTriple design := htie.2

/-- A design with no strictly dominating triple carries no strict certificate. -/
theorem not_hasStrictCertificate_of_noStrictTriple {design : WeightedDesign size 3}
    (hno : NoStrictTriple design) (selected : Finset (Fin size)) (hcard : selected.card = 3) :
    ¬ HasStrictCertificate design selected := fun hcertificate =>
  hno selected hcard (posDef_gap_of_hasStrictCertificate_unconditional design selected
    hcertificate)

/-- **THE WEIGHT-FREE LAW AT EVERY LABEL TRIPLE.**  Under no strict domination the squared
bracket of ANY three labels is at most the total of the three pair Gram determinants
inside them.  The distinctness hypothesis of `Gtz.posDef_gap_of_sum_pairBracketSq_lt` is
gone, because a repeated label kills the bracket while the right side stays nonnegative.
That is what makes the law summable over the full index. -/
theorem sq_tripleBracket_le_sum_pairBracketSq_of_noStrictTriple
    (design : WeightedDesign size 3) (hno : NoStrictTriple design)
    (pivot leftLabel rightLabel : Fin size) :
    tripleBracket (design.atom pivot) (design.atom leftLabel) (design.atom rightLabel) ^ 2
      ≤ pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
        + pairBracketSq (design.atom pivot) (design.atom rightLabel)
        + pairBracketSq (design.atom pivot) (design.atom leftLabel) := by
  classical
  have hnonneg : (0 : ℝ) ≤ pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
      + pairBracketSq (design.atom pivot) (design.atom rightLabel)
      + pairBracketSq (design.atom pivot) (design.atom leftLabel) := by
    have h1 := pairBracketSq_nonneg (design.atom leftLabel) (design.atom rightLabel)
    have h2 := pairBracketSq_nonneg (design.atom pivot) (design.atom rightLabel)
    have h3 := pairBracketSq_nonneg (design.atom pivot) (design.atom leftLabel)
    linarith
  by_cases hpivotLeft : pivot = leftLabel
  · subst hpivotLeft
    rw [tripleBracket_self_left _ _]
    simpa using hnonneg
  by_cases hpivotRight : pivot = rightLabel
  · subst hpivotRight
    rw [tripleBracket_repeat_first]
    simpa using hnonneg
  by_cases hleftRight : leftLabel = rightLabel
  · subst hleftRight
    rw [tripleBracket_repeat_second]
    simpa using hnonneg
  by_contra hlt
  push Not at hlt
  have hbracket : tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ≠ 0 := by
    intro hzero
    rw [hzero] at hlt
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hlt
    linarith
  exact hno _ (card_triple_eq_three hpivotLeft hpivotRight hleftRight)
    (posDef_gap_of_sum_pairBracketSq_lt design hpivotLeft hpivotRight hleftRight hbracket hlt)

/-! ## 4. The third-label moment, and the no-go it produces

Fix a pair `l ≠ r` and integrate the weight-free law over the third label against the
weights.  The left side is the two-point marginal itself, the right side is three copies of
the marginal ladder, and everything collapses to a two-atom inequality. -/

/-- Splitting a full sum off a two-element complement. -/
theorem sum_compl_pair_eq {leftLabel rightLabel : Fin size}
    (hne : leftLabel ≠ rightLabel) (target : Fin size → ℝ) :
    ∑ label ∈ ({leftLabel, rightLabel} : Finset (Fin size))ᶜ, target label
      = (∑ label, target label) - (target leftLabel + target rightLabel) := by
  classical
  have hsplit := Finset.sum_add_sum_compl ({leftLabel, rightLabel} : Finset (Fin size)) target
  rw [Finset.sum_pair hne] at hsplit
  linarith

/-- The two-point marginal survives the removal of its own two labels, because a repeated
slot kills the bracket. -/
theorem sum_compl_pair_weight_mul_sq_tripleBracket (design : WeightedDesign size 3)
    {leftLabel rightLabel : Fin size} (hne : leftLabel ≠ rightLabel) :
    ∑ pivot ∈ ({leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight pivot
        * tripleBracket (design.atom pivot) (design.atom leftLabel)
            (design.atom rightLabel) ^ 2
      = pairBracketSq (design.atom leftLabel) (design.atom rightLabel) := by
  classical
  rw [sum_compl_pair_eq hne]
  have hfull : ∑ pivot, design.weight pivot
      * tripleBracket (design.atom pivot) (design.atom leftLabel)
          (design.atom rightLabel) ^ 2
      = pairBracketSq (design.atom leftLabel) (design.atom rightLabel) := by
    rw [← sum_weight_mul_sq_tripleBracket design leftLabel rightLabel]
    exact Finset.sum_congr rfl fun pivot _ => by
      rw [sq_tripleBracket_rotate (design.atom pivot) (design.atom leftLabel)
        (design.atom rightLabel)]
  rw [hfull, tripleBracket_self_left _ _, tripleBracket_repeat_first]
  norm_num

/-- The one-point marginal, with its own two labels removed. -/
theorem sum_compl_pair_weight_mul_pairBracketSq (design : WeightedDesign size 3)
    {leftLabel rightLabel : Fin size} (hne : leftLabel ≠ rightLabel) (anchor : Fin size) :
    ∑ pivot ∈ ({leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight pivot
        * pairBracketSq (design.atom pivot) (design.atom anchor)
      = 2 * leverageOf (design.atom anchor)
        - (design.weight leftLabel
            * pairBracketSq (design.atom leftLabel) (design.atom anchor)
          + design.weight rightLabel
            * pairBracketSq (design.atom rightLabel) (design.atom anchor)) := by
  classical
  rw [sum_compl_pair_eq hne]
  have hfull : ∑ pivot, design.weight pivot
      * pairBracketSq (design.atom pivot) (design.atom anchor)
      = 2 * leverageOf (design.atom anchor) := by
    rw [← sum_weight_mul_pairBracketSq design anchor]
    exact Finset.sum_congr rfl fun pivot _ => by
      rw [pairBracketSq_comm (design.atom pivot) (design.atom anchor)]
  rw [hfull]

/-- The weights outside a pair total the pair's free weight. -/
theorem sum_compl_pair_weight (design : WeightedDesign size rank)
    {leftLabel rightLabel : Fin size} (hne : leftLabel ≠ rightLabel) :
    ∑ pivot ∈ ({leftLabel, rightLabel} : Finset (Fin size))ᶜ, design.weight pivot
      = 1 - (design.weight leftLabel + design.weight rightLabel) := by
  classical
  rw [sum_compl_pair_eq hne, design.weight_sum_one]

/-- **THE THIRD-LABEL MOMENT OF THE WEIGHT-FREE TEST.**  At a design with no strictly
dominating triple every pair obeys `(t_l + t_r) ⟨l, r⟩ ≤ ℓ_l + ℓ_r`.  Both marginals of the
ladder are spent, and no bracket, no third atom and no matrix survive. -/
theorem weight_add_weight_mul_pairBracketSq_le_of_noStrictTriple
    (design : WeightedDesign size 3) (hno : NoStrictTriple design)
    {leftLabel rightLabel : Fin size} (hne : leftLabel ≠ rightLabel) :
    (design.weight leftLabel + design.weight rightLabel)
        * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
      ≤ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) := by
  classical
  set pairSet := ({leftLabel, rightLabel} : Finset (Fin size)) with hpairSet
  have hstep : ∑ pivot ∈ pairSetᶜ, design.weight pivot
        * tripleBracket (design.atom pivot) (design.atom leftLabel)
            (design.atom rightLabel) ^ 2
      ≤ ∑ pivot ∈ pairSetᶜ, design.weight pivot
          * (pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
            + pairBracketSq (design.atom pivot) (design.atom rightLabel)
            + pairBracketSq (design.atom pivot) (design.atom leftLabel)) := by
    refine Finset.sum_le_sum fun pivot _ => ?_
    exact mul_le_mul_of_nonneg_left
      (sq_tripleBracket_le_sum_pairBracketSq_of_noStrictTriple design hno pivot leftLabel
        rightLabel)
      (le_of_lt (design.weight_pos pivot))
  rw [sum_compl_pair_weight_mul_sq_tripleBracket design hne] at hstep
  have hexpand : ∑ pivot ∈ pairSetᶜ, design.weight pivot
        * (pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
          + pairBracketSq (design.atom pivot) (design.atom rightLabel)
          + pairBracketSq (design.atom pivot) (design.atom leftLabel))
      = (∑ pivot ∈ pairSetᶜ, design.weight pivot)
          * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
        + (∑ pivot ∈ pairSetᶜ, design.weight pivot
            * pairBracketSq (design.atom pivot) (design.atom rightLabel))
        + (∑ pivot ∈ pairSetᶜ, design.weight pivot
            * pairBracketSq (design.atom pivot) (design.atom leftLabel)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun pivot _ => by ring
  rw [hexpand, sum_compl_pair_weight design hne,
    sum_compl_pair_weight_mul_pairBracketSq design hne rightLabel,
    sum_compl_pair_weight_mul_pairBracketSq design hne leftLabel,
    pairBracketSq_self (design.atom rightLabel), pairBracketSq_self (design.atom leftLabel),
    pairBracketSq_comm (design.atom rightLabel) (design.atom leftLabel)] at hstep
  linarith [hstep]

/-- **THE SAME INEQUALITY, UNCONDITIONALLY.**  Every weighted rank-three design obeys
`(t_l + t_r) ⟨l, r⟩ ≤ ℓ_l + ℓ_r`, by the Parseval leverage cap alone.  No domination
hypothesis, no pair hypothesis, and no distinctness. -/
theorem weight_add_weight_mul_pairBracketSq_le (design : WeightedDesign size 3)
    (leftLabel rightLabel : Fin size) :
    (design.weight leftLabel + design.weight rightLabel)
        * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
      ≤ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel) := by
  have hcapLeft := weight_mul_leverage_le_one design leftLabel
  have hcapRight := weight_mul_leverage_le_one design rightLabel
  have hleft := leverageOf_nonneg (design.atom leftLabel)
  have hright := leverageOf_nonneg (design.atom rightLabel)
  have hprod := pairBracketSq_le_mul_leverage (design.atom leftLabel) (design.atom rightLabel)
  have hweightLeft := design.weight_pos leftLabel
  have hweightRight := design.weight_pos rightLabel
  nlinarith [hcapLeft, hcapRight, hleft, hright, hprod, hweightLeft, hweightRight]

/-- **THE NO-GO.**  The third-label moment of the weight-free domination test is EMPTY: the
inequality it produces at a design with no strictly dominating triple is a theorem about
every design.  The route "aggregate `Gtz.posDef_gap_of_sum_pairBracketSq_lt` over the free
slot" is closed, and no sharpening of the pair Gram side can reopen it. -/
theorem pairAggregate_of_noStrictTriple_isVacuous (design : WeightedDesign size 3)
    (leftLabel rightLabel : Fin size) :
    ((design.weight leftLabel + design.weight rightLabel)
          * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
        ≤ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel))
      ∧ (NoStrictTriple design → leftLabel ≠ rightLabel →
        (design.weight leftLabel + design.weight rightLabel)
            * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
          ≤ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel)) :=
  ⟨weight_add_weight_mul_pairBracketSq_le design leftLabel rightLabel,
    fun hno hne =>
      weight_add_weight_mul_pairBracketSq_le_of_noStrictTriple design hno hne⟩

/-! ## 5. The sharp arm, cleared of every division

The swap mass of `Gtz.pairSwapMass` carries three distinct denominators.  Writing
`s_c = t_c / (1 − t_c)` turns `1 / (1 − t_c)` into `1 + s_c`, and the whole quantity becomes
a polynomial in the pair Gram determinants, the squared bracket and the three `s_c`. -/

/-- The swap weight `s_c = t_c / (1 − t_c)` of an atom. -/
noncomputable def swapWeight (design : WeightedDesign size rank) (label : Fin size) : ℝ :=
  design.weight label / (1 - design.weight label)

/-- The swap weight is never negative, at any design with two or more atoms. -/
theorem swapWeight_nonneg (design : WeightedDesign size 3) {first second : Fin size}
    (hne : first ≠ second) (label : Fin size) : 0 ≤ swapWeight design label := by
  rw [swapWeight]
  exact le_of_lt (div_pos (design.weight_pos label)
    (one_sub_weight_pos_of_two_labels design hne label))

/-- The defining relation of the swap weight, cleared of its denominator. -/
theorem one_add_swapWeight_mul (design : WeightedDesign size 3) {first second : Fin size}
    (hne : first ≠ second) (label : Fin size) :
    (1 + swapWeight design label) * (1 - design.weight label) = 1 := by
  have hpos := one_sub_weight_pos_of_two_labels design hne label
  rw [swapWeight]
  field_simp
  ring

/-- The swap weight times the free weight is the weight. -/
theorem swapWeight_mul_one_sub_weight (design : WeightedDesign size 3)
    {first second : Fin size} (hne : first ≠ second) (label : Fin size) :
    swapWeight design label * (1 - design.weight label) = design.weight label := by
  have hpos := one_sub_weight_pos_of_two_labels design hne label
  rw [swapWeight]
  field_simp

/-- **THE SWAP MASS WITHOUT A DIVISION.**  Form (II) of
`Gtz/Wave/NoStressResidualSwapBrackets.lean` still carries three denominators.  In the swap
weights it is a polynomial:
`pairSwapMass(C) = Σ_{c ∈ C} (1 + s_c) ⟨C ∖ c⟩ − (Σ_{c ∈ C} s_c) [C]²`. -/
theorem pairSwapMass_eq_divisionFree (design : WeightedDesign size 3)
    {pivot leftLabel rightLabel : Fin size} (hpivotLeft : pivot ≠ leftLabel) :
    pairSwapMass design pivot leftLabel rightLabel
      = (1 + swapWeight design pivot)
          * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
        + (1 + swapWeight design leftLabel)
          * pairBracketSq (design.atom pivot) (design.atom rightLabel)
        + (1 + swapWeight design rightLabel)
          * pairBracketSq (design.atom pivot) (design.atom leftLabel)
        - (swapWeight design pivot + swapWeight design leftLabel
            + swapWeight design rightLabel)
          * tripleBracket (design.atom pivot) (design.atom leftLabel)
              (design.atom rightLabel) ^ 2 := by
  have hpivot := one_sub_weight_pos_of_two_labels design hpivotLeft pivot
  have hleft := one_sub_weight_pos_of_two_labels design hpivotLeft leftLabel
  have hright := one_sub_weight_pos_of_two_labels design hpivotLeft rightLabel
  rw [pairSwapMass, swapWeight, swapWeight, swapWeight]
  field_simp
  ring

/-- **THE SHARP LAW AT EVERY LABEL TRIPLE.**  Under no strict domination, for ANY three
labels the squared bracket inflated by the three swap weights is at most the swap-weighted
total of the three pair Gram determinants.  As with the weight-free law, no distinctness
hypothesis survives, so the law is summable over the full index. -/
theorem sharp_swapLaw_of_noStrictTriple (design : WeightedDesign size 3)
    (hno : NoStrictTriple design) {first second : Fin size} (hdistinct : first ≠ second)
    (pivot leftLabel rightLabel : Fin size) :
    tripleBracket (design.atom pivot) (design.atom leftLabel) (design.atom rightLabel) ^ 2
        * (1 + swapWeight design pivot + swapWeight design leftLabel
            + swapWeight design rightLabel)
      ≤ (1 + swapWeight design pivot)
          * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
        + (1 + swapWeight design leftLabel)
          * pairBracketSq (design.atom pivot) (design.atom rightLabel)
        + (1 + swapWeight design rightLabel)
          * pairBracketSq (design.atom pivot) (design.atom leftLabel) := by
  classical
  have hswapPivot := swapWeight_nonneg design hdistinct pivot
  have hswapLeft := swapWeight_nonneg design hdistinct leftLabel
  have hswapRight := swapWeight_nonneg design hdistinct rightLabel
  have honePivot := pairBracketSq_nonneg (design.atom leftLabel) (design.atom rightLabel)
  have honeLeft := pairBracketSq_nonneg (design.atom pivot) (design.atom rightLabel)
  have honeRight := pairBracketSq_nonneg (design.atom pivot) (design.atom leftLabel)
  have hnonneg : (0 : ℝ) ≤ (1 + swapWeight design pivot)
        * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
      + (1 + swapWeight design leftLabel)
        * pairBracketSq (design.atom pivot) (design.atom rightLabel)
      + (1 + swapWeight design rightLabel)
        * pairBracketSq (design.atom pivot) (design.atom leftLabel) := by
    have h1 : (0 : ℝ) ≤ (1 + swapWeight design pivot)
        * pairBracketSq (design.atom leftLabel) (design.atom rightLabel) := by
      apply mul_nonneg (by linarith) honePivot
    have h2 : (0 : ℝ) ≤ (1 + swapWeight design leftLabel)
        * pairBracketSq (design.atom pivot) (design.atom rightLabel) := by
      apply mul_nonneg (by linarith) honeLeft
    have h3 : (0 : ℝ) ≤ (1 + swapWeight design rightLabel)
        * pairBracketSq (design.atom pivot) (design.atom leftLabel) := by
      apply mul_nonneg (by linarith) honeRight
    linarith
  by_cases hpivotLeft : pivot = leftLabel
  · subst hpivotLeft
    rw [tripleBracket_self_left _ _]
    simpa using hnonneg
  by_cases hpivotRight : pivot = rightLabel
  · subst hpivotRight
    rw [tripleBracket_repeat_first]
    simpa using hnonneg
  by_cases hleftRight : leftLabel = rightLabel
  · subst hleftRight
    rw [tripleBracket_repeat_second]
    simpa using hnonneg
  by_contra hlt
  push Not at hlt
  have hbracket : tripleBracket (design.atom pivot) (design.atom leftLabel)
      (design.atom rightLabel) ≠ 0 := by
    intro hzero
    rw [hzero] at hlt
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hlt
    linarith
  have hswap : pairSwapMass design pivot leftLabel rightLabel
      < tripleBracket (design.atom pivot) (design.atom leftLabel)
          (design.atom rightLabel) ^ 2 := by
    rw [pairSwapMass_eq_divisionFree design hpivotLeft]
    nlinarith [hlt]
  exact hno _ (card_triple_eq_three hpivotLeft hpivotRight hleftRight)
    (posDef_gap_of_pairSwapMass_lt design hpivotLeft hpivotRight hleftRight hbracket hswap)

/-! ## 6. The swap moments of a design

Two scalars of the weight-and-leverage profile alone.  They are what the sharp law
integrates to. -/

/-- The swap moment `Q = Σ_c t_c s_c` of a design. -/
noncomputable def swapMoment (design : WeightedDesign size rank) : ℝ :=
  ∑ label, design.weight label * swapWeight design label

/-- The swap leverage moment `P = Σ_c t_c s_c ℓ_c` of a design. -/
noncomputable def swapLeverageMoment (design : WeightedDesign size rank) : ℝ :=
  ∑ label, design.weight label * swapWeight design label * leverageOf (design.atom label)

/-- **THE SWAP LEVERAGE MOMENT IS BOUNDED BY THE SWAP TOTAL.**  The Parseval leverage cap
`t_c ℓ_c ≤ 1` gives `P ≤ Σ_c s_c` at every design. -/
theorem swapLeverageMoment_le_sum_swapWeight (design : WeightedDesign size 3)
    {first second : Fin size} (hdistinct : first ≠ second) :
    swapLeverageMoment design ≤ ∑ label, swapWeight design label := by
  rw [swapLeverageMoment]
  refine Finset.sum_le_sum fun label _ => ?_
  have hcap := weight_mul_leverage_le_one design label
  have hswap := swapWeight_nonneg design hdistinct label
  nlinarith [hcap, hswap]

/-- The swap moment is never negative. -/
theorem swapMoment_nonneg (design : WeightedDesign size 3) {first second : Fin size}
    (hdistinct : first ≠ second) : 0 ≤ swapMoment design := by
  rw [swapMoment]
  refine Finset.sum_nonneg fun label _ => ?_
  exact mul_nonneg (le_of_lt (design.weight_pos label))
    (swapWeight_nonneg design hdistinct label)

/-- The swap leverage moment is never negative. -/
theorem swapLeverageMoment_nonneg (design : WeightedDesign size 3) {first second : Fin size}
    (hdistinct : first ≠ second) : 0 ≤ swapLeverageMoment design := by
  rw [swapLeverageMoment]
  refine Finset.sum_nonneg fun label _ => ?_
  exact mul_nonneg (mul_nonneg (le_of_lt (design.weight_pos label))
    (swapWeight_nonneg design hdistinct label)) (leverageOf_nonneg (design.atom label))

/-! ## 7. The root design, calibrated in the new invariants -/

/-- Every atom of the root design has leverage exactly three. -/
theorem leverageOf_coordinateDiagonalDesign (atomLabel : Fin 6) :
    leverageOf (coordinateDiagonalDesign.atom atomLabel) = 3 := by
  rw [leverageOf_eq_dotProduct_self, coordinateDiagonalDesign_dotProduct]
  fin_cases atomLabel <;>
    simp [diagonalPattern_zero, diagonalPattern_one, diagonalPattern_two, diagonalPattern_three,
      diagonalPattern_four, diagonalPattern_five, dotProduct, Fin.sum_univ_three] <;>
    norm_num

/-- Every swap weight of the root design is `1/5`. -/
theorem swapWeight_coordinateDiagonalDesign (atomLabel : Fin 6) :
    swapWeight coordinateDiagonalDesign atomLabel = 1 / 5 := by
  rw [swapWeight, coordinateDiagonalDesign_weight_apply]
  norm_num

/-- **THE SWAP MOMENT OF THE ROOT DESIGN IS `1/5`.** -/
theorem swapMoment_coordinateDiagonalDesign :
    swapMoment coordinateDiagonalDesign = 1 / 5 := by
  have hterm : ∀ label : Fin 6,
      coordinateDiagonalDesign.weight label * swapWeight coordinateDiagonalDesign label
        = 1 / 30 := by
    intro label
    rw [coordinateDiagonalDesign_weight_apply, swapWeight_coordinateDiagonalDesign]
    norm_num
  rw [swapMoment, Finset.sum_congr rfl fun label _ => hterm label]
  norm_num

/-- **THE SWAP LEVERAGE MOMENT OF THE ROOT DESIGN IS `3/5`.** -/
theorem swapLeverageMoment_coordinateDiagonalDesign :
    swapLeverageMoment coordinateDiagonalDesign = 3 / 5 := by
  have hterm : ∀ label : Fin 6,
      coordinateDiagonalDesign.weight label * swapWeight coordinateDiagonalDesign label
          * leverageOf (coordinateDiagonalDesign.atom label) = 1 / 10 := by
    intro label
    rw [coordinateDiagonalDesign_weight_apply, swapWeight_coordinateDiagonalDesign,
      leverageOf_coordinateDiagonalDesign]
    norm_num
  rw [swapLeverageMoment, Finset.sum_congr rfl fun label _ => hterm label]
  norm_num

/-- **THE PAIR ENERGY OF THE ROOT DESIGN IS SIX**, as the ladder demands at rank three. -/
theorem sum_weight_pair_mul_pairBracketSq_coordinateDiagonalDesign :
    ∑ label, ∑ other, coordinateDiagonalDesign.weight label
        * coordinateDiagonalDesign.weight other
        * pairBracketSq (coordinateDiagonalDesign.atom label)
            (coordinateDiagonalDesign.atom other) = 6 :=
  sum_weight_pair_mul_pairBracketSq coordinateDiagonalDesign

/-! ## 8. The sharp arm aggregated against the ladder, and the second no-go

The sharp law is summable over the FULL triple index, so the whole ladder applies to it at
once.  Every one of the six pieces collapses onto `P` or onto `Q`, and the aggregate is a
two-scalar inequality in the weight-and-leverage profile alone. -/

/-- The two-slot marginal read at the MIDDLE slot. -/
theorem sum_pair_sq_tripleBracket_mid (design : WeightedDesign size 3) (mid : Fin size) :
    ∑ firstLabel, ∑ thirdLabel, design.weight firstLabel * design.weight thirdLabel
        * tripleBracket (design.atom firstLabel) (design.atom mid)
            (design.atom thirdLabel) ^ 2
      = 2 * leverageOf (design.atom mid) := by
  rw [Finset.sum_comm, ← sum_weight_pair_mul_sq_tripleBracket design mid]
  refine Finset.sum_congr rfl fun thirdLabel _ => Finset.sum_congr rfl fun firstLabel _ => ?_
  rw [sq_tripleBracket_rotate (design.atom firstLabel) (design.atom mid)
    (design.atom thirdLabel)]
  ring

/-- The two-slot marginal read at the LAST slot. -/
theorem sum_pair_sq_tripleBracket_last (design : WeightedDesign size 3) (last : Fin size) :
    ∑ firstLabel, ∑ secondLabel, design.weight firstLabel * design.weight secondLabel
        * tripleBracket (design.atom firstLabel) (design.atom secondLabel)
            (design.atom last) ^ 2
      = 2 * leverageOf (design.atom last) := by
  rw [← sum_weight_pair_mul_sq_tripleBracket design last]
  refine Finset.sum_congr rfl fun firstLabel _ => Finset.sum_congr rfl fun secondLabel _ => ?_
  rw [sq_tripleBracket_rotate (design.atom firstLabel) (design.atom secondLabel)
      (design.atom last),
    sq_tripleBracket_rotate (design.atom secondLabel) (design.atom last)
      (design.atom firstLabel)]

/-- The weighted total of `1 + s_c` is `1 + Q`. -/
theorem sum_weight_mul_one_add_swapWeight (design : WeightedDesign size rank) :
    ∑ label, design.weight label * (1 + swapWeight design label)
      = 1 + swapMoment design := by
  have hterm : ∀ label : Fin size, design.weight label * (1 + swapWeight design label)
      = design.weight label + design.weight label * swapWeight design label :=
    fun label => by ring
  rw [Finset.sum_congr rfl fun label _ => hterm label, Finset.sum_add_distrib,
    design.weight_sum_one, swapMoment]

/-- The swap moment of the squared bracket carried by the PIVOT slot. -/
theorem sum_triple_swapPivot (design : WeightedDesign size 3) :
    ∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * (tripleBracket (design.atom pivot) (design.atom leftLabel)
              (design.atom rightLabel) ^ 2 * swapWeight design pivot)
      = 2 * swapLeverageMoment design := by
  have hstep : ∀ pivot : Fin size,
      (∑ leftLabel, ∑ rightLabel,
          design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * (tripleBracket (design.atom pivot) (design.atom leftLabel)
                (design.atom rightLabel) ^ 2 * swapWeight design pivot))
        = design.weight pivot * swapWeight design pivot
            * (2 * leverageOf (design.atom pivot)) := by
    intro pivot
    rw [← sum_weight_pair_mul_sq_tripleBracket design pivot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun leftLabel _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  rw [Finset.sum_congr rfl fun pivot _ => hstep pivot, swapLeverageMoment, Finset.mul_sum]
  exact Finset.sum_congr rfl fun pivot _ => by ring

/-- The swap moment of the squared bracket carried by the MIDDLE slot. -/
theorem sum_triple_swapMid (design : WeightedDesign size 3) :
    ∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * (tripleBracket (design.atom pivot) (design.atom leftLabel)
              (design.atom rightLabel) ^ 2 * swapWeight design leftLabel)
      = 2 * swapLeverageMoment design := by
  rw [Finset.sum_comm]
  have hstep : ∀ leftLabel : Fin size,
      (∑ pivot, ∑ rightLabel,
          design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * (tripleBracket (design.atom pivot) (design.atom leftLabel)
                (design.atom rightLabel) ^ 2 * swapWeight design leftLabel))
        = design.weight leftLabel * swapWeight design leftLabel
            * (2 * leverageOf (design.atom leftLabel)) := by
    intro leftLabel
    rw [← sum_pair_sq_tripleBracket_mid design leftLabel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun pivot _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  rw [Finset.sum_congr rfl fun leftLabel _ => hstep leftLabel, swapLeverageMoment,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun leftLabel _ => by ring

/-- The swap moment of the squared bracket carried by the LAST slot. -/
theorem sum_triple_swapLast (design : WeightedDesign size 3) :
    ∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * (tripleBracket (design.atom pivot) (design.atom leftLabel)
              (design.atom rightLabel) ^ 2 * swapWeight design rightLabel)
      = 2 * swapLeverageMoment design := by
  have hreorder : (∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * (tripleBracket (design.atom pivot) (design.atom leftLabel)
              (design.atom rightLabel) ^ 2 * swapWeight design rightLabel))
      = ∑ rightLabel, ∑ pivot, ∑ leftLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * (tripleBracket (design.atom pivot) (design.atom leftLabel)
              (design.atom rightLabel) ^ 2 * swapWeight design rightLabel) :=
    (Finset.sum_congr rfl fun pivot _ => Finset.sum_comm).trans Finset.sum_comm
  rw [hreorder]
  have hstep : ∀ rightLabel : Fin size,
      (∑ pivot, ∑ leftLabel,
          design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * (tripleBracket (design.atom pivot) (design.atom leftLabel)
                (design.atom rightLabel) ^ 2 * swapWeight design rightLabel))
        = design.weight rightLabel * swapWeight design rightLabel
            * (2 * leverageOf (design.atom rightLabel)) := by
    intro rightLabel
    rw [← sum_pair_sq_tripleBracket_last design rightLabel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun pivot _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun leftLabel _ => by ring
  rw [Finset.sum_congr rfl fun rightLabel _ => hstep rightLabel, swapLeverageMoment,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun rightLabel _ => by ring

/-- The pair energy carried by the PIVOT slot. -/
theorem sum_triple_energyPivot (design : WeightedDesign size 3) :
    ∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * ((1 + swapWeight design pivot)
            * pairBracketSq (design.atom leftLabel) (design.atom rightLabel))
      = 6 * (1 + swapMoment design) := by
  have hstep : ∀ pivot : Fin size,
      (∑ leftLabel, ∑ rightLabel,
          design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * ((1 + swapWeight design pivot)
              * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)))
        = design.weight pivot * (1 + swapWeight design pivot) * 6 := by
    intro pivot
    rw [← sum_weight_pair_mul_pairBracketSq design, Finset.mul_sum]
    refine Finset.sum_congr rfl fun leftLabel _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  rw [Finset.sum_congr rfl fun pivot _ => hstep pivot, ← Finset.sum_mul,
    sum_weight_mul_one_add_swapWeight design]
  ring

/-- The pair energy carried by the MIDDLE slot. -/
theorem sum_triple_energyMid (design : WeightedDesign size 3) :
    ∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * ((1 + swapWeight design leftLabel)
            * pairBracketSq (design.atom pivot) (design.atom rightLabel))
      = 6 * (1 + swapMoment design) := by
  rw [Finset.sum_comm]
  have hstep : ∀ leftLabel : Fin size,
      (∑ pivot, ∑ rightLabel,
          design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * ((1 + swapWeight design leftLabel)
              * pairBracketSq (design.atom pivot) (design.atom rightLabel)))
        = design.weight leftLabel * (1 + swapWeight design leftLabel) * 6 := by
    intro leftLabel
    rw [← sum_weight_pair_mul_pairBracketSq design, Finset.mul_sum]
    refine Finset.sum_congr rfl fun pivot _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  rw [Finset.sum_congr rfl fun leftLabel _ => hstep leftLabel, ← Finset.sum_mul,
    sum_weight_mul_one_add_swapWeight design]
  ring

/-- The pair energy carried by the LAST slot. -/
theorem sum_triple_energyLast (design : WeightedDesign size 3) :
    ∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * ((1 + swapWeight design rightLabel)
            * pairBracketSq (design.atom pivot) (design.atom leftLabel))
      = 6 * (1 + swapMoment design) := by
  have hreorder : (∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * ((1 + swapWeight design rightLabel)
            * pairBracketSq (design.atom pivot) (design.atom leftLabel)))
      = ∑ rightLabel, ∑ pivot, ∑ leftLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * ((1 + swapWeight design rightLabel)
            * pairBracketSq (design.atom pivot) (design.atom leftLabel)) :=
    (Finset.sum_congr rfl fun pivot _ => Finset.sum_comm).trans Finset.sum_comm
  rw [hreorder]
  have hstep : ∀ rightLabel : Fin size,
      (∑ pivot, ∑ leftLabel,
          design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * ((1 + swapWeight design rightLabel)
              * pairBracketSq (design.atom pivot) (design.atom leftLabel)))
        = design.weight rightLabel * (1 + swapWeight design rightLabel) * 6 := by
    intro rightLabel
    rw [← sum_weight_pair_mul_pairBracketSq design, Finset.mul_sum]
    refine Finset.sum_congr rfl fun pivot _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun leftLabel _ => by ring
  rw [Finset.sum_congr rfl fun rightLabel _ => hstep rightLabel, ← Finset.sum_mul,
    sum_weight_mul_one_add_swapWeight design]
  ring

/-- **THE LEFT SIDE OF THE SHARP LAW, AGGREGATED.**  `6 + 6 P`: the Cauchy-Binet total plus
three equal swap moments. -/
theorem sum_triple_sharpLeft (design : WeightedDesign size 3) :
    ∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * (tripleBracket (design.atom pivot) (design.atom leftLabel)
                (design.atom rightLabel) ^ 2
            * (1 + swapWeight design pivot + swapWeight design leftLabel
              + swapWeight design rightLabel))
      = 6 + 6 * swapLeverageMoment design := by
  have hsplit : ∀ pivot leftLabel rightLabel : Fin size,
      design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * (tripleBracket (design.atom pivot) (design.atom leftLabel)
                (design.atom rightLabel) ^ 2
            * (1 + swapWeight design pivot + swapWeight design leftLabel
              + swapWeight design rightLabel))
        = design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * tripleBracket (design.atom pivot) (design.atom leftLabel)
                (design.atom rightLabel) ^ 2
          + design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * (tripleBracket (design.atom pivot) (design.atom leftLabel)
                (design.atom rightLabel) ^ 2 * swapWeight design pivot)
          + design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * (tripleBracket (design.atom pivot) (design.atom leftLabel)
                (design.atom rightLabel) ^ 2 * swapWeight design leftLabel)
          + design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * (tripleBracket (design.atom pivot) (design.atom leftLabel)
                (design.atom rightLabel) ^ 2 * swapWeight design rightLabel) := by
    intro pivot leftLabel rightLabel; ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun leftLabel _ =>
    Finset.sum_congr rfl fun rightLabel _ => hsplit pivot leftLabel rightLabel]
  simp only [Finset.sum_add_distrib]
  rw [sum_weight_triple_mul_sq_tripleBracket design, sum_triple_swapPivot design,
    sum_triple_swapMid design, sum_triple_swapLast design]
  ring

/-- **THE RIGHT SIDE OF THE SHARP LAW, AGGREGATED.**  `18 (1 + Q)`: three equal pair
energies, each the product of the swap total with the rank-three pair energy six. -/
theorem sum_triple_sharpRight (design : WeightedDesign size 3) :
    ∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * ((1 + swapWeight design pivot)
              * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
            + (1 + swapWeight design leftLabel)
              * pairBracketSq (design.atom pivot) (design.atom rightLabel)
            + (1 + swapWeight design rightLabel)
              * pairBracketSq (design.atom pivot) (design.atom leftLabel))
      = 18 * (1 + swapMoment design) := by
  have hsplit : ∀ pivot leftLabel rightLabel : Fin size,
      design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * ((1 + swapWeight design pivot)
              * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
            + (1 + swapWeight design leftLabel)
              * pairBracketSq (design.atom pivot) (design.atom rightLabel)
            + (1 + swapWeight design rightLabel)
              * pairBracketSq (design.atom pivot) (design.atom leftLabel))
        = design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * ((1 + swapWeight design pivot)
              * pairBracketSq (design.atom leftLabel) (design.atom rightLabel))
          + design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * ((1 + swapWeight design leftLabel)
              * pairBracketSq (design.atom pivot) (design.atom rightLabel))
          + design.weight pivot * design.weight leftLabel * design.weight rightLabel
            * ((1 + swapWeight design rightLabel)
              * pairBracketSq (design.atom pivot) (design.atom leftLabel)) := by
    intro pivot leftLabel rightLabel; ring
  rw [Finset.sum_congr rfl fun pivot _ => Finset.sum_congr rfl fun leftLabel _ =>
    Finset.sum_congr rfl fun rightLabel _ => hsplit pivot leftLabel rightLabel]
  simp only [Finset.sum_add_distrib]
  rw [sum_triple_energyPivot design, sum_triple_energyMid design,
    sum_triple_energyLast design]
  ring

/-- **THE SHARP AGGREGATE.**  At a design with no strictly dominating triple the two swap
moments obey `P ≤ 3 Q + 2`.  Every trace of the geometry is gone: only the weights and the
leverages survive the ladder. -/
theorem swapLeverageMoment_le_of_noStrictTriple (design : WeightedDesign size 3)
    (hno : NoStrictTriple design) {first second : Fin size} (hdistinct : first ≠ second) :
    swapLeverageMoment design ≤ 3 * swapMoment design + 2 := by
  have hsum : (∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * (tripleBracket (design.atom pivot) (design.atom leftLabel)
                (design.atom rightLabel) ^ 2
            * (1 + swapWeight design pivot + swapWeight design leftLabel
              + swapWeight design rightLabel)))
      ≤ ∑ pivot, ∑ leftLabel, ∑ rightLabel,
        design.weight pivot * design.weight leftLabel * design.weight rightLabel
          * ((1 + swapWeight design pivot)
              * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
            + (1 + swapWeight design leftLabel)
              * pairBracketSq (design.atom pivot) (design.atom rightLabel)
            + (1 + swapWeight design rightLabel)
              * pairBracketSq (design.atom pivot) (design.atom leftLabel)) := by
    refine Finset.sum_le_sum fun pivot _ => Finset.sum_le_sum fun leftLabel _ =>
      Finset.sum_le_sum fun rightLabel _ => ?_
    refine mul_le_mul_of_nonneg_left
      (sharp_swapLaw_of_noStrictTriple design hno hdistinct pivot leftLabel rightLabel) ?_
    exact le_of_lt (mul_pos (mul_pos (design.weight_pos pivot) (design.weight_pos leftLabel))
      (design.weight_pos rightLabel))
  rw [sum_triple_sharpLeft design, sum_triple_sharpRight design] at hsum
  linarith

/-- **THE SAME BOUND, UNCONDITIONALLY.**  `P ≤ 3 Q + 2` at every weighted rank-three
design.  The pointwise step is `t ℓ (5 t − 2) ≤ 9 t²`, which the Parseval leverage cap
`t ℓ ≤ 1` gives because `9 t² − 5 t + 2` has negative discriminant. -/
theorem swapLeverageMoment_le (design : WeightedDesign size 3) {first second : Fin size}
    (hdistinct : first ≠ second) :
    swapLeverageMoment design ≤ 3 * swapMoment design + 2 := by
  have hpoint : ∀ label : Fin size,
      design.weight label * swapWeight design label * leverageOf (design.atom label)
        ≤ 3 * (design.weight label * swapWeight design label)
          + 2 / 3 * (design.weight label * leverageOf (design.atom label)) := by
    intro label
    have hfree := one_sub_weight_pos_of_two_labels design hdistinct label
    have hst := swapWeight_mul_one_sub_weight design hdistinct label
    have hcap := weight_mul_leverage_le_one design label
    have hlev := leverageOf_nonneg (design.atom label)
    have hpos := design.weight_pos label
    have hmass : 0 ≤ design.weight label * leverageOf (design.atom label) :=
      mul_nonneg (le_of_lt hpos) hlev
    have hkey : design.weight label * leverageOf (design.atom label)
        * (5 * design.weight label - 2) ≤ 9 * design.weight label ^ 2 := by
      rcases le_or_gt (5 * design.weight label) 2 with hsmall | hlarge
      · nlinarith [hmass, sq_nonneg (design.weight label)]
      · nlinarith [hcap, hmass, sq_nonneg (18 * design.weight label - 5)]
    have hscale : (0 : ℝ) < 3 * (1 - design.weight label) := by linarith
    refine le_of_mul_le_mul_left ?_ hscale
    have hleftExp : 3 * (1 - design.weight label)
        * (design.weight label * swapWeight design label * leverageOf (design.atom label))
        = 3 * (design.weight label * leverageOf (design.atom label))
          * (swapWeight design label * (1 - design.weight label)) := by ring
    have hrightExp : 3 * (1 - design.weight label)
        * (3 * (design.weight label * swapWeight design label)
          + 2 / 3 * (design.weight label * leverageOf (design.atom label)))
        = 9 * design.weight label
            * (swapWeight design label * (1 - design.weight label))
          + 2 * (1 - design.weight label)
            * (design.weight label * leverageOf (design.atom label)) := by ring
    rw [hleftExp, hrightExp, hst]
    nlinarith [hkey]
  have hrank : ∑ label, design.weight label * leverageOf (design.atom label) = (3 : ℝ) := by
    have := sum_weight_mul_leverage design
    simpa using this
  have hbound := Finset.sum_le_sum fun label (_ : label ∈ Finset.univ) => hpoint label
  rw [← swapLeverageMoment] at hbound
  have hrhs : (∑ label, (3 * (design.weight label * swapWeight design label)
        + 2 / 3 * (design.weight label * leverageOf (design.atom label))))
      = 3 * swapMoment design + 2 / 3 * 3 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrank, swapMoment]
  rw [hrhs] at hbound
  linarith

/-- **THE SECOND NO-GO.**  The full moment aggregate of the SHARP certificate is EMPTY
too.  The inequality it produces at a design with no strictly dominating triple is a
theorem about every design, so the route "integrate the swap-mass test against the Parseval
weights" is closed.  Read it with `Gtz.pairAggregate_of_noStrictTriple_isVacuous`: BOTH arms
of `Gtz.HasStrictCertificate` die the same way.

The cause is structural and is proved above.  `Gtz.sum_weight_mul_pairBracketSq` says the
first moment of the pair Gram determinant is `2 ℓ_d`, a quantity with no angle in it, so
every moment of the certificate family against the Parseval weights is ANGLE-BLIND.  A
certificate-free tie and `Gtz.kFourDesign` carry the same weights and the same leverages,
and no angle-blind functional separates them. -/
theorem sharpAggregate_of_noStrictTriple_isVacuous (design : WeightedDesign size 3)
    {first second : Fin size} (hdistinct : first ≠ second) :
    (swapLeverageMoment design ≤ 3 * swapMoment design + 2)
      ∧ (NoStrictTriple design →
        swapLeverageMoment design ≤ 3 * swapMoment design + 2) :=
  ⟨swapLeverageMoment_le design hdistinct,
    fun hno => swapLeverageMoment_le_of_noStrictTriple design hno hdistinct⟩

/-- **THE MOMENT ROUTE IS CLOSED AT BOTH ARMS.**  Neither the weight-free test nor the
swap-mass test survives integration against the Parseval ladder.  Any future certificate
must be read at a single triple, or against a measure that is not the Parseval measure. -/
theorem certificateMomentRoute_isClosed (design : WeightedDesign size 3)
    {first second : Fin size} (hdistinct : first ≠ second)
    (leftLabel rightLabel : Fin size) :
    ((design.weight leftLabel + design.weight rightLabel)
        * pairBracketSq (design.atom leftLabel) (design.atom rightLabel)
      ≤ leverageOf (design.atom leftLabel) + leverageOf (design.atom rightLabel))
    ∧ (swapLeverageMoment design ≤ 3 * swapMoment design + 2) :=
  ⟨weight_add_weight_mul_pairBracketSq_le design leftLabel rightLabel,
    swapLeverageMoment_le design hdistinct⟩

end Gtz
