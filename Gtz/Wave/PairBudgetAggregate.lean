/-
# The pair budget aggregated, and the corner's own pairs

`Gtz.weighted_tripleGapDet_pairCompl` spends the design on one pair: the
weighted total of the gap determinants of every triple through `{a,b}` is a
closed form in that pair's leverages, pairing and weights.  This module adds it
up, and reads it at the two kinds of pair a corner carries.

## The aggregate keeps the design, and that is a surprise

The campaign's banked rule is that aggregating the gap determinants destroys the
design: `Gtz.weighted_aggregate_design_blind` proves
`∑_{a,b,c} t_a t_b t_c · tripleGapDet = −4` at EVERY design of EVERY size, so no
certificate of that shape can distinguish two designs.  The rule was stated for
the weighting `t_a t_b t_c`.

It is not a rule about aggregation.  Summing the pair budget over ordered pairs
weights each triple by `t_a + t_b + t_c` instead of `t_a t_b t_c`, and the
result (`Gtz.pairBudget_ordered_sum`, `Gtz.pairBudget_ordered_sum_closed`) is

  `∑_a ∑_{b ≠ a} ∑_{c ∉ {a,b}} t_c · tripleGapDet g_a g_b g_c
      = 2·∑_a ∑_{b ≠ a} q_ab·(t_a + t_b) − 2·(m−2)·∑_a (ℓ_a − 1) − 4` ,

which is NOT constant: measured over random `(6,3)` designs it ranges across
`−29` to `−82`, against the constant `−4` of the blind weighting.  So the
sum-weighting retains what the product-weighting destroys, and an aggregate
certificate is not dead in general -- only for the product.

## What a tie pays

Every triple of a tie whose leading pair is admissible and heavy has nonpositive
gap determinant, so on a design all of whose pairs are admissible and all of
whose atoms are strictly heavy -- the branch the hinge has no witness for -- the
whole aggregate is nonpositive (`Gtz.allAdmissible_tie_aggregate_nonpos`):

  `∑_a ∑_{b ≠ a} q_ab·(t_a + t_b)  ≤  (m−2)·∑_a (ℓ_a − 1) + 2` .

No determinant appears.  It is a bound on the weighted pair minors of that
branch by its leverages alone.

## The corner's two kinds of pair

A corner has rank-one inside gap, so all three of its inside pair minors vanish
and its own gap determinant is zero.  The budget at a boundary-admissible pair
(`Gtz.pairBudget_of_pairGapMinor_eq_zero`) is therefore exactly

  `−(ℓ_a − 1)(1 − t_b) − (ℓ_b − 1)(1 − t_a)` ,

nonpositive at heavy atoms, and at a corner one term of the sum -- the corner's
own triple -- drops out, leaving the three two-inside determinants alone
(`Gtz.weighted_tripleGapDet_offPair_of_vanishing`).  So a corner's inside pairs
carry no repayment at all, which is why the arm's whole question sits on the
outside pairs.

[MEASURED before proving.  The aggregate identity: max relative residual
`4.7e-12` over designs at sizes 4,5,6,7,9; exact at the `(5,3)` diamond, where
both sides are `−12`.  The corner readings: `|det(K_C − 1)|` and the three
inside pair minors below `9.9e-14`, and the inside-pair identity at `8.2e-15`,
over 2500 corners of the corrected chart.

SHARPNESS, and it is the campaign's non-strictness in a new place: at the
`(5,3)` diamond the budget is exactly zero at four of the ten pairs, and at each
of those all three gap determinants in the sum are exactly zero.  A real tie
attains the bound with every term vanishing, so no certificate built on it can
carry a positive constant.]
-/
import Gtz.Wave.PairComplementBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The budget as a function of the pair -/

/-- The pair budget: the closed form the design collapses to. -/
noncomputable def pairBudget (D : WeightedDesign m 3) (a b : Fin m) : ℝ :=
  2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
    - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
    - (leverageOf (D.atom b) - 1) * (1 - D.weight a)

/-- The landed identity, in the budget's own name. -/
theorem weighted_tripleGapDet_pairCompl' (D : WeightedDesign m 3) {a b : Fin m}
    (hab : a ≠ b) :
    ∑ c ∈ ({a, b} : Finset (Fin m))ᶜ,
        D.weight c * tripleGapDet (D.atom a) (D.atom b) (D.atom c)
      = pairBudget D a b :=
  weighted_tripleGapDet_pairCompl D hab

/-- The budget is symmetric in the pair, because the pair minor is. -/
theorem pairBudget_comm (D : WeightedDesign m 3) (a b : Fin m) :
    pairBudget D a b = pairBudget D b a := by
  rw [pairBudget, pairBudget, pairGapMinor_comm]; ring

/-! ## 2. A boundary-admissible pair carries no repayment -/

/-- **AT A VANISHING PAIR MINOR THE BUDGET IS THE PAIR'S OWN EXCESS FORM.**  The
minor term drops and what is left is nonpositive at heavy atoms.  A corner's
three inside pairs are exactly of this kind. -/
theorem pairBudget_of_pairGapMinor_eq_zero (D : WeightedDesign m 3) {a b : Fin m}
    (hq : pairGapMinor (D.atom a) (D.atom b) = 0) :
    pairBudget D a b
      = -((leverageOf (D.atom a) - 1) * (1 - D.weight b)
          + (leverageOf (D.atom b) - 1) * (1 - D.weight a)) := by
  rw [pairBudget, hq]; ring

/-- **AND IT IS NONPOSITIVE.**  Two heavy atoms at a boundary-admissible pair
cannot repay: every triple through them has, on the weighted total, nothing to
give. -/
theorem pairBudget_nonpos_of_pairGapMinor_eq_zero (D : WeightedDesign m 3)
    (hm : 2 ≤ m) {a b : Fin m}
    (ha : 1 ≤ leverageOf (D.atom a)) (hb : 1 ≤ leverageOf (D.atom b))
    (hq : pairGapMinor (D.atom a) (D.atom b) = 0) :
    pairBudget D a b ≤ 0 := by
  have hwa : D.weight a < 1 := weight_lt_one D hm a
  have hwb : D.weight b < 1 := weight_lt_one D hm b
  rw [pairBudget_of_pairGapMinor_eq_zero D hq]
  have h1 : 0 ≤ (leverageOf (D.atom a) - 1) * (1 - D.weight b) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (leverageOf (D.atom b) - 1) * (1 - D.weight a) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- **ONE TERM DROPS OUT.**  If a distinguished atom off the pair contributes a
vanishing gap determinant -- at a corner the third inside atom does, because the
corner's own gap has rank one -- the weighted total over the REMAINING atoms is
still the budget. -/
theorem weighted_tripleGapDet_offPair_of_vanishing (D : WeightedDesign m 3)
    {a b f : Fin m} (hab : a ≠ b) (hfa : f ≠ a) (hfb : f ≠ b)
    (hzero : tripleGapDet (D.atom a) (D.atom b) (D.atom f) = 0) :
    ∑ c ∈ (({a, b} : Finset (Fin m))ᶜ).erase f,
        D.weight c * tripleGapDet (D.atom a) (D.atom b) (D.atom c)
      = pairBudget D a b := by
  classical
  have hmem : f ∈ ({a, b} : Finset (Fin m))ᶜ := by
    simp [Finset.mem_compl, hfa, hfb]
  have hsplit := Finset.sum_erase_add (({a, b} : Finset (Fin m))ᶜ)
    (fun c => D.weight c * tripleGapDet (D.atom a) (D.atom b) (D.atom c)) hmem
  rw [hzero, mul_zero, add_zero] at hsplit
  rw [hsplit]
  exact weighted_tripleGapDet_pairCompl D hab

/-! ## 3. The aggregate over ordered pairs -/

/-- **THE AGGREGATE.**  Summing the pair identity over ordered pairs is one
congruence.  The left side weights each triple by the sum of its three weights,
not by their product, and that is what keeps the design in it. -/
theorem pairBudget_ordered_sum (D : WeightedDesign m 3) :
    ∑ a, ∑ b ∈ Finset.univ.erase a,
        ∑ c ∈ ({a, b} : Finset (Fin m))ᶜ,
          D.weight c * tripleGapDet (D.atom a) (D.atom b) (D.atom c)
      = ∑ a, ∑ b ∈ Finset.univ.erase a, pairBudget D a b := by
  classical
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  exact weighted_tripleGapDet_pairCompl D (Ne.symm (Finset.ne_of_mem_erase hb))

/-- An off-diagonal double sum is the full double sum less its diagonal. -/
theorem sum_offDiag_eq_sum_sub_diag (F : Fin m → Fin m → ℝ) :
    ∑ a, ∑ b ∈ Finset.univ.erase a, F a b
      = (∑ a, ∑ b, F a b) - ∑ a, F a a := by
  classical
  have hrow : ∀ a : Fin m,
      ∑ b ∈ Finset.univ.erase a, F a b = (∑ b, F a b) - F a a := by
    intro a
    have := Finset.sum_erase_add Finset.univ (F a) (Finset.mem_univ a)
    linarith
  rw [Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_sub_distrib]

/-- A constant against the coweights totals the size less one. -/
theorem sum_coweight (D : WeightedDesign m 3) :
    ∑ _b : Fin m, (1 : ℝ) - ∑ b, D.weight b = (m : ℝ) - 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    D.weight_sum_one]

/-- The mixed excess moment over ordered pairs.  Each atom meets every other
one, so its excess is counted `m - 2` times against the constant and once
against its own weight -- and the weighted total of the excesses is two. -/
theorem sum_offDiag_excess_mul_coweight (D : WeightedDesign m 3) :
    ∑ a, ∑ b ∈ Finset.univ.erase a,
        (leverageOf (D.atom a) - 1) * (1 - D.weight b)
      = ((m : ℝ) - 2) * ∑ a, (leverageOf (D.atom a) - 1) + 2 := by
  classical
  rw [sum_offDiag_eq_sum_sub_diag
    (fun a b => (leverageOf (D.atom a) - 1) * (1 - D.weight b))]
  have hfull : ∑ a, ∑ b, (leverageOf (D.atom a) - 1) * (1 - D.weight b)
      = ((m : ℝ) - 1) * ∑ a, (leverageOf (D.atom a) - 1) := by
    have hin : ∀ a : Fin m,
        ∑ b, (leverageOf (D.atom a) - 1) * (1 - D.weight b)
          = (leverageOf (D.atom a) - 1) * ((m : ℝ) - 1) := by
      intro a
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_sub_distrib]
      exact sum_coweight D
    rw [Finset.sum_congr rfl fun a _ => hin a, ← Finset.sum_mul]
    ring
  have hdiag : ∑ a, (leverageOf (D.atom a) - 1) * (1 - D.weight a)
      = (∑ a, (leverageOf (D.atom a) - 1)) - 2 := by
    have hterm : ∀ a : Fin m,
        (leverageOf (D.atom a) - 1) * (1 - D.weight a)
          = (leverageOf (D.atom a) - 1)
            - D.weight a * (leverageOf (D.atom a) - 1) := by
      intro a; ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_sub_distrib,
      total_weighted_excess D]
  rw [hfull, hdiag]
  ring

/-- **THE AGGREGATE IN CLOSED FORM.**  The weighted pair minors against the pair
weights, less the leverages counted `m - 2` times, less four. -/
theorem pairBudget_ordered_sum_closed (D : WeightedDesign m 3) :
    ∑ a, ∑ b ∈ Finset.univ.erase a, pairBudget D a b
      = 2 * (∑ a, ∑ b ∈ Finset.univ.erase a,
          pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b))
        - 2 * (((m : ℝ) - 2) * ∑ a, (leverageOf (D.atom a) - 1) + 2) := by
  classical
  have hterm : ∀ a b : Fin m,
      pairBudget D a b
        = 2 * (pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b))
          - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
          - (leverageOf (D.atom b) - 1) * (1 - D.weight a) := by
    intro a b; rw [pairBudget]; ring
  have hsplit : ∀ a : Fin m,
      ∑ b ∈ Finset.univ.erase a, pairBudget D a b
      = 2 * (∑ b ∈ Finset.univ.erase a,
            pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b))
        - (∑ b ∈ Finset.univ.erase a,
            (leverageOf (D.atom a) - 1) * (1 - D.weight b))
        - (∑ b ∈ Finset.univ.erase a,
            (leverageOf (D.atom b) - 1) * (1 - D.weight a)) := by
    intro a
    rw [Finset.sum_congr rfl fun b _ => hterm a b, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hswap : ∑ a, ∑ b ∈ Finset.univ.erase a,
        (leverageOf (D.atom b) - 1) * (1 - D.weight a)
      = ∑ a, ∑ b ∈ Finset.univ.erase a,
        (leverageOf (D.atom a) - 1) * (1 - D.weight b) := by
    rw [sum_offDiag_eq_sum_sub_diag
        (fun a b => (leverageOf (D.atom b) - 1) * (1 - D.weight a)),
      sum_offDiag_eq_sum_sub_diag
        (fun a b => (leverageOf (D.atom a) - 1) * (1 - D.weight b))]
    congr 1
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hswap,
    sum_offDiag_excess_mul_coweight D]
  ring

/-! ## 4. What a tie pays on the all-admissible branch -/

/-- **EVERY TRIPLE OF THE ALL-ADMISSIBLE BRANCH IS FLAT AT A TIE.**  With the
leading pair admissible and its first atom heavy, a positive gap determinant
would strictly dominate. -/
theorem tripleGapDet_nonpos_of_allAdmissible (D : WeightedDesign m 3)
    (htie : IsTie D)
    (hheavy : ∀ c : Fin m, 1 < leverageOf (D.atom c))
    (hadm : ∀ x y : Fin m, x ≠ y → 0 < pairGapMinor (D.atom x) (D.atom y))
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    tripleGapDet (D.atom a) (D.atom b) (D.atom c) ≤ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  refine htie.2 ({a, b, c} : Finset (Fin m)) ?_ ?_
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  · refine (subsetSum_posDef_iff_tripleGram D a b c hab hac hbc).mpr ?_
    exact (tripleGram_posDef_iff_pairVocabulary _ _ _).mpr
      ⟨by linarith [hheavy a], hadm a b hab, hcon⟩

/-- **THE BRANCH PAYS ITS WHOLE AGGREGATE.**  On a tie whose atoms are all
strictly heavy and whose pairs are all admissible, the weighted pair minors are
bounded by the leverages, with no determinant anywhere in the statement.

This is the branch of the hinge with no witness to point at -- a parallel pair is
never admissible, so such a design carries none -- and this is a constraint on it
in pair data alone. -/
theorem allAdmissible_tie_aggregate_nonpos (D : WeightedDesign m 3)
    (htie : IsTie D)
    (hheavy : ∀ c : Fin m, 1 < leverageOf (D.atom c))
    (hadm : ∀ x y : Fin m, x ≠ y → 0 < pairGapMinor (D.atom x) (D.atom y)) :
    ∑ a, ∑ b ∈ Finset.univ.erase a,
        pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
      ≤ ((m : ℝ) - 2) * ∑ a, (leverageOf (D.atom a) - 1) + 2 := by
  classical
  have hagg : ∑ a, ∑ b ∈ Finset.univ.erase a, pairBudget D a b ≤ 0 := by
    rw [← pairBudget_ordered_sum D]
    refine Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b hb => ?_
    have hab : a ≠ b := Ne.symm (Finset.ne_of_mem_erase hb)
    refine Finset.sum_nonpos fun c hc => ?_
    have hne : c ≠ a ∧ c ≠ b := by
      have := Finset.mem_compl.mp hc
      constructor <;> intro h <;> exact this (by simp [h])
    have hd := tripleGapDet_nonpos_of_allAdmissible D htie hheavy hadm hab
      (Ne.symm hne.1) (Ne.symm hne.2)
    have hw := (D.weight_pos c).le
    nlinarith [hw, hd]
  rw [pairBudget_ordered_sum_closed D] at hagg
  linarith

end Gtz
