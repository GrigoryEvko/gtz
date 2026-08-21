/-
# The second invariant, summed over a pair, and the producer with no side condition

`Gtz.weighted_tripleGapDet_pairCompl` spends the design on a pair through the
THIRD symmetric invariant of a triple's gap.  The landed
`Gtz.sum_weight_mul_pairGapMinor` does the same for a single row of the SECOND.
This module puts them together.

## The second invariant has a pair budget too

`Gtz.secondInvariant_tripleGap_eq_pairMinorSum` reads `e₂` of a triple's gap as
the sum of its three pair minors, so summing `e₂` over the atoms off a pair is
one pair minor carried by the complement's mass plus two rows of minors, and
each row is the landed row law.  The design cancels exactly as it did for `e₃`
(`Gtz.weighted_pairMinorSum_pairCompl`):

  `∑_{c ∉ {a,b}} t_c · (q_ab + q_ac + q_bc)
      = q_ab·(1 − 2t_a − 2t_b) + ℓ_a·(1 + 2t_a) + ℓ_b·(1 + 2t_b) − 4 − t_a − t_b` .

So BOTH invariants that the new symmetric criterion needs have closed-form pair
budgets, and neither mentions an atom off the pair.

## The producer loses its side condition

`Gtz.not_isTie_of_pairBudget_pos` asked for an admissible pair.  It does not need
one: at heavy atoms a positive budget FORCES admissibility, because the two
subtracted terms of the budget are then nonnegative and

  `2·q_ab·(t_a + t_b) = budget + (ℓ_a−1)(1−t_b) + (ℓ_b−1)(1−t_a) > 0` .

Strict heaviness follows from the minor in turn.  So
`Gtz.not_isTie_of_pairBudget_pos_of_heavy` needs only `1 ≤ ℓ` at the two atoms,
and at a tie that is free (`Gtz.leverage_one_le_of_isTie`).  The criterion is
then: **a positive budget at ANY pair refutes the tie**, with nothing to check.

## What the second budget buys, and what it does not

`Gtz.isTie_triple_pairMinorSum_or_det_nonpos` says every triple of a boundary
system has `e₂ ≤ 0` or `e₃ ≤ 0`.  A positive second budget names a triple with
`e₂ > 0` (`Gtz.exists_pairMinorSum_pos_of_budget_pos`), and at a tie that triple
is forced flat (`Gtz.exists_tripleGapDet_nonpos_of_pairMinorSum_budget_pos`).

That is a genuine consequence and it is NOT a producer.  The disjunction resists
summation: at each atom off the pair at most one of `e₂` and `e₃` is positive, so
`e₂ + e₃ ≤ max(e₂, e₃)` and no weighted total of the two is bounded.  This is
the arm's standing rule -- select a slot or multiply slots, never add them -- met
again, now in the one place where both invariants are simultaneously in closed
form.

[MEASURED before proving.  The second budget: max relative residual `4.5e-13`
over designs at sizes 4,5,6,7,9.  The row law reproduces exactly at the `(5,3)`
diamond, row sums `[0, 1.25, 1.25, 1.25, 1.25]` against `ℓ_a − 2`.

A REFUTATION, caught by the mandatory calibration and recorded so no successor
repeats it.  The identity holds at every design, so it is tempting to apply it
to the REWEIGHTED atoms `h_c = √(t_c/s_c)·g_c` with weights `s`, which satisfy
Parseval for every positive `s` summing to one, and to optimise `s`.  That
family measured `100.000%` on `(6,3)` where the plain budget measured `98.667%`.
IT IS UNSOUND: domination sums the atoms UNWEIGHTED, so `∑_{c∈T} h_c h_cᵀ`
is not `∑_{c∈T} g_c g_cᵀ` and the reweighted design has different dominators.
The `(5,3)` diamond, a genuine tie, returns `+∞` under the family.]
-/
import Gtz.Wave.PairComplementBudget
import Gtz.Wave.SymmetricTripleCriterion
import Gtz.Wave.InsertionDowndateLedger
import Gtz.Wave.PairMinorBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. Summing over the complement of a pair -/

/-- A sum over everything off a pair is the total less the pair's two terms. -/
theorem sum_pairCompl_eq (f : Fin m → ℝ) {a b : Fin m} (hab : a ≠ b) :
    ∑ c ∈ ({a, b} : Finset (Fin m))ᶜ, f c = (∑ c, f c) - f a - f b := by
  classical
  have hsplit := Finset.sum_add_sum_compl ({a, b} : Finset (Fin m)) f
  rw [Finset.sum_pair hab] at hsplit
  linarith

/-! ## 2. The second invariant's pair budget -/

/-- **THE SECOND BUDGET.**  The design-weighted total of the pair-minor sums of
every triple through a pair is a closed form in that pair's leverages, pairing
and weights.  Two rows of the landed row law and one carried minor. -/
theorem weighted_pairMinorSum_pairCompl (D : WeightedDesign m 3) {a b : Fin m}
    (hab : a ≠ b) :
    ∑ c ∈ ({a, b} : Finset (Fin m))ᶜ,
        D.weight c * (pairGapMinor (D.atom a) (D.atom b)
          + pairGapMinor (D.atom a) (D.atom c)
          + pairGapMinor (D.atom b) (D.atom c))
      = pairGapMinor (D.atom a) (D.atom b) * (1 - 2 * D.weight a - 2 * D.weight b)
        + leverageOf (D.atom a) * (1 + 2 * D.weight a)
        + leverageOf (D.atom b) * (1 + 2 * D.weight b)
        - 4 - D.weight a - D.weight b := by
  classical
  have hterm : ∀ c : Fin m,
      D.weight c * (pairGapMinor (D.atom a) (D.atom b)
          + pairGapMinor (D.atom a) (D.atom c)
          + pairGapMinor (D.atom b) (D.atom c))
        = D.weight c * pairGapMinor (D.atom a) (D.atom b)
          + D.weight c * pairGapMinor (D.atom a) (D.atom c)
          + D.weight c * pairGapMinor (D.atom b) (D.atom c) := by
    intro c; ring
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  rw [sum_pairCompl_eq _ hab, sum_pairCompl_eq _ hab, sum_pairCompl_eq _ hab]
  rw [← Finset.sum_mul, D.weight_sum_one, sum_weight_mul_pairGapMinor D a,
    sum_weight_mul_pairGapMinor D b, pairGapMinor_self, pairGapMinor_self,
    pairGapMinor_comm (D.atom b) (D.atom a)]
  ring

/-! ## 3. The producer without a side condition -/

/-- **A POSITIVE BUDGET FORCES ADMISSIBILITY.**  At heavy atoms the two
subtracted terms of the budget are nonnegative, so the minor term alone carries
the whole positive value. -/
theorem pairGapMinor_pos_of_pairBudget_pos (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b : Fin m}
    (ha : 1 ≤ leverageOf (D.atom a)) (hb : 1 ≤ leverageOf (D.atom b))
    (hpos : 0 < 2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
        - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        - (leverageOf (D.atom b) - 1) * (1 - D.weight a)) :
    0 < pairGapMinor (D.atom a) (D.atom b) := by
  have hwa : D.weight a < 1 := weight_lt_one D hm a
  have hwb : D.weight b < 1 := weight_lt_one D hm b
  have hw : 0 < D.weight a + D.weight b :=
    add_pos (D.weight_pos a) (D.weight_pos b)
  have h1 : 0 ≤ (leverageOf (D.atom a) - 1) * (1 - D.weight b) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (leverageOf (D.atom b) - 1) * (1 - D.weight a) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hpos, h1, h2, hw]

/-- **STRICT HEAVINESS COMES WITH IT.**  A positive minor cannot come from a
vanishing excess. -/
theorem one_lt_leverage_of_pairBudget_pos (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b : Fin m}
    (ha : 1 ≤ leverageOf (D.atom a)) (hb : 1 ≤ leverageOf (D.atom b))
    (hpos : 0 < 2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
        - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        - (leverageOf (D.atom b) - 1) * (1 - D.weight a)) :
    1 < leverageOf (D.atom a) := by
  have hq := pairGapMinor_pos_of_pairBudget_pos D hm ha hb hpos
  rcases eq_or_lt_of_le ha with heq | hlt
  · exfalso
    rw [pairGapMinor, ← heq] at hq
    nlinarith [sq_nonneg (D.atom a ⬝ᵥ D.atom b)]
  · exact hlt

/-- **THE PRODUCER, WITH NOTHING TO CHECK.**  Heaviness at the two atoms is all
it asks, and at a tie heaviness is free.  So a positive budget at ANY pair
refutes the tie. -/
theorem not_isTie_of_pairBudget_pos_of_heavy (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b : Fin m} (hab : a ≠ b)
    (ha : 1 ≤ leverageOf (D.atom a)) (hb : 1 ≤ leverageOf (D.atom b))
    (hpos : 0 < 2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
        - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        - (leverageOf (D.atom b) - 1) * (1 - D.weight a)) :
    ¬ IsTie D :=
  not_isTie_of_pairBudget_pos D hab
    (one_lt_leverage_of_pairBudget_pos D hm ha hb hpos)
    (pairGapMinor_pos_of_pairBudget_pos D hm ha hb hpos) hpos

/-! ## 4. What the second budget names -/

/-- **A POSITIVE SECOND BUDGET NAMES A TRIPLE WITH POSITIVE `e₂`.** -/
theorem exists_pairMinorSum_pos_of_budget_pos (D : WeightedDesign m 3)
    {a b : Fin m} (hab : a ≠ b)
    (hpos : 0 < pairGapMinor (D.atom a) (D.atom b)
          * (1 - 2 * D.weight a - 2 * D.weight b)
        + leverageOf (D.atom a) * (1 + 2 * D.weight a)
        + leverageOf (D.atom b) * (1 + 2 * D.weight b)
        - 4 - D.weight a - D.weight b) :
    ∃ c : Fin m, c ≠ a ∧ c ≠ b
      ∧ 0 < pairGapMinor (D.atom a) (D.atom b)
          + pairGapMinor (D.atom a) (D.atom c)
          + pairGapMinor (D.atom b) (D.atom c) := by
  classical
  rw [← weighted_pairMinorSum_pairCompl D hab] at hpos
  by_contra hcon
  push Not at hcon
  have hnonpos : ∑ c ∈ ({a, b} : Finset (Fin m))ᶜ,
      D.weight c * (pairGapMinor (D.atom a) (D.atom b)
        + pairGapMinor (D.atom a) (D.atom c)
        + pairGapMinor (D.atom b) (D.atom c)) ≤ 0 := by
    refine Finset.sum_nonpos fun c hc => ?_
    have hne : c ≠ a ∧ c ≠ b := by
      have := Finset.mem_compl.mp hc
      constructor <;> intro h <;> exact this (by simp [h])
    have hw := (D.weight_pos c).le
    have hd := hcon c hne.1 hne.2
    nlinarith [hw, hd]
  linarith

/-- **AND AT A TIE THAT TRIPLE IS FLAT.**  The new symmetric criterion turns a
positive second invariant into a nonpositive determinant. -/
theorem exists_tripleGapDet_nonpos_of_pairMinorSum_budget_pos
    (D : WeightedDesign m 3) (htie : IsTie D) {a b : Fin m} (hab : a ≠ b)
    (ha : 1 ≤ leverageOf (D.atom a)) (hb : 1 ≤ leverageOf (D.atom b))
    (hheavy : ∀ c : Fin m, 1 ≤ leverageOf (D.atom c))
    (hnotall : ∀ c : Fin m, 1 < leverageOf (D.atom a) + leverageOf (D.atom b)
        + leverageOf (D.atom c) - 2)
    (hpos : 0 < pairGapMinor (D.atom a) (D.atom b)
          * (1 - 2 * D.weight a - 2 * D.weight b)
        + leverageOf (D.atom a) * (1 + 2 * D.weight a)
        + leverageOf (D.atom b) * (1 + 2 * D.weight b)
        - 4 - D.weight a - D.weight b) :
    ∃ c : Fin m, c ≠ a ∧ c ≠ b
      ∧ tripleGapDet (D.atom a) (D.atom b) (D.atom c) ≤ 0 := by
  obtain ⟨c, hca, hcb, he2⟩ := exists_pairMinorSum_pos_of_budget_pos D hab hpos
  refine ⟨c, hca, hcb, ?_⟩
  rcases isTie_triple_pairMinorSum_or_det_nonpos D htie hab (Ne.symm hca)
    (Ne.symm hcb) ha hb (hheavy c) (hnotall c) with h | h
  · exact absurd he2 (by linarith)
  · exact h

end Gtz
