/-
# Branch B caps its own pair minors

Every instrument this campaign has for a pair minor bounds it from BELOW or
asserts its sign: the landed pair-minor budget `Gtz.pairMinor_budget` totals the
weighted minors at one and hands back an admissible pair, the row floor
`Gtz.leverageExcess_floor_of_admissibleRow` turns positivity of a whole row into
a leverage bound, and the strong-pair law
`Gtz.exists_strongPair_of_tripleGapDet_nonpos` caps `q` by three quarters of the
excess product at ONE pair of a refused triple.  None of them caps a GIVEN pair.

The pair budget `Gtz.weighted_tripleGapDet_pairCompl`, landed this rotation,
spends the design on a pair: the weighted total of the gap determinants of the
triples through `{a,b}` is a closed form in that pair's own leverages, pairing
and weights, with the rest of the design cancelled.  On branch B every one of
those determinants is nonpositive and every weight is positive, so the total is
nonpositive and the closed form is an upper bound:

  **`Gtz.branchB_pairGapMinor_cap`:**
  `2·q_ab·(t_a + t_b) ≤ (l_a − 1)(1 − t_b) + (l_b − 1)(1 − t_a)` .

This is the first upper bound on a named pair minor in the campaign, and it
holds at EVERY pair of a branch-B boundary system rather than at one pair of one
triple.  It needs no chart, no probe and no corner.

## What it gives, and what it does not

Divided through by the positive `2(t_a + t_b)` it reads

  `q_ab ≤ (x_a(1 − t_b) + x_b(1 − t_a)) / (2(t_a + t_b))` ,   `x_c = l_c − 1` ,

so a pair of heavy weights forces a small minor, and the admissibility
`0 < q_ab` of branch B then forces the two excesses to be large together
(`Gtz.branchB_excess_pos_of_cap`).  Combined with the landed pair-minor budget
it eliminates the pairings from branch B altogether, leaving one scalar
inequality in the six weights and the six leverages.

[MEASURED: that eliminated system is NOT empty.  Maximising its slack over the
twelve scalars returns `+1.5000000000000027`, attained near
`t = (0.170, 0.063, 0.274, 0.095, 0.244, 0.153)` with
`l = (2.94, 7.94, 1.83, 5.25, 2.05, 3.26)`.  So the cap alone does not close
Question 7.5(a) of the survey, and a successor should not spend a round on the
eliminated system as posed.  The sibling identity itself was verified to
`1.3e-13` over one hundred and fifty random designs before this module was
written.]
-/
import Gtz.Wave.PairComplementBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The cap -/

/-- **BRANCH B CAPS EVERY ONE OF ITS PAIR MINORS.**  If every triple through the
pair `{a,b}` has nonpositive gap determinant, the pair budget's closed form is
an upper bound on twice the minor against the two weights.  Nothing else is
assumed: no tie, no primitivity, no heaviness anywhere. -/
theorem branchB_pairGapMinor_cap (D : WeightedDesign m 3) {a b : Fin m} (hab : a ≠ b)
    (hdet : ∀ c, c ≠ a → c ≠ b →
      tripleGapDet (D.atom a) (D.atom b) (D.atom c) ≤ 0) :
    2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
      ≤ (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        + (leverageOf (D.atom b) - 1) * (1 - D.weight a) := by
  classical
  have hid := weighted_tripleGapDet_pairCompl D hab
  have hle : ∑ c ∈ ({a, b} : Finset (Fin m))ᶜ,
      D.weight c * tripleGapDet (D.atom a) (D.atom b) (D.atom c) ≤ 0 := by
    refine Finset.sum_nonpos fun c hc => ?_
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hc
    have hw := (D.weight_pos c).le
    have hd := hdet c hc.1 hc.2
    nlinarith [hw, hd]
  linarith [hid, hle]

/-! ## 2. The excesses of an admissible pair are large together -/

/-- **AN ADMISSIBLE PAIR OF BRANCH B CARRIES EXCESS.**  The cap is an upper
bound on a quantity branch B makes positive, so the right side is positive too:
the two leverage excesses cannot both be small against the two co-weights. -/
theorem branchB_excess_pos_of_cap (D : WeightedDesign m 3) {a b : Fin m} (hab : a ≠ b)
    (hdet : ∀ c, c ≠ a → c ≠ b →
      tripleGapDet (D.atom a) (D.atom b) (D.atom c) ≤ 0)
    (hadm : 0 < pairGapMinor (D.atom a) (D.atom b)) :
    0 < (leverageOf (D.atom a) - 1) * (1 - D.weight b)
      + (leverageOf (D.atom b) - 1) * (1 - D.weight a) := by
  have hcap := branchB_pairGapMinor_cap D hab hdet
  have hwa := D.weight_pos a
  have hwb := D.weight_pos b
  nlinarith [hcap, hadm, hwa, hwb]

/-- **THE CAP IN QUOTIENT FORM.**  Twice the sum of the two weights is positive,
so the minor is bounded by the closed form divided by it. -/
theorem branchB_pairGapMinor_le_div (D : WeightedDesign m 3) {a b : Fin m} (hab : a ≠ b)
    (hdet : ∀ c, c ≠ a → c ≠ b →
      tripleGapDet (D.atom a) (D.atom b) (D.atom c) ≤ 0) :
    pairGapMinor (D.atom a) (D.atom b)
      ≤ ((leverageOf (D.atom a) - 1) * (1 - D.weight b)
          + (leverageOf (D.atom b) - 1) * (1 - D.weight a))
        / (2 * (D.weight a + D.weight b)) := by
  have hcap := branchB_pairGapMinor_cap D hab hdet
  have hpos : (0 : ℝ) < 2 * (D.weight a + D.weight b) := by
    have hwa := D.weight_pos a
    have hwb := D.weight_pos b
    linarith
  rw [le_div_iff₀ hpos]
  linarith [hcap]

/-! ## 3. The cap at a tie

A boundary system whose atoms are all strictly heavy and whose pairs are all
admissible has every gap determinant nonpositive, by the landed Sylvester
criterion, so the cap applies at every one of its pairs at once. -/

/-- **THE CAP AT EVERY PAIR OF A BRANCH-B DESIGN.**  Stated against the
hypothesis branch B actually supplies: all twenty gap determinants nonpositive. -/
theorem branchB_forall_pairGapMinor_cap (D : WeightedDesign m 3)
    (hdet : ∀ x y z : Fin m, x ≠ y → x ≠ z → y ≠ z →
      tripleGapDet (D.atom x) (D.atom y) (D.atom z) ≤ 0)
    {a b : Fin m} (hab : a ≠ b) :
    2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
      ≤ (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        + (leverageOf (D.atom b) - 1) * (1 - D.weight a) :=
  branchB_pairGapMinor_cap D hab
    (fun c hca hcb => hdet a b c hab (Ne.symm hca) (Ne.symm hcb))

end Gtz
