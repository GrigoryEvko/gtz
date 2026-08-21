/-
# The pair minor budget, and the admissible pair that every design carries

The campaign prices pairs with the second Sylvester minor of the gap,

  `Gtz.pairGapMinor a b = (l_a - 1)(l_b - 1) - (a . b)^2` ,

and calls a pair ADMISSIBLE when that minor is positive.  Admissibility is the
edge relation of the tie graph: the first Sylvester minor names one atom, the
second names one pair, and only the third sees a triple, so a tie is a statement
about a graph rather than about forms.  Every lane of the campaign has needed
the same missing fact about that graph — THAT IT HAS AN EDGE AT ALL — and each
has reached for it by descent.

This module proves it, exactly, for every weighted design.  There is no tie
hypothesis, no corner, no domination, and no size restriction.

## The conservation law

The weighted pair minors of a design total ONE over ordered pairs
(`Gtz.pairMinor_budget`):

  **`sum_a sum_b t_a t_b * pairGapMinor g_a g_b = 1`** .

This is a new conservation law, and it sits beside the two the campaign already
carries.  The wedge masses total six and the squared brackets total six, both
over ordered tuples.  The pair minor is the wedge shifted by the two leverages,

  `pairGapMinor a b = w_ab - l_a - l_b + 1` ,

so its budget is the wedge budget less twice the leverage total plus the weight
total: `6 - 3 - 3 + 1 = 1`.  The proof is that arithmetic and nothing else.

## What the budget buys

The diagonal of the pair minor is `1 - 2*l_a`, which the leverage total makes
strongly negative.  Moving it to the other side leaves the OFF-DIAGONAL budget

  `sum_{a != b} t_a t_b * pairGapMinor g_a g_b = 1 - sum_a t_a^2 + 2*sum_a t_a^2*l_a` ,

whose first two terms are the off-diagonal weight mass `1 - sum_a t_a^2`, itself
positive at every size of at least two.  So the off-diagonal mass is positive,
and one pair must carry a positive share (`Gtz.exists_offDiag_pairMinor_pos`).

Dividing the mass by the weight that carries it gives more than positivity.  The
best off-diagonal pair minor is strictly more than ONE at every design
(`Gtz.exists_offDiag_pairMinor_gt_one`), because the leftover `2*sum_a t_a^2*l_a`
is positive whenever a single atom is not zero.  The bound is sharp: at the
orthonormal design of three atoms every off-diagonal minor is exactly four, and
the estimate returns four.

## Why this closes an existence question in three lanes at once

A corner is a weak dominator whose gap is rank one.  Its three inside pair
minors are equal and vanish, so the inside triangle carries NO budget mass.  The
mass is conserved, so it moves to the pairs that meet the outside
(`Gtz.exists_pairMinor_pos_not_both_mem`): at a corner, some admissible pair has
an atom outside the dominator.  That statement is the existence half the two
horn lanes have been descending for, and it is also the edge the tie-graph
argument needs before Mantel can bite.

The budget is field-blind, as every determinant identity is.  It supplies an
edge, not a refutation, and the realness layer must still be spent where the
campaign already spends it.
-/
import Gtz.Wave.InvariantBudgets
import Gtz.Design.TripleGramSylvester

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

variable {m : ℕ}

/-! ## 1. The pair minor on the diagonal -/

/-- The self pairing of an atom is its leverage. -/
theorem dotProduct_self_eq_leverage (a : Fin 3 → ℝ) : a ⬝ᵥ a = leverageOf a := by
  simp only [leverageOf, dotProduct, Fin.sum_univ_three]; ring

/-- **THE DIAGONAL OF THE PAIR MINOR.**  A pair of one atom with itself has
minor `1 - 2*l`, because the two leverage excesses multiply to `(l-1)^2` and the
self pairing squares to `l^2`. -/
theorem pairGapMinor_self (a : Fin 3 → ℝ) :
    pairGapMinor a a = 1 - 2 * leverageOf a := by
  rw [pairGapMinor, dotProduct_self_eq_leverage]; ring

/-- The diagonal minor is at most one, because the leverage is not negative. -/
theorem pairGapMinor_self_le_one (a : Fin 3 → ℝ) : pairGapMinor a a ≤ 1 := by
  rw [pairGapMinor_self]
  have := leverageOf_nonneg a
  linarith

/-! ## 2. The conservation law -/

/-- **THE PAIR MINOR BUDGET.**  The weighted pair minors of any design total
exactly one over ordered pairs.  The pair minor is the wedge less the two
leverages plus one, so the three landed totals — wedge six, leverage three,
weight one — give `6 - 3 - 3 + 1 = 1`.

This is a conservation law of the same class as `Gtz.wedge_mass_budget` and
`Gtz.bracket_budget`, in the vocabulary the tie graph uses for its edges. -/
theorem pairMinor_budget (D : WeightedDesign m 3) :
    ∑ a, ∑ b, D.weight a * (D.weight b * pairGapMinor (D.atom a) (D.atom b)) = 1 := by
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = 3 := sum_weighted_leverage D
  have hone : ∑ c, D.weight c = 1 := D.weight_sum_one
  have hwedge := wedge_mass_budget D
  have hsplit : ∑ a, ∑ b, D.weight a * (D.weight b * pairGapMinor (D.atom a) (D.atom b))
      = (∑ a, ∑ b, D.weight a * (D.weight b
            * (leverageOf (D.atom a) * leverageOf (D.atom b) - atomPairing D a b ^ 2)))
        - (∑ a, ∑ b, (D.weight a * leverageOf (D.atom a)) * D.weight b)
        - (∑ a, ∑ b, D.weight a * (D.weight b * leverageOf (D.atom b)))
        + (∑ a, ∑ b, D.weight a * D.weight b) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [pairGapMinor, atomPairing]
    ring
  have e1 : ∑ a, ∑ b, (D.weight a * leverageOf (D.atom a)) * D.weight b = 3 := by
    rw [← Finset.sum_mul_sum, hlev, hone]; ring
  have e2 : ∑ a, ∑ b, D.weight a * (D.weight b * leverageOf (D.atom b)) = 3 := by
    have : ∑ a, ∑ b, D.weight a * (D.weight b * leverageOf (D.atom b))
        = ∑ a, ∑ b, D.weight a * (D.weight b * leverageOf (D.atom b)) := rfl
    rw [← Finset.sum_mul_sum, hone, hlev]; ring
  have e3 : ∑ a, ∑ b, D.weight a * D.weight b = 1 := by
    rw [← Finset.sum_mul_sum, hone]; ring
  rw [hsplit, hwedge, e1, e2, e3]; ring

/-! ## 3. The weight facts the split needs -/

/-- The squared weights total strictly less than one at two atoms or more, since
each weight is strictly between zero and one and so exceeds its own square. -/
theorem sum_weight_sq_lt_one {k : ℕ} (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ a, D.weight a ^ 2 < 1 := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, Fintype.card_fin]
    omega
  calc ∑ a, D.weight a ^ 2 < ∑ a, D.weight a := by
        refine Finset.sum_lt_sum_of_nonempty hne fun a _ => ?_
        have h1 := D.weight_pos a
        have h2 := weight_lt_one D hm a
        nlinarith
    _ = 1 := D.weight_sum_one

/-- The off-diagonal weight mass is one less the squared weights.  Erasing an
atom from its own row leaves `1 - t_a`, and weighting that by `t_a` and totalling
gives the statement. -/
theorem offDiag_weight_mass {k : ℕ} (D : WeightedDesign m k) :
    ∑ a, ∑ b ∈ Finset.univ.erase a, D.weight a * D.weight b
      = 1 - ∑ a, D.weight a ^ 2 := by
  have hrow : ∀ a : Fin m, ∑ b ∈ Finset.univ.erase a, D.weight a * D.weight b
      = D.weight a - D.weight a ^ 2 := by
    intro a
    rw [← Finset.mul_sum]
    have h := Finset.sum_erase_add Finset.univ D.weight (Finset.mem_univ a)
    rw [D.weight_sum_one] at h
    have hb : ∑ b ∈ Finset.univ.erase a, D.weight b = 1 - D.weight a := by linarith
    rw [hb]; ring
  rw [Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_sub_distrib, D.weight_sum_one]

/-! ## 4. The off-diagonal budget -/

/-- **THE OFF-DIAGONAL PAIR MINOR BUDGET.**  Removing the diagonal from the
conservation law leaves the mass that the true pairs carry:

  `sum_{a != b} t_a t_b * pairGapMinor = 1 - sum_a t_a^2 + 2*sum_a t_a^2*l_a` .

The first two terms are the off-diagonal weight mass, and the last term is a
strictly positive leftover at every design. -/
theorem pairMinor_offDiag_budget (D : WeightedDesign m 3) :
    ∑ a, ∑ b ∈ Finset.univ.erase a,
        D.weight a * (D.weight b * pairGapMinor (D.atom a) (D.atom b))
      = 1 - ∑ a, D.weight a ^ 2 + 2 * ∑ a, D.weight a ^ 2 * leverageOf (D.atom a) := by
  have key : ∀ a : Fin m,
      (∑ b ∈ Finset.univ.erase a, D.weight a * (D.weight b * pairGapMinor (D.atom a) (D.atom b)))
      = (∑ b, D.weight a * (D.weight b * pairGapMinor (D.atom a) (D.atom b)))
        - (D.weight a ^ 2 - 2 * (D.weight a ^ 2 * leverageOf (D.atom a))) := by
    intro a
    have h := Finset.sum_erase_add Finset.univ
      (fun b => D.weight a * (D.weight b * pairGapMinor (D.atom a) (D.atom b)))
      (Finset.mem_univ a)
    have hd : D.weight a * (D.weight a * pairGapMinor (D.atom a) (D.atom a))
        = D.weight a ^ 2 - 2 * (D.weight a ^ 2 * leverageOf (D.atom a)) := by
      rw [pairGapMinor_self]; ring
    rw [hd] at h
    linarith
  have hexp : ∑ a, (D.weight a ^ 2 - 2 * (D.weight a ^ 2 * leverageOf (D.atom a)))
      = (∑ a, D.weight a ^ 2) - 2 * ∑ a, D.weight a ^ 2 * leverageOf (D.atom a) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun a _ => key a, Finset.sum_sub_distrib, pairMinor_budget D, hexp]
  ring

/-- The weighted leverage moment is not negative, and it is the leftover term of
the off-diagonal budget. -/
theorem sum_weightSq_leverage_nonneg {k : ℕ} (D : WeightedDesign m k) :
    0 ≤ ∑ a, D.weight a ^ 2 * leverageOf (D.atom a) :=
  Finset.sum_nonneg fun a _ => mul_nonneg (sq_nonneg _) (leverageOf_nonneg _)

/-- The weighted leverage moment is strictly positive, because the leverages
total three against the weights and cannot all be zero. -/
theorem sum_weightSq_leverage_pos (D : WeightedDesign m 3) :
    0 < ∑ a, D.weight a ^ 2 * leverageOf (D.atom a) := by
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = 3 := sum_weighted_leverage D
  obtain ⟨a, -, ha⟩ : ∃ a ∈ Finset.univ, 0 < D.weight a * leverageOf (D.atom a) := by
    by_contra hcon
    push_neg at hcon
    have hnp : ∑ c, D.weight c * leverageOf (D.atom c) ≤ 0 :=
      Finset.sum_nonpos fun c hc => hcon c hc
    linarith
  refine Finset.sum_pos' (fun c _ => mul_nonneg (sq_nonneg _) (leverageOf_nonneg _))
    ⟨a, Finset.mem_univ a, ?_⟩
  have hw := D.weight_pos a
  nlinarith [leverageOf_nonneg (D.atom a)]

/-! ## 5. Every design carries an admissible pair -/

/-- **EVERY DESIGN CARRIES AN ADMISSIBLE PAIR.**  No tie hypothesis, no corner,
no domination, and no size beyond two atoms.  If every off-diagonal pair minor
were not positive, the off-diagonal budget would put the whole mass on the
diagonal, where the minor is at most one — and the squared weights total less
than one, so the mass does not fit. -/
theorem exists_offDiag_pairMinor_pos (D : WeightedDesign m 3) (hm : 2 ≤ m) :
    ∃ a b, a ≠ b ∧ 0 < pairGapMinor (D.atom a) (D.atom b) := by
  by_contra hcon
  push_neg at hcon
  have hle : ∑ a, ∑ b ∈ Finset.univ.erase a,
      D.weight a * (D.weight b * pairGapMinor (D.atom a) (D.atom b)) ≤ 0 := by
    refine Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b hb => ?_
    have hne : a ≠ b := fun h => (Finset.ne_of_mem_erase hb) h.symm
    have hwa := D.weight_pos a
    have hwb := D.weight_pos b
    have hgrp := mul_nonneg (mul_pos hwa hwb).le (neg_nonneg.mpr (hcon a b hne))
    nlinarith [hgrp]
  have hbud := pairMinor_offDiag_budget D
  have hsq := sum_weight_sq_lt_one D hm
  have hlev := sum_weightSq_leverage_nonneg D
  linarith

/-- **THE BEST PAIR MINOR PASSES ONE.**  Dividing the off-diagonal mass by the
off-diagonal weight that carries it leaves a strict surplus of
`2*sum_a t_a^2*l_a`, so some pair minor is strictly more than one.

The estimate is sharp.  At the orthonormal design of three atoms every weight is
one third, every leverage is three, every off-diagonal minor is four, and the
bound returns four. -/
theorem exists_offDiag_pairMinor_gt_one (D : WeightedDesign m 3) (hm : 2 ≤ m) :
    ∃ a b, a ≠ b ∧ 1 < pairGapMinor (D.atom a) (D.atom b) := by
  by_contra hcon
  push_neg at hcon
  have hle : ∑ a, ∑ b ∈ Finset.univ.erase a,
      D.weight a * (D.weight b * pairGapMinor (D.atom a) (D.atom b))
      ≤ ∑ a, ∑ b ∈ Finset.univ.erase a, D.weight a * D.weight b := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b hb => ?_
    have hne : a ≠ b := fun h => (Finset.ne_of_mem_erase hb) h.symm
    have hwa := D.weight_pos a
    have hwb := D.weight_pos b
    have hgrp := mul_le_mul_of_nonneg_left (hcon a b hne) (mul_pos hwa hwb).le
    nlinarith [hgrp]
  rw [pairMinor_offDiag_budget D, offDiag_weight_mass D] at hle
  have := sum_weightSq_leverage_pos D
  linarith

/-! ## 6. The corner consequence -/

/-- **AN ADMISSIBLE PAIR ALWAYS MEETS THE COMPLEMENT OF A DEAD SET.**  If every
internal pair of a set carries no positive minor, the budget's admissible pair
cannot sit inside that set.

A corner supplies exactly that hypothesis without any tie assumption: the gap of
a weak dominator is rank one, its three inside pair minors are equal, and weak
domination makes them vanish.  So at a corner some admissible pair has an atom
outside the dominator — the existence fact the horn lanes need, and the edge the
tie-graph argument needs before an extremal-graph bound can bite. -/
theorem exists_pairMinor_pos_not_both_mem (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (C : Finset (Fin m))
    (hdead : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → pairGapMinor (D.atom a) (D.atom b) ≤ 0) :
    ∃ a b, a ≠ b ∧ ¬(a ∈ C ∧ b ∈ C) ∧ 0 < pairGapMinor (D.atom a) (D.atom b) := by
  obtain ⟨a, b, hne, hpos⟩ := exists_offDiag_pairMinor_pos D hm
  refine ⟨a, b, hne, ?_, hpos⟩
  rintro ⟨ha, hb⟩
  exact absurd hpos (not_lt.mpr (hdead a ha b hb hne))

/-- The same statement with the surplus kept: the pair that meets the complement
of a dead set carries a minor strictly past one. -/
theorem exists_pairMinor_gt_one_not_both_mem (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (C : Finset (Fin m))
    (hdead : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → pairGapMinor (D.atom a) (D.atom b) ≤ 1) :
    ∃ a b, a ≠ b ∧ ¬(a ∈ C ∧ b ∈ C) ∧ 1 < pairGapMinor (D.atom a) (D.atom b) := by
  obtain ⟨a, b, hne, hgt⟩ := exists_offDiag_pairMinor_gt_one D hm
  refine ⟨a, b, hne, ?_, hgt⟩
  rintro ⟨ha, hb⟩
  exact absurd hgt (not_lt.mpr (hdead a ha b hb hne))

end Gtz
