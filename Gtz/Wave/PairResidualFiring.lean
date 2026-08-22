/-
# The firing budget of the pair producer, and the leverage floor that empties it

The campaign's cheapest producer at a pair is
`Gtz.not_isTie_of_pairBudget_pos_of_heavy`: at two heavy atoms a POSITIVE value of

  `E(a,b) := 2 q_ab (t_a + t_b) - (l_a - 1)(1 - t_b) - (l_b - 1)(1 - t_a)`

refutes the tie outright, with nothing else to check.  The producer is landed and
its per-pair form is sharp.  What the tree never asked is the only question that
decides whether the producer is a ROUTE: **at how many pairs can it fire?**

This module answers it, and the answer is none often enough to matter.

## 1. The firing value has a closed total

`Gtz.pairFiringValue` names `E(a,b)`.  Summing it over the ordered pairs of
distinct atoms collapses onto the leverage total alone
(`Gtz.sum_offDiag_pairFiringValue`):

  **`sum_{a != b} E(a,b) = (8 - 2m) * L + 2m^2 - 12m + 16`** ,   `L := sum_c l_c` .

Nothing else survives -- not one angle, not one individual weight.  The proof is
two readings of the landed row law `Gtz.sum_weight_mul_pairGapMinor` (once as it
stands, once after `Gtz.pairGapMinor_comm`), the self term
`Gtz.pairGapMinor_self`, and the two Parseval totals.

## 2. At `(6,3)` the total is at most `-20`, at EVERY design

At the hinge's own cell the total is `16 - 4L`
(`Gtz.sum_offDiag_pairFiringValue_sixThree`), and the landed leverage floor
`Gtz.sixThree_nine_le_sum_leverage` puts `L` at nine or more.  So

  **`sum_{a != b} E(a,b) <= -20`**   at every `(6,3)` design

(`Gtz.sum_offDiag_pairFiringValue_le`), that is `-2/3` for each of the thirty
ordered pairs on average.  The producer does not fail narrowly at the residual: it
fails by a fixed margin at EVERY design of the open cell, including the ones where
`GtzWeighted 6 3` is easy.  **A route that selects a firing pair cannot exist.**
This is a NO-GO, and it is the point of the file.

## 3. The window it can fire in

Firing needs more than a positive total, and the necessary condition is free of
every angle.  Since `q_ab <= (l_a - 1)(l_b - 1)` always,

  **`(l_a-1)(1-t_b) + (l_b-1)(1-t_a) < 2 (t_a+t_b) (l_a-1)(l_b-1)`**

(`Gtz.window_of_pairFiringValue_pos`), which in divided form is
`(1-t_a)/(l_a-1) + (1-t_b)/(l_b-1) < 2(t_a+t_b)`.  So the producer lives on HEAVY
pairs only.  Read at the uniform frame `t = 1/6`, `l = 3` the left side is `5/6`
and the right side is `2/3`: the producer is SILENT at every pair of it
(`Gtz.pairFiringValue_nonpos_of_uniformFrame`), although that design has a strict
dominator.  A per-atom half of the window is `2 s_c - t_c > 1`, and at most FOUR
of the six atoms can meet it (`Gtz.card_strongAtoms_le_four`).

## 4. What the file leaves standing, and what it does NOT reach

The budget above integrates the producer against the PAIRS.  Every per-TRIPLE
route survives it untouched, and the tree already carries the sharpest of them:
`Gtz.exists_strong_triangle_of_isTie_of_allHeavy` and
`Gtz.gtzWeighted_sixThree_of_strongGraph` in `Gtz/Wave/ElliptopeTrichotomy.lean`
turn the quarter-slack cell `Gtz.subsetSum_posDef_of_quarterSlack` into a
triangle-free graph and spend Mantel and Ramsey on it.  Nothing here weakens or
duplicates that: a weaker per-triple restatement was written for this file and
DELETED once the sibling landed, because the sibling's is strictly stronger.

The distinction is the point.  An INTEGRATED producer at the pairs is dead by the
budget, at every design of the open cell and by a fixed margin.  A SELECTED one at
a single triple is not, and that is where the cell is still open.

[MEASURED, exact rational arithmetic, at the landed `(5,3)` diamond
`Gtz.diamondTieDesign` and at its `(6,3)` duplicate splits.  The four rim pairs
with `|<g_a,g_b>| = 3/4` carry `E = 0` EXACTLY, the two rim pairs with
`|<g_a,g_b>| = 7/4` carry `E = -2`, and the four pairs meeting the diagonal edge
carry `E = -2`.  Total `-12`, against the formula `-L + 3 = -15 + 3` at `m = 5`.
CONFIRMED BY A SECOND, INDEPENDENT ROUTE, at the coordinator's instruction.  The
landed doubled criterion `Gtz.dominates_of_sum_coLeverageRatio_le_two` reads
domination off one determinant sign once a triple's co-leverage ratios total at
most two.  At the `(6,3)` split the ratios are `8/9` at the two halves and `7/16`
at the four rim atoms, totalling `127/36 < 4`, and SIXTEEN of the twenty triples
qualify by mass.  Of those, twelve carry `det(S_T - 1) = 0` and four carry `-10`;
the four that fail the mass test carry `-15/4`.  **No triple has a positive
determinant, so there is no strict dominator and the two routes agree.**  The same
computation at the `(5,3)` primitive returns eight zeros and two values `-10` at
exactly the two circuits `{ab,ac,bc}` and `{ab,ad,bd}`, reproducing
`Gtz.diamondTieDesign_no_strictDominator`.

The agreement is term by term, not merely in sign.  The aggregate identity
`sum_{e not in {c,d}} t_e det(S_{cde} - 1) = E(c,d)` reproduces every firing value
above from those determinants: a rim pair with `|<g,g>| = 3/4` sees four zeros and
gives `0`, a rim pair with `7/4` sees `(-10, -10, 0, 0)` against weights
`(1/10, 1/10, 1/5, 1/5)` and gives `-2`, and a half-to-rim pair sees
`(-15/4, 0, -10, 0)` and gives `-19/8`.

So the producer is not merely silent at the diamond: it is EXACTLY TIGHT at four
of its pairs, which is what a boundary system must do, and it therefore admits no
strengthening that keeps the diamond a tie.  Splitting the diagonal edge changes
neither the rim leverages nor the rim weights nor the rim overlaps, so every rim
value is inherited verbatim by the `(6,3)` splits.  None of that paragraph is
proved here.]
-/
import Gtz.Wave.PairMinorSumBudget
import Gtz.Wave.TripleDeterminantCells
import Gtz.Design.StressFreeStratum
import Gtz.Quantitative.ChartHadamard

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The firing value -/

/-- **THE FIRING VALUE OF THE PAIR PRODUCER.**  A positive value at two heavy
atoms refutes the tie (`Gtz.not_isTie_of_pairBudget_pos_of_heavy`).  This names
the quantity so that it can be summed. -/
noncomputable def pairFiringValue (D : WeightedDesign m 3) (a b : Fin m) : ℝ :=
  2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
    - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
    - (leverageOf (D.atom b) - 1) * (1 - D.weight a)

/-- The firing value is symmetric in its two atoms. -/
theorem pairFiringValue_comm (D : WeightedDesign m 3) (a b : Fin m) :
    pairFiringValue D a b = pairFiringValue D b a := by
  rw [pairFiringValue, pairFiringValue, pairGapMinor_comm]
  ring

/-- The producer, restated on the named value: a positive firing value at two
heavy atoms refutes the tie.  This is `Gtz.not_isTie_of_pairBudget_pos_of_heavy`
with the value named. -/
theorem not_isTie_of_pairFiringValue_pos (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b : Fin m} (hab : a ≠ b)
    (ha : 1 ≤ leverageOf (D.atom a)) (hb : 1 ≤ leverageOf (D.atom b))
    (hpos : 0 < pairFiringValue D a b) :
    ¬ IsTie D :=
  not_isTie_of_pairBudget_pos_of_heavy D hm hab ha hb hpos

/-! ## 2. The two readings of the landed row law

`Gtz.sum_weight_mul_pairGapMinor` totals a row of the pair minors against the
weights.  The double sum needs it twice: once with the weight on the SUMMED slot,
once with the weight on the FIXED slot.  The second is the first after
`Gtz.pairGapMinor_comm`. -/

/-- The double total of the pair minors, weighted on the inner slot. -/
theorem sum_sum_weight_right_mul_pairGapMinor (D : WeightedDesign m 3) :
    ∑ a, ∑ b, D.weight b * pairGapMinor (D.atom a) (D.atom b)
      = (∑ a, leverageOf (D.atom a)) - 2 * (m : ℝ) := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => sum_weight_mul_pairGapMinor D a,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- The double total of the pair minors, weighted on the OUTER slot.  The same
number: the pair minor does not care which way round it is read. -/
theorem sum_sum_weight_left_mul_pairGapMinor (D : WeightedDesign m 3) :
    ∑ a, ∑ b, D.weight a * pairGapMinor (D.atom a) (D.atom b)
      = (∑ a, leverageOf (D.atom a)) - 2 * (m : ℝ) := by
  rw [Finset.sum_comm]
  have hrow : ∀ b : Fin m, ∑ a, D.weight a * pairGapMinor (D.atom a) (D.atom b)
      = leverageOf (D.atom b) - 2 := by
    intro b
    rw [← sum_weight_mul_pairGapMinor D b]
    exact Finset.sum_congr rfl fun a _ => by rw [pairGapMinor_comm]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hrow b,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- The double total of the leverage excess against the co-weights, read with the
excess on the outer slot. -/
theorem sum_sum_leverageSub_mul_coWeight (D : WeightedDesign m 3) :
    ∑ a, ∑ b, (leverageOf (D.atom a) - 1) * (1 - D.weight b)
      = ((∑ a, leverageOf (D.atom a)) - (m : ℝ)) * ((m : ℝ) - 1) := by
  have hco : ∑ b, (1 - D.weight b) = (m : ℝ) - 1 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, D.weight_sum_one]
    ring
  have hexcess : ∑ a, (leverageOf (D.atom a) - 1) = (∑ a, leverageOf (D.atom a)) - (m : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hinner : ∀ a : Fin m, ∑ b, (leverageOf (D.atom a) - 1) * (1 - D.weight b)
      = (leverageOf (D.atom a) - 1) * ((m : ℝ) - 1) := by
    intro a
    rw [← Finset.mul_sum, hco]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hinner a, ← Finset.sum_mul, hexcess]

/-- The same total with the excess on the INNER slot. -/
theorem sum_sum_coWeight_mul_leverageSub (D : WeightedDesign m 3) :
    ∑ a, ∑ b, (leverageOf (D.atom b) - 1) * (1 - D.weight a)
      = ((∑ a, leverageOf (D.atom a)) - (m : ℝ)) * ((m : ℝ) - 1) := by
  rw [Finset.sum_comm]
  have hswap : ∀ b : Fin m, ∑ a, (leverageOf (D.atom b) - 1) * (1 - D.weight a)
      = ∑ a, (leverageOf (D.atom b) - 1) * (1 - D.weight a) := fun _ => rfl
  rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hswap b]
  exact sum_sum_leverageSub_mul_coWeight D

/-! ## 3. The closed total of the firing value -/

/-- **THE FULL DOUBLE TOTAL.**  Every angle has cancelled: only the leverage total
and the size remain. -/
theorem sum_sum_pairFiringValue (D : WeightedDesign m 3) :
    ∑ a, ∑ b, pairFiringValue D a b
      = 4 * ((∑ c, leverageOf (D.atom c)) - 2 * (m : ℝ))
        - 2 * ((m : ℝ) - 1) * ((∑ c, leverageOf (D.atom c)) - (m : ℝ)) := by
  have hsplit : ∀ a b : Fin m, pairFiringValue D a b
      = 2 * (D.weight a * pairGapMinor (D.atom a) (D.atom b))
        + 2 * (D.weight b * pairGapMinor (D.atom a) (D.atom b))
        - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        - (leverageOf (D.atom b) - 1) * (1 - D.weight a) := by
    intro a b; rw [pairFiringValue]; ring
  have hlin : ∑ a, ∑ b, pairFiringValue D a b
      = 2 * (∑ a, ∑ b, D.weight a * pairGapMinor (D.atom a) (D.atom b))
        + 2 * (∑ a, ∑ b, D.weight b * pairGapMinor (D.atom a) (D.atom b))
        - (∑ a, ∑ b, (leverageOf (D.atom a) - 1) * (1 - D.weight b))
        - ∑ a, ∑ b, (leverageOf (D.atom b) - 1) * (1 - D.weight a) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => hsplit a b
  rw [hlin, sum_sum_weight_left_mul_pairGapMinor,
    sum_sum_weight_right_mul_pairGapMinor, sum_sum_leverageSub_mul_coWeight,
    sum_sum_coWeight_mul_leverageSub]
  ring

/-- The diagonal of the firing value, in closed form.  A repeated atom makes the
pair minor `1 - 2 l_a` (`Gtz.pairGapMinor_self`). -/
theorem sum_diag_pairFiringValue (D : WeightedDesign m 3) :
    ∑ a, pairFiringValue D a a
      = 2 * (m : ℝ) - 16 - 2 * ∑ c, leverageOf (D.atom c) := by
  have hterm : ∀ a : Fin m, pairFiringValue D a a
      = 2 * D.weight a - 6 * (D.weight a * leverageOf (D.atom a))
        - 2 * leverageOf (D.atom a) + 2 := by
    intro a
    rw [pairFiringValue, pairGapMinor_self]
    ring
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hterm a]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, D.weight_sum_one,
    sum_weighted_leverage D, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

/-- **THE FIRING BUDGET.**  The total of the firing value over the ordered pairs
of DISTINCT atoms is a function of the leverage total and the size alone. -/
theorem sum_offDiag_pairFiringValue (D : WeightedDesign m 3) :
    ∑ pair ∈ (Finset.univ : Finset (Fin m)).offDiag, pairFiringValue D pair.1 pair.2
      = (8 - 2 * (m : ℝ)) * (∑ c, leverageOf (D.atom c))
        + 2 * (m : ℝ) ^ 2 - 12 * (m : ℝ) + 16 := by
  classical
  rw [sum_offDiag_eq_sum_sub_diagonal (fun a b => pairFiringValue D a b),
    sum_sum_pairFiringValue D, sum_diag_pairFiringValue D]
  ring

/-! ## 4. The no-go at `(6,3)` -/

/-- **THE `(6,3)` FIRING BUDGET.**  Sixteen less four times the leverage total. -/
theorem sum_offDiag_pairFiringValue_sixThree (D : WeightedDesign 6 3) :
    ∑ pair ∈ (Finset.univ : Finset (Fin 6)).offDiag, pairFiringValue D pair.1 pair.2
      = 16 - 4 * ∑ c, leverageOf (D.atom c) := by
  have hbudget := sum_offDiag_pairFiringValue D
  norm_num at hbudget
  linarith [hbudget]

/-- **THE PRODUCER IS EMPTY AT EVERY `(6,3)` DESIGN.**  The leverage floor
`Gtz.sixThree_nine_le_sum_leverage` puts the total at `-20` or less, so the thirty
ordered pairs share a DEBT of twenty.  No selection rule can find a firing pair by
an averaging argument, at the residual or anywhere else in the open cell. -/
theorem sum_offDiag_pairFiringValue_le (D : WeightedDesign 6 3) :
    ∑ pair ∈ (Finset.univ : Finset (Fin 6)).offDiag, pairFiringValue D pair.1 pair.2
      ≤ -20 := by
  have htotal := sum_offDiag_pairFiringValue_sixThree D
  have hfloor := sixThree_nine_le_sum_leverage D
  linarith

/-- **SOME PAIR OF EVERY `(6,3)` DESIGN IS SILENT BY AT LEAST `2/3`.**  The
averaging reading of the budget: thirty ordered pairs cannot all be above the
mean of a total that is at most `-20`. -/
theorem exists_pairFiringValue_le (D : WeightedDesign 6 3) :
    ∃ a b : Fin 6, a ≠ b ∧ pairFiringValue D a b ≤ -(2 / 3) := by
  classical
  by_contra hcontra
  push_neg at hcontra
  have hcard : ((Finset.univ : Finset (Fin 6)).offDiag).card = 30 := by decide
  have hbound : ∑ _pair ∈ (Finset.univ : Finset (Fin 6)).offDiag, (-(2 / 3) : ℝ)
      < ∑ pair ∈ (Finset.univ : Finset (Fin 6)).offDiag, pairFiringValue D pair.1 pair.2 := by
    refine Finset.sum_lt_sum_of_nonempty ?_ fun pair hpair => ?_
    · exact ⟨(0, 1), Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, by decide⟩⟩
    · exact hcontra pair.1 pair.2 (Finset.mem_offDiag.mp hpair).2.2
  rw [Finset.sum_const, hcard] at hbound
  have hle := sum_offDiag_pairFiringValue_le D
  norm_num at hbound
  linarith

/-! ## 5. The window the producer can fire in -/

/-- **THE FIRING WINDOW, WITH NO ANGLE IN IT.**  The pair minor never exceeds the
product of the two leverage excesses, so a positive firing value forces a
comparison between the weights and the excesses alone.  Divided through by
`(l_a - 1)(l_b - 1)` this reads `(1-t_a)/(l_a-1) + (1-t_b)/(l_b-1) < 2(t_a+t_b)`. -/
theorem window_of_pairFiringValue_pos (D : WeightedDesign m 3) {a b : Fin m}
    (hpos : 0 < pairFiringValue D a b) :
    (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        + (leverageOf (D.atom b) - 1) * (1 - D.weight a)
      < 2 * (D.weight a + D.weight b)
        * ((leverageOf (D.atom a) - 1) * (leverageOf (D.atom b) - 1)) := by
  have hweights : 0 < D.weight a + D.weight b := add_pos (D.weight_pos a) (D.weight_pos b)
  have hcap : pairGapMinor (D.atom a) (D.atom b)
      ≤ (leverageOf (D.atom a) - 1) * (leverageOf (D.atom b) - 1) := by
    rw [pairGapMinor]
    nlinarith [sq_nonneg (D.atom a ⬝ᵥ D.atom b)]
  rw [pairFiringValue] at hpos
  nlinarith [hpos, hcap, hweights]

/-- A per-atom half of the window.  If BOTH atoms satisfy `2 s_c - t_c > 1` the
window holds, so an atom failing it can only fire against a partner that
overcompensates. -/
theorem window_of_strong_pair (D : WeightedDesign m 3) {a b : Fin m}
    (ha : 1 < leverageOf (D.atom a)) (hb : 1 < leverageOf (D.atom b))
    (hstrongA : 1 < 2 * (D.weight a * leverageOf (D.atom a)) - D.weight a)
    (hstrongB : 1 < 2 * (D.weight b * leverageOf (D.atom b)) - D.weight b) :
    (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        + (leverageOf (D.atom b) - 1) * (1 - D.weight a)
      < 2 * (D.weight a + D.weight b)
        * ((leverageOf (D.atom a) - 1) * (leverageOf (D.atom b) - 1)) := by
  have hexA : 0 < leverageOf (D.atom a) - 1 := by linarith
  have hexB : 0 < leverageOf (D.atom b) - 1 := by linarith
  have hA : (1 - D.weight a) < 2 * D.weight a * (leverageOf (D.atom a) - 1) := by nlinarith
  have hB : (1 - D.weight b) < 2 * D.weight b * (leverageOf (D.atom b) - 1) := by nlinarith
  nlinarith [hA, hB, hexA, hexB]

/-- **THE PRODUCER IS SILENT AT THE UNIFORM FRAME.**  At `t = 1/6` and `l = 3` the
window fails at every pair, so the firing value is nonpositive there -- although
that design has a strict dominator and `GtzWeighted` is easy on it.  So the
producer is not merely weak at the residual: it decides nothing on its own. -/
theorem pairFiringValue_nonpos_of_uniformFrame (D : WeightedDesign 6 3)
    (hweight : ∀ c, D.weight c = 1 / 6) (hlev : ∀ c, leverageOf (D.atom c) = 3)
    (a b : Fin 6) : pairFiringValue D a b ≤ 0 := by
  have hcap : pairGapMinor (D.atom a) (D.atom b)
      ≤ (leverageOf (D.atom a) - 1) * (leverageOf (D.atom b) - 1) := by
    rw [pairGapMinor]
    nlinarith [sq_nonneg (D.atom a ⬝ᵥ D.atom b)]
  rw [hlev a, hlev b] at hcap
  rw [pairFiringValue, hweight a, hweight b, hlev a, hlev b]
  nlinarith [hcap]

/-! ## 6. How many atoms can meet the per-atom half of the window -/

/-- **AT MOST FOUR ATOMS OF AN ALL-HEAVY `(6,3)` DESIGN ARE STRONG.**  The shares
total three and the weights total one, so `sum_c (2 s_c - t_c) = 5`; a strong atom
spends more than one of that, and an all-heavy atom that is NOT strong still
spends more than its own weight.  Five strong atoms would spend more than five.

The count is attained: the duplicate split of the `(5,3)` diamond has weights
`(1/10, 1/10, 1/5, 1/5, 1/5, 1/5)` and leverages `(2, 2, 13/4, 13/4, 13/4, 13/4)`,
whose four rim atoms give `2 s - t = 11/10 > 1` and whose two split halves give
`3/10 < 1`.  That witness is MEASURED, not proved here. -/
theorem card_strongAtoms_le_four (D : WeightedDesign 6 3) (hheavy : AllHeavy D) :
    ((Finset.univ : Finset (Fin 6)).filter fun c =>
        1 < 2 * (D.weight c * leverageOf (D.atom c)) - D.weight c).card ≤ 4 := by
  classical
  set strong : Finset (Fin 6) :=
    (Finset.univ : Finset (Fin 6)).filter fun c =>
      1 < 2 * (D.weight c * leverageOf (D.atom c)) - D.weight c with hstrong
  set spend : Fin 6 → ℝ :=
    fun c => 2 * (D.weight c * leverageOf (D.atom c)) - D.weight c with hspend
  have htotal : ∑ c, spend c = 5 := by
    rw [hspend]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_weighted_leverage D, D.weight_sum_one]
    norm_num
  have hpos : ∀ c : Fin 6, 0 < spend c := by
    intro c
    have hw := D.weight_pos c
    have hl := hheavy c
    have : D.weight c < D.weight c * leverageOf (D.atom c) := by nlinarith
    rw [hspend]; nlinarith
  have hsplit : ∑ c ∈ strong, spend c + ∑ c ∈ strongᶜ, spend c = 5 := by
    rw [Finset.sum_add_sum_compl, htotal]
  have hstrongLow : (strong.card : ℝ) ≤ ∑ c ∈ strong, spend c := by
    have hmem : ∀ c ∈ strong, (1 : ℝ) ≤ spend c := by
      intro c hc
      have := (Finset.mem_filter.mp (hstrong ▸ hc)).2
      rw [hspend]; linarith
    have := Finset.card_nsmul_le_sum strong spend 1 hmem
    simpa using this
  have hcomplNonneg : 0 ≤ ∑ c ∈ strongᶜ, spend c :=
    Finset.sum_nonneg fun c _ => (hpos c).le
  have hcardLe5R : (strong.card : ℝ) ≤ 5 := by linarith
  have hcardLe5 : strong.card ≤ 5 := by exact_mod_cast hcardLe5R
  by_contra hcontra
  push_neg at hcontra
  have h5 : strong.card = 5 := le_antisymm hcardLe5 hcontra
  have hcomplCard : strongᶜ.card = 1 := by
    have hsum := Finset.card_add_card_compl strong
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    omega
  obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.mp hcomplCard
  have hcomplPos : 0 < ∑ c ∈ strongᶜ, spend c := by
    rw [hc₀, Finset.sum_singleton]; exact hpos c₀
  have hfive : (5 : ℝ) ≤ ∑ c ∈ strong, spend c := by
    rw [h5] at hstrongLow; exact_mod_cast hstrongLow
  linarith

end Gtz
