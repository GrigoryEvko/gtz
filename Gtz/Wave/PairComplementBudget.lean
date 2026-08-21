/-
# The pair budget: the weighted gap determinants outside a pair are pair data

The corank-two arm's remaining existence fact is that at a corner some outside
pair is repaid.  Every instrument for it has been a WEIGHTED SUM of the three
one-inside gap determinants, and the landed `Gtz.weighted_tripleGapDet_sum_compl`
says what that sum is: the pair minor against the subset's weighted excess, less
the pair trace, less the axis moment of the COMPLEMENTARY subset.  The last term
is the one nobody could bound, and the lane's own note records that dropping it
loses the whole statement.

This module removes it, by summing over the RIGHT subset.

## The identity

Take the subset to be the complement of the pair ITSELF, and let the two probes
be the pair's own atoms.  Then the leftover subset is the two-element set
`{a, b}`, its axis moment is a closed form in the pair's leverages and pairing
alone, and the design cancels completely:

  **`Gtz.weighted_tripleGapDet_pairCompl`:**
  `∑_{c ∉ {a,b}} t_c · tripleGapDet g_a g_b g_c
      = 2·q_ab·(t_a + t_b) − (ℓ_a − 1)(1 − t_b) − (ℓ_b − 1)(1 − t_a)` .

No hypothesis beyond the design axioms and `a ≠ b`, at every size.  The left
side runs over every atom other than the two, so it carries the whole design;
the right side names only the pair.  Two facts do it: the weighted excess of the
complement is `2 − t_a(ℓ_a−1) − t_b(ℓ_b−1)` by the landed total
(`Gtz.total_weighted_excess`), and the axis moment at the pair's own two atoms
evaluates by `ring`, because a pair reads itself at `(ℓ_a, p)` and `(p, ℓ_b)`.

## What it produces

A positive right side names an atom outside the pair whose triple has positive
gap determinant (`Gtz.exists_tripleGapDet_pos_of_pairBudget_pos`), and on an
admissible pair of heavy atoms Sylvester turns that into a STRICT dominator
(`Gtz.exists_posDef_of_pairBudget_pos`).  So

  **`Gtz.not_isTie_of_pairBudget_pos`:** a design carrying an admissible pair of
  heavy atoms with positive budget is not a tie.

The contrapositive is a necessary condition on ties in PAIR DATA ONLY -- no
triple, no determinant, no selection:

  **`Gtz.pairComplBudget_nonpos_of_isTie`:** at a tie EVERY pair obeys
  `2·q_ab·(t_a+t_b) ≤ (ℓ_a−1)(1−t_b) + (ℓ_b−1)(1−t_a)` .

An inadmissible pair obeys it for free, because at a tie every atom is heavy and
the right side is then nonnegative while the left is not positive; an admissible
heavy pair obeys it because every determinant in the sum is nonpositive.

## The three outside pairs of a corner couple

Summing the identity over the three pairs of a fixed triple `{a,b,f}` makes the
third-atom terms collapse: pair `{a,b}` contributes `t_f·det(a,b,f)`, pair
`{a,f}` contributes `t_b·det(a,b,f)`, and pair `{b,f}` contributes
`t_a·det(a,b,f)`, so the triple's own determinant appears exactly once, weighted
by the triple's total weight (`Gtz.tripleBudget_sum`).  At a corner with outside
triple `{a,b,f}` the left side is then the nine one-inside slots plus the
complement, in one equation -- which is the arm's disjunction "the complement
dominates, or some one-inside triple does" written as a single scalar.

[MEASURED before proving.  The identity: max relative residual `2.0e-12` over
35200 pairs of designs at sizes 4,5,6,7,9, and `3.1e-15` absolute at the `(5,3)`
diamond.  The joint form: `6.9e-12` over 4000 corners.  Fire rate of the
producer at corners: some outside admissible pair has positive budget at
`98.45%`, some pair at all at `99.63%`; the summed form fires at only `85.7%`,
which is the arm's own rule that a selection beats an average.

FIELD-BLIND, and this is a limitation, not an oversight.  The identity uses only
Parseval and the Sylvester split, so it holds verbatim over `ℂ` in the Hermitian
reading -- checked at `7.7e-15` on the complex corank-two corner tie recorded in
`scratchpad/NOTES-f68-etwo.txt`, where the producer correctly does NOT fire (best
budget `−1.145`).  A complex corner tie exists, so no field-blind instrument can
be total, and the residual of this one is exactly where realness must act.]
-/
import Gtz.Wave.WeightedRepaymentTrace
import Gtz.Wave.CornerAdmissibleGateway
import Gtz.Design.TripleGramSylvester

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The pair reads itself -/

/-- **A PAIR'S AXIS FORM AT ITS OWN FIRST ATOM.**  The readings are the atom's
leverage and the pairing, and the form collapses to the pair minor against the
atom's excess.  One `ring`. -/
theorem pairAxisForm_self_left (a b : Fin 3 → ℝ) :
    pairAxisForm a b (a ⬝ᵥ a) (b ⬝ᵥ a)
      = -(pairGapMinor a b * (leverageOf a - 1) + 2 * pairGapMinor a b
          + (leverageOf b - 1)) := by
  have hsa : a ⬝ᵥ a = leverageOf a := by
    simp only [leverageOf, dotProduct, Fin.sum_univ_three]; ring
  rw [pairAxisForm, pairGapMinor, hsa, dotProduct_comm b a]
  ring

/-- **A PAIR'S AXIS FORM AT ITS OWN SECOND ATOM.**  The same statement with the
two atoms interchanged. -/
theorem pairAxisForm_self_right (a b : Fin 3 → ℝ) :
    pairAxisForm a b (a ⬝ᵥ b) (b ⬝ᵥ b)
      = -(pairGapMinor a b * (leverageOf b - 1) + 2 * pairGapMinor a b
          + (leverageOf a - 1)) := by
  have hsb : b ⬝ᵥ b = leverageOf b := by
    simp only [leverageOf, dotProduct, Fin.sum_univ_three]; ring
  rw [pairAxisForm, pairGapMinor, hsb]
  ring

/-- **THE AXIS MOMENT AT THE PAIR ITSELF.**  Over the two-element set carrying
the pair's own atoms the moment is a closed form in the pair's leverages,
pairing and weights.  This is the term the landed complement identity leaves
behind, and it is the whole reason the design cancels. -/
theorem axisMoment_pair (D : WeightedDesign m 3) {a b : Fin m} (hab : a ≠ b) :
    axisMoment D (D.atom a) (D.atom b) ({a, b} : Finset (Fin m))
      = -(D.weight a * (pairGapMinor (D.atom a) (D.atom b)
              * (leverageOf (D.atom a) - 1) + 2 * pairGapMinor (D.atom a) (D.atom b)
            + (leverageOf (D.atom b) - 1))
          + D.weight b * (pairGapMinor (D.atom a) (D.atom b)
              * (leverageOf (D.atom b) - 1) + 2 * pairGapMinor (D.atom a) (D.atom b)
            + (leverageOf (D.atom a) - 1))) := by
  rw [axisMoment, Finset.sum_pair hab, pairAxisForm_self_left,
    pairAxisForm_self_right]
  ring

/-! ## 2. The weighted excess of the complement of a pair -/

/-- The weighted excess of everything outside a pair is two less the pair's own
weighted excess, by the landed total. -/
theorem weightedExcess_pairCompl (D : WeightedDesign m 3) {a b : Fin m}
    (hab : a ≠ b) :
    weightedExcess D ({a, b} : Finset (Fin m))ᶜ
      = 2 - D.weight a * (leverageOf (D.atom a) - 1)
          - D.weight b * (leverageOf (D.atom b) - 1) := by
  classical
  have hsplit : weightedExcess D ({a, b} : Finset (Fin m))
      + weightedExcess D ({a, b} : Finset (Fin m))ᶜ
      = ∑ c, D.weight c * (leverageOf (D.atom c) - 1) := by
    rw [weightedExcess, weightedExcess]
    exact Finset.sum_add_sum_compl _ _
  rw [total_weighted_excess D] at hsplit
  have hpair : weightedExcess D ({a, b} : Finset (Fin m))
      = D.weight a * (leverageOf (D.atom a) - 1)
        + D.weight b * (leverageOf (D.atom b) - 1) := by
    rw [weightedExcess, Finset.sum_pair hab]
  rw [hpair] at hsplit
  linarith

/-! ## 3. The identity -/

/-- **THE PAIR BUDGET.**  The design-weighted total of the gap determinants of
every triple through a pair equals a closed form in the pair's own leverages,
pairing and weights.  No hypothesis beyond `a ≠ b`, at every size.

The left side carries the whole design and the right side names only the pair,
so the design has been spent exactly as in the landed total axis moment -- but
here the leftover subset is the pair itself, which evaluates, rather than the
complement, which does not. -/
theorem weighted_tripleGapDet_pairCompl (D : WeightedDesign m 3) {a b : Fin m}
    (hab : a ≠ b) :
    ∑ c ∈ ({a, b} : Finset (Fin m))ᶜ,
        D.weight c * tripleGapDet (D.atom a) (D.atom b) (D.atom c)
      = 2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
        - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        - (leverageOf (D.atom b) - 1) * (1 - D.weight a) := by
  classical
  have hsum := weighted_tripleGapDet_sum_compl D (D.atom a) (D.atom b)
    (({a, b} : Finset (Fin m))ᶜ)
  rw [compl_compl] at hsum
  rw [hsum, weightedExcess_pairCompl D hab, axisMoment_pair D hab]
  ring

/-! ## 4. The producer -/

/-- **A POSITIVE BUDGET NAMES AN ATOM.**  A sum of terms cannot be positive with
every term nonpositive, so a positive budget produces an atom outside the pair
whose triple has positive gap determinant. -/
theorem exists_tripleGapDet_pos_of_pairBudget_pos (D : WeightedDesign m 3)
    {a b : Fin m} (hab : a ≠ b)
    (hpos : 0 < 2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
        - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        - (leverageOf (D.atom b) - 1) * (1 - D.weight a)) :
    ∃ c : Fin m, c ≠ a ∧ c ≠ b
      ∧ 0 < tripleGapDet (D.atom a) (D.atom b) (D.atom c) := by
  classical
  rw [← weighted_tripleGapDet_pairCompl D hab] at hpos
  by_contra hcon
  push_neg at hcon
  have hnonpos : ∑ c ∈ ({a, b} : Finset (Fin m))ᶜ,
      D.weight c * tripleGapDet (D.atom a) (D.atom b) (D.atom c) ≤ 0 := by
    refine Finset.sum_nonpos fun c hc => ?_
    have hne : c ≠ a ∧ c ≠ b := by
      have := Finset.mem_compl.mp hc
      constructor <;> intro h <;> exact this (by simp [h])
    have hw := (D.weight_pos c).le
    have hd := hcon c hne.1 hne.2
    nlinarith [hw, hd]
  linarith

/-- **THE STRICT DOMINATOR.**  On an admissible pair of heavy atoms Sylvester
turns the named atom into a strictly dominating triple. -/
theorem exists_posDef_of_pairBudget_pos (D : WeightedDesign m 3)
    {a b : Fin m} (hab : a ≠ b)
    (ha : 1 < leverageOf (D.atom a))
    (hq : 0 < pairGapMinor (D.atom a) (D.atom b))
    (hpos : 0 < 2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
        - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        - (leverageOf (D.atom b) - 1) * (1 - D.weight a)) :
    ∃ c : Fin m, c ≠ a ∧ c ≠ b
      ∧ (tripleGram (D.atom a) (D.atom b) (D.atom c) - 1).PosDef := by
  obtain ⟨c, hca, hcb, hdet⟩ :=
    exists_tripleGapDet_pos_of_pairBudget_pos D hab hpos
  exact ⟨c, hca, hcb,
    (tripleGram_posDef_iff_pairVocabulary _ _ _).mpr ⟨by linarith, hq, hdet⟩⟩

/-- **THE DESIGN IS NOT A TIE.**  A design carrying an admissible pair of heavy
atoms with positive budget has a strictly dominating triple. -/
theorem not_isTie_of_pairBudget_pos (D : WeightedDesign m 3)
    {a b : Fin m} (hab : a ≠ b)
    (ha : 1 < leverageOf (D.atom a))
    (hq : 0 < pairGapMinor (D.atom a) (D.atom b))
    (hpos : 0 < 2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
        - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        - (leverageOf (D.atom b) - 1) * (1 - D.weight a)) :
    ¬ IsTie D := by
  classical
  intro htie
  obtain ⟨c, hca, hcb, hpd⟩ := exists_posDef_of_pairBudget_pos D hab ha hq hpos
  refine htie.2 ({a, b, c} : Finset (Fin m)) ?_ ?_
  · rw [Finset.card_insert_of_notMem (by simp [hab, Ne.symm hca]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hcb]), Finset.card_singleton]
  · exact (subsetSum_posDef_iff_tripleGram D a b c hab (Ne.symm hca)
      (Ne.symm hcb)).mpr hpd

/-! ## 5. The necessary condition on a tie -/

/-- **EVERY PAIR OF A TIE OBEYS THE BUDGET BOUND.**  In pair data only: no
triple, no determinant, no selection.  An admissible heavy pair obeys it because
the producer above would otherwise fire; every other pair obeys it for free,
because at a tie the excesses are nonnegative, so the right side is nonnegative
while a nonpositive minor makes the left side nonpositive. -/
theorem pairComplBudget_nonpos_of_isTie (D : WeightedDesign (m + 1) 3) (hm : 1 ≤ m)
    (hsmaller : GtzWeighted m 3) (htie : IsTie D) {a b : Fin (m + 1)} (hab : a ≠ b) :
    2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
      ≤ (leverageOf (D.atom a) - 1) * (1 - D.weight b)
        + (leverageOf (D.atom b) - 1) * (1 - D.weight a) := by
  have hla : 1 ≤ leverageOf (D.atom a) :=
    leverage_one_le_of_isTie D hm hsmaller htie a
  have hlb : 1 ≤ leverageOf (D.atom b) :=
    leverage_one_le_of_isTie D hm hsmaller htie b
  have hwa : D.weight a < 1 := weight_lt_one D (by omega) a
  have hwb : D.weight b < 1 := weight_lt_one D (by omega) b
  by_contra hcon
  push_neg at hcon
  rcases le_or_gt (pairGapMinor (D.atom a) (D.atom b)) 0 with hq | hq
  · -- a nonpositive minor cannot beat a nonnegative right side
    have hw : 0 < D.weight a + D.weight b :=
      add_pos (D.weight_pos a) (D.weight_pos b)
    have hleft : 2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b) ≤ 0 := by
      nlinarith [hq, hw]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ leverageOf (D.atom a) - 1)
        (by linarith : (0:ℝ) ≤ 1 - D.weight b),
      mul_nonneg (by linarith : (0:ℝ) ≤ leverageOf (D.atom b) - 1)
        (by linarith : (0:ℝ) ≤ 1 - D.weight a)]
  · -- an admissible pair of atoms that are heavy at a tie is heavy STRICTLY,
    -- because a positive minor cannot come from a vanishing excess
    have hstrict : 1 < leverageOf (D.atom a) := by
      rcases eq_or_lt_of_le hla with heq | hlt
      · exfalso
        rw [pairGapMinor, ← heq] at hq
        nlinarith [sq_nonneg (D.atom a ⬝ᵥ D.atom b)]
      · exact hlt
    exact not_isTie_of_pairBudget_pos D hab hstrict hq (by linarith) htie

/-! ## 6. The three pairs of a triple couple -/

/-- **THE TRIPLE BUDGET.**  Summing the pair budget over the three pairs of a
triple makes the triple's own determinant appear exactly once, weighted by the
triple's total weight: each pair contributes the third atom's term.

At a corner, taken at the OUTSIDE triple, the left side is the nine one-inside
gap determinants together with the complement's own, so the arm's disjunction
"the complement dominates, or some one-inside triple does" becomes the sign of
one scalar built from the outside triple alone. -/
theorem tripleBudget_sum (D : WeightedDesign m 3) {a b f : Fin m}
    (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f) :
    (∑ c ∈ ({a, b} : Finset (Fin m))ᶜ,
        D.weight c * tripleGapDet (D.atom a) (D.atom b) (D.atom c))
      + (∑ c ∈ ({a, f} : Finset (Fin m))ᶜ,
        D.weight c * tripleGapDet (D.atom a) (D.atom f) (D.atom c))
      + (∑ c ∈ ({b, f} : Finset (Fin m))ᶜ,
        D.weight c * tripleGapDet (D.atom b) (D.atom f) (D.atom c))
      = (2 * pairGapMinor (D.atom a) (D.atom b) * (D.weight a + D.weight b)
          - (leverageOf (D.atom a) - 1) * (1 - D.weight b)
          - (leverageOf (D.atom b) - 1) * (1 - D.weight a))
        + (2 * pairGapMinor (D.atom a) (D.atom f) * (D.weight a + D.weight f)
          - (leverageOf (D.atom a) - 1) * (1 - D.weight f)
          - (leverageOf (D.atom f) - 1) * (1 - D.weight a))
        + (2 * pairGapMinor (D.atom b) (D.atom f) * (D.weight b + D.weight f)
          - (leverageOf (D.atom b) - 1) * (1 - D.weight f)
          - (leverageOf (D.atom f) - 1) * (1 - D.weight b)) := by
  rw [weighted_tripleGapDet_pairCompl D hab, weighted_tripleGapDet_pairCompl D haf,
    weighted_tripleGapDet_pairCompl D hbf]

end Gtz
