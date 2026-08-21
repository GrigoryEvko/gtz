/-
# The star of a pair: a second size law, in the pair alphabet

`Gtz.sum_sixSet_gapDet_eq` totals the gap determinants of ALL triples of a design
and spends the size in the coefficients of the whole gap's invariants.  This
module totals a different family — the STAR of a pair, meaning every triple that
contains one fixed pair — and finds a second, independent size law, written in
leverages, pairings and wedges instead of in matrix invariants.

## The law

Fix a pair `{a,b}` of an `m`-atom design.  Exactly `m − 2` triples contain it.
The triple ledger `Gtz.tripleGapDet_eq_bracketSq_sub_wedgeSum` applied to each and
summed gives the LEDGER FORM (`Gtz.pairStar_gapDet_total_six`):

  `Σ_{c ∉ {a,b}} det(gap_abc)`
    `= Σ_c [a b c]² + (m−2)(ℓ_a + ℓ_b) + Σ_c ℓ_c`
      `− (m−2)·w_ab − Σ_c (w_ac + w_bc) − (m−2)` .

The sums on the right still run over the star.  Extending each to the WHOLE
design costs nothing, because the degenerate slots vanish — `[a b a] = [a b b] =
0` and `w_aa = 0` — and it collapses two of them, since the design total of a
pair's wedges is `ℓ_a·Σℓ − Σ⟨a,g⟩²`.  What is left is the CLOSED FORM
(`Gtz.pairStar_gapDet_closed_six`), where every sum runs over all `m` atoms:

  **`Σ_{c ∉ {a,b}} det(gap_abc)`**
    **`= Σ_i [a b g_i]² + (m−3)(ℓ_a + ℓ_b) + Σ_i ℓ_i − (m−4)·w_ab`**
      **`− (ℓ_a + ℓ_b)·Σ_i ℓ_i + Σ_i ⟨a,g_i⟩² + Σ_i ⟨b,g_i⟩²  − (m−2)`** .

**The size appears in THREE separate coefficients — `m−3`, `m−4` and `m−2`.**  At
five atoms they read `2, 1, 3` and at six they read `3, 2, 4`, so the law cannot
even be stated at both sizes without changing, which is the campaign's own test
for a law that consumes the size rather than holding across it.  Both sizes are
landed side by side (`Gtz.pairStar_gapDet_closed_five`) so the change is visible
in the statements themselves.

[MEASURED: the closed form reproduces the four determinants at `m = 4, 5, 6, 7,
8` to `1.7e-13` or better, on random vector families with no design condition at
all — `scratchpad/f42/starsize.jl` — and at all fifteen pairs of a corner to
`2.1e-12` (`pairstar.jl`).]

## The producers, and what they are worth

A total that is positive forces one of its summands positive.  So each size law
is a REFUSAL PRODUCER with no tie hypothesis: a positive total names a triple of
positive gap determinant, and a triple that is also live then dominates strictly
(`Gtz.posDef_subsetSum_iff_live_and_gapDet`).  Three are landed here:

* `Gtz.exists_posGapDet_of_fourSet_pos` — from the four-set law
* `Gtz.exists_posGapDet_of_pairStar_pos` — from the pair-star law
* `Gtz.exists_posDef_of_pairStar_pos_of_live` — the same, delivered as strict
  domination

[MEASURED COVERAGE at corank-two corners, and this is a PARTIAL kill, not a
closure.  Alone, the outside-pair star fires at 95.4 percent of corners
(12013 of 12594), the four-sets `{e} ∪ Cᶜ` at 85 percent, and the six-set law at
12 percent.  Their union over all fifteen four-sets, all fifteen pair stars and
the six-set law fires at 99.83 percent — but 17 of 10110 corners escape all
thirty-one, and adversarial descent drives the best producer to `−7.99` and
`−5.43` on two independent seeds.  **So this family does not close the horn.**
What is true at 100 percent, at every corner where a producer fires, is that the
triple it names is LIVE — so the producer always converts into an actual strict
dominator.  `scratchpad/f42/union.jl`, `fourset.jl`, `pairstar.jl`.]
-/
import Gtz.Wave.CornerSizeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

/-! ## 0. The degenerate slots -/

/-- A bracket with a repeated slot vanishes. -/
theorem tripleBracket_repeat_outer (a b : Fin 3 → ℝ) : tripleBracket a b a = 0 := by
  rw [tripleBracket, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem tripleBracket_repeat_right (a b : Fin 3 → ℝ) : tripleBracket a b b = 0 := by
  rw [tripleBracket, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- A pair's wedge with itself vanishes. -/
theorem pairWedge_self (a : Fin 3 → ℝ) : pairWedge a a = 0 := by
  rw [pairWedge, ← leverageOf_eq_dotProduct]; ring

/-! ## 1. The pair-star law at size six -/

/-- **THE PAIR-STAR LAW, LEDGER FORM, SIZE SIX.**  The four triples containing a
fixed pair total their squared brackets, plus `m − 2` copies of the pair's
leverages, plus the other leverages, less `m − 2` copies of the pair wedge, less
the mixed wedges, less `m − 2`.  Four applications of the triple ledger. -/
theorem pairStar_gapDet_total_six (a b c d e f : Fin 3 → ℝ) :
    tripleGapDet a b c + tripleGapDet a b d + tripleGapDet a b e
        + tripleGapDet a b f
      = (tripleBracket a b c ^ 2 + tripleBracket a b d ^ 2
            + tripleBracket a b e ^ 2 + tripleBracket a b f ^ 2)
        + 4 * (leverageOf a + leverageOf b)
        + (leverageOf c + leverageOf d + leverageOf e + leverageOf f)
        - 4 * pairWedge a b
        - (pairWedge a c + pairWedge a d + pairWedge a e + pairWedge a f)
        - (pairWedge b c + pairWedge b d + pairWedge b e + pairWedge b f)
        - 4 := by
  have hc := tripleGapDet_eq_bracketSq_sub_wedgeSum a b c
  have hd := tripleGapDet_eq_bracketSq_sub_wedgeSum a b d
  have he := tripleGapDet_eq_bracketSq_sub_wedgeSum a b e
  have hf := tripleGapDet_eq_bracketSq_sub_wedgeSum a b f
  linarith [hc, hd, he, hf]

/-- **THE PAIR-STAR LAW, CLOSED FORM, SIZE SIX.**  Extending every sum to the
whole design costs nothing — the degenerate slots vanish — and collapses the
mixed wedges into design totals.  The size now sits in THREE coefficients:
`m−3 = 3` on the pair's leverages, `m−4 = 2` on the pair wedge, and `m−2 = 4` in
the constant. -/
theorem pairStar_gapDet_closed_six (a b c d e f : Fin 3 → ℝ) :
    tripleGapDet a b c + tripleGapDet a b d + tripleGapDet a b e
        + tripleGapDet a b f
      = (tripleBracket a b a ^ 2 + tripleBracket a b b ^ 2
            + tripleBracket a b c ^ 2 + tripleBracket a b d ^ 2
            + tripleBracket a b e ^ 2 + tripleBracket a b f ^ 2)
        + 3 * (leverageOf a + leverageOf b)
        + (leverageOf a + leverageOf b + leverageOf c + leverageOf d
            + leverageOf e + leverageOf f)
        - 2 * pairWedge a b
        - (leverageOf a + leverageOf b)
          * (leverageOf a + leverageOf b + leverageOf c + leverageOf d
              + leverageOf e + leverageOf f)
        + ((a ⬝ᵥ a) ^ 2 + (a ⬝ᵥ b) ^ 2 + (a ⬝ᵥ c) ^ 2 + (a ⬝ᵥ d) ^ 2
            + (a ⬝ᵥ e) ^ 2 + (a ⬝ᵥ f) ^ 2)
        + ((b ⬝ᵥ a) ^ 2 + (b ⬝ᵥ b) ^ 2 + (b ⬝ᵥ c) ^ 2 + (b ⬝ᵥ d) ^ 2
            + (b ⬝ᵥ e) ^ 2 + (b ⬝ᵥ f) ^ 2)
        - 4 := by
  have hled := pairStar_gapDet_total_six a b c d e f
  rw [tripleBracket_repeat_outer a b, tripleBracket_repeat_right a b]
  simp only [pairWedge, ← leverageOf_eq_dotProduct] at hled ⊢
  have hab : b ⬝ᵥ a = a ⬝ᵥ b := dotProduct_comm b a
  rw [hab]
  linarith [hled]

/-! ## 2. The same law at size five, so the size is visible -/

/-- **THE PAIR-STAR LAW, CLOSED FORM, SIZE FIVE.**  The three coefficients are
now `m−3 = 2`, `m−4 = 1` and `m−2 = 3`.  Set beside
`Gtz.pairStar_gapDet_closed_six` this is the campaign's size test passed in the
statement itself: the two laws are different polynomials, so a design cannot
satisfy one by satisfying the other. -/
theorem pairStar_gapDet_closed_five (a b c d e : Fin 3 → ℝ) :
    tripleGapDet a b c + tripleGapDet a b d + tripleGapDet a b e
      = (tripleBracket a b a ^ 2 + tripleBracket a b b ^ 2
            + tripleBracket a b c ^ 2 + tripleBracket a b d ^ 2
            + tripleBracket a b e ^ 2)
        + 2 * (leverageOf a + leverageOf b)
        + (leverageOf a + leverageOf b + leverageOf c + leverageOf d
            + leverageOf e)
        - 1 * pairWedge a b
        - (leverageOf a + leverageOf b)
          * (leverageOf a + leverageOf b + leverageOf c + leverageOf d
              + leverageOf e)
        + ((a ⬝ᵥ a) ^ 2 + (a ⬝ᵥ b) ^ 2 + (a ⬝ᵥ c) ^ 2 + (a ⬝ᵥ d) ^ 2
            + (a ⬝ᵥ e) ^ 2)
        + ((b ⬝ᵥ a) ^ 2 + (b ⬝ᵥ b) ^ 2 + (b ⬝ᵥ c) ^ 2 + (b ⬝ᵥ d) ^ 2
            + (b ⬝ᵥ e) ^ 2)
        - 3 := by
  have hc := tripleGapDet_eq_bracketSq_sub_wedgeSum a b c
  have hd := tripleGapDet_eq_bracketSq_sub_wedgeSum a b d
  have he := tripleGapDet_eq_bracketSq_sub_wedgeSum a b e
  rw [tripleBracket_repeat_outer a b, tripleBracket_repeat_right a b]
  simp only [pairWedge, ← leverageOf_eq_dotProduct] at hc hd he ⊢
  have hab : b ⬝ᵥ a = a ⬝ᵥ b := dotProduct_comm b a
  rw [hab]
  linarith [hc, hd, he]

/-! ## 3. The producers -/

/-- **THE FOUR-SET PRODUCER.**  A positive four-set invariant names a triple of
positive gap determinant.  No tie hypothesis, no corner, no design. -/
theorem exists_posGapDet_of_fourSet_pos (a b c d : Fin 3 → ℝ)
    (hpos : 0 < (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).det
      - gapSecondInvariant
          (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1)) :
    0 < tripleGapDet b c d ∨ 0 < tripleGapDet a c d
      ∨ 0 < tripleGapDet a b d ∨ 0 < tripleGapDet a b c := by
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hcon
  have hlaw := sum_fourSet_gapDet_eq_det_sub_secondInvariant a b c d
  linarith [hlaw, h₁, h₂, h₃, h₄, hpos]

/-- **THE PAIR-STAR PRODUCER.**  A positive star total names one of the four
triples through the pair.  This is the sharpest of the three producers at a
corank-two corner: on the three outside pairs alone it fires at 95.4 percent. -/
theorem exists_posGapDet_of_pairStar_pos (a b c d e f : Fin 3 → ℝ)
    (hpos : 0 < tripleGapDet a b c + tripleGapDet a b d + tripleGapDet a b e
      + tripleGapDet a b f) :
    0 < tripleGapDet a b c ∨ 0 < tripleGapDet a b d
      ∨ 0 < tripleGapDet a b e ∨ 0 < tripleGapDet a b f := by
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hcon
  linarith [hpos, h₁, h₂, h₃, h₄]

/-- **THE SIX-SET PRODUCER.**  A positive whole-design total names a triple of
positive gap determinant among the twenty. -/
theorem exists_posGapDet_of_sixSet_pos (a b c d e f : Fin 3 → ℝ)
    (hpos : 0 < (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d
          + atomMatrix e + atomMatrix f - 1).det
        - 3 * gapSecondInvariant (atomMatrix a + atomMatrix b + atomMatrix c
            + atomMatrix d + atomMatrix e + atomMatrix f - 1)
        + 3 * Matrix.trace (atomMatrix a + atomMatrix b + atomMatrix c
            + atomMatrix d + atomMatrix e + atomMatrix f - 1)
        - 1) :
    ¬ (tripleGapDet a b c ≤ 0 ∧ tripleGapDet a b d ≤ 0 ∧ tripleGapDet a b e ≤ 0
        ∧ tripleGapDet a b f ≤ 0 ∧ tripleGapDet a c d ≤ 0
        ∧ tripleGapDet a c e ≤ 0 ∧ tripleGapDet a c f ≤ 0
        ∧ tripleGapDet a d e ≤ 0 ∧ tripleGapDet a d f ≤ 0
        ∧ tripleGapDet a e f ≤ 0 ∧ tripleGapDet b c d ≤ 0
        ∧ tripleGapDet b c e ≤ 0 ∧ tripleGapDet b c f ≤ 0
        ∧ tripleGapDet b d e ≤ 0 ∧ tripleGapDet b d f ≤ 0
        ∧ tripleGapDet b e f ≤ 0 ∧ tripleGapDet c d e ≤ 0
        ∧ tripleGapDet c d f ≤ 0 ∧ tripleGapDet c e f ≤ 0
        ∧ tripleGapDet d e f ≤ 0) := by
  rintro ⟨t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀, t₁₁, t₁₂, t₁₃, t₁₄, t₁₅,
    t₁₆, t₁₇, t₁₈, t₁₉, t₂₀⟩
  have hlaw := sum_sixSet_gapDet_eq a b c d e f
  linarith [hlaw, hpos, t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀, t₁₁, t₁₂, t₁₃,
    t₁₄, t₁₅, t₁₆, t₁₇, t₁₈, t₁₉, t₂₀]

/-! ## 4. From a producer to a strict dominator -/

/-- **THE PRODUCER DELIVERS DOMINATION.**  If the star of a pair is positive and
every triple through that pair is live, then one of them dominates strictly.  At
a tie no triple dominates, so a tie forces the star of every all-live pair to be
nonpositive — a pair-local, size-carrying necessary condition.

[MEASURED: at every corank-two corner where a producer fires, the triple it names
IS live, at 100 percent — so the liveness hypothesis is not the obstruction.] -/
theorem exists_posDef_of_pairStar_pos_of_live {m : ℕ} (D : WeightedDesign m 3)
    (a b c d e f : Fin m) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d) (hbd : b ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (haf : a ≠ f) (hbf : b ≠ f)
    (lc : LiveTriple D a b c) (ld : LiveTriple D a b d)
    (le : LiveTriple D a b e) (lf : LiveTriple D a b f)
    (hpos : 0 < tripleGapDet (D.atom a) (D.atom b) (D.atom c)
      + tripleGapDet (D.atom a) (D.atom b) (D.atom d)
      + tripleGapDet (D.atom a) (D.atom b) (D.atom e)
      + tripleGapDet (D.atom a) (D.atom b) (D.atom f)) :
    (subsetSum D ({a, b, c} : Finset (Fin m)) - 1).PosDef
      ∨ (subsetSum D ({a, b, d} : Finset (Fin m)) - 1).PosDef
      ∨ (subsetSum D ({a, b, e} : Finset (Fin m)) - 1).PosDef
      ∨ (subsetSum D ({a, b, f} : Finset (Fin m)) - 1).PosDef := by
  rcases exists_posGapDet_of_pairStar_pos (D.atom a) (D.atom b) (D.atom c)
    (D.atom d) (D.atom e) (D.atom f) hpos with h | h | h | h
  · exact Or.inl ((posDef_subsetSum_iff_live_and_gapDet D a b c hab
      (by simpa using hac) hbc).mpr ⟨lc, h⟩)
  · exact Or.inr (Or.inl ((posDef_subsetSum_iff_live_and_gapDet D a b d hab
      (by simpa using had) hbd).mpr ⟨ld, h⟩))
  · exact Or.inr (Or.inr (Or.inl ((posDef_subsetSum_iff_live_and_gapDet D a b e
      hab (by simpa using hae) hbe).mpr ⟨le, h⟩)))
  · exact Or.inr (Or.inr (Or.inr ((posDef_subsetSum_iff_live_and_gapDet D a b f
      hab (by simpa using haf) hbf).mpr ⟨lf, h⟩)))

end Gtz
