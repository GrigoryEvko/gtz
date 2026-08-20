import Gtz.Wave.TripleGramChart
import Gtz.Wave.BracketContractionTax
import Gtz.Wave.CoherentHornDualFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The chart bracket tax

The chart of a triple carries its determinant, and that determinant is the
squared bracket (`Gtz.tripleGram_det_eq_bracket_sq` is the landed
`Gtz.sq_tripleBracket_eq_gramDet` in chart form).  The landed contraction
tax prices exactly that scalar at a tie.  This module joins the two, so
the tax speaks in the chart's own currency and composes with the corner
laws.

* `Gtz.chartDet_eq_bracket_sq` — `det P = [abc]²` for the landed Gram.
* `Gtz.subsetSum_det_eq_chartDet` — a triple's atom-sum determinant is its
  chart determinant.
* `Gtz.isTie_chartDet_tax` — THE TAX IN CHART CURRENCY: at a tie every
  triple obeys `t_at_bt_c·det P ≤ (some member weight)`.  Measured share
  of the both-light cell on which the strict form already produces a
  dominator: `92.94%` of `200000` chart inhabitants.
* `Gtz.corner_bothLight_outside_chartDet_cap` — the corner instance: at a
  tie the outside triple's chart determinant obeys
  `t₄t₅t₆·det P ≤ tcap`, a cap on the very scalar the weight-gap floor
  multiplies.
* `Gtz.chart_parseval_det_identity` — the determinant of the chart
  Parseval identity: `(det P)²·t₄t₅t₆ = det(P − t_x·ωωᵀ − t_y·ω^yω^yᵀ −
  t_z·ω^zω^zᵀ)`, an exact relation between the chart determinant and the
  inside witnesses.
* `Gtz.posDef_subsetSum_of_obtuse_rowPositive` — THE M-MATRIX PRODUCER IN
  THE CHART: a triple with nonpositive pairwise pairings whose chart gap
  sends a positive vector to a positive vector dominates strictly.  Its
  tie contrapositive refuses every such triple.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The chart determinant is the squared bracket -/

/-- **THE CHART DETERMINANT IS THE SQUARED BRACKET.** -/
theorem chartDet_eq_bracket_sq (a b c : Fin 3 → ℝ) :
    (tripleGram a b c).det = tripleBracket a b c ^ 2 := by
  rw [sq_tripleBracket_eq_gramDet, tripleGram_eq_literal]
  simp only [Matrix.det_fin_three, leverageOf, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **THE ATOM SUM AND THE CHART SHARE THEIR DETERMINANT.** -/
theorem subsetSum_det_eq_chartDet (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (subsetSum D ({x, y, z} : Finset (Fin m))).det
      = (tripleGram (D.atom x) (D.atom y) (D.atom z)).det := by
  rw [chartDet_eq_bracket_sq,
    show subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z)
    from by
      rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
        Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
      abel]
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.add_apply, tripleBracket_eq]
  ring

/-! ## 2. The tax in chart currency -/

/-- **THE CONTRACTION TAX IN CHART CURRENCY.**  At a tie every triple pays
its chart determinant against one of its member weights:

  `t_at_bt_c·det P ≤ t_member` .

Measured: the strict form already produces a dominator on `92.94%` of the
both-light cell, so this single landed law removes most of the cell before
any floor is consulted. -/
theorem isTie_chartDet_tax (D : WeightedDesign m 3) (htie : IsTie D)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ member ∈ ({a, b, c} : Finset (Fin m)),
      D.weight a * D.weight b * D.weight c
          * (tripleGram (D.atom a) (D.atom b) (D.atom c)).det
        ≤ D.weight member := by
  obtain ⟨member, hmem, hle⟩ := isTie_bracket_tax D htie hab hac hbc
  refine ⟨member, hmem, ?_⟩
  rw [chartDet_eq_bracket_sq, show tripleBracket (D.atom a) (D.atom b) (D.atom c)
      = atomBracket D a b c from rfl]
  calc D.weight a * D.weight b * D.weight c * atomBracket D a b c ^ 2
      = D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2)) := by
        ring
    _ ≤ D.weight member := hle

/-- **THE OUTSIDE CAP OF A CORNER TIE.**  At a tie the outside triple's
chart determinant is capped by the largest outside weight over the product
of all three:

  `t₄t₅t₆·det P ≤ tcap` .

The capped scalar is exactly the one the weight-gap floor multiplies, so
the cap and the floor speak of the same quantity. -/
theorem corner_bothLight_outside_chartDet_cap (D : WeightedDesign m 3)
    (htie : IsTie D) {d4 d5 d6 : Fin m}
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    {tcap : ℝ} (hc4 : D.weight d4 ≤ tcap) (hc5 : D.weight d5 ≤ tcap)
    (hc6 : D.weight d6 ≤ tcap) :
    D.weight d4 * D.weight d5 * D.weight d6
        * (tripleGram (D.atom d4) (D.atom d5) (D.atom d6)).det
      ≤ tcap := by
  obtain ⟨member, hmem, hle⟩ := isTie_chartDet_tax D htie h45 h46 h56
  have hcap : D.weight member ≤ tcap := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hc4
    · exact hc5
    · exact hc6
  linarith [hle, hcap]

/-! ## 3. The determinant of the chart Parseval identity -/

/-- **THE DETERMINANT OF THE CHART IDENTITY.**  Taking determinants in the
chart Parseval identity relates the chart determinant to the inside
witnesses exactly:

  `(det P)²·t₄t₅t₆ = det(P − t_x·ωωᵀ − t_y·ω^yω^yᵀ − t_z·ω^zω^zᵀ)` .

The left side is the chart determinant squared against the outside weight
product — the very product the tax caps. -/
theorem chart_parseval_det_identity (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6}) :
    (tripleGram (D.atom d4) (D.atom d5) (D.atom d6)).det ^ 2
        * (D.weight d4 * D.weight d5 * D.weight d6)
      = (tripleGram (D.atom d4) (D.atom d5) (D.atom d6)
          - (D.weight x • atomMatrix
              (tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x))
            + D.weight y • atomMatrix
              (tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom y))
            + D.weight z • atomMatrix
              (tripleWitness (D.atom d4) (D.atom d5) (D.atom d6)
                (D.atom z)))).det := by
  classical
  set P : Matrix (Fin 3) (Fin 3) ℝ :=
    tripleGram (D.atom d4) (D.atom d5) (D.atom d6) with hP
  set T : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6] with hT
  have hid := parseval_tripleGram_identity D hxy hxz hyz h45 h46 h56 hcompl
  rw [← hP, ← hT] at hid
  have hblock : P * T * P
      = P - (D.weight x • atomMatrix
            (tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x))
          + D.weight y • atomMatrix
            (tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom y))
          + D.weight z • atomMatrix
            (tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom z))) :=
    eq_sub_of_add_eq' hid
  have hdet := congrArg Matrix.det hblock
  rw [Matrix.det_mul, Matrix.det_mul, hT, Matrix.det_diagonal,
    Fin.prod_univ_three] at hdet
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hdet
  rw [← hdet]
  ring

/-! ## 4. The M-matrix producer in the chart -/

/-- **THE M-MATRIX PRODUCER IN THE CHART.**  A triple whose three pairwise
pairings are nonpositive and whose chart gap sends some strictly positive
vector to a strictly positive vector DOMINATES STRICTLY.  No eigenvalue and
no diagonal dominance: the landed `Gtz.posDef_three_of_zPattern_of_posVector`
supplies positive definiteness of the chart gap, and the landed Gram
criterion transports it to the atom sum.

Measured: an obtuse triple exists on essentially every both-light chart
inhabitant, and the row-positive test fires on `15.95%` of them at the
four probe vectors tried. -/
theorem posDef_subsetSum_of_obtuse_rowPositive (D : WeightedDesign m 3)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpab : D.atom a ⬝ᵥ D.atom b ≤ 0) (hpac : D.atom a ⬝ᵥ D.atom c ≤ 0)
    (hpbc : D.atom b ⬝ᵥ D.atom c ≤ 0)
    {scale : Fin 3 → ℝ} (hv0 : 0 < scale 0) (hv1 : 0 < scale 1)
    (hv2 : 0 < scale 2)
    (hr0 : 0 < (D.atom a ⬝ᵥ D.atom a - 1) * scale 0
      + (D.atom a ⬝ᵥ D.atom b) * scale 1 + (D.atom a ⬝ᵥ D.atom c) * scale 2)
    (hr1 : 0 < (D.atom a ⬝ᵥ D.atom b) * scale 0
      + (D.atom b ⬝ᵥ D.atom b - 1) * scale 1 + (D.atom b ⬝ᵥ D.atom c) * scale 2)
    (hr2 : 0 < (D.atom a ⬝ᵥ D.atom c) * scale 0
      + (D.atom b ⬝ᵥ D.atom c) * scale 1
      + (D.atom c ⬝ᵥ D.atom c - 1) * scale 2) :
    (subsetSum D ({a, b, c} : Finset (Fin m)) - 1).PosDef := by
  classical
  rw [subsetSum_posDef_iff_tripleGram D a b c hab hac hbc]
  set G : Matrix (Fin 3) (Fin 3) ℝ :=
    tripleGram (D.atom a) (D.atom b) (D.atom c) - 1 with hG
  have hlit := tripleGram_eq_literal (D.atom a) (D.atom b) (D.atom c)
  have hentry : ∀ i j : Fin 3,
      G i j = (!![D.atom a ⬝ᵥ D.atom a - 1, D.atom a ⬝ᵥ D.atom b,
                    D.atom a ⬝ᵥ D.atom c;
                  D.atom a ⬝ᵥ D.atom b, D.atom b ⬝ᵥ D.atom b - 1,
                    D.atom b ⬝ᵥ D.atom c;
                  D.atom a ⬝ᵥ D.atom c, D.atom b ⬝ᵥ D.atom c,
                    D.atom c ⬝ᵥ D.atom c - 1] : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    intro i j
    rw [hG, Matrix.sub_apply, hlit]
    fin_cases i <;> fin_cases j <;> simp
  have hsymm : Gᵀ = G := by
    ext i j
    rw [Matrix.transpose_apply, hentry, hentry]
    fin_cases i <;> fin_cases j <;> simp
  refine posDef_three_of_zPattern_of_posVector hsymm ?_ ?_ ?_ hv0 hv1 hv2 ?_ ?_ ?_
  · rw [hentry]; simpa using hpab
  · rw [hentry]; simpa using hpac
  · rw [hentry]; simpa using hpbc
  · rw [hentry, hentry, hentry]; simpa using hr0
  · rw [hentry, hentry, hentry]; simpa using hr1
  · rw [hentry, hentry, hentry]; simpa using hr2

/-- **THE TIE REFUSES EVERY OBTUSE ROW-POSITIVE TRIPLE.**  The
contrapositive: at a tie no triple with nonpositive pairwise pairings has a
row-positive chart gap. -/
theorem isTie_not_obtuse_rowPositive (D : WeightedDesign m 3) (htie : IsTie D)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpab : D.atom a ⬝ᵥ D.atom b ≤ 0) (hpac : D.atom a ⬝ᵥ D.atom c ≤ 0)
    (hpbc : D.atom b ⬝ᵥ D.atom c ≤ 0)
    {scale : Fin 3 → ℝ} (hv0 : 0 < scale 0) (hv1 : 0 < scale 1)
    (hv2 : 0 < scale 2) :
    ¬ (0 < (D.atom a ⬝ᵥ D.atom a - 1) * scale 0
        + (D.atom a ⬝ᵥ D.atom b) * scale 1 + (D.atom a ⬝ᵥ D.atom c) * scale 2
      ∧ 0 < (D.atom a ⬝ᵥ D.atom b) * scale 0
        + (D.atom b ⬝ᵥ D.atom b - 1) * scale 1 + (D.atom b ⬝ᵥ D.atom c) * scale 2
      ∧ 0 < (D.atom a ⬝ᵥ D.atom c) * scale 0
        + (D.atom b ⬝ᵥ D.atom c) * scale 1
        + (D.atom c ⬝ᵥ D.atom c - 1) * scale 2) := by
  rintro ⟨hr0, hr1, hr2⟩
  have hcard : (({a, b, c} : Finset (Fin m))).card = 3 :=
    card_triple_eq hab hac hbc
  exact htie.2 _ hcard
    (posDef_subsetSum_of_obtuse_rowPositive D hab hac hbc hpab hpac hpbc
      hv0 hv1 hv2 hr0 hr1 hr2)

end Gtz
