import Gtz.Design.TripleGramSylvester
import Gtz.Wave.ChartProgrammeHeavyResidual

/-!
# The admissible-pair graph, and the collapse of the one-line residual to one
# determinant sign

`Gtz.subsetSum_posDef_iff_tripleInvariants` decides strict domination by three
polynomial inequalities.  `Gtz.subsetSum_posDef_of_heavy_of_minorSum_of_det`
discharges the first from heaviness, leaving two.  This file removes the second.

Put an edge between two labels when their pair minor is positive.  Every strict
dominator is a TRIANGLE of that graph (`Gtz.forall_pairGapMinor_pos_of_subsetSum_posDef`),
and the second invariant is the SUM of the triangle's three pair minors
(`Gtz.pairMinor_sum_eq_secondInvariant`).  A triangle therefore discharges the
second inequality for free, and `Gtz.posDef_iff_tripleGapDet_of_admissibleTriangle`
states what is left: ONE determinant sign.

The file also records that the obligation's raw-weight antecedent is free.  Six
weights sum to one, so one of them is at least `1/6`, which already exceeds the
demanded `1/10`.
-/

namespace Gtz

open Finset

/-! ## 1. The tenth-heavy antecedent costs nothing -/

/-- **THE ONE-LINE OBLIGATION'S RAW-WEIGHT ANTECEDENT IS FREE.**
`Gtz.OneLineTenthHeavyJointBlindLineSparse` demands a label of raw weight at
least `1/10`.  Six weights sum to one, so one is at least `1/6`, which already
exceeds `1/10`.  The hypothesis therefore narrows nothing.

The underlying fact is `Gtz.not_forall_weight_lt_tenth`, which is the same
statement with the quantifier negated; this is that fact carried to a different
consumer, not a new one. -/
theorem oneLineTenthHeavy_antecedent_free (design : WeightedDesign 6 3) :
    ∃ heavyLabel : Fin 6, (1 : ℝ) / 10 ≤ design.weight heavyLabel := by
  by_contra hno
  push Not at hno
  exact not_forall_weight_lt_tenth design hno

/-! ## 2. Weak heaviness plus one admissible pair gives strict heaviness -/

/-- **AN ADMISSIBLE PAIR UPGRADES WEAK HEAVINESS TO STRICT.**  The pair minor is
`(la - 1)(lb - 1) - (a . b)^2`.  A vanishing left factor kills the product and
leaves a negative square, so both factors are strictly positive. -/
theorem one_lt_leverage_left_of_admissiblePair (a b : Fin 3 → ℝ)
    (hadm : AdmissiblePair a b) (_hwa : 1 ≤ leverageOf a) (hwb : 1 ≤ leverageOf b) :
    1 < leverageOf a := by
  rw [AdmissiblePair, pairGapMinor] at hadm
  nlinarith [sq_nonneg (a ⬝ᵥ b), hadm, hwb]

/-- The right-hand companion.  The opposite endpoint's weak heaviness is what
carries it, so the two lemmas read different hypotheses. -/
theorem one_lt_leverage_right_of_admissiblePair (a b : Fin 3 → ℝ)
    (hadm : AdmissiblePair a b) (hwa : 1 ≤ leverageOf a) (_hwb : 1 ≤ leverageOf b) :
    1 < leverageOf b := by
  rw [AdmissiblePair, pairGapMinor] at hadm
  nlinarith [sq_nonneg (a ⬝ᵥ b), hadm, hwa]

/-- Both endpoints of an admissible pair are strictly heavy under weak
heaviness. -/
theorem one_lt_leverage_both_of_admissiblePair (a b : Fin 3 → ℝ)
    (hadm : AdmissiblePair a b) (hwa : 1 ≤ leverageOf a) (hwb : 1 ≤ leverageOf b) :
    1 < leverageOf a ∧ 1 < leverageOf b :=
  ⟨one_lt_leverage_left_of_admissiblePair a b hadm hwa hwb,
    one_lt_leverage_right_of_admissiblePair a b hadm hwa hwb⟩

/-! ## 3. The admissible-pair graph -/

/-- **THE EDGE RELATION.**  Two labels are adjacent when their pair minor is
positive.  The relation reads two atoms and nothing else. -/
def AdmissibleEdge {m : ℕ} (D : WeightedDesign m 3) (x y : Fin m) : Prop :=
  AdmissiblePair (D.atom x) (D.atom y)

theorem admissibleEdge_symm {m : ℕ} (D : WeightedDesign m 3) (x y : Fin m)
    (hxy : AdmissibleEdge D x y) : AdmissibleEdge D y x := by
  rw [AdmissibleEdge, AdmissiblePair, pairGapMinor_comm]
  exact hxy

theorem admissibleEdge_iff {m : ℕ} (D : WeightedDesign m 3) (x y : Fin m) :
    AdmissibleEdge D x y ↔ 0 < pairGapMinor (D.atom x) (D.atom y) := Iff.rfl

/-- The edge relation in cross-norm vocabulary: the pair's squared area beats
the sum of its leverages less one. -/
theorem admissibleEdge_iff_crossNormSq {m : ℕ} (D : WeightedDesign m 3) (x y : Fin m) :
    AdmissibleEdge D x y ↔
      leverageOf (D.atom x) + leverageOf (D.atom y) - 1
        < crossNormSq (D.atom x) (D.atom y) := by
  rw [admissibleEdge_iff, pairGapMinor_eq_crossNormSq]
  constructor <;> intro h <;> linarith

/-- **A TRIANGLE.**  Three labels pairwise adjacent. -/
def AdmissibleTriangle {m : ℕ} (D : WeightedDesign m 3) (x y z : Fin m) : Prop :=
  AdmissibleEdge D x y ∧ AdmissibleEdge D x z ∧ AdmissibleEdge D y z

theorem admissibleTriangle_fst {m : ℕ} (D : WeightedDesign m 3) (x y z : Fin m)
    (h : AdmissibleTriangle D x y z) : 0 < pairGapMinor (D.atom x) (D.atom y) := h.1

theorem admissibleTriangle_snd {m : ℕ} (D : WeightedDesign m 3) (x y z : Fin m)
    (h : AdmissibleTriangle D x y z) : 0 < pairGapMinor (D.atom x) (D.atom z) := h.2.1

theorem admissibleTriangle_thd {m : ℕ} (D : WeightedDesign m 3) (x y z : Fin m)
    (h : AdmissibleTriangle D x y z) : 0 < pairGapMinor (D.atom y) (D.atom z) := h.2.2

/-! ## 4. Every strict dominator is a triangle -/

/-- **TRIANGLE NECESSITY.**  A strictly dominating triple is pairwise
adjacent. -/
theorem admissibleTriangle_of_subsetSum_posDef {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpos : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    AdmissibleTriangle D x y z := by
  obtain ⟨h1, h2, h3⟩ := forall_pairGapMinor_pos_of_subsetSum_posDef D x y z hxy hxz hyz hpos
  exact ⟨h1, h2, h3⟩

/-- **THE TRIANGLE PRUNING RULE.**  A triple missing an edge is not a strict
dominator.  This is the contrapositive of triangle necessity and it is the form
a search consumes. -/
theorem not_subsetSum_posDef_of_not_admissibleTriangle {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hbad : ¬ AdmissibleTriangle D x y z) :
    ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef := fun hpos =>
  hbad (admissibleTriangle_of_subsetSum_posDef D x y z hxy hxz hyz hpos)

/-! ## 5. The collapse: at a triangle only the determinant is left -/

/-- **THE SECOND INVARIANT IS FREE AT A TRIANGLE.**  It is the sum of the
triangle's three pair minors, each positive by adjacency. -/
theorem secondInvariant_pos_of_admissibleTriangle {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (htri : AdmissibleTriangle D x y z) :
    0 < triplePairAreaSum (D.atom x) (D.atom y) (D.atom z)
        - 2 * tripleLeverageSum (D.atom x) (D.atom y) (D.atom z) + 3 := by
  rw [← pairMinor_sum_eq_secondInvariant]
  have h1 := admissibleTriangle_fst D x y z htri
  have h2 := admissibleTriangle_snd D x y z htri
  have h3 := admissibleTriangle_thd D x y z htri
  linarith

/-- **THE RESIDUAL IS ONE DETERMINANT SIGN.**  Under weak heaviness, a triple
whose three pairs are all admissible is a strict dominator exactly when its Gram
gap determinant is positive.  Both other Sylvester minors are discharged: the
first by heaviness upgraded through an admissible pair, the second by adjacency.

This is the reduction the one-line obligation needed.  Its residual was two
polynomial inequalities and at a triangle it is one. -/
theorem posDef_iff_tripleGapDet_of_admissibleTriangle {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (htri : AdmissibleTriangle D x y z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z) := by
  rw [subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz]
  constructor
  · rintro ⟨-, -, hdet⟩
    exact hdet
  · intro hdet
    have hstrict : 1 < leverageOf (D.atom x) :=
      one_lt_leverage_left_of_admissiblePair _ _ htri.1 (hheavy x) (hheavy y)
    exact ⟨by linarith, htri.1, hdet⟩

/-- The producer form: a triangle with positive determinant is a strict
dominator. -/
theorem subsetSum_posDef_of_admissibleTriangle_of_det {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (htri : AdmissibleTriangle D x y z)
    (hdet : 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z)) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef :=
  (posDef_iff_tripleGapDet_of_admissibleTriangle D x y z hxy hxz hyz hheavy htri).mpr hdet

/-- Every atom of a triangle is strictly heavy under weak heaviness. -/
theorem one_lt_leverage_of_admissibleTriangle {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (htri : AdmissibleTriangle D x y z) :
    1 < leverageOf (D.atom x) ∧ 1 < leverageOf (D.atom y)
      ∧ 1 < leverageOf (D.atom z) := by
  refine ⟨?_, ?_, ?_⟩
  · exact one_lt_leverage_left_of_admissiblePair _ _ htri.1 (hheavy x) (hheavy y)
  · exact one_lt_leverage_right_of_admissiblePair _ _ htri.1 (hheavy x) (hheavy y)
  · exact one_lt_leverage_right_of_admissiblePair _ _ htri.2.1 (hheavy x) (hheavy z)

/-! ## 6. The residual against the corpus's own three-invariant form -/

/-- **THE TRACE INVARIANT IS FREE AT A TRIANGLE.**  Adjacency upgrades weak
heaviness to strict at every atom of the triangle, and one strictly heavy member
is what the landed trace discharge asks for. -/
theorem firstInvariant_pos_of_admissibleTriangle {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (htri : AdmissibleTriangle D x y z) :
    0 < tripleLeverageSum (D.atom x) (D.atom y) (D.atom z) - 3 :=
  tripleLeverageSum_sub_three_pos_of_heavy D x y z hheavy
    (one_lt_leverage_left_of_admissiblePair _ _ htri.1 (hheavy x) (hheavy y))

/-- **THE ONE-LINE RESIDUAL, IN THE CORPUS'S OWN COORDINATES.**  The corpus
states strict domination as three polynomial inequalities in the leverages, the
pair areas and the bracket.  Under weak heaviness a triangle discharges the
first two, so the whole content is the THIRD.

`Gtz.subsetSum_posDef_of_heavy_of_minorSum_of_det` discharged one of the three
and left two.  This leaves one. -/
theorem posDef_iff_thirdInvariant_of_admissibleTriangle {m : ℕ}
    (D : WeightedDesign m 3) (x y z : Fin m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (htri : AdmissibleTriangle D x y z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ 0 < atomBracket D x y z ^ 2
            - triplePairAreaSum (D.atom x) (D.atom y) (D.atom z)
            + tripleLeverageSum (D.atom x) (D.atom y) (D.atom z) - 1 := by
  rw [subsetSum_posDef_iff_tripleInvariants D x y z hxy hxz hyz]
  constructor
  · rintro ⟨-, -, hthird⟩
    exact hthird
  · intro hthird
    exact ⟨firstInvariant_pos_of_admissibleTriangle D x y z hheavy htri,
      secondInvariant_pos_of_admissibleTriangle D x y z htri, hthird⟩

/-! ## 7. The pair rule catches what the leverage floor cannot -/

/-- **A LIGHT ATOM KILLS ITS EDGES TO HEAVY PARTNERS.**  A light atom has a
non-positive left factor and a heavy partner a non-negative right one, so the
product cannot beat a square.

This does NOT subsume `Gtz.notPosDef_of_mem_leverage_le_one`, which prunes a
light atom's triples with no hypothesis at all on the other two.  It matches it
only on the class the one-line obligation quantifies over, where every leverage
is at least one. -/
theorem not_admissiblePair_of_leverage_le_one (a b : Fin 3 → ℝ)
    (hlight : leverageOf a ≤ 1) (hheavy : 1 ≤ leverageOf b) :
    ¬ AdmissiblePair a b := by
  rw [AdmissiblePair, pairGapMinor]
  push Not
  nlinarith [sq_nonneg (a ⬝ᵥ b), hlight, hheavy]

/-- **THE PAIR RULE IS STRICTLY FINER THAN THE LEVERAGE FLOOR.**  Heaviness is a
diagonal reading and adjacency is an off-diagonal one, so a pair can fail while
both of its atoms are strictly heavy.  The leverage floor never prunes such a
pair, and the pair rule always does. -/
theorem exists_heavy_inadmissiblePair :
    ∃ a b : Fin 3 → ℝ, 1 < leverageOf a ∧ 1 < leverageOf b
      ∧ ¬ AdmissiblePair a b := by
  refine ⟨![2, 0, 0], ![1, 1, 0], ?_, ?_, ?_⟩
  · simp [leverageOf, Fin.sum_univ_three]
  · simp [leverageOf, Fin.sum_univ_three]
  · rw [AdmissiblePair, pairGapMinor]
    simp only [leverageOf, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    norm_num

/-- **ON THE HEAVY CLASS, ADJACENCY STRICTLY REFINES THE LEVERAGE FLOOR.**
Restricted to designs whose leverages are all at least one — the class the
one-line obligation quantifies over — adjacency prunes every pair a light atom
gives, and it also prunes pairs whose two atoms are both strictly heavy.  The
floor never sees the second kind, because heaviness is a diagonal reading and
adjacency is an off-diagonal one. -/
theorem pairRule_strictly_refines_leverageFloor_on_heavy :
    (∀ a b : Fin 3 → ℝ, leverageOf a ≤ 1 → 1 ≤ leverageOf b → ¬ AdmissiblePair a b)
      ∧ ∃ a b : Fin 3 → ℝ, 1 < leverageOf a ∧ 1 < leverageOf b
          ∧ ¬ AdmissiblePair a b :=
  ⟨not_admissiblePair_of_leverage_le_one, exists_heavy_inadmissiblePair⟩

/-! ## 8. What one failed edge costs -/

/-- **A FAILED EDGE POISONS FOUR TRIPLES.**  At six labels the third member of a
triple through a fixed pair ranges over the four remaining labels, so one
inadmissible pair removes exactly four of the twenty candidates. -/
theorem card_thirdLabels_through_pair (x y : Fin 6) (hxy : x ≠ y) :
    ((Finset.univ : Finset (Fin 6)) \ ({x, y} : Finset (Fin 6))).card = 4 := by
  rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl,
    Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton,
    Fintype.card_fin]

/-- Every triple through an inadmissible pair fails, and there are four of
them. -/
theorem not_posDef_of_mem_thirdLabels {m : ℕ} (D : WeightedDesign m 3)
    (x y : Fin m) (hbad : ¬ AdmissibleEdge D x y) (z : Fin m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef :=
  not_subsetSum_posDef_of_not_admissibleTriangle D x y z hxy hxz hyz
    (fun htri => hbad htri.1)

/-! ## 9. The covering statement and its consumer -/

/-- **THE TRIANGLE COVER.**  Some card-three set of labels is pairwise adjacent
and carries a positive determinant.  This is the covering shape the one-line
obligation consumes, and it is stated at the graph level with no normal, no
probe and no anatomy. -/
def AdmissibleTriangleCovers {m : ℕ} (D : WeightedDesign m 3) : Prop :=
  ∃ x y z : Fin m, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ AdmissibleTriangle D x y z
    ∧ 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z)

/-- **THE COVER SUPPLIES A STRICT DOMINATOR.** -/
theorem exists_subsetSum_posDef_of_admissibleTriangleCovers {m : ℕ}
    (D : WeightedDesign m 3)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (hcover : AdmissibleTriangleCovers D) :
    ∃ selected : Finset (Fin m), selected.card = 3
      ∧ (subsetSum D selected - 1).PosDef := by
  obtain ⟨x, y, z, hxy, hxz, hyz, htri, hdet⟩ := hcover
  refine ⟨{x, y, z}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  · exact subsetSum_posDef_of_admissibleTriangle_of_det D x y z hxy hxz hyz hheavy htri hdet

/-- The converse half: a strict dominator gives a triangle with a positive
determinant, so the cover is not a strengthening. -/
theorem admissibleTriangleCovers_of_subsetSum_posDef {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpos : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    AdmissibleTriangleCovers D := by
  refine ⟨x, y, z, hxy, hxz, hyz,
    admissibleTriangle_of_subsetSum_posDef D x y z hxy hxz hyz hpos, ?_⟩
  exact ((subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz).mp hpos).2.2

end Gtz
