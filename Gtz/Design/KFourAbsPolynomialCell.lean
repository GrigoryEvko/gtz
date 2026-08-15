/-
# The first sufficient cell for the third invariant of a K4 chart tree

`Gtz.kFourInvariantThree_eq` reads the third invariant coefficient as the
spanning-tree polynomial of the six selection values, and
`Gtz.selectionValue_pos_iff_mem` shows the sign pattern of those values is the
tree.  So at a spanning tree the polynomial carries one distinguished positive
term -- the tree's own monomial -- and fifteen terms of mixed sign.

The third coefficient is the whole of A3's remaining difficulty: the first two
never fail at a designated tree, while the third fails every time.  This module
lands the first sufficient condition the corpus carries for it.

The condition is one inequality.  Write `own` for the tree's own monomial and
`absPoly` for the polynomial evaluated at the absolute selection values.  Then
`absPoly < 2 * own` forces the third coefficient positive, because the sixteen
absolute terms bound the sixteen signed terms one by one and the own term is
already positive.

The same inequality reads as a threshold on the ratio `absPoly / own`, which is
the quantity that orders the trees best.  So the cell and the ratio designation
are one object seen at threshold two.
-/
import Mathlib
import Gtz.Design.KFourOwnMonomial
import Gtz.Design.KFourChartClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The sandwich, at the level of the six values

The polynomial has sixteen terms and every term is a product of three values.
Each signed term is at least minus its absolute term, and the term belonging to
the selection is at least two of itself minus its absolute term.  Summing the
sixteen bounds gives the sandwich, with no positivity hypothesis anywhere. -/

/-- **The one-term sandwich.**  For any values and any spanning tree, twice the
product over the tree is bounded by the signed polynomial plus the absolute
polynomial.  The tree enters only through which of the sixteen terms is
distinguished, so the statement holds with no sign hypothesis at all. -/
theorem kFourTreePolynomial_two_mul_prod_le (value : Fin 6 → ℝ)
    (tree : Finset (Fin 6)) (hmem : tree ∈ kFourSpanningTreeList) :
    2 * (∏ label ∈ tree, value label)
      ≤ kFourTreePolynomial value + kFourTreePolynomial (fun label => |value label|) := by
  have habs : ∀ a b c : Fin 6,
      |value a| * |value b| * |value c| = |value a * value b * value c| := by
    intro a b c; rw [abs_mul, abs_mul]
  have key : ∀ a b c : Fin 6,
      0 ≤ value a * value b * value c + |value a| * |value b| * |value c| := by
    intro a b c; rw [habs]; linarith [neg_abs_le (value a * value b * value c)]
  have self : ∀ a b c : Fin 6,
      2 * (value a * value b * value c)
        ≤ value a * value b * value c + |value a| * |value b| * |value c| := by
    intro a b c; rw [habs]; linarith [le_abs_self (value a * value b * value c)]
  simp only [kFourSpanningTreeList, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [kFourTreePolynomial] <;>
    · simp
      linarith [key 0 1 3, key 0 1 4, key 0 1 5, key 0 2 3, key 0 2 4, key 0 2 5,
        key 0 3 5, key 0 4 5, key 1 2 3, key 1 2 4, key 1 2 5, key 1 3 4,
        key 1 4 5, key 2 3 4, key 2 3 5, key 3 4 5,
        self 0 1 3, self 0 2 4, self 1 2 5, self 3 4 5, self 0 1 4, self 0 1 5,
        self 0 2 3, self 0 2 5, self 0 3 5, self 0 4 5, self 1 2 3, self 1 2 4,
        self 1 3 4, self 1 4 5, self 2 3 4, self 2 3 5]

/-! ## The absolute polynomial of a chart point

`Gtz.absSelectionValue` writes the absolute selection value without an absolute
value: the boost on the selection and the mass off it.  The absolute polynomial
is the tree polynomial read at those values, and it is division-free in the
same sense. -/

/-- The tree polynomial at the absolute selection values of a selection. -/
noncomputable def kFourAbsPolynomial (mass weight : Fin 6 → ℝ)
    (tree : Finset (Fin 6)) : ℝ :=
  kFourTreePolynomial (absSelectionValue mass weight tree)

/-- The absolute polynomial is the polynomial of the pointwise absolute values. -/
theorem kFourAbsPolynomial_eq (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    kFourAbsPolynomial point.mass point.weight tree
      = kFourTreePolynomial
          (fun label => |selectionValue point.mass point.weight tree label|) := by
  unfold kFourAbsPolynomial
  congr 1
  funext label
  exact (abs_selectionValue_eq point tree label).symm

/-- Every absolute selection value is nonnegative, so every term of the absolute
polynomial is nonnegative and the polynomial itself is. -/
theorem kFourAbsPolynomial_nonneg (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    0 ≤ kFourAbsPolynomial point.mass point.weight tree := by
  have hnn : ∀ label : Fin 6,
      0 ≤ absSelectionValue point.mass point.weight tree label :=
    fun label => absSelectionValue_nonneg point tree label
  simp only [kFourAbsPolynomial, kFourTreePolynomial]
  have hmul : ∀ a b c : Fin 6,
      0 ≤ absSelectionValue point.mass point.weight tree a
        * absSelectionValue point.mass point.weight tree b
        * absSelectionValue point.mass point.weight tree c :=
    fun a b c => mul_nonneg (mul_nonneg (hnn a) (hnn b)) (hnn c)
  linarith [hmul 0 1 3, hmul 0 1 4, hmul 0 1 5, hmul 0 2 3, hmul 0 2 4, hmul 0 2 5,
    hmul 0 3 5, hmul 0 4 5, hmul 1 2 3, hmul 1 2 4, hmul 1 2 5, hmul 1 3 4,
    hmul 1 4 5, hmul 2 3 4, hmul 2 3 5, hmul 3 4 5]

/-! ## The sandwich at a chart point

Instantiating the value-level sandwich at the selection values turns the product
over the tree into the tree's own monomial, by
`Gtz.kFourOwnMonomial_eq_prod_selectionValue`. -/

/-- **The chart sandwich.**  The third coefficient is at least twice the own
monomial minus the absolute polynomial. -/
theorem two_mul_kFourOwnMonomial_sub_le (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (hmem : tree ∈ kFourSpanningTreeList) :
    2 * kFourOwnMonomial point.mass point.weight tree
        - kFourAbsPolynomial point.mass point.weight tree
      ≤ kFourTreePolynomial (selectionValue point.mass point.weight tree) := by
  have hsand := kFourTreePolynomial_two_mul_prod_le
    (selectionValue point.mass point.weight tree) tree hmem
  rw [← kFourOwnMonomial_eq_prod_selectionValue] at hsand
  rw [kFourAbsPolynomial_eq point tree]
  linarith

/-! ## The cell

The own monomial is strictly positive at every chart point, so the hypothesis
below is a statement about how far the fifteen other terms can pull the third
coefficient down. -/

/-- **The cell for the third coefficient.**  An absolute polynomial below twice
the own monomial forces the third coefficient positive. -/
theorem kFourTreePolynomial_pos_of_absPolynomial_lt (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (hmem : tree ∈ kFourSpanningTreeList)
    (hcell : kFourAbsPolynomial point.mass point.weight tree
      < 2 * kFourOwnMonomial point.mass point.weight tree) :
    0 < kFourTreePolynomial (selectionValue point.mass point.weight tree) := by
  have hsand := two_mul_kFourOwnMonomial_sub_le point tree hmem
  linarith

/-- The cell reads as a threshold on the ratio of the absolute polynomial to the
own monomial.  The own monomial is positive, so the two forms are equivalent and
the cell is the ratio designation seen at threshold two. -/
theorem kFourAbsPolynomial_lt_iff_ratio_lt_two (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    kFourAbsPolynomial point.mass point.weight tree
        < 2 * kFourOwnMonomial point.mass point.weight tree
      ↔ kFourAbsPolynomial point.mass point.weight tree
          / kFourOwnMonomial point.mass point.weight tree < 2 := by
  have hown := kFourOwnMonomial_pos point tree
  rw [div_lt_iff₀ hown]

/-! ## The cell as a positive definiteness criterion

`Gtz.kFourTree_posDef_iff_polynomial` decides the gap by three explicit
polynomial conditions in the six selection values.  The cell discharges the
third, which is the one that fails. -/

/-- **The full cell.**  The first two conditions together with the cell give a
positive definite gap. -/
theorem posDef_kFourTree_of_absPolynomial_cell (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (hmem : tree ∈ kFourSpanningTreeList)
    (hone : 0 < ∑ label, selectionValue point.mass point.weight tree label)
    (htwo : 0 < kFourPairForm (selectionValue point.mass point.weight tree))
    (hcell : kFourAbsPolynomial point.mass point.weight tree
      < 2 * kFourOwnMonomial point.mass point.weight tree) :
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  rw [kFourTree_posDef_iff_polynomial]
  exact ⟨hone, htwo,
    kFourTreePolynomial_pos_of_absPolynomial_lt point tree hmem hcell⟩

/-! ## The cell at the family level

Every member of the spanning tree list has three labels, so a firing tree is a
card-three selection and the leaf's existential is discharged. -/

/-- Each of the sixteen spanning trees carries three labels. -/
theorem card_eq_three_of_mem_kFourSpanningTreeList (tree : Finset (Fin 6))
    (hmem : tree ∈ kFourSpanningTreeList) : tree.card = 3 := by
  simp only [kFourSpanningTreeList, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- **The family reading.**  A spanning tree that clears the first two
conditions and fires the cell supplies the leaf's card-three witness. -/
theorem exists_posDef_of_kFourAbsPolynomialCell (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (hmem : tree ∈ kFourSpanningTreeList)
    (hone : 0 < ∑ label, selectionValue point.mass point.weight tree label)
    (htwo : 0 < kFourPairForm (selectionValue point.mass point.weight tree))
    (hcell : kFourAbsPolynomial point.mass point.weight tree
      < 2 * kFourOwnMonomial point.mass point.weight tree) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap kFourDirection point.mass point.weight selected).PosDef :=
  ⟨tree, card_eq_three_of_mem_kFourSpanningTreeList tree hmem,
    posDef_kFourTree_of_absPolynomial_cell point tree hmem hone htwo hcell⟩

/-! ## The cell as a named condition

The Prop below is the cell quantified over the chart, in the shape the atlas
uses.  It is a sufficient condition and is not claimed to be total: the census
records that some tree fires it at a high but not unit rate. -/

/-- The cell fires at a chart point when some spanning tree clears all three
conditions with the third supplied by the absolute polynomial bound. -/
def KFourAbsPolynomialCellFires (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList,
    0 < ∑ label, selectionValue point.mass point.weight tree label
      ∧ 0 < kFourPairForm (selectionValue point.mass point.weight tree)
      ∧ kFourAbsPolynomial point.mass point.weight tree
        < 2 * kFourOwnMonomial point.mass point.weight tree

/-- **The cell discharges the leaf where it fires.** -/
theorem exists_posDef_of_kFourAbsPolynomialCellFires (point : DirectionChartPoint 6)
    (hfires : KFourAbsPolynomialCellFires point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap kFourDirection point.mass point.weight selected).PosDef := by
  obtain ⟨tree, hmem, hone, htwo, hcell⟩ := hfires
  exact exists_posDef_of_kFourAbsPolynomialCell point tree hmem hone htwo hcell

/-! ## The gap the cell leaves

The sandwich is one-sided.  The cell asks the absolute polynomial to stay below
twice the own monomial, while the third coefficient only needs to stay positive,
so every point where the fifteen other terms cancel among themselves is outside
the cell and inside the leaf.  The two statements below record that the cell is
strictly stronger than the conclusion it delivers. -/

/-- The cell implies the own monomial exceeds half the absolute polynomial, which
is a statement about the tree alone. -/
theorem two_mul_kFourOwnMonomial_gt_of_cell (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6))
    (hcell : kFourAbsPolynomial point.mass point.weight tree
      < 2 * kFourOwnMonomial point.mass point.weight tree) :
    kFourAbsPolynomial point.mass point.weight tree / 2
      < kFourOwnMonomial point.mass point.weight tree := by
  linarith

/-- The own monomial is one of the sixteen absolute terms, so it never exceeds
the absolute polynomial.  The cell therefore lives in the band where the ratio
sits between one and two. -/
theorem kFourOwnMonomial_le_kFourAbsPolynomial (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (hmem : tree ∈ kFourSpanningTreeList) :
    kFourOwnMonomial point.mass point.weight tree
      ≤ kFourAbsPolynomial point.mass point.weight tree := by
  have hnn : ∀ label : Fin 6,
      0 ≤ absSelectionValue point.mass point.weight tree label :=
    fun label => absSelectionValue_nonneg point tree label
  have hmul : ∀ a b c : Fin 6,
      0 ≤ absSelectionValue point.mass point.weight tree a
        * absSelectionValue point.mass point.weight tree b
        * absSelectionValue point.mass point.weight tree c :=
    fun a b c => mul_nonneg (mul_nonneg (hnn a) (hnn b)) (hnn c)
  have hown : kFourOwnMonomial point.mass point.weight tree
      = ∏ label ∈ tree, absSelectionValue point.mass point.weight tree label := by
    unfold kFourOwnMonomial
    refine Finset.prod_congr rfl (fun label hlabel => ?_)
    simp only [absSelectionValue, if_pos hlabel]
  rw [hown]
  simp only [kFourAbsPolynomial, kFourTreePolynomial]
  simp only [kFourSpanningTreeList, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    · simp
      linarith [hmul 0 1 3, hmul 0 1 4, hmul 0 1 5, hmul 0 2 3, hmul 0 2 4, hmul 0 2 5,
        hmul 0 3 5, hmul 0 4 5, hmul 1 2 3, hmul 1 2 4, hmul 1 2 5, hmul 1 3 4,
        hmul 1 4 5, hmul 2 3 4, hmul 2 3 5, hmul 3 4 5]

end Gtz
