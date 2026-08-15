/-
# The own monomial of a K4 chart tree, and the refutation of its greedy maximum

`Gtz.kFourInvariantThree_eq` reads the third invariant coefficient of a K4 chart
tree gap as the spanning-tree polynomial of the six selection values, and
`Gtz.selectionValue_pos_iff_mem` shows the sign pattern of those values IS the
tree.  So at a tree the polynomial has one distinguished positive term -- the
product over the tree itself -- and fifteen terms of mixed sign.

This module names that distinguished term, gives it the multiplicative law that
makes its maximum a greedy matroid maximum, refutes the designation that takes
the maximizing tree, and lands the first sufficient cell for the third
coefficient that the corpus carries.

The refutation matters because the four mandatory chart points do NOT
discriminate this designation: it survives all four and fails only under a
directed sweep.
-/
import Mathlib
import Gtz.Design.ChartEntrySumRung

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The own monomial

A tree prices each of its own labels at the boost `mass / weight - mass`, which
is the selection value the tree gives that label.  The product of those three
prices is the tree's own monomial in the spanning-tree polynomial. -/

/-- The boost a selection gives one of its own labels. -/
noncomputable def treeBoost (mass weight : Fin 6 → ℝ) (label : Fin 6) : ℝ :=
  mass label / weight label - mass label

/-- **The own monomial of a selection**: the product of the boosts of its
members.  It does not read the labels outside the selection at all. -/
noncomputable def kFourOwnMonomial (mass weight : Fin 6 → ℝ)
    (tree : Finset (Fin 6)) : ℝ :=
  ∏ label ∈ tree, treeBoost mass weight label

theorem kFourOwnMonomial_empty (mass weight : Fin 6 → ℝ) :
    kFourOwnMonomial mass weight ∅ = 1 := by
  simp [kFourOwnMonomial]

/-- **The multiplicative law.**  Adding a label multiplies the own monomial by
that label's boost, so the own monomial is modular in the logarithm and its
maximum over a matroid is a greedy maximum. -/
theorem kFourOwnMonomial_insert (mass weight : Fin 6 → ℝ)
    (tree : Finset (Fin 6)) (label : Fin 6) (hnot : label ∉ tree) :
    kFourOwnMonomial mass weight (insert label tree)
      = treeBoost mass weight label * kFourOwnMonomial mass weight tree := by
  simp [kFourOwnMonomial, Finset.prod_insert hnot]

/-- The boost of a chart label is strictly positive: the weight is below one and
the mass is positive. -/
theorem treeBoost_pos (point : DirectionChartPoint 6) (label : Fin 6) :
    0 < treeBoost point.mass point.weight label := by
  have hw := point.weight_pos label
  have hm := point.mass_pos label
  have hlt : point.weight label < 1 := chartPoint_weight_lt_one point label
  have hdiv : point.mass label < point.mass label / point.weight label := by
    rw [lt_div_iff₀ hw]
    nlinarith
  simpa [treeBoost] using sub_pos.mpr hdiv

/-- The own monomial of any selection at a chart point is strictly positive. -/
theorem kFourOwnMonomial_pos (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    0 < kFourOwnMonomial point.mass point.weight tree :=
  Finset.prod_pos (fun label _ => treeBoost_pos point label)

/-- **The own monomial is the tree's own selection values.**  On its own tree a
label's selection value IS its boost. -/
theorem selectionValue_eq_treeBoost_of_mem (mass weight : Fin 6 → ℝ)
    (tree : Finset (Fin 6)) (label : Fin 6) (hmem : label ∈ tree) :
    selectionValue mass weight tree label = treeBoost mass weight label := by
  simp [selectionValue, treeBoost, if_pos hmem]

theorem kFourOwnMonomial_eq_prod_selectionValue (mass weight : Fin 6 → ℝ)
    (tree : Finset (Fin 6)) :
    kFourOwnMonomial mass weight tree
      = ∏ label ∈ tree, selectionValue mass weight tree label := by
  refine Finset.prod_congr rfl (fun label hmem => ?_) |>.symm
  exact selectionValue_eq_treeBoost_of_mem mass weight tree label hmem

/-! ## The designation that takes the greedy maximum, and its refutation

Every designation the campaign has refuted ordered the trees by something other
than their own monomial: max conductance, determinant argmax, leverage edge, the
three invariant argmaxes, and the entry-sum rung.  The determinant is the SIGNED
SUM of all sixteen monomials, which is a different quantity from a tree's own.

The designation below is therefore new.  It is also false. -/

/-- The designation: at every chart point, a selection of largest own monomial
carries a positive definite gap. -/
def KFourOwnMonomialArgmaxHostsStrictTree : Prop :=
  ∀ point : DirectionChartPoint 6, ∀ tree : Finset (Fin 6),
    tree.card = 3 →
    (∀ other : Finset (Fin 6), other.card = 3 →
      kFourOwnMonomial point.mass point.weight other
        ≤ kFourOwnMonomial point.mass point.weight tree) →
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-! ### The witness

`mass = (1, 3/2, 1, 1, 1, 2)` and `weight = (1/9, 2/9, 1/9, 1/9, 2/9, 2/9)`.
The six boosts are `8`, `21/4`, `8`, `8`, `7/2`, `7`.

The selection `{0,2,3}` has own monomial `8 * 8 * 8 = 512`, the strict maximum
over all twenty card-three selections.  Its third coefficient is `-79`, so it is
not positive definite.  The selection `{0,1,3}`, of own monomial `336`, is
positive definite, so the leaf holds at this point and the failure is the
designation's alone. -/

noncomputable def ownMonomialRefuterMass : Fin 6 → ℝ
  | 0 => 1
  | 1 => 3 / 2
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 2

noncomputable def ownMonomialRefuterWeight : Fin 6 → ℝ
  | 0 => 1 / 9
  | 1 => 2 / 9
  | 2 => 1 / 9
  | 3 => 1 / 9
  | 4 => 2 / 9
  | 5 => 2 / 9

noncomputable def ownMonomialRefuterPoint : DirectionChartPoint 6 where
  mass := ownMonomialRefuterMass
  weight := ownMonomialRefuterWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [ownMonomialRefuterMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [ownMonomialRefuterWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [ownMonomialRefuterWeight]

theorem ownMonomialRefuterPoint_mass_eq :
    ownMonomialRefuterPoint.mass = ownMonomialRefuterMass := rfl

theorem ownMonomialRefuterPoint_weight_eq :
    ownMonomialRefuterPoint.weight = ownMonomialRefuterWeight := rfl

/-- The six boosts of the witness. -/
theorem ownMonomialRefuter_treeBoost :
    treeBoost ownMonomialRefuterMass ownMonomialRefuterWeight 0 = 8
      ∧ treeBoost ownMonomialRefuterMass ownMonomialRefuterWeight 1 = 21 / 4
      ∧ treeBoost ownMonomialRefuterMass ownMonomialRefuterWeight 2 = 8
      ∧ treeBoost ownMonomialRefuterMass ownMonomialRefuterWeight 3 = 8
      ∧ treeBoost ownMonomialRefuterMass ownMonomialRefuterWeight 4 = 7 / 2
      ∧ treeBoost ownMonomialRefuterMass ownMonomialRefuterWeight 5 = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [treeBoost, ownMonomialRefuterMass, ownMonomialRefuterWeight]

/-- The maximizing selection has own monomial `512`. -/
theorem ownMonomialRefuter_own_zeroTwoThree :
    kFourOwnMonomial ownMonomialRefuterMass ownMonomialRefuterWeight {0, 2, 3} = 512 := by
  rw [kFourOwnMonomial, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  norm_num [treeBoost, ownMonomialRefuterMass, ownMonomialRefuterWeight]

/-- A positive definite selection at the same point, of strictly smaller own
monomial.  This is what makes the point a refutation rather than a hard case. -/
theorem ownMonomialRefuter_own_zeroOneThree :
    kFourOwnMonomial ownMonomialRefuterMass ownMonomialRefuterWeight {0, 1, 3} = 336 := by
  rw [kFourOwnMonomial, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  norm_num [treeBoost, ownMonomialRefuterMass, ownMonomialRefuterWeight]

/-- The selection values of `{0,2,3}` at the witness. -/
theorem ownMonomialRefuter_selectionValue_zeroTwoThree :
    selectionValue ownMonomialRefuterMass ownMonomialRefuterWeight {0, 2, 3} 0 = 8
      ∧ selectionValue ownMonomialRefuterMass ownMonomialRefuterWeight {0, 2, 3} 1 = -(3 / 2)
      ∧ selectionValue ownMonomialRefuterMass ownMonomialRefuterWeight {0, 2, 3} 2 = 8
      ∧ selectionValue ownMonomialRefuterMass ownMonomialRefuterWeight {0, 2, 3} 3 = 8
      ∧ selectionValue ownMonomialRefuterMass ownMonomialRefuterWeight {0, 2, 3} 4 = -1
      ∧ selectionValue ownMonomialRefuterMass ownMonomialRefuterWeight {0, 2, 3} 5 = -2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [selectionValue, ownMonomialRefuterMass, ownMonomialRefuterWeight,
      Finset.mem_insert, Finset.mem_singleton] <;> decide

/-- **The third coefficient of the maximizing selection is negative.** -/
theorem ownMonomialRefuter_invariantThree_zeroTwoThree :
    kFourTreePolynomial
      (selectionValue ownMonomialRefuterMass ownMonomialRefuterWeight {0, 2, 3}) = -79 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := ownMonomialRefuter_selectionValue_zeroTwoThree
  simp only [kFourTreePolynomial, h0, h1, h2, h3, h4, h5]
  norm_num

/-- **The maximizing selection is not positive definite.** -/
theorem ownMonomialRefuter_zeroTwoThree_not_posDef :
    ¬ (directionChartGap kFourDirection ownMonomialRefuterPoint.mass
        ownMonomialRefuterPoint.weight {0, 2, 3}).PosDef := by
  rw [ownMonomialRefuterPoint_mass_eq, ownMonomialRefuterPoint_weight_eq,
    kFourTree_posDef_iff_polynomial]
  intro hall
  have hthree := hall.2.2
  rw [ownMonomialRefuter_invariantThree_zeroTwoThree] at hthree
  norm_num at hthree

/-! ### The maximality, over all twenty card-three selections

The six boosts are `8, 21/4, 8, 8, 7/2, 7`, all at most `8`, so every product of
three of them is at most `512`, with equality only at `{0,2,3}`.  That bounds
the twenty selections uniformly without enumerating them. -/

/-- Every boost of the witness is at most `8`, and at least `21/4`. -/
theorem ownMonomialRefuter_treeBoost_le_eight (label : Fin 6) :
    treeBoost ownMonomialRefuterMass ownMonomialRefuterWeight label ≤ 8 := by
  fin_cases label <;>
    norm_num [treeBoost, ownMonomialRefuterMass, ownMonomialRefuterWeight]

theorem ownMonomialRefuter_treeBoost_pos (label : Fin 6) :
    0 < treeBoost ownMonomialRefuterMass ownMonomialRefuterWeight label := by
  fin_cases label <;>
    norm_num [treeBoost, ownMonomialRefuterMass, ownMonomialRefuterWeight]

/-- **`{0,2,3}` maximizes the own monomial over every card-three selection.**
Each of its three boosts is the largest available, so no selection of the same
size can beat the product. -/
theorem ownMonomialRefuter_zeroTwoThree_maximal (other : Finset (Fin 6))
    (hcard : other.card = 3) :
    kFourOwnMonomial ownMonomialRefuterMass ownMonomialRefuterWeight other
      ≤ kFourOwnMonomial ownMonomialRefuterMass ownMonomialRefuterWeight {0, 2, 3} := by
  rw [ownMonomialRefuter_own_zeroTwoThree, kFourOwnMonomial]
  calc ∏ label ∈ other, treeBoost ownMonomialRefuterMass ownMonomialRefuterWeight label
      ≤ ∏ _label ∈ other, (8 : ℝ) := by
        refine Finset.prod_le_prod (fun label _ => ?_) (fun label _ => ?_)
        · exact (ownMonomialRefuter_treeBoost_pos label).le
        · exact ownMonomialRefuter_treeBoost_le_eight label
    _ = 512 := by rw [Finset.prod_const, hcard]; norm_num

/-- **The designation is false.**  At the witness the unique own-monomial
maximizer `{0,2,3}` is not positive definite, while `{0,1,3}` at own monomial
`336` is, so the point carries a positive definite selection and only the
designation fails. -/
theorem not_kFourOwnMonomialArgmaxHostsStrictTree :
    ¬ KFourOwnMonomialArgmaxHostsStrictTree := by
  intro hdesignation
  exact ownMonomialRefuter_zeroTwoThree_not_posDef
    (hdesignation ownMonomialRefuterPoint {0, 2, 3} (by decide)
      (fun other hcard => by
        rw [ownMonomialRefuterPoint_mass_eq, ownMonomialRefuterPoint_weight_eq]
        exact ownMonomialRefuter_zeroTwoThree_maximal other hcard))

/-! ## The first sufficient cell for the third coefficient

At a selection the sixteen monomials split into the tree's own -- positive, by
`kFourOwnMonomial_pos` -- and fifteen others of mixed sign.  Bounding each of
the fifteen below by minus its absolute value gives a cell: if the polynomial of
absolute selection values stays below twice the own monomial, the third
coefficient is positive.

The absolute selection value is division-free off the selection, where it is
just the mass. -/

/-- The absolute value of a selection value, written without an absolute value:
the boost on the selection and the mass off it. -/
noncomputable def absSelectionValue (mass weight : Fin 6 → ℝ)
    (tree : Finset (Fin 6)) (label : Fin 6) : ℝ :=
  if label ∈ tree then treeBoost mass weight label else mass label

/-- **The two readings agree.**  On the selection the value is the boost, which
is positive; off it the value is minus the mass, whose absolute value is the
mass. -/
theorem abs_selectionValue_eq (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (label : Fin 6) :
    |selectionValue point.mass point.weight tree label|
      = absSelectionValue point.mass point.weight tree label := by
  classical
  by_cases hmem : label ∈ tree
  · rw [selectionValue_eq_treeBoost_of_mem _ _ _ _ hmem]
    simp only [absSelectionValue, if_pos hmem]
    exact abs_of_pos (treeBoost_pos point label)
  · simp only [selectionValue, absSelectionValue, if_neg hmem]
    rw [abs_neg]
    exact abs_of_pos (point.mass_pos label)

theorem absSelectionValue_nonneg (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (label : Fin 6) :
    0 ≤ absSelectionValue point.mass point.weight tree label := by
  rw [← abs_selectionValue_eq point tree label]
  exact abs_nonneg _

/-- **The tree polynomial is sandwiched by its absolute reading.**  Each of the
sixteen monomials lies between minus and plus the product of the absolute
values, and the sum of sixteen such bounds is the statement. -/
theorem abs_kFourTreePolynomial_le (value : Fin 6 → ℝ) :
    |kFourTreePolynomial value| ≤ kFourTreePolynomial (fun label => |value label|) := by
  have habs : ∀ a b c : ℝ, |a * b * c| = |a| * |b| * |c| := by
    intro a b c; rw [abs_mul, abs_mul]
  have up : ∀ a b c : ℝ, a * b * c ≤ |a| * |b| * |c| := by
    intro a b c; rw [← habs]; exact le_abs_self _
  have dn : ∀ a b c : ℝ, -(|a| * |b| * |c|) ≤ a * b * c := by
    intro a b c; rw [← habs]; exact neg_abs_le _
  simp only [kFourTreePolynomial]
  rw [abs_le]
  constructor
  · linarith [dn (value 0) (value 1) (value 3), dn (value 0) (value 1) (value 4),
      dn (value 0) (value 1) (value 5), dn (value 0) (value 2) (value 3),
      dn (value 0) (value 2) (value 4), dn (value 0) (value 2) (value 5),
      dn (value 0) (value 3) (value 5), dn (value 0) (value 4) (value 5),
      dn (value 1) (value 2) (value 3), dn (value 1) (value 2) (value 4),
      dn (value 1) (value 2) (value 5), dn (value 1) (value 3) (value 4),
      dn (value 1) (value 4) (value 5), dn (value 2) (value 3) (value 4),
      dn (value 2) (value 3) (value 5), dn (value 3) (value 4) (value 5)]
  · linarith [up (value 0) (value 1) (value 3), up (value 0) (value 1) (value 4),
      up (value 0) (value 1) (value 5), up (value 0) (value 2) (value 3),
      up (value 0) (value 2) (value 4), up (value 0) (value 2) (value 5),
      up (value 0) (value 3) (value 5), up (value 0) (value 4) (value 5),
      up (value 1) (value 2) (value 3), up (value 1) (value 2) (value 4),
      up (value 1) (value 2) (value 5), up (value 1) (value 3) (value 4),
      up (value 1) (value 4) (value 5), up (value 2) (value 3) (value 4),
      up (value 2) (value 3) (value 5), up (value 3) (value 4) (value 5)]

end Gtz
