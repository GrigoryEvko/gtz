import Gtz.Wave.A1NeedleCollapse
import Gtz.Ties.SplitClassTieFamily
import Gtz.Ties.NonUniformLeverageTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Every landed `(6,3)` tie is line-degenerate

`Gtz.not_heavyNeedleResidual_iff_exists_lineFreeOffConicTie` pins the only
counterexample shape for the A1 registry axiom: one line-free off-conic `(6,3)`
tie.  This module asks whether the ties the tree already carries have that
shape.  They do not, and the reason is the same in every case.

A repeated atom kills a bracket, so it kills line-freeness outright.  The two
landed `(6,3)` tie families both repeat an atom:

- `Gtz.splitClassDesign` gives every atom the corank-one atom of its class.  At
  size six and rank three there are four classes, so two labels share a class
  and carry EQUAL atoms.  This covers the whole family behind
  `Gtz.exists_isTie_six_three`, at every weight vector and every class map.
- `Gtz.nonUniformLeverageTieDesign` has its three light atoms literally equal.

So no landed `(6,3)` tie refutes the axiom, and none of them even enters the
antecedent region.  A counterexample must carry six pairwise distinct atoms in
general position, and the tree has never exhibited one.

The reading is a warning, not a proof of vacuity.  A line-degenerate tie family
says nothing about the line-free stratum, and
`Gtz.heavyNeedleResidual_iff_stressFreeStratumIsTieFree` shows that deciding
emptiness there is the class statement itself.
-/

namespace Gtz

open Matrix Finset

/-! ## A repeated atom kills line-freeness -/

/-- Two distinct labels of a six-element index set leave a third label that
differs from each.  The third slot is placed between them, so the bracket that
follows has its outer slots equal. -/
theorem exists_thirdLabel_off_pair : ∀ firstLabel secondLabel : Fin 6,
    firstLabel ≠ secondLabel →
      ∃ thirdLabel : Fin 6, firstLabel ≠ thirdLabel ∧ thirdLabel ≠ secondLabel := by
  decide

/-- **A repeated atom is a line-degeneracy.**  Two labels with equal atoms sit
on a bracket that vanishes at every third label, and the empty line family
forbids a vanishing bracket. -/
theorem not_hasLinePattern_lineFree_of_atom_eq (design : WeightedDesign 6 3)
    {firstLabel secondLabel : Fin 6} (hdistinct : firstLabel ≠ secondLabel)
    (hatomEq : design.atom firstLabel = design.atom secondLabel) :
    ¬ HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro hlineFree
  obtain ⟨thirdLabel, hthirdFirst, hthirdSecond⟩ :=
    exists_thirdLabel_off_pair firstLabel secondLabel hdistinct
  refine atomBracket_ne_zero_of_lineFree design hlineFree hthirdFirst hdistinct
    hthirdSecond ?_
  rw [atomBracket, hatomEq]
  exact tripleBracket_eq_zero_of_repeatMid (design.atom secondLabel) (design.atom thirdLabel)

/-- **A line-free design has six distinct atoms.**  The counterexample shape of
the registry axiom is therefore an injective atom map. -/
theorem atom_injective_of_lineFree (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    Function.Injective design.atom := by
  intro firstLabel secondLabel hatomEq
  by_contra hdistinct
  exact not_hasLinePattern_lineFree_of_atom_eq design hdistinct hatomEq hlineFree

/-! ## The split-class family -/

/-- **Six labels do not fit in four classes.**  Pigeonhole on the class map. -/
theorem exists_sameClass_pair (classOf : Fin 6 → Fin 4) :
    ∃ firstLabel secondLabel : Fin 6,
      firstLabel ≠ secondLabel ∧ classOf firstLabel = classOf secondLabel :=
  Fintype.exists_ne_map_eq_of_card_lt classOf (by simp)

/-- **EVERY split-class `(6,3)` tie is line-degenerate.**  The class map lands in
four classes and the atoms are constant on a class, so two of the six atoms are
equal.  This holds at every weight vector and every class map, so it covers the
whole family that `Gtz.exists_isTie_six_three` produces. -/
theorem not_lineFree_splitClassDesign_six (classOf : Fin 6 → Fin 4) (weight : Fin 6 → ℝ)
    (hrank : 1 ≤ 3) (hsurjective : Function.Surjective classOf)
    (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1) :
    ¬ HasLinePattern (splitClassDesign classOf weight hrank hsurjective hpos hsum)
        (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  obtain ⟨firstLabel, secondLabel, hdistinct, hsameClass⟩ := exists_sameClass_pair classOf
  refine not_hasLinePattern_lineFree_of_atom_eq _ hdistinct ?_
  exact splitClassAtom_eq_of_sameClass hsameClass

/-! ## The non-uniform leverage fixture -/

/-- **The named `(6,3)` tie is line-degenerate.**  Its three light atoms are
literally equal. -/
theorem not_lineFree_nonUniformLeverageTieDesign :
    ¬ HasLinePattern nonUniformLeverageTieDesign
        (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  not_hasLinePattern_lineFree_of_atom_eq nonUniformLeverageTieDesign (by decide)
    nonUniformLeverageTieDesign_light_atoms_eq.1

/-- **The named `(6,3)` tie is also on a conic.**  A repeated atom leaves the
six Veronese rows dependent, so the design carries a nonzero stress. -/
theorem not_isStressFree_nonUniformLeverageTieDesign :
    ¬ IsStressFreeDesign nonUniformLeverageTieDesign := by
  intro hstressFree
  have hstressNe : (![0, 0, 0, 1, -1, 0] : Fin 6 → ℝ) ≠ 0 := by
    intro hzero
    have hread : (1 : ℝ) = 0 := by simpa using congrFun hzero 3
    norm_num at hread
  refine hstressNe (hstressFree _ ?_)
  have hatomEq : nonUniformLeverageTieDesign.atom 3 = nonUniformLeverageTieDesign.atom 4 :=
    nonUniformLeverageTieDesign_light_atoms_eq.1
  rw [Fin.sum_univ_six]
  simp [hatomEq]

/-! ## The split-tetrahedron family -/

/-- **THE SPLIT-TETRAHEDRON TIE IS LINE-DEGENERATE.**  Its six atoms carry the
four tetrahedron directions through `![0, 1, 2, 2, 3, 3]`, so labels two and
three read the same direction. -/
theorem not_lineFree_splitTetraDesign (splitA splitB : ℝ) (hAPos : 0 < splitA)
    (hALt : splitA < 1 / 4) (hBPos : 0 < splitB) (hBLt : splitB < 1 / 4) :
    ¬ HasLinePattern (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt)
        (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  not_hasLinePattern_lineFree_of_atom_eq _ (by decide : (2 : Fin 6) ≠ 3) rfl

/-! ## The route the census names -/

/-- **THE FOUR-DIRECTION ROUTE TO A1.**  Every `(6,3)` tie in the tree repeats an
atom, and the exhaustive census finds no tie anywhere with six pairwise distinct
directions.  If that regularity is a theorem, the registry axiom follows at once:
a repeated atom is not line-free, so no tie meets the stratum.

This states the route and nothing more.  The hypothesis is NOT proved here, and
the evidence for it is a census plus a directed search, not a proof. -/
theorem heavyNeedleResidual_of_tie_repeats_an_atom
    (hrepeat : ∀ design : WeightedDesign 6 3, IsTie design →
      ∃ firstLabel secondLabel : Fin 6,
        firstLabel ≠ secondLabel ∧ design.atom firstLabel = design.atom secondLabel) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual := by
  refine heavyNeedleResidual_of_pinnedStratumTieFree ?_
  intro design hlineFree _hoffConic htie
  obtain ⟨firstLabel, secondLabel, hdistinct, hatomEq⟩ := hrepeat design htie
  exact not_hasLinePattern_lineFree_of_atom_eq design hdistinct hatomEq hlineFree

/-! ## The reading for the registry axiom -/

/-- **No landed `(6,3)` tie enters the antecedent region.**  A design with two
equal atoms is neither line-free nor stress-free, so it cannot be the
counterexample that
`Gtz.not_heavyNeedleResidual_iff_exists_lineFreeOffConicTie` asks for. -/
theorem not_counterexample_of_atom_eq (design : WeightedDesign 6 3)
    {firstLabel secondLabel : Fin 6} (hdistinct : firstLabel ≠ secondLabel)
    (hatomEq : design.atom firstLabel = design.atom secondLabel) :
    ¬ (HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) ∧
        HasNoCommonQuadric design.atom ∧ IsTie design) := by
  rintro ⟨hlineFree, _, _⟩
  exact not_hasLinePattern_lineFree_of_atom_eq design hdistinct hatomEq hlineFree

end Gtz
