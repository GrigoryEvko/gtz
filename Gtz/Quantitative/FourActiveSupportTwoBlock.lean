import Gtz.Quantitative.StrongStationarityIndexFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The four-active case always has an active block of tight support exactly two

At a `(6,3)` crux with exactly four active blocks the campaign's handed case split is a
DISJUNCTION: a selected tight direction has support two, OR it has support three and its
complementary triple is active with a uniform row and multiplier one half.  This file
records that the LEFT disjunct is available unconditionally and for EVERY least
eigenvector family, so the split is avoidable.

Both ingredients are landed and neither is new here:

* `Gtz.SixThreeCrux.not_forall_exists_fullSupport_activeEigenvector_of_card_eq_four`
  -- at four active blocks one cannot choose a full-support unit least eigenvector at
  every active block;
* `Gtz.SixThreeCrux.two_le_card_totalTightSupport`
  -- every card-three least eigenvector at a crux has at least two nonzero coordinates,
  at ACTIVE and INACTIVE blocks alike.

The support of a tight vector lies inside its own block, which has three atoms, so the
two bounds pinch: at four active blocks some active block has support EXACTLY two.  The
statement quantifies over the eigenvector family, so it survives a block whose least
eigenvalue is multiple -- no choice of eigenvectors escapes it.

WHAT THIS DOES NOT DO.  It does not attach the row-span property of
`Gtz.SixThreeCrux.exists_argmax_supportTwo_coordinateSingles_mem_finiteRowSpan` to the
block it produces; that theorem selects its block by the vanishing-submodule condition
and the two blocks are different in general.  A proof that needs both must still work
for the row-span block.

VACUITY.  Every statement here is quantified over `Gtz.SixThreeCrux`, which is
conjecturally empty, so all of it is VACUOUSLY TRUE IF GTZ HOLDS.
-/

namespace Gtz

open Matrix

/-- **THE FOUR-ACTIVE SUPPORT-TWO BLOCK, FOR EVERY EIGENVECTOR FAMILY.**  At a `(6,3)`
crux with exactly four active blocks, ANY family of unit least eigenvectors of the
card-three blocks has an ACTIVE block on which its support is exactly two atoms.

Quantifying over the family rather than producing one is what makes this
multiplicity-robust: at a block whose least eigenvalue is multiple, no choice of
eigenvector inside the eigenspace avoids the conclusion. -/
theorem SixThreeCrux.exists_argmaxBlock_totalTightSupport_eq_two_of_card_eq_four
    (crux : SixThreeCrux)
    (hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected) :
    ∃ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      (totalTightSupport tightVec block).card = 2 := by
  classical
  by_contra hnoSupportTwo
  refine crux.not_forall_exists_fullSupport_activeEigenvector_of_card_eq_four hfour ?_
  intro selected hmember
  have hcard : selected.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
  refine ⟨hcard, tightVec selected, hunit selected hcard, hEigen selected hcard, ?_⟩
  have hlower : 2 ≤ (totalTightSupport tightVec selected).card :=
    crux.two_le_card_totalTightSupport tightVec hunit hEigen selected hcard
  have hupper : (totalTightSupport tightVec selected).card ≤ 3 := by
    have hsubsetCard := Finset.card_le_card (totalTightSupport_subset tightVec hcard)
    omega
  have hnotTwo : (totalTightSupport tightVec selected).card ≠ 2 := fun hexactlyTwo =>
    hnoSupportTwo ⟨selected, hmember, hexactlyTwo⟩
  have hexactlyThree : (totalTightSupport tightVec selected).card = 3 := by omega
  rw [card_totalTightSupport tightVec hcard] at hexactlyThree
  have hfullFilter :
      (Finset.univ.filter fun blockIndex => tightVec selected blockIndex ≠ 0)
        = (Finset.univ : Finset (Fin 3)) :=
    Finset.eq_univ_of_card _ (by simpa using hexactlyThree)
  intro blockIndex
  have hmemFilter :
      blockIndex ∈ (Finset.univ.filter fun index => tightVec selected index ≠ 0) := by
    rw [hfullFilter]
    exact Finset.mem_univ blockIndex
  exact (Finset.mem_filter.mp hmemFilter).2

/-- **THE PRODUCED FORM.**  A `(6,3)` crux with exactly four active blocks carries a unit
least eigenvector family together with an ACTIVE block on which that family's support is
exactly two atoms.  The family comes from the landed
`Gtz.exists_unit_chartBlockEigenvectorFamily`, which needs no hypothesis at all, so the
LEFT disjunct of the four-active fork is reachable without any case analysis. -/
theorem SixThreeCrux.exists_tightVec_argmaxBlock_totalTightSupport_eq_two_of_card_eq_four
    (crux : SixThreeCrux)
    (hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ∃ (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
      (block : Finset (Fin 6)),
      (∀ selected : Finset (Fin 6), selected.card = 3 →
        tightVec selected ⬝ᵥ tightVec selected = 1)
      ∧ (∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        (chartPointGap (chartPointOfDesign crux.design)).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
          = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
      ∧ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
      ∧ (totalTightSupport tightVec block).card = 2 := by
  classical
  obtain ⟨tightVec, hunit, hEigen⟩ :=
    exists_unit_chartBlockEigenvectorFamily (chartPointOfDesign crux.design)
  obtain ⟨block, hblock, hsupport⟩ :=
    crux.exists_argmaxBlock_totalTightSupport_eq_two_of_card_eq_four hfour tightVec hunit hEigen
  exact ⟨tightVec, block, hunit, hEigen, hblock, hsupport⟩

/-- **THE CONTRAPOSITIVE, AS A FLOOR.**  If some unit least eigenvector family has
support three at every active block, the active family has at least five members.  This
is the four-active statement above read as an index bound, and it is the shape a descent
consumes. -/
theorem SixThreeCrux.five_le_card_chartArgmaxFamily_of_forall_totalTightSupport_ne_two
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hEigen : ∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
      (chartPointGap (chartPointOfDesign crux.design)).submatrix
          (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard) *ᵥ tightVec selected
        = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
            (chartPointOfDesign crux.design).weight) :
            (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
    (hnoSupportTwo : ∀ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      (totalTightSupport tightVec block).card ≠ 2) :
    5 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  classical
  have hfloor := crux.four_le_card_chartArgmaxFamily_strong
  rcases Nat.lt_or_ge (chartArgmaxFamily (chartPointOfDesign crux.design)).card 5 with
    hsmall | hlarge
  · have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by omega
    obtain ⟨block, hblock, hsupport⟩ :=
      crux.exists_argmaxBlock_totalTightSupport_eq_two_of_card_eq_four hfour tightVec hunit hEigen
    exact absurd hsupport (hnoSupportTwo block hblock)
  · exact hlarge

end Gtz
