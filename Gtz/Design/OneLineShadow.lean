import Gtz.Design.InPlaneRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz
open Matrix

/-! # Shadow collisions on the one-line stratum

At the line normal the three LINE atoms are their own shadows and are pairwise
non-parallel, so they already occupy three distinct shadow directions.  When the
rank-two hinge `Gtz.rankTwoFourDirectionHinge_holds` does NOT apply -- that is,
when no four atoms carry pairwise non-parallel shadows -- every FREE shadow must
land on one of those three directions or vanish.  This file shows the resulting
bookkeeping is FORCED, and forced by the pattern alone:

* two free atoms never share a line plane (`oneLine_freeAtoms_not_shareLinePlane`);
* consequently the free-to-line assignment is INJECTIVE, hence bijective on the
  one-line stratum, and no free shadow vanishes
  (`oneLine_shadowColumn_injective_and_nonzero`).

So the hinge's negation collapses to a single rigid shape: three free atoms
sitting one per line plane, each with a nonzero shadow.  One plane lemma does
all the killing. -/

/-- **Three vectors drawn from one plane have vanishing bracket.**  Multilinearity
alone: every monomial of the expanded determinant repeats a spanning direction. -/
theorem tripleBracket_eq_zero_of_spannedByPair
    (dirFirst dirSecond leftVec midVec rightVec : Fin 3 → ℝ)
    (hleft : ∃ alongFirst alongSecond : ℝ,
      leftVec = alongFirst • dirFirst + alongSecond • dirSecond)
    (hmid : ∃ alongFirst alongSecond : ℝ,
      midVec = alongFirst • dirFirst + alongSecond • dirSecond)
    (hright : ∃ alongFirst alongSecond : ℝ,
      rightVec = alongFirst • dirFirst + alongSecond • dirSecond) :
    tripleBracket leftVec midVec rightVec = 0 := by
  obtain ⟨leftAlong, leftAcross, hleftEq⟩ := hleft
  obtain ⟨midAlong, midAcross, hmidEq⟩ := hmid
  obtain ⟨rightAlong, rightAcross, hrightEq⟩ := hright
  subst hleftEq; subst hmidEq; subst hrightEq
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A vector spans its own plane with any partner. -/
theorem spannedByPair_self (dirFirst dirSecond : Fin 3 → ℝ) :
    ∃ alongFirst alongSecond : ℝ,
      dirFirst = alongFirst • dirFirst + alongSecond • dirSecond :=
  ⟨1, 0, by simp⟩

/-- **The shadow bridge.**  An atom whose shadow at a normal is a multiple of a
line atom lies in the plane that line atom spans with the normal. -/
theorem spannedByPair_of_shadow_eq_smul
    (atomVec lineVec normalVec : Fin 3 → ℝ) (ratio : ℝ)
    (hshadow : atomVec - (atomVec ⬝ᵥ normalVec) • normalVec = ratio • lineVec) :
    ∃ alongLine alongNormal : ℝ,
      atomVec = alongLine • lineVec + alongNormal • normalVec := by
  refine ⟨ratio, atomVec ⬝ᵥ normalVec, ?_⟩
  rw [← hshadow]
  abel

/-- **THE SHADOW-COLLISION KILL.**  On the one-line stratum no two distinct FREE
atoms lie in the plane spanned by a single LINE atom and the normal: that plane
would carry three atoms, so a bracket outside the pattern's only dependent
triple would vanish. -/
theorem oneLine_freeAtoms_not_shareLinePlane (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (normalVec : Fin 3 → ℝ) (lineLabel freeFirst freeSecond : Fin 6)
    (hlineMem : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hfirstMem : freeFirst ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hsecondMem : freeSecond ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hdistinct : freeFirst ≠ freeSecond)
    (hfirstInPlane : ∃ alongLine alongNormal : ℝ,
      design.atom freeFirst = alongLine • design.atom lineLabel + alongNormal • normalVec)
    (hsecondInPlane : ∃ alongLine alongNormal : ℝ,
      design.atom freeSecond = alongLine • design.atom lineLabel + alongNormal • normalVec) :
    False := by
  have hlineFirst : lineLabel ≠ freeFirst := by
    fin_cases hlineMem <;> fin_cases hfirstMem <;> decide
  have hlineSecond : lineLabel ≠ freeSecond := by
    fin_cases hlineMem <;> fin_cases hsecondMem <;> decide
  have hbracket : atomBracket design lineLabel freeFirst freeSecond = 0 :=
    tripleBracket_eq_zero_of_spannedByPair (design.atom lineLabel) normalVec _ _ _
      (spannedByPair_self _ _) hfirstInPlane hsecondInPlane
  have hinPattern :=
    (hpattern lineLabel freeFirst freeSecond hlineFirst hlineSecond hdistinct).mp hbracket
  simp only [lineFamilyPattern, List.mem_singleton, exists_eq_left] at hinPattern
  have hfreeInLine : freeFirst ∈ [(0 : Fin 6), 1, 2] := hinPattern.2.1
  fin_cases hfirstMem <;> simp at hfreeInLine

/-- Every free label has a distinct free partner. -/
theorem oneLine_exists_freePartner (freeLabel : Fin 6)
    (hmem : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    ∃ partner ∈ ({3, 4, 5} : Finset (Fin 6)), partner ≠ freeLabel := by
  fin_cases hmem
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩

/-- **THE CASE-(ii) NORMAL FORM.**  Suppose every free shadow at the line normal
is a multiple of some line atom -- exactly what the FAILURE of the rank-two
four-direction hinge leaves available on this stratum.  Then the assignment of
free labels to line labels is INJECTIVE, and no free shadow vanishes.  Since
both label sets have three elements the assignment is a bijection: the stratum's
hinge-free shape is three free atoms, one per line plane, each with a nonzero
shadow. -/
theorem oneLine_shadowColumn_injective_and_nonzero (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (normalVec : Fin 3 → ℝ) (columnOf : Fin 6 → Fin 6) (ratioOf : Fin 6 → ℝ)
    (hcolumnMem : ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      columnOf freeLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hshadow : ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      design.atom freeLabel - (design.atom freeLabel ⬝ᵥ normalVec) • normalVec
        = ratioOf freeLabel • design.atom (columnOf freeLabel)) :
    (∀ freeFirst ∈ ({3, 4, 5} : Finset (Fin 6)),
        ∀ freeSecond ∈ ({3, 4, 5} : Finset (Fin 6)),
        freeFirst ≠ freeSecond → columnOf freeFirst ≠ columnOf freeSecond)
      ∧ (∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)), ratioOf freeLabel ≠ 0) := by
  constructor
  · intro freeFirst hfirstMem freeSecond hsecondMem hdistinct hcolumnEq
    refine oneLine_freeAtoms_not_shareLinePlane design hpattern normalVec
      (columnOf freeFirst) freeFirst freeSecond (hcolumnMem freeFirst hfirstMem)
      hfirstMem hsecondMem hdistinct
      (spannedByPair_of_shadow_eq_smul _ _ _ _ (hshadow freeFirst hfirstMem)) ?_
    rw [hcolumnEq]
    exact spannedByPair_of_shadow_eq_smul _ _ _ _ (hshadow freeSecond hsecondMem)
  · intro freeLabel hmem hratioZero
    obtain ⟨partner, hpartnerMem, hpartnerNe⟩ := oneLine_exists_freePartner freeLabel hmem
    have hflat : design.atom freeLabel
        = (design.atom freeLabel ⬝ᵥ normalVec) • normalVec := by
      have hraw := hshadow freeLabel hmem
      rw [hratioZero, zero_smul, sub_eq_zero] at hraw
      exact hraw
    exact oneLine_freeAtoms_not_shareLinePlane design hpattern normalVec
      (columnOf partner) freeLabel partner (hcolumnMem partner hpartnerMem)
      hmem hpartnerMem (Ne.symm hpartnerNe)
      ⟨0, design.atom freeLabel ⬝ᵥ normalVec, by rw [zero_smul, zero_add]; exact hflat⟩
      (spannedByPair_of_shadow_eq_smul _ _ _ _ (hshadow partner hpartnerMem))

/-! ## Toward the rigid family: each column over-covers its own in-plane mass

In the normal form above the six atoms split into three COLUMNS, a line atom and
a free atom sharing one plane through the normal.  The column's in-plane mass is
the weighted average of the two squared in-plane lengths, and because a column
never carries the whole weight budget that average is STRICTLY below the larger
of the two.  So the longer atom of each column strictly over-covers its column,
which is the in-plane half of any transversal certificate on the rigid family. -/

/-- **A sub-unit weighted average is strictly below the larger value.**  The
positivity hypothesis is load-bearing: at two zero values the average equals the
maximum. -/
theorem weightedPair_lt_max_of_massLtOne
    (weightFirst weightSecond valueFirst valueSecond : ℝ)
    (hweightFirstNonneg : 0 ≤ weightFirst) (hweightSecondNonneg : 0 ≤ weightSecond)
    (hmassLtOne : weightFirst + weightSecond < 1)
    (_hvalueFirstNonneg : 0 ≤ valueFirst) (_hvalueSecondNonneg : 0 ≤ valueSecond)
    (hmaxPos : 0 < max valueFirst valueSecond) :
    weightFirst * valueFirst + weightSecond * valueSecond
      < max valueFirst valueSecond := by
  have hfirstLe : valueFirst ≤ max valueFirst valueSecond := le_max_left _ _
  have hsecondLe : valueSecond ≤ max valueFirst valueSecond := le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_left hfirstLe hweightFirstNonneg,
    mul_le_mul_of_nonneg_left hsecondLe hweightSecondNonneg]

/-- **THE COLUMN SURPLUS.**  In a column -- a line atom and a free atom sharing
one plane through the normal -- the weighted in-plane mass is STRICTLY below the
longer atom's squared in-plane length, so that atom alone strictly over-covers
its own column.  The weight budget is spent through the shipped
`Gtz.weightPair_lt_one`; positivity comes free from the LINE atom's heaviness.
Summed over the three columns of the normal form this is the in-plane half of a
transversal certificate on the rigid family. -/
theorem oneLine_columnMass_lt_max {size rank : ℕ} (design : WeightedDesign size rank)
    {lineLabel freeLabel witnessLabel : Fin size} (hdistinct : lineLabel ≠ freeLabel)
    (hwitnessLine : witnessLabel ≠ lineLabel) (hwitnessFree : witnessLabel ≠ freeLabel)
    (lineLengthSq freeLengthSq : ℝ)
    (hlinePos : 0 < lineLengthSq) (hfreeNonneg : 0 ≤ freeLengthSq) :
    design.weight lineLabel * lineLengthSq + design.weight freeLabel * freeLengthSq
      < max lineLengthSq freeLengthSq :=
  weightedPair_lt_max_of_massLtOne _ _ _ _ (design.weight_pos lineLabel).le
    (design.weight_pos freeLabel).le
    (weightPair_lt_one design hdistinct hwitnessLine hwitnessFree)
    hlinePos.le hfreeNonneg (lt_of_lt_of_le hlinePos (le_max_left _ _))

end Gtz
