import Gtz.Design.LineBranchUnitAxisNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix

/-- Triple brackets scale by the determinant under a common congruence map. -/
theorem tripleBracket_transpose_mulVec (P : Matrix (Fin 3) (Fin 3) ℝ)
    (first second third : Fin 3 → ℝ) :
    tripleBracket (Pᵀ *ᵥ first) (Pᵀ *ᵥ second) (Pᵀ *ᵥ third)
      = tripleBracket first second third * P.det := by
  rw [tripleBracket, tripleBracket, ← Matrix.det_mul]
  congr 1
  ext row col
  fin_cases row <;> simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- Line-freeness survives the square-root-free normalization, pointwise on
every ordered triple of distinct labels. -/
theorem unitAxisAtomBracket_ne_zero_of_lineFree
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    tripleBracket
        ((unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom first)
        ((unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom second)
        ((unitAxisBaseNormalizer design)ᵀ *ᵥ design.atom third) ≠ 0 := by
  have horiginal :
      tripleBracket (design.atom first) (design.atom second) (design.atom third) ≠ 0 :=
    atomBracket_ne_zero_of_lineFree design hlineFree hfirstSecond hfirstThird
      hsecondThird
  rw [tripleBracket_transpose_mulVec]
  exact mul_ne_zero horiginal
    (isUnit_iff_ne_zero.mp (unitAxisBaseNormalizer_det_isUnit design hlineFree))

/-- The first nine of the nineteen normalized line-free inequations: every
coordinate of every free atom is nonzero. -/
theorem unitAxisFreeAtom_coordinate_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (freeIndex coordinate : Fin 3) :
    unitAxisFreeAtom design freeIndex coordinate ≠ 0 := by
  fin_cases coordinate
  · have h := unitAxisAtomBracket_ne_zero_of_lineFree design hlineFree
        (first := 1) (second := 2) (third := freeThreeLabel freeIndex)
        (by decide) (by fin_cases freeIndex <;> decide)
        (by fin_cases freeIndex <;> decide)
    have hone := unitAxisBaseNormalizer_baseAtom design hlineFree 1
    have htwo := unitAxisBaseNormalizer_baseAtom design hlineFree 2
    simp [baseThreeLabel] at hone htwo
    rw [hone, htwo] at h
    change tripleBracket (Pi.single 1 1) (Pi.single 2 1)
      (unitAxisFreeAtom design freeIndex) ≠ 0 at h
    simpa [Pi.single_apply, tripleBracket, Matrix.det_fin_three] using h
  · have h := unitAxisAtomBracket_ne_zero_of_lineFree design hlineFree
        (first := 0) (second := 2) (third := freeThreeLabel freeIndex)
        (by decide) (by fin_cases freeIndex <;> decide)
        (by fin_cases freeIndex <;> decide)
    have hzero := unitAxisBaseNormalizer_baseAtom design hlineFree 0
    have htwo := unitAxisBaseNormalizer_baseAtom design hlineFree 2
    simp [baseThreeLabel] at hzero htwo
    rw [hzero, htwo] at h
    change tripleBracket (Pi.single 0 1) (Pi.single 2 1)
      (unitAxisFreeAtom design freeIndex) ≠ 0 at h
    simpa [Pi.single_apply, tripleBracket, Matrix.det_fin_three] using h
  · have h := unitAxisAtomBracket_ne_zero_of_lineFree design hlineFree
        (first := 0) (second := 1) (third := freeThreeLabel freeIndex)
        (by decide) (by fin_cases freeIndex <;> decide)
        (by fin_cases freeIndex <;> decide)
    have hzero := unitAxisBaseNormalizer_baseAtom design hlineFree 0
    have hone := unitAxisBaseNormalizer_baseAtom design hlineFree 1
    simp [baseThreeLabel] at hzero hone
    rw [hzero, hone] at h
    change tripleBracket (Pi.single 0 1) (Pi.single 1 1)
      (unitAxisFreeAtom design freeIndex) ≠ 0 at h
    simpa [Pi.single_apply, tripleBracket, Matrix.det_fin_three] using h

/-- The next nine normalized line-free inequations: every coordinate of every
cross product of two distinct free atoms is nonzero. -/
theorem unitAxisFreePair_bracketNormal_coordinate_ne_zero
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {firstFree secondFree : Fin 3} (hdistinct : firstFree ≠ secondFree)
    (coordinate : Fin 3) :
    bracketNormal (unitAxisFreeAtom design firstFree)
        (unitAxisFreeAtom design secondFree) coordinate ≠ 0 := by
  have hfreeDistinct : freeThreeLabel firstFree ≠ freeThreeLabel secondFree :=
    fun heq => hdistinct (freeThreeLabel_injective heq)
  fin_cases coordinate
  · have h := unitAxisAtomBracket_ne_zero_of_lineFree design hlineFree
        (first := 0) (second := freeThreeLabel firstFree)
        (third := freeThreeLabel secondFree)
        (by fin_cases firstFree <;> decide)
        (by fin_cases secondFree <;> decide) hfreeDistinct
    have hzero := unitAxisBaseNormalizer_baseAtom design hlineFree 0
    simp [baseThreeLabel] at hzero
    rw [hzero] at h
    change tripleBracket (Pi.single 0 1) (unitAxisFreeAtom design firstFree)
      (unitAxisFreeAtom design secondFree) ≠ 0 at h
    simp [tripleBracket, Matrix.det_fin_three, bracketNormal] at h ⊢
    intro hzero
    apply h
    linear_combination hzero
  · have h := unitAxisAtomBracket_ne_zero_of_lineFree design hlineFree
        (first := 1) (second := freeThreeLabel firstFree)
        (third := freeThreeLabel secondFree)
        (by fin_cases firstFree <;> decide)
        (by fin_cases secondFree <;> decide) hfreeDistinct
    have hone := unitAxisBaseNormalizer_baseAtom design hlineFree 1
    simp [baseThreeLabel] at hone
    rw [hone] at h
    change tripleBracket (Pi.single 1 1) (unitAxisFreeAtom design firstFree)
      (unitAxisFreeAtom design secondFree) ≠ 0 at h
    simp [tripleBracket, Matrix.det_fin_three, bracketNormal] at h ⊢
    intro hzero
    apply h
    linear_combination hzero
  · have h := unitAxisAtomBracket_ne_zero_of_lineFree design hlineFree
        (first := 2) (second := freeThreeLabel firstFree)
        (third := freeThreeLabel secondFree)
        (by fin_cases firstFree <;> decide)
        (by fin_cases secondFree <;> decide) hfreeDistinct
    have htwo := unitAxisBaseNormalizer_baseAtom design hlineFree 2
    simp [baseThreeLabel] at htwo
    rw [htwo] at h
    change tripleBracket (Pi.single 2 1) (unitAxisFreeAtom design firstFree)
      (unitAxisFreeAtom design secondFree) ≠ 0 at h
    simpa [Pi.single_apply, tripleBracket, Matrix.det_fin_three, bracketNormal] using h

/-- The normalized line-free package: nine nonzero free coordinates, nine
nonzero free-pair cross coordinates, and the nonzero free-frame determinant. -/
theorem unitAxis_lineFree_nineteen_inequations
    (design : WeightedDesign 6 3)
    (hlineFree :
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (∀ freeIndex coordinate,
        unitAxisFreeAtom design freeIndex coordinate ≠ 0)
      ∧ (∀ firstFree secondFree, firstFree ≠ secondFree →
          ∀ coordinate,
            bracketNormal (unitAxisFreeAtom design firstFree)
                (unitAxisFreeAtom design secondFree) coordinate ≠ 0)
      ∧ (unitAxisFreeFrame design).det ≠ 0 := by
  exact ⟨unitAxisFreeAtom_coordinate_ne_zero design hlineFree,
    fun _ _ hne => unitAxisFreePair_bracketNormal_coordinate_ne_zero design hlineFree hne,
    unitAxisFreeFrame_det_ne_zero design hlineFree⟩

end Gtz
