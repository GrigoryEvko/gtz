/-
# Four atoms on one plane force a stress

The size-six lever in its exact load-bearing form.  Rank-one atoms of vectors
lying in a fixed plane through the origin live in the symmetric square of that
plane, a THREE-dimensional space, so FOUR such atoms are linearly dependent and
any dependence of atom matrices is a stress.  At size five a tight plane can
only ever be asked to carry three atoms, and three rank-ones in a
three-dimensional space are generically independent — this is why the lemma has
no five-point analogue.

Contents:
* `exists_stress_of_four_onPlane_atoms` — four distinct atoms orthogonal to a
  unit axis carry a nonzero stress supported on them (any size, rank three);
* `exists_stress_of_four_onPlane_atoms_of_ne_zero` — the same for a merely
  nonzero axis;
* `planarLabels_card_le_three_of_stressFree` — at a stress-free `(6,3)` design
  every plane through the origin contains at most THREE of the six atoms.

The last statement is the transversality dividend for the tight-drop lane: a
tight plane of a stress-free design cannot swallow four atoms, so at least two
atoms sit strictly off every tight plane.

Calibration (exact rationals, recorded in the lane report): at the `(5,3)`
diamond the four budget-equality pairs have their three outside atoms NOT
coplanar (incidence determinants `1, -1, 1, 1`), so the equality locus does not
manufacture the hypothesis of this lemma by itself; what budget equality does
produce is the inverse-gap quadric conditions, mechanized in the sibling file
`PairGapQuadricLocus.lean`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Design.TwoPoleStratum
import Gtz.Design.TightAxisPairBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## Part 1: an orthonormal frame under a unit axis (textual base:
`/tmp/gtz-p16/tightaxis/TightAxisPairLane.lean`, verified against the tree) -/

/-! ## Part 2: four rank-one atoms of a plane are dependent -/

/-- **THE SIZE-SIX LEVER.**  Four distinct atoms of a rank-three design that lie
on the plane orthogonal to a unit axis support a nonzero stress: their four
rank-one atom matrices sit inside the symmetric square of the plane, which is
three-dimensional. -/
theorem exists_stress_of_four_onPlane_atoms
    (design : WeightedDesign size 3) {axis : Fin 3 → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    {labelOne labelTwo labelThree labelFour : Fin size}
    (hneOneTwo : labelOne ≠ labelTwo) (hneOneThree : labelOne ≠ labelThree)
    (hneOneFour : labelOne ≠ labelFour) (hneTwoThree : labelTwo ≠ labelThree)
    (hneTwoFour : labelTwo ≠ labelFour) (hneThreeFour : labelThree ≠ labelFour)
    (honPlaneOne : design.atom labelOne ⬝ᵥ axis = 0)
    (honPlaneTwo : design.atom labelTwo ⬝ᵥ axis = 0)
    (honPlaneThree : design.atom labelThree ⬝ᵥ axis = 0)
    (honPlaneFour : design.atom labelFour ⬝ᵥ axis = 0) :
    ∃ stress : Fin size → ℝ, stress ≠ 0
      ∧ (∀ c : Fin size, stress c ≠ 0 →
          c = labelOne ∨ c = labelTwo ∨ c = labelThree ∨ c = labelFour)
      ∧ ∑ c, stress c • atomMatrix (design.atom c) = 0 := by
  classical
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  set pickedLabel : Fin 4 → Fin size := ![labelOne, labelTwo, labelThree, labelFour]
    with hpickedDef
  set seedCoord : Fin 4 → ℝ := fun pick => design.atom (pickedLabel pick) ⬝ᵥ pOne
    with hseedCoordDef
  set probeCoord : Fin 4 → ℝ := fun pick => design.atom (pickedLabel pick) ⬝ᵥ pTwo
    with hprobeCoordDef
  set veroneseVec : Fin 4 → (Fin 3 → ℝ) := fun pick =>
    ![seedCoord pick ^ 2, seedCoord pick * probeCoord pick, probeCoord pick ^ 2]
    with hveroneseDef
  have hnotIndependent : ¬ LinearIndependent ℝ veroneseVec := by
    intro hindependent
    have hcardBound := hindependent.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_fin]
      at hcardBound
    omega
  obtain ⟨relCoeff, hrelSum, pivotIndex, hpivotNe⟩ :=
    Fintype.not_linearIndependent_iff.mp hnotIndependent
  have hcomponent : ∀ coord : Fin 3,
      ∑ pick : Fin 4, relCoeff pick * veroneseVec pick coord = 0 := by
    intro coord
    have hcoord := congrFun hrelSum coord
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcoord
  have hsumSq : ∑ pick : Fin 4, relCoeff pick * seedCoord pick ^ 2 = 0 := by
    have hval := hcomponent 0
    simpa [hveroneseDef] using hval
  have hsumCross : ∑ pick : Fin 4, relCoeff pick * (seedCoord pick * probeCoord pick)
      = 0 := by
    have hval := hcomponent 1
    simpa [hveroneseDef] using hval
  have hsumProbeSq : ∑ pick : Fin 4, relCoeff pick * probeCoord pick ^ 2 = 0 := by
    have hval := hcomponent 2
    simpa [hveroneseDef] using hval
  -- the stress: the relation coefficients at the four labels, zero elsewhere
  set stress : Fin size → ℝ := fun c =>
    if c = labelOne then relCoeff 0 else if c = labelTwo then relCoeff 1
      else if c = labelThree then relCoeff 2 else if c = labelFour then relCoeff 3
        else 0
    with hstressDef
  have hstressValues : stress labelOne = relCoeff 0 ∧ stress labelTwo = relCoeff 1
      ∧ stress labelThree = relCoeff 2 ∧ stress labelFour = relCoeff 3 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [hstressDef, hneOneTwo, hneOneThree, hneOneFour, hneTwoThree, hneTwoFour,
        hneThreeFour, hneOneTwo.symm, hneOneThree.symm, hneOneFour.symm,
        hneTwoThree.symm, hneTwoFour.symm, hneThreeFour.symm]
  -- planar expansion of each picked atom
  have hexpansion : ∀ pick : Fin 4, ∀ coord : Fin 3,
      design.atom (pickedLabel pick) coord
        = seedCoord pick * pOne coord + probeCoord pick * pTwo coord := by
    intro pick coord
    have honPlane : design.atom (pickedLabel pick) ⬝ᵥ axis = 0 := by
      fin_cases pick <;>
        simpa [hpickedDef] using
          (by first
            | exact honPlaneOne
            | exact honPlaneTwo
            | exact honPlaneThree
            | exact honPlaneFour :
              design.atom _ ⬝ᵥ axis = 0)
    have hresolve := orthonormalFrame_expansion hOneOne hTwoTwo hunit hOneTwo
      hOneAxis hTwoAxis (design.atom (pickedLabel pick))
    rw [honPlane, zero_smul, add_zero] at hresolve
    have hcoord := congrFun hresolve coord
    simpa [hseedCoordDef, hprobeCoordDef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      using hcoord
  -- the four-atom combination vanishes entrywise
  have hfourSum : ∑ pick : Fin 4, relCoeff pick • atomMatrix (design.atom (pickedLabel pick))
      = 0 := by
    ext rowIndex colIndex
    rw [Matrix.sum_apply, Matrix.zero_apply]
    have hterm : ∀ pick : Fin 4,
        (relCoeff pick • atomMatrix (design.atom (pickedLabel pick))) rowIndex colIndex
          = relCoeff pick
              * ((seedCoord pick * pOne rowIndex + probeCoord pick * pTwo rowIndex)
                * (seedCoord pick * pOne colIndex + probeCoord pick * pTwo colIndex)) := by
      intro pick
      rw [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul,
        hexpansion pick rowIndex, hexpansion pick colIndex]
    rw [Finset.sum_congr rfl fun pick _ => hterm pick]
    have hexpandAll : ∑ pick : Fin 4, relCoeff pick
          * ((seedCoord pick * pOne rowIndex + probeCoord pick * pTwo rowIndex)
            * (seedCoord pick * pOne colIndex + probeCoord pick * pTwo colIndex))
        = (pOne rowIndex * pOne colIndex)
              * (∑ pick : Fin 4, relCoeff pick * seedCoord pick ^ 2)
          + (pOne rowIndex * pTwo colIndex + pTwo rowIndex * pOne colIndex)
              * (∑ pick : Fin 4, relCoeff pick * (seedCoord pick * probeCoord pick))
          + (pTwo rowIndex * pTwo colIndex)
              * (∑ pick : Fin 4, relCoeff pick * probeCoord pick ^ 2) := by
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun pick _ => by ring
    rw [hexpandAll, hsumSq, hsumCross, hsumProbeSq]
    ring
  refine ⟨stress, ?_, ?_, ?_⟩
  · -- nonzero at the pivot label
    intro hstressZero
    have hpivotValue : stress (pickedLabel pivotIndex) = relCoeff pivotIndex := by
      fin_cases pivotIndex <;>
        simp only [hpickedDef, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.cons_val_three] <;>
        first
          | exact hstressValues.1
          | exact hstressValues.2.1
          | exact hstressValues.2.2.1
          | exact hstressValues.2.2.2
    rw [hstressZero] at hpivotValue
    exact hpivotNe (by simpa using hpivotValue.symm)
  · -- support confined to the four labels
    intro c hstressNe
    by_contra houtside
    push Not at houtside
    obtain ⟨hneOne, hneTwo, hneThree, hneFour⟩ := houtside
    rw [hstressDef] at hstressNe
    simp only [hneOne, hneTwo, hneThree, hneFour, if_false] at hstressNe
    exact hstressNe rfl
  · -- the full sum collapses to the four labels
    set supportSet : Finset (Fin size) :=
      insert labelOne (insert labelTwo (insert labelThree {labelFour}))
      with hsupportDef
    have hcollapse : ∑ c, stress c • atomMatrix (design.atom c)
        = ∑ c ∈ supportSet, stress c • atomMatrix (design.atom c) := by
      refine (Finset.sum_subset (Finset.subset_univ supportSet) ?_).symm
      intro c _ hnotMem
      have hzero : stress c = 0 := by
        rw [hstressDef]
        rw [hsupportDef] at hnotMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hnotMem
        push Not at hnotMem
        obtain ⟨hneOne, hneTwo, hneThree, hneFour⟩ := hnotMem
        simp [hneOne, hneTwo, hneThree, hneFour]
      rw [hzero, zero_smul]
    rw [hcollapse, hsupportDef]
    rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hneOneTwo, hneOneThree, hneOneFour⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hneTwoThree, hneTwoFour⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_singleton]
        exact hneThreeFour),
      Finset.sum_singleton]
    have hfourExpanded := hfourSum
    rw [Fin.sum_univ_four] at hfourExpanded
    simp only [hpickedDef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hfourExpanded
    rw [hstressValues.1, hstressValues.2.1, hstressValues.2.2.1, hstressValues.2.2.2,
      ← add_assoc, ← add_assoc]
    exact hfourExpanded

/-- The lever for a merely nonzero axis: normalize and reuse. -/
theorem exists_stress_of_four_onPlane_atoms_of_ne_zero
    (design : WeightedDesign size 3) {axis : Fin 3 → ℝ} (haxisNe : axis ≠ 0)
    {labelOne labelTwo labelThree labelFour : Fin size}
    (hneOneTwo : labelOne ≠ labelTwo) (hneOneThree : labelOne ≠ labelThree)
    (hneOneFour : labelOne ≠ labelFour) (hneTwoThree : labelTwo ≠ labelThree)
    (hneTwoFour : labelTwo ≠ labelFour) (hneThreeFour : labelThree ≠ labelFour)
    (honPlaneOne : design.atom labelOne ⬝ᵥ axis = 0)
    (honPlaneTwo : design.atom labelTwo ⬝ᵥ axis = 0)
    (honPlaneThree : design.atom labelThree ⬝ᵥ axis = 0)
    (honPlaneFour : design.atom labelFour ⬝ᵥ axis = 0) :
    ∃ stress : Fin size → ℝ, stress ≠ 0
      ∧ (∀ c : Fin size, stress c ≠ 0 →
          c = labelOne ∨ c = labelTwo ∨ c = labelThree ∨ c = labelFour)
      ∧ ∑ c, stress c • atomMatrix (design.atom c) = 0 := by
  have hnormPos : 0 < axis ⬝ᵥ axis := dotProduct_self_pos haxisNe
  set unitAxis : Fin 3 → ℝ := (Real.sqrt (axis ⬝ᵥ axis))⁻¹ • axis with hunitDef
  have hunit : unitAxis ⬝ᵥ unitAxis = 1 := by
    rw [hunitDef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← mul_inv, Real.mul_self_sqrt hnormPos.le]
    exact inv_mul_cancel₀ hnormPos.ne'
  have honUnit : ∀ vec : Fin 3 → ℝ, vec ⬝ᵥ axis = 0 → vec ⬝ᵥ unitAxis = 0 := by
    intro vec hzero
    rw [hunitDef, dotProduct_smul, hzero, smul_eq_mul, mul_zero]
  exact exists_stress_of_four_onPlane_atoms design hunit hneOneTwo hneOneThree hneOneFour
    hneTwoThree hneTwoFour hneThreeFour (honUnit _ honPlaneOne) (honUnit _ honPlaneTwo)
    (honUnit _ honPlaneThree) (honUnit _ honPlaneFour)

/-! ## Part 3: the stress-free dividend at size six -/

/-- **A STRESS-FREE `(6,3)` DESIGN PUTS AT MOST THREE ATOMS ON ANY PLANE.**  In
particular at most three atoms of a stress-free design lie on any tight plane,
so at least two atoms sit strictly off it — the on-plane drop hunted by
`TightDropOnPlaneSixThree` can never come from a coplanar quadruple. -/
theorem planarLabels_card_le_three_of_stressFree
    (design : WeightedDesign 6 3)
    (hstressFree : ∀ stress : Fin 6 → ℝ,
      (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0)
    {axis : Fin 3 → ℝ} (haxisNe : axis ≠ 0)
    (planarLabels : Finset (Fin 6))
    (honPlane : ∀ c ∈ planarLabels, design.atom c ⬝ᵥ axis = 0) :
    planarLabels.card ≤ 3 := by
  classical
  by_contra hlarge
  push Not at hlarge
  obtain ⟨quadruple, hsubset, hquadCard⟩ :=
    Finset.exists_subset_card_eq (s := planarLabels) (n := 4) (by omega)
  obtain ⟨labelOne, restThree, hnotMemOne, hinsertQuad, hrestCard⟩ :=
    Finset.card_eq_succ.mp hquadCard
  obtain ⟨labelTwo, labelThree, labelFour, hneTwoThree, hneTwoFour, hneThreeFour,
    hrestEq⟩ := Finset.card_eq_three.mp hrestCard
  have hmemQuad : ∀ c ∈ quadruple, design.atom c ⬝ᵥ axis = 0 := fun c hmem =>
    honPlane c (hsubset hmem)
  have hneOneTwo : labelOne ≠ labelTwo := fun hEq => hnotMemOne (by
    rw [hrestEq, hEq]
    simp)
  have hneOneThree : labelOne ≠ labelThree := fun hEq => hnotMemOne (by
    rw [hrestEq, hEq]
    simp)
  have hneOneFour : labelOne ≠ labelFour := fun hEq => hnotMemOne (by
    rw [hrestEq, hEq]
    simp)
  have hmemOne : labelOne ∈ quadruple := by
    rw [← hinsertQuad]
    simp
  have hmemTwo : labelTwo ∈ quadruple := by
    rw [← hinsertQuad, hrestEq]
    simp
  have hmemThree : labelThree ∈ quadruple := by
    rw [← hinsertQuad, hrestEq]
    simp
  have hmemFour : labelFour ∈ quadruple := by
    rw [← hinsertQuad, hrestEq]
    simp
  obtain ⟨stress, hstressNe, _, hstressSum⟩ :=
    exists_stress_of_four_onPlane_atoms_of_ne_zero design haxisNe hneOneTwo hneOneThree
      hneOneFour hneTwoThree hneTwoFour hneThreeFour (hmemQuad _ hmemOne)
      (hmemQuad _ hmemTwo) (hmemQuad _ hmemThree) (hmemQuad _ hmemFour)
  exact hstressNe (hstressFree stress hstressSum)

end Gtz
