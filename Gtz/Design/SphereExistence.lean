/-
# The existence half of the sphere dichotomy

`Gtz.exists_planeStrictPair_of_transversalAxis` (Gtz/Design/TightAxisPairBudget.lean:390)
turns a unit axis that misses the six pair-planes of four labels into a pair of atoms
that strictly dominates every nonzero probe in the plane orthogonal to that axis.  Its
hypothesis is an axis the CONSUMER must supply, and nothing in the tree produces one.
Agent 1.1 recorded that gap verbatim: "Nobody has yet shown that a normal avoiding all
fifteen planes EXISTS for a given six-atom design."

This file supplies it, and thereby removes the axis from the statement entirely.

The mechanism is the moment curve `param -> (1, param, param^2)`.  A nonzero vector
pairs against it as a quadratic in `param`, so it can annihilate at most two parameters;
`2 * n` bad parameters cannot cover `2 * n + 1` candidates.  No topology, no measure
theory, no genericity language -- a pigeonhole over `Finset.range (2 * n + 1)`.

Chained against the tree's simplicity predicate the payoff is unconditional:
a design with NO parallel pair and four distinct labels admits a plane in which some
pair of its atoms strictly dominates.  The consumer supplies nothing but the labels.
-/
import Gtz.Design.TightAxisPairBudget
import Gtz.Design.TwoPoleStratum
import Gtz.Design.LinePatternEnumeration
import Gtz.Design.StratumEmptinessLedger
import Gtz.Reduction.SplitTransfer
import Gtz.Ties.TetrahedronCertifiedTie
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

/-! ## Part 1 -- finite avoidance along the moment curve -/

/-- The moment curve in three dimensions.  Its defining property is that a nonzero
covector pairs against it as a quadratic polynomial in the parameter. -/
noncomputable def momentDirection (param : ℝ) : Fin 3 → ℝ := ![1, param, param ^ 2]

/-- Pairing against the moment curve reads off the quadratic. -/
theorem dotProduct_momentDirection (probeVec : Fin 3 → ℝ) (param : ℝ) :
    probeVec ⬝ᵥ momentDirection param
      = probeVec 0 + probeVec 1 * param + probeVec 2 * param ^ 2 := by
  simp only [momentDirection, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The moment curve never meets the origin; its squared length is `1 + t^2 + t^4`. -/
theorem momentDirection_dotProduct_self (param : ℝ) :
    momentDirection param ⬝ᵥ momentDirection param = 1 + param ^ 2 + param ^ 4 := by
  simp only [momentDirection, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **A quadratic with three distinct roots is the zero quadratic.**  Stated on the
coefficient vector, which is what the avoidance count consumes. -/
theorem eq_zero_of_three_momentRoots (probeVec : Fin 3 → ℝ)
    {paramFirst paramSecond paramThird : ℝ}
    (hneFirstSecond : paramFirst ≠ paramSecond)
    (hneFirstThird : paramFirst ≠ paramThird)
    (hneSecondThird : paramSecond ≠ paramThird)
    (hrootFirst : probeVec ⬝ᵥ momentDirection paramFirst = 0)
    (hrootSecond : probeVec ⬝ᵥ momentDirection paramSecond = 0)
    (hrootThird : probeVec ⬝ᵥ momentDirection paramThird = 0) :
    probeVec = 0 := by
  rw [dotProduct_momentDirection] at hrootFirst hrootSecond hrootThird
  have hsubFirstSecond : (paramFirst - paramSecond)
      * (probeVec 1 + probeVec 2 * (paramFirst + paramSecond)) = 0 := by
    linear_combination hrootFirst - hrootSecond
  have hsubFirstThird : (paramFirst - paramThird)
      * (probeVec 1 + probeVec 2 * (paramFirst + paramThird)) = 0 := by
    linear_combination hrootFirst - hrootThird
  have hlinearSecond : probeVec 1 + probeVec 2 * (paramFirst + paramSecond) = 0 := by
    rcases mul_eq_zero.mp hsubFirstSecond with hzero | hgood
    · exact absurd (sub_eq_zero.mp hzero) hneFirstSecond
    · exact hgood
  have hlinearThird : probeVec 1 + probeVec 2 * (paramFirst + paramThird) = 0 := by
    rcases mul_eq_zero.mp hsubFirstThird with hzero | hgood
    · exact absurd (sub_eq_zero.mp hzero) hneFirstThird
    · exact hgood
  have hleadZero : probeVec 2 = 0 := by
    have hdiff : probeVec 2 * (paramSecond - paramThird) = 0 := by
      linear_combination hlinearSecond - hlinearThird
    rcases mul_eq_zero.mp hdiff with hzero | hbad
    · exact hzero
    · exact absurd (sub_eq_zero.mp hbad) hneSecondThird
  have hmidZero : probeVec 1 = 0 := by
    rw [hleadZero] at hlinearSecond; linarith
  have hconstZero : probeVec 0 = 0 := by
    rw [hleadZero, hmidZero] at hrootFirst; linarith
  funext coord
  fin_cases coord
  · exact hconstZero
  · exact hmidZero
  · exact hleadZero

/-- **Finite avoidance, parameter form.**  Finitely many nonzero covectors cannot
annihilate every point of the moment curve: each kills at most two parameters, and
`2 * n` parameters do not cover `2 * n + 1` candidates. -/
theorem exists_momentParam_dotProduct_ne_zero {indexType : Type*}
    (indexSet : Finset indexType) (family : indexType → (Fin 3 → ℝ))
    (hnonzero : ∀ index ∈ indexSet, family index ≠ 0) :
    ∃ param : ℝ, ∀ index ∈ indexSet, family index ⬝ᵥ momentDirection param ≠ 0 := by
  classical
  set candidateSteps : Finset ℕ := Finset.range (2 * indexSet.card + 1) with hcandidateDef
  set badSteps : Finset ℕ := indexSet.biUnion
      (fun index => candidateSteps.filter
        (fun step : ℕ => family index ⬝ᵥ momentDirection (step : ℝ) = 0)) with hbadDef
  have hfilterCard : ∀ index ∈ indexSet,
      (candidateSteps.filter
        (fun step : ℕ => family index ⬝ᵥ momentDirection (step : ℝ) = 0)).card ≤ 2 := by
    intro index hindex
    by_contra hbig
    obtain ⟨stepFirst, stepSecond, stepThird, hmemFirst, hmemSecond, hmemThird,
      hneFirstSecond, hneFirstThird, hneSecondThird⟩ :=
      Finset.two_lt_card_iff.mp (not_le.mp hbig)
    refine hnonzero index hindex (eq_zero_of_three_momentRoots (family index)
      (paramFirst := (stepFirst : ℝ)) (paramSecond := (stepSecond : ℝ))
      (paramThird := (stepThird : ℝ)) ?_ ?_ ?_
      (Finset.mem_filter.mp hmemFirst).2 (Finset.mem_filter.mp hmemSecond).2
      (Finset.mem_filter.mp hmemThird).2)
    · exact_mod_cast hneFirstSecond
    · exact_mod_cast hneFirstThird
    · exact_mod_cast hneSecondThird
  have hbadCard : badSteps.card ≤ 2 * indexSet.card := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum hfilterCard) ?_
    rw [Finset.sum_const, smul_eq_mul]
    omega
  have hnotSubset : ¬ candidateSteps ⊆ badSteps := by
    intro hsubset
    have hcardLe := Finset.card_le_card hsubset
    rw [hcandidateDef, Finset.card_range] at hcardLe
    omega
  obtain ⟨step, hstepMem, hstepNot⟩ := Finset.not_subset.mp hnotSubset
  refine ⟨(step : ℝ), fun index hindex hzero => hstepNot ?_⟩
  rw [hbadDef]
  exact Finset.mem_biUnion.mpr ⟨index, hindex, Finset.mem_filter.mpr ⟨hstepMem, hzero⟩⟩

/-- **Finite avoidance on the unit sphere.**  Given finitely many nonzero vectors in
three space there is a SINGLE unit direction transversal to all of them at once.  This
is the existence half of the sphere dichotomy, and the hypothesis that
`Gtz.exists_planeStrictPair_of_transversalAxis` was missing. -/
theorem exists_unitDirection_dotProduct_ne_zero {indexType : Type*}
    (indexSet : Finset indexType) (family : indexType → (Fin 3 → ℝ))
    (hnonzero : ∀ index ∈ indexSet, family index ≠ 0) :
    ∃ unitDirection : Fin 3 → ℝ, unitDirection ⬝ᵥ unitDirection = 1
      ∧ ∀ index ∈ indexSet, family index ⬝ᵥ unitDirection ≠ 0 := by
  obtain ⟨param, hparam⟩ := exists_momentParam_dotProduct_ne_zero indexSet family hnonzero
  have hnormPos : (0 : ℝ) < 1 + param ^ 2 + param ^ 4 := by positivity
  have hsqrtPos : 0 < Real.sqrt (1 + param ^ 2 + param ^ 4) := Real.sqrt_pos.mpr hnormPos
  have hsqrtSq : Real.sqrt (1 + param ^ 2 + param ^ 4) ^ 2 = 1 + param ^ 2 + param ^ 4 :=
    Real.sq_sqrt hnormPos.le
  set scale : ℝ := (Real.sqrt (1 + param ^ 2 + param ^ 4))⁻¹ with hscaleDef
  have hscalePos : 0 < scale := by rw [hscaleDef]; exact inv_pos.mpr hsqrtPos
  have hscaleSq : scale ^ 2 = (1 + param ^ 2 + param ^ 4)⁻¹ := by
    rw [hscaleDef, inv_pow, hsqrtSq]
  refine ⟨scale • momentDirection param, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, momentDirection_dotProduct_self,
      smul_eq_mul, smul_eq_mul]
    calc scale * (scale * (1 + param ^ 2 + param ^ 4))
        = scale ^ 2 * (1 + param ^ 2 + param ^ 4) := by ring
      _ = 1 := by rw [hscaleSq]; field_simp
  · intro index hindex hzero
    rw [dotProduct_smul, smul_eq_mul] at hzero
    rcases mul_eq_zero.mp hzero with hbad | hgood
    · exact absurd hbad (ne_of_gt hscalePos)
    · exact hparam index hindex hgood

/-- **The sphere dichotomy.**  For any finite family of vectors in three space, either
some member is degenerate, or one unit direction is transversal to the whole family. -/
theorem sphereDichotomy_of_family {indexType : Type*} (indexSet : Finset indexType)
    (family : indexType → (Fin 3 → ℝ)) :
    (∃ index ∈ indexSet, family index = 0)
      ∨ ∃ unitDirection : Fin 3 → ℝ, unitDirection ⬝ᵥ unitDirection = 1
          ∧ ∀ index ∈ indexSet, family index ⬝ᵥ unitDirection ≠ 0 := by
  classical
  by_cases hdegenerate : ∃ index ∈ indexSet, family index = 0
  · exact Or.inl hdegenerate
  · exact Or.inr (exists_unitDirection_dotProduct_ne_zero indexSet family
      (fun index hindex hzero => hdegenerate ⟨index, hindex, hzero⟩))

/-! ## Part 2 -- when a cross product degenerates -/

/-- A vector and a multiple of itself have vanishing cross product. -/
theorem crossProduct_smul_right_self_eq_zero (baseVec : Fin 3 → ℝ) (ratio : ℝ) :
    crossProduct baseVec (ratio • baseVec) = 0 := by
  rw [map_smul, cross_self, smul_zero]

/-- **The cross product is nonzero exactly when Cauchy-Schwarz is strict.**  Both
directions come from the Lagrange identity `Gtz.planarCross_self_dot`; no separate
Cauchy-Schwarz input is needed. -/
theorem crossProduct_ne_zero_iff_sq_lt_mul (leftVec rightVec : Fin 3 → ℝ) :
    crossProduct leftVec rightVec ≠ 0
      ↔ (leftVec ⬝ᵥ rightVec) ^ 2 < (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) := by
  constructor
  · intro hne
    have hpos := dotProduct_self_pos hne
    rw [planarCross_self_dot] at hpos
    linarith
  · intro hlt hzero
    have hself : crossProduct leftVec rightVec ⬝ᵥ crossProduct leftVec rightVec = 0 := by
      rw [hzero]; simp
    rw [planarCross_self_dot] at hself
    linarith

/-- **A vanishing cross product against a nonzero vector means proportionality.** -/
theorem eq_smul_of_crossProduct_eq_zero {leftVec rightVec : Fin 3 → ℝ}
    (hleftNe : leftVec ≠ 0) (hcross : crossProduct leftVec rightVec = 0) :
    ∃ ratio : ℝ, rightVec = ratio • leftVec := by
  have hzerothEq : leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1 = 0 := by
    have hcomp := congrFun hcross 0
    rw [cross_apply] at hcomp
    simpa using hcomp
  have hfirstEq : leftVec 2 * rightVec 0 - leftVec 0 * rightVec 2 = 0 := by
    have hcomp := congrFun hcross 1
    rw [cross_apply] at hcomp
    simpa using hcomp
  have hsecondEq : leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0 = 0 := by
    have hcomp := congrFun hcross 2
    rw [cross_apply] at hcomp
    simpa using hcomp
  by_cases hleftFirstNe : leftVec 0 ≠ 0
  · refine ⟨rightVec 0 / leftVec 0, ?_⟩
    have hzeroth : rightVec 0 = rightVec 0 / leftVec 0 * leftVec 0 := by field_simp
    have hfirst : rightVec 1 = rightVec 0 / leftVec 0 * leftVec 1 := by
      field_simp
      linear_combination hsecondEq
    have hsecond : rightVec 2 = rightVec 0 / leftVec 0 * leftVec 2 := by
      field_simp
      linear_combination -hfirstEq
    funext coord
    fin_cases coord
    · simpa using hzeroth
    · simpa using hfirst
    · simpa using hsecond
  · have hleftFirstZero : leftVec 0 = 0 := not_ne_iff.mp hleftFirstNe
    by_cases hleftSecondNe : leftVec 1 ≠ 0
    · refine ⟨rightVec 1 / leftVec 1, ?_⟩
      have hzeroth : rightVec 0 = rightVec 1 / leftVec 1 * leftVec 0 := by
        rw [hleftFirstZero, mul_zero]
        rw [hleftFirstZero, zero_mul] at hsecondEq
        have hproduct : leftVec 1 * rightVec 0 = 0 := by linarith
        rcases mul_eq_zero.mp hproduct with hbad | hgood
        · exact absurd hbad hleftSecondNe
        · exact hgood
      have hfirst : rightVec 1 = rightVec 1 / leftVec 1 * leftVec 1 := by field_simp
      have hsecond : rightVec 2 = rightVec 1 / leftVec 1 * leftVec 2 := by
        field_simp
        linear_combination hzerothEq
      funext coord
      fin_cases coord
      · simpa using hzeroth
      · simpa using hfirst
      · simpa using hsecond
    · have hleftSecondZero : leftVec 1 = 0 := not_ne_iff.mp hleftSecondNe
      have hleftThirdNe : leftVec 2 ≠ 0 := by
        intro hleftThirdZero
        refine hleftNe ?_
        funext coord
        fin_cases coord
        · simpa using hleftFirstZero
        · simpa using hleftSecondZero
        · simpa using hleftThirdZero
      refine ⟨rightVec 2 / leftVec 2, ?_⟩
      have hzeroth : rightVec 0 = rightVec 2 / leftVec 2 * leftVec 0 := by
        rw [hleftFirstZero, mul_zero]
        rw [hleftFirstZero, zero_mul] at hfirstEq
        have hproduct : leftVec 2 * rightVec 0 = 0 := by linarith
        rcases mul_eq_zero.mp hproduct with hbad | hgood
        · exact absurd hbad hleftThirdNe
        · exact hgood
      have hfirst : rightVec 1 = rightVec 2 / leftVec 2 * leftVec 1 := by
        rw [hleftSecondZero, mul_zero]
        rw [hleftSecondZero, zero_mul] at hzerothEq
        have hproduct : leftVec 2 * rightVec 1 = 0 := by linarith
        rcases mul_eq_zero.mp hproduct with hbad | hgood
        · exact absurd hbad hleftThirdNe
        · exact hgood
      have hsecond : rightVec 2 = rightVec 2 / leftVec 2 * leftVec 2 := by field_simp
      funext coord
      fin_cases coord
      · simpa using hzeroth
      · simpa using hfirst
      · simpa using hsecond

/-- A degenerate cross product between two distinct atoms IS a parallel pair, in the
tree's own sense (`Gtz.HasParallelPair`, Gtz/Reduction/SplitTransfer.lean:1971).  The
zero atom is handled by taking the ratio to be zero. -/
theorem hasParallelPair_of_crossProduct_atom_eq_zero {size : ℕ}
    (design : WeightedDesign size 3) {leftLabel rightLabel : Fin size}
    (hnelabel : leftLabel ≠ rightLabel)
    (hcross : crossProduct (design.atom leftLabel) (design.atom rightLabel) = 0) :
    HasParallelPair design := by
  by_cases hleftZero : design.atom leftLabel = 0
  · exact ⟨rightLabel, leftLabel, 0, hnelabel.symm, by rw [hleftZero, zero_smul]⟩
  · obtain ⟨ratio, hratio⟩ := eq_smul_of_crossProduct_eq_zero hleftZero hcross
    exact ⟨leftLabel, rightLabel, ratio, hnelabel, hratio⟩

/-- **Simplicity is transversality input.**  In a design with no parallel pair every
cross product of two distinct atoms is a nonzero vector, hence a legitimate member of
the family the sphere dichotomy consumes. -/
theorem crossProduct_atom_ne_zero_of_not_hasParallelPair {size : ℕ}
    (design : WeightedDesign size 3) (hsimple : ¬ HasParallelPair design)
    {leftLabel rightLabel : Fin size} (hnelabel : leftLabel ≠ rightLabel) :
    crossProduct (design.atom leftLabel) (design.atom rightLabel) ≠ 0 :=
  fun hcross => hsimple (hasParallelPair_of_crossProduct_atom_eq_zero design hnelabel hcross)

/-! ## Part 3 -- a transversal axis for a design -/

/-- **One axis misses every pair-plane at once.**  The label set is arbitrary and
finite; nothing is assumed about the design beyond the listed non-degeneracies. -/
theorem exists_unitAxis_transversal_of_labelPairs {size : ℕ}
    (design : WeightedDesign size 3) (labelPairs : Finset (Fin size × Fin size))
    (hnonparallel : ∀ entry ∈ labelPairs,
      crossProduct (design.atom entry.1) (design.atom entry.2) ≠ 0) :
    ∃ unitAxis : Fin 3 → ℝ, unitAxis ⬝ᵥ unitAxis = 1
      ∧ ∀ entry ∈ labelPairs,
          crossProduct (design.atom entry.1) (design.atom entry.2) ⬝ᵥ unitAxis ≠ 0 :=
  exists_unitDirection_dotProduct_ne_zero labelPairs
    (fun entry => crossProduct (design.atom entry.1) (design.atom entry.2)) hnonparallel

/-- The four-label instance, with the six transversality facts in the shape
`Gtz.exists_planeStrictPair_of_transversalAxis` consumes them. -/
theorem exists_unitAxis_transversal_of_not_hasParallelPair {size : ℕ}
    (design : WeightedDesign size 3) (hsimple : ¬ HasParallelPair design)
    {labelOne labelTwo labelThree labelFour : Fin size}
    (hneOneTwo : labelOne ≠ labelTwo) (hneOneThree : labelOne ≠ labelThree)
    (hneOneFour : labelOne ≠ labelFour) (hneTwoThree : labelTwo ≠ labelThree)
    (hneTwoFour : labelTwo ≠ labelFour) (hneThreeFour : labelThree ≠ labelFour) :
    ∃ unitAxis : Fin 3 → ℝ, unitAxis ⬝ᵥ unitAxis = 1
      ∧ crossProduct (design.atom labelOne) (design.atom labelTwo) ⬝ᵥ unitAxis ≠ 0
      ∧ crossProduct (design.atom labelOne) (design.atom labelThree) ⬝ᵥ unitAxis ≠ 0
      ∧ crossProduct (design.atom labelOne) (design.atom labelFour) ⬝ᵥ unitAxis ≠ 0
      ∧ crossProduct (design.atom labelTwo) (design.atom labelThree) ⬝ᵥ unitAxis ≠ 0
      ∧ crossProduct (design.atom labelTwo) (design.atom labelFour) ⬝ᵥ unitAxis ≠ 0
      ∧ crossProduct (design.atom labelThree) (design.atom labelFour) ⬝ᵥ unitAxis ≠ 0 := by
  classical
  have hnonparallel : ∀ entry ∈ ({(labelOne, labelTwo), (labelOne, labelThree),
      (labelOne, labelFour), (labelTwo, labelThree), (labelTwo, labelFour),
      (labelThree, labelFour)} : Finset (Fin size × Fin size)),
      crossProduct (design.atom entry.1) (design.atom entry.2) ≠ 0 := by
    intro entry hentry
    simp only [Finset.mem_insert, Finset.mem_singleton] at hentry
    rcases hentry with rfl | rfl | rfl | rfl | rfl | rfl
    · exact crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneOneTwo
    · exact crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneOneThree
    · exact crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneOneFour
    · exact crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneTwoThree
    · exact crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneTwoFour
    · exact crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneThreeFour
  obtain ⟨unitAxis, hunit, htransversal⟩ :=
    exists_unitAxis_transversal_of_labelPairs design _ hnonparallel
  exact ⟨unitAxis, hunit,
    htransversal (labelOne, labelTwo) (by simp),
    htransversal (labelOne, labelThree) (by simp),
    htransversal (labelOne, labelFour) (by simp),
    htransversal (labelTwo, labelThree) (by simp),
    htransversal (labelTwo, labelFour) (by simp),
    htransversal (labelThree, labelFour) (by simp)⟩

/-! ## Part 4 -- the axis leaves the statement -/

/-- **The plane-strict pair, with the axis produced rather than assumed.**  Input: four
distinct labels whose six cross products are nonzero.  Output: a unit axis AND a pair of
atoms strictly dominating every nonzero probe in the orthogonal plane. -/
theorem exists_unitAxis_planeStrictPair_of_sixCrossProducts {size : ℕ}
    (design : WeightedDesign size 3)
    {labelOne labelTwo labelThree labelFour : Fin size}
    (hneOneTwo : labelOne ≠ labelTwo) (hneOneThree : labelOne ≠ labelThree)
    (hneOneFour : labelOne ≠ labelFour) (hneTwoThree : labelTwo ≠ labelThree)
    (hneTwoFour : labelTwo ≠ labelFour) (hneThreeFour : labelThree ≠ labelFour)
    (hcrossOneTwo : crossProduct (design.atom labelOne) (design.atom labelTwo) ≠ 0)
    (hcrossOneThree : crossProduct (design.atom labelOne) (design.atom labelThree) ≠ 0)
    (hcrossOneFour : crossProduct (design.atom labelOne) (design.atom labelFour) ≠ 0)
    (hcrossTwoThree : crossProduct (design.atom labelTwo) (design.atom labelThree) ≠ 0)
    (hcrossTwoFour : crossProduct (design.atom labelTwo) (design.atom labelFour) ≠ 0)
    (hcrossThreeFour : crossProduct (design.atom labelThree) (design.atom labelFour) ≠ 0) :
    ∃ unitAxis : Fin 3 → ℝ, unitAxis ⬝ᵥ unitAxis = 1
      ∧ ∃ strongLabel otherLabel : Fin size, strongLabel ≠ otherLabel
          ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ unitAxis = 0 → planar ≠ 0 →
              planar ⬝ᵥ planar
                < (design.atom strongLabel ⬝ᵥ planar) ^ 2
                  + (design.atom otherLabel ⬝ᵥ planar) ^ 2 := by
  classical
  have hnonparallel : ∀ entry ∈ ({(labelOne, labelTwo), (labelOne, labelThree),
      (labelOne, labelFour), (labelTwo, labelThree), (labelTwo, labelFour),
      (labelThree, labelFour)} : Finset (Fin size × Fin size)),
      crossProduct (design.atom entry.1) (design.atom entry.2) ≠ 0 := by
    intro entry hentry
    simp only [Finset.mem_insert, Finset.mem_singleton] at hentry
    rcases hentry with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcrossOneTwo
    · exact hcrossOneThree
    · exact hcrossOneFour
    · exact hcrossTwoThree
    · exact hcrossTwoFour
    · exact hcrossThreeFour
  obtain ⟨unitAxis, hunit, htransversal⟩ :=
    exists_unitAxis_transversal_of_labelPairs design _ hnonparallel
  exact ⟨unitAxis, hunit,
    exists_planeStrictPair_of_transversalAxis design hunit hneOneTwo hneOneThree
      hneOneFour hneTwoThree hneTwoFour hneThreeFour
      (htransversal (labelOne, labelTwo) (by simp))
      (htransversal (labelOne, labelThree) (by simp))
      (htransversal (labelOne, labelFour) (by simp))
      (htransversal (labelTwo, labelThree) (by simp))
      (htransversal (labelTwo, labelFour) (by simp))
      (htransversal (labelThree, labelFour) (by simp))⟩

/-- **The headline.**  A design with no parallel pair and four distinct labels admits a
plane in which some pair of its atoms strictly dominates every nonzero probe.  The
consumer supplies the labels and nothing else -- no frame, no axis, no genericity. -/
theorem exists_unitAxis_planeStrictPair_of_not_hasParallelPair {size : ℕ}
    (design : WeightedDesign size 3) (hsimple : ¬ HasParallelPair design)
    {labelOne labelTwo labelThree labelFour : Fin size}
    (hneOneTwo : labelOne ≠ labelTwo) (hneOneThree : labelOne ≠ labelThree)
    (hneOneFour : labelOne ≠ labelFour) (hneTwoThree : labelTwo ≠ labelThree)
    (hneTwoFour : labelTwo ≠ labelFour) (hneThreeFour : labelThree ≠ labelFour) :
    ∃ unitAxis : Fin 3 → ℝ, unitAxis ⬝ᵥ unitAxis = 1
      ∧ ∃ strongLabel otherLabel : Fin size, strongLabel ≠ otherLabel
          ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ unitAxis = 0 → planar ≠ 0 →
              planar ⬝ᵥ planar
                < (design.atom strongLabel ⬝ᵥ planar) ^ 2
                  + (design.atom otherLabel ⬝ᵥ planar) ^ 2 :=
  exists_unitAxis_planeStrictPair_of_sixCrossProducts design hneOneTwo hneOneThree
    hneOneFour hneTwoThree hneTwoFour hneThreeFour
    (crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneOneTwo)
    (crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneOneThree)
    (crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneOneFour)
    (crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneTwoThree)
    (crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneTwoFour)
    (crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hneThreeFour)

/-! ## Part 5 -- non-vacuity on a shipped fixture -/

/-- The tetrahedron carries no parallel pair, from the tree's shipped primitivity. -/
theorem tetraDesign_not_hasParallelPair : ¬ HasParallelPair tetraDesign :=
  (isPrimitiveDesign_iff_not_hasParallelPair tetraDesign).mp isPrimitiveDesign_tetraDesign

/-- **The headline fires on the tetrahedron.**  A certified tie in three space whose
shadow in a produced plane carries a strictly dominating pair -- the rank drop buys
strictness, and no axis had to be guessed. -/
theorem tetraDesign_exists_unitAxis_planeStrictPair :
    ∃ unitAxis : Fin 3 → ℝ, unitAxis ⬝ᵥ unitAxis = 1
      ∧ ∃ strongLabel otherLabel : Fin 4, strongLabel ≠ otherLabel
          ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ unitAxis = 0 → planar ≠ 0 →
              planar ⬝ᵥ planar
                < (tetraDesign.atom strongLabel ⬝ᵥ planar) ^ 2
                  + (tetraDesign.atom otherLabel ⬝ᵥ planar) ^ 2 :=
  exists_unitAxis_planeStrictPair_of_not_hasParallelPair tetraDesign
    tetraDesign_not_hasParallelPair (labelOne := 0) (labelTwo := 1) (labelThree := 2)
    (labelFour := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Gtz
