/-
# Branch (i), phase 1: the coplanarity mechanism is FALSE at size six

The proposed size-six lever for branch (i) ran: at a `(6,3)` design, vanishing of
the pair budget makes all FOUR completions of a plane-strict pair singular; the
four singular gaps' null directions were expected to drive the four outside
atoms into a common plane; four coplanar atoms then carry a stress
(`Gtz.exists_stress_of_four_onPlane_atoms`, sibling file), contradicting
stress-freeness and forcing the budget STRICTLY negative.

This file kills the middle step by exhibiting the configuration it forbids.

`mirrorFamilyDesign` is a parameter family of genuine `(6,3)` weighted designs
with the mirror symmetry `y -> -y`, `z -> -z`:

    g_0 = (a,  b, 0)      g_2 = (c,  d,  e)     g_4 = (c, -d,  e)
    g_1 = (a, -b, 0)      g_3 = (c,  d, -e)     g_5 = (c, -d, -e)

weights `t_in, t_in, t_out, t_out, t_out, t_out`.  Three facts, all
unconditional in the parameters:

* `det_gapTriple_mirrorPair` — all four completions of the inner pair share ONE
  gap determinant, the sign-free closed form

      (2a^2 - 1)(2b^2 - 1)(e^2 - 1) - (2a^2 - 1) d^2 - (2b^2 - 1) c^2,

  so the whole pair budget vanishes on a single hypersurface, not on four.

* `mirrorPair_planeStrict` — with `2a^2 > 1` and `2b^2 > 1` the inner pair
  dominates the plane of the axis `(0,0,1)` strictly, so the pair-budget
  machinery applies verbatim.

* `mirrorOutside_spans` — no nonzero direction is orthogonal to all four outside
  atoms: three of them already have determinant `-4cde`.  The outside quadruple
  is NEVER coplanar in this family, whatever the parameters.

`exists_pairBudgetEquality_with_spanningOutside` assembles the three at an exact
rational parameter point

    a^2 = 7/10, b^2 = 103/98, c^2 = 89/20, d = 9/14, e^2 = 25/2,
    t_in = 23/50, t_out = 1/50,

verified in the kernel: Parseval exact, weights positive, all four completions
singular, the inner pair plane-strict, and the outside quadruple spanning.  The
mechanism is refuted at six points: budget equality does NOT force coplanarity,
and the strict-negativity step of branch (i) has no proof along this route.

What survives: the equality locus is still an inverse-gap QUADRIC condition (all
four outside atoms sitting on `g^T (-B^{-1}) g = 1`), a codimension-one
condition on each atom separately rather than a rank condition on the
quadruple.  The `(5,3)` diamond agrees: at its four budget-equality pairs the
outside triples have incidence determinants `1, -1, 1, 1`, likewise
non-coplanar (exact rationals, lane report).  Any strict-negativity argument
must consume the tie inequalities at all twenty triples, not the equality locus
alone.

Calibration note: this witness is not itself a tie — the triples `{0,4,5}` and
`{1,2,3}` dominate strictly there (certified in exact radical arithmetic in the
lane report).  What it refutes is the geometric implication "four singular
completions => four coplanar atoms", which the proposed route used as an
unconditional step.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Gtz

open Matrix

/-! ## Part 1: the shared gap determinant of a mirror pair's completions -/

/-- Summing three atoms over an explicit triple. -/
theorem subsetSum_explicitTriple {size : ℕ} (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hFirstSecond : firstLabel ≠ secondLabel) (hFirstThird : firstLabel ≠ thirdLabel)
    (hSecondThird : secondLabel ≠ thirdLabel) :
    subsetSum design {firstLabel, secondLabel, thirdLabel}
      = atomMatrix (design.atom firstLabel) + atomMatrix (design.atom secondLabel)
        + atomMatrix (design.atom thirdLabel) := by
  classical
  rw [subsetSum, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hFirstSecond, hFirstThird⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact hSecondThird),
    Finset.sum_singleton, ← add_assoc]

set_option maxRecDepth 10000 in
/-- **THE COMPLETIONS SHARE ONE DETERMINANT.**  For a mirror pair `(a, b, 0)`,
`(a, -b, 0)` and any third atom, the gap determinant depends on the third atom
only through the SQUARES of its coordinates, so all four sign patterns of a
mirror quadruple give the same value. -/
theorem det_gapTriple_mirrorPair (rootA rootB thirdOne thirdTwo thirdThree : ℝ) :
    (atomMatrix ![rootA, rootB, 0] + atomMatrix ![rootA, -rootB, 0]
        + atomMatrix ![thirdOne, thirdTwo, thirdThree]
        - (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      = (2 * rootA ^ 2 - 1) * (2 * rootB ^ 2 - 1) * (thirdThree ^ 2 - 1)
        - (2 * rootA ^ 2 - 1) * thirdTwo ^ 2 - (2 * rootB ^ 2 - 1) * thirdOne ^ 2 := by
  have hmatrixEq : (atomMatrix ![rootA, rootB, 0] + atomMatrix ![rootA, -rootB, 0]
        + atomMatrix ![thirdOne, thirdTwo, thirdThree] - (1 : Matrix (Fin 3) (Fin 3) ℝ))
      = !![2 * rootA ^ 2 + thirdOne ^ 2 - 1, thirdOne * thirdTwo, thirdOne * thirdThree;
          thirdOne * thirdTwo, 2 * rootB ^ 2 + thirdTwo ^ 2 - 1, thirdTwo * thirdThree;
          thirdOne * thirdThree, thirdTwo * thirdThree, thirdThree ^ 2 - 1] := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
        Matrix.one_fin_three] <;>
      ring
  rw [hmatrixEq, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## Part 2: the mirror family -/

/-- The six atoms of the mirror family. -/
def mirrorAtomFamily (rootA rootB rootC rootD rootE : ℝ) : Fin 6 → (Fin 3 → ℝ) :=
  ![![rootA, rootB, 0], ![rootA, -rootB, 0], ![rootC, rootD, rootE],
    ![rootC, rootD, -rootE], ![rootC, -rootD, rootE], ![rootC, -rootD, -rootE]]

/-- The six weights of the mirror family. -/
def mirrorWeightFamily (weightInner weightOuter : ℝ) : Fin 6 → ℝ :=
  ![weightInner, weightInner, weightOuter, weightOuter, weightOuter, weightOuter]

theorem mirrorAtomFamily_zero (rootA rootB rootC rootD rootE : ℝ) :
    mirrorAtomFamily rootA rootB rootC rootD rootE 0 = ![rootA, rootB, 0] := rfl

theorem mirrorAtomFamily_one (rootA rootB rootC rootD rootE : ℝ) :
    mirrorAtomFamily rootA rootB rootC rootD rootE 1 = ![rootA, -rootB, 0] := rfl

theorem mirrorAtomFamily_two (rootA rootB rootC rootD rootE : ℝ) :
    mirrorAtomFamily rootA rootB rootC rootD rootE 2 = ![rootC, rootD, rootE] := rfl

theorem mirrorAtomFamily_three (rootA rootB rootC rootD rootE : ℝ) :
    mirrorAtomFamily rootA rootB rootC rootD rootE 3 = ![rootC, rootD, -rootE] := rfl

theorem mirrorAtomFamily_four (rootA rootB rootC rootD rootE : ℝ) :
    mirrorAtomFamily rootA rootB rootC rootD rootE 4 = ![rootC, -rootD, rootE] := rfl

theorem mirrorAtomFamily_five (rootA rootB rootC rootD rootE : ℝ) :
    mirrorAtomFamily rootA rootB rootC rootD rootE 5 = ![rootC, -rootD, -rootE] := rfl

theorem mirrorWeightFamily_zero (weightInner weightOuter : ℝ) :
    mirrorWeightFamily weightInner weightOuter 0 = weightInner := rfl

theorem mirrorWeightFamily_one (weightInner weightOuter : ℝ) :
    mirrorWeightFamily weightInner weightOuter 1 = weightInner := rfl

theorem mirrorWeightFamily_two (weightInner weightOuter : ℝ) :
    mirrorWeightFamily weightInner weightOuter 2 = weightOuter := rfl

theorem mirrorWeightFamily_three (weightInner weightOuter : ℝ) :
    mirrorWeightFamily weightInner weightOuter 3 = weightOuter := rfl

theorem mirrorWeightFamily_four (weightInner weightOuter : ℝ) :
    mirrorWeightFamily weightInner weightOuter 4 = weightOuter := rfl

theorem mirrorWeightFamily_five (weightInner weightOuter : ℝ) :
    mirrorWeightFamily weightInner weightOuter 5 = weightOuter := rfl

/-- **THE MIRROR FAMILY.**  A `(6,3)` weighted design with an inner pair on the
plane `z = 0` and an outside quadruple carrying all four sign patterns.  The
three hypotheses are exactly the diagonal moment equations; the off-diagonal
Parseval entries hold identically by the mirror symmetry. -/
noncomputable def mirrorFamilyDesign (rootA rootB rootC rootD rootE
    weightInner weightOuter : ℝ) (hInnerPos : 0 < weightInner)
    (hOuterPos : 0 < weightOuter)
    (hweightSum : 2 * weightInner + 4 * weightOuter = 1)
    (hmomentOne : 2 * weightInner * rootA ^ 2 + 4 * weightOuter * rootC ^ 2 = 1)
    (hmomentTwo : 2 * weightInner * rootB ^ 2 + 4 * weightOuter * rootD ^ 2 = 1)
    (hmomentThree : 4 * weightOuter * rootE ^ 2 = 1) : WeightedDesign 6 3 where
  atom := mirrorAtomFamily rootA rootB rootC rootD rootE
  weight := mirrorWeightFamily weightInner weightOuter
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;> first | exact hInnerPos | exact hOuterPos
  weight_sum_one := by
    simp only [Fin.sum_univ_six, mirrorWeightFamily_zero, mirrorWeightFamily_one,
      mirrorWeightFamily_two, mirrorWeightFamily_three, mirrorWeightFamily_four,
      mirrorWeightFamily_five]
    linarith [hweightSum]
  isParseval := by
    ext rowIndex colIndex
    rw [Matrix.sum_apply]
    simp only [Fin.sum_univ_six, mirrorWeightFamily_zero, mirrorWeightFamily_one,
      mirrorWeightFamily_two, mirrorWeightFamily_three, mirrorWeightFamily_four,
      mirrorWeightFamily_five, mirrorAtomFamily_zero, mirrorAtomFamily_one,
      mirrorAtomFamily_two, mirrorAtomFamily_three, mirrorAtomFamily_four,
      mirrorAtomFamily_five, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.one_fin_three,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_fin_const] <;>
      (try norm_num)
    all_goals linarith [hmomentOne, hmomentTwo, hmomentThree]

/-- The family's atoms, unfolded. -/
theorem mirrorFamilyDesign_atom (rootA rootB rootC rootD rootE
    weightInner weightOuter : ℝ) (hInnerPos : 0 < weightInner)
    (hOuterPos : 0 < weightOuter)
    (hweightSum : 2 * weightInner + 4 * weightOuter = 1)
    (hmomentOne : 2 * weightInner * rootA ^ 2 + 4 * weightOuter * rootC ^ 2 = 1)
    (hmomentTwo : 2 * weightInner * rootB ^ 2 + 4 * weightOuter * rootD ^ 2 = 1)
    (hmomentThree : 4 * weightOuter * rootE ^ 2 = 1) :
    (mirrorFamilyDesign rootA rootB rootC rootD rootE weightInner weightOuter hInnerPos
        hOuterPos hweightSum hmomentOne hmomentTwo hmomentThree).atom
      = mirrorAtomFamily rootA rootB rootC rootD rootE := rfl

/-! ## Part 3: the two unconditional geometric facts -/

/-- **THE INNER PAIR IS PLANE-STRICT.**  Against the axis `(0,0,1)` the pair
`(a, b, 0)`, `(a, -b, 0)` dominates the plane strictly as soon as both `2a^2`
and `2b^2` exceed one. -/
theorem mirrorPair_planeStrict (rootA rootB : ℝ) (hSeedBig : 1 < 2 * rootA ^ 2)
    (hProbeBig : 1 < 2 * rootB ^ 2) (planar : Fin 3 → ℝ)
    (hplanarPerp : planar ⬝ᵥ ![0, 0, 1] = 0) (hplanarNe : planar ≠ 0) :
    planar ⬝ᵥ planar
      < ((![rootA, rootB, 0] : Fin 3 → ℝ) ⬝ᵥ planar) ^ 2
        + ((![rootA, -rootB, 0] : Fin 3 → ℝ) ⬝ᵥ planar) ^ 2 := by
  have hthirdZero : planar 2 = 0 := by
    have hvalue := hplanarPerp
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hvalue
    linarith [hvalue]
  have hcoordsNe : ¬ (planar 0 = 0 ∧ planar 1 = 0) := by
    rintro ⟨hfirst, hsecond⟩
    refine hplanarNe (funext fun coord => ?_)
    fin_cases coord
    · exact hfirst
    · exact hsecond
    · exact hthirdZero
  have hnormValue : planar ⬝ᵥ planar = planar 0 ^ 2 + planar 1 ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_three, hthirdZero]
    ring
  have hseedValue : (![rootA, rootB, 0] : Fin 3 → ℝ) ⬝ᵥ planar
      = rootA * planar 0 + rootB * planar 1 := by
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hprobeValue : (![rootA, -rootB, 0] : Fin 3 → ℝ) ⬝ᵥ planar
      = rootA * planar 0 - rootB * planar 1 := by
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hnormValue, hseedValue, hprobeValue]
  rcases (not_and_or.mp hcoordsNe) with hfirstNe | hsecondNe
  · have hfirstSqPos : 0 < planar 0 ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hfirstNe))
    nlinarith [hSeedBig, hProbeBig, hfirstSqPos, sq_nonneg (planar 1)]
  · have hsecondSqPos : 0 < planar 1 ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsecondNe))
    nlinarith [hSeedBig, hProbeBig, hsecondSqPos, sq_nonneg (planar 0)]

/-- **THE OUTSIDE QUADRUPLE IS NEVER COPLANAR.**  Three of the four mirror
images already span: their determinant is `-4 c d e`. -/
theorem mirrorOutside_spans (rootC rootD rootE : ℝ) (hSeedNe : rootC ≠ 0)
    (hMiddleNe : rootD ≠ 0) (hLastNe : rootE ≠ 0) (probe : Fin 3 → ℝ)
    (hFirstPerp : (![rootC, rootD, rootE] : Fin 3 → ℝ) ⬝ᵥ probe = 0)
    (hSecondPerp : (![rootC, rootD, -rootE] : Fin 3 → ℝ) ⬝ᵥ probe = 0)
    (hThirdPerp : (![rootC, -rootD, rootE] : Fin 3 → ℝ) ⬝ᵥ probe = 0) :
    probe = 0 := by
  have hFirstValue : rootC * probe 0 + rootD * probe 1 + rootE * probe 2 = 0 := by
    have hvalue := hFirstPerp
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hvalue
    linarith [hvalue]
  have hSecondValue : rootC * probe 0 + rootD * probe 1 - rootE * probe 2 = 0 := by
    have hvalue := hSecondPerp
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hvalue
    linarith [hvalue]
  have hThirdValue : rootC * probe 0 - rootD * probe 1 + rootE * probe 2 = 0 := by
    have hvalue := hThirdPerp
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hvalue
    linarith [hvalue]
  have hLastZero : probe 2 = 0 := by
    have hdiff : rootE * probe 2 = 0 := by linarith [hFirstValue, hSecondValue]
    exact (mul_eq_zero.mp hdiff).resolve_left hLastNe
  have hMiddleZero : probe 1 = 0 := by
    have hdiff : rootD * probe 1 = 0 := by linarith [hFirstValue, hThirdValue]
    exact (mul_eq_zero.mp hdiff).resolve_left hMiddleNe
  have hFirstZero : probe 0 = 0 := by
    have hvalue : rootC * probe 0 = 0 := by
      rw [hMiddleZero, hLastZero] at hFirstValue
      linarith [hFirstValue]
    exact (mul_eq_zero.mp hvalue).resolve_left hSeedNe
  funext coord
  fin_cases coord
  · exact hFirstZero
  · exact hMiddleZero
  · exact hLastZero

/-! ## Part 4: the exact witness -/

/-- First mirror parameter of the witness, `sqrt(7/10)`. -/
noncomputable def witnessSeedRoot : ℝ := Real.sqrt (7 / 10)

/-- Second mirror parameter of the witness, `sqrt(103/98)`. -/
noncomputable def witnessProbeRoot : ℝ := Real.sqrt (103 / 98)

/-- Outside first coordinate of the witness, `sqrt(89/20)`. -/
noncomputable def witnessOutsideRoot : ℝ := Real.sqrt (89 / 20)

/-- Outside third coordinate of the witness, `sqrt(25/2)`. -/
noncomputable def witnessLastRoot : ℝ := Real.sqrt (25 / 2)

theorem witnessSeedRoot_sq : witnessSeedRoot ^ 2 = 7 / 10 := by
  rw [witnessSeedRoot, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 10)]

theorem witnessProbeRoot_sq : witnessProbeRoot ^ 2 = 103 / 98 := by
  rw [witnessProbeRoot, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 103 / 98)]

theorem witnessOutsideRoot_sq : witnessOutsideRoot ^ 2 = 89 / 20 := by
  rw [witnessOutsideRoot, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 89 / 20)]

theorem witnessLastRoot_sq : witnessLastRoot ^ 2 = 25 / 2 := by
  rw [witnessLastRoot, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 25 / 2)]

theorem witnessOutsideRoot_pos : 0 < witnessOutsideRoot :=
  Real.sqrt_pos.mpr (by norm_num)

theorem witnessLastRoot_pos : 0 < witnessLastRoot :=
  Real.sqrt_pos.mpr (by norm_num)

/-- **THE MECHANISM IS REFUTED AT SIX POINTS.**  A `(6,3)` weighted design whose
inner pair dominates the plane of a unit axis STRICTLY, whose four completions
of that pair all have SINGULAR gap — the exact equality locus of the pair
budget, where all four completions weakly dominate — and whose four outside
atoms admit NO common orthogonal direction.  Budget equality therefore does not
drive the outside atoms into a plane, and the coplanarity route to strict
negativity is dead. -/
theorem exists_pairBudgetEquality_with_spanningOutside :
    ∃ design : WeightedDesign 6 3,
      (∀ planar : Fin 3 → ℝ, planar ⬝ᵥ ![0, 0, 1] = 0 → planar ≠ 0 →
          planar ⬝ᵥ planar
            < (design.atom 0 ⬝ᵥ planar) ^ 2 + (design.atom 1 ⬝ᵥ planar) ^ 2)
        ∧ (∀ outsideLabel : Fin 6, outsideLabel ≠ 0 → outsideLabel ≠ 1 →
            (subsetSum design {0, 1, outsideLabel} - 1).det = 0)
        ∧ (∀ probe : Fin 3 → ℝ,
            (∀ outsideLabel : Fin 6, outsideLabel ≠ 0 → outsideLabel ≠ 1 →
              design.atom outsideLabel ⬝ᵥ probe = 0) → probe = 0) := by
  classical
  have hweightSum : 2 * (23 / 50 : ℝ) + 4 * (1 / 50 : ℝ) = 1 := by norm_num
  have hmomentOne : 2 * (23 / 50 : ℝ) * witnessSeedRoot ^ 2
      + 4 * (1 / 50 : ℝ) * witnessOutsideRoot ^ 2 = 1 := by
    rw [witnessSeedRoot_sq, witnessOutsideRoot_sq]
    norm_num
  have hmomentTwo : 2 * (23 / 50 : ℝ) * witnessProbeRoot ^ 2
      + 4 * (1 / 50 : ℝ) * (9 / 14 : ℝ) ^ 2 = 1 := by
    rw [witnessProbeRoot_sq]
    norm_num
  have hmomentThree : 4 * (1 / 50 : ℝ) * witnessLastRoot ^ 2 = 1 := by
    rw [witnessLastRoot_sq]
    norm_num
  refine ⟨mirrorFamilyDesign witnessSeedRoot witnessProbeRoot witnessOutsideRoot
    (9 / 14 : ℝ) witnessLastRoot (23 / 50 : ℝ) (1 / 50 : ℝ) (by norm_num) (by norm_num)
    hweightSum hmomentOne hmomentTwo hmomentThree, ?_, ?_, ?_⟩
  · intro planar hplanarPerp hplanarNe
    have hseedBig : 1 < 2 * witnessSeedRoot ^ 2 := by
      rw [witnessSeedRoot_sq]; norm_num
    have hprobeBig : 1 < 2 * witnessProbeRoot ^ 2 := by
      rw [witnessProbeRoot_sq]; norm_num
    have hatomZero : (mirrorFamilyDesign witnessSeedRoot witnessProbeRoot
        witnessOutsideRoot (9 / 14 : ℝ) witnessLastRoot (23 / 50 : ℝ) (1 / 50 : ℝ)
        (by norm_num) (by norm_num) hweightSum hmomentOne hmomentTwo hmomentThree).atom 0
        = ![witnessSeedRoot, witnessProbeRoot, 0] := rfl
    have hatomOne : (mirrorFamilyDesign witnessSeedRoot witnessProbeRoot
        witnessOutsideRoot (9 / 14 : ℝ) witnessLastRoot (23 / 50 : ℝ) (1 / 50 : ℝ)
        (by norm_num) (by norm_num) hweightSum hmomentOne hmomentTwo hmomentThree).atom 1
        = ![witnessSeedRoot, -witnessProbeRoot, 0] := rfl
    rw [hatomZero, hatomOne]
    exact mirrorPair_planeStrict witnessSeedRoot witnessProbeRoot hseedBig hprobeBig
      planar hplanarPerp hplanarNe
  · intro outsideLabel hneFirst hneSecond
    have hdetValue : ∀ thirdOne thirdTwo thirdThree : ℝ,
        thirdOne ^ 2 = 89 / 20 → thirdTwo ^ 2 = 81 / 196 → thirdThree ^ 2 = 25 / 2 →
        (atomMatrix ![witnessSeedRoot, witnessProbeRoot, 0]
            + atomMatrix ![witnessSeedRoot, -witnessProbeRoot, 0]
            + atomMatrix ![thirdOne, thirdTwo, thirdThree]
            - (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
      intro thirdOne thirdTwo thirdThree hOneSq hTwoSq hThreeSq
      rw [det_gapTriple_mirrorPair, witnessSeedRoot_sq, witnessProbeRoot_sq, hOneSq,
        hTwoSq, hThreeSq]
      norm_num
    have hmiddleSq : (9 / 14 : ℝ) ^ 2 = 81 / 196 := by norm_num
    have hnegMiddleSq : (-(9 / 14 : ℝ)) ^ 2 = 81 / 196 := by norm_num
    have hnegLastSq : (-witnessLastRoot) ^ 2 = 25 / 2 := by
      rw [neg_pow, witnessLastRoot_sq]
      norm_num
    fin_cases outsideLabel
    · exact absurd rfl hneFirst
    · exact absurd rfl hneSecond
    · rw [subsetSum_explicitTriple _ (by decide) (by decide) (by decide)]
      exact hdetValue _ _ _ witnessOutsideRoot_sq hmiddleSq witnessLastRoot_sq
    · rw [subsetSum_explicitTriple _ (by decide) (by decide) (by decide)]
      exact hdetValue _ _ _ witnessOutsideRoot_sq hmiddleSq hnegLastSq
    · rw [subsetSum_explicitTriple _ (by decide) (by decide) (by decide)]
      exact hdetValue _ _ _ witnessOutsideRoot_sq hnegMiddleSq witnessLastRoot_sq
    · rw [subsetSum_explicitTriple _ (by decide) (by decide) (by decide)]
      exact hdetValue _ _ _ witnessOutsideRoot_sq hnegMiddleSq hnegLastSq
  · intro probe hperp
    exact mirrorOutside_spans witnessOutsideRoot (9 / 14 : ℝ) witnessLastRoot
      witnessOutsideRoot_pos.ne' (by norm_num) witnessLastRoot_pos.ne' probe
      (hperp 2 (by decide) (by decide)) (hperp 3 (by decide) (by decide))
      (hperp 4 (by decide) (by decide))

end Gtz
