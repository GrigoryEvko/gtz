/-
# The selection obstruction: no constant, and no label-free, choice of dominating subset

`Gtz.LiftingLemma`'s docstring records the campaign's operative claim that
"the pivot/subset SELECTION is the open content: every deterministic rule is refuted;
selection is global". This file turns that sentence from prose into kernel-checked
mathematics, in the two precise senses in which it is true, and marks off the sense in
which it is false.

**What the selection set is.** For a `(k+1)`-design the Lifting Lemma quantifies over
tuples `(pivot, pivotUnit, deflator, subset)`, but only the first and last are free:
`liftingCertificates_of_dominates_atPivot` below shows EVERY nonzero atom of a
dominating `(k+1)`-subset serves as a pivot, with the complementary subset forced to be
the rest of that subset. So the set of good `(pivot, subset)` pairs is the
`(k+1)`-to-one preimage of the domination mask `Dom(D) = {C : C.card = k+1, S_C ⪰ I}`.
At `(6,3)` that is a subset of a fixed 60-element index set varying over the design
space — a combinatorial bundle whose fibres are finite and discrete, so "non-contractible
fibre" is not available as an obstruction and Michael's selection theorem does not apply
(its values must be closed and CONVEX).

**Sense 1 — no constant selector (`no_universal_dominating_subset`).** Two explicit
rational `(6,3)` designs have DISJOINT domination masks: `heavyPivotDesign` dominates on
`{3,4,5}` and on nothing else, and `rotatedHeavyPivotDesign` does not dominate there. So
no single `(pivot, subset)` combination is good at every design
(`no_universal_goodPair`), and two designs already share no good subset at all
(`exists_designs_with_disjoint_dominationSets`). Since the good-selection set takes
values in a FIXED FINITE set, a continuous selector over a connected design space is
locally constant, hence constant, hence universal — so the finite theorem here is exactly
the obstruction to a continuous selector. The connectivity input is classical (a weighted
`(m,k)` design is the same thing as a point of `V_k(ℝᵐ) × Δ°_{m-1}` via
`a_c = √t_c · g_c`, and `V₃(ℝ⁶)` is 2-connected) and is NOT mechanized here; the finite
statements below are.

**Sense 2 — no label-free selector
(`exists_symmetry_with_no_fixed_dominatingSubset`).** `doubledTetrahedronDesign` is fixed
by the double transposition `(0 1)(3 4)`, yet none of its four subsets invariant under
that relabelling dominates — each contains a repeated atom, which
`not_dominates_of_repeated_atom` excludes — while twelve other 3-subsets do dominate. Any
selector computed from relabelling-invariant data must return an invariant subset there,
so it must fail. This is the sense that explains the campaign's refuted catalogue:
heaviest atom, largest total leverage, maximum determinant, minimum coherence, Seidel
sign — every one of those rules is relabelling-invariant.

**The sense in which the claim is FALSE, recorded so it is not lost.** "Every
deterministic rule is refuted" is not literally true. E-optimal selection — take the
3-subset maximising `λ_min(S_C)` — dominates whenever ANY subset dominates, because
domination IS `λ_min(S_C) ≥ 1`. What it does not do is certify anything: it presupposes
the existence it is meant to produce. The refutable classes are the continuous ones and
the label-free ones, and those are what is proved here.

**A named rule, refuted outright.**
`heaviest_atom_can_lie_outside_every_dominatingSubset`: at `heavyPivotDesign` atom `1`
has strictly the largest leverage (`216/25`, next `126/25`), a dominating subset exists
with margin `51/25`, and every 3-subset containing atom `1` fails to dominate. The
refutation is on the interior of the all-heavy stratum, not at a tie.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.LiftingLemma
import Gtz.Reduction.RayleighCertificate
import Gtz.Ties.RepeatedAtomExclusion

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! ## Non-domination from one explicit direction -/

/-- **Non-domination from a negative direction**: a single test vector at which the
selected atoms fail to majorize the identity form refutes domination outright. The
contrapositive of `sum_sq_ge_of_dominates`, and the only engine the explicit witnesses
below need. -/
theorem not_dominates_of_negativeDirection {m dim : ℕ} (D : WeightedDesign m dim)
    (C : Finset (Fin m)) (testVec : Fin dim → ℝ)
    (hnegative : (∑ c ∈ C, (D.atom c ⬝ᵥ testVec) ^ 2) < testVec ⬝ᵥ testVec) :
    ¬ Dominates D C :=
  fun hdominates =>
    absurd (sum_sq_ge_of_dominates hdominates testVec) (not_le.mpr hnegative)

/-- The three-atom reading: the sum over an explicit 3-subset unfolds to three squared
pairings, so each witness below is a `norm_num` computation on rationals. -/
theorem not_dominates_triple_of_negativeDirection {m dim : ℕ} (D : WeightedDesign m dim)
    (first second third : Fin m) (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (testVec : Fin dim → ℝ)
    (hnegative : (D.atom first ⬝ᵥ testVec) ^ 2 + (D.atom second ⬝ᵥ testVec) ^ 2
        + (D.atom third ⬝ᵥ testVec) ^ 2 < testVec ⬝ᵥ testVec) :
    ¬ Dominates D {first, second, third} := by
  refine not_dominates_of_negativeDirection D _ testVec ?_
  rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton]
  linarith [hnegative]

/-- **The twenty 3-subsets of `Fin 6`**, enumerated by decision — the finite index set
the good-selection bundle takes values in. -/
theorem finset_card_three_cases (C : Finset (Fin 6)) (hcard : C.card = 3) :
    C = {0, 1, 2} ∨ C = {0, 1, 3} ∨ C = {0, 1, 4} ∨ C = {0, 1, 5} ∨ C = {0, 2, 3} ∨
    C = {0, 2, 4} ∨ C = {0, 2, 5} ∨ C = {0, 3, 4} ∨ C = {0, 3, 5} ∨ C = {0, 4, 5} ∨
    C = {1, 2, 3} ∨ C = {1, 2, 4} ∨ C = {1, 2, 5} ∨ C = {1, 3, 4} ∨ C = {1, 3, 5} ∨
    C = {1, 4, 5} ∨ C = {2, 3, 4} ∨ C = {2, 3, 5} ∨ C = {2, 4, 5} ∨ C = {3, 4, 5} := by
  revert hcard
  revert C
  decide

/-! ## The good-selection set IS the domination mask

`liftingLemma_of_gtzWeighted` extracts the seven certificates at SOME atom of SOME
dominating subset. The refinement below supplies the pivot instead of obtaining it: any
nonzero atom of any dominating `(k+1)`-subset works, with the complementary subset forced
to be the rest. So a `(pivot, subset)` pair carries the certificates exactly when
`insert pivot subset` dominates and the pivot atom is nonzero — the 60-element index set
at `(6,3)` collapses to the 20-element domination mask, three pairs per dominating
subset. Everything below is therefore stated about `Dominates`. -/

/-- **Every nonzero atom of a dominating subset is a good pivot.** The Lifting Lemma's
certificates hold at `(pivot, g_pivot/|g_pivot|, deflator, C.erase pivot)` for EVERY
`pivot ∈ C` with `D.atom pivot ≠ 0` — the pivot is a hypothesis here, not a witness. -/
theorem liftingCertificates_of_dominates_atPivot {m k : ℕ}
    (D : WeightedDesign m (k + 1)) {C : Finset (Fin m)} (hcard : C.card = k + 1)
    (hdominates : Dominates D C) {pivot : Fin m} (hpivotMem : pivot ∈ C)
    (hpivotNonzero : D.atom pivot ≠ 0) :
    ∃ (pivotUnit : Fin (k + 1) → ℝ) (deflator : Matrix (Fin k) (Fin (k + 1)) ℝ),
      deflatorᵀ * deflator + atomMatrix pivotUnit = 1
      ∧ deflator *ᵥ D.atom pivot = 0
      ∧ pivot ∉ C.erase pivot
      ∧ (C.erase pivot).card = k
      ∧ (∀ testVec : Fin k → ℝ, testVec ⬝ᵥ testVec
          ≤ ∑ c ∈ C.erase pivot, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
      ∧ 0 ≤ (pivotUnit ⬝ᵥ D.atom pivot) ^ 2
          + (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1
      ∧ ∀ testVec : Fin k → ℝ,
          (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c)
              * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec)) ^ 2
            ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
                  + (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
                * ((∑ c ∈ C.erase pivot,
                    ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
                  - testVec ⬝ᵥ testVec) := by
  obtain ⟨scale, deflator, hscalePos, hcoisometry, hkill, hsplit, hunit⟩ :=
    exists_pivot_deflation D pivot hpivotNonzero
  set pivotUnit := scale • D.atom pivot with hpivotUnitDef
  have hkillUnit : deflator *ᵥ pivotUnit = 0 := by
    rw [hpivotUnitDef, Matrix.mulVec_smul, hkill, smul_zero]
  have hformNonneg : ∀ anyW : Fin (k + 1) → ℝ,
      0 ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
            + (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
          * (pivotUnit ⬝ᵥ anyW) ^ 2
        + 2 * (pivotUnit ⬝ᵥ anyW)
          * (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c)
              * ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)))
        + ((∑ c ∈ C.erase pivot,
            ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)) ^ 2)
          - (deflator *ᵥ anyW) ⬝ᵥ (deflator *ᵥ anyW)) := by
    intro anyW
    have hexpansion := bordered_form_eq D pivot hsplit hkill (C.erase pivot)
      (Finset.notMem_erase pivot C) anyW
    rw [Finset.insert_erase hpivotMem] at hexpansion
    have hcoercive := sum_sq_ge_of_dominates hdominates anyW
    rw [← subsetSum_form_eq_sum_sq] at hcoercive
    linarith [hexpansion, hcoercive]
  have hpivotOrthToLift : ∀ testVec : Fin k → ℝ,
      pivotUnit ⬝ᵥ (deflatorᵀ *ᵥ testVec) = 0 := by
    intro testVec
    rw [dotProduct_comm, dotProduct_mulVec_transpose, hkillUnit, dotProduct_zero]
  have hcoordRecover : ∀ (coordinate : ℝ) (testVec : Fin k → ℝ),
      pivotUnit ⬝ᵥ (deflatorᵀ *ᵥ testVec + coordinate • pivotUnit) = coordinate := by
    intro coordinate testVec
    rw [dotProduct_add, hpivotOrthToLift, dotProduct_smul, smul_eq_mul, hunit,
      mul_one, zero_add]
  have hprojRecover : ∀ (coordinate : ℝ) (testVec : Fin k → ℝ),
      deflator *ᵥ (deflatorᵀ *ᵥ testVec + coordinate • pivotUnit) = testVec := by
    intro coordinate testVec
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hcoisometry, Matrix.one_mulVec,
      Matrix.mulVec_smul, hkillUnit, smul_zero, add_zero]
  have hquadraticAll : ∀ (testVec : Fin k → ℝ) (coordinate : ℝ),
      0 ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
            + (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
          * coordinate ^ 2
        + 2 * coordinate
          * (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c)
              * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec))
        + ((∑ c ∈ C.erase pivot, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
          - testVec ⬝ᵥ testVec) := by
    intro testVec coordinate
    have hlifted := hformNonneg (deflatorᵀ *ᵥ testVec + coordinate • pivotUnit)
    rw [hcoordRecover coordinate testVec, hprojRecover coordinate testVec] at hlifted
    exact hlifted
  have hprojected : ∀ testVec : Fin k → ℝ, testVec ⬝ᵥ testVec
      ≤ ∑ c ∈ C.erase pivot, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2 := by
    intro testVec
    have hatZero := hquadraticAll testVec 0
    nlinarith [hatZero]
  have hfloor : 0 ≤ (pivotUnit ⬝ᵥ D.atom pivot) ^ 2
      + (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1 := by
    have hatOne := hquadraticAll 0 1
    simp only [dotProduct_zero, mul_zero, Finset.sum_const_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one, one_pow, add_zero,
      sub_zero] at hatOne
    nlinarith [hatOne]
  exact ⟨pivotUnit, deflator, hsplit, hkill, Finset.notMem_erase pivot C,
    by rw [Finset.card_erase_of_mem hpivotMem, hcard]; omega, hprojected, hfloor,
    fun testVec => discriminant_le_of_quadratic_nonneg hfloor (hquadraticAll testVec)⟩

/-! ## The heavy-pivot design: a rational `(6,3)` design with a UNIQUE dominating subset

Six atoms of denominator `5`, weights `(1/4, 1/36, 1/4, 1/4, 1/9, 1/9)`. The leverages
are `44/25, 216/25, 44/25, 76/25, 126/25, 126/25` — all exceed `1`, so the design sits
in the interior of the campaign's all-heavy stratum, and atom `1` is strictly the
heaviest. Exactly one of the twenty 3-subsets dominates, namely `{3, 4, 5}`, which does
not contain atom `1`. -/

/-- The six atoms, all of denominator `5`. -/
noncomputable def heavyPivotAtom : Fin 6 → Fin 3 → ℝ :=
  ![![(6/5), (2/5), (2/5)], ![-(6/5), (12/5), (6/5)], ![-(2/5), (2/5), -(6/5)],
    ![-(6/5), -(2/5), (6/5)], ![(6/5), -(9/5), (3/5)], ![(3/5), (9/5), (6/5)]]

/-- The exactly rational all-heavy `(6,3)` design whose ONLY dominating 3-subset is `{3, 4, 5}`. -/
noncomputable def heavyPivotDesign : WeightedDesign 6 3 where
  atom := heavyPivotAtom
  weight := ![1/4, 1/36, 1/4, 1/4, 1/9, 1/9]
  weight_pos := by intro c; fin_cases c <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, heavyPivotAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

/-- **The unique dominating subset dominates.** `50 · (S − I)` has quadratic form
`15(2x₀−x₁)² + 15(x₁+2x₂)² + 52x₀² + 252x₁² + 52x₂²`, a manifest sum of
squares; the eigenvalues of `S − I` are `51/25, 56/25, 146/25`. -/
theorem heavyPivotDesign_dominates_lastThree :
    Dominates heavyPivotDesign {3, 4, 5} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · have htranspose : (subsetSum heavyPivotDesign {3, 4, 5}
        - (1 : Matrix (Fin 3) (Fin 3) ℝ))ᵀ
        = subsetSum heavyPivotDesign {3, 4, 5} - 1 := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum,
        Matrix.transpose_sum]
      refine congrArg (· - 1) (Finset.sum_congr rfl fun c _ => ?_)
      ext a b
      simp [atomMatrix, Matrix.transpose_apply, Matrix.vecMulVec_apply,
        mul_comm]
    exact isHermitian_of_transpose_eq htranspose
  · rw [star_trivial, dominationGap_form,
      show ({3, 4, 5} : Finset (Fin 6)) = insert 3 (insert 4 {5}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    nlinarith [sq_nonneg (2 * x 0 - x 1), sq_nonneg (x 1 + 2 * x 2),
    sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

/-! ### The nineteen non-dominating subsets, each with an explicit integer direction -/

/-- Subset `{0, 1, 2}` fails: the direction `[-1, -1, 1]` has gap form `-3/25`. -/
theorem heavyPivotDesign_not_dominates_ZeroOneTwo :
    ¬ Dominates heavyPivotDesign {0, 1, 2} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 0 1 2
    (by decide) (by decide) (by decide) ![-1, -1, 1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

/-- Subset `{0, 1, 3}` fails: the direction `[-2, 1, -4]` has gap form `-1/5`. -/
theorem heavyPivotDesign_not_dominates_ZeroOneThree :
    ¬ Dominates heavyPivotDesign {0, 1, 3} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 0 1 3
    (by decide) (by decide) (by decide) ![-2, 1, -4] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons]
  norm_num

/-- Subset `{0, 1, 4}` fails: the direction `[-1, -1, 1]` has gap form `-3/25`. -/
theorem heavyPivotDesign_not_dominates_ZeroOneFour :
    ¬ Dominates heavyPivotDesign {0, 1, 4} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 0 1 4
    (by decide) (by decide) (by decide) ![-1, -1, 1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_four, Matrix.tail_cons]
  norm_num

/-- Subset `{0, 1, 5}` fails: the direction `[0, -1, 1]` has gap form `-1/5`. -/
theorem heavyPivotDesign_not_dominates_ZeroOneFive :
    ¬ Dominates heavyPivotDesign {0, 1, 5} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 0 1 5
    (by decide) (by decide) (by decide) ![0, -1, 1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- Subset `{0, 2, 3}` fails: the direction `[0, -1, 0]` has gap form `-13/25`. -/
theorem heavyPivotDesign_not_dominates_ZeroTwoThree :
    ¬ Dominates heavyPivotDesign {0, 2, 3} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 0 2 3
    (by decide) (by decide) (by decide) ![0, -1, 0] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons]
  norm_num

/-- Subset `{0, 2, 4}` fails: the direction `[-1, 0, 1]` has gap form `-9/25`. -/
theorem heavyPivotDesign_not_dominates_ZeroTwoFour :
    ¬ Dominates heavyPivotDesign {0, 2, 4} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 0 2 4
    (by decide) (by decide) (by decide) ![-1, 0, 1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_four, Matrix.tail_cons]
  norm_num

/-- Subset `{0, 2, 5}` fails: the direction `[-1, 0, 1]` has gap form `-9/25`. -/
theorem heavyPivotDesign_not_dominates_ZeroTwoFive :
    ¬ Dominates heavyPivotDesign {0, 2, 5} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 0 2 5
    (by decide) (by decide) (by decide) ![-1, 0, 1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- Subset `{0, 3, 4}` fails: the direction `[-1, -2, -3]` has gap form `-21/25`. -/
theorem heavyPivotDesign_not_dominates_ZeroThreeFour :
    ¬ Dominates heavyPivotDesign {0, 3, 4} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 0 3 4
    (by decide) (by decide) (by decide) ![-1, -2, -3] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  norm_num

/-- Subset `{0, 3, 5}` fails: the direction `[-1, 1, -1]` has gap form `-7/5`. -/
theorem heavyPivotDesign_not_dominates_ZeroThreeFive :
    ¬ Dominates heavyPivotDesign {0, 3, 5} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 0 3 5
    (by decide) (by decide) (by decide) ![-1, 1, -1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- Subset `{0, 4, 5}` fails: the direction `[-1, 0, 1]` has gap form `-16/25`. -/
theorem heavyPivotDesign_not_dominates_ZeroFourFive :
    ¬ Dominates heavyPivotDesign {0, 4, 5} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 0 4 5
    (by decide) (by decide) (by decide) ![-1, 0, 1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- Subset `{1, 2, 3}` fails: the direction `[-4, -1, -2]` has gap form `-1/5`. -/
theorem heavyPivotDesign_not_dominates_OneTwoThree :
    ¬ Dominates heavyPivotDesign {1, 2, 3} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 1 2 3
    (by decide) (by decide) (by decide) ![-4, -1, -2] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons]
  norm_num

/-- Subset `{1, 2, 4}` fails: the direction `[-1, -1, 0]` has gap form `-1/5`. -/
theorem heavyPivotDesign_not_dominates_OneTwoFour :
    ¬ Dominates heavyPivotDesign {1, 2, 4} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 1 2 4
    (by decide) (by decide) (by decide) ![-1, -1, 0] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_four, Matrix.tail_cons]
  norm_num

/-- Subset `{1, 2, 5}` fails: the direction `[-1, -1, 1]` has gap form `-3/25`. -/
theorem heavyPivotDesign_not_dominates_OneTwoFive :
    ¬ Dominates heavyPivotDesign {1, 2, 5} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 1 2 5
    (by decide) (by decide) (by decide) ![-1, -1, 1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- Subset `{1, 3, 4}` fails: the direction `[-2, -1, -1]` has gap form `-14/25`. -/
theorem heavyPivotDesign_not_dominates_OneThreeFour :
    ¬ Dominates heavyPivotDesign {1, 3, 4} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 1 3 4
    (by decide) (by decide) (by decide) ![-2, -1, -1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  norm_num

/-- Subset `{1, 3, 5}` fails: the direction `[-1, 1, -2]` has gap form `-14/25`. -/
theorem heavyPivotDesign_not_dominates_OneThreeFive :
    ¬ Dominates heavyPivotDesign {1, 3, 5} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 1 3 5
    (by decide) (by decide) (by decide) ![-1, 1, -2] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- Subset `{1, 4, 5}` fails: the direction `[-1, -1, 1]` has gap form `-3/25`. -/
theorem heavyPivotDesign_not_dominates_OneFourFive :
    ¬ Dominates heavyPivotDesign {1, 4, 5} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 1 4 5
    (by decide) (by decide) (by decide) ![-1, -1, 1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- Subset `{2, 3, 4}` fails: the direction `[-1, -1, -1]` has gap form `-7/5`. -/
theorem heavyPivotDesign_not_dominates_TwoThreeFour :
    ¬ Dominates heavyPivotDesign {2, 3, 4} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 2 3 4
    (by decide) (by decide) (by decide) ![-1, -1, -1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  norm_num

/-- Subset `{2, 3, 5}` fails: the direction `[-3, 2, -1]` has gap form `-21/25`. -/
theorem heavyPivotDesign_not_dominates_TwoThreeFive :
    ¬ Dominates heavyPivotDesign {2, 3, 5} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 2 3 5
    (by decide) (by decide) (by decide) ![-3, 2, -1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- Subset `{2, 4, 5}` fails: the direction `[-1, 0, 1]` has gap form `-16/25`. -/
theorem heavyPivotDesign_not_dominates_TwoFourFive :
    ¬ Dominates heavyPivotDesign {2, 4, 5} := by
  refine not_dominates_triple_of_negativeDirection heavyPivotDesign 2 4 5
    (by decide) (by decide) (by decide) ![-1, 0, 1] ?_
  simp only [heavyPivotDesign, heavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-- **The domination mask, completely determined**: at `heavyPivotDesign` a
3-subset dominates if and only if it is `{3, 4, 5}`. Nineteen explicit
directions and one sum of squares decide all twenty cases, so `Dom(D)` is a
singleton — the good-selection set is as small as it can be while nonempty. -/
theorem heavyPivotDesign_dominates_iff (C : Finset (Fin 6)) (hcard : C.card = 3) :
    Dominates heavyPivotDesign C ↔ C = {3, 4, 5} := by
  constructor
  · intro hdominates
    rcases finset_card_three_cases C hcard with
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h <;> subst h
    · exact absurd hdominates heavyPivotDesign_not_dominates_ZeroOneTwo
    · exact absurd hdominates heavyPivotDesign_not_dominates_ZeroOneThree
    · exact absurd hdominates heavyPivotDesign_not_dominates_ZeroOneFour
    · exact absurd hdominates heavyPivotDesign_not_dominates_ZeroOneFive
    · exact absurd hdominates heavyPivotDesign_not_dominates_ZeroTwoThree
    · exact absurd hdominates heavyPivotDesign_not_dominates_ZeroTwoFour
    · exact absurd hdominates heavyPivotDesign_not_dominates_ZeroTwoFive
    · exact absurd hdominates heavyPivotDesign_not_dominates_ZeroThreeFour
    · exact absurd hdominates heavyPivotDesign_not_dominates_ZeroThreeFive
    · exact absurd hdominates heavyPivotDesign_not_dominates_ZeroFourFive
    · exact absurd hdominates heavyPivotDesign_not_dominates_OneTwoThree
    · exact absurd hdominates heavyPivotDesign_not_dominates_OneTwoFour
    · exact absurd hdominates heavyPivotDesign_not_dominates_OneTwoFive
    · exact absurd hdominates heavyPivotDesign_not_dominates_OneThreeFour
    · exact absurd hdominates heavyPivotDesign_not_dominates_OneThreeFive
    · exact absurd hdominates heavyPivotDesign_not_dominates_OneFourFive
    · exact absurd hdominates heavyPivotDesign_not_dominates_TwoThreeFour
    · exact absurd hdominates heavyPivotDesign_not_dominates_TwoThreeFive
    · exact absurd hdominates heavyPivotDesign_not_dominates_TwoFourFive
    · rfl
  · rintro rfl
    exact heavyPivotDesign_dominates_lastThree

/-- The leverage of atom `1` is `216/25`, the largest in the design. -/
theorem heavyPivotDesign_leverage_one :
    leverageOf (heavyPivotDesign.atom 1) = 216 / 25 := by
    simp only [heavyPivotDesign, heavyPivotAtom, leverageOf,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    norm_num

/-- Atom `1` is STRICTLY the heaviest: the six leverages are
`44/25, 216/25, 44/25, 76/25, 126/25, 126/25`. -/
theorem heavyPivotDesign_leverage_lt_one (other : Fin 6) (hother : other ≠ 1) :
    leverageOf (heavyPivotDesign.atom other)
      < leverageOf (heavyPivotDesign.atom 1) := by
  rw [heavyPivotDesign_leverage_one]
  have hcases : other = 0 ∨ other = 2 ∨ other = 3 ∨ other = 4 ∨ other = 5 := by
    revert hother
    revert other
    decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [heavyPivotDesign, heavyPivotAtom, leverageOf,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num

/-! ## A second design: the same atoms, relabelled

Rotating the atom indices by three moves the unique dominating subset from `{3, 4, 5}`
to `{0, 1, 2}`. Two designs, disjoint domination masks. -/

/-- The heavy-pivot atoms with indices rotated by three. -/
noncomputable def rotatedHeavyPivotAtom : Fin 6 → Fin 3 → ℝ :=
  ![![-(6/5), -(2/5), (6/5)], ![(6/5), -(9/5), (3/5)], ![(3/5), (9/5), (6/5)],
    ![(6/5), (2/5), (2/5)], ![-(6/5), (12/5), (6/5)], ![-(2/5), (2/5), -(6/5)]]

/-- The relabelled heavy-pivot design; its unique dominating subset is `{0, 1, 2}`. -/
noncomputable def rotatedHeavyPivotDesign : WeightedDesign 6 3 where
  atom := rotatedHeavyPivotAtom
  weight := ![1/4, 1/9, 1/9, 1/4, 1/36, 1/4]
  weight_pos := by intro c; fin_cases c <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, rotatedHeavyPivotAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

/-- The rotated design dominates on `{0, 1, 2}` — the image of `{3, 4, 5}`. -/
theorem rotatedHeavyPivotDesign_dominates_firstThree :
    Dominates rotatedHeavyPivotDesign {0, 1, 2} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · have htranspose : (subsetSum rotatedHeavyPivotDesign {0, 1, 2}
        - (1 : Matrix (Fin 3) (Fin 3) ℝ))ᵀ
        = subsetSum rotatedHeavyPivotDesign {0, 1, 2} - 1 := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum,
        Matrix.transpose_sum]
      refine congrArg (· - 1) (Finset.sum_congr rfl fun c _ => ?_)
      ext a b
      simp [atomMatrix, Matrix.transpose_apply, Matrix.vecMulVec_apply,
        mul_comm]
    exact isHermitian_of_transpose_eq htranspose
  · rw [star_trivial, dominationGap_form,
      show ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 {2}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp only [rotatedHeavyPivotDesign, rotatedHeavyPivotAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    nlinarith [sq_nonneg (2 * x 0 - x 1), sq_nonneg (x 1 + 2 * x 2),
    sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

/-- The rotated design does NOT dominate on `{3, 4, 5}`, the subset
`heavyPivotDesign` uniquely dominates. The direction `[-1, -1, 1]` has gap
form `-3/25`. -/
theorem rotatedHeavyPivotDesign_not_dominates_lastThree :
    ¬ Dominates rotatedHeavyPivotDesign {3, 4, 5} := by
  refine not_dominates_triple_of_negativeDirection rotatedHeavyPivotDesign 3 4 5
    (by decide) (by decide) (by decide) ![-1, -1, 1] ?_
  simp only [rotatedHeavyPivotDesign, rotatedHeavyPivotAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  norm_num

/-! ## Sense 1: no constant, hence no continuous, selector -/

/-- **NO UNIVERSAL DOMINATING SUBSET.** No 3-subset of `Fin 6` dominates at every
weighted `(6,3)` design. Two explicit rational designs decide all twenty cases. -/
theorem no_universal_dominating_subset :
    ¬ ∃ C : Finset (Fin 6), C.card = 3 ∧ ∀ D : WeightedDesign 6 3, Dominates D C := by
  rintro ⟨C, hcard, huniversal⟩
  by_cases hlast : C = {3, 4, 5}
  · subst hlast
    exact rotatedHeavyPivotDesign_not_dominates_lastThree
      (huniversal rotatedHeavyPivotDesign)
  · exact hlast
      ((heavyPivotDesign_dominates_iff C hcard).mp (huniversal heavyPivotDesign))

/-- **NO UNIVERSAL GOOD PAIR** — the Lifting-Lemma-shaped reading. None of the sixty
`(pivot, subset)` combinations available at `(6,3)` yields a dominating
`insert pivot subset` at every design. Together with connectedness of the design space
and finiteness of the index set (both classical, neither mechanized here) this is
exactly the statement that no CONTINUOUS selector `D ↦ (pivot, subset)` exists. -/
theorem no_universal_goodPair :
    ¬ ∃ (pivot : Fin 6) (subset : Finset (Fin 6)),
        pivot ∉ subset ∧ subset.card = 2
        ∧ ∀ D : WeightedDesign 6 3, Dominates D (insert pivot subset) := by
  rintro ⟨pivot, subset, hnotMem, hcard, huniversal⟩
  exact no_universal_dominating_subset
    ⟨insert pivot subset, by rw [Finset.card_insert_of_notMem hnotMem, hcard],
      huniversal⟩

/-- **Two designs sharing NO good subset.** The discrete shadow of "selection is
global": along any path joining these two designs a chosen dominating subset must be
abandoned, because no subset is good at both ends. -/
theorem exists_designs_with_disjoint_dominationSets :
    ∃ designOne designTwo : WeightedDesign 6 3,
      (∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates designOne C)
      ∧ (∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates designTwo C)
      ∧ ∀ C : Finset (Fin 6), C.card = 3
          → ¬ (Dominates designOne C ∧ Dominates designTwo C) := by
  refine ⟨heavyPivotDesign, rotatedHeavyPivotDesign,
    ⟨{3, 4, 5}, by decide, heavyPivotDesign_dominates_lastThree⟩,
    ⟨{0, 1, 2}, by decide, rotatedHeavyPivotDesign_dominates_firstThree⟩,
    fun C hcard hboth => ?_⟩
  have hlast : C = {3, 4, 5} := (heavyPivotDesign_dominates_iff C hcard).mp hboth.1
  subst hlast
  exact rotatedHeavyPivotDesign_not_dominates_lastThree hboth.2

/-- **THE HEAVIEST-ATOM RULE IS REFUTED, with an explicit rational witness.** At
`heavyPivotDesign` the atom of strictly greatest leverage lies in NO dominating 3-subset,
while a dominating 3-subset exists. Any pivot rule that selects the heaviest atom — the
campaign's `top-1` rule — therefore fails, and fails on the interior of the all-heavy
stratum (every leverage exceeds `1`, and the winning margin is
`λ_min(S_{3,4,5}) − 1 = 51/25`), not at a tie or a boundary. -/
theorem heaviest_atom_can_lie_outside_every_dominatingSubset :
    ∃ (D : WeightedDesign 6 3) (heaviest : Fin 6),
      (∀ other : Fin 6, other ≠ heaviest
        → leverageOf (D.atom other) < leverageOf (D.atom heaviest))
      ∧ (∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C)
      ∧ (∀ C : Finset (Fin 6), C.card = 3 → heaviest ∈ C → ¬ Dominates D C) := by
  refine ⟨heavyPivotDesign, 1, heavyPivotDesign_leverage_lt_one,
    ⟨{3, 4, 5}, by decide, heavyPivotDesign_dominates_lastThree⟩,
    fun C hcard hmem hdominates => ?_⟩
  have hlast : C = {3, 4, 5} := (heavyPivotDesign_dominates_iff C hcard).mp hdominates
  subst hlast
  exact absurd hmem (by decide)

/-! ## Sense 2: no label-free selector

Relabelling atom indices is a symmetry of the whole problem: it permutes atoms and
weights together and carries dominating subsets to dominating subsets. A selector
computed without reference to the arbitrary atom indices must commute with it, so at a
design fixed by a relabelling it must return a subset fixed by that relabelling. -/

/-- **The relabelling action on designs**: permute atoms and weights together. -/
noncomputable def relabelDesign {m k : ℕ} (D : WeightedDesign m k)
    (relabel : Equiv.Perm (Fin m)) : WeightedDesign m k where
  atom index := D.atom (relabel index)
  weight index := D.weight (relabel index)
  weight_pos index := D.weight_pos (relabel index)
  weight_sum_one := by
    rw [Equiv.sum_comp relabel D.weight]
    exact D.weight_sum_one
  isParseval := by
    rw [Equiv.sum_comp relabel fun index => D.weight index • atomMatrix (D.atom index)]
    exact D.isParseval

/-- Relabelling transports subset sums along the permutation. -/
theorem subsetSum_relabelDesign {m k : ℕ} (D : WeightedDesign m k)
    (relabel : Equiv.Perm (Fin m)) (C : Finset (Fin m)) :
    subsetSum (relabelDesign D relabel) C
      = subsetSum D (C.map relabel.toEmbedding) := by
  rw [subsetSum, subsetSum, Finset.sum_map]
  rfl

/-- **Domination is relabelling-equivariant.** -/
theorem dominates_relabelDesign_iff {m k : ℕ} (D : WeightedDesign m k)
    (relabel : Equiv.Perm (Fin m)) (C : Finset (Fin m)) :
    Dominates (relabelDesign D relabel) C
      ↔ Dominates D (C.map relabel.toEmbedding) := by
  rw [Dominates, Dominates, subsetSum_relabelDesign]

/-- The four simplex directions with the first and the fourth doubled: atoms `0, 1` coincide and atoms `3, 4` coincide. -/
noncomputable def doubledTetrahedronAtom : Fin 6 → Fin 3 → ℝ :=
  ![![1, 1, 1], ![1, 1, 1], ![1, -1, -1],
    ![-1, 1, -1], ![-1, 1, -1], ![-1, -1, 1]]

/-- The `(6,3)` design got by splitting two atoms of the simplex `(4,3)` design into equal-weight copies. -/
noncomputable def doubledTetrahedronDesign : WeightedDesign 6 3 where
  atom := doubledTetrahedronAtom
  weight := ![1/8, 1/8, 1/4, 1/8, 1/8, 1/4]
  weight_pos := by intro c; fin_cases c <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, doubledTetrahedronAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

/-- The doubled tetrahedron DOES dominate on `{0, 2, 3}`: the gap form is
`(x₀−x₁)² + (x₀+x₂)² + (x₁+x₂)²`. -/
theorem doubledTetrahedron_dominates_zeroTwoThree :
    Dominates doubledTetrahedronDesign {0, 2, 3} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · have htranspose : (subsetSum doubledTetrahedronDesign {0, 2, 3}
        - (1 : Matrix (Fin 3) (Fin 3) ℝ))ᵀ
        = subsetSum doubledTetrahedronDesign {0, 2, 3} - 1 := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum,
        Matrix.transpose_sum]
      refine congrArg (· - 1) (Finset.sum_congr rfl fun c _ => ?_)
      ext a b
      simp [atomMatrix, Matrix.transpose_apply, Matrix.vecMulVec_apply,
        mul_comm]
    exact isHermitian_of_transpose_eq htranspose
  · rw [star_trivial, dominationGap_form,
      show ({0, 2, 3} : Finset (Fin 6)) = insert 0 (insert 2 {3}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp only [doubledTetrahedronDesign, doubledTetrahedronAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 2), sq_nonneg (x 1 + x 2)]

/-- A 3-subset containing the repeated pair `{0, 1}` never dominates — the shipped
`not_dominates_of_repeated_atom` at this design. -/
theorem doubledTetrahedron_zeroOnePair_not_dominates (third : Fin 6)
    (hzero : (0 : Fin 6) ≠ third) (hone : (1 : Fin 6) ≠ third) :
    ¬ Dominates doubledTetrahedronDesign {0, 1, third} :=
  not_dominates_of_repeated_atom doubledTetrahedronDesign (by decide) hzero hone rfl

/-- A 3-subset containing the repeated pair `{3, 4}` never dominates. -/
theorem doubledTetrahedron_threeFourPair_not_dominates (third : Fin 6)
    (hthree : (3 : Fin 6) ≠ third) (hfour : (4 : Fin 6) ≠ third) :
    ¬ Dominates doubledTetrahedronDesign {3, 4, third} :=
  not_dominates_of_repeated_atom doubledTetrahedronDesign (by decide) hthree hfour rfl

/-- **No subset invariant under the doubled-tetrahedron symmetry dominates.** A 3-subset
invariant under `(0 1)(3 4)` is a union of orbits of sizes `2, 2, 1, 1`, so it is one of
`{0,1,2}`, `{0,1,5}`, `{2,3,4}`, `{3,4,5}` — and each of those contains a repeated atom,
so its moment has rank at most two and cannot majorize the identity in `ℝ³`. The other
sixteen 3-subsets are not invariant, and the two membership hypotheses refute each. -/
theorem doubledTetrahedron_invariantSubset_not_dominates (C : Finset (Fin 6))
    (hcard : C.card = 3) (hzeroOne : (0 : Fin 6) ∈ C ↔ (1 : Fin 6) ∈ C)
    (hthreeFour : (3 : Fin 6) ∈ C ↔ (4 : Fin 6) ∈ C) :
    ¬ Dominates doubledTetrahedronDesign C := by
  rcases finset_card_three_cases C hcard with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h
  · exact doubledTetrahedron_zeroOnePair_not_dominates 2 (by decide) (by decide)
  · exact absurd hthreeFour (by decide)
  · exact absurd hthreeFour (by decide)
  · exact doubledTetrahedron_zeroOnePair_not_dominates 5 (by decide) (by decide)
  · exact absurd hzeroOne (by decide)
  · exact absurd hzeroOne (by decide)
  · exact absurd hzeroOne (by decide)
  · exact absurd hzeroOne (by decide)
  · exact absurd hzeroOne (by decide)
  · exact absurd hzeroOne (by decide)
  · exact absurd hzeroOne (by decide)
  · exact absurd hzeroOne (by decide)
  · exact absurd hzeroOne (by decide)
  · exact absurd hzeroOne (by decide)
  · exact absurd hzeroOne (by decide)
  · exact absurd hzeroOne (by decide)
  · rw [show ({2, 3, 4} : Finset (Fin 6)) = {3, 4, 2} from by decide]
    exact doubledTetrahedron_threeFourPair_not_dominates 2 (by decide) (by decide)
  · exact absurd hthreeFour (by decide)
  · exact absurd hthreeFour (by decide)
  · exact doubledTetrahedron_threeFourPair_not_dominates 5 (by decide) (by decide)

/-- The double transposition `(0 1)(3 4)` on `Fin 6` — the symmetry of the
doubled-tetrahedron design. -/
def doubleTransposition : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 1).trans (Equiv.swap 3 4)

/-- It swaps `0` with `1`. -/
theorem doubleTransposition_zero : doubleTransposition 0 = 1 := by decide

/-- It swaps `1` back to `0`. -/
theorem doubleTransposition_one : doubleTransposition 1 = 0 := by decide

/-- It fixes `2`. -/
theorem doubleTransposition_two : doubleTransposition 2 = 2 := by decide

/-- It swaps `3` with `4`. -/
theorem doubleTransposition_three : doubleTransposition 3 = 4 := by decide

/-- It swaps `4` back to `3`. -/
theorem doubleTransposition_four : doubleTransposition 4 = 3 := by decide

/-- It fixes `5`. -/
theorem doubleTransposition_five : doubleTransposition 5 = 5 := by decide

/-- It is not the identity. -/
theorem doubleTransposition_ne_one : doubleTransposition ≠ 1 := by
  intro hidentity
  have hzero : doubleTransposition 0 = (1 : Equiv.Perm (Fin 6)) 0 := by rw [hidentity]
  revert hzero
  decide

/-- The doubled-tetrahedron atoms are invariant under the symmetry. -/
theorem doubledTetrahedron_atom_invariant (c : Fin 6) :
    doubledTetrahedronDesign.atom (doubleTransposition c)
      = doubledTetrahedronDesign.atom c := by
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by
    revert c
    decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [doubleTransposition_zero, doubleTransposition_one,
      doubleTransposition_two, doubleTransposition_three, doubleTransposition_four,
      doubleTransposition_five, doubledTetrahedronDesign, doubledTetrahedronAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]

/-- The doubled-tetrahedron weights are invariant under the symmetry. -/
theorem doubledTetrahedron_weight_invariant (c : Fin 6) :
    doubledTetrahedronDesign.weight (doubleTransposition c)
      = doubledTetrahedronDesign.weight c := by
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by
    revert c
    decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [doubleTransposition_zero, doubleTransposition_one,
      doubleTransposition_two, doubleTransposition_three, doubleTransposition_four,
      doubleTransposition_five, doubledTetrahedronDesign, doubledTetrahedronAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]

/-- **NO LABEL-FREE SELECTOR.** There is a weighted `(6,3)` design and a nontrivial
relabelling that fixes it atom-for-atom and weight-for-weight, such that a dominating
3-subset exists but NO relabelling-invariant 3-subset dominates. Any selection rule
computed from relabelling-invariant data must return an invariant subset at this design,
hence must fail there. This is the precise sense in which the campaign's whole refuted
catalogue — heaviest atom, largest total leverage, maximum determinant, minimum
coherence, Seidel sign, volume sampling — was bound to fail: every one of those rules is
label-free. -/
theorem exists_symmetry_with_no_fixed_dominatingSubset :
    ∃ (D : WeightedDesign 6 3) (relabel : Equiv.Perm (Fin 6)),
      relabel ≠ 1
      ∧ (∀ c : Fin 6, D.atom (relabel c) = D.atom c)
      ∧ (∀ c : Fin 6, D.weight (relabel c) = D.weight c)
      ∧ (∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C)
      ∧ (∀ C : Finset (Fin 6), C.card = 3 → (∀ c : Fin 6, c ∈ C ↔ relabel c ∈ C)
          → ¬ Dominates D C) := by
  refine ⟨doubledTetrahedronDesign, doubleTransposition, doubleTransposition_ne_one,
    doubledTetrahedron_atom_invariant, doubledTetrahedron_weight_invariant,
    ⟨{0, 2, 3}, by decide, doubledTetrahedron_dominates_zeroTwoThree⟩,
    fun C hcard hinvariant => ?_⟩
  refine doubledTetrahedron_invariantSubset_not_dominates C hcard ?_ ?_
  · have hzero := hinvariant 0
    rwa [doubleTransposition_zero] at hzero
  · have hthree := hinvariant 3
    rwa [doubleTransposition_three] at hthree

end Gtz
