import Gtz.Design.LineClassObstructions
import Gtz.Design.OneDeterminantReduction
import Gtz.Quantitative.DesignQuadraticFloors
import Gtz.LinAlg.SchurRankOne
import Gtz.Reduction.RayleighCertificate
import Gtz.Core.Sanity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The canonical free triple of the one-line stratum can fail

Every chartless certificate written so far nominates the SAME triple: the
complement `{3,4,5}` of the line.  That triple is handed one free Sylvester
condition (`Gtz.oneLine_freeTriple_strictly_overcovers_normal`), which makes it a
natural candidate, and the shipped member `Gtz.oneLineSampleDesign` confirms it
by having `{3,4,5}` strictly dominating.

This file REFUTES the nomination.  `Gtz.oneLineFailureDesign` is a one-line
stratum member -- exact rational atoms, exact rational weights, Parseval on the
nose -- that is HEAVY and carries a weakly dominating triple, and on which
`{3,4,5}` does not merely fail to dominate strictly: it fails to dominate at all.
The probe `(1, -1, 1/10)` sees a strictly negative gap.

Consequences for the campaign.

* Any residual of the form "the canonical free triple is Lagrange-dominating"
  has a genuinely nonempty complement on the stratum; that hypothesis is FALSE
  somewhere, so a certificate for `Gtz.PatternHeavyWeakToStrict` at the one-line
  pattern must branch and nominate a different triple.
* The design still satisfies the conclusion: `{2,3,5}` and `{2,4,5}` are both
  strictly dominating.  So this refutes the STRATEGY, not the obligation.
* The winning triples both mix one line atom with two free atoms.  The free atom
  `5` is in both; the line atom `2` is the one line atom that is not a coordinate
  axis.
-/

namespace Gtz

open Matrix

/-- Three line atoms in the horizontal plane and three free atoms off it. -/
noncomputable def oneLineFailureAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![2, -2, 0]
  | 3 => ![1, 0, 1]
  | 4 => ![0, 1, 4]
  | 5 => ![-1, -1, 1 / 2]

/-- Exact elevenths and twenty-seconds. -/
noncomputable def oneLineFailureWeight : Fin 6 → ℝ
  | 0 => 1 / 11
  | 1 => 5 / 22
  | 2 => 1 / 11
  | 3 => 2 / 11
  | 4 => 1 / 22
  | 5 => 4 / 11

/-- **The refuting one-line design.**  Parseval holds exactly. -/
noncomputable def oneLineFailureDesign : WeightedDesign 6 3 where
  atom := oneLineFailureAtom
  weight := oneLineFailureWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [oneLineFailureWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [oneLineFailureWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [oneLineFailureAtom, oneLineFailureWeight, atomMatrix] <;> norm_num

/-- The design sits on the one-line stratum: `{0,1,2}` is its ONLY dependent
triple, so no two atoms are parallel and every free triple is independent. -/
theorem oneLineFailureDesign_hasLinePattern :
    HasLinePattern oneLineFailureDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, oneLineFailureDesign,
            oneLineFailureAtom, Matrix.cons_val_two])
          (by decide)
      | exact iff_of_true
          (by norm_num [atomBracket, tripleBracket_eq, oneLineFailureDesign,
            oneLineFailureAtom, Matrix.cons_val_two])
          (by decide)

/-- Every atom is heavy. -/
theorem oneLineFailureDesign_allHeavy (label : Fin 6) :
    1 ≤ leverageOf (oneLineFailureDesign.atom label) := by
  fin_cases label <;>
    norm_num [leverageOf, Fin.sum_univ_three, oneLineFailureDesign, oneLineFailureAtom,
      Matrix.cons_val_two]

/-! ## The winning triple `{2,3,5}` -/

/-- The gap of `{2,3,5}` as an explicit sum of three squares.  The coefficients
`5`, `11/5`, `2/11` multiply out to the determinant `2`. -/
theorem oneLineFailure_dominatorGap_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ ((subsetSum oneLineFailureDesign {2, 3, 5} - 1) *ᵥ probeVec)
      = 5 * (probeVec 0 - 3 / 5 * probeVec 1 + 1 / 10 * probeVec 2) ^ 2
        + 11 / 5 * (probeVec 1 - 1 / 11 * probeVec 2) ^ 2
        + 2 / 11 * probeVec 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [oneLineFailureDesign, oneLineFailureAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

/-- `{2,3,5}` dominates. -/
theorem oneLineFailure_dominates_mixedTriple :
    Dominates oneLineFailureDesign {2, 3, 5} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one oneLineFailureDesign _),
      fun probeVec => ?_⟩
  rw [star_trivial, oneLineFailure_dominatorGap_form]
  positivity

/-- So the design carries a weakly dominating card-three subset -- the antecedent
of `Gtz.PatternHeavyWeakToStrict` is met. -/
theorem oneLineFailureDesign_hasWeakDominator :
    ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧
      Dominates oneLineFailureDesign dominator :=
  ⟨{2, 3, 5}, by decide, oneLineFailure_dominates_mixedTriple⟩

/-! ## The canonical free triple fails -/

/-- The free triple's gap at the probe `(1, -1, 1/10)` is `-7/16`. -/
theorem oneLineFailure_freeTripleGap_at_witness :
    (![1, -1, 1 / 10] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum oneLineFailureDesign {3, 4, 5} - 1) *ᵥ ![1, -1, 1 / 10])
      = -7 / 16 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [oneLineFailureDesign, oneLineFailureAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-- **The canonical free triple does not even dominate weakly.** -/
theorem oneLineFailure_freeTriple_not_dominates :
    ¬ Dominates oneLineFailureDesign {3, 4, 5} := by
  intro hdominates
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2
    (![1, -1, 1 / 10] : Fin 3 → ℝ)
  rw [star_trivial, oneLineFailure_freeTripleGap_at_witness] at hnonneg
  norm_num at hnonneg

/-- A fortiori it does not dominate strictly. -/
theorem oneLineFailure_freeTripleGap_not_posDef :
    ¬ (subsetSum oneLineFailureDesign {3, 4, 5} - 1).PosDef := fun hposDef =>
  oneLineFailure_freeTriple_not_dominates hposDef.posSemidef

/-- **Where the plane-Schur criterion fails on this design.**  Take the line
normal `(0,0,1)` and the horizontal probe `(1,-1,0)`.  The criterion's left side
is `9` and its right side is `0`, because that probe is a null direction of the
free triple's gap: the free atoms `3` and `4` read it with opposite signs while
atom `5` is blind to it.  This is an exact witness for the residual branch of
`Gtz.oneLine_freeTriple_posDef_iff_planeSchur`. -/
theorem oneLineFailure_planeSchurCrossTerm_eq :
    (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
        (oneLineFailureDesign.atom freeLabel ⬝ᵥ ![1, -1, 0])
          * (oneLineFailureDesign.atom freeLabel ⬝ᵥ ![0, 0, 1])) ^ 2 = 9 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [oneLineFailureDesign, oneLineFailureAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-- The right side of the same inequality is `0`: the horizontal probe is a null
direction of the free triple's gap. -/
theorem oneLineFailure_planeSchurProduct_eq :
    ((∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
        (oneLineFailureDesign.atom freeLabel ⬝ᵥ ![0, 0, 1]) ^ 2)
      - (![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ ![0, 0, 1])
      * ((∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
          (oneLineFailureDesign.atom freeLabel ⬝ᵥ ![1, -1, 0]) ^ 2)
          - (![1, -1, 0] : Fin 3 → ℝ) ⬝ᵥ ![1, -1, 0]) = 0 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [oneLineFailureDesign, oneLineFailureAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-! ## The refutation, packaged -/

/-- **REFUTATION.**  There is a HEAVY one-line-stratum design carrying a weakly
dominating card-three subset on which the canonical free triple `{3,4,5}` fails
to dominate.  Every certificate that nominates `{3,4,5}` unconditionally on this
stratum is therefore false; a proof of `Gtz.PatternHeavyWeakToStrict` at the
one-line pattern must branch. -/
theorem exists_oneLine_heavy_weaklyDominated_freeTriple_not_dominates :
    ∃ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) ∧
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) ∧
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) ∧
      ¬ Dominates design {3, 4, 5} :=
  ⟨oneLineFailureDesign, oneLineFailureDesign_hasLinePattern,
    oneLineFailureDesign_allHeavy, oneLineFailureDesign_hasWeakDominator,
    oneLineFailure_freeTriple_not_dominates⟩

/-- The obligation's CONCLUSION still holds on the refuting design: `{2,3,5}` is
strictly dominating.  So the counterexample refutes the canonical-triple
strategy, never the obligation. -/
theorem oneLineFailure_mixedTripleGap_posDef :
    (subsetSum oneLineFailureDesign {2, 3, 5} - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one oneLineFailureDesign _),
      fun probeVec hprobeNe => ?_⟩
  rw [star_trivial, oneLineFailure_dominatorGap_form]
  by_contra hnonpos
  push Not at hnonpos
  have hfirstSq := sq_nonneg (probeVec 0 - 3 / 5 * probeVec 1 + 1 / 10 * probeVec 2)
  have hsecondSq := sq_nonneg (probeVec 1 - 1 / 11 * probeVec 2)
  have hthirdSq := sq_nonneg (probeVec 2)
  have hthirdZero : probeVec 2 = 0 := sq_eq_zero_iff.mp (by linarith)
  have hsecondZero : probeVec 1 = 0 := by
    have hshifted : probeVec 1 - 1 / 11 * probeVec 2 = 0 := sq_eq_zero_iff.mp (by linarith)
    rw [hthirdZero] at hshifted
    linarith
  have hfirstZero : probeVec 0 = 0 := by
    have hshifted : probeVec 0 - 3 / 5 * probeVec 1 + 1 / 10 * probeVec 2 = 0 :=
      sq_eq_zero_iff.mp (by linarith)
    rw [hthirdZero, hsecondZero] at hshifted
    linarith
  exact hprobeNe (eq_zero_of_coordinates_eq_zero hfirstZero hsecondZero hthirdZero)

end Gtz
