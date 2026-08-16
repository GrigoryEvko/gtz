/-
# The free-mass budget misses the K4 star

`Gtz.posDef_gap_of_freeMassBudget` is one of the two arms of
`Gtz.HasStrictCertificate`: a subset whose outside labels spend less than one unit
of free mass against the base deficit dominates strictly.  On branch (i) that arm is
the one whose slack runs to zero at the deepest near-ties, so it is the natural
candidate for a covering criterion.

It does not cover.  This module exhibits the K4 edge design — the six root
directions of `A3`, at uniform weight — which is STRESS-FREE, and whose four vertex
stars dominate STRICTLY while spending free mass `6/5`.  The certificate is blind
there, and the design is not a boundary point: every weight is `1/6`, every share is
`1/2`, every leverage is `3`.

The star gap is exactly `Gtz.rootStarGap`, the repository's own two-invariant
calibration matrix, so the witness is anchored to landed content.

## What is proved here

* `Gtz.kFourDesign` — the K4 edge design at uniform weight.
* `Gtz.kFourDesign_stressFree` — it lies on branch (i).
* `Gtz.subsetSum_kFourDesign_star_sub_one` — the star gap is `Gtz.rootStarGap`.
* `Gtz.posDef_gap_kFourDesign_star` — the star dominates strictly.
* `Gtz.freeMassBudget_kFourDesign_star` — the free mass it spends is `6/5`.
* `Gtz.not_freeMassBudget_lt_one_kFourDesign_star` — the free-mass arm is blind.
* `Gtz.not_hasIsotropicGap_kFourDesign_star` — the isotropy arm is blind too.
* `Gtz.not_hasStrictCertificate_kFourDesign_star` — so the whole strict certificate
  misses a triple that dominates strictly.

## Scope

One design and one triple.  The claim is that the free-mass arm alone cannot close
branch (i), not that it is useless: it fires at the deep near-ties where the balance
law does not.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.StressFreeStratum
import Gtz.Design.BalancedStratum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Finset Matrix

/-! ## Part 1: the six edge directions of K4 -/

/-- The six edge directions of `K4`, as the positive roots of `A3`. -/
def kFourRootEdge : Fin 6 → Fin 3 → ℝ :=
  ![![1, 1, 0], ![1, -1, 0], ![1, 0, 1], ![1, 0, -1], ![0, 1, 1], ![0, 1, -1]]

/-- The scale that turns the edge directions into a design at uniform weight. -/
noncomputable def kFourRootScale : ℝ := Real.sqrt (3 / 2)

theorem kFourRootScale_sq : kFourRootScale ^ 2 = 3 / 2 := by
  rw [kFourRootScale, Real.sq_sqrt]
  norm_num

/-- The six atoms of the K4 edge design. -/
noncomputable def kFourAtom (label : Fin 6) : Fin 3 → ℝ := kFourRootScale • kFourRootEdge label

theorem atomMatrix_kFourAtom (label : Fin 6) :
    atomMatrix (kFourAtom label) = (3 / 2 : ℝ) • atomMatrix (kFourRootEdge label) := by
  rw [kFourAtom, atomMatrix_smul, kFourRootScale_sq]

/-- The unweighted edge atoms sum to four times the identity. -/
theorem sum_atomMatrix_kFourRootEdge :
    ∑ label, atomMatrix (kFourRootEdge label) = (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex colIndex
  simp only [Matrix.sum_apply, Fin.sum_univ_six, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases rowIndex <;> fin_cases colIndex <;> simp [kFourRootEdge] <;> norm_num

/-- **The K4 edge design**: six atoms, uniform weight `1/6`, every leverage `3`. -/
noncomputable def kFourDesign : WeightedDesign 6 3 where
  atom := kFourAtom
  weight := fun _ => 1 / 6
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six]
    norm_num
  isParseval := by
    have hstep : ∑ label, (1 / 6 : ℝ) • atomMatrix (kFourAtom label)
        = (1 / 4 : ℝ) • ∑ label, atomMatrix (kFourRootEdge label) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun label _ => ?_
      rw [atomMatrix_kFourAtom, smul_smul]
      norm_num
    rw [hstep, sum_atomMatrix_kFourRootEdge, smul_smul]
    norm_num

theorem kFourDesign_atom (label : Fin 6) : kFourDesign.atom label = kFourAtom label := rfl

theorem kFourDesign_weight (label : Fin 6) : kFourDesign.weight label = 1 / 6 := rfl

/-- Every subset sum of the design is a rational multiple of the edge atom sum. -/
theorem subsetSum_kFourDesign_eq (selected : Finset (Fin 6)) :
    subsetSum kFourDesign selected
      = (3 / 2 : ℝ) • ∑ label ∈ selected, atomMatrix (kFourRootEdge label) := by
  rw [subsetSum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [kFourDesign_atom, atomMatrix_kFourAtom]

/-- The base deficit of any subset, likewise. -/
theorem baseDeficit_kFourDesign_eq (selected : Finset (Fin 6)) :
    ∑ label ∈ selected, (1 - kFourDesign.weight label) • atomMatrix (kFourDesign.atom label)
      = (5 / 4 : ℝ) • ∑ label ∈ selected, atomMatrix (kFourRootEdge label) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [kFourDesign_atom, kFourDesign_weight, atomMatrix_kFourAtom, smul_smul]
  norm_num

/-- The scale squares out of every quadratic reading of an atom. -/
theorem dotProduct_kFourAtom_mulVec (form : Matrix (Fin 3) (Fin 3) ℝ) (label : Fin 6) :
    kFourDesign.atom label ⬝ᵥ (form *ᵥ kFourDesign.atom label)
      = (3 / 2 : ℝ) * (kFourRootEdge label ⬝ᵥ (form *ᵥ kFourRootEdge label)) := by
  rw [kFourDesign_atom, kFourAtom, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, kFourRootScale_sq]

/-- The edge atom sum over the vertex star `{0, 2, 4}`. -/
theorem sum_atomMatrix_kFourRootEdge_star :
    ∑ label ∈ ({0, 2, 4} : Finset (Fin 6)), atomMatrix (kFourRootEdge label)
      = !![2, 1, 1; 1, 2, 1; 1, 1, 2] := by
  ext rowIndex colIndex
  rw [Matrix.sum_apply, show ({0, 2, 4} : Finset (Fin 6)) = {0, 2, 4} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [atomMatrix, Matrix.vecMulVec_apply]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourRootEdge, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply] <;> norm_num

/-! ## Part 2: the design lies on branch (i) -/

/-- **THE K4 EDGE DESIGN IS STRESS-FREE.**  The six symmetric squares are
independent: the three off-diagonal equations pair the coefficients, and the three
diagonal equations then force them all to vanish. -/
theorem kFourDesign_stressFree :
    ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (kFourDesign.atom atomIndex)) = 0 →
        stressCoeff = 0 := by
  intro stressCoeff hstress
  have hedge : ∑ atomIndex, ((3 / 2 : ℝ) * stressCoeff atomIndex)
      • atomMatrix (kFourRootEdge atomIndex) = 0 := by
    rw [← hstress]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [kFourDesign_atom, atomMatrix_kFourAtom, smul_smul]
    ring_nf
  have hentry : ∀ rowIndex colIndex : Fin 3,
      (∑ atomIndex, ((3 / 2 : ℝ) * stressCoeff atomIndex)
        • atomMatrix (kFourRootEdge atomIndex)) rowIndex colIndex = 0 := by
    intro rowIndex colIndex
    rw [hedge]
    rfl
  have hexpand : ∀ rowIndex colIndex : Fin 3,
      ∑ atomIndex, ((3 / 2 : ℝ) * stressCoeff atomIndex)
          * (kFourRootEdge atomIndex rowIndex * kFourRootEdge atomIndex colIndex) = 0 := by
    intro rowIndex colIndex
    have hone := hentry rowIndex colIndex
    rw [Matrix.sum_apply] at hone
    simpa only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul] using hone
  have h01 := hexpand 0 1
  have h02 := hexpand 0 2
  have h12 := hexpand 1 2
  have h00 := hexpand 0 0
  have h11 := hexpand 1 1
  have h22 := hexpand 2 2
  simp [Fin.sum_univ_six, kFourRootEdge] at h00 h11 h22 h01 h02 h12
  have e0 : stressCoeff 0 = 0 := by linarith
  have e1 : stressCoeff 1 = 0 := by linarith
  have e2 : stressCoeff 2 = 0 := by linarith
  have e3 : stressCoeff 3 = 0 := by linarith
  have e4 : stressCoeff 4 = 0 := by linarith
  have e5 : stressCoeff 5 = 0 := by linarith
  funext atomIndex
  fin_cases atomIndex <;> simp only [Pi.zero_apply]
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5

/-! ## Part 3: the star triple and its gap -/

/-- The vertex star `{0, 2, 4}`: the three edges through one vertex of `K4`. -/
theorem subsetSum_kFourDesign_star :
    subsetSum kFourDesign ({0, 2, 4} : Finset (Fin 6))
      = !![3, 3 / 2, 3 / 2; 3 / 2, 3, 3 / 2; 3 / 2, 3 / 2, 3] := by
  rw [subsetSum_kFourDesign_eq, sum_atomMatrix_kFourRootEdge_star]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.smul_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply] <;> norm_num

/-- **THE STAR GAP IS `Gtz.rootStarGap`.**  The repository's two-invariant
calibration matrix is the K4 star gap. -/
theorem subsetSum_kFourDesign_star_sub_one :
    subsetSum kFourDesign ({0, 2, 4} : Finset (Fin 6)) - 1 = rootStarGap := by
  rw [subsetSum_kFourDesign_star, rootStarGap]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.one_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply] <;> norm_num

/-- **THE STAR DOMINATES STRICTLY.** -/
theorem posDef_gap_kFourDesign_star :
    (subsetSum kFourDesign ({0, 2, 4} : Finset (Fin 6)) - 1).PosDef := by
  rw [subsetSum_kFourDesign_star_sub_one]
  exact no_two_invariant_domination_test.2.2.2.2.2.1

/-! ## Part 4: the free mass the star spends -/

/-- The base deficit of the star, in closed form. -/
theorem baseDeficit_kFourDesign_star :
    ∑ label ∈ ({0, 2, 4} : Finset (Fin 6)),
        (1 - kFourDesign.weight label) • atomMatrix (kFourDesign.atom label)
      = !![5 / 2, 5 / 4, 5 / 4; 5 / 4, 5 / 2, 5 / 4; 5 / 4, 5 / 4, 5 / 2] := by
  rw [baseDeficit_kFourDesign_eq, sum_atomMatrix_kFourRootEdge_star]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.smul_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply] <;> norm_num

/-- The inverse of the star's base deficit, checked by multiplication. -/
theorem baseDeficit_kFourDesign_star_inv :
    (!![5 / 2, 5 / 4, 5 / 4; 5 / 4, 5 / 2, 5 / 4; 5 / 4, 5 / 4, 5 / 2]
        : Matrix (Fin 3) (Fin 3) ℝ)⁻¹
      = !![3 / 5, -(1 / 5), -(1 / 5); -(1 / 5), 3 / 5, -(1 / 5); -(1 / 5), -(1 / 5), 3 / 5] := by
  refine Matrix.inv_eq_right_inv ?_
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.of_apply] <;> norm_num

/-- **THE FREE MASS THE STAR SPENDS IS `6/5`.**  Each of the three edges outside the
star reads `12/5` against the inverse base deficit, at weight `1/6`. -/
theorem freeMassBudget_kFourDesign_star :
    ∑ label ∈ (({0, 2, 4} : Finset (Fin 6))ᶜ), kFourDesign.weight label
        * (kFourDesign.atom label ⬝ᵥ ((∑ other ∈ ({0, 2, 4} : Finset (Fin 6)),
            (1 - kFourDesign.weight other) • atomMatrix (kFourDesign.atom other))⁻¹
          *ᵥ kFourDesign.atom label))
      = 6 / 5 := by
  have hcompl : (({0, 2, 4} : Finset (Fin 6))ᶜ) = ({1, 3, 5} : Finset (Fin 6)) := by decide
  rw [hcompl, baseDeficit_kFourDesign_star, baseDeficit_kFourDesign_star_inv,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    dotProduct_kFourAtom_mulVec, dotProduct_kFourAtom_mulVec, dotProduct_kFourAtom_mulVec,
    kFourDesign_weight, kFourDesign_weight, kFourDesign_weight]
  simp [kFourRootEdge, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.of_apply]
  norm_num

/-- **THE FREE-MASS CERTIFICATE IS BLIND AT THE K4 STAR.**  The star dominates
strictly and its free-mass budget is `6/5`, so the budget hypothesis of
`Gtz.posDef_gap_of_freeMassBudget` is FALSE there.  The certificate cannot be the
covering criterion for branch (i). -/
theorem not_freeMassBudget_lt_one_kFourDesign_star :
    ¬ (∑ label ∈ (({0, 2, 4} : Finset (Fin 6))ᶜ), kFourDesign.weight label
        * (kFourDesign.atom label ⬝ᵥ ((∑ other ∈ ({0, 2, 4} : Finset (Fin 6)),
            (1 - kFourDesign.weight other) • atomMatrix (kFourDesign.atom other))⁻¹
          *ᵥ kFourDesign.atom label)) < 1) := by
  rw [freeMassBudget_kFourDesign_star]
  norm_num

/-- **THE MISS, PACKAGED.**  One stress-free `(6,3)` design, one triple: the gap is
positive definite and the free-mass budget is at least one. -/
theorem freeMass_certificate_misses_on_stressFree_sixThree :
    (∀ stressCoeff : Fin 6 → ℝ,
        (∑ atomIndex, stressCoeff atomIndex • atomMatrix (kFourDesign.atom atomIndex)) = 0 →
          stressCoeff = 0)
      ∧ ({0, 2, 4} : Finset (Fin 6)).card = 3
      ∧ (subsetSum kFourDesign ({0, 2, 4} : Finset (Fin 6)) - 1).PosDef
      ∧ ¬ (∑ label ∈ (({0, 2, 4} : Finset (Fin 6))ᶜ), kFourDesign.weight label
          * (kFourDesign.atom label ⬝ᵥ ((∑ other ∈ ({0, 2, 4} : Finset (Fin 6)),
              (1 - kFourDesign.weight other) • atomMatrix (kFourDesign.atom other))⁻¹
            *ᵥ kFourDesign.atom label)) < 1) :=
  ⟨kFourDesign_stressFree, by decide, posDef_gap_kFourDesign_star,
    not_freeMassBudget_lt_one_kFourDesign_star⟩

/-! ## Part 5: the isotropy arm fails too, so the whole certificate fails -/

theorem trace_rootStarGap : Matrix.trace rootStarGap = 6 := by
  rw [rootStarGap, Matrix.trace_fin_three]
  simp [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  norm_num

theorem frobeniusNormSq_rootStarGap : frobeniusNormSq rootStarGap = 51 / 2 := by
  rw [rootStarGap, frobeniusNormSq]
  simp [frobeniusInner, Fin.sum_univ_three, Matrix.trace_fin_three, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  norm_num

/-- **THE ISOTROPY ARM FAILS AT THE K4 STAR.**  The star gap has trace `6` and
Frobenius square `51/2`, and `51 > 36`. -/
theorem not_hasIsotropicGap_kFourDesign_star :
    ¬ HasIsotropicGap kFourDesign ({0, 2, 4} : Finset (Fin 6)) := by
  rintro ⟨-, hisotropy⟩
  rw [subsetSum_kFourDesign_star_sub_one, frobeniusNormSq_rootStarGap,
    trace_rootStarGap] at hisotropy
  norm_num at hisotropy

/-- **THE WHOLE STRICT CERTIFICATE FAILS AT THE K4 STAR, WHICH DOMINATES STRICTLY.**
Both arms of `Gtz.HasStrictCertificate` are false at a triple whose gap is positive
definite, on a stress-free `(6,3)` design at uniform weight.  The certificate is not
necessary for strict domination, and the case split of
`Gtz.sixThree_exists_posDef_triple_of_stressFree` is empty here. -/
theorem not_hasStrictCertificate_kFourDesign_star :
    ¬ HasStrictCertificate kFourDesign ({0, 2, 4} : Finset (Fin 6)) := by
  rintro (hisotropy | ⟨-, hbudget⟩)
  · exact not_hasIsotropicGap_kFourDesign_star hisotropy
  · exact not_freeMassBudget_lt_one_kFourDesign_star hbudget

/-- The refutation, packaged: stress-free, the triple dominates strictly, and no arm
of the strict certificate reaches it. -/
theorem strictCertificate_misses_a_strict_dominator :
    (∀ stressCoeff : Fin 6 → ℝ,
        (∑ atomIndex, stressCoeff atomIndex • atomMatrix (kFourDesign.atom atomIndex)) = 0 →
          stressCoeff = 0)
      ∧ ({0, 2, 4} : Finset (Fin 6)).card = 3
      ∧ (subsetSum kFourDesign ({0, 2, 4} : Finset (Fin 6)) - 1).PosDef
      ∧ ¬ HasStrictCertificate kFourDesign ({0, 2, 4} : Finset (Fin 6)) :=
  ⟨kFourDesign_stressFree, by decide, posDef_gap_kFourDesign_star,
    not_hasStrictCertificate_kFourDesign_star⟩

end Gtz
