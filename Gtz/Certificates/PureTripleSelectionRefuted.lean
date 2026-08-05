/-
# The pure-triple selection conjecture for branch (ii) is FALSE — kernel-checked refutation

The p16 lead for `Gtz.BalancedStratumSelection 6` (branch (ii) of the rank-3
trichotomy) proposed that on the zero-sum slice the SELECTION can always be one
of the two PURE TRIPLES — the all-positive-stress side or the all-negative-stress
side — under the certificate-free residual hypotheses (no stress mass gap in
either orientation, free-mass budget failing at every triple).  Both exact
residual witnesses of the p16 zero-sum lab supported it.

This file refutes the conjecture outright.  `refutationAtom`/`refutationWeight`
give an exact rational configuration in the diagonal two-frame gauge:
  * six atoms, positive side axis-aligned, negative side a scaled exact rational
    rotation frame, carrying the FULL-SUPPORT ZERO-SUM stress
    `(1/alpha_i^2, -1/beta_j^2)` with the balance equation exact;
  * a PRIMITIVE family (no two atoms parallel, checked coordinate-wise);
  * the residual hypotheses hold: NO stress mass gap in either orientation
    (crossing pairs exhibited), and the free-mass budget FAILS at all twenty
    triples (variational multiplier certificates, spend >= 1 exactly);
  * yet BOTH pure triples fail to dominate: explicit rational witness vectors
    make both pure gaps non-positive-definite.
The whitening dictionary of the tree (`whitenedFamilyDesign`,
`posDef_gap_whitenedFamilyDesign_iff`) transports the rational family to a
genuine `WeightedDesign 6 3`, so the refuted statement is the DESIGN-LEVEL
conjecture, with the residual hypotheses in exactly the shape of
`Gtz.BalancedStratumSelection`.

The configuration is NOT a tie — mixed triples strictly dominate it — so it does
not touch `NoPrimitiveBalancedTieZeroSumSixThree` itself.  What it kills is the
pure-triple SELECTOR: any selector closing branch (ii) must be able to output
MIXED triples on the residual stratum.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.StressMassGap
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.BalancedStratum
import Gtz.Design.BalancedNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

namespace Gtz
namespace PureTripleRefutation

open Matrix

/-! ## The conjecture under refutation

`Gtz.BalancedStratumSelection 6` sharpened to the zero-sum slice with the
dominating triple REQUIRED to be a stress side.  This is the strongest honest
formulation of the p16 pure-triple lead: hypotheses exactly as in the landed
residual (plus the zero-sum equation, free on the tie side), conclusion
restricted to the two pure triples. -/

/-- **The pure-triple selection conjecture.**  Every primitive `(6,3)` design
carrying a full-support zero-sum stress on which neither mass-gap orientation
fires and no triple meets the free-mass budget is strictly dominated by one of
the two PURE stress sides. -/
def PureTripleZeroSumSelectionSixThree : Prop :=
  ∀ (design : WeightedDesign 6 3) (stressCoeff : Fin 6 → ℝ),
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0) →
    (∑ c, stressCoeff c) = 0 →
    IsPrimitiveDesign design →
    ¬ HasStressMassGap design stressCoeff →
    ¬ HasStressMassGap design (-stressCoeff) →
    (∀ triple : Finset (Fin 6), triple.card = 3 → ¬ HasFreeMassBudget design triple) →
    (subsetSum design (Finset.univ.filter fun c => 0 < stressCoeff c) - 1).PosDef
      ∨ (subsetSum design (Finset.univ.filter fun c => stressCoeff c < 0) - 1).PosDef

/-! ## General transport lemmas -/

/-- **The variational lower bound for the inverse form.**  For a positive
definite metric, `2<a,u> - <u,Yu> <= <a, Y^{-1} a>` at every multiplier `u`,
with equality at `u = Y^{-1} a`.  This certifies budget FAILURE by rational
arithmetic alone: no inverse matrix ever needs to be exhibited. -/
theorem two_mul_dot_sub_form_le_inverseForm {rank : ℕ}
    {gramMat : Matrix (Fin rank) (Fin rank) ℝ} (hposDef : gramMat.PosDef)
    (source multiplier : Fin rank → ℝ) :
    2 * (source ⬝ᵥ multiplier) - multiplier ⬝ᵥ (gramMat *ᵥ multiplier)
      ≤ source ⬝ᵥ (gramMat⁻¹ *ᵥ source) := by
  have hdet : IsUnit gramMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have htranspose : gramMatᵀ = gramMat := transpose_eq_of_isHermitian hposDef.1
  set dual : Fin rank → ℝ := gramMat⁻¹ *ᵥ source with hdual
  have hmulDual : gramMat *ᵥ dual = source := by
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv gramMat hdet,
      Matrix.one_mulVec]
  have hformNonneg : 0 ≤ (multiplier - dual) ⬝ᵥ (gramMat *ᵥ (multiplier - dual)) := by
    have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposDef.posSemidef).2
      (multiplier - dual)
    rwa [star_trivial] at hstep
  have hexpand : (multiplier - dual) ⬝ᵥ (gramMat *ᵥ (multiplier - dual))
      = multiplier ⬝ᵥ (gramMat *ᵥ multiplier) - multiplier ⬝ᵥ (gramMat *ᵥ dual)
        - dual ⬝ᵥ (gramMat *ᵥ multiplier) + dual ⬝ᵥ (gramMat *ᵥ dual) := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
    ring
  have hcross : multiplier ⬝ᵥ (gramMat *ᵥ dual) = source ⬝ᵥ multiplier := by
    rw [hmulDual, dotProduct_comm]
  have hcross' : dual ⬝ᵥ (gramMat *ᵥ multiplier) = source ⬝ᵥ multiplier := by
    rw [dot_mulVec_comm htranspose, hmulDual, dotProduct_comm]
  have hself : dual ⬝ᵥ (gramMat *ᵥ dual) = source ⬝ᵥ (gramMat⁻¹ *ᵥ source) := by
    rw [hmulDual, dotProduct_comm, hdual]
  rw [hexpand, hcross, hcross', hself] at hformNonneg
  linarith [hformNonneg]

/-- **The inverse form is invariant under congruence transport.**  The whitened
budget spend of an atom equals its raw spend: the whitener cancels through the
inverse of the conjugated metric. -/
theorem dotProduct_inv_conjugate_eq {rank : ℕ}
    {whitener gramMat : Matrix (Fin rank) (Fin rank) ℝ}
    (hwUnit : IsUnit whitener.det) (source : Fin rank → ℝ) :
    (whitenerᵀ *ᵥ source) ⬝ᵥ ((whitenerᵀ * gramMat * whitener)⁻¹
        *ᵥ (whitenerᵀ *ᵥ source))
      = source ⬝ᵥ (gramMat⁻¹ *ᵥ source) := by
  have hwtUnit : IsUnit (whitenerᵀ).det := by
    rw [Matrix.det_transpose]; exact hwUnit
  have hinv : (whitenerᵀ * gramMat * whitener)⁻¹
      = whitener⁻¹ * (gramMat⁻¹ * (whitenerᵀ)⁻¹) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  rw [hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec source ((whitenerᵀ)⁻¹) whitenerᵀ,
    Matrix.nonsing_inv_mul _ hwtUnit, Matrix.one_mulVec,
    Matrix.mulVec_transpose, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hwUnit, Matrix.vecMul_one]

/-- An invertible matrix preserves non-parallelism of vectors.  (Textual reuse
of the p16 zero-sum reduction lemma; needed to transport primitivity through
the whitener.) -/
theorem mulVec_ne_smul_of_ne_smul {transform : Matrix (Fin 3) (Fin 3) ℝ}
    (hdetNe : transform.det ≠ 0) {sourceVec targetVec : Fin 3 → ℝ} {ratio : ℝ}
    (hnotParallel : targetVec ≠ ratio • sourceVec) :
    transform *ᵥ targetVec ≠ ratio • (transform *ᵥ sourceVec) := by
  intro heq
  have hunit : IsUnit transform.det := isUnit_iff_ne_zero.mpr hdetNe
  have hcancel : ∀ probe : Fin 3 → ℝ, transform⁻¹ *ᵥ (transform *ᵥ probe) = probe := by
    intro probe
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  have htarget : targetVec = ratio • sourceVec := by
    calc targetVec = transform⁻¹ *ᵥ (transform *ᵥ targetVec) := (hcancel targetVec).symm
      _ = transform⁻¹ *ᵥ (ratio • (transform *ᵥ sourceVec)) := by rw [heq]
      _ = ratio • (transform⁻¹ *ᵥ (transform *ᵥ sourceVec)) := by
          rw [Matrix.mulVec_smul]
      _ = ratio • sourceVec := by rw [hcancel sourceVec]
  exact hnotParallel htarget

/-- **Budget failure descends from rational data.**  If the raw variational
lower bound on the complement's spend already reaches one, the whitened design
cannot satisfy the free-mass budget at that subset. -/
theorem not_hasFreeMassBudget_whitened_of_rawBound
    (baseAtom : Fin 6 → Fin 3 → ℝ) (baseWeight : Fin 6 → ℝ)
    (hweightPos : ∀ c, 0 < baseWeight c) (hweightSumOne : ∑ c, baseWeight c = 1)
    {whitener : Matrix (Fin 3) (Fin 3) ℝ} (hwUnit : IsUnit whitener.det)
    (hwhiten : whitenerᵀ * (∑ c, baseWeight c • atomMatrix (baseAtom c))
      * whitener = 1)
    (selected : Finset (Fin 6)) (multiplier : Fin 6 → Fin 3 → ℝ)
    (hbound : 1 ≤ ∑ c ∈ selectedᶜ, baseWeight c
        * (2 * (baseAtom c ⬝ᵥ multiplier c)
          - ∑ d ∈ selected, (1 - baseWeight d) * (baseAtom d ⬝ᵥ multiplier c) ^ 2)) :
    ¬ HasFreeMassBudget
        (whitenedFamilyDesign baseAtom baseWeight hweightPos hweightSumOne
          whitener hwhiten) selected := by
  rintro ⟨hfreePosDef, hspend⟩
  set rawFree : Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ d ∈ selected, (1 - baseWeight d) • atomMatrix (baseAtom d) with hrawFree
  have hconj : (∑ d ∈ selected,
        (1 - (whitenedFamilyDesign baseAtom baseWeight hweightPos hweightSumOne
          whitener hwhiten).weight d)
        • atomMatrix ((whitenedFamilyDesign baseAtom baseWeight hweightPos
          hweightSumOne whitener hwhiten).atom d))
      = whitenerᵀ * rawFree * whitener := by
    have hstep := sum_smul_atomMatrix_mulVec_eq_conjugate whitenerᵀ baseAtom
      (fun d => 1 - baseWeight d) selected
    rw [Matrix.transpose_transpose] at hstep
    exact hstep
  rw [hconj] at hfreePosDef hspend
  have hrawPosDef : rawFree.PosDef := (posDef_congruence_iff hwUnit).mp hfreePosDef
  have hspendRaw : ∑ c ∈ selectedᶜ,
      baseWeight c * (baseAtom c ⬝ᵥ (rawFree⁻¹ *ᵥ baseAtom c)) < 1 := by
    refine lt_of_le_of_lt (le_of_eq ?_) hspend
    refine Finset.sum_congr rfl fun c _ => ?_
    show baseWeight c * (baseAtom c ⬝ᵥ (rawFree⁻¹ *ᵥ baseAtom c))
      = baseWeight c * ((whitenerᵀ *ᵥ baseAtom c)
          ⬝ᵥ ((whitenerᵀ * rawFree * whitener)⁻¹ *ᵥ (whitenerᵀ *ᵥ baseAtom c)))
    rw [dotProduct_inv_conjugate_eq hwUnit]
  have hlower : ∀ c ∈ selectedᶜ,
      baseWeight c * (2 * (baseAtom c ⬝ᵥ multiplier c)
          - ∑ d ∈ selected, (1 - baseWeight d) * (baseAtom d ⬝ᵥ multiplier c) ^ 2)
        ≤ baseWeight c * (baseAtom c ⬝ᵥ (rawFree⁻¹ *ᵥ baseAtom c)) := by
    intro c _
    refine mul_le_mul_of_nonneg_left ?_ (hweightPos c).le
    have hform : multiplier c ⬝ᵥ (rawFree *ᵥ multiplier c)
        = ∑ d ∈ selected, (1 - baseWeight d) * (baseAtom d ⬝ᵥ multiplier c) ^ 2 :=
      atomForm_eq_on_subset selected (fun d => 1 - baseWeight d) baseAtom
        (multiplier c)
    have hstep := two_mul_dot_sub_form_le_inverseForm hrawPosDef (baseAtom c)
      (multiplier c)
    rw [hform] at hstep
    exact hstep
  have hchain := Finset.sum_le_sum hlower
  linarith [hbound, hchain, hspendRaw]

/-- A sum over an explicit three-element finset of `Fin 6` expands to three
terms; the generic expander behind every budget block below. -/
theorem sum_tripleFinset_eq {carrier : Type*} [AddCommMonoid carrier]
    {first second third : Fin 6} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) (summand : Fin 6 → carrier) :
    ∑ label ∈ ({first, second, third} : Finset (Fin 6)), summand label
      = summand first + summand second + summand third := by
  rw [show ({first, second, third} : Finset (Fin 6))
      = insert first (insert second {third}) from rfl,
    Finset.sum_insert (by simp [Finset.mem_insert, hfs, hft]),
    Finset.sum_insert (by simp [hst]), Finset.sum_singleton, add_assoc]

/-- **No stress mass gap, from one crossing pair.**  A negative-side atom whose
bound-mass ratio reaches a positive-side atom's free-mass ratio blocks every
`(freeFloor, boundCeiling)` witness. -/
theorem not_hasStressMassGap_of_crossing {design : WeightedDesign 6 3}
    {stressCoeff : Fin 6 → ℝ} (posLabel negLabel : Fin 6)
    (hpos : 0 < stressCoeff posLabel) (hneg : stressCoeff negLabel < 0)
    (hcross : (1 - design.weight posLabel) * (-stressCoeff negLabel)
      ≤ design.weight negLabel * stressCoeff posLabel) :
    ¬ HasStressMassGap design stressCoeff := by
  rintro ⟨freeFloor, boundCeiling, hfree, hbound, hlt⟩
  have h1 := hfree posLabel hpos
  have h2 := hbound negLabel hneg
  have hnegPos : 0 < -stressCoeff negLabel := neg_pos.mpr hneg
  nlinarith [mul_le_mul_of_nonneg_right h1 hnegPos.le,
    mul_le_mul_of_nonneg_right h2 hpos.le, hcross,
    mul_pos hpos hnegPos, hlt]

/-- **A raw witness vector refutes domination.**  If the raw quadratic gap of a
subset is nonpositive at one nonzero vector, the subset's raw gap is not
positive definite. -/
theorem raw_gap_not_posDef_of_witnessVec (baseAtom : Fin 6 → Fin 3 → ℝ)
    (baseWeight : Fin 6 → ℝ) (selected : Finset (Fin 6))
    (witnessVec : Fin 3 → ℝ) (hne : witnessVec ≠ 0)
    (hval : (∑ c ∈ selected, (baseAtom c ⬝ᵥ witnessVec) ^ 2)
        - (∑ c, baseWeight c * (baseAtom c ⬝ᵥ witnessVec) ^ 2) ≤ 0) :
    ¬ ((∑ c ∈ selected, atomMatrix (baseAtom c))
        - ∑ c, baseWeight c • atomMatrix (baseAtom c)).PosDef := by
  intro hposDef
  have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hne
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hstep
  have hleft : witnessVec ⬝ᵥ ((∑ c ∈ selected, atomMatrix (baseAtom c)) *ᵥ witnessVec)
      = ∑ c ∈ selected, (baseAtom c ⬝ᵥ witnessVec) ^ 2 := by
    have hstep' := atomForm_eq_on_subset selected (fun _ => (1 : ℝ)) baseAtom witnessVec
    simpa using hstep'
  have hright : witnessVec ⬝ᵥ ((∑ c, baseWeight c • atomMatrix (baseAtom c))
        *ᵥ witnessVec)
      = ∑ c, baseWeight c * (baseAtom c ⬝ᵥ witnessVec) ^ 2 :=
    atomForm_eq_on_subset Finset.univ baseWeight baseAtom witnessVec
  rw [hleft, hright] at hstep
  linarith [hstep, hval]





/-! ## The exact rational witness

Diagonal two-frame chart data: positive atoms `alpha_i * e_i`, negative atoms
`beta_j * w_j` with `w` the exact rational rotation of the integer quaternion
`(-23, -26, 22, -11)`; scales `alpha = (1/x, 9/10, 31/2)`,
`beta = (9/2, 1, 1/y)` where `x, y` solve the zero-sum
balance exactly through `x = (r + S/r)/2`, `y = (r - S/r)/2` at `r = 13/5`. -/

/-- The six base atoms. -/
noncomputable def refAtom : Fin 6 → Fin 3 → ℝ :=
  ![![(1686555/2131109 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (9/10 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (31/2 : ℝ)],
    ![(270/181 : ℝ), (-2871/1810 : ℝ), (3564/905 : ℝ)],
    ![(-165/181 : ℝ), (108/905 : ℝ), (356/905 : ℝ)],
    ![(-37104210/203981027 : ℝ), (-141670620/203981027 : ℝ), (-86014305/407962054 : ℝ)]]

/-- The six weights (positive, summing to one exactly). -/
noncomputable def refWeight : Fin 6 → ℝ :=
  ![(15/61 : ℝ), (19/72 : ℝ), (1/112 : ℝ), (9/98 : ℝ), (5/13 : ℝ), (27019/5595408 : ℝ)]

/-- The full-support zero-sum stress `(1/alpha_i^2, -1/beta_j^2)`. -/
noncomputable def refStress : Fin 6 → ℝ :=
  ![(4541625569881/2844467768025 : ℝ),
    (100/81 : ℝ),
    (4/961 : ℝ),
    (-4/81 : ℝ),
    (-1 : ℝ),
    (-5080218476356/2844467768025 : ℝ)]

/-- Witness vector against the positive pure triple. -/
noncomputable def refWitnessPos : Fin 3 → ℝ := ![(1 : ℝ), (-32/71 : ℝ), (0 : ℝ)]

/-- Witness vector against the negative pure triple. -/
noncomputable def refWitnessNeg : Fin 3 → ℝ := ![(-104/163 : ℝ), (1 : ℝ), (99/139 : ℝ)]

/-- Budget multipliers for triple `{0, 1, 2}`. -/
noncomputable def refMult0 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(319/101 : ℝ), (-415/156 : ℝ), (2/121 : ℝ)],
    ![(-359/186 : ℝ), (1/5 : ℝ), (0 : ℝ)],
    ![(-57/148 : ℝ), (-106/91 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{0, 1, 3}`. -/
noncomputable def refMult1 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-2076/167 : ℝ), (178/17 : ℝ), (1133/113 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-128/57 : ℝ), (41/88 : ℝ), (145/136 : ℝ)],
    ![(-35/162 : ℝ), (-234/179 : ℝ), (-57/124 : ℝ)]]

/-- Budget multipliers for triple `{0, 1, 4}`. -/
noncomputable def refMult2 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(12853/169 : ℝ), (-347/44 : ℝ), (27313/80 : ℝ)],
    ![(607/27 : ℝ), (-583/125 : ℝ), (13851/146 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-159/112 : ℝ), (-147/139 : ℝ), (-679/131 : ℝ)]]

/-- Budget multipliers for triple `{0, 1, 5}`. -/
noncomputable def refMult3 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-1444/51 : ℝ), (-2569/30 : ℝ), (58463/89 : ℝ)],
    ![(-343/85 : ℝ), (-3101/127 : ℝ), (29399/170 : ℝ)],
    ![(-98/37 : ℝ), (-367/186 : ℝ), (1149/65 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{0, 2, 3}`. -/
noncomputable def refMult4 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(181/101 : ℝ), (82/39 : ℝ), (1/107 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-325/192 : ℝ), (-95/62 : ℝ), (1/192 : ℝ)],
    ![(-122/69 : ℝ), (-304/153 : ℝ), (-1/123 : ℝ)]]

/-- Budget multipliers for triple `{0, 2, 4}`. -/
noncomputable def refMult5 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(1805/124 : ℝ), (39791/186 : ℝ), (-2/161 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-3037/135 : ℝ), (-20119/57 : ℝ), (1/26 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-1522/131 : ℝ), (-5881/35 : ℝ), (1/115 : ℝ)]]

/-- Budget multipliers for triple `{0, 2, 5}`. -/
noncomputable def refMult6 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-1/2 : ℝ), (339/169 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(319/79 : ℝ), (-725/166 : ℝ), (1/54 : ℝ)],
    ![(-383/192 : ℝ), (101/131 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{0, 3, 4}`. -/
noncomputable def refMult7 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(211/29 : ℝ), (3749/80 : ℝ), (2789/174 : ℝ)],
    ![(1940/51 : ℝ), (49965/181 : ℝ), (18575/191 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-189/29 : ℝ), (-6912/167 : ℝ), (-1428/101 : ℝ)]]

/-- Budget multipliers for triple `{0, 3, 5}`. -/
noncomputable def refMult8 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-1/4 : ℝ), (206/135 : ℝ), (110/159 : ℝ)],
    ![(-1841/130 : ℝ), (2228/187 : ℝ), (1939/174 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-72/31 : ℝ), (103/136 : ℝ), (163/135 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{0, 4, 5}`. -/
noncomputable def refMult9 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-77/38 : ℝ), (192/35 : ℝ), (-238/25 : ℝ)],
    ![(2166/25 : ℝ), (-19019/116 : ℝ), (76935/179 : ℝ)],
    ![(4685/163 : ℝ), (-4320/79 : ℝ), (2955/22 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{1, 2, 3}`. -/
noncomputable def refMult10 : Fin 6 → Fin 3 → ℝ :=
  ![![(136/71 : ℝ), (199/141 : ℝ), (-1/114 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-2 : ℝ), (-67/47 : ℝ), (1/85 : ℝ)],
    ![(-57/34 : ℝ), (-207/139 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{1, 2, 4}`. -/
noncomputable def refMult11 : Fin 6 → Fin 3 → ℝ :=
  ![![(300/191 : ℝ), (33/190 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(448/171 : ℝ), (-7/3 : ℝ), (1/52 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-92/179 : ℝ), (-153/127 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{1, 2, 5}`. -/
noncomputable def refMult12 : Fin 6 → Fin 3 → ℝ :=
  ![![(7593/175 : ℝ), (-299/59 : ℝ), (-1/192 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(5883/64 : ℝ), (-2125/174 : ℝ), (1/108 : ℝ)],
    ![(-7561/149 : ℝ), (320/53 : ℝ), (1/164 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{1, 3, 4}`. -/
noncomputable def refMult13 : Fin 6 → Fin 3 → ℝ :=
  ![![(195/157 : ℝ), (65/187 : ℝ), (-48/155 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-285/47 : ℝ), (655/83 : ℝ), (1143/178 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-63/124 : ℝ), (-96/71 : ℝ), (-71/192 : ℝ)]]

/-- Budget multipliers for triple `{1, 3, 5}`. -/
noncomputable def refMult14 : Fin 6 → Fin 3 → ℝ :=
  ![![(28195/183 : ℝ), (-1896/187 : ℝ), (-11949/191 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-118852/97 : ℝ), (13539/158 : ℝ), (83099/166 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-36557/174 : ℝ), (2347/167 : ℝ), (12216/143 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{1, 4, 5}`. -/
noncomputable def refMult15 : Fin 6 → Fin 3 → ℝ :=
  ![![(719/191 : ℝ), (-176/141 : ℝ), (305/47 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(22242/175 : ℝ), (-7035/109 : ℝ), (35111/98 : ℝ)],
    ![(7959/190 : ℝ), (-2291/107 : ℝ), (17029/155 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{2, 3, 4}`. -/
noncomputable def refMult16 : Fin 6 → Fin 3 → ℝ :=
  ![![(89/44 : ℝ), (353/180 : ℝ), (1/192 : ℝ)],
    ![(310/139 : ℝ), (183/71 : ℝ), (2/161 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-363/166 : ℝ), (-469/192 : ℝ), (-2/179 : ℝ)]]

/-- Budget multipliers for triple `{2, 3, 5}`. -/
noncomputable def refMult17 : Fin 6 → Fin 3 → ℝ :=
  ![![(130/93 : ℝ), (136/135 : ℝ), (-1/130 : ℝ)],
    ![(118/103 : ℝ), (218/187 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-212/145 : ℝ), (-190/189 : ℝ), (2/187 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{2, 4, 5}`. -/
noncomputable def refMult18 : Fin 6 → Fin 3 → ℝ :=
  ![![(277/188 : ℝ), (-27/152 : ℝ), (0 : ℝ)],
    ![(-20/99 : ℝ), (209/112 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(427/136 : ℝ), (-599/165 : ℝ), (3/139 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers for triple `{3, 4, 5}`. -/
noncomputable def refMult19 : Fin 6 → Fin 3 → ℝ :=
  ![![(125/108 : ℝ), (33/188 : ℝ), (-13/37 : ℝ)],
    ![(1/5 : ℝ), (200/141 : ℝ), (89/187 : ℝ)],
    ![(-117/17 : ℝ), (1287/157 : ℝ), (1114/165 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-! ### Evaluation lemmas (definitional; keep every later proof numeric) -/

@[simp] theorem finSix_mk_two (h : 2 < 6) : (⟨2, h⟩ : Fin 6) = 2 := rfl
@[simp] theorem finSix_mk_three (h : 3 < 6) : (⟨3, h⟩ : Fin 6) = 3 := rfl
@[simp] theorem finSix_mk_four (h : 4 < 6) : (⟨4, h⟩ : Fin 6) = 4 := rfl
@[simp] theorem finSix_mk_five (h : 5 < 6) : (⟨5, h⟩ : Fin 6) = 5 := rfl
@[simp] theorem finThree_mk_two (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl

@[simp] theorem refAtom_eval_0_0 : refAtom 0 0 = (1686555/2131109 : ℝ) := rfl
@[simp] theorem refAtom_eval_0_1 : refAtom 0 1 = (0 : ℝ) := rfl
@[simp] theorem refAtom_eval_0_2 : refAtom 0 2 = (0 : ℝ) := rfl
@[simp] theorem refAtom_eval_1_0 : refAtom 1 0 = (0 : ℝ) := rfl
@[simp] theorem refAtom_eval_1_1 : refAtom 1 1 = (9/10 : ℝ) := rfl
@[simp] theorem refAtom_eval_1_2 : refAtom 1 2 = (0 : ℝ) := rfl
@[simp] theorem refAtom_eval_2_0 : refAtom 2 0 = (0 : ℝ) := rfl
@[simp] theorem refAtom_eval_2_1 : refAtom 2 1 = (0 : ℝ) := rfl
@[simp] theorem refAtom_eval_2_2 : refAtom 2 2 = (31/2 : ℝ) := rfl
@[simp] theorem refAtom_eval_3_0 : refAtom 3 0 = (270/181 : ℝ) := rfl
@[simp] theorem refAtom_eval_3_1 : refAtom 3 1 = (-2871/1810 : ℝ) := rfl
@[simp] theorem refAtom_eval_3_2 : refAtom 3 2 = (3564/905 : ℝ) := rfl
@[simp] theorem refAtom_eval_4_0 : refAtom 4 0 = (-165/181 : ℝ) := rfl
@[simp] theorem refAtom_eval_4_1 : refAtom 4 1 = (108/905 : ℝ) := rfl
@[simp] theorem refAtom_eval_4_2 : refAtom 4 2 = (356/905 : ℝ) := rfl
@[simp] theorem refAtom_eval_5_0 : refAtom 5 0 = (-37104210/203981027 : ℝ) := rfl
@[simp] theorem refAtom_eval_5_1 : refAtom 5 1 = (-141670620/203981027 : ℝ) := rfl
@[simp] theorem refAtom_eval_5_2 : refAtom 5 2 = (-86014305/407962054 : ℝ) := rfl
@[simp] theorem refWeight_eval_0 : refWeight 0 = (15/61 : ℝ) := rfl
@[simp] theorem refWeight_eval_1 : refWeight 1 = (19/72 : ℝ) := rfl
@[simp] theorem refWeight_eval_2 : refWeight 2 = (1/112 : ℝ) := rfl
@[simp] theorem refWeight_eval_3 : refWeight 3 = (9/98 : ℝ) := rfl
@[simp] theorem refWeight_eval_4 : refWeight 4 = (5/13 : ℝ) := rfl
@[simp] theorem refWeight_eval_5 : refWeight 5 = (27019/5595408 : ℝ) := rfl
@[simp] theorem refStress_eval_0 : refStress 0 = (4541625569881/2844467768025 : ℝ) := rfl
@[simp] theorem refStress_eval_1 : refStress 1 = (100/81 : ℝ) := rfl
@[simp] theorem refStress_eval_2 : refStress 2 = (4/961 : ℝ) := rfl
@[simp] theorem refStress_eval_3 : refStress 3 = (-4/81 : ℝ) := rfl
@[simp] theorem refStress_eval_4 : refStress 4 = (-1 : ℝ) := rfl
@[simp] theorem refStress_eval_5 : refStress 5 = (-5080218476356/2844467768025 : ℝ) := rfl
@[simp] theorem refWitnessPos_eval_0 : refWitnessPos 0 = (1 : ℝ) := rfl
@[simp] theorem refWitnessPos_eval_1 : refWitnessPos 1 = (-32/71 : ℝ) := rfl
@[simp] theorem refWitnessPos_eval_2 : refWitnessPos 2 = (0 : ℝ) := rfl
@[simp] theorem refWitnessNeg_eval_0 : refWitnessNeg 0 = (-104/163 : ℝ) := rfl
@[simp] theorem refWitnessNeg_eval_1 : refWitnessNeg 1 = (1 : ℝ) := rfl
@[simp] theorem refWitnessNeg_eval_2 : refWitnessNeg 2 = (99/139 : ℝ) := rfl
@[simp] theorem refMult0_eval_3_0 : refMult0 3 0 = (319/101 : ℝ) := rfl
@[simp] theorem refMult0_eval_3_1 : refMult0 3 1 = (-415/156 : ℝ) := rfl
@[simp] theorem refMult0_eval_3_2 : refMult0 3 2 = (2/121 : ℝ) := rfl
@[simp] theorem refMult0_eval_4_0 : refMult0 4 0 = (-359/186 : ℝ) := rfl
@[simp] theorem refMult0_eval_4_1 : refMult0 4 1 = (1/5 : ℝ) := rfl
@[simp] theorem refMult0_eval_4_2 : refMult0 4 2 = (0 : ℝ) := rfl
@[simp] theorem refMult0_eval_5_0 : refMult0 5 0 = (-57/148 : ℝ) := rfl
@[simp] theorem refMult0_eval_5_1 : refMult0 5 1 = (-106/91 : ℝ) := rfl
@[simp] theorem refMult0_eval_5_2 : refMult0 5 2 = (0 : ℝ) := rfl
@[simp] theorem refMult1_eval_2_0 : refMult1 2 0 = (-2076/167 : ℝ) := rfl
@[simp] theorem refMult1_eval_2_1 : refMult1 2 1 = (178/17 : ℝ) := rfl
@[simp] theorem refMult1_eval_2_2 : refMult1 2 2 = (1133/113 : ℝ) := rfl
@[simp] theorem refMult1_eval_4_0 : refMult1 4 0 = (-128/57 : ℝ) := rfl
@[simp] theorem refMult1_eval_4_1 : refMult1 4 1 = (41/88 : ℝ) := rfl
@[simp] theorem refMult1_eval_4_2 : refMult1 4 2 = (145/136 : ℝ) := rfl
@[simp] theorem refMult1_eval_5_0 : refMult1 5 0 = (-35/162 : ℝ) := rfl
@[simp] theorem refMult1_eval_5_1 : refMult1 5 1 = (-234/179 : ℝ) := rfl
@[simp] theorem refMult1_eval_5_2 : refMult1 5 2 = (-57/124 : ℝ) := rfl
@[simp] theorem refMult2_eval_2_0 : refMult2 2 0 = (12853/169 : ℝ) := rfl
@[simp] theorem refMult2_eval_2_1 : refMult2 2 1 = (-347/44 : ℝ) := rfl
@[simp] theorem refMult2_eval_2_2 : refMult2 2 2 = (27313/80 : ℝ) := rfl
@[simp] theorem refMult2_eval_3_0 : refMult2 3 0 = (607/27 : ℝ) := rfl
@[simp] theorem refMult2_eval_3_1 : refMult2 3 1 = (-583/125 : ℝ) := rfl
@[simp] theorem refMult2_eval_3_2 : refMult2 3 2 = (13851/146 : ℝ) := rfl
@[simp] theorem refMult2_eval_5_0 : refMult2 5 0 = (-159/112 : ℝ) := rfl
@[simp] theorem refMult2_eval_5_1 : refMult2 5 1 = (-147/139 : ℝ) := rfl
@[simp] theorem refMult2_eval_5_2 : refMult2 5 2 = (-679/131 : ℝ) := rfl
@[simp] theorem refMult3_eval_2_0 : refMult3 2 0 = (-1444/51 : ℝ) := rfl
@[simp] theorem refMult3_eval_2_1 : refMult3 2 1 = (-2569/30 : ℝ) := rfl
@[simp] theorem refMult3_eval_2_2 : refMult3 2 2 = (58463/89 : ℝ) := rfl
@[simp] theorem refMult3_eval_3_0 : refMult3 3 0 = (-343/85 : ℝ) := rfl
@[simp] theorem refMult3_eval_3_1 : refMult3 3 1 = (-3101/127 : ℝ) := rfl
@[simp] theorem refMult3_eval_3_2 : refMult3 3 2 = (29399/170 : ℝ) := rfl
@[simp] theorem refMult3_eval_4_0 : refMult3 4 0 = (-98/37 : ℝ) := rfl
@[simp] theorem refMult3_eval_4_1 : refMult3 4 1 = (-367/186 : ℝ) := rfl
@[simp] theorem refMult3_eval_4_2 : refMult3 4 2 = (1149/65 : ℝ) := rfl
@[simp] theorem refMult4_eval_1_0 : refMult4 1 0 = (181/101 : ℝ) := rfl
@[simp] theorem refMult4_eval_1_1 : refMult4 1 1 = (82/39 : ℝ) := rfl
@[simp] theorem refMult4_eval_1_2 : refMult4 1 2 = (1/107 : ℝ) := rfl
@[simp] theorem refMult4_eval_4_0 : refMult4 4 0 = (-325/192 : ℝ) := rfl
@[simp] theorem refMult4_eval_4_1 : refMult4 4 1 = (-95/62 : ℝ) := rfl
@[simp] theorem refMult4_eval_4_2 : refMult4 4 2 = (1/192 : ℝ) := rfl
@[simp] theorem refMult4_eval_5_0 : refMult4 5 0 = (-122/69 : ℝ) := rfl
@[simp] theorem refMult4_eval_5_1 : refMult4 5 1 = (-304/153 : ℝ) := rfl
@[simp] theorem refMult4_eval_5_2 : refMult4 5 2 = (-1/123 : ℝ) := rfl
@[simp] theorem refMult5_eval_1_0 : refMult5 1 0 = (1805/124 : ℝ) := rfl
@[simp] theorem refMult5_eval_1_1 : refMult5 1 1 = (39791/186 : ℝ) := rfl
@[simp] theorem refMult5_eval_1_2 : refMult5 1 2 = (-2/161 : ℝ) := rfl
@[simp] theorem refMult5_eval_3_0 : refMult5 3 0 = (-3037/135 : ℝ) := rfl
@[simp] theorem refMult5_eval_3_1 : refMult5 3 1 = (-20119/57 : ℝ) := rfl
@[simp] theorem refMult5_eval_3_2 : refMult5 3 2 = (1/26 : ℝ) := rfl
@[simp] theorem refMult5_eval_5_0 : refMult5 5 0 = (-1522/131 : ℝ) := rfl
@[simp] theorem refMult5_eval_5_1 : refMult5 5 1 = (-5881/35 : ℝ) := rfl
@[simp] theorem refMult5_eval_5_2 : refMult5 5 2 = (1/115 : ℝ) := rfl
@[simp] theorem refMult6_eval_1_0 : refMult6 1 0 = (-1/2 : ℝ) := rfl
@[simp] theorem refMult6_eval_1_1 : refMult6 1 1 = (339/169 : ℝ) := rfl
@[simp] theorem refMult6_eval_1_2 : refMult6 1 2 = (0 : ℝ) := rfl
@[simp] theorem refMult6_eval_3_0 : refMult6 3 0 = (319/79 : ℝ) := rfl
@[simp] theorem refMult6_eval_3_1 : refMult6 3 1 = (-725/166 : ℝ) := rfl
@[simp] theorem refMult6_eval_3_2 : refMult6 3 2 = (1/54 : ℝ) := rfl
@[simp] theorem refMult6_eval_4_0 : refMult6 4 0 = (-383/192 : ℝ) := rfl
@[simp] theorem refMult6_eval_4_1 : refMult6 4 1 = (101/131 : ℝ) := rfl
@[simp] theorem refMult6_eval_4_2 : refMult6 4 2 = (0 : ℝ) := rfl
@[simp] theorem refMult7_eval_1_0 : refMult7 1 0 = (211/29 : ℝ) := rfl
@[simp] theorem refMult7_eval_1_1 : refMult7 1 1 = (3749/80 : ℝ) := rfl
@[simp] theorem refMult7_eval_1_2 : refMult7 1 2 = (2789/174 : ℝ) := rfl
@[simp] theorem refMult7_eval_2_0 : refMult7 2 0 = (1940/51 : ℝ) := rfl
@[simp] theorem refMult7_eval_2_1 : refMult7 2 1 = (49965/181 : ℝ) := rfl
@[simp] theorem refMult7_eval_2_2 : refMult7 2 2 = (18575/191 : ℝ) := rfl
@[simp] theorem refMult7_eval_5_0 : refMult7 5 0 = (-189/29 : ℝ) := rfl
@[simp] theorem refMult7_eval_5_1 : refMult7 5 1 = (-6912/167 : ℝ) := rfl
@[simp] theorem refMult7_eval_5_2 : refMult7 5 2 = (-1428/101 : ℝ) := rfl
@[simp] theorem refMult8_eval_1_0 : refMult8 1 0 = (-1/4 : ℝ) := rfl
@[simp] theorem refMult8_eval_1_1 : refMult8 1 1 = (206/135 : ℝ) := rfl
@[simp] theorem refMult8_eval_1_2 : refMult8 1 2 = (110/159 : ℝ) := rfl
@[simp] theorem refMult8_eval_2_0 : refMult8 2 0 = (-1841/130 : ℝ) := rfl
@[simp] theorem refMult8_eval_2_1 : refMult8 2 1 = (2228/187 : ℝ) := rfl
@[simp] theorem refMult8_eval_2_2 : refMult8 2 2 = (1939/174 : ℝ) := rfl
@[simp] theorem refMult8_eval_4_0 : refMult8 4 0 = (-72/31 : ℝ) := rfl
@[simp] theorem refMult8_eval_4_1 : refMult8 4 1 = (103/136 : ℝ) := rfl
@[simp] theorem refMult8_eval_4_2 : refMult8 4 2 = (163/135 : ℝ) := rfl
@[simp] theorem refMult9_eval_1_0 : refMult9 1 0 = (-77/38 : ℝ) := rfl
@[simp] theorem refMult9_eval_1_1 : refMult9 1 1 = (192/35 : ℝ) := rfl
@[simp] theorem refMult9_eval_1_2 : refMult9 1 2 = (-238/25 : ℝ) := rfl
@[simp] theorem refMult9_eval_2_0 : refMult9 2 0 = (2166/25 : ℝ) := rfl
@[simp] theorem refMult9_eval_2_1 : refMult9 2 1 = (-19019/116 : ℝ) := rfl
@[simp] theorem refMult9_eval_2_2 : refMult9 2 2 = (76935/179 : ℝ) := rfl
@[simp] theorem refMult9_eval_3_0 : refMult9 3 0 = (4685/163 : ℝ) := rfl
@[simp] theorem refMult9_eval_3_1 : refMult9 3 1 = (-4320/79 : ℝ) := rfl
@[simp] theorem refMult9_eval_3_2 : refMult9 3 2 = (2955/22 : ℝ) := rfl
@[simp] theorem refMult10_eval_0_0 : refMult10 0 0 = (136/71 : ℝ) := rfl
@[simp] theorem refMult10_eval_0_1 : refMult10 0 1 = (199/141 : ℝ) := rfl
@[simp] theorem refMult10_eval_0_2 : refMult10 0 2 = (-1/114 : ℝ) := rfl
@[simp] theorem refMult10_eval_4_0 : refMult10 4 0 = (-2 : ℝ) := rfl
@[simp] theorem refMult10_eval_4_1 : refMult10 4 1 = (-67/47 : ℝ) := rfl
@[simp] theorem refMult10_eval_4_2 : refMult10 4 2 = (1/85 : ℝ) := rfl
@[simp] theorem refMult10_eval_5_0 : refMult10 5 0 = (-57/34 : ℝ) := rfl
@[simp] theorem refMult10_eval_5_1 : refMult10 5 1 = (-207/139 : ℝ) := rfl
@[simp] theorem refMult10_eval_5_2 : refMult10 5 2 = (0 : ℝ) := rfl
@[simp] theorem refMult11_eval_0_0 : refMult11 0 0 = (300/191 : ℝ) := rfl
@[simp] theorem refMult11_eval_0_1 : refMult11 0 1 = (33/190 : ℝ) := rfl
@[simp] theorem refMult11_eval_0_2 : refMult11 0 2 = (0 : ℝ) := rfl
@[simp] theorem refMult11_eval_3_0 : refMult11 3 0 = (448/171 : ℝ) := rfl
@[simp] theorem refMult11_eval_3_1 : refMult11 3 1 = (-7/3 : ℝ) := rfl
@[simp] theorem refMult11_eval_3_2 : refMult11 3 2 = (1/52 : ℝ) := rfl
@[simp] theorem refMult11_eval_5_0 : refMult11 5 0 = (-92/179 : ℝ) := rfl
@[simp] theorem refMult11_eval_5_1 : refMult11 5 1 = (-153/127 : ℝ) := rfl
@[simp] theorem refMult11_eval_5_2 : refMult11 5 2 = (0 : ℝ) := rfl
@[simp] theorem refMult12_eval_0_0 : refMult12 0 0 = (7593/175 : ℝ) := rfl
@[simp] theorem refMult12_eval_0_1 : refMult12 0 1 = (-299/59 : ℝ) := rfl
@[simp] theorem refMult12_eval_0_2 : refMult12 0 2 = (-1/192 : ℝ) := rfl
@[simp] theorem refMult12_eval_3_0 : refMult12 3 0 = (5883/64 : ℝ) := rfl
@[simp] theorem refMult12_eval_3_1 : refMult12 3 1 = (-2125/174 : ℝ) := rfl
@[simp] theorem refMult12_eval_3_2 : refMult12 3 2 = (1/108 : ℝ) := rfl
@[simp] theorem refMult12_eval_4_0 : refMult12 4 0 = (-7561/149 : ℝ) := rfl
@[simp] theorem refMult12_eval_4_1 : refMult12 4 1 = (320/53 : ℝ) := rfl
@[simp] theorem refMult12_eval_4_2 : refMult12 4 2 = (1/164 : ℝ) := rfl
@[simp] theorem refMult13_eval_0_0 : refMult13 0 0 = (195/157 : ℝ) := rfl
@[simp] theorem refMult13_eval_0_1 : refMult13 0 1 = (65/187 : ℝ) := rfl
@[simp] theorem refMult13_eval_0_2 : refMult13 0 2 = (-48/155 : ℝ) := rfl
@[simp] theorem refMult13_eval_2_0 : refMult13 2 0 = (-285/47 : ℝ) := rfl
@[simp] theorem refMult13_eval_2_1 : refMult13 2 1 = (655/83 : ℝ) := rfl
@[simp] theorem refMult13_eval_2_2 : refMult13 2 2 = (1143/178 : ℝ) := rfl
@[simp] theorem refMult13_eval_5_0 : refMult13 5 0 = (-63/124 : ℝ) := rfl
@[simp] theorem refMult13_eval_5_1 : refMult13 5 1 = (-96/71 : ℝ) := rfl
@[simp] theorem refMult13_eval_5_2 : refMult13 5 2 = (-71/192 : ℝ) := rfl
@[simp] theorem refMult14_eval_0_0 : refMult14 0 0 = (28195/183 : ℝ) := rfl
@[simp] theorem refMult14_eval_0_1 : refMult14 0 1 = (-1896/187 : ℝ) := rfl
@[simp] theorem refMult14_eval_0_2 : refMult14 0 2 = (-11949/191 : ℝ) := rfl
@[simp] theorem refMult14_eval_2_0 : refMult14 2 0 = (-118852/97 : ℝ) := rfl
@[simp] theorem refMult14_eval_2_1 : refMult14 2 1 = (13539/158 : ℝ) := rfl
@[simp] theorem refMult14_eval_2_2 : refMult14 2 2 = (83099/166 : ℝ) := rfl
@[simp] theorem refMult14_eval_4_0 : refMult14 4 0 = (-36557/174 : ℝ) := rfl
@[simp] theorem refMult14_eval_4_1 : refMult14 4 1 = (2347/167 : ℝ) := rfl
@[simp] theorem refMult14_eval_4_2 : refMult14 4 2 = (12216/143 : ℝ) := rfl
@[simp] theorem refMult15_eval_0_0 : refMult15 0 0 = (719/191 : ℝ) := rfl
@[simp] theorem refMult15_eval_0_1 : refMult15 0 1 = (-176/141 : ℝ) := rfl
@[simp] theorem refMult15_eval_0_2 : refMult15 0 2 = (305/47 : ℝ) := rfl
@[simp] theorem refMult15_eval_2_0 : refMult15 2 0 = (22242/175 : ℝ) := rfl
@[simp] theorem refMult15_eval_2_1 : refMult15 2 1 = (-7035/109 : ℝ) := rfl
@[simp] theorem refMult15_eval_2_2 : refMult15 2 2 = (35111/98 : ℝ) := rfl
@[simp] theorem refMult15_eval_3_0 : refMult15 3 0 = (7959/190 : ℝ) := rfl
@[simp] theorem refMult15_eval_3_1 : refMult15 3 1 = (-2291/107 : ℝ) := rfl
@[simp] theorem refMult15_eval_3_2 : refMult15 3 2 = (17029/155 : ℝ) := rfl
@[simp] theorem refMult16_eval_0_0 : refMult16 0 0 = (89/44 : ℝ) := rfl
@[simp] theorem refMult16_eval_0_1 : refMult16 0 1 = (353/180 : ℝ) := rfl
@[simp] theorem refMult16_eval_0_2 : refMult16 0 2 = (1/192 : ℝ) := rfl
@[simp] theorem refMult16_eval_1_0 : refMult16 1 0 = (310/139 : ℝ) := rfl
@[simp] theorem refMult16_eval_1_1 : refMult16 1 1 = (183/71 : ℝ) := rfl
@[simp] theorem refMult16_eval_1_2 : refMult16 1 2 = (2/161 : ℝ) := rfl
@[simp] theorem refMult16_eval_5_0 : refMult16 5 0 = (-363/166 : ℝ) := rfl
@[simp] theorem refMult16_eval_5_1 : refMult16 5 1 = (-469/192 : ℝ) := rfl
@[simp] theorem refMult16_eval_5_2 : refMult16 5 2 = (-2/179 : ℝ) := rfl
@[simp] theorem refMult17_eval_0_0 : refMult17 0 0 = (130/93 : ℝ) := rfl
@[simp] theorem refMult17_eval_0_1 : refMult17 0 1 = (136/135 : ℝ) := rfl
@[simp] theorem refMult17_eval_0_2 : refMult17 0 2 = (-1/130 : ℝ) := rfl
@[simp] theorem refMult17_eval_1_0 : refMult17 1 0 = (118/103 : ℝ) := rfl
@[simp] theorem refMult17_eval_1_1 : refMult17 1 1 = (218/187 : ℝ) := rfl
@[simp] theorem refMult17_eval_1_2 : refMult17 1 2 = (0 : ℝ) := rfl
@[simp] theorem refMult17_eval_4_0 : refMult17 4 0 = (-212/145 : ℝ) := rfl
@[simp] theorem refMult17_eval_4_1 : refMult17 4 1 = (-190/189 : ℝ) := rfl
@[simp] theorem refMult17_eval_4_2 : refMult17 4 2 = (2/187 : ℝ) := rfl
@[simp] theorem refMult18_eval_0_0 : refMult18 0 0 = (277/188 : ℝ) := rfl
@[simp] theorem refMult18_eval_0_1 : refMult18 0 1 = (-27/152 : ℝ) := rfl
@[simp] theorem refMult18_eval_0_2 : refMult18 0 2 = (0 : ℝ) := rfl
@[simp] theorem refMult18_eval_1_0 : refMult18 1 0 = (-20/99 : ℝ) := rfl
@[simp] theorem refMult18_eval_1_1 : refMult18 1 1 = (209/112 : ℝ) := rfl
@[simp] theorem refMult18_eval_1_2 : refMult18 1 2 = (0 : ℝ) := rfl
@[simp] theorem refMult18_eval_3_0 : refMult18 3 0 = (427/136 : ℝ) := rfl
@[simp] theorem refMult18_eval_3_1 : refMult18 3 1 = (-599/165 : ℝ) := rfl
@[simp] theorem refMult18_eval_3_2 : refMult18 3 2 = (3/139 : ℝ) := rfl
@[simp] theorem refMult19_eval_0_0 : refMult19 0 0 = (125/108 : ℝ) := rfl
@[simp] theorem refMult19_eval_0_1 : refMult19 0 1 = (33/188 : ℝ) := rfl
@[simp] theorem refMult19_eval_0_2 : refMult19 0 2 = (-13/37 : ℝ) := rfl
@[simp] theorem refMult19_eval_1_0 : refMult19 1 0 = (1/5 : ℝ) := rfl
@[simp] theorem refMult19_eval_1_1 : refMult19 1 1 = (200/141 : ℝ) := rfl
@[simp] theorem refMult19_eval_1_2 : refMult19 1 2 = (89/187 : ℝ) := rfl
@[simp] theorem refMult19_eval_2_0 : refMult19 2 0 = (-117/17 : ℝ) := rfl
@[simp] theorem refMult19_eval_2_1 : refMult19 2 1 = (1287/157 : ℝ) := rfl
@[simp] theorem refMult19_eval_2_2 : refMult19 2 2 = (1114/165 : ℝ) := rfl

/-! ### Elementary facts about the witness -/

theorem refWeight_pos : ∀ c, 0 < refWeight c := by
  intro c; fin_cases c <;> norm_num

theorem refWeight_sum : ∑ c, refWeight c = 1 := by
  norm_num [Fin.sum_univ_six]

theorem refStress_full : ∀ c, refStress c ≠ 0 := by
  intro c; fin_cases c <;> norm_num

theorem refStress_zeroSum : ∑ c, refStress c = 0 := by
  norm_num [Fin.sum_univ_six]

theorem refStress_kills : ∑ c, refStress c • atomMatrix (refAtom c) = 0 := by
  ext rowIdx colIdx
  fin_cases rowIdx <;> fin_cases colIdx <;>
    norm_num [Fin.sum_univ_six, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]

theorem refPosFilter :
    (Finset.univ.filter fun c => 0 < refStress c) = ({0, 1, 2} : Finset (Fin 6)) := by
  ext c; fin_cases c <;> simp <;> try norm_num

theorem refNegFilter :
    (Finset.univ.filter fun c => refStress c < 0) = ({3, 4, 5} : Finset (Fin 6)) := by
  ext c; fin_cases c <;> simp <;> try norm_num

theorem refGram_posDef : (∑ c, refWeight c • atomMatrix (refAtom c)).PosDef := by
  have hsymm : (∑ c, refWeight c • atomMatrix (refAtom c))ᵀ
      = ∑ c, refWeight c • atomMatrix (refAtom c) := by
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun c _ => by
      rw [Matrix.transpose_smul,
        transpose_eq_of_isHermitian (posSemidef_atomMatrix _).1]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  rw [star_trivial, atomForm_eq_on_subset Finset.univ refWeight refAtom probe,
    Fin.sum_univ_six]
  have hdot0 : refAtom 0 ⬝ᵥ probe = (1686555/2131109 : ℝ) * probe 0 := by
    simp [dotProduct, Fin.sum_univ_three]
  have hdot1 : refAtom 1 ⬝ᵥ probe = (9/10 : ℝ) * probe 1 := by
    simp [dotProduct, Fin.sum_univ_three]
  have hdot2 : refAtom 2 ⬝ᵥ probe = (31/2 : ℝ) * probe 2 := by
    simp [dotProduct, Fin.sum_univ_three]
  rw [hdot0, hdot1, hdot2]
  have hterm3 : 0 ≤ refWeight 3 * (refAtom 3 ⬝ᵥ probe) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hterm4 : 0 ≤ refWeight 4 * (refAtom 4 ⬝ᵥ probe) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hterm5 : 0 ≤ refWeight 5 * (refAtom 5 ⬝ᵥ probe) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hcoord : probe 0 ≠ 0 ∨ probe 1 ≠ 0 ∨ probe 2 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hprobe (funext fun coordIdx => by
      fin_cases coordIdx <;> simp [hall.1, hall.2.1, hall.2.2])
  rcases hcoord with hcoordNe | hcoordNe | hcoordNe
  · have hposTerm : 0 < refWeight 0 * ((1686555/2131109 : ℝ) * probe 0) ^ 2 := by
      have hbaseNe : (1686555/2131109 : ℝ) * probe 0 ≠ 0 :=
        mul_ne_zero (by norm_num) hcoordNe
      have hsqPos : 0 < ((1686555/2131109 : ℝ) * probe 0) ^ 2 := by
        rw [pow_two]; exact mul_self_pos.mpr hbaseNe
      exact mul_pos (by norm_num) hsqPos
    have hdiag1 : 0 ≤ refWeight 1 * ((9/10 : ℝ) * probe 1) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have hdiag2 : 0 ≤ refWeight 2 * ((31/2 : ℝ) * probe 2) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    linarith [hposTerm, hdiag1, hdiag2, hterm3, hterm4, hterm5]
  · have hposTerm : 0 < refWeight 1 * ((9/10 : ℝ) * probe 1) ^ 2 := by
      have hbaseNe : (9/10 : ℝ) * probe 1 ≠ 0 :=
        mul_ne_zero (by norm_num) hcoordNe
      have hsqPos : 0 < ((9/10 : ℝ) * probe 1) ^ 2 := by
        rw [pow_two]; exact mul_self_pos.mpr hbaseNe
      exact mul_pos (by norm_num) hsqPos
    have hdiag0 : 0 ≤ refWeight 0 * ((1686555/2131109 : ℝ) * probe 0) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have hdiag2 : 0 ≤ refWeight 2 * ((31/2 : ℝ) * probe 2) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    linarith [hposTerm, hdiag0, hdiag2, hterm3, hterm4, hterm5]
  · have hposTerm : 0 < refWeight 2 * ((31/2 : ℝ) * probe 2) ^ 2 := by
      have hbaseNe : (31/2 : ℝ) * probe 2 ≠ 0 :=
        mul_ne_zero (by norm_num) hcoordNe
      have hsqPos : 0 < ((31/2 : ℝ) * probe 2) ^ 2 := by
        rw [pow_two]; exact mul_self_pos.mpr hbaseNe
      exact mul_pos (by norm_num) hsqPos
    have hdiag0 : 0 ≤ refWeight 0 * ((1686555/2131109 : ℝ) * probe 0) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have hdiag1 : 0 ≤ refWeight 1 * ((9/10 : ℝ) * probe 1) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    linarith [hposTerm, hdiag0, hdiag1, hterm3, hterm4, hterm5]

theorem refPrimitive : ∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ),
    keptLabel ≠ dropLabel → refAtom dropLabel ≠ ratio • refAtom keptLabel := by
  intro keptLabel dropLabel ratio hne heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    first
      | exact hne rfl
      | ((try norm_num at h0)
         (try norm_num at h1)
         (try norm_num at h2)
         all_goals (first
           | linarith [h0, h1, h2]
           | linarith [h0, h1]
           | linarith [h0, h2]
           | linarith [h1, h2]))

theorem refWitnessPos_ne : refWitnessPos ≠ 0 := by
  intro hzero
  have hentry := congrFun hzero 0
  norm_num at hentry

theorem refPosGap_value :
    (∑ c ∈ ({0, 1, 2} : Finset (Fin 6)),
        (refAtom c ⬝ᵥ refWitnessPos) ^ 2)
      - (∑ c, refWeight c * (refAtom c ⬝ᵥ refWitnessPos) ^ 2) ≤ 0 := by
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide), Fin.sum_univ_six]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refWitnessNeg_ne : refWitnessNeg ≠ 0 := by
  intro hzero
  have hentry := congrFun hzero 1
  norm_num at hentry

theorem refNegGap_value :
    (∑ c ∈ ({3, 4, 5} : Finset (Fin 6)),
        (refAtom c ⬝ᵥ refWitnessNeg) ^ 2)
      - (∑ c, refWeight c * (refAtom c ⬝ᵥ refWitnessNeg) ^ 2) ≤ 0 := by
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide), Fin.sum_univ_six]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound0 :
    1 ≤ ∑ c ∈ (({0, 1, 2} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult0 c)
          - ∑ d ∈ ({0, 1, 2} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult0 c) ^ 2) := by
  rw [show (({0, 1, 2} : Finset (Fin 6)))ᶜ
      = ({3, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 2 by decide) (show (1 : Fin 6) ≠ 2 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound1 :
    1 ≤ ∑ c ∈ (({0, 1, 3} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult1 c)
          - ∑ d ∈ ({0, 1, 3} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult1 c) ^ 2) := by
  rw [show (({0, 1, 3} : Finset (Fin 6)))ᶜ
      = ({2, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 3 by decide) (show (1 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound2 :
    1 ≤ ∑ c ∈ (({0, 1, 4} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult2 c)
          - ∑ d ∈ ({0, 1, 4} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult2 c) ^ 2) := by
  rw [show (({0, 1, 4} : Finset (Fin 6)))ᶜ
      = ({2, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (1 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound3 :
    1 ≤ ∑ c ∈ (({0, 1, 5} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult3 c)
          - ∑ d ∈ ({0, 1, 5} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult3 c) ^ 2) := by
  rw [show (({0, 1, 5} : Finset (Fin 6)))ᶜ
      = ({2, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (1 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound4 :
    1 ≤ ∑ c ∈ (({0, 2, 3} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult4 c)
          - ∑ d ∈ ({0, 2, 3} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult4 c) ^ 2) := by
  rw [show (({0, 2, 3} : Finset (Fin 6)))ᶜ
      = ({1, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 3 by decide) (show (2 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound5 :
    1 ≤ ∑ c ∈ (({0, 2, 4} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult5 c)
          - ∑ d ∈ ({0, 2, 4} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult5 c) ^ 2) := by
  rw [show (({0, 2, 4} : Finset (Fin 6)))ᶜ
      = ({1, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (2 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound6 :
    1 ≤ ∑ c ∈ (({0, 2, 5} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult6 c)
          - ∑ d ∈ ({0, 2, 5} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult6 c) ^ 2) := by
  rw [show (({0, 2, 5} : Finset (Fin 6)))ᶜ
      = ({1, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (2 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound7 :
    1 ≤ ∑ c ∈ (({0, 3, 4} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult7 c)
          - ∑ d ∈ ({0, 3, 4} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult7 c) ^ 2) := by
  rw [show (({0, 3, 4} : Finset (Fin 6)))ᶜ
      = ({1, 2, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 3 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound8 :
    1 ≤ ∑ c ∈ (({0, 3, 5} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult8 c)
          - ∑ d ∈ ({0, 3, 5} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult8 c) ^ 2) := by
  rw [show (({0, 3, 5} : Finset (Fin 6)))ᶜ
      = ({1, 2, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 3 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound9 :
    1 ≤ ∑ c ∈ (({0, 4, 5} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult9 c)
          - ∑ d ∈ ({0, 4, 5} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult9 c) ^ 2) := by
  rw [show (({0, 4, 5} : Finset (Fin 6)))ᶜ
      = ({1, 2, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 4 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound10 :
    1 ≤ ∑ c ∈ (({1, 2, 3} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult10 c)
          - ∑ d ∈ ({1, 2, 3} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult10 c) ^ 2) := by
  rw [show (({1, 2, 3} : Finset (Fin 6)))ᶜ
      = ({0, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 3 by decide) (show (2 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound11 :
    1 ≤ ∑ c ∈ (({1, 2, 4} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult11 c)
          - ∑ d ∈ ({1, 2, 4} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult11 c) ^ 2) := by
  rw [show (({1, 2, 4} : Finset (Fin 6)))ᶜ
      = ({0, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 4 by decide) (show (2 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound12 :
    1 ≤ ∑ c ∈ (({1, 2, 5} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult12 c)
          - ∑ d ∈ ({1, 2, 5} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult12 c) ^ 2) := by
  rw [show (({1, 2, 5} : Finset (Fin 6)))ᶜ
      = ({0, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (2 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound13 :
    1 ≤ ∑ c ∈ (({1, 3, 4} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult13 c)
          - ∑ d ∈ ({1, 3, 4} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult13 c) ^ 2) := by
  rw [show (({1, 3, 4} : Finset (Fin 6)))ᶜ
      = ({0, 2, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 3 by decide)
    (show (1 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound14 :
    1 ≤ ∑ c ∈ (({1, 3, 5} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult14 c)
          - ∑ d ∈ ({1, 3, 5} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult14 c) ^ 2) := by
  rw [show (({1, 3, 5} : Finset (Fin 6)))ᶜ
      = ({0, 2, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 3 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound15 :
    1 ≤ ∑ c ∈ (({1, 4, 5} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult15 c)
          - ∑ d ∈ ({1, 4, 5} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult15 c) ^ 2) := by
  rw [show (({1, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 2, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 4 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound16 :
    1 ≤ ∑ c ∈ (({2, 3, 4} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult16 c)
          - ∑ d ∈ ({2, 3, 4} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult16 c) ^ 2) := by
  rw [show (({2, 3, 4} : Finset (Fin 6)))ᶜ
      = ({0, 1, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 3 by decide)
    (show (2 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound17 :
    1 ≤ ∑ c ∈ (({2, 3, 5} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult17 c)
          - ∑ d ∈ ({2, 3, 5} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult17 c) ^ 2) := by
  rw [show (({2, 3, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 3 by decide)
    (show (2 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound18 :
    1 ≤ ∑ c ∈ (({2, 4, 5} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult18 c)
          - ∑ d ∈ ({2, 4, 5} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult18 c) ^ 2) := by
  rw [show (({2, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 4 by decide)
    (show (2 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem refBudgetBound19 :
    1 ≤ ∑ c ∈ (({3, 4, 5} : Finset (Fin 6)))ᶜ, refWeight c
        * (2 * (refAtom c ⬝ᵥ refMult19 c)
          - ∑ d ∈ ({3, 4, 5} : Finset (Fin 6)), (1 - refWeight d)
              * (refAtom d ⬝ᵥ refMult19 c) ^ 2) := by
  rw [show (({3, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 2} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (3 : Fin 6) ≠ 4 by decide)
    (show (3 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem triple_cases : ∀ s : Finset (Fin 6), s.card = 3 →
    s = {0, 1, 2} ∨ s = {0, 1, 3} ∨ s = {0, 1, 4} ∨ s = {0, 1, 5} ∨ s = {0, 2, 3} ∨ s = {0, 2, 4} ∨ s = {0, 2, 5} ∨ s = {0, 3, 4} ∨ s = {0, 3, 5} ∨ s = {0, 4, 5} ∨ s = {1, 2, 3} ∨ s = {1, 2, 4} ∨ s = {1, 2, 5} ∨ s = {1, 3, 4} ∨ s = {1, 3, 5} ∨ s = {1, 4, 5} ∨ s = {2, 3, 4} ∨ s = {2, 3, 5} ∨ s = {2, 4, 5} ∨ s = {3, 4, 5} := by
  decide

/-! ## The refutation -/

/-- **THE PURE-TRIPLE SELECTION CONJECTURE IS FALSE.**  The witness design
satisfies every hypothesis of the conjecture — primitive, full-support
zero-sum stress, no mass gap in either orientation, free-mass budget failing
at all twenty triples — yet neither pure stress side dominates. -/
theorem pureTripleZeroSumSelection_refuted :
    ¬ PureTripleZeroSumSelectionSixThree := by
  intro hconjecture
  obtain ⟨whitener, hwUnit, hwhiten⟩ := exists_congruence_to_one refGram_posDef
  have hstressDesign := stress_whitenedFamilyDesign refAtom refWeight refWeight_pos
    refWeight_sum whitener hwhiten refStress_kills
  have hprimitive : IsPrimitiveDesign
      (whitenedFamilyDesign refAtom refWeight refWeight_pos refWeight_sum
        whitener hwhiten) := by
    intro keptLabel dropLabel ratio hlabelsNe
    have hdetNe : (whitenerᵀ).det ≠ 0 := by
      rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mp hwUnit
    exact mulVec_ne_smul_of_ne_smul hdetNe
      (refPrimitive keptLabel dropLabel ratio hlabelsNe)
  have hnoGapPos : ¬ HasStressMassGap
      (whitenedFamilyDesign refAtom refWeight refWeight_pos refWeight_sum
        whitener hwhiten) refStress := by
    refine not_hasStressMassGap_of_crossing 0 3 (by norm_num)
      (by norm_num) ?_
    show (1 - refWeight 0) * (-refStress 3) ≤ refWeight 3 * refStress 0
    norm_num
  have hnoGapNeg : ¬ HasStressMassGap
      (whitenedFamilyDesign refAtom refWeight refWeight_pos refWeight_sum
        whitener hwhiten) (-refStress) := by
    refine not_hasStressMassGap_of_crossing 5 2
      (by norm_num) (by norm_num) ?_
    show (1 - refWeight 5) * (-(-refStress) 2)
      ≤ refWeight 2 * (-refStress) 5
    norm_num
  have hbudget : ∀ triple : Finset (Fin 6), triple.card = 3 →
      ¬ HasFreeMassBudget
        (whitenedFamilyDesign refAtom refWeight refWeight_pos refWeight_sum
          whitener hwhiten) triple := by
    intro triple hcard
    rcases triple_cases triple hcard with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult0 refBudgetBound0
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult1 refBudgetBound1
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult2 refBudgetBound2
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult3 refBudgetBound3
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult4 refBudgetBound4
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult5 refBudgetBound5
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult6 refBudgetBound6
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult7 refBudgetBound7
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult8 refBudgetBound8
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult9 refBudgetBound9
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult10 refBudgetBound10
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult11 refBudgetBound11
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult12 refBudgetBound12
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult13 refBudgetBound13
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult14 refBudgetBound14
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult15 refBudgetBound15
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult16 refBudgetBound16
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult17 refBudgetBound17
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult18 refBudgetBound18
    · exact not_hasFreeMassBudget_whitened_of_rawBound refAtom refWeight
        refWeight_pos refWeight_sum hwUnit hwhiten _
        refMult19 refBudgetBound19
  rcases hconjecture
      (whitenedFamilyDesign refAtom refWeight refWeight_pos refWeight_sum
        whitener hwhiten)
      refStress hstressDesign refStress_full refStress_zeroSum hprimitive
      hnoGapPos hnoGapNeg hbudget with hposSide | hnegSide
  · rw [refPosFilter, posDef_gap_whitenedFamilyDesign_iff refAtom refWeight
      refWeight_pos refWeight_sum hwhiten hwUnit] at hposSide
    exact raw_gap_not_posDef_of_witnessVec refAtom refWeight _ refWitnessPos
      refWitnessPos_ne refPosGap_value hposSide
  · rw [refNegFilter, posDef_gap_whitenedFamilyDesign_iff refAtom refWeight
      refWeight_pos refWeight_sum hwhiten hwUnit] at hnegSide
    exact raw_gap_not_posDef_of_witnessVec refAtom refWeight _ refWitnessNeg
      refWitnessNeg_ne refNegGap_value hnegSide

end PureTripleRefutation
end Gtz
