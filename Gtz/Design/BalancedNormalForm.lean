/-
# The two-frame normal form of the balanced stratum, and its diagonal criterion

Branch (ii) of `Gtz.sixThree_stress_trichotomy` is the stratum carrying a
FULL-SUPPORT stress.  There the split law forces exactly three positive and
three negative stress coefficients and a common middle matrix
`X = sum_P z_c A_c = sum_N (-z_c) A_c` which is positive definite.  Whitening
`X` turns EACH side into an orthonormal triple, and the landed
`Gtz.twoFrame_normalForm` says so for the positive side.  This file says it for
BOTH sides AT ONCE — the two frames are orthonormal in the SAME whitened
coordinates, because the middle matrix they whiten is literally the same
matrix — and then reads the domination test off in those coordinates.

## What the common whitener buys

Write `u_a` for the whitened positive frame and `v_b` for the whitened negative
one, both orthonormal bases of `R^3`.  Transporting a probe by `whitener^T`
turns the domination gap of ANY subset into a free-minus-bound sum of squared
pairings against the whitened atoms
(`gapForm_eq_freeMinusBound_at_transportedProbe`), and the whitened atoms are
just the frame vectors rescaled by the stress:

    whitener *ᵥ atom (posEnum a) = (1 / sqrt (z (posEnum a))) • u a
    whitener *ᵥ atom (negEnum b) = (1 / sqrt (-z (negEnum b))) • v b.

For the POSITIVE triple the free half is therefore DIAGONAL in the `u` basis,
and the whole test collapses to one scalar inequality in three real
coordinates:

    sum_a ((1 - t_{P a}) / z_{P a}) * coeff a ^ 2
      >  sum_b (t_{N b} / (-z_{N b})) * (sum_a coeff a * (v b . u a)) ^ 2 .

That is `sixThree_posSide_dominates_iff_diagonalCriterion`, an EQUIVALENCE, not
a sufficient condition: nine variables become three, one positive semidefinite
matrix tested against a diagonal one.  Running it on the negated stress gives
the mirror statement at the negative triple.

## The overlap inequality

The two frames cannot be aligned wherever the weights are large.  Writing
`tau c = sqrt (t_c / (1 - t_c))`, the frame overlaps obey the UNCONDITIONAL

    sum_a sum_b  tau (P a) * tau (N b) * (u a . v b) ^ 2  <  1

(`frameOverlap_weightedSum_lt_one`), by Parseval on each frame, one
arithmetic-geometric step, and the fact that a positive weight outside a side
is what separates `1 - t_c` from the other side's total mass.  The bound is
TIGHT in the limit where one positive atom and one negative atom become
parallel and their two weights exhaust the design, which is exactly the corner
where the domination margin of this stratum degenerates to zero.
-/
import Gtz.Reduction.HingeFunnel
import Gtz.Reduction.StressMassGap
import Gtz.Quantitative.HingeStressNarrowing
import Gtz.Design.BalancedStratum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Part 1: the gap form at a transported probe -/

/-- **THE GAP FORM AT A TRANSPORTED PROBE.**  Pairing the domination gap against
`transposeʷ *ᵥ probe` is the free-minus-bound sum of squared pairings of the
WHITENED atoms against `probe`, because moving the congruence across the dot
product replaces every atom by its whitened image. -/
theorem gapForm_eq_freeMinusBound_at_transportedProbe (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (whitener : Matrix (Fin rank) (Fin rank) ℝ)
    (probe : Fin rank → ℝ) :
    (whitenerᵀ *ᵥ probe) ⬝ᵥ ((subsetSum design selected - 1) *ᵥ (whitenerᵀ *ᵥ probe))
      = (∑ c ∈ selected,
            (1 - design.weight c) * ((whitener *ᵥ design.atom c) ⬝ᵥ probe) ^ 2)
        - ∑ c ∈ selectedᶜ,
            design.weight c * ((whitener *ᵥ design.atom c) ⬝ᵥ probe) ^ 2 := by
  classical
  have htransport : ∀ c : Fin size,
      design.atom c ⬝ᵥ (whitenerᵀ *ᵥ probe) = (whitener *ᵥ design.atom c) ⬝ᵥ probe := by
    intro c
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
      dotProduct_comm]
  rw [subsetSum_sub_one_eq_freeMass_sub_boundMass, Matrix.sub_mulVec, dotProduct_sub,
    atomForm_eq_on_subset, atomForm_eq_on_subset]
  exact congrArg₂ (· - ·)
    (Finset.sum_congr rfl fun c _ => by rw [htransport c])
    (Finset.sum_congr rfl fun c _ => by rw [htransport c])

/-- **THE DOMINATION TEST IN WHITENED COORDINATES.**  A congruence by an
invertible matrix is a bijection on probes, so the gap is positive definite
exactly when its free-minus-bound form is positive at every nonzero probe of
the whitened picture. -/
theorem posDef_gap_iff_forall_whitenedProbe (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) {whitener : Matrix (Fin rank) (Fin rank) ℝ}
    (hdetNe : whitener.det ≠ 0) :
    (subsetSum design selected - 1).PosDef
      ↔ ∀ probe : Fin rank → ℝ, probe ≠ 0 →
          (∑ c ∈ selectedᶜ,
              design.weight c * ((whitener *ᵥ design.atom c) ⬝ᵥ probe) ^ 2)
            < ∑ c ∈ selected,
                (1 - design.weight c) * ((whitener *ᵥ design.atom c) ⬝ᵥ probe) ^ 2 := by
  classical
  have hsymm : (subsetSum design selected - 1)ᵀ = subsetSum design selected - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, transpose_subsetSum]
  have htransposeDet : (whitenerᵀ).det ≠ 0 := by rwa [Matrix.det_transpose]
  have hunit : IsUnit (whitenerᵀ).det := isUnit_iff_ne_zero.mpr htransposeDet
  constructor
  · intro hposDef probe hprobeNe
    have hnonzero : whitenerᵀ *ᵥ probe ≠ 0 := by
      intro hzero
      exact hprobeNe (Matrix.eq_zero_of_mulVec_eq_zero htransposeDet hzero)
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hnonzero
    rw [star_trivial, gapForm_eq_freeMinusBound_at_transportedProbe] at hpos
    linarith
  · intro hcriterion
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hsymm, fun testVec htestNe => ?_⟩
    obtain ⟨probe, hprobe⟩ : ∃ probe : Fin rank → ℝ, whitenerᵀ *ᵥ probe = testVec :=
      ⟨(whitenerᵀ)⁻¹ *ᵥ testVec, by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]⟩
    have hprobeNe : probe ≠ 0 := by
      intro hzero
      exact htestNe (by rw [← hprobe, hzero, Matrix.mulVec_zero])
    have hstep := hcriterion probe hprobeNe
    rw [star_trivial, ← hprobe, gapForm_eq_freeMinusBound_at_transportedProbe]
    linarith

/-! ## Part 2: one whitener orthonormalises BOTH stress frames -/

/-- Reindexing a filtered sum along an enumeration of the filter. -/
theorem sum_filter_eq_sum_enum {count enumSize : ℕ} {carrier : Type*} [AddCommMonoid carrier]
    (predicate : Fin count → Prop) [DecidablePred predicate]
    (enum : Fin enumSize → Fin count) (hinjective : Function.Injective enum)
    (hmem : ∀ idx, predicate (enum idx))
    (honto : ∀ label, predicate label → ∃ idx, enum idx = label)
    (summand : Fin count → carrier) :
    ∑ label ∈ Finset.univ.filter predicate, summand label = ∑ idx, summand (enum idx) := by
  classical
  refine (Finset.sum_bij (fun idx _ => enum idx)
    (fun idx _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem idx⟩)
    (fun leftIdx _ rightIdx _ hEq => hinjective hEq) (fun label hlabel => ?_)
    (fun idx _ => rfl)).symm
  obtain ⟨idx, hidx⟩ := honto label (Finset.mem_filter.mp hlabel).2
  exact ⟨idx, Finset.mem_univ idx, hidx⟩

/-- **A WHITENED SIDE IS AN ORTHONORMAL TRIPLE.**  If a congruence carries a
coefficient-weighted atom sum over a three-element selection to the identity,
the transported atoms scaled by the square roots of their coefficients are
pairwise orthonormal.  The `Gtz.twoFrame_normalForm` argument, stated for an
arbitrary selection and coefficient family so that it can be run on BOTH sides
of a stress with the SAME whitener. -/
theorem orthonormalWhitenedFrame_of_sandwich {count : ℕ}
    (atomFamily : Fin count → Fin 3 → ℝ) (coeff : Fin count → ℝ)
    (selected : Finset (Fin count)) {whitener : Matrix (Fin 3) (Fin 3) ℝ}
    (hsandwich :
      whitener * (∑ label ∈ selected, coeff label • atomMatrix (atomFamily label))
        * whitenerᵀ = 1)
    (frameEnum : Fin 3 → Fin count) (hinjective : Function.Injective frameEnum)
    (hmem : ∀ frameIdx, frameEnum frameIdx ∈ selected)
    (honto : ∀ label ∈ selected, ∃ frameIdx, frameEnum frameIdx = label)
    (hcoeffPos : ∀ frameIdx, 0 < coeff (frameEnum frameIdx)) (leftIdx rightIdx : Fin 3) :
    (Real.sqrt (coeff (frameEnum leftIdx)) • (whitener *ᵥ atomFamily (frameEnum leftIdx)))
        ⬝ᵥ (Real.sqrt (coeff (frameEnum rightIdx))
          • (whitener *ᵥ atomFamily (frameEnum rightIdx)))
      = if leftIdx = rightIdx then 1 else 0 := by
  classical
  have hterm : ∀ frameIdx : Fin 3,
      Matrix.vecMulVec
        (Real.sqrt (coeff (frameEnum frameIdx)) • (whitener *ᵥ atomFamily (frameEnum frameIdx)))
        (Real.sqrt (coeff (frameEnum frameIdx)) • (whitener *ᵥ atomFamily (frameEnum frameIdx)))
      = coeff (frameEnum frameIdx) • atomMatrix (whitener *ᵥ atomFamily (frameEnum frameIdx)) := by
    intro frameIdx
    show atomMatrix _ = _
    rw [atomMatrix_smul, Real.sq_sqrt (hcoeffPos frameIdx).le]
  have hreindex : ∑ frameIdx : Fin 3,
        coeff (frameEnum frameIdx) • atomMatrix (whitener *ᵥ atomFamily (frameEnum frameIdx))
      = ∑ label ∈ selected, coeff label • atomMatrix (whitener *ᵥ atomFamily label) := by
    refine Finset.sum_bij (fun frameIdx _ => frameEnum frameIdx)
      (fun frameIdx _ => hmem frameIdx)
      (fun leftFrame _ rightFrame _ hEq => hinjective hEq) (fun label hlabel => ?_)
      (fun frameIdx _ => rfl)
    obtain ⟨frameIdx, hframeIdx⟩ := honto label hlabel
    exact ⟨frameIdx, Finset.mem_univ frameIdx, hframeIdx⟩
  have hframeSum : ∑ frameIdx : Fin 3, Matrix.vecMulVec
      (Real.sqrt (coeff (frameEnum frameIdx)) • (whitener *ᵥ atomFamily (frameEnum frameIdx)))
      (Real.sqrt (coeff (frameEnum frameIdx)) • (whitener *ᵥ atomFamily (frameEnum frameIdx)))
      = 1 :=
    (Finset.sum_congr rfl fun frameIdx _ => hterm frameIdx).trans
      (hreindex.trans (whitened_sum_parseval _ _ _ hsandwich))
  exact orthonormal_of_three_rank_ones_sum_one
    (fun frameIdx => Real.sqrt (coeff (frameEnum frameIdx))
      • (whitener *ᵥ atomFamily (frameEnum frameIdx))) hframeSum leftIdx rightIdx

/-- **THE TWO-FRAME NORMAL FORM, BOTH FRAMES AT ONCE.**  A full-support stress
of a `(6,3)` design has a single whitener that turns the positive side AND the
negative side into orthonormal bases of `R^3`.  One whitener suffices because
the matrix the two sides whiten is literally the same — the middle matrix
`X = sum_P z_c A_c = sum_N (-z_c) A_c` of the balanced branch.  The landed
`Gtz.twoFrame_normalForm` gives the positive half only, with no claim that the
negative half is orthonormal in the same coordinates. -/
theorem twoFrame_normalForm_bothFrames (design : WeightedDesign 6 3)
    {stressCoeff : Fin 6 → ℝ}
    (hstress : ∑ label, stressCoeff label • atomMatrix (design.atom label) = 0)
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (posEnum negEnum : Fin 3 → Fin 6)
    (hposInjective : Function.Injective posEnum)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hposOnto : ∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label)
    (hnegInjective : Function.Injective negEnum)
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hnegOnto : ∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label) :
    ∃ whitener : Matrix (Fin 3) (Fin 3) ℝ, whitener.det ≠ 0
      ∧ (∀ leftIdx rightIdx : Fin 3,
          (Real.sqrt (stressCoeff (posEnum leftIdx))
              • (whitener *ᵥ design.atom (posEnum leftIdx)))
            ⬝ᵥ (Real.sqrt (stressCoeff (posEnum rightIdx))
              • (whitener *ᵥ design.atom (posEnum rightIdx)))
          = if leftIdx = rightIdx then 1 else 0)
      ∧ (∀ leftIdx rightIdx : Fin 3,
          (Real.sqrt (-stressCoeff (negEnum leftIdx))
              • (whitener *ᵥ design.atom (negEnum leftIdx)))
            ⬝ᵥ (Real.sqrt (-stressCoeff (negEnum rightIdx))
              • (whitener *ᵥ design.atom (negEnum rightIdx)))
          = if leftIdx = rightIdx then 1 else 0) := by
  classical
  obtain ⟨whitener, hdetNe, hsandwichPos⟩ :=
    exists_whitening_of_positiveSide design hstress hfull
  have hmiddle := posSide_sum_eq_negSide_sum design.atom hstress hfull
  have hsandwichNeg :
      whitener * (∑ label ∈ Finset.univ.filter (fun label => stressCoeff label < 0),
        (-stressCoeff label) • atomMatrix (design.atom label)) * whitenerᵀ = 1 := by
    rw [← hmiddle]; exact hsandwichPos
  refine ⟨whitener, hdetNe, ?_, ?_⟩
  · exact orthonormalWhitenedFrame_of_sandwich design.atom stressCoeff
      (Finset.univ.filter fun label => 0 < stressCoeff label) hsandwichPos posEnum
      hposInjective
      (fun posIdx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hposSign posIdx⟩)
      (fun label hlabel => hposOnto label (Finset.mem_filter.mp hlabel).2) hposSign
  · exact orthonormalWhitenedFrame_of_sandwich design.atom (fun label => -stressCoeff label)
      (Finset.univ.filter fun label => stressCoeff label < 0) hsandwichNeg negEnum
      hnegInjective
      (fun negIdx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnegSign negIdx⟩)
      (fun label hlabel => hnegOnto label (Finset.mem_filter.mp hlabel).2)
      (fun negIdx => neg_pos.mpr (hnegSign negIdx))

/-! ## Part 3: the criterion at the positive triple, and its diagonal form -/

/-- **AN ORTHONORMAL TRIPLE OF `R^3` RESOLVES THE IDENTITY.**  The converse of
`Gtz.orthonormal_of_three_rank_ones_sum_one`: pairwise orthonormality of three
vectors already forces their rank-ones to sum to the identity, because a square
matrix with `V Vᵀ = 1` also has `Vᵀ V = 1`. -/
theorem sum_rankOne_eq_one_of_orthonormalFrame (frame : Fin 3 → Fin 3 → ℝ)
    (horthonormal : ∀ leftIdx rightIdx : Fin 3,
      frame leftIdx ⬝ᵥ frame rightIdx = if leftIdx = rightIdx then 1 else 0) :
    ∑ frameIdx, Matrix.vecMulVec (frame frameIdx) (frame frameIdx)
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hrows : (Matrix.of fun row col => frame row col)
      * (Matrix.of fun row col => frame row col)ᵀ = 1 := by
    ext leftIdx rightIdx
    rw [Matrix.mul_apply, Matrix.one_apply, ← horthonormal leftIdx rightIdx]
    exact Finset.sum_congr rfl fun coord _ => by
      rw [Matrix.transpose_apply]; simp only [Matrix.of_apply]
  have hcols := mul_eq_one_comm.mp hrows
  ext rowIdx colIdx
  have hentry : ((Matrix.of fun row col => frame row col)ᵀ
      * (Matrix.of fun row col => frame row col)) rowIdx colIdx
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) rowIdx colIdx := by rw [hcols]
  rw [Matrix.sum_apply, ← hentry, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun frameIdx _ => by
    rw [Matrix.vecMulVec_apply, Matrix.transpose_apply]; simp only [Matrix.of_apply]

/-- Every probe is its own expansion in an orthonormal triple. -/
theorem eq_sum_smul_of_orthonormalFrame (frame : Fin 3 → Fin 3 → ℝ)
    (horthonormal : ∀ leftIdx rightIdx : Fin 3,
      frame leftIdx ⬝ᵥ frame rightIdx = if leftIdx = rightIdx then 1 else 0)
    (probe : Fin 3 → ℝ) : probe = ∑ frameIdx, (frame frameIdx ⬝ᵥ probe) • frame frameIdx := by
  have happlied := congrArg (fun gramSum => gramSum *ᵥ probe)
    (sum_rankOne_eq_one_of_orthonormalFrame frame horthonormal)
  simp only [Matrix.sum_mulVec, Matrix.one_mulVec] at happlied
  calc probe
      = ∑ frameIdx, Matrix.vecMulVec (frame frameIdx) (frame frameIdx) *ᵥ probe :=
        happlied.symm
    _ = ∑ frameIdx, (frame frameIdx ⬝ᵥ probe) • frame frameIdx :=
        Finset.sum_congr rfl fun frameIdx _ => by rw [vecMulVec_mulVec_eq]

/-- The coefficients of an expansion in an orthonormal triple are the pairings. -/
theorem dotProduct_sum_smul_orthonormalFrame (frame : Fin 3 → Fin 3 → ℝ)
    (horthonormal : ∀ leftIdx rightIdx : Fin 3,
      frame leftIdx ⬝ᵥ frame rightIdx = if leftIdx = rightIdx then 1 else 0)
    (coeff : Fin 3 → ℝ) (readIdx : Fin 3) :
    frame readIdx ⬝ᵥ (∑ frameIdx, coeff frameIdx • frame frameIdx) = coeff readIdx := by
  rw [dotProduct_sum]
  rw [Finset.sum_congr rfl fun frameIdx _ =>
    (by rw [dotProduct_smul, smul_eq_mul, horthonormal readIdx frameIdx, mul_comm]
      : frame readIdx ⬝ᵥ (coeff frameIdx • frame frameIdx)
        = coeff frameIdx * if readIdx = frameIdx then 1 else 0)]
  simp

/-- **THE POSITIVE TRIPLE'S TEST IN THE TWO FRAMES.**  Whitening turns the
domination test of the positive stress side into a comparison of two sums of
squared pairings against the two whitened frames.  Purely algebraic: the frames
need not be orthonormal for this step, only the stress signs and the
invertibility of the whitener. -/
theorem sixThree_posSide_dominates_iff_frameCriterion (design : WeightedDesign 6 3)
    {stressCoeff : Fin 6 → ℝ} (hfull : ∀ label, stressCoeff label ≠ 0)
    (posEnum negEnum : Fin 3 → Fin 6)
    (hposInjective : Function.Injective posEnum)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hposOnto : ∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label)
    (hnegInjective : Function.Injective negEnum)
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hnegOnto : ∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label)
    {whitener : Matrix (Fin 3) (Fin 3) ℝ} (hdetNe : whitener.det ≠ 0) :
    (subsetSum design (Finset.univ.filter fun label => 0 < stressCoeff label) - 1).PosDef
      ↔ ∀ probe : Fin 3 → ℝ, probe ≠ 0 →
          (∑ negIdx, design.weight (negEnum negIdx) / -stressCoeff (negEnum negIdx)
              * ((Real.sqrt (-stressCoeff (negEnum negIdx))
                  • (whitener *ᵥ design.atom (negEnum negIdx))) ⬝ᵥ probe) ^ 2)
            < ∑ posIdx, (1 - design.weight (posEnum posIdx)) / stressCoeff (posEnum posIdx)
                * ((Real.sqrt (stressCoeff (posEnum posIdx))
                    • (whitener *ᵥ design.atom (posEnum posIdx))) ⬝ᵥ probe) ^ 2 := by
  classical
  have hcompl : (Finset.univ.filter fun label => 0 < stressCoeff label)ᶜ
      = Finset.univ.filter fun label => stressCoeff label < 0 := by
    ext label
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact ⟨fun hle => lt_of_le_of_ne hle (hfull label), fun hlt => hlt.le⟩
  have hrescale : ∀ (scale : ℝ) (hscalePos : 0 < scale) (vec probe : Fin 3 → ℝ)
      (mass : ℝ), mass / scale * ((Real.sqrt scale • vec) ⬝ᵥ probe) ^ 2
        = mass * (vec ⬝ᵥ probe) ^ 2 := by
    intro scale hscalePos vec probe mass
    rw [smul_dotProduct, smul_eq_mul, mul_pow, Real.sq_sqrt hscalePos.le]
    field_simp
  rw [posDef_gap_iff_forall_whitenedProbe design _ hdetNe, hcompl]
  refine forall_congr' fun probe => forall_congr' fun _ => ?_
  rw [sum_filter_eq_sum_enum (fun label => stressCoeff label < 0) negEnum hnegInjective
      hnegSign hnegOnto,
    sum_filter_eq_sum_enum (fun label => 0 < stressCoeff label) posEnum hposInjective
      hposSign hposOnto]
  rw [Finset.sum_congr rfl fun negIdx _ =>
      hrescale (-stressCoeff (negEnum negIdx)) (neg_pos.mpr (hnegSign negIdx))
        (whitener *ᵥ design.atom (negEnum negIdx)) probe (design.weight (negEnum negIdx)),
    Finset.sum_congr rfl fun posIdx _ =>
      hrescale (stressCoeff (posEnum posIdx)) (hposSign posIdx)
        (whitener *ᵥ design.atom (posEnum posIdx)) probe (1 - design.weight (posEnum posIdx))]

/-- **PROBES BECOME COORDINATES.**  Reading a probe in an orthonormal triple
turns a test over all nonzero probes into a test over all nonzero coefficient
vectors, and makes the triple's own quadratic form DIAGONAL. -/
theorem forall_probe_iff_forall_coeff_of_orthonormalFrame
    (posFrame negFrame : Fin 3 → Fin 3 → ℝ)
    (horthonormal : ∀ leftIdx rightIdx : Fin 3,
      posFrame leftIdx ⬝ᵥ posFrame rightIdx = if leftIdx = rightIdx then 1 else 0)
    (freeRatio boundRatio : Fin 3 → ℝ) :
    (∀ probe : Fin 3 → ℝ, probe ≠ 0 →
        (∑ negIdx, boundRatio negIdx * (negFrame negIdx ⬝ᵥ probe) ^ 2)
          < ∑ posIdx, freeRatio posIdx * (posFrame posIdx ⬝ᵥ probe) ^ 2)
      ↔ ∀ coeff : Fin 3 → ℝ, coeff ≠ 0 →
          (∑ negIdx, boundRatio negIdx
              * (∑ posIdx, coeff posIdx * (negFrame negIdx ⬝ᵥ posFrame posIdx)) ^ 2)
            < ∑ posIdx, freeRatio posIdx * coeff posIdx ^ 2 := by
  have hspread : ∀ (coeff : Fin 3 → ℝ) (negIdx : Fin 3),
      negFrame negIdx ⬝ᵥ (∑ posIdx, coeff posIdx • posFrame posIdx)
        = ∑ posIdx, coeff posIdx * (negFrame negIdx ⬝ᵥ posFrame posIdx) := by
    intro coeff negIdx
    rw [dotProduct_sum]
    exact Finset.sum_congr rfl fun posIdx _ => by
      rw [dotProduct_smul, smul_eq_mul]
  constructor
  · intro hprobeTest coeff hcoeffNe
    have hread := dotProduct_sum_smul_orthonormalFrame posFrame horthonormal coeff
    have hnonzero : (∑ posIdx, coeff posIdx • posFrame posIdx) ≠ 0 := by
      intro hzero
      refine hcoeffNe (funext fun posIdx => ?_)
      have hentry := hread posIdx
      rw [hzero, dotProduct_zero] at hentry
      exact hentry.symm
    have hstep := hprobeTest _ hnonzero
    simp only [hspread coeff, hread] at hstep
    exact hstep
  · intro hcoeffTest probe hprobeNe
    have hexpand := eq_sum_smul_of_orthonormalFrame posFrame horthonormal probe
    have hcoeffNe : (fun posIdx => posFrame posIdx ⬝ᵥ probe) ≠ 0 := by
      intro hzero
      refine hprobeNe ?_
      rw [hexpand]
      refine Finset.sum_eq_zero fun posIdx _ => ?_
      rw [show posFrame posIdx ⬝ᵥ probe = 0 from congrFun hzero posIdx, zero_smul]
    have hstep := hcoeffTest _ hcoeffNe
    have hrewrite : ∀ negIdx : Fin 3,
        (∑ posIdx, (posFrame posIdx ⬝ᵥ probe) * (negFrame negIdx ⬝ᵥ posFrame posIdx))
          = negFrame negIdx ⬝ᵥ probe := fun negIdx => by
      rw [← hspread (fun posIdx => posFrame posIdx ⬝ᵥ probe) negIdx, ← hexpand]
    simp only [hrewrite] at hstep
    exact hstep

/-- **THE DIAGONAL CRITERION OF THE BALANCED STRATUM.**  A `(6,3)` design with a
full-support stress has ONE whitener putting both stress sides into orthonormal
frames, and in the coordinates of the positive frame the positive triple's
domination test is a DIAGONAL form against the overlap form of the two frames:
nine unknowns become three, and one positive semidefinite matrix is tested
against a diagonal one.  Free mass enters only through the ratios
`(1 - t_c) / z_c`, bound mass only through `t_c / (-z_c)` — the mass-gap
quantities of `Gtz.posDef_gap_of_stressMassGap` at their sharpest, with the
maximum and minimum of that criterion replaced by the exact quadratic form. -/
theorem sixThree_posSide_dominates_iff_diagonalCriterion (design : WeightedDesign 6 3)
    {stressCoeff : Fin 6 → ℝ}
    (hstress : ∑ label, stressCoeff label • atomMatrix (design.atom label) = 0)
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (posEnum negEnum : Fin 3 → Fin 6)
    (hposInjective : Function.Injective posEnum)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hposOnto : ∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label)
    (hnegInjective : Function.Injective negEnum)
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hnegOnto : ∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label) :
    ∃ posFrame negFrame : Fin 3 → Fin 3 → ℝ,
      (∀ leftIdx rightIdx : Fin 3,
          posFrame leftIdx ⬝ᵥ posFrame rightIdx = if leftIdx = rightIdx then 1 else 0)
      ∧ (∀ leftIdx rightIdx : Fin 3,
          negFrame leftIdx ⬝ᵥ negFrame rightIdx = if leftIdx = rightIdx then 1 else 0)
      ∧ ((subsetSum design (Finset.univ.filter fun label => 0 < stressCoeff label)
            - 1).PosDef
          ↔ ∀ coeff : Fin 3 → ℝ, coeff ≠ 0 →
              (∑ negIdx, design.weight (negEnum negIdx) / -stressCoeff (negEnum negIdx)
                  * (∑ posIdx, coeff posIdx * (negFrame negIdx ⬝ᵥ posFrame posIdx)) ^ 2)
                < ∑ posIdx, (1 - design.weight (posEnum posIdx))
                    / stressCoeff (posEnum posIdx) * coeff posIdx ^ 2) := by
  obtain ⟨whitener, hdetNe, hposOrthonormal, hnegOrthonormal⟩ :=
    twoFrame_normalForm_bothFrames design hstress hfull posEnum negEnum hposInjective
      hposSign hposOnto hnegInjective hnegSign hnegOnto
  refine ⟨fun posIdx => Real.sqrt (stressCoeff (posEnum posIdx))
      • (whitener *ᵥ design.atom (posEnum posIdx)),
    fun negIdx => Real.sqrt (-stressCoeff (negEnum negIdx))
      • (whitener *ᵥ design.atom (negEnum negIdx)),
    hposOrthonormal, hnegOrthonormal, ?_⟩
  rw [sixThree_posSide_dominates_iff_frameCriterion design hfull posEnum negEnum
    hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hdetNe]
  exact forall_probe_iff_forall_coeff_of_orthonormalFrame _ _ hposOrthonormal _ _

/-! ## Part 4: the stratum realised — every whitened family IS a design

The dictionary read backwards.  The tree already builds the design
(`Gtz.whitenedFamilyDesign` over `Gtz.exists_congruence_to_one`); what is added
here is that BOTH questions asked of it — does a subset dominate, and does the
family carry a stress — are answered by the UNWHITENED data.  So a candidate
configuration may be written down in any coordinates, with any weighted Gram,
and its domination behaviour is decided by rational arithmetic on the raw atoms:
no square root, no whitener, ever appears in a verdict. -/

/-- Over the reals the conjugate transpose is the transpose. -/
theorem conjTranspose_eq_transpose_real {rows cols : ℕ}
    (mat : Matrix (Fin rows) (Fin cols) ℝ) : matᴴ = matᵀ := by
  ext rowIdx colIdx
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]

/-- **CONGRUENCE BY AN INVERTIBLE MATRIX PRESERVES AND REFLECTS DEFINITENESS.** -/
theorem posDef_congruence_iff {rank : ℕ} {gramMat congruence : Matrix (Fin rank) (Fin rank) ℝ}
    (hunit : IsUnit congruence.det) :
    (congruenceᵀ * gramMat * congruence).PosDef ↔ gramMat.PosDef := by
  have hmatrixUnit : IsUnit congruence := (Matrix.isUnit_iff_isUnit_det congruence).mpr hunit
  have hinjective : Function.Injective congruence.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hmatrixUnit
  constructor
  · intro hconjugated
    have hinverseUnit : IsUnit congruence⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hmatrixUnit
    have hrightInv : congruence * congruence⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
    have hleftTranspose : (congruence⁻¹)ᵀ * congruenceᵀ = 1 := by
      rw [← Matrix.transpose_mul, hrightInv, Matrix.transpose_one]
    have hstep := hconjugated.conjTranspose_mul_mul_same (B := congruence⁻¹)
      (Matrix.mulVec_injective_iff_isUnit.mpr hinverseUnit)
    rw [conjTranspose_eq_transpose_real] at hstep
    have hcollapse : (congruence⁻¹)ᵀ * (congruenceᵀ * gramMat * congruence) * congruence⁻¹
        = gramMat := by
      calc (congruence⁻¹)ᵀ * (congruenceᵀ * gramMat * congruence) * congruence⁻¹
          = ((congruence⁻¹)ᵀ * congruenceᵀ) * gramMat * (congruence * congruence⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = gramMat := by rw [hleftTranspose, hrightInv, Matrix.one_mul, Matrix.mul_one]
    rwa [hcollapse] at hstep
  · intro hposDef
    have hstep := hposDef.conjTranspose_mul_mul_same (B := congruence) hinjective
    rwa [conjTranspose_eq_transpose_real] at hstep

/-- The whitened design's subset sums are the raw ones, conjugated. -/
theorem subsetSum_whitenedFamilyDesign_eq_conjugate {size rank : ℕ}
    (baseAtom : Fin size → Fin rank → ℝ) (baseWeight : Fin size → ℝ)
    (hweightPos : ∀ label, 0 < baseWeight label) (hweightSumOne : ∑ label, baseWeight label = 1)
    (whitener : Matrix (Fin rank) (Fin rank) ℝ)
    (hwhiten : whitenerᵀ * (∑ label, baseWeight label • atomMatrix (baseAtom label))
      * whitener = 1) (selected : Finset (Fin size)) :
    subsetSum (whitenedFamilyDesign baseAtom baseWeight hweightPos hweightSumOne whitener
        hwhiten) selected
      = whitenerᵀ * (∑ label ∈ selected, atomMatrix (baseAtom label)) * whitener := by
  rw [whitenedDesign_subsetSum_eq, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun label _ => (transpose_mul_atomMatrix_mul whitener _).symm

/-- **DOMINATION IS DECIDED BY THE UNWHITENED DATA.**  A subset of the whitened
design dominates STRICTLY exactly when its raw atom sum beats the raw weighted
Gram in the Loewner order.  No whitener appears on the right, so the test is
rational whenever the base family is. -/
theorem posDef_gap_whitenedFamilyDesign_iff {size rank : ℕ}
    (baseAtom : Fin size → Fin rank → ℝ) (baseWeight : Fin size → ℝ)
    (hweightPos : ∀ label, 0 < baseWeight label) (hweightSumOne : ∑ label, baseWeight label = 1)
    {whitener : Matrix (Fin rank) (Fin rank) ℝ}
    (hwhiten : whitenerᵀ * (∑ label, baseWeight label • atomMatrix (baseAtom label))
      * whitener = 1) (hunit : IsUnit whitener.det) (selected : Finset (Fin size)) :
    (subsetSum (whitenedFamilyDesign baseAtom baseWeight hweightPos hweightSumOne whitener
        hwhiten) selected - 1).PosDef
      ↔ ((∑ label ∈ selected, atomMatrix (baseAtom label))
          - ∑ label, baseWeight label • atomMatrix (baseAtom label)).PosDef := by
  have hidentity : whitenerᵀ * ((∑ label ∈ selected, atomMatrix (baseAtom label))
        - ∑ label, baseWeight label • atomMatrix (baseAtom label)) * whitener
      = whitenerᵀ * (∑ label ∈ selected, atomMatrix (baseAtom label)) * whitener - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hwhiten]
  rw [subsetSum_whitenedFamilyDesign_eq_conjugate, ← hidentity]
  exact posDef_congruence_iff hunit

/-- **A DEPENDENCE OF THE BASE FAMILY IS A STRESS OF THE WHITENED DESIGN.** -/
theorem stress_whitenedFamilyDesign {size rank : ℕ}
    (baseAtom : Fin size → Fin rank → ℝ) (baseWeight : Fin size → ℝ)
    (hweightPos : ∀ label, 0 < baseWeight label) (hweightSumOne : ∑ label, baseWeight label = 1)
    (whitener : Matrix (Fin rank) (Fin rank) ℝ)
    (hwhiten : whitenerᵀ * (∑ label, baseWeight label • atomMatrix (baseAtom label))
      * whitener = 1) {stressCoeff : Fin size → ℝ}
    (hbaseStress : ∑ label, stressCoeff label • atomMatrix (baseAtom label) = 0) :
    ∑ label, stressCoeff label
      • atomMatrix ((whitenedFamilyDesign baseAtom baseWeight hweightPos hweightSumOne
          whitener hwhiten).atom label) = 0 := by
  have hconjugate : ∑ label, stressCoeff label • atomMatrix (whitenerᵀ *ᵥ baseAtom label)
      = whitenerᵀ * (∑ label, stressCoeff label • atomMatrix (baseAtom label)) * whitener := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.mul_smul, Matrix.smul_mul, transpose_mul_atomMatrix_mul]
  show ∑ label, stressCoeff label • atomMatrix (whitenerᵀ *ᵥ baseAtom label) = 0
  rw [hconjugate, hbaseStress, Matrix.mul_zero, Matrix.zero_mul]

/-- **THE BALANCED STRATUM IS REALISED BY ANY WHITENABLE FAMILY.**  Given base
atoms, positive weights summing to one whose weighted Gram is positive definite,
and a linear dependence of the base atoms with all coefficients nonzero, there
is a genuine weighted design carrying that dependence as a FULL-SUPPORT stress,
and its domination behaviour at every subset is the raw Loewner comparison.
This is the converse of `twoFrame_normalForm_bothFrames`: together they make the
balanced stratum a two-way dictionary between designs and raw families. -/
theorem exists_design_of_baseFamily {size rank : ℕ}
    (baseAtom : Fin size → Fin rank → ℝ) (baseWeight : Fin size → ℝ)
    (hweightPos : ∀ label, 0 < baseWeight label) (hweightSumOne : ∑ label, baseWeight label = 1)
    (hgramPosDef : (∑ label, baseWeight label • atomMatrix (baseAtom label)).PosDef)
    {stressCoeff : Fin size → ℝ}
    (hbaseStress : ∑ label, stressCoeff label • atomMatrix (baseAtom label) = 0) :
    ∃ design : WeightedDesign size rank,
      design.weight = baseWeight
      ∧ (∑ label, stressCoeff label • atomMatrix (design.atom label)) = 0
      ∧ ∀ selected : Finset (Fin size),
          ((subsetSum design selected - 1).PosDef
            ↔ ((∑ label ∈ selected, atomMatrix (baseAtom label))
                - ∑ label, baseWeight label • atomMatrix (baseAtom label)).PosDef) := by
  obtain ⟨whitener, hunit, hwhiten⟩ := exists_congruence_to_one hgramPosDef
  exact ⟨whitenedFamilyDesign baseAtom baseWeight hweightPos hweightSumOne whitener hwhiten,
    rfl,
    stress_whitenedFamilyDesign baseAtom baseWeight hweightPos hweightSumOne whitener hwhiten
      hbaseStress,
    fun selected => posDef_gap_whitenedFamilyDesign_iff baseAtom baseWeight hweightPos
      hweightSumOne hwhiten hunit selected⟩

/-! ## Part 5: the two frames cannot align where the weights are heavy

The only new inequality here, and the only one tight at the corner where this
stratum's domination margin degenerates.  It says nothing about the atoms — only
about the weights and the OVERLAPS of the two whitened frames. -/

/-- Each frame's squared overlaps against the other frame sum to one. -/
theorem sum_overlap_sq_eq_one (posFrame negFrame : Fin 3 → Fin 3 → ℝ)
    (hposUnit : ∀ posIdx, posFrame posIdx ⬝ᵥ posFrame posIdx = 1)
    (hnegOrthonormal : ∀ leftIdx rightIdx : Fin 3,
      negFrame leftIdx ⬝ᵥ negFrame rightIdx = if leftIdx = rightIdx then 1 else 0)
    (posIdx : Fin 3) : ∑ negIdx, (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2 = 1 := by
  have hresolve := sum_rankOne_eq_one_of_orthonormalFrame negFrame hnegOrthonormal
  have hform : posFrame posIdx
        ⬝ᵥ ((∑ negIdx, Matrix.vecMulVec (negFrame negIdx) (negFrame negIdx))
          *ᵥ posFrame posIdx)
      = ∑ negIdx, (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun negIdx _ => by
      rw [vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
        dotProduct_comm (posFrame posIdx) (negFrame negIdx)]
      ring
  rw [← hform, hresolve, Matrix.one_mulVec, hposUnit posIdx]

/-- **THE FRAME-OVERLAP BOUND.**  Write `tau c = sqrt (t_c / (1 - t_c))`.  For any
partition of a design's labels into a positive side and a negative side of three
labels each, and any two orthonormal frames indexed by the two sides,

    sum_a sum_b  tau (P a) * tau (N b) * (u_a . v_b) ^ 2  <  1 .

Nothing about atoms enters: the two frames are arbitrary orthonormal bases and
the weights are arbitrary.  The mechanism is that a label's co-weight `1 - t_c`
strictly exceeds the OTHER side's total mass, because the two remaining labels
of its own side carry positive weight — the one place where six labels rather
than four is used.  The bound is TIGHT in the limit where one positive atom and
one negative atom align and their two weights exhaust the design, which is
exactly the corner at which this stratum's domination margin degenerates to
zero. -/
theorem frameOverlap_weightedSum_lt_one {size : ℕ} (weight : Fin size → ℝ)
    (hweightPos : ∀ label, 0 < weight label)
    (posEnum negEnum : Fin 3 → Fin size)
    (hposMass : ∑ posIdx, weight (posEnum posIdx)
      + ∑ negIdx, weight (negEnum negIdx) = 1)
    (posFrame negFrame : Fin 3 → Fin 3 → ℝ)
    (hposOrthonormal : ∀ leftIdx rightIdx : Fin 3,
      posFrame leftIdx ⬝ᵥ posFrame rightIdx = if leftIdx = rightIdx then 1 else 0)
    (hnegOrthonormal : ∀ leftIdx rightIdx : Fin 3,
      negFrame leftIdx ⬝ᵥ negFrame rightIdx = if leftIdx = rightIdx then 1 else 0) :
    ∑ posIdx, ∑ negIdx,
        Real.sqrt (weight (posEnum posIdx) / (1 - weight (posEnum posIdx)))
          * Real.sqrt (weight (negEnum negIdx) / (1 - weight (negEnum negIdx)))
          * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2 < 1 := by
  classical
  set posMass := ∑ posIdx, weight (posEnum posIdx) with hposMassDef
  set negMass := ∑ negIdx, weight (negEnum negIdx) with hnegMassDef
  have hposMassPos : 0 < posMass := by
    rw [hposMassDef, Fin.sum_univ_three]
    have := hweightPos (posEnum 0); have := hweightPos (posEnum 1); have := hweightPos (posEnum 2)
    linarith
  have hnegMassPos : 0 < negMass := by
    rw [hnegMassDef, Fin.sum_univ_three]
    have := hweightPos (negEnum 0); have := hweightPos (negEnum 1); have := hweightPos (negEnum 2)
    linarith
  -- a label's co-weight strictly exceeds the other side's total mass
  have hdropPositive : ∀ (enum : Fin 3 → Fin size) (dropIdx : Fin 3),
      0 < (∑ idx, weight (enum idx)) - weight (enum dropIdx) := by
    intro enum dropIdx
    have herase : ∑ idx ∈ Finset.univ.erase dropIdx, weight (enum idx)
        = (∑ idx, weight (enum idx)) - weight (enum dropIdx) := by
      rw [← Finset.sum_erase_add Finset.univ (fun idx => weight (enum idx))
        (Finset.mem_univ dropIdx)]
      ring
    have hnonempty : (Finset.univ.erase dropIdx).Nonempty := by
      refine Finset.card_pos.mp ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ dropIdx), Finset.card_univ,
        Fintype.card_fin]
      norm_num
    rw [← herase]
    exact Finset.sum_pos (fun idx _ => hweightPos (enum idx)) hnonempty
  have hcoweightPos : ∀ posIdx, negMass < 1 - weight (posEnum posIdx) := by
    intro posIdx
    have hsplit := hdropPositive posEnum posIdx
    rw [← hposMassDef] at hsplit
    linarith [hposMass]
  have hcoweightNeg : ∀ negIdx, posMass < 1 - weight (negEnum negIdx) := by
    intro negIdx
    have hsplit := hdropPositive negEnum negIdx
    rw [← hnegMassDef] at hsplit
    linarith [hposMass]
  set tauPos : Fin 3 → ℝ := fun posIdx =>
    Real.sqrt (weight (posEnum posIdx) / (1 - weight (posEnum posIdx))) with htauPosDef
  set tauNeg : Fin 3 → ℝ := fun negIdx =>
    Real.sqrt (weight (negEnum negIdx) / (1 - weight (negEnum negIdx))) with htauNegDef
  have htauPosSq : ∀ posIdx, tauPos posIdx ^ 2
      = weight (posEnum posIdx) / (1 - weight (posEnum posIdx)) := by
    intro posIdx
    exact Real.sq_sqrt (div_nonneg (hweightPos _).le
      (by linarith [hcoweightPos posIdx, hnegMassPos]))
  have htauNegSq : ∀ negIdx, tauNeg negIdx ^ 2
      = weight (negEnum negIdx) / (1 - weight (negEnum negIdx)) := by
    intro negIdx
    exact Real.sq_sqrt (div_nonneg (hweightPos _).le
      (by linarith [hcoweightNeg negIdx, hposMassPos]))
  have htauPosNonneg : ∀ posIdx, 0 ≤ tauPos posIdx := fun _ => Real.sqrt_nonneg _
  have htauNegNonneg : ∀ negIdx, 0 ≤ tauNeg negIdx := fun _ => Real.sqrt_nonneg _
  -- the two square-sum ceilings
  have hposCeiling : ∑ posIdx, tauPos posIdx ^ 2 < posMass / negMass := by
    have hterm : ∀ posIdx, tauPos posIdx ^ 2 < weight (posEnum posIdx) / negMass := by
      intro posIdx
      rw [htauPosSq posIdx]
      exact div_lt_div_of_pos_left (hweightPos _) hnegMassPos (hcoweightPos posIdx)
    calc ∑ posIdx, tauPos posIdx ^ 2
        < ∑ posIdx, weight (posEnum posIdx) / negMass :=
          Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun posIdx _ => hterm posIdx
      _ = posMass / negMass := by rw [← Finset.sum_div]
  have hnegCeiling : ∑ negIdx, tauNeg negIdx ^ 2 < negMass / posMass := by
    have hterm : ∀ negIdx, tauNeg negIdx ^ 2 < weight (negEnum negIdx) / posMass := by
      intro negIdx
      rw [htauNegSq negIdx]
      exact div_lt_div_of_pos_left (hweightPos _) hposMassPos (hcoweightNeg negIdx)
    calc ∑ negIdx, tauNeg negIdx ^ 2
        < ∑ negIdx, weight (negEnum negIdx) / posMass :=
          Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun negIdx _ => hterm negIdx
      _ = negMass / posMass := by rw [← Finset.sum_div]
  -- the arithmetic-geometric step at the balancing level
  set level := negMass / posMass with hlevelDef
  have hlevelPos : 0 < level := div_pos hnegMassPos hposMassPos
  have hlevelMul : level * (posMass / negMass) = 1 := by
    rw [hlevelDef]
    field_simp
  have hlevelSelf : level / level = 1 := div_self (ne_of_gt hlevelPos)
  have hstep : ∀ posIdx negIdx,
      tauPos posIdx * tauNeg negIdx * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2
        ≤ (level * tauPos posIdx ^ 2 + tauNeg negIdx ^ 2 / level) / 2
            * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2 := by
    intro posIdx negIdx
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hsquare : 0 ≤ (level * tauPos posIdx - tauNeg negIdx) ^ 2 / level :=
      div_nonneg (sq_nonneg _) hlevelPos.le
    have hexpand : (level * tauPos posIdx - tauNeg negIdx) ^ 2 / level
        = level * tauPos posIdx ^ 2 - 2 * (tauPos posIdx * tauNeg negIdx)
          + tauNeg negIdx ^ 2 / level := by
      field_simp
      ring
    rw [hexpand] at hsquare
    linarith
  have hbound : ∑ posIdx, ∑ negIdx,
        tauPos posIdx * tauNeg negIdx * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2
      ≤ ∑ posIdx, ∑ negIdx, (level * tauPos posIdx ^ 2 + tauNeg negIdx ^ 2 / level) / 2
          * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2 :=
    Finset.sum_le_sum fun posIdx _ =>
      Finset.sum_le_sum fun negIdx _ => hstep posIdx negIdx
  -- the majorant evaluates by Parseval on each frame
  have hrowSum : ∀ posIdx, ∑ negIdx, (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2 = 1 :=
    sum_overlap_sq_eq_one posFrame negFrame
      (fun posIdx => by simpa using hposOrthonormal posIdx posIdx) hnegOrthonormal
  have hcolSum : ∀ negIdx, ∑ posIdx, (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2 = 1 := by
    intro negIdx
    have hstepCol := sum_overlap_sq_eq_one negFrame posFrame
      (fun idx => by simpa using hnegOrthonormal idx idx) hposOrthonormal negIdx
    rw [← hstepCol]
    exact Finset.sum_congr rfl fun posIdx _ => by
      rw [dotProduct_comm (posFrame posIdx) (negFrame negIdx)]
  have hrowSplit : ∀ posIdx, ∑ negIdx,
        (level * tauPos posIdx ^ 2 + tauNeg negIdx ^ 2 / level) / 2
          * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2
      = level * tauPos posIdx ^ 2 / 2
        + ∑ negIdx, tauNeg negIdx ^ 2 / level / 2
            * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2 := by
    intro posIdx
    calc ∑ negIdx, (level * tauPos posIdx ^ 2 + tauNeg negIdx ^ 2 / level) / 2
            * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2
        = ∑ negIdx, (level * tauPos posIdx ^ 2 / 2
              * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2
            + tauNeg negIdx ^ 2 / level / 2
              * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2) :=
          Finset.sum_congr rfl fun negIdx _ => by ring
      _ = level * tauPos posIdx ^ 2 / 2
            * (∑ negIdx, (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2)
          + ∑ negIdx, tauNeg negIdx ^ 2 / level / 2
              * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = level * tauPos posIdx ^ 2 / 2
          + ∑ negIdx, tauNeg negIdx ^ 2 / level / 2
              * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2 := by
          rw [hrowSum posIdx, mul_one]
  have hcolCollapse : ∀ negIdx, ∑ posIdx, tauNeg negIdx ^ 2 / level / 2
      * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2 = tauNeg negIdx ^ 2 / level / 2 := by
    intro negIdx
    rw [← Finset.mul_sum, hcolSum negIdx, mul_one]
  have hmajorant : ∑ posIdx, ∑ negIdx,
        (level * tauPos posIdx ^ 2 + tauNeg negIdx ^ 2 / level) / 2
          * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2
      = level * (∑ posIdx, tauPos posIdx ^ 2) / 2
        + (∑ negIdx, tauNeg negIdx ^ 2) / level / 2 := by
    rw [Finset.sum_congr rfl fun posIdx _ => hrowSplit posIdx, Finset.sum_add_distrib,
      Finset.sum_comm, Finset.sum_congr rfl fun negIdx _ => hcolCollapse negIdx,
      ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum]
  have hposScaled : level * (∑ posIdx, tauPos posIdx ^ 2) < level * (posMass / negMass) :=
    mul_lt_mul_of_pos_left hposCeiling hlevelPos
  have hnegScaled : (∑ negIdx, tauNeg negIdx ^ 2) / level < level / level := by
    have hstepInv := mul_lt_mul_of_pos_right hnegCeiling (inv_pos.mpr hlevelPos)
    simpa [div_eq_mul_inv] using hstepInv
  calc ∑ posIdx, ∑ negIdx,
        tauPos posIdx * tauNeg negIdx * (posFrame posIdx ⬝ᵥ negFrame negIdx) ^ 2
      ≤ _ := hbound
    _ = level * (∑ posIdx, tauPos posIdx ^ 2) / 2
        + (∑ negIdx, tauNeg negIdx ^ 2) / level / 2 := hmajorant
    _ < level * (posMass / negMass) / 2 + level / level / 2 := by linarith
    _ = 1 := by rw [hlevelMul, hlevelSelf]; norm_num


/-! ## Part 6: the pairwise dichotomy — the corner kill, at every pair

The float descent puts the infimum of this stratum's domination margin at a
corner where one positive atom and one negative atom become parallel with equal
length and their two weights exhaust the design.  That corner cannot happen: the
two mass comparisons at a single pair cannot BOTH fail, because multiplying them
would force the pair's two weights to sum to one, and four other weights are
positive.  Stated at every pair it is a nine-cell colouring of the stratum. -/

/-- Two distinct labels never carry all the weight: a third label is positive. -/
theorem weightPair_lt_one (design : WeightedDesign size rank)
    {firstLabel secondLabel thirdLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel)
    (hthirdFirst : thirdLabel ≠ firstLabel) (hthirdSecond : thirdLabel ≠ secondLabel) :
    design.weight firstLabel + design.weight secondLabel < 1 := by
  classical
  have hpart : ∑ label ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
      design.weight label ≤ 1 := by
    rw [← design.weight_sum_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun label _ _ => (design.weight_pos label).le
  have htriple : ∑ label ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
      design.weight label
      = design.weight firstLabel + design.weight secondLabel + design.weight thirdLabel := by
    rw [Finset.sum_insert (by simp [hdistinct, Ne.symm hthirdFirst]),
      Finset.sum_insert (by simp [Ne.symm hthirdSecond]), Finset.sum_singleton, add_assoc]
  rw [htriple] at hpart
  linarith [design.weight_pos thirdLabel]

/-- **THE PAIRWISE DICHOTOMY.**  For any two distinct labels and any two positive
scales, the first label's FREE mass beats the second's BOUND mass, or the other
way round.  Both cannot fail: multiplying the two failures cancels the scales and
leaves `1 <= t_first + t_second`, which a third positive weight forbids.

Read on the balanced stratum with the scales `A_i` and `B_j` of the two stress
sides, this colours each of the nine positive-negative pairs, and the all-one-
colour corners are exactly the two orientations of the stress mass gap.  It is
the exact statement that kills the degenerate corner of this stratum. -/
theorem freeMass_beats_or_coFreeMass_beats (design : WeightedDesign size rank)
    {firstLabel secondLabel thirdLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel)
    (hthirdFirst : thirdLabel ≠ firstLabel) (hthirdSecond : thirdLabel ≠ secondLabel)
    {firstScale secondScale : ℝ} (hfirstPos : 0 < firstScale) (hsecondPos : 0 < secondScale) :
    design.weight secondLabel * secondScale
        < (1 - design.weight firstLabel) * firstScale
      ∨ design.weight firstLabel * firstScale
        < (1 - design.weight secondLabel) * secondScale := by
  by_contra hneither
  push Not at hneither
  obtain ⟨hfirstFails, hsecondFails⟩ := hneither
  have hweightSum := weightPair_lt_one design hdistinct hthirdFirst hthirdSecond
  have hfirstLtOne : design.weight firstLabel < 1 := by
    linarith [design.weight_pos secondLabel]
  have hsecondLtOne : design.weight secondLabel < 1 := by
    linarith [design.weight_pos firstLabel]
  have hproduct : (1 - design.weight firstLabel) * firstScale
        * ((1 - design.weight secondLabel) * secondScale)
      ≤ design.weight secondLabel * secondScale * (design.weight firstLabel * firstScale) :=
    mul_le_mul hfirstFails hsecondFails
      (mul_nonneg (by linarith) hsecondPos.le)
      (mul_nonneg (design.weight_pos secondLabel).le hsecondPos.le)
  have hscalePos : 0 < firstScale * secondScale := mul_pos hfirstPos hsecondPos
  nlinarith [hproduct, hscalePos, design.weight_pos firstLabel,
    design.weight_pos secondLabel]

/-! ## Part 7: the residual, in the thirteen coordinates of the stratum

Branch (ii) is now a finite-dimensional semialgebraic question and nothing else.
`BalancedFrameDominationSixThree` states it with no design, no whitener and no
square root: two families of three vectors whose stress-scaled rank-ones EACH
resolve the identity — which by `Gtz.orthonormal_of_three_rank_ones_sum_one` is
exactly "two orthonormal frames rescaled" — plus six positive weights.  The
equivalence proved here makes it match the branch's domination statement
exactly, so it is the residual itself and not a relaxation of it. -/

/-- Conjugating an atom family conjugates its coefficient-weighted sums. -/
theorem sum_smul_atomMatrix_mulVec_eq_conjugate {size rank : ℕ}
    (whitener : Matrix (Fin rank) (Fin rank) ℝ) (atomFamily : Fin size → Fin rank → ℝ)
    (coeff : Fin size → ℝ) (selected : Finset (Fin size)) :
    ∑ label ∈ selected, coeff label • atomMatrix (whitener *ᵥ atomFamily label)
      = whitener * (∑ label ∈ selected, coeff label • atomMatrix (atomFamily label))
        * whitenerᵀ := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun label _ => by
    rw [atomMatrix_conj, Matrix.mul_smul, Matrix.smul_mul]

/-- **THE SIGN SIDES OF A FULL-SUPPORT `(6,3)` STRESS ARE ENUMERABLE.**  The split
law makes each side a three-element set, so each is the image of an injective
`Fin 3`-indexed enumeration.  Supplies the enumerations that the frame criteria
of Parts 2 and 3 ask their callers for. -/
theorem exists_signEnumerations_sixThree (design : WeightedDesign 6 3)
    {stressCoeff : Fin 6 → ℝ}
    (hstress : ∑ label, stressCoeff label • atomMatrix (design.atom label) = 0)
    (hfull : ∀ label, stressCoeff label ≠ 0) :
    ∃ posEnum negEnum : Fin 3 → Fin 6,
      Function.Injective posEnum
      ∧ (∀ posIdx, 0 < stressCoeff (posEnum posIdx))
      ∧ (∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label)
      ∧ Function.Injective negEnum
      ∧ (∀ negIdx, stressCoeff (negEnum negIdx) < 0)
      ∧ (∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label) := by
  classical
  have hspan : ∀ probe : Fin 3 → ℝ, (∀ label, design.atom label ⬝ᵥ probe = 0) → probe = 0 :=
    fun probe hprobe => weightedDesign_atoms_span design hprobe
  obtain ⟨hposCard, hnegCard⟩ :=
    sixThree_fullSupport_stress_splits_three_three design.atom hspan hstress hfull
  set posSide := Finset.univ.filter (fun label => 0 < stressCoeff label) with hposSideDef
  set negSide := Finset.univ.filter (fun label => stressCoeff label < 0) with hnegSideDef
  refine ⟨fun posIdx => ((posSide.orderIsoOfFin hposCard) posIdx : Fin 6),
    fun negIdx => ((negSide.orderIsoOfFin hnegCard) negIdx : Fin 6), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun leftIdx rightIdx hEq =>
      (posSide.orderIsoOfFin hposCard).injective (Subtype.ext hEq)
  · exact fun posIdx => (Finset.mem_filter.mp ((posSide.orderIsoOfFin hposCard) posIdx).2).2
  · intro label hlabel
    obtain ⟨posIdx, hposIdx⟩ := (posSide.orderIsoOfFin hposCard).surjective
      ⟨label, Finset.mem_filter.mpr ⟨Finset.mem_univ label, hlabel⟩⟩
    exact ⟨posIdx, congrArg Subtype.val hposIdx⟩
  · exact fun leftIdx rightIdx hEq =>
      (negSide.orderIsoOfFin hnegCard).injective (Subtype.ext hEq)
  · exact fun negIdx => (Finset.mem_filter.mp ((negSide.orderIsoOfFin hnegCard) negIdx).2).2
  · intro label hlabel
    obtain ⟨negIdx, hnegIdx⟩ := (negSide.orderIsoOfFin hnegCard).surjective
      ⟨label, Finset.mem_filter.mpr ⟨Finset.mem_univ label, hlabel⟩⟩
    exact ⟨negIdx, congrArg Subtype.val hnegIdx⟩

/-- The branch-(ii) domination statement: every `(6,3)` design carrying a
FULL-SUPPORT stress has a strictly dominating triple.  This is what closes the
balanced branch — it implies the capstone outright, since a tie has no strictly
dominating triple. -/
def BalancedStratumHasStrictDominator : Prop :=
  ∀ (design : WeightedDesign 6 3) (stressCoeff : Fin 6 → ℝ),
    (∑ label, stressCoeff label • atomMatrix (design.atom label)) = 0 →
    (∀ label, stressCoeff label ≠ 0) →
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef

/-- **THE SAME STATEMENT IN THE THIRTEEN COORDINATES OF THE STRATUM.**  Six raw
vectors whose two stress sides EACH resolve the identity, and six positive
weights summing to one; the claim is that some triple's raw atom sum beats the
raw weighted Gram in the Loewner order.  No design, no whitener, no square root
occurs, so every clause is rational in the data. -/
def BalancedFrameDominationSixThree : Prop :=
  ∀ (baseAtom : Fin 6 → Fin 3 → ℝ) (weight stressCoeff : Fin 6 → ℝ)
    (posEnum negEnum : Fin 3 → Fin 6),
    (∀ label, 0 < weight label) → (∑ label, weight label = 1) →
    (∀ label, stressCoeff label ≠ 0) →
    Function.Injective posEnum →
    (∀ posIdx, 0 < stressCoeff (posEnum posIdx)) →
    (∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label) →
    Function.Injective negEnum →
    (∀ negIdx, stressCoeff (negEnum negIdx) < 0) →
    (∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label) →
    (∑ posIdx, stressCoeff (posEnum posIdx)
      • atomMatrix (baseAtom (posEnum posIdx)) = 1) →
    (∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1) →
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ ((∑ label ∈ selected, atomMatrix (baseAtom label))
          - ∑ label, weight label • atomMatrix (baseAtom label)).PosDef

/-- **THE RESIDUAL IS EXACTLY THE THIRTEEN-COORDINATE STATEMENT.**  Not a
relaxation and not a strengthening: whitening carries a branch-(ii) design to a
raw family whose two sides resolve the identity, and `Gtz.exists_design_of_baseFamily`
carries any such family back to a design, with the domination verdict preserved
in both directions by congruence.  So the balanced branch of the `(6,3)` stress
trichotomy is a semialgebraic question in thirteen real coordinates and nothing
more. -/
theorem balancedFrameDomination_iff_balancedStratumHasStrictDominator :
    BalancedFrameDominationSixThree ↔ BalancedStratumHasStrictDominator := by
  classical
  constructor
  · intro hframe design stressCoeff hstress hfull
    obtain ⟨posEnum, negEnum, hposInjective, hposSign, hposOnto,
      hnegInjective, hnegSign, hnegOnto⟩ :=
      exists_signEnumerations_sixThree design hstress hfull
    obtain ⟨whitener, hdetNe, hsandwichPos⟩ :=
      exists_whitening_of_positiveSide design hstress hfull
    have hmiddle := posSide_sum_eq_negSide_sum design.atom hstress hfull
    have hposSide : ∑ posIdx, stressCoeff (posEnum posIdx)
        • atomMatrix (whitener *ᵥ design.atom (posEnum posIdx)) = 1 := by
      have hreindex := sum_filter_eq_sum_enum (fun label => 0 < stressCoeff label) posEnum
        hposInjective hposSign hposOnto
        (fun label => stressCoeff label • atomMatrix (whitener *ᵥ design.atom label))
      rw [← hreindex, sum_smul_atomMatrix_mulVec_eq_conjugate]
      exact hsandwichPos
    have hnegSide : ∑ negIdx, (-stressCoeff (negEnum negIdx))
        • atomMatrix (whitener *ᵥ design.atom (negEnum negIdx)) = 1 := by
      have hreindex := sum_filter_eq_sum_enum (fun label => stressCoeff label < 0) negEnum
        hnegInjective hnegSign hnegOnto
        (fun label => (-stressCoeff label) • atomMatrix (whitener *ᵥ design.atom label))
      rw [← hreindex, sum_smul_atomMatrix_mulVec_eq_conjugate, ← hmiddle]
      exact hsandwichPos
    obtain ⟨selected, hcard, hposDef⟩ := hframe (fun label => whitener *ᵥ design.atom label)
      design.weight stressCoeff posEnum negEnum design.weight_pos design.weight_sum_one hfull
      hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hposSide hnegSide
    refine ⟨selected, hcard, ?_⟩
    have hunit : IsUnit (whitenerᵀ).det := by
      rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hdetNe
    have hselectedSum : ∑ label ∈ selected, atomMatrix (whitener *ᵥ design.atom label)
        = whitener * (subsetSum design selected) * whitenerᵀ := by
      have hstep := sum_smul_atomMatrix_mulVec_eq_conjugate whitener design.atom
        (fun _ => (1 : ℝ)) selected
      simpa only [one_smul, subsetSum] using hstep
    have hgramSum : ∑ label, design.weight label
        • atomMatrix (whitener *ᵥ design.atom label) = whitener * whitenerᵀ := by
      rw [sum_smul_atomMatrix_mulVec_eq_conjugate, design.isParseval, Matrix.mul_one]
    rw [hselectedSum, hgramSum] at hposDef
    have hconjugate : whitener * (subsetSum design selected) * whitenerᵀ - whitener * whitenerᵀ
        = (whitenerᵀ)ᵀ * (subsetSum design selected - 1) * whitenerᵀ := by
      rw [Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [hconjugate] at hposDef
    exact (posDef_congruence_iff hunit).mp hposDef
  · intro hdesignSide baseAtom weight stressCoeff posEnum negEnum hweightPos hweightSumOne
      hfull hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto
      hposSide hnegSide
    -- the two side identities make the coefficient family a stress of the base atoms
    have hbaseStress : ∑ label, stressCoeff label • atomMatrix (baseAtom label) = 0 := by
      have hdisjoint : Disjoint (Finset.univ.filter fun label => 0 < stressCoeff label)
          (Finset.univ.filter fun label => stressCoeff label < 0) := by
        rw [Finset.disjoint_left]
        intro label hposMem hnegMem
        exact absurd (Finset.mem_filter.mp hnegMem).2
          (asymm (Finset.mem_filter.mp hposMem).2)
      have hcover : (Finset.univ.filter fun label => 0 < stressCoeff label)
          ∪ (Finset.univ.filter fun label => stressCoeff label < 0) = Finset.univ := by
        refine Finset.eq_univ_of_forall fun label => ?_
        rcases lt_or_lt_iff_ne.mpr (hfull label) with hlt | hgt
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ label, hlt⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ label, hgt⟩)
      have hposPart : ∑ label ∈ Finset.univ.filter (fun label => 0 < stressCoeff label),
          stressCoeff label • atomMatrix (baseAtom label) = 1 := by
        have hreindex := sum_filter_eq_sum_enum (fun label => 0 < stressCoeff label) posEnum
          hposInjective hposSign hposOnto
          (fun label => stressCoeff label • atomMatrix (baseAtom label))
        rw [hreindex]
        exact hposSide
      have hnegPart : ∑ label ∈ Finset.univ.filter (fun label => stressCoeff label < 0),
          stressCoeff label • atomMatrix (baseAtom label) = -1 := by
        have hreindex := sum_filter_eq_sum_enum (fun label => stressCoeff label < 0) negEnum
          hnegInjective hnegSign hnegOnto
          (fun label => stressCoeff label • atomMatrix (baseAtom label))
        have hflip : ∑ negIdx, stressCoeff (negEnum negIdx)
              • atomMatrix (baseAtom (negEnum negIdx))
            = -∑ negIdx, (-stressCoeff (negEnum negIdx))
              • atomMatrix (baseAtom (negEnum negIdx)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun negIdx _ => by rw [neg_smul, neg_neg]
        rw [hreindex, hflip, hnegSide]
      rw [← hcover, Finset.sum_union hdisjoint, hposPart, hnegPart]
      simp
    -- the base family's weighted Gram is positive definite
    have hgramPosDef : (∑ label, weight label • atomMatrix (baseAtom label)).PosDef := by
      have hsymm : (∑ label, weight label • atomMatrix (baseAtom label))ᵀ
          = ∑ label, weight label • atomMatrix (baseAtom label) := by
        rw [Matrix.transpose_sum]
        exact Finset.sum_congr rfl fun label _ => by
          rw [Matrix.transpose_smul,
            transpose_eq_of_isHermitian (posSemidef_atomMatrix (baseAtom label)).1]
      refine Matrix.posDef_iff_dotProduct_mulVec.mpr
        ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobeNe => ?_⟩
      rw [star_trivial, atomForm_eq_on_subset]
      have hresolve : ∑ posIdx, stressCoeff (posEnum posIdx)
          * (baseAtom (posEnum posIdx) ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
        have hstep := congrArg (fun gramSum => probe ⬝ᵥ (gramSum *ᵥ probe)) hposSide
        simpa only [atomForm_eq_on_subset, Matrix.one_mulVec] using hstep
      have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
      have hlive : ∃ posIdx, baseAtom (posEnum posIdx) ⬝ᵥ probe ≠ 0 := by
        by_contra hdead
        push Not at hdead
        have hzero : ∑ posIdx, stressCoeff (posEnum posIdx)
            * (baseAtom (posEnum posIdx) ⬝ᵥ probe) ^ 2 = 0 :=
          Finset.sum_eq_zero fun posIdx _ => by rw [hdead posIdx]; ring
        rw [hzero] at hresolve
        exact absurd hresolve.symm (ne_of_gt hprobePos)
      obtain ⟨liveIdx, hliveNe⟩ := hlive
      refine Finset.sum_pos' (fun label _ => mul_nonneg (hweightPos label).le (sq_nonneg _))
        ⟨posEnum liveIdx, Finset.mem_univ _, mul_pos (hweightPos _) ?_⟩
      exact (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hliveNe))
    obtain ⟨design, hweightEq, hdesignStress, hdominationIff⟩ :=
      exists_design_of_baseFamily baseAtom weight hweightPos hweightSumOne hgramPosDef
        hbaseStress
    obtain ⟨selected, hcard, hposDef⟩ := hdesignSide design stressCoeff hdesignStress hfull
    exact ⟨selected, hcard, (hdominationIff selected).mp hposDef⟩

/-- **THE THIRTEEN-COORDINATE STATEMENT CLOSES THE BALANCED BRANCH.**  A `(6,3)`
tie carrying a full-support stress has a parallel pair — vacuously, since it
cannot exist at all: the thirteen-coordinate statement hands it a strictly
dominating triple and tightness forbids one.  This is the branch-(ii) capstone
of `Gtz.sixThree_stress_trichotomy` with its residual moved into coordinates. -/
theorem hasParallelPair_of_isTie_of_fullSupportStress_of_frameDomination
    (hframe : BalancedFrameDominationSixThree) (design : WeightedDesign 6 3)
    (htie : IsTie design) {stressCoeff : Fin 6 → ℝ}
    (hstress : ∑ label, stressCoeff label • atomMatrix (design.atom label) = 0)
    (hfull : ∀ label, stressCoeff label ≠ 0) : HasParallelPair design := by
  obtain ⟨selected, hcard, hposDef⟩ :=
    balancedFrameDomination_iff_balancedStratumHasStrictDominator.mp hframe design stressCoeff
      hstress hfull
  exact absurd hposDef (htie.2 selected hcard)


/-- **THE UNBALANCED HALF OF THE STRATUM IS ALREADY A THEOREM.**  A stress whose
coordinates do not sum to zero hands the design a strictly dominating triple
outright, by the landed strict stress walk
`Gtz.exists_posDef_sixThree_of_stress_sum_ne_zero`.  So the thirteen-coordinate
residual may assume the stress BALANCED — in the coordinates of
`BalancedFrameDominationSixThree` that is the single linear equation
`sum 1/A_i = sum 1/B_j`, one more constraint and one fewer free coordinate, at
no cost.  Any search over the stratum should impose it. -/
theorem balancedStratumHasStrictDominator_of_zeroSumStresses
    (hzeroSum : ∀ (design : WeightedDesign 6 3) (stressCoeff : Fin 6 → ℝ),
      (∑ label, stressCoeff label • atomMatrix (design.atom label)) = 0 →
      (∀ label, stressCoeff label ≠ 0) →
      (∑ label, stressCoeff label) = 0 →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    BalancedStratumHasStrictDominator := by
  intro design stressCoeff hstress hfull
  by_cases hsum : (∑ label, stressCoeff label) = 0
  · exact hzeroSum design stressCoeff hstress hfull hsum
  · exact exists_posDef_sixThree_of_stress_sum_ne_zero design
      (fun hzero => hfull 0 (congrFun hzero 0)) hstress hsum

end Gtz
