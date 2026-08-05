/-
# The endpoint-gauge descent: the walk-bottom is stress-free, and the boundary
# splits into named (5,3)/(4,3) residuals

The zero-sum frame-domination chain and the descent layer on top of it.
Content, all kernel-checked:

**1. THE WALK-BOTTOM IS STRESS-FREE** (`diagonalGauge_dependence_proportional`,
`diagonalGauge_dependence_eq_zero_of_vanishes`): in the diagonal endpoint
gauge, the dependence space of the six atom matrices is EXACTLY the line
through the given stress.  The proof is elementary and structural: the
off-diagonal entries of any dependence see only the negative side (the
positive side is axis-aligned), so a second dependence direction would force
the three negative off-diagonal patterns onto one line, and the case analysis
kills every pattern — a common vanished coordinate contradicts the negative
resolution, a common ratio contradicts primitivity, an axis-aligned negative
atom is parallel to a positive one.  Consequence: dropping ANY single atom
leaves five INDEPENDENT atom matrices.  The five-atom walk-bottom carries no
stress; the diamond worry dies structurally (see 3).

**2. THE VANISHED-COUNT SPLIT.**  At the endpoint one, two, or all three
positive-side weights vanish.  All-three is a THEOREM
(`exists_posDef_of_threeVanished`: the negative triple strictly dominates).
The remaining two strata are the named residuals
`OneVanishedRigidBottomDominationSixThree` (the generic (5,3)-type boundary)
and `TwoVanishedRigidBottomDominationSixThree` (the (4,3)-type boundary, whose
equality locus is the explicit (4,3) total-tie family), each handed the
rigidity of 1 as a free hypothesis.  `diagonalEndpointGauge_of_vanishedCases`
assembles them into `DiagonalEndpointZeroSumFrameDominationSixThree`, hence
into `BalancedStratumSelection 6` and rank-3 GTZ modulo the stress-free hinge.

**3. THE DIAMOND CANNOT BE THE WALK-BOTTOM**
(`no_relabeled_diamondShape_of_endpointGauge`): the landed Theorem A
(`Gtz.diamondExtension_no_fullSupport_stress`) says NO extension of a
diamond-shape five-family carries a full-support stress; the endpoint data
carries one; so no five of the six atoms realize the diamond shape under any
relabeling.  The only known primitive (5,3) tie is therefore excluded from
the boundary.

**4. THE (5,3) ISOLATION** (`oneVanished_of_spikedBottomDomination`): the
one-vanished stratum whitens to a genuine `WeightedDesign 5 3` — the BOTTOM —
plus one weightless SPIKE direction, the stress and its zero sum riding along.
`SpikedStressFreeBottomDominationFiveThree` is that statement: a stress-free
primitive weighted (5,3) design, a spike of positive stress coefficient
closing the zero-sum balance, conclusion a strict dominator among the ten
bottom triples OR the ten spike triples.  Its tie-exclusion sharpening
`EndpointBottomTieExclusionFiveThree` (the bottom design is never an exact
tie) IMPLIES it through the landed `Gtz.gtzWeighted_of_le_five`
(`spikedBottomDomination_of_tieExclusion`) — so the sharpest one-premise
conditional for the one-vanished stratum is a (5,3) TIE EXCLUSION, exactly
one rung below the (6,3) tie exclusion that branch (ii) itself is.

Measured controls (p16 witnesses, exact rationals + 80-digit mpmath): at all
eight walked bottoms the stress space is exactly one-dimensional, a BOTTOM
triple strictly dominates (spike never required: best bottom margins
1.7e-5 … 0.28), and no coplanar atom triple exists (diamond distance
positive).  The p16 dominator lists reproduce exactly.

The p16 base layer starts here; two contributions, both reductions.

**1. The zero-sum frame residual.**  `Gtz.BalancedFrameDominationSixThree`
(landed) moved branch (ii) into raw coordinates but kept neither the balance
equation nor primitivity.  `ZeroSumFrameDominationSixThree` restores both: the
quantified family may be assumed BALANCED (`∑ stressCoeff = 0`) and PRIMITIVE
(no two base atoms parallel), because the design-side statement it must serve —
`NoPrimitiveBalancedTieZeroSumSixThree` — supplies both, and the whitening
transport preserves both (the stress coefficients pass through untouched; an
invertible whitener preserves non-parallelism).

**2. The endpoint gauge.**  On the zero-sum slice the weight walk along the
stress FIXES the frame residual's data: the walked weights still sum to one
(their defect is `walkStep * ∑ stressCoeff = 0`) and the weighted Gram is
literally unchanged (the walk direction is a stress).  Walking to the first
vanishing weight is therefore free, and the residual only has to be proved at
configurations where SOME positive-side weight is ZERO —
`EndpointZeroSumFrameDominationSixThree`.  One coordinate of the thirteen is
gone, at no cost.  This gauge is special to the slice: off it the walk loses
mass and the landed strict walk already closes everything
(`Gtz.exists_posDef_sixThree_of_stress_sum_ne_zero`).

**The wall this file does NOT break** (measured, and mechanized as
`dotProduct_frameTripleSum_inv_self_eq_one`): the stratum's margin infimum is
ZERO, reached along the heavy-weight escape.  For ANY basis triple the frame
operator of the triple gives each of its own members self-pivot exactly one, so
as one atom's weight tends to one the whitened gaps of every triple through
that atom flatten to zero from whichever side the second-order data chooses.
Exact certification of the escape: a slice configuration with
`t_heavy = 1 - 1.2e-7` has exact max-margin `5.49e-9 > 0` (positive — no tie),
while interior configurations with weights bounded by `0.02` certify at
`1.35e-2`.  A uniform threshold certificate therefore cannot exist on the open
stratum, exactly as on branch (i); any closing argument must be weight-aware,
with the heavy corner as its equality locus.

The tail of the file re-records the `/tmp` reduction of `BalancedTieReduction`
(p15, not in the tree) so that the chain from the endpoint gauge to
`Gtz.BalancedStratumSelection 6` — and through the landed composite to rank-3
GTZ conditional on the stress-free hinge — is verifiable from this one file.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.BalancedStratum
import Gtz.Design.BalancedNormalForm
import Gtz.Reduction.BalancedTieReduction
import Gtz.Reduction.StressConditionalWalk
import Gtz.Reduction.HingeFunnel
import Gtz.Quantitative.HingeStressNarrowing
import Gtz.Reduction.TrichotomyLedger
import Gtz.Reduction.RankThreeComposite
import Gtz.Design.DiamondStressSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The two-sided resolutions are a stress

Extracted from the reverse leg of
`Gtz.balancedFrameDomination_iff_balancedStratumHasStrictDominator`: if the
positive-side atoms resolve the identity against the stress coefficients and
the negative-side atoms resolve it against their negatives, the whole family
carries the coefficients as a stress. -/

theorem stress_of_twoSidedResolutions (baseAtom : Fin 6 → Fin 3 → ℝ)
    (stressCoeff : Fin 6 → ℝ) (posEnum negEnum : Fin 3 → Fin 6)
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (hposInjective : Function.Injective posEnum)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hposOnto : ∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label)
    (hnegInjective : Function.Injective negEnum)
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hnegOnto : ∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label)
    (hposSide : ∑ posIdx, stressCoeff (posEnum posIdx)
      • atomMatrix (baseAtom (posEnum posIdx)) = 1)
    (hnegSide : ∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1) :
    ∑ label, stressCoeff label • atomMatrix (baseAtom label) = 0 := by
  classical
  have hdisjoint : Disjoint (Finset.univ.filter fun label => 0 < stressCoeff label)
      (Finset.univ.filter fun label => stressCoeff label < 0) := by
    rw [Finset.disjoint_left]
    intro label hposMem hnegMem
    exact absurd (Finset.mem_filter.mp hnegMem).2 (asymm (Finset.mem_filter.mp hposMem).2)
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

/-! ## The zero-sum frame residual -/

/-- **The zero-sum, primitive frame residual.**  The landed
`Gtz.BalancedFrameDominationSixThree` with two extra hypotheses the design side
supplies for free: the stress coefficients sum to ZERO (the balance equation,
`sum 1/A_i = sum 1/B_j` in scale coordinates), and the base family is
PRIMITIVE.  Anything proving this proves branch (ii) on the slice — and off
the slice the strict walk is already a theorem. -/
def ZeroSumFrameDominationSixThree : Prop :=
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
    (∑ label, stressCoeff label) = 0 →
    (∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel) →
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ ((∑ label ∈ selected, atomMatrix (baseAtom label))
          - ∑ label, weight label • atomMatrix (baseAtom label)).PosDef

/-! ## The endpoint gauge -/

/-- **The endpoint-gauge residual.**  The same statement asked only where some
positive-side weight has already been walked to ZERO; every weight is still
nonnegative and the negative side is still strictly positive.  One fewer free
coordinate. -/
def EndpointZeroSumFrameDominationSixThree : Prop :=
  ∀ (baseAtom : Fin 6 → Fin 3 → ℝ) (weight stressCoeff : Fin 6 → ℝ)
    (posEnum negEnum : Fin 3 → Fin 6),
    (∀ label, 0 ≤ weight label) → (∑ label, weight label = 1) →
    (∀ label, stressCoeff label < 0 → 0 < weight label) →
    (∃ posIdx, weight (posEnum posIdx) = 0) →
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
    (∑ label, stressCoeff label) = 0 →
    (∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel) →
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ ((∑ label ∈ selected, atomMatrix (baseAtom label))
          - ∑ label, weight label • atomMatrix (baseAtom label)).PosDef

/-- **THE WALK TO THE ENDPOINT IS FREE ON THE SLICE.**  Walking the weights
along the stress until the first positive-side weight vanishes changes NOTHING
the residual can see: the weight sum survives because the stress balances, and
the weighted Gram survives because the direction is a stress.  So the interior
residual follows from its endpoint restriction outright. -/
theorem zeroSumFrameDomination_of_endpointGauge
    (hendpoint : EndpointZeroSumFrameDominationSixThree) :
    ZeroSumFrameDominationSixThree := by
  classical
  intro baseAtom weight stressCoeff posEnum negEnum hweightPos hweightSumOne hfull
    hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto
    hposSide hnegSide hzeroSum hprimitive
  obtain ⟨minIdx, -, hminIdx⟩ := Finset.exists_min_image Finset.univ
    (fun posIdx => weight (posEnum posIdx) / stressCoeff (posEnum posIdx))
    ⟨0, Finset.mem_univ 0⟩
  set walkStep : ℝ := weight (posEnum minIdx) / stressCoeff (posEnum minIdx) with hwalkStep
  have hstepPos : 0 < walkStep :=
    div_pos (hweightPos (posEnum minIdx)) (hposSign minIdx)
  set walked : Fin 6 → ℝ := fun label => weight label - walkStep * stressCoeff label
    with hwalked
  have hwalkedNegSide : ∀ label, stressCoeff label < 0 → 0 < walked label := by
    intro label hneg
    have hweight := hweightPos label
    simp only [hwalked]
    nlinarith
  have hwalkedNonneg : ∀ label, 0 ≤ walked label := by
    intro label
    rcases lt_or_lt_iff_ne.mpr (hfull label) with hneg | hpos
    · exact (hwalkedNegSide label hneg).le
    · obtain ⟨posIdx, hposIdx⟩ := hposOnto label hpos
      have hbound : walkStep ≤ weight (posEnum posIdx) / stressCoeff (posEnum posIdx) := by
        rw [hwalkStep]
        exact hminIdx posIdx (Finset.mem_univ posIdx)
      rw [hposIdx] at hbound
      have hproduct : walkStep * stressCoeff label ≤ weight label :=
        (le_div_iff₀ hpos).mp hbound
      simp only [hwalked]
      linarith
  have hwalkedAtMin : walked (posEnum minIdx) = 0 := by
    simp only [hwalked, hwalkStep]
    rw [div_mul_cancel₀ _ (ne_of_gt (hposSign minIdx)), sub_self]
  have hwalkedSumOne : ∑ label, walked label = 1 := by
    simp only [hwalked]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzeroSum, mul_zero, sub_zero,
      hweightSumOne]
  have hbaseStress : ∑ label, stressCoeff label • atomMatrix (baseAtom label) = 0 :=
    stress_of_twoSidedResolutions baseAtom stressCoeff posEnum negEnum hfull
      hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hposSide hnegSide
  have hsameGram : ∑ label, walked label • atomMatrix (baseAtom label)
      = ∑ label, weight label • atomMatrix (baseAtom label) := by
    simp only [hwalked, sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hbaseStress, smul_zero, sub_zero]
  obtain ⟨selected, hcard, hposDef⟩ := hendpoint baseAtom walked stressCoeff posEnum negEnum
    hwalkedNonneg hwalkedSumOne hwalkedNegSide ⟨minIdx, hwalkedAtMin⟩ hfull
    hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto
    hposSide hnegSide hzeroSum hprimitive
  rw [hsameGram] at hposDef
  exact ⟨selected, hcard, hposDef⟩

/-! ## Primitivity survives whitening -/

/-- An invertible matrix preserves non-parallelism of vectors. -/
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

/-! ## The transport from the residual to the design side -/

/-- **The zero-sum frame residual hands every primitive balanced zero-sum
design a strictly dominating triple.**  The forward transport of
`Gtz.balancedFrameDomination_iff_balancedStratumHasStrictDominator`, carrying
the two extra facts through the whitening: the stress coefficients cross
untouched, so their zero sum survives, and the whitener is invertible, so
primitivity survives. -/
theorem exists_posDef_triple_of_zeroSumFrameDomination
    (hframe : ZeroSumFrameDominationSixThree) (design : WeightedDesign 6 3)
    (stressCoeff : Fin 6 → ℝ)
    (hstress : ∑ label, stressCoeff label • atomMatrix (design.atom label) = 0)
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (hzeroSum : (∑ label, stressCoeff label) = 0)
    (hprimitive : IsPrimitiveDesign design) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
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
  have hbasePrimitive : ∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ),
      keptLabel ≠ dropLabel →
      (fun label => whitener *ᵥ design.atom label) dropLabel
        ≠ ratio • (fun label => whitener *ᵥ design.atom label) keptLabel := by
    intro keptLabel dropLabel ratio hdistinct
    exact mulVec_ne_smul_of_ne_smul hdetNe (hprimitive keptLabel dropLabel ratio hdistinct)
  obtain ⟨selected, hcard, hposDef⟩ := hframe (fun label => whitener *ᵥ design.atom label)
    design.weight stressCoeff posEnum negEnum design.weight_pos design.weight_sum_one hfull
    hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hposSide hnegSide
    hzeroSum hbasePrimitive
  refine ⟨selected, hcard, ?_⟩
  have hunit : IsUnit (whitenerᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hdetNe
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

/-! ## The `/tmp` reduction of p15, re-recorded

The following block builds on `Gtz.Reduction.BalancedTieReduction`
(verified against the tree, never landed) so this file's chain is closed. -/

/-- The zero-sum slice is no restriction on the tie side. -/
theorem noPrimitiveBalancedTie_of_zeroSumExclusion
    (hexclusion : NoPrimitiveBalancedTieZeroSumSixThree) :
    NoPrimitiveBalancedTieSixThree := by
  intro design stressCoeff hstress hfull hprimitive htie
  exact hexclusion design stressCoeff hstress hfull
    (hasOnlyBalancedStress_of_isTie_sixThree design htie stressCoeff
      (stress_ne_zero_of_fullSupport hfull) hstress)
    hprimitive htie

/-! ## The chain assembled -/

/-- **The zero-sum frame residual excludes the zero-sum tie.** -/
theorem noPrimitiveBalancedTieZeroSum_of_zeroSumFrameDomination
    (hframe : ZeroSumFrameDominationSixThree) :
    NoPrimitiveBalancedTieZeroSumSixThree := by
  intro design stressCoeff hstress hfull hzeroSum hprimitive htie
  obtain ⟨selected, hcard, hposDef⟩ := exists_posDef_triple_of_zeroSumFrameDomination
    hframe design stressCoeff hstress hfull hzeroSum hprimitive
  exact htie.2 selected hcard hposDef

/-- **The endpoint gauge closes branch (ii).**  The sharpest single-premise
conditional this file reaches: `Gtz.BalancedStratumSelection 6` from the
endpoint-gauge frame statement alone. -/
theorem balancedStratumSelection_six_of_endpointGauge
    (hendpoint : EndpointZeroSumFrameDominationSixThree) :
    BalancedStratumSelection 6 :=
  balancedStratumSelection_six_of_zeroSumTieExclusion
    (noPrimitiveBalancedTieZeroSum_of_zeroSumFrameDomination
      (zeroSumFrameDomination_of_endpointGauge hendpoint))

/-- **Rank-3 GTZ from two Props, the balanced one in endpoint gauge.**  With the
landed composite, every `n`-by-three orthonormal-column matrix has a three-row
submatrix of least singular value at least `1 / sqrt n`, as soon as the
endpoint-gauge frame statement and the stress-free hinge hold. -/
theorem forall_gtzOriginal_rank_three_of_endpointGauge_and_stressFreeHinge
    (hendpoint : EndpointZeroSumFrameDominationSixThree)
    (hstressFreeHinge : StressFreeHingeHoldsSixThree) :
    ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  forall_gtzOriginal_rank_three_of_balancedSelection_and_stressFreeHinge
    (balancedStratumSelection_six_of_endpointGauge hendpoint) hstressFreeHinge

/-! ## The diagonal gauge

The whitener of the two-frame normal form is determined only up to a left
rotation.  Spending that freedom on the ROTATION THAT CARRIES THE WHITENED
POSITIVE FRAME TO THE COORDINATE AXES makes the positive side literally
diagonal: each positive-side base atom is supported on its own axis.  Three
more coordinates gone; what remains is the numeric lab's chart — one rotation,
six scales, six weights, two linear relations, and the endpoint gauge. -/

/-- **The diagonal endpoint residual.**  The endpoint-gauge statement asked
only of families whose positive side is axis-aligned: the atom enumerated at
`posIdx` vanishes at every coordinate other than `posIdx`.  This is the
sharpest single premise this file reaches. -/
def DiagonalEndpointZeroSumFrameDominationSixThree : Prop :=
  ∀ (baseAtom : Fin 6 → Fin 3 → ℝ) (weight stressCoeff : Fin 6 → ℝ)
    (posEnum negEnum : Fin 3 → Fin 6),
    (∀ label, 0 ≤ weight label) → (∑ label, weight label = 1) →
    (∀ label, stressCoeff label < 0 → 0 < weight label) →
    (∃ posIdx, weight (posEnum posIdx) = 0) →
    (∀ label, stressCoeff label ≠ 0) →
    Function.Injective posEnum →
    (∀ posIdx, 0 < stressCoeff (posEnum posIdx)) →
    (∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label) →
    Function.Injective negEnum →
    (∀ negIdx, stressCoeff (negEnum negIdx) < 0) →
    (∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label) →
    (∀ posIdx coord, coord ≠ posIdx → baseAtom (posEnum posIdx) coord = 0) →
    (∑ posIdx, stressCoeff (posEnum posIdx)
      • atomMatrix (baseAtom (posEnum posIdx)) = 1) →
    (∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1) →
    (∑ label, stressCoeff label) = 0 →
    (∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel) →
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ ((∑ label ∈ selected, atomMatrix (baseAtom label))
          - ∑ label, weight label • atomMatrix (baseAtom label)).PosDef

/-- The interior form of the diagonal residual, an intermediate station: the
walk to the endpoint does not touch the atoms, so axis alignment survives it
verbatim. -/
def DiagonalZeroSumFrameDominationSixThree : Prop :=
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
    (∀ posIdx coord, coord ≠ posIdx → baseAtom (posEnum posIdx) coord = 0) →
    (∑ posIdx, stressCoeff (posEnum posIdx)
      • atomMatrix (baseAtom (posEnum posIdx)) = 1) →
    (∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1) →
    (∑ label, stressCoeff label) = 0 →
    (∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel) →
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ ((∑ label ∈ selected, atomMatrix (baseAtom label))
          - ∑ label, weight label • atomMatrix (baseAtom label)).PosDef

/-- The endpoint walk, re-run with the diagonal hypothesis riding along
untouched. -/
theorem diagonalZeroSumFrameDomination_of_endpointGauge
    (hendpoint : DiagonalEndpointZeroSumFrameDominationSixThree) :
    DiagonalZeroSumFrameDominationSixThree := by
  classical
  intro baseAtom weight stressCoeff posEnum negEnum hweightPos hweightSumOne hfull
    hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hdiagonal
    hposSide hnegSide hzeroSum hprimitive
  obtain ⟨minIdx, -, hminIdx⟩ := Finset.exists_min_image Finset.univ
    (fun posIdx => weight (posEnum posIdx) / stressCoeff (posEnum posIdx))
    ⟨0, Finset.mem_univ 0⟩
  set walkStep : ℝ := weight (posEnum minIdx) / stressCoeff (posEnum minIdx) with hwalkStep
  have hstepPos : 0 < walkStep :=
    div_pos (hweightPos (posEnum minIdx)) (hposSign minIdx)
  set walked : Fin 6 → ℝ := fun label => weight label - walkStep * stressCoeff label
    with hwalked
  have hwalkedNegSide : ∀ label, stressCoeff label < 0 → 0 < walked label := by
    intro label hneg
    have hweight := hweightPos label
    simp only [hwalked]
    nlinarith
  have hwalkedNonneg : ∀ label, 0 ≤ walked label := by
    intro label
    rcases lt_or_lt_iff_ne.mpr (hfull label) with hneg | hpos
    · exact (hwalkedNegSide label hneg).le
    · obtain ⟨posIdx, hposIdx⟩ := hposOnto label hpos
      have hbound : walkStep ≤ weight (posEnum posIdx) / stressCoeff (posEnum posIdx) := by
        rw [hwalkStep]
        exact hminIdx posIdx (Finset.mem_univ posIdx)
      rw [hposIdx] at hbound
      have hproduct : walkStep * stressCoeff label ≤ weight label :=
        (le_div_iff₀ hpos).mp hbound
      simp only [hwalked]
      linarith
  have hwalkedAtMin : walked (posEnum minIdx) = 0 := by
    simp only [hwalked, hwalkStep]
    rw [div_mul_cancel₀ _ (ne_of_gt (hposSign minIdx)), sub_self]
  have hwalkedSumOne : ∑ label, walked label = 1 := by
    simp only [hwalked]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzeroSum, mul_zero, sub_zero,
      hweightSumOne]
  have hbaseStress : ∑ label, stressCoeff label • atomMatrix (baseAtom label) = 0 :=
    stress_of_twoSidedResolutions baseAtom stressCoeff posEnum negEnum hfull
      hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hposSide hnegSide
  have hsameGram : ∑ label, walked label • atomMatrix (baseAtom label)
      = ∑ label, weight label • atomMatrix (baseAtom label) := by
    simp only [hwalked, sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hbaseStress, smul_zero, sub_zero]
  obtain ⟨selected, hcard, hposDef⟩ := hendpoint baseAtom walked stressCoeff posEnum negEnum
    hwalkedNonneg hwalkedSumOne hwalkedNegSide ⟨minIdx, hwalkedAtMin⟩ hfull
    hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hdiagonal
    hposSide hnegSide hzeroSum hprimitive
  rw [hsameGram] at hposDef
  exact ⟨selected, hcard, hposDef⟩

/-- **The rotated transport.**  The whitener composed with the rotation onto the
whitened positive frame is again a whitener of the positive side, and it sends
each positive-side atom to its own coordinate axis, so the diagonal residual
receives everything it asks for. -/
theorem exists_posDef_triple_of_diagonalZeroSumFrameDomination
    (hframe : DiagonalZeroSumFrameDominationSixThree) (design : WeightedDesign 6 3)
    (stressCoeff : Fin 6 → ℝ)
    (hstress : ∑ label, stressCoeff label • atomMatrix (design.atom label) = 0)
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (hzeroSum : (∑ label, stressCoeff label) = 0)
    (hprimitive : IsPrimitiveDesign design) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  obtain ⟨posEnum, negEnum, hposInjective, hposSign, hposOnto,
    hnegInjective, hnegSign, hnegOnto⟩ :=
    exists_signEnumerations_sixThree design hstress hfull
  obtain ⟨whitener, hdetNe, horthonormal⟩ :=
    twoFrame_normalForm design hstress hfull posEnum hposInjective hposSign hposOnto
  -- the whitened, stress-normalised positive frame
  set posFrame : Fin 3 → Fin 3 → ℝ := fun posIdx =>
    Real.sqrt (stressCoeff (posEnum posIdx))
      • (whitener *ᵥ design.atom (posEnum posIdx)) with hposFrame
  have hframeOrthonormal : ∀ leftIdx rightIdx : Fin 3,
      posFrame leftIdx ⬝ᵥ posFrame rightIdx = if leftIdx = rightIdx then 1 else 0 := by
    intro leftIdx rightIdx
    simp only [hposFrame]
    exact horthonormal leftIdx rightIdx
  -- the rotation whose rows are the positive frame
  set rotation : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of posFrame with hrotation
  have hrotationOrtho : rotation * rotationᵀ = 1 := by
    ext leftIdx rightIdx
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hdot := hframeOrthonormal leftIdx rightIdx
    simpa [hrotation, Matrix.transpose_apply, dotProduct] using hdot
  have hrotationDetUnit : IsUnit rotation.det := by
    have hdetProduct : rotation.det * rotation.det = 1 := by
      have hstep := congrArg Matrix.det hrotationOrtho
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hstep
    have hdetNeZero : rotation.det ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hdetProduct
      exact zero_ne_one hdetProduct
    exact isUnit_iff_ne_zero.mpr hdetNeZero
  have hrotationDetNe : rotation.det ≠ 0 := hrotationDetUnit.ne_zero
  -- the rotated whitener
  set alignedWhitener : Matrix (Fin 3) (Fin 3) ℝ := rotation * whitener
    with halignedWhitener
  have halignedDetNe : alignedWhitener.det ≠ 0 := by
    rw [halignedWhitener, Matrix.det_mul]
    exact mul_ne_zero hrotationDetNe hdetNe
  -- the rotation carries each whitened positive atom to its own axis
  have hsqrtPos : ∀ posIdx : Fin 3, 0 < Real.sqrt (stressCoeff (posEnum posIdx)) :=
    fun posIdx => Real.sqrt_pos.mpr (hposSign posIdx)
  have haligned : ∀ posIdx coord : Fin 3, coord ≠ posIdx →
      (alignedWhitener *ᵥ design.atom (posEnum posIdx)) coord = 0 := by
    intro posIdx coord hne
    have hvalue : (alignedWhitener *ᵥ design.atom (posEnum posIdx)) coord
        = posFrame coord ⬝ᵥ (whitener *ᵥ design.atom (posEnum posIdx)) := by
      rw [halignedWhitener, ← Matrix.mulVec_mulVec]
      simp [hrotation, Matrix.mulVec, dotProduct]
    have hpaired : posFrame coord ⬝ᵥ posFrame posIdx = 0 := by
      rw [hframeOrthonormal coord posIdx, if_neg hne]
    have hexpanded : posFrame coord ⬝ᵥ posFrame posIdx
        = Real.sqrt (stressCoeff (posEnum posIdx))
          * (posFrame coord ⬝ᵥ (whitener *ᵥ design.atom (posEnum posIdx))) := by
      simp only [hposFrame]
      rw [dotProduct_smul]
      simp
    rw [hexpanded] at hpaired
    rcases mul_eq_zero.mp hpaired with hsqrtZero | hdotZero
    · exact absurd hsqrtZero (ne_of_gt (hsqrtPos posIdx))
    · rw [hvalue]
      exact hdotZero
  -- the rotated whitener still whitens the positive side
  obtain ⟨plainWhitener, hplainDetNe, hplainSandwich⟩ :=
    exists_whitening_of_positiveSide design hstress hfull
  have halignedSandwich : alignedWhitener
      * (∑ label ∈ Finset.univ.filter (fun label => 0 < stressCoeff label),
          stressCoeff label • atomMatrix (design.atom label)) * alignedWhitenerᵀ = 1 := by
    have hposSum : ∑ posIdx, Matrix.vecMulVec (posFrame posIdx) (posFrame posIdx)
        = (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
      sum_rankOne_eq_one_of_orthonormalFrame posFrame hframeOrthonormal
    have hterm : ∀ posIdx : Fin 3,
        Matrix.vecMulVec (posFrame posIdx) (posFrame posIdx)
          = stressCoeff (posEnum posIdx)
            • atomMatrix (whitener *ᵥ design.atom (posEnum posIdx)) := by
      intro posIdx
      show atomMatrix _ = _
      simp only [hposFrame]
      rw [atomMatrix_smul, Real.sq_sqrt (hposSign posIdx).le]
    have hwhitenerSandwich : whitener
        * (∑ label ∈ Finset.univ.filter (fun label => 0 < stressCoeff label),
            stressCoeff label • atomMatrix (design.atom label)) * whitenerᵀ = 1 := by
      have hreindex := sum_filter_eq_sum_enum (fun label => 0 < stressCoeff label) posEnum
        hposInjective hposSign hposOnto
        (fun label => stressCoeff label • atomMatrix (whitener *ᵥ design.atom label))
      calc whitener * (∑ label ∈ Finset.univ.filter (fun label => 0 < stressCoeff label),
              stressCoeff label • atomMatrix (design.atom label)) * whitenerᵀ
          = ∑ label ∈ Finset.univ.filter (fun label => 0 < stressCoeff label),
              stressCoeff label • atomMatrix (whitener *ᵥ design.atom label) :=
            (sum_smul_atomMatrix_mulVec_eq_conjugate whitener design.atom stressCoeff
              (Finset.univ.filter fun label => 0 < stressCoeff label)).symm
        _ = ∑ posIdx, stressCoeff (posEnum posIdx)
              • atomMatrix (whitener *ᵥ design.atom (posEnum posIdx)) := hreindex
        _ = ∑ posIdx, Matrix.vecMulVec (posFrame posIdx) (posFrame posIdx) :=
            (Finset.sum_congr rfl fun posIdx _ => (hterm posIdx).symm)
        _ = 1 := hposSum
    rw [halignedWhitener, Matrix.transpose_mul]
    calc rotation * whitener
          * (∑ label ∈ Finset.univ.filter (fun label => 0 < stressCoeff label),
              stressCoeff label • atomMatrix (design.atom label))
          * (whitenerᵀ * rotationᵀ)
        = rotation * (whitener
            * (∑ label ∈ Finset.univ.filter (fun label => 0 < stressCoeff label),
                stressCoeff label • atomMatrix (design.atom label)) * whitenerᵀ)
          * rotationᵀ := by
          simp only [Matrix.mul_assoc]
      _ = rotation * rotationᵀ := by rw [hwhitenerSandwich, Matrix.mul_one]
      _ = 1 := hrotationOrtho
  have hmiddle := posSide_sum_eq_negSide_sum design.atom hstress hfull
  have hposSide : ∑ posIdx, stressCoeff (posEnum posIdx)
      • atomMatrix (alignedWhitener *ᵥ design.atom (posEnum posIdx)) = 1 := by
    have hreindex := sum_filter_eq_sum_enum (fun label => 0 < stressCoeff label) posEnum
      hposInjective hposSign hposOnto
      (fun label => stressCoeff label • atomMatrix (alignedWhitener *ᵥ design.atom label))
    rw [← hreindex, sum_smul_atomMatrix_mulVec_eq_conjugate]
    exact halignedSandwich
  have hnegSide : ∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (alignedWhitener *ᵥ design.atom (negEnum negIdx)) = 1 := by
    have hreindex := sum_filter_eq_sum_enum (fun label => stressCoeff label < 0) negEnum
      hnegInjective hnegSign hnegOnto
      (fun label => (-stressCoeff label)
        • atomMatrix (alignedWhitener *ᵥ design.atom label))
    rw [← hreindex, sum_smul_atomMatrix_mulVec_eq_conjugate, ← hmiddle]
    exact halignedSandwich
  have hbasePrimitive : ∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ),
      keptLabel ≠ dropLabel →
      (fun label => alignedWhitener *ᵥ design.atom label) dropLabel
        ≠ ratio • (fun label => alignedWhitener *ᵥ design.atom label) keptLabel := by
    intro keptLabel dropLabel ratio hdistinct
    exact mulVec_ne_smul_of_ne_smul halignedDetNe
      (hprimitive keptLabel dropLabel ratio hdistinct)
  obtain ⟨selected, hcard, hposDef⟩ := hframe
    (fun label => alignedWhitener *ᵥ design.atom label)
    design.weight stressCoeff posEnum negEnum design.weight_pos design.weight_sum_one hfull
    hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto haligned
    hposSide hnegSide hzeroSum hbasePrimitive
  refine ⟨selected, hcard, ?_⟩
  have hunit : IsUnit (alignedWhitenerᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr halignedDetNe
  have hselectedSum : ∑ label ∈ selected, atomMatrix (alignedWhitener *ᵥ design.atom label)
      = alignedWhitener * (subsetSum design selected) * alignedWhitenerᵀ := by
    have hstep := sum_smul_atomMatrix_mulVec_eq_conjugate alignedWhitener design.atom
      (fun _ => (1 : ℝ)) selected
    simpa only [one_smul, subsetSum] using hstep
  have hgramSum : ∑ label, design.weight label
      • atomMatrix (alignedWhitener *ᵥ design.atom label)
      = alignedWhitener * alignedWhitenerᵀ := by
    rw [sum_smul_atomMatrix_mulVec_eq_conjugate, design.isParseval, Matrix.mul_one]
  rw [hselectedSum, hgramSum] at hposDef
  have hconjugate : alignedWhitener * (subsetSum design selected) * alignedWhitenerᵀ
      - alignedWhitener * alignedWhitenerᵀ
      = (alignedWhitenerᵀ)ᵀ * (subsetSum design selected - 1) * alignedWhitenerᵀ := by
    rw [Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [hconjugate] at hposDef
  exact (posDef_congruence_iff hunit).mp hposDef

/-- The diagonal residual excludes the zero-sum tie. -/
theorem noPrimitiveBalancedTieZeroSum_of_diagonalZeroSumFrameDomination
    (hframe : DiagonalZeroSumFrameDominationSixThree) :
    NoPrimitiveBalancedTieZeroSumSixThree := by
  intro design stressCoeff hstress hfull hzeroSum hprimitive htie
  obtain ⟨selected, hcard, hposDef⟩ := exists_posDef_triple_of_diagonalZeroSumFrameDomination
    hframe design stressCoeff hstress hfull hzeroSum hprimitive
  exact htie.2 selected hcard hposDef

/-- **The diagonal endpoint gauge closes branch (ii).**  The single sharpest
premise of this file: ten coordinates, axis-aligned positive side, one weight
walked to zero. -/
theorem balancedStratumSelection_six_of_diagonalEndpointGauge
    (hendpoint : DiagonalEndpointZeroSumFrameDominationSixThree) :
    BalancedStratumSelection 6 :=
  balancedStratumSelection_six_of_zeroSumTieExclusion
    (noPrimitiveBalancedTieZeroSum_of_diagonalZeroSumFrameDomination
      (diagonalZeroSumFrameDomination_of_endpointGauge hendpoint))

/-- Rank-3 GTZ from the diagonal endpoint gauge and the stress-free hinge. -/
theorem forall_gtzOriginal_rank_three_of_diagonalEndpointGauge_and_stressFreeHinge
    (hendpoint : DiagonalEndpointZeroSumFrameDominationSixThree)
    (hstressFreeHinge : StressFreeHingeHoldsSixThree) :
    ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  forall_gtzOriginal_rank_three_of_balancedSelection_and_stressFreeHinge
    (balancedStratumSelection_six_of_diagonalEndpointGauge hendpoint) hstressFreeHinge

/-! ## The heavy-corner wall

The margin infimum of the zero-sum stratum is ZERO, along the escape where one
weight exhausts the design.  The mechanism is the identity below: in the frame
operator of any basis triple, each member's self-pivot is exactly one.  As the
weight of an atom tends to one, the design's weighted Gram concentrates on that
atom, and every triple through the atom has its whitened gap flattened to the
self-pivot direction — generalized margin tending to `1/1 - 1 = 0`.  Exact
certification of the escape (p16 lab): max-margin `5.49e-9 > 0` at
`t_heavy = 1 - 1.2e-7` on the slice; `1.35e-2` at weights bounded by `0.02`.
So no uniform threshold closes the endpoint residual; a closing argument must
be weight-aware, with the heavy corner as its equality locus — the same shape
branch (iii) resolved by an exact-product defect. -/

/-- **Self-pivot one in a basis triple.**  For an invertible `rowFrame`, the row
`rowFrame 0` evaluated in the inverse of the frame operator `rowFrameᵀ *
rowFrame` gives exactly one. -/
theorem dotProduct_frameTripleSum_inv_self_eq_one
    (rowFrame : Matrix (Fin 3) (Fin 3) ℝ) (hunit : IsUnit rowFrame.det) :
    rowFrame 0 ⬝ᵥ ((rowFrameᵀ * rowFrame)⁻¹ *ᵥ rowFrame 0) = 1 := by
  classical
  have hunitTranspose : IsUnit (rowFrameᵀ).det := by
    rw [Matrix.det_transpose]
    exact hunit
  have hrowAsMulVec : rowFrame 0
      = rowFrameᵀ *ᵥ (fun index => if index = 0 then 1 else 0) := by
    funext coord
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro other _ hother
      simp [hother]
    · intro habsurd
      exact absurd (Finset.mem_univ 0) habsurd
  have hinvCollapse : (rowFrameᵀ * rowFrame)⁻¹ * rowFrameᵀ = rowFrame⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunitTranspose,
      Matrix.mul_one]
  rw [hrowAsMulVec, Matrix.mulVec_mulVec, hinvCollapse, Matrix.mulVec_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
    Matrix.one_mulVec]
  simp [dotProduct]

/-! # The p17 layer

## Layer 1: entries, sign splits, and THE STRESS-FREE WALK-BOTTOM -/

/-- One scalar entry of a matrix identity between an atom combination and a
target matrix. -/
theorem entry_of_atomCombination {count : ℕ} {atomFamily : Fin count → Fin 3 → ℝ}
    {coeff : Fin count → ℝ} {targetMatrix : Matrix (Fin 3) (Fin 3) ℝ}
    (hcombination : ∑ label, coeff label • atomMatrix (atomFamily label) = targetMatrix)
    (rowIdx colIdx : Fin 3) :
    ∑ label, coeff label * (atomFamily label rowIdx * atomFamily label colIdx)
      = targetMatrix rowIdx colIdx := by
  have hentry := congrFun (congrFun hcombination rowIdx) colIdx
  simpa only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
    smul_eq_mul, mul_assoc] using hentry

/-- Any six-label sum splits into its positive-side and negative-side
enumerations. -/
theorem sum_split_by_signEnumerations {carrier : Type*} [AddCommMonoid carrier]
    {stressCoeff : Fin 6 → ℝ} {posEnum negEnum : Fin 3 → Fin 6}
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (hposInjective : Function.Injective posEnum)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hposOnto : ∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label)
    (hnegInjective : Function.Injective negEnum)
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hnegOnto : ∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label)
    (summand : Fin 6 → carrier) :
    ∑ label, summand label
      = (∑ posIdx, summand (posEnum posIdx)) + ∑ negIdx, summand (negEnum negIdx) := by
  classical
  have hdisjoint : Disjoint (Finset.univ.filter fun label => 0 < stressCoeff label)
      (Finset.univ.filter fun label => stressCoeff label < 0) := by
    rw [Finset.disjoint_left]
    intro label hposMem hnegMem
    exact absurd (Finset.mem_filter.mp hnegMem).2 (asymm (Finset.mem_filter.mp hposMem).2)
  have hcover : (Finset.univ.filter fun label => 0 < stressCoeff label)
      ∪ (Finset.univ.filter fun label => stressCoeff label < 0) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun label => ?_
    rcases lt_or_lt_iff_ne.mpr (hfull label) with hlt | hgt
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ label, hlt⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ label, hgt⟩)
  rw [← hcover, Finset.sum_union hdisjoint,
    sum_filter_eq_sum_enum _ posEnum hposInjective hposSign hposOnto,
    sum_filter_eq_sum_enum _ negEnum hnegInjective hnegSign hnegOnto]

/-- A negative atom supported on one coordinate axis is a multiple of that
axis's positive atom — primitivity forbids it.  (`hother` says every other
coordinate vanishes; a zero atom fires primitivity at ratio zero.) -/
theorem axisSupported_negAtom_contradiction
    (baseAtom : Fin 6 → Fin 3 → ℝ) (stressCoeff : Fin 6 → ℝ)
    (posEnum negEnum : Fin 3 → Fin 6)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hdiagonal : ∀ posIdx coord, coord ≠ posIdx → baseAtom (posEnum posIdx) coord = 0)
    (hposScaleNe : ∀ axisIdx : Fin 3, baseAtom (posEnum axisIdx) axisIdx ≠ 0)
    (hprimitive : ∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel)
    (negIdx axisIdx : Fin 3)
    (hother : ∀ coord, coord ≠ axisIdx → baseAtom (negEnum negIdx) coord = 0) : False := by
  have hsideNe : posEnum axisIdx ≠ negEnum negIdx := by
    intro heq
    have hpos := hposSign axisIdx
    rw [heq] at hpos
    exact absurd hpos (asymm (hnegSign negIdx))
  refine hprimitive (posEnum axisIdx) (negEnum negIdx)
    (baseAtom (negEnum negIdx) axisIdx / baseAtom (posEnum axisIdx) axisIdx) hsideNe ?_
  funext coord
  by_cases hcoord : coord = axisIdx
  · subst hcoord
    rw [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ (hposScaleNe coord)]
  · rw [hother coord hcoord, Pi.smul_apply, smul_eq_mul,
      hdiagonal axisIdx coord hcoord, mul_zero]

/-- A negative atom with all three off-diagonal products zero is supported on
one axis — impossible in the diagonal gauge. -/
theorem offdiagZero_negAtom_contradiction
    (baseAtom : Fin 6 → Fin 3 → ℝ) (stressCoeff : Fin 6 → ℝ)
    (posEnum negEnum : Fin 3 → Fin 6)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hdiagonal : ∀ posIdx coord, coord ≠ posIdx → baseAtom (posEnum posIdx) coord = 0)
    (hposScaleNe : ∀ axisIdx : Fin 3, baseAtom (posEnum axisIdx) axisIdx ≠ 0)
    (hprimitive : ∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel)
    (negIdx : Fin 3)
    (hzero01 : baseAtom (negEnum negIdx) 0 * baseAtom (negEnum negIdx) 1 = 0)
    (hzero02 : baseAtom (negEnum negIdx) 0 * baseAtom (negEnum negIdx) 2 = 0)
    (hzero12 : baseAtom (negEnum negIdx) 1 * baseAtom (negEnum negIdx) 2 = 0) : False := by
  by_cases hcoordZero : baseAtom (negEnum negIdx) 0 = 0
  · by_cases hcoordOne : baseAtom (negEnum negIdx) 1 = 0
    · refine axisSupported_negAtom_contradiction baseAtom stressCoeff posEnum negEnum
        hposSign hnegSign hdiagonal hposScaleNe hprimitive negIdx 2 fun coord hcoord => ?_
      fin_cases coord
      · exact hcoordZero
      · exact hcoordOne
      · exact absurd rfl hcoord
    · have hcoordTwo : baseAtom (negEnum negIdx) 2 = 0 :=
        (mul_eq_zero.mp hzero12).resolve_left hcoordOne
      refine axisSupported_negAtom_contradiction baseAtom stressCoeff posEnum negEnum
        hposSign hnegSign hdiagonal hposScaleNe hprimitive negIdx 1 fun coord hcoord => ?_
      fin_cases coord
      · exact hcoordZero
      · exact absurd rfl hcoord
      · exact hcoordTwo
  · have hcoordOne : baseAtom (negEnum negIdx) 1 = 0 :=
      (mul_eq_zero.mp hzero01).resolve_left hcoordZero
    have hcoordTwo : baseAtom (negEnum negIdx) 2 = 0 :=
      (mul_eq_zero.mp hzero02).resolve_left hcoordZero
    refine axisSupported_negAtom_contradiction baseAtom stressCoeff posEnum negEnum
      hposSign hnegSign hdiagonal hposScaleNe hprimitive negIdx 0 fun coord hcoord => ?_
    fin_cases coord
    · exact absurd rfl hcoord
    · exact hcoordOne
    · exact hcoordTwo

/-- Three negative atoms cannot all vanish at one coordinate: the negative
resolution's diagonal entry there would read `0 = 1`. -/
theorem commonVanishedCoord_contradiction
    (baseAtom : Fin 6 → Fin 3 → ℝ) (stressCoeff : Fin 6 → ℝ) (negEnum : Fin 3 → Fin 6)
    (hnegSide : ∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1)
    (coordIdx : Fin 3)
    (hzeroAll : ∀ negIdx : Fin 3, baseAtom (negEnum negIdx) coordIdx = 0) : False := by
  have hentry := entry_of_atomCombination hnegSide coordIdx coordIdx
  rw [Matrix.one_apply_eq, Fin.sum_univ_three, hzeroAll 0, hzeroAll 1, hzeroAll 2] at hentry
  norm_num at hentry

/-- Two negative atoms with proportional off-diagonal patterns, all products of
the second one nonzero, are parallel — primitivity forbids it. -/
theorem proportionalOffdiag_negPair_contradiction
    (baseAtom : Fin 6 → Fin 3 → ℝ) (negEnum : Fin 3 → Fin 6)
    (hnegInjective : Function.Injective negEnum)
    (hprimitive : ∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel)
    (firstNegIdx secondNegIdx : Fin 3) (hdistinct : firstNegIdx ≠ secondNegIdx)
    (scaleFirst scaleSecond : ℝ)
    (hscaleFirstNe : scaleFirst ≠ 0) (hscaleSecondNe : scaleSecond ≠ 0)
    (hrelation01 : scaleFirst
          * (baseAtom (negEnum firstNegIdx) 0 * baseAtom (negEnum firstNegIdx) 1)
        + scaleSecond
          * (baseAtom (negEnum secondNegIdx) 0 * baseAtom (negEnum secondNegIdx) 1) = 0)
    (hrelation02 : scaleFirst
          * (baseAtom (negEnum firstNegIdx) 0 * baseAtom (negEnum firstNegIdx) 2)
        + scaleSecond
          * (baseAtom (negEnum secondNegIdx) 0 * baseAtom (negEnum secondNegIdx) 2) = 0)
    (hrelation12 : scaleFirst
          * (baseAtom (negEnum firstNegIdx) 1 * baseAtom (negEnum firstNegIdx) 2)
        + scaleSecond
          * (baseAtom (negEnum secondNegIdx) 1 * baseAtom (negEnum secondNegIdx) 2) = 0)
    (hproduct01 : baseAtom (negEnum secondNegIdx) 0 * baseAtom (negEnum secondNegIdx) 1 ≠ 0)
    (hproduct02 : baseAtom (negEnum secondNegIdx) 0 * baseAtom (negEnum secondNegIdx) 2 ≠ 0) :
    False := by
  have hsecondZero : baseAtom (negEnum secondNegIdx) 0 ≠ 0 := left_ne_zero_of_mul hproduct01
  have hsecondOne : baseAtom (negEnum secondNegIdx) 1 ≠ 0 := right_ne_zero_of_mul hproduct01
  have hsecondTwo : baseAtom (negEnum secondNegIdx) 2 ≠ 0 := right_ne_zero_of_mul hproduct02
  have hfirstProduct01 : baseAtom (negEnum firstNegIdx) 0
      * baseAtom (negEnum firstNegIdx) 1 ≠ 0 := by
    intro hvanish
    rw [hvanish, mul_zero, zero_add] at hrelation01
    exact (mul_ne_zero hscaleSecondNe hproduct01) hrelation01
  have hfirstProduct02 : baseAtom (negEnum firstNegIdx) 0
      * baseAtom (negEnum firstNegIdx) 2 ≠ 0 := by
    intro hvanish
    rw [hvanish, mul_zero, zero_add] at hrelation02
    exact (mul_ne_zero hscaleSecondNe hproduct02) hrelation02
  have hfirstZero : baseAtom (negEnum firstNegIdx) 0 ≠ 0 :=
    left_ne_zero_of_mul hfirstProduct01
  have hfirstOne : baseAtom (negEnum firstNegIdx) 1 ≠ 0 :=
    right_ne_zero_of_mul hfirstProduct01
  have hfirstTwo : baseAtom (negEnum firstNegIdx) 2 ≠ 0 :=
    right_ne_zero_of_mul hfirstProduct02
  have hminor01 : baseAtom (negEnum firstNegIdx) 0 * baseAtom (negEnum secondNegIdx) 1
      = baseAtom (negEnum firstNegIdx) 1 * baseAtom (negEnum secondNegIdx) 0 := by
    have hcancel : (scaleFirst
          * (baseAtom (negEnum firstNegIdx) 2 * baseAtom (negEnum secondNegIdx) 2))
          * (baseAtom (negEnum firstNegIdx) 0 * baseAtom (negEnum secondNegIdx) 1)
        = (scaleFirst
          * (baseAtom (negEnum firstNegIdx) 2 * baseAtom (negEnum secondNegIdx) 2))
          * (baseAtom (negEnum firstNegIdx) 1 * baseAtom (negEnum secondNegIdx) 0) := by
      linear_combination (baseAtom (negEnum secondNegIdx) 2
          * baseAtom (negEnum secondNegIdx) 1) * hrelation02
        - (baseAtom (negEnum secondNegIdx) 2 * baseAtom (negEnum secondNegIdx) 0)
          * hrelation12
    exact mul_left_cancel₀
      (mul_ne_zero hscaleFirstNe (mul_ne_zero hfirstTwo hsecondTwo)) hcancel
  have hminor02 : baseAtom (negEnum firstNegIdx) 0 * baseAtom (negEnum secondNegIdx) 2
      = baseAtom (negEnum firstNegIdx) 2 * baseAtom (negEnum secondNegIdx) 0 := by
    have hcancel : (scaleFirst
          * (baseAtom (negEnum firstNegIdx) 1 * baseAtom (negEnum secondNegIdx) 1))
          * (baseAtom (negEnum firstNegIdx) 0 * baseAtom (negEnum secondNegIdx) 2)
        = (scaleFirst
          * (baseAtom (negEnum firstNegIdx) 1 * baseAtom (negEnum secondNegIdx) 1))
          * (baseAtom (negEnum firstNegIdx) 2 * baseAtom (negEnum secondNegIdx) 0) := by
      linear_combination (baseAtom (negEnum secondNegIdx) 1
          * baseAtom (negEnum secondNegIdx) 2) * hrelation01
        - (baseAtom (negEnum secondNegIdx) 1 * baseAtom (negEnum secondNegIdx) 0)
          * hrelation12
    exact mul_left_cancel₀
      (mul_ne_zero hscaleFirstNe (mul_ne_zero hfirstOne hsecondOne)) hcancel
  have hcoordZeroEq : baseAtom (negEnum firstNegIdx) 0
      = (baseAtom (negEnum firstNegIdx) 0 / baseAtom (negEnum secondNegIdx) 0)
        * baseAtom (negEnum secondNegIdx) 0 := by
    rw [div_mul_cancel₀ _ hsecondZero]
  have hcoordOneEq : baseAtom (negEnum firstNegIdx) 1
      = (baseAtom (negEnum firstNegIdx) 0 / baseAtom (negEnum secondNegIdx) 0)
        * baseAtom (negEnum secondNegIdx) 1 := by
    rw [div_mul_eq_mul_div, eq_div_iff hsecondZero]
    linarith [hminor01]
  have hcoordTwoEq : baseAtom (negEnum firstNegIdx) 2
      = (baseAtom (negEnum firstNegIdx) 0 / baseAtom (negEnum secondNegIdx) 0)
        * baseAtom (negEnum secondNegIdx) 2 := by
    rw [div_mul_eq_mul_div, eq_div_iff hsecondZero]
    linarith [hminor02]
  refine hprimitive (negEnum secondNegIdx) (negEnum firstNegIdx)
    (baseAtom (negEnum firstNegIdx) 0 / baseAtom (negEnum secondNegIdx) 0)
    (fun heq => hdistinct (hnegInjective heq).symm) ?_
  funext coord
  rw [Pi.smul_apply, smul_eq_mul]
  fin_cases coord
  · exact hcoordZeroEq
  · exact hcoordOneEq
  · exact hcoordTwoEq

/-- **THE WALK-BOTTOM IS STRESS-FREE (proportionality form).**  In the diagonal
gauge EVERY dependence of the six atom matrices is a scalar multiple of the
stress: the dependence space is exactly one line.  Off-diagonal entries see
only the negative side (the positive side is axis-aligned), so a transverse
dependence direction would align the three negative off-diagonal patterns on
one line — and every alignment shape dies: an all-nonzero common pattern makes
two negative atoms parallel (primitivity), a one-slot pattern forces a common
vanished coordinate (contradicting the negative resolution's diagonal), a zero
pattern makes a negative atom axis-supported (parallel to a positive atom). -/
theorem diagonalGauge_dependence_proportional
    (baseAtom : Fin 6 → Fin 3 → ℝ) (stressCoeff : Fin 6 → ℝ)
    (posEnum negEnum : Fin 3 → Fin 6)
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (hposInjective : Function.Injective posEnum)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hposOnto : ∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label)
    (hnegInjective : Function.Injective negEnum)
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hnegOnto : ∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label)
    (hdiagonal : ∀ posIdx coord, coord ≠ posIdx → baseAtom (posEnum posIdx) coord = 0)
    (hposSide : ∑ posIdx, stressCoeff (posEnum posIdx)
      • atomMatrix (baseAtom (posEnum posIdx)) = 1)
    (hnegSide : ∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1)
    (hprimitive : ∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel)
    (dep : Fin 6 → ℝ)
    (hdep : ∑ label, dep label • atomMatrix (baseAtom label) = 0) :
    ∃ ratio : ℝ, ∀ label, dep label = ratio * stressCoeff label := by
  classical
  -- the axis scales are nonzero: the positive resolution's diagonal is one
  have hposDiagonalUnit : ∀ axisIdx : Fin 3, stressCoeff (posEnum axisIdx)
      * (baseAtom (posEnum axisIdx) axisIdx * baseAtom (posEnum axisIdx) axisIdx) = 1 := by
    intro axisIdx
    have hentry := entry_of_atomCombination hposSide axisIdx axisIdx
    rw [Matrix.one_apply_eq] at hentry
    have hsingle : ∑ posIdx : Fin 3, stressCoeff (posEnum posIdx)
        * (baseAtom (posEnum posIdx) axisIdx * baseAtom (posEnum posIdx) axisIdx)
        = stressCoeff (posEnum axisIdx)
          * (baseAtom (posEnum axisIdx) axisIdx * baseAtom (posEnum axisIdx) axisIdx) := by
      refine Finset.sum_eq_single axisIdx (fun otherIdx _ hne => ?_)
        (fun habsurd => absurd (Finset.mem_univ axisIdx) habsurd)
      rw [hdiagonal otherIdx axisIdx (Ne.symm hne)]
      ring
    rw [← hsingle]
    exact hentry
  have hposScaleNe : ∀ axisIdx : Fin 3, baseAtom (posEnum axisIdx) axisIdx ≠ 0 := by
    intro axisIdx hzero
    have hunit := hposDiagonalUnit axisIdx
    rw [hzero] at hunit
    norm_num at hunit
  -- the two-sided resolutions make the coefficients a stress
  have hbaseStress : ∑ label, stressCoeff label • atomMatrix (baseAtom label) = 0 :=
    stress_of_twoSidedResolutions baseAtom stressCoeff posEnum negEnum hfull
      hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hposSide hnegSide
  -- off-diagonal entries of any dependence see only the negative side
  have hoffdiagNegOnly : ∀ (coefficient : Fin 6 → ℝ),
      (∑ label, coefficient label • atomMatrix (baseAtom label) = 0) →
      ∀ rowIdx colIdx : Fin 3, rowIdx ≠ colIdx →
      coefficient (negEnum 0) * (baseAtom (negEnum 0) rowIdx * baseAtom (negEnum 0) colIdx)
        + coefficient (negEnum 1)
          * (baseAtom (negEnum 1) rowIdx * baseAtom (negEnum 1) colIdx)
        + coefficient (negEnum 2)
          * (baseAtom (negEnum 2) rowIdx * baseAtom (negEnum 2) colIdx) = 0 := by
    intro coefficient hcombination rowIdx colIdx hne
    have hentry := entry_of_atomCombination hcombination rowIdx colIdx
    rw [Matrix.zero_apply] at hentry
    have hsplit := sum_split_by_signEnumerations hfull hposInjective hposSign hposOnto
      hnegInjective hnegSign hnegOnto
      (fun label => coefficient label * (baseAtom label rowIdx * baseAtom label colIdx))
    rw [hsplit] at hentry
    have hposVanish : ∑ posIdx : Fin 3, coefficient (posEnum posIdx)
        * (baseAtom (posEnum posIdx) rowIdx * baseAtom (posEnum posIdx) colIdx) = 0 := by
      refine Finset.sum_eq_zero fun posIdx _ => ?_
      by_cases hrow : rowIdx = posIdx
      · have hcol : colIdx ≠ posIdx := by rw [← hrow]; exact hne.symm
        rw [hdiagonal posIdx colIdx hcol]
        ring
      · rw [hdiagonal posIdx rowIdx hrow]
        ring
    rw [hposVanish, zero_add, Fin.sum_univ_three] at hentry
    exact hentry
  -- the residual dependence, anchored at the first negative label
  set anchorRatio : ℝ := dep (negEnum 0) / stressCoeff (negEnum 0) with hanchorRatioDef
  have hresidualStress : ∑ label, (dep label - anchorRatio * stressCoeff label)
      • atomMatrix (baseAtom label) = 0 := by
    simp only [sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, hdep, ← Finset.smul_sum, hbaseStress, smul_zero, sub_zero]
  have hresidualAnchor : dep (negEnum 0) - anchorRatio * stressCoeff (negEnum 0) = 0 := by
    rw [hanchorRatioDef, div_mul_cancel₀ _ (hfull (negEnum 0)), sub_self]
  have hresidualEq : ∀ rowIdx colIdx : Fin 3, rowIdx ≠ colIdx →
      (dep (negEnum 1) - anchorRatio * stressCoeff (negEnum 1))
          * (baseAtom (negEnum 1) rowIdx * baseAtom (negEnum 1) colIdx)
        + (dep (negEnum 2) - anchorRatio * stressCoeff (negEnum 2))
          * (baseAtom (negEnum 2) rowIdx * baseAtom (negEnum 2) colIdx) = 0 := by
    intro rowIdx colIdx hne
    have hthree := hoffdiagNegOnly (fun label => dep label - anchorRatio * stressCoeff label)
      hresidualStress rowIdx colIdx hne
    rw [hresidualAnchor, zero_mul, zero_add] at hthree
    exact hthree
  have hstressEq : ∀ rowIdx colIdx : Fin 3, rowIdx ≠ colIdx →
      stressCoeff (negEnum 0) * (baseAtom (negEnum 0) rowIdx * baseAtom (negEnum 0) colIdx)
        + stressCoeff (negEnum 1)
          * (baseAtom (negEnum 1) rowIdx * baseAtom (negEnum 1) colIdx)
        + stressCoeff (negEnum 2)
          * (baseAtom (negEnum 2) rowIdx * baseAtom (negEnum 2) colIdx) = 0 :=
    fun rowIdx colIdx hne => hoffdiagNegOnly stressCoeff hbaseStress rowIdx colIdx hne
  -- the central claim: the residual vanishes on the other two negative labels
  have hresidualNegOne : dep (negEnum 1) - anchorRatio * stressCoeff (negEnum 1) = 0 ∧
      dep (negEnum 2) - anchorRatio * stressCoeff (negEnum 2) = 0 := by
    have hE01 := hresidualEq 0 1 (by decide)
    have hE02 := hresidualEq 0 2 (by decide)
    have hE12 := hresidualEq 1 2 (by decide)
    by_cases hresOne : dep (negEnum 1) - anchorRatio * stressCoeff (negEnum 1) = 0
    · refine ⟨hresOne, ?_⟩
      by_cases hresTwo : dep (negEnum 2) - anchorRatio * stressCoeff (negEnum 2) = 0
      · exact hresTwo
      · exfalso
        rw [hresOne, zero_mul, zero_add] at hE01 hE02 hE12
        exact offdiagZero_negAtom_contradiction baseAtom stressCoeff posEnum negEnum
          hposSign hnegSign hdiagonal hposScaleNe hprimitive 2
          ((mul_eq_zero.mp hE01).resolve_left hresTwo)
          ((mul_eq_zero.mp hE02).resolve_left hresTwo)
          ((mul_eq_zero.mp hE12).resolve_left hresTwo)
    · exfalso
      by_cases hresTwo : dep (negEnum 2) - anchorRatio * stressCoeff (negEnum 2) = 0
      · rw [hresTwo, zero_mul, add_zero] at hE01 hE02 hE12
        exact offdiagZero_negAtom_contradiction baseAtom stressCoeff posEnum negEnum
          hposSign hnegSign hdiagonal hposScaleNe hprimitive 1
          ((mul_eq_zero.mp hE01).resolve_left hresOne)
          ((mul_eq_zero.mp hE02).resolve_left hresOne)
          ((mul_eq_zero.mp hE12).resolve_left hresOne)
      · -- both transverse coefficients nonzero: patterns 1 and 2 are
        -- proportional and, through the stress, so is pattern 0
        have hS01 := hstressEq 0 1 (by decide)
        have hS02 := hstressEq 0 2 (by decide)
        have hS12 := hstressEq 1 2 (by decide)
        by_cases hQ01 : baseAtom (negEnum 2) 0 * baseAtom (negEnum 2) 1 = 0
        · by_cases hQ02 : baseAtom (negEnum 2) 0 * baseAtom (negEnum 2) 2 = 0
          · by_cases hQ12 : baseAtom (negEnum 2) 1 * baseAtom (negEnum 2) 2 = 0
            · exact offdiagZero_negAtom_contradiction baseAtom stressCoeff posEnum negEnum
                hposSign hnegSign hdiagonal hposScaleNe hprimitive 2 hQ01 hQ02 hQ12
            · -- pattern lives on the (1,2) slot only: coordinate 0 dies everywhere
              have hu21 : baseAtom (negEnum 2) 1 ≠ 0 := left_ne_zero_of_mul hQ12
              have hu22 : baseAtom (negEnum 2) 2 ≠ 0 := right_ne_zero_of_mul hQ12
              have hu20 : baseAtom (negEnum 2) 0 = 0 :=
                (mul_eq_zero.mp hQ01).resolve_right hu21
              have hP01 : baseAtom (negEnum 1) 0 * baseAtom (negEnum 1) 1 = 0 := by
                rw [hQ01, mul_zero, add_zero] at hE01
                exact (mul_eq_zero.mp hE01).resolve_left hresOne
              have hP02 : baseAtom (negEnum 1) 0 * baseAtom (negEnum 1) 2 = 0 := by
                rw [hQ02, mul_zero, add_zero] at hE02
                exact (mul_eq_zero.mp hE02).resolve_left hresOne
              have hP12ne : baseAtom (negEnum 1) 1 * baseAtom (negEnum 1) 2 ≠ 0 := by
                intro hvanish
                rw [hvanish, mul_zero, zero_add] at hE12
                exact (mul_ne_zero hresTwo hQ12) hE12
              have hu11 : baseAtom (negEnum 1) 1 ≠ 0 := left_ne_zero_of_mul hP12ne
              have hu10 : baseAtom (negEnum 1) 0 = 0 :=
                (mul_eq_zero.mp hP01).resolve_right hu11
              have hR01 : baseAtom (negEnum 0) 0 * baseAtom (negEnum 0) 1 = 0 := by
                rw [hP01, hQ01, mul_zero, mul_zero, add_zero, add_zero] at hS01
                exact (mul_eq_zero.mp hS01).resolve_left (hfull (negEnum 0))
              have hR02 : baseAtom (negEnum 0) 0 * baseAtom (negEnum 0) 2 = 0 := by
                rw [hP02, hQ02, mul_zero, mul_zero, add_zero, add_zero] at hS02
                exact (mul_eq_zero.mp hS02).resolve_left (hfull (negEnum 0))
              by_cases hu00 : baseAtom (negEnum 0) 0 = 0
              · refine commonVanishedCoord_contradiction baseAtom stressCoeff negEnum
                  hnegSide 0 fun negIdx => ?_
                fin_cases negIdx
                · exact hu00
                · exact hu10
                · exact hu20
              · have hu01 : baseAtom (negEnum 0) 1 = 0 :=
                  (mul_eq_zero.mp hR01).resolve_left hu00
                have hu02 : baseAtom (negEnum 0) 2 = 0 :=
                  (mul_eq_zero.mp hR02).resolve_left hu00
                refine axisSupported_negAtom_contradiction baseAtom stressCoeff posEnum
                  negEnum hposSign hnegSign hdiagonal hposScaleNe hprimitive 0 0
                  fun coord hcoord => ?_
                fin_cases coord
                · exact absurd rfl hcoord
                · exact hu01
                · exact hu02
          · by_cases hQ12 : baseAtom (negEnum 2) 1 * baseAtom (negEnum 2) 2 = 0
            · -- pattern lives on the (0,2) slot only: coordinate 1 dies everywhere
              have hu20 : baseAtom (negEnum 2) 0 ≠ 0 := left_ne_zero_of_mul hQ02
              have hu22 : baseAtom (negEnum 2) 2 ≠ 0 := right_ne_zero_of_mul hQ02
              have hu21 : baseAtom (negEnum 2) 1 = 0 :=
                (mul_eq_zero.mp hQ01).resolve_left hu20
              have hP01 : baseAtom (negEnum 1) 0 * baseAtom (negEnum 1) 1 = 0 := by
                rw [hQ01, mul_zero, add_zero] at hE01
                exact (mul_eq_zero.mp hE01).resolve_left hresOne
              have hP12 : baseAtom (negEnum 1) 1 * baseAtom (negEnum 1) 2 = 0 := by
                rw [hQ12, mul_zero, add_zero] at hE12
                exact (mul_eq_zero.mp hE12).resolve_left hresOne
              have hP02ne : baseAtom (negEnum 1) 0 * baseAtom (negEnum 1) 2 ≠ 0 := by
                intro hvanish
                rw [hvanish, mul_zero, zero_add] at hE02
                exact (mul_ne_zero hresTwo hQ02) hE02
              have hu10 : baseAtom (negEnum 1) 0 ≠ 0 := left_ne_zero_of_mul hP02ne
              have hu11 : baseAtom (negEnum 1) 1 = 0 :=
                (mul_eq_zero.mp hP01).resolve_left hu10
              have hR01 : baseAtom (negEnum 0) 0 * baseAtom (negEnum 0) 1 = 0 := by
                rw [hP01, hQ01, mul_zero, mul_zero, add_zero, add_zero] at hS01
                exact (mul_eq_zero.mp hS01).resolve_left (hfull (negEnum 0))
              have hR12 : baseAtom (negEnum 0) 1 * baseAtom (negEnum 0) 2 = 0 := by
                rw [hP12, hQ12, mul_zero, mul_zero, add_zero, add_zero] at hS12
                exact (mul_eq_zero.mp hS12).resolve_left (hfull (negEnum 0))
              by_cases hu01 : baseAtom (negEnum 0) 1 = 0
              · refine commonVanishedCoord_contradiction baseAtom stressCoeff negEnum
                  hnegSide 1 fun negIdx => ?_
                fin_cases negIdx
                · exact hu01
                · exact hu11
                · exact hu21
              · have hu00 : baseAtom (negEnum 0) 0 = 0 :=
                  (mul_eq_zero.mp hR01).resolve_right hu01
                have hu02 : baseAtom (negEnum 0) 2 = 0 :=
                  (mul_eq_zero.mp hR12).resolve_left hu01
                refine axisSupported_negAtom_contradiction baseAtom stressCoeff posEnum
                  negEnum hposSign hnegSign hdiagonal hposScaleNe hprimitive 0 1
                  fun coord hcoord => ?_
                fin_cases coord
                · exact hu00
                · exact absurd rfl hcoord
                · exact hu02
            · -- two slots alive forces the third alive on one atom
              have hu20 : baseAtom (negEnum 2) 0 ≠ 0 := left_ne_zero_of_mul hQ02
              have hu22 : baseAtom (negEnum 2) 2 ≠ 0 := right_ne_zero_of_mul hQ02
              have hu21 : baseAtom (negEnum 2) 1 ≠ 0 := left_ne_zero_of_mul hQ12
              exact (mul_ne_zero hu20 hu21) hQ01
        · by_cases hQ02 : baseAtom (negEnum 2) 0 * baseAtom (negEnum 2) 2 = 0
          · by_cases hQ12 : baseAtom (negEnum 2) 1 * baseAtom (negEnum 2) 2 = 0
            · -- pattern lives on the (0,1) slot only: coordinate 2 dies everywhere
              have hu20 : baseAtom (negEnum 2) 0 ≠ 0 := left_ne_zero_of_mul hQ01
              have hu21 : baseAtom (negEnum 2) 1 ≠ 0 := right_ne_zero_of_mul hQ01
              have hu22 : baseAtom (negEnum 2) 2 = 0 :=
                (mul_eq_zero.mp hQ02).resolve_left hu20
              have hP02 : baseAtom (negEnum 1) 0 * baseAtom (negEnum 1) 2 = 0 := by
                rw [hQ02, mul_zero, add_zero] at hE02
                exact (mul_eq_zero.mp hE02).resolve_left hresOne
              have hP12 : baseAtom (negEnum 1) 1 * baseAtom (negEnum 1) 2 = 0 := by
                rw [hQ12, mul_zero, add_zero] at hE12
                exact (mul_eq_zero.mp hE12).resolve_left hresOne
              have hP01ne : baseAtom (negEnum 1) 0 * baseAtom (negEnum 1) 1 ≠ 0 := by
                intro hvanish
                rw [hvanish, mul_zero, zero_add] at hE01
                exact (mul_ne_zero hresTwo hQ01) hE01
              have hu10 : baseAtom (negEnum 1) 0 ≠ 0 := left_ne_zero_of_mul hP01ne
              have hu12 : baseAtom (negEnum 1) 2 = 0 :=
                (mul_eq_zero.mp hP02).resolve_left hu10
              have hR02 : baseAtom (negEnum 0) 0 * baseAtom (negEnum 0) 2 = 0 := by
                rw [hP02, hQ02, mul_zero, mul_zero, add_zero, add_zero] at hS02
                exact (mul_eq_zero.mp hS02).resolve_left (hfull (negEnum 0))
              have hR12 : baseAtom (negEnum 0) 1 * baseAtom (negEnum 0) 2 = 0 := by
                rw [hP12, hQ12, mul_zero, mul_zero, add_zero, add_zero] at hS12
                exact (mul_eq_zero.mp hS12).resolve_left (hfull (negEnum 0))
              by_cases hu02 : baseAtom (negEnum 0) 2 = 0
              · refine commonVanishedCoord_contradiction baseAtom stressCoeff negEnum
                  hnegSide 2 fun negIdx => ?_
                fin_cases negIdx
                · exact hu02
                · exact hu12
                · exact hu22
              · have hu00 : baseAtom (negEnum 0) 0 = 0 :=
                  (mul_eq_zero.mp hR02).resolve_right hu02
                have hu01 : baseAtom (negEnum 0) 1 = 0 :=
                  (mul_eq_zero.mp hR12).resolve_right hu02
                refine axisSupported_negAtom_contradiction baseAtom stressCoeff posEnum
                  negEnum hposSign hnegSign hdiagonal hposScaleNe hprimitive 0 2
                  fun coord hcoord => ?_
                fin_cases coord
                · exact hu00
                · exact hu01
                · exact absurd rfl hcoord
            · -- two slots alive forces the third alive on one atom
              have hu21 : baseAtom (negEnum 2) 1 ≠ 0 := right_ne_zero_of_mul hQ01
              have hu20 : baseAtom (negEnum 2) 0 ≠ 0 := left_ne_zero_of_mul hQ01
              have hu22 : baseAtom (negEnum 2) 2 ≠ 0 := right_ne_zero_of_mul hQ12
              exact (mul_ne_zero hu20 hu22) hQ02
          · by_cases hQ12 : baseAtom (negEnum 2) 1 * baseAtom (negEnum 2) 2 = 0
            · -- two slots alive forces the third alive on one atom
              have hu21 : baseAtom (negEnum 2) 1 ≠ 0 := right_ne_zero_of_mul hQ01
              have hu22 : baseAtom (negEnum 2) 2 ≠ 0 := right_ne_zero_of_mul hQ02
              exact (mul_ne_zero hu21 hu22) hQ12
            · -- all three slots alive: atoms 1 and 2 are parallel
              exact proportionalOffdiag_negPair_contradiction baseAtom negEnum
                hnegInjective hprimitive 1 2 (by decide) _ _ hresOne hresTwo
                hE01 hE02 hE12 hQ01 hQ02
  -- the positive-side residual coordinates die on the diagonal entries
  have hresidualPos : ∀ axisIdx : Fin 3,
      dep (posEnum axisIdx) - anchorRatio * stressCoeff (posEnum axisIdx) = 0 := by
    intro axisIdx
    have hentry := entry_of_atomCombination hresidualStress axisIdx axisIdx
    rw [Matrix.zero_apply] at hentry
    have hsplit := sum_split_by_signEnumerations hfull hposInjective hposSign hposOnto
      hnegInjective hnegSign hnegOnto
      (fun label => (dep label - anchorRatio * stressCoeff label)
        * (baseAtom label axisIdx * baseAtom label axisIdx))
    rw [hsplit] at hentry
    have hnegVanish : ∑ negIdx : Fin 3, (dep (negEnum negIdx)
        - anchorRatio * stressCoeff (negEnum negIdx))
        * (baseAtom (negEnum negIdx) axisIdx * baseAtom (negEnum negIdx) axisIdx) = 0 := by
      rw [Fin.sum_univ_three, hresidualAnchor, hresidualNegOne.1, hresidualNegOne.2]
      ring
    have hposSingle : ∑ posIdx : Fin 3, (dep (posEnum posIdx)
        - anchorRatio * stressCoeff (posEnum posIdx))
        * (baseAtom (posEnum posIdx) axisIdx * baseAtom (posEnum posIdx) axisIdx)
        = (dep (posEnum axisIdx) - anchorRatio * stressCoeff (posEnum axisIdx))
          * (baseAtom (posEnum axisIdx) axisIdx * baseAtom (posEnum axisIdx) axisIdx) := by
      refine Finset.sum_eq_single axisIdx (fun otherIdx _ hne => ?_)
        (fun habsurd => absurd (Finset.mem_univ axisIdx) habsurd)
      rw [hdiagonal otherIdx axisIdx (Ne.symm hne)]
      ring
    rw [hposSingle, hnegVanish, add_zero] at hentry
    rcases mul_eq_zero.mp hentry with hvanish | hvanish
    · exact hvanish
    · exact absurd (mul_self_eq_zero.mp hvanish) (hposScaleNe axisIdx)
  -- assemble the proportionality over every label
  refine ⟨anchorRatio, fun label => ?_⟩
  rcases lt_or_lt_iff_ne.mpr (hfull label) with hneg | hpos
  · obtain ⟨negIdx, hnegIdx⟩ := hnegOnto label hneg
    have hres : dep (negEnum negIdx) - anchorRatio * stressCoeff (negEnum negIdx) = 0 := by
      fin_cases negIdx
      · exact hresidualAnchor
      · exact hresidualNegOne.1
      · exact hresidualNegOne.2
    rw [← hnegIdx]
    linarith [hres]
  · obtain ⟨posIdx, hposIdx⟩ := hposOnto label hpos
    have hres := hresidualPos posIdx
    rw [← hposIdx]
    linarith [hres]

/-- **THE WALK-BOTTOM IS STRESS-FREE.**  A dependence of the six atom matrices
vanishing at ANY single label vanishes identically: dropping one atom leaves
five INDEPENDENT atom matrices.  In particular the five-atom family left
behind at the endpoint (the vanished atom removed) carries no stress of its
own — the boundary's (5,3) object is stress-free, kernel-checked. -/
theorem diagonalGauge_dependence_eq_zero_of_vanishes
    (baseAtom : Fin 6 → Fin 3 → ℝ) (stressCoeff : Fin 6 → ℝ)
    (posEnum negEnum : Fin 3 → Fin 6)
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (hposInjective : Function.Injective posEnum)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hposOnto : ∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label)
    (hnegInjective : Function.Injective negEnum)
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hnegOnto : ∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label)
    (hdiagonal : ∀ posIdx coord, coord ≠ posIdx → baseAtom (posEnum posIdx) coord = 0)
    (hposSide : ∑ posIdx, stressCoeff (posEnum posIdx)
      • atomMatrix (baseAtom (posEnum posIdx)) = 1)
    (hnegSide : ∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1)
    (hprimitive : ∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel)
    (dep : Fin 6 → ℝ)
    (hdep : ∑ label, dep label • atomMatrix (baseAtom label) = 0)
    (vanishedLabel : Fin 6) (hvanish : dep vanishedLabel = 0) :
    ∀ label, dep label = 0 := by
  obtain ⟨ratio, hratio⟩ := diagonalGauge_dependence_proportional baseAtom stressCoeff
    posEnum negEnum hfull hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto
    hdiagonal hposSide hnegSide hprimitive dep hdep
  have hratioZero : ratio = 0 := by
    have hanchor := hratio vanishedLabel
    rw [hvanish] at hanchor
    rcases mul_eq_zero.mp hanchor.symm with hzero | hzero
    · exact hzero
    · exact absurd hzero (hfull vanishedLabel)
  intro label
  rw [hratio label, hratioZero, zero_mul]

/-! ## Layer 2: the vanished-count split of the endpoint

At the endpoint one, two, or all three positive-side weights are zero.  The
all-three stratum is a THEOREM; the other two are the named residuals, each
handed the walk-bottom rigidity of layer 1 as a free hypothesis. -/

/-- A probe orthogonal to all three negative atoms is zero: they resolve the
identity. -/
theorem probe_eq_zero_of_negSide_orthogonal
    (baseAtom : Fin 6 → Fin 3 → ℝ) (stressCoeff : Fin 6 → ℝ) (negEnum : Fin 3 → Fin 6)
    (hnegSide : ∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1)
    (probe : Fin 3 → ℝ)
    (horthogonal : ∀ negIdx, baseAtom (negEnum negIdx) ⬝ᵥ probe = 0) : probe = 0 := by
  have hform := weighted_atomForm_eq_on Finset.univ
    (fun negIdx => -stressCoeff (negEnum negIdx))
    (fun negIdx => baseAtom (negEnum negIdx)) probe
  rw [hnegSide, Matrix.one_mulVec] at hform
  have hzero : probe ⬝ᵥ probe = 0 := by
    rw [hform]
    exact Finset.sum_eq_zero fun negIdx _ => by rw [horthogonal negIdx]; ring
  exact dotProduct_self_eq_zero.mp hzero

/-- The gap of a selected subset against the weighted Gram is symmetric. -/
theorem isHermitian_selectedSub_weightedGram (baseAtom : Fin 6 → Fin 3 → ℝ)
    (selected : Finset (Fin 6)) (weight : Fin 6 → ℝ) :
    ((∑ label ∈ selected, atomMatrix (baseAtom label))
      - ∑ label, weight label • atomMatrix (baseAtom label)).IsHermitian := by
  have hleft : (∑ label ∈ selected, atomMatrix (baseAtom label))ᵀ
      = ∑ label ∈ selected, atomMatrix (baseAtom label) := by
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun label _ =>
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (baseAtom label)).1
  have hright : (∑ label, weight label • atomMatrix (baseAtom label))ᵀ
      = ∑ label, weight label • atomMatrix (baseAtom label) := by
    rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (baseAtom label)).1]
  exact isHermitian_of_transpose_eq (by rw [Matrix.transpose_sub, hleft, hright])

/-- **THE ALL-VANISHED STRATUM IS A THEOREM.**  When every positive-side weight
has been walked to zero the negative triple strictly dominates: the gap form is
`sum (1 - t_j) u_j u_j^T` with every coefficient positive and the `u_j`
resolving the identity. -/
theorem exists_posDef_of_threeVanished
    (baseAtom : Fin 6 → Fin 3 → ℝ) (weight stressCoeff : Fin 6 → ℝ)
    (posEnum negEnum : Fin 3 → Fin 6)
    (hweightSumOne : ∑ label, weight label = 1)
    (hweightNegSide : ∀ label, stressCoeff label < 0 → 0 < weight label)
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (hposInjective : Function.Injective posEnum)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hposOnto : ∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label)
    (hnegInjective : Function.Injective negEnum)
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hnegOnto : ∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label)
    (hnegSide : ∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1)
    (hallVanished : ∀ posIdx, weight (posEnum posIdx) = 0) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ ((∑ label ∈ selected, atomMatrix (baseAtom label))
          - ∑ label, weight label • atomMatrix (baseAtom label)).PosDef := by
  classical
  have hnegWeightSum : ∑ negIdx : Fin 3, weight (negEnum negIdx) = 1 := by
    have hsplit := sum_split_by_signEnumerations hfull hposInjective hposSign hposOnto
      hnegInjective hnegSign hnegOnto weight
    rw [hweightSumOne] at hsplit
    have hposZero : ∑ posIdx : Fin 3, weight (posEnum posIdx) = 0 :=
      Finset.sum_eq_zero fun posIdx _ => hallVanished posIdx
    rw [hposZero, zero_add] at hsplit
    exact hsplit.symm
  have hnegWeightLt : ∀ negIdx : Fin 3, weight (negEnum negIdx) < 1 := by
    have hexpand : weight (negEnum 0) + weight (negEnum 1) + weight (negEnum 2) = 1 := by
      rw [← Fin.sum_univ_three (fun negIdx => weight (negEnum negIdx))]
      exact hnegWeightSum
    have hposFirst := hweightNegSide _ (hnegSign 0)
    have hposSecond := hweightNegSide _ (hnegSign 1)
    have hposThird := hweightNegSide _ (hnegSign 2)
    have hltFirst : weight (negEnum 0) < 1 := by linarith
    have hltSecond : weight (negEnum 1) < 1 := by linarith
    have hltThird : weight (negEnum 2) < 1 := by linarith
    intro negIdx
    fin_cases negIdx
    · exact hltFirst
    · exact hltSecond
    · exact hltThird
  refine ⟨Finset.univ.image negEnum, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hnegInjective, Finset.card_univ, Fintype.card_fin]
  · refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_selectedSub_weightedGram baseAtom _ weight, fun probe hprobe => ?_⟩
    rw [star_trivial]
    have hgapForm : probe ⬝ᵥ (((∑ label ∈ Finset.univ.image negEnum,
          atomMatrix (baseAtom label))
        - ∑ label, weight label • atomMatrix (baseAtom label)) *ᵥ probe)
        = ∑ negIdx : Fin 3, (1 - weight (negEnum negIdx))
            * (baseAtom (negEnum negIdx) ⬝ᵥ probe) ^ 2 := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
      have honeSmul : ∑ label ∈ Finset.univ.image negEnum, atomMatrix (baseAtom label)
          = ∑ label ∈ Finset.univ.image negEnum,
              (1 : ℝ) • atomMatrix (baseAtom label) := by
        simp only [one_smul]
      have hselForm := weighted_atomForm_eq_on (Finset.univ.image negEnum)
        (fun _ => (1 : ℝ)) baseAtom probe
      have hgramForm := weighted_atomForm_eq_on Finset.univ weight baseAtom probe
      rw [honeSmul, hselForm, hgramForm,
        Finset.sum_image (fun leftIdx _ rightIdx _ hEq => hnegInjective hEq)]
      have hgramSplit := sum_split_by_signEnumerations hfull hposInjective hposSign
        hposOnto hnegInjective hnegSign hnegOnto
        (fun label => weight label * (baseAtom label ⬝ᵥ probe) ^ 2)
      rw [hgramSplit]
      have hposZero : ∑ posIdx : Fin 3, weight (posEnum posIdx)
          * (baseAtom (posEnum posIdx) ⬝ᵥ probe) ^ 2 = 0 :=
        Finset.sum_eq_zero fun posIdx _ => by rw [hallVanished posIdx]; ring
      rw [hposZero, zero_add, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
      ring
    rw [hgapForm]
    have hterms : ∀ negIdx ∈ (Finset.univ : Finset (Fin 3)),
        0 ≤ (1 - weight (negEnum negIdx)) * (baseAtom (negEnum negIdx) ⬝ᵥ probe) ^ 2 :=
      fun negIdx _ =>
        mul_nonneg (by linarith [hnegWeightLt negIdx]) (sq_nonneg _)
    have hwitness : ∃ negIdx ∈ (Finset.univ : Finset (Fin 3)),
        0 < (1 - weight (negEnum negIdx)) * (baseAtom (negEnum negIdx) ⬝ᵥ probe) ^ 2 := by
      by_contra hnone
      push Not at hnone
      refine hprobe (probe_eq_zero_of_negSide_orthogonal baseAtom stressCoeff negEnum
        hnegSide probe fun negIdx => ?_)
      have hle := hnone negIdx (Finset.mem_univ negIdx)
      have hcoeff : 0 < 1 - weight (negEnum negIdx) := by linarith [hnegWeightLt negIdx]
      have hsq : (baseAtom (negEnum negIdx) ⬝ᵥ probe) ^ 2 ≤ 0 := by nlinarith [hle, hcoeff]
      exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
    exact Finset.sum_pos' hterms hwitness

/-- **The one-vanished residual: the generic (5,3)-type boundary.**  Exactly
one positive-side weight is zero; the five-atom bottom is handed as
INDEPENDENT (the layer-1 rigidity, packaged as the final hypothesis). -/
def OneVanishedRigidBottomDominationSixThree : Prop :=
  ∀ (baseAtom : Fin 6 → Fin 3 → ℝ) (weight stressCoeff : Fin 6 → ℝ)
    (posEnum negEnum : Fin 3 → Fin 6) (vanishedIdx : Fin 3),
    (∀ label, 0 ≤ weight label) → (∑ label, weight label = 1) →
    (∀ label, stressCoeff label < 0 → 0 < weight label) →
    weight (posEnum vanishedIdx) = 0 →
    (∀ otherIdx, otherIdx ≠ vanishedIdx → 0 < weight (posEnum otherIdx)) →
    (∀ label, stressCoeff label ≠ 0) →
    Function.Injective posEnum →
    (∀ posIdx, 0 < stressCoeff (posEnum posIdx)) →
    (∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label) →
    Function.Injective negEnum →
    (∀ negIdx, stressCoeff (negEnum negIdx) < 0) →
    (∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label) →
    (∀ posIdx coord, coord ≠ posIdx → baseAtom (posEnum posIdx) coord = 0) →
    (∑ posIdx, stressCoeff (posEnum posIdx)
      • atomMatrix (baseAtom (posEnum posIdx)) = 1) →
    (∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1) →
    ((∑ label, stressCoeff label) = 0) →
    (∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel) →
    (∀ dep : Fin 6 → ℝ, dep (posEnum vanishedIdx) = 0 →
      (∑ label, dep label • atomMatrix (baseAtom label)) = 0 → ∀ label, dep label = 0) →
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ ((∑ label ∈ selected, atomMatrix (baseAtom label))
          - ∑ label, weight label • atomMatrix (baseAtom label)).PosDef

/-- **The two-vanished residual: the (4,3)-type boundary.**  Two positive-side
weights are zero; the four-atom bottom (one axis atom, three negative atoms)
is where the explicit (4,3) total-tie family lives, so this stratum's
inequality must be exact on that family.  Rigidity rides along as before. -/
def TwoVanishedRigidBottomDominationSixThree : Prop :=
  ∀ (baseAtom : Fin 6 → Fin 3 → ℝ) (weight stressCoeff : Fin 6 → ℝ)
    (posEnum negEnum : Fin 3 → Fin 6) (firstVanishedIdx secondVanishedIdx : Fin 3),
    firstVanishedIdx ≠ secondVanishedIdx →
    (∀ label, 0 ≤ weight label) → (∑ label, weight label = 1) →
    (∀ label, stressCoeff label < 0 → 0 < weight label) →
    weight (posEnum firstVanishedIdx) = 0 →
    weight (posEnum secondVanishedIdx) = 0 →
    (∀ otherIdx, otherIdx ≠ firstVanishedIdx → otherIdx ≠ secondVanishedIdx →
      0 < weight (posEnum otherIdx)) →
    (∀ label, stressCoeff label ≠ 0) →
    Function.Injective posEnum →
    (∀ posIdx, 0 < stressCoeff (posEnum posIdx)) →
    (∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label) →
    Function.Injective negEnum →
    (∀ negIdx, stressCoeff (negEnum negIdx) < 0) →
    (∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label) →
    (∀ posIdx coord, coord ≠ posIdx → baseAtom (posEnum posIdx) coord = 0) →
    (∑ posIdx, stressCoeff (posEnum posIdx)
      • atomMatrix (baseAtom (posEnum posIdx)) = 1) →
    (∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1) →
    ((∑ label, stressCoeff label) = 0) →
    (∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel) →
    (∀ dep : Fin 6 → ℝ, dep (posEnum firstVanishedIdx) = 0 →
      (∑ label, dep label • atomMatrix (baseAtom label)) = 0 → ∀ label, dep label = 0) →
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ ((∑ label ∈ selected, atomMatrix (baseAtom label))
          - ∑ label, weight label • atomMatrix (baseAtom label)).PosDef

/-- **THE VANISHED-COUNT DISPATCH.**  The endpoint statement follows from the
two named residuals: rigidity is supplied by layer 1, the all-vanished
stratum is discharged outright, and the zero pattern of the three positive
weights routes every configuration to its residual. -/
theorem diagonalEndpointGauge_of_vanishedCases
    (honeVanished : OneVanishedRigidBottomDominationSixThree)
    (htwoVanished : TwoVanishedRigidBottomDominationSixThree) :
    DiagonalEndpointZeroSumFrameDominationSixThree := by
  intro baseAtom weight stressCoeff posEnum negEnum hweightNonneg hweightSumOne
    hweightNegSide hexistsVanished hfull hposInjective hposSign hposOnto
    hnegInjective hnegSign hnegOnto hdiagonal hposSide hnegSide hzeroSum hprimitive
  have hrigid : ∀ (anchorIdx : Fin 3) (dep : Fin 6 → ℝ), dep (posEnum anchorIdx) = 0 →
      (∑ label, dep label • atomMatrix (baseAtom label)) = 0 → ∀ label, dep label = 0 :=
    fun anchorIdx dep hvanish hdep =>
      diagonalGauge_dependence_eq_zero_of_vanishes baseAtom stressCoeff posEnum negEnum
        hfull hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hdiagonal
        hposSide hnegSide hprimitive dep hdep (posEnum anchorIdx) hvanish
  by_cases hzeroFirst : weight (posEnum 0) = 0
  · by_cases hzeroSecond : weight (posEnum 1) = 0
    · by_cases hzeroThird : weight (posEnum 2) = 0
      · exact exists_posDef_of_threeVanished baseAtom weight stressCoeff posEnum negEnum
          hweightSumOne hweightNegSide hfull hposInjective hposSign hposOnto
          hnegInjective hnegSign hnegOnto hnegSide
          (fun posIdx => by
            fin_cases posIdx
            · exact hzeroFirst
            · exact hzeroSecond
            · exact hzeroThird)
      · exact htwoVanished baseAtom weight stressCoeff posEnum negEnum 0 1 (by decide)
          hweightNonneg hweightSumOne hweightNegSide hzeroFirst hzeroSecond
          (fun otherIdx hneFirst hneSecond => by
            fin_cases otherIdx
            · exact absurd rfl hneFirst
            · exact absurd rfl hneSecond
            · exact lt_of_le_of_ne (hweightNonneg _) (Ne.symm hzeroThird))
          hfull hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto
          hdiagonal hposSide hnegSide hzeroSum hprimitive (hrigid 0)
    · by_cases hzeroThird : weight (posEnum 2) = 0
      · exact htwoVanished baseAtom weight stressCoeff posEnum negEnum 0 2 (by decide)
          hweightNonneg hweightSumOne hweightNegSide hzeroFirst hzeroThird
          (fun otherIdx hneFirst hneThird => by
            fin_cases otherIdx
            · exact absurd rfl hneFirst
            · exact lt_of_le_of_ne (hweightNonneg _) (Ne.symm hzeroSecond)
            · exact absurd rfl hneThird)
          hfull hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto
          hdiagonal hposSide hnegSide hzeroSum hprimitive (hrigid 0)
      · exact honeVanished baseAtom weight stressCoeff posEnum negEnum 0
          hweightNonneg hweightSumOne hweightNegSide hzeroFirst
          (fun otherIdx hne => by
            fin_cases otherIdx
            · exact absurd rfl hne
            · exact lt_of_le_of_ne (hweightNonneg _) (Ne.symm hzeroSecond)
            · exact lt_of_le_of_ne (hweightNonneg _) (Ne.symm hzeroThird))
          hfull hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto
          hdiagonal hposSide hnegSide hzeroSum hprimitive (hrigid 0)
  · by_cases hzeroSecond : weight (posEnum 1) = 0
    · by_cases hzeroThird : weight (posEnum 2) = 0
      · exact htwoVanished baseAtom weight stressCoeff posEnum negEnum 1 2 (by decide)
          hweightNonneg hweightSumOne hweightNegSide hzeroSecond hzeroThird
          (fun otherIdx hneSecond hneThird => by
            fin_cases otherIdx
            · exact lt_of_le_of_ne (hweightNonneg _) (Ne.symm hzeroFirst)
            · exact absurd rfl hneSecond
            · exact absurd rfl hneThird)
          hfull hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto
          hdiagonal hposSide hnegSide hzeroSum hprimitive (hrigid 1)
      · exact honeVanished baseAtom weight stressCoeff posEnum negEnum 1
          hweightNonneg hweightSumOne hweightNegSide hzeroSecond
          (fun otherIdx hne => by
            fin_cases otherIdx
            · exact lt_of_le_of_ne (hweightNonneg _) (Ne.symm hzeroFirst)
            · exact absurd rfl hne
            · exact lt_of_le_of_ne (hweightNonneg _) (Ne.symm hzeroThird))
          hfull hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto
          hdiagonal hposSide hnegSide hzeroSum hprimitive (hrigid 1)
    · by_cases hzeroThird : weight (posEnum 2) = 0
      · exact honeVanished baseAtom weight stressCoeff posEnum negEnum 2
          hweightNonneg hweightSumOne hweightNegSide hzeroThird
          (fun otherIdx hne => by
            fin_cases otherIdx
            · exact lt_of_le_of_ne (hweightNonneg _) (Ne.symm hzeroFirst)
            · exact lt_of_le_of_ne (hweightNonneg _) (Ne.symm hzeroSecond)
            · exact absurd rfl hne)
          hfull hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto
          hdiagonal hposSide hnegSide hzeroSum hprimitive (hrigid 2)
      · exfalso
        obtain ⟨vanishedIdx, hvanishedIdx⟩ := hexistsVanished
        fin_cases vanishedIdx
        · exact hzeroFirst hvanishedIdx
        · exact hzeroSecond hvanishedIdx
        · exact hzeroThird hvanishedIdx

/-- Branch (ii) from the two bottom residuals. -/
theorem balancedStratumSelection_six_of_vanishedCases
    (honeVanished : OneVanishedRigidBottomDominationSixThree)
    (htwoVanished : TwoVanishedRigidBottomDominationSixThree) :
    BalancedStratumSelection 6 :=
  balancedStratumSelection_six_of_diagonalEndpointGauge
    (diagonalEndpointGauge_of_vanishedCases honeVanished htwoVanished)

/-- Rank-3 GTZ from the two bottom residuals and the stress-free hinge. -/
theorem forall_gtzOriginal_rank_three_of_vanishedCases_and_stressFreeHinge
    (honeVanished : OneVanishedRigidBottomDominationSixThree)
    (htwoVanished : TwoVanishedRigidBottomDominationSixThree)
    (hstressFreeHinge : StressFreeHingeHoldsSixThree) :
    ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  forall_gtzOriginal_rank_three_of_diagonalEndpointGauge_and_stressFreeHinge
    (diagonalEndpointGauge_of_vanishedCases honeVanished htwoVanished) hstressFreeHinge

/-! ## Layer 3: the diamond cannot be the walk-bottom

The landed Theorem A (`Gtz.diamondExtension_no_fullSupport_stress`) says NO
six-atom extension of a diamond-shape five-family carries a full-support
stress.  The endpoint data carries one, so no relabeling of the six endpoint
atoms puts a diamond in the first five slots — the one known primitive (5,3)
tie is structurally excluded from every walk-bottom. -/

/-- The diamond-shape data of `Gtz.diamondExtension_stress_support` on slots
`0..4`, bundled: two coplanar three-circuits `{0,1,2}` and `{0,3,4}` with
distinct planes and independent off-plane pairs. -/
def RealizesDiamondShape (atomFamily : Fin 6 → Fin 3 → ℝ)
    (planeNormalOne planeNormalTwo : Fin 3 → ℝ) : Prop :=
  atomFamily 0 ⬝ᵥ planeNormalOne = 0 ∧ atomFamily 1 ⬝ᵥ planeNormalOne = 0
    ∧ atomFamily 2 ⬝ᵥ planeNormalOne = 0 ∧ atomFamily 0 ⬝ᵥ planeNormalTwo = 0
    ∧ atomFamily 3 ⬝ᵥ planeNormalTwo = 0 ∧ atomFamily 4 ⬝ᵥ planeNormalTwo = 0
    ∧ atomFamily 3 ⬝ᵥ planeNormalOne ≠ 0 ∧ atomFamily 4 ⬝ᵥ planeNormalOne ≠ 0
    ∧ atomFamily 1 ⬝ᵥ planeNormalTwo ≠ 0 ∧ atomFamily 2 ⬝ᵥ planeNormalTwo ≠ 0
    ∧ (∀ firstScale secondScale : ℝ,
        firstScale • atomFamily 3 + secondScale • atomFamily 4 = 0 →
        firstScale = 0 ∧ secondScale = 0)
    ∧ (∀ firstScale secondScale : ℝ,
        firstScale • atomFamily 1 + secondScale • atomFamily 2 = 0 →
        firstScale = 0 ∧ secondScale = 0)

/-- A family with a full-support stress realizes the diamond shape under NO
relabeling: the stress rides through the permutation and Theorem A fires. -/
theorem no_diamondShape_of_fullSupport_stress (atomFamily : Fin 6 → Fin 3 → ℝ)
    (stressCoeff : Fin 6 → ℝ)
    (hstress : ∑ label, stressCoeff label • atomMatrix (atomFamily label) = 0)
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (relabel : Equiv.Perm (Fin 6)) (planeNormalOne planeNormalTwo : Fin 3 → ℝ) :
    ¬ RealizesDiamondShape (fun slot => atomFamily (relabel slot))
      planeNormalOne planeNormalTwo := by
  rintro ⟨hsharedOne, hfirstOne, hsecondOne, hsharedTwo, hthirdTwo, hfourthTwo,
    hthirdOffOne, hfourthOffOne, hfirstOffTwo, hsecondOffTwo, hpairTwoIndep, hpairOneIndep⟩
  have hpermStress : ∑ slot, stressCoeff (relabel slot)
      • atomMatrix (atomFamily (relabel slot)) = 0 := by
    rw [Equiv.sum_comp relabel
      (fun label => stressCoeff label • atomMatrix (atomFamily label))]
    exact hstress
  exact diamondExtension_no_fullSupport_stress (fun slot => atomFamily (relabel slot))
    planeNormalOne planeNormalTwo hsharedOne hfirstOne hsecondOne hsharedTwo hthirdTwo
    hfourthTwo hthirdOffOne hfourthOffOne hfirstOffTwo hsecondOffTwo
    hpairTwoIndep hpairOneIndep hpermStress (fun slot => hfull (relabel slot))

/-- **THE DIAMOND CANNOT BE THE WALK-BOTTOM.**  The endpoint-gauge resolutions
manufacture the full-support stress, so no five of the six boundary atoms
realize the diamond shape under any relabeling.  Any (5,3) tie obstructing the
one-vanished residual must therefore be a NEW, non-diamond primitive tie. -/
theorem no_relabeled_diamondShape_of_endpointGauge
    (baseAtom : Fin 6 → Fin 3 → ℝ) (stressCoeff : Fin 6 → ℝ)
    (posEnum negEnum : Fin 3 → Fin 6)
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (hposInjective : Function.Injective posEnum)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hposOnto : ∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label)
    (hnegInjective : Function.Injective negEnum)
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hnegOnto : ∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label)
    (hposSide : ∑ posIdx, stressCoeff (posEnum posIdx)
      • atomMatrix (baseAtom (posEnum posIdx)) = 1)
    (hnegSide : ∑ negIdx, (-stressCoeff (negEnum negIdx))
      • atomMatrix (baseAtom (negEnum negIdx)) = 1) :
    ∀ (relabel : Equiv.Perm (Fin 6)) (planeNormalOne planeNormalTwo : Fin 3 → ℝ),
      ¬ RealizesDiamondShape (fun slot => baseAtom (relabel slot))
        planeNormalOne planeNormalTwo :=
  fun relabel planeNormalOne planeNormalTwo =>
    no_diamondShape_of_fullSupport_stress baseAtom stressCoeff
      (stress_of_twoSidedResolutions baseAtom stressCoeff posEnum negEnum hfull
        hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hposSide hnegSide)
      hfull relabel planeNormalOne planeNormalTwo

/-! ## Layer 4: the (5,3) isolation

The one-vanished stratum whitens to a genuine `WeightedDesign 5 3` — the
BOTTOM — plus one weightless SPIKE direction carrying the sixth stress
coefficient.  `SpikedStressFreeBottomDominationFiveThree` is the boundary
statement in that gauge; its tie-exclusion sharpening implies it through the
landed small-size weighted GTZ. -/

/-- **The spiked stress-free (5,3) bottom statement.**  A primitive weighted
(5,3) design with INDEPENDENT atom matrices, a spike direction of positive
stress coefficient closing a zero-sum full-support dependence: then either a
bottom triple dominates strictly, or a spike pair does.  This is the
one-vanished boundary of branch (ii), whitened. -/
def SpikedStressFreeBottomDominationFiveThree : Prop :=
  ∀ (bottomDesign : WeightedDesign 5 3) (spikeDirection : Fin 3 → ℝ)
    (bottomCoeff : Fin 5 → ℝ) (spikeCoeff : ℝ),
    ((∑ bottomIdx, bottomCoeff bottomIdx • atomMatrix (bottomDesign.atom bottomIdx))
        + spikeCoeff • atomMatrix spikeDirection = 0) →
    (∀ bottomIdx, bottomCoeff bottomIdx ≠ 0) →
    0 < spikeCoeff →
    ((∑ bottomIdx, bottomCoeff bottomIdx) + spikeCoeff = 0) →
    IsPrimitiveDesign bottomDesign →
    (∀ (bottomIdx : Fin 5) (ratio : ℝ),
      spikeDirection ≠ ratio • bottomDesign.atom bottomIdx) →
    (∀ (bottomIdx : Fin 5) (ratio : ℝ),
      bottomDesign.atom bottomIdx ≠ ratio • spikeDirection) →
    (∀ dep : Fin 5 → ℝ,
      (∑ bottomIdx, dep bottomIdx • atomMatrix (bottomDesign.atom bottomIdx)) = 0 →
      ∀ bottomIdx, dep bottomIdx = 0) →
    (∃ bottomTriple : Finset (Fin 5), bottomTriple.card = 3
        ∧ (subsetSum bottomDesign bottomTriple - 1).PosDef)
    ∨ (∃ bottomPair : Finset (Fin 5), bottomPair.card = 2
        ∧ (atomMatrix spikeDirection
            + (∑ bottomIdx ∈ bottomPair, atomMatrix (bottomDesign.atom bottomIdx))
            - 1).PosDef)

/-- **The (5,3) TIE EXCLUSION under the spike.**  The sharpest one-premise
residual of the one-vanished stratum: the bottom design of a spiked
configuration is never an exact tie.  The diamond — the only known primitive
(5,3) tie — is already excluded (`no_relabeled_diamondShape_of_endpointGauge`);
a counterexample must be a NEW primitive stress-free (5,3) tie admitting a
spike with full-support zero-sum dependence. -/
def EndpointBottomTieExclusionFiveThree : Prop :=
  ∀ (bottomDesign : WeightedDesign 5 3) (spikeDirection : Fin 3 → ℝ)
    (bottomCoeff : Fin 5 → ℝ) (spikeCoeff : ℝ),
    ((∑ bottomIdx, bottomCoeff bottomIdx • atomMatrix (bottomDesign.atom bottomIdx))
        + spikeCoeff • atomMatrix spikeDirection = 0) →
    (∀ bottomIdx, bottomCoeff bottomIdx ≠ 0) →
    0 < spikeCoeff →
    ((∑ bottomIdx, bottomCoeff bottomIdx) + spikeCoeff = 0) →
    IsPrimitiveDesign bottomDesign →
    (∀ (bottomIdx : Fin 5) (ratio : ℝ),
      spikeDirection ≠ ratio • bottomDesign.atom bottomIdx) →
    (∀ (bottomIdx : Fin 5) (ratio : ℝ),
      bottomDesign.atom bottomIdx ≠ ratio • spikeDirection) →
    (∀ dep : Fin 5 → ℝ,
      (∑ bottomIdx, dep bottomIdx • atomMatrix (bottomDesign.atom bottomIdx)) = 0 →
      ∀ bottomIdx, dep bottomIdx = 0) →
    ¬ IsTie bottomDesign

/-- **Tie exclusion closes the spiked bottom through landed (5,3) GTZ.**  The
bottom design always has a WEAKLY dominating triple
(`Gtz.gtzWeighted_of_le_five`); if it is not a tie, some bottom triple
dominates STRICTLY — the spike lane is not even needed. -/
theorem spikedBottomDomination_of_tieExclusion
    (hexclusion : EndpointBottomTieExclusionFiveThree) :
    SpikedStressFreeBottomDominationFiveThree := by
  intro bottomDesign spikeDirection bottomCoeff spikeCoeff hstress hfullBottom hspikePos
    hzeroSum hprimitive hspikeNotBottom hbottomNotSpike hbottomFree
  left
  obtain ⟨candidate, hcard, hdominates⟩ :=
    gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num) bottomDesign
  by_contra hnone
  push Not at hnone
  exact hexclusion bottomDesign spikeDirection bottomCoeff spikeCoeff hstress hfullBottom
    hspikePos hzeroSum hprimitive hspikeNotBottom hbottomNotSpike hbottomFree
    ⟨⟨candidate, hcard, hdominates⟩, hnone⟩

/-- **THE (5,3) TRANSPORT.**  The one-vanished residual follows from the spiked
bottom statement: whiten by the weighted Gram (positive definite because the
negative side resolves the identity), enumerate the five surviving labels,
carry the stress, the zero sum, primitivity, and — through the layer-1
rigidity — the INDEPENDENCE of the bottom atoms, then pull the dominating
triple or the spike pair back through the congruence. -/
theorem oneVanished_of_spikedBottomDomination
    (hspiked : SpikedStressFreeBottomDominationFiveThree) :
    OneVanishedRigidBottomDominationSixThree := by
  intro baseAtom weight stressCoeff posEnum negEnum vanishedIdx hweightNonneg
    hweightSumOne hweightNegSide hvanishedZero hothersPos hfull hposInjective hposSign
    hposOnto hnegInjective hnegSign hnegOnto hdiagonal hposSide hnegSide hzeroSum
    hprimitive hrigid
  classical
  -- the weighted Gram is positive definite
  set gram : Matrix (Fin 3) (Fin 3) ℝ := ∑ label, weight label • atomMatrix (baseAtom label)
    with hgramDef
  have hgramSymm : gramᵀ = gram := by
    rw [hgramDef, Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (baseAtom label)).1]
  have hgramEntrySymm : ∀ leftIdx rightIdx : Fin 3,
      gram leftIdx rightIdx = gram rightIdx leftIdx := by
    intro leftIdx rightIdx
    have hflip := congrFun (congrFun hgramSymm rightIdx) leftIdx
    rwa [Matrix.transpose_apply] at hflip
  have hgramPosDef : gram.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hgramSymm, fun probe hprobe => ?_⟩
    rw [star_trivial, hgramDef]
    have hgramForm := weighted_atomForm_eq_on Finset.univ weight baseAtom probe
    rw [hgramForm]
    have hterms : ∀ label ∈ (Finset.univ : Finset (Fin 6)),
        0 ≤ weight label * (baseAtom label ⬝ᵥ probe) ^ 2 :=
      fun label _ => mul_nonneg (hweightNonneg label) (sq_nonneg _)
    have hwitness : ∃ label ∈ (Finset.univ : Finset (Fin 6)),
        0 < weight label * (baseAtom label ⬝ᵥ probe) ^ 2 := by
      by_contra hnone
      push Not at hnone
      refine hprobe (probe_eq_zero_of_negSide_orthogonal baseAtom stressCoeff negEnum
        hnegSide probe fun negIdx => ?_)
      have hle := hnone (negEnum negIdx) (Finset.mem_univ _)
      have hweightPos := hweightNegSide _ (hnegSign negIdx)
      have hsq : (baseAtom (negEnum negIdx) ⬝ᵥ probe) ^ 2 ≤ 0 := by
        nlinarith [hle, hweightPos]
      exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
    exact Finset.sum_pos' hterms hwitness
  -- the whitener of the Gram
  have hwhitenerDetNe : (whitenMatrix gram).det ≠ 0 :=
    whitenMatrix_det_ne_zero hgramPosDef (hgramEntrySymm 0 1) (hgramEntrySymm 0 2)
      (hgramEntrySymm 1 2)
  have hsandwich : whitenMatrix gram * gram * (whitenMatrix gram)ᵀ = 1 :=
    sandwich_eq_one
      (cholOf_mul_transpose hgramPosDef (hgramEntrySymm 0 1) (hgramEntrySymm 0 2)
        (hgramEntrySymm 1 2))
      (whitenMatrix_mul_cholOf hgramPosDef (hgramEntrySymm 0 1) (hgramEntrySymm 0 2)
        (hgramEntrySymm 1 2))
  have hunitWhitener : IsUnit (whitenMatrix gram).det := isUnit_iff_ne_zero.mpr hwhitenerDetNe
  have hunitTranspose : IsUnit ((whitenMatrix gram)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact hunitWhitener
  -- the five surviving labels, enumerated
  have hbottomCard : (Finset.univ.erase (posEnum vanishedIdx)).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  set bottomEnum : Fin 5 → Fin 6 := fun bottomIdx =>
    (((Finset.univ.erase (posEnum vanishedIdx)).orderIsoOfFin hbottomCard) bottomIdx : Fin 6)
    with hbottomEnumDef
  have hbottomMem : ∀ bottomIdx,
      bottomEnum bottomIdx ∈ Finset.univ.erase (posEnum vanishedIdx) := by
    intro bottomIdx
    rw [hbottomEnumDef]
    exact (((Finset.univ.erase (posEnum vanishedIdx)).orderIsoOfFin hbottomCard)
      bottomIdx).2
  have hbottomNe : ∀ bottomIdx, bottomEnum bottomIdx ≠ posEnum vanishedIdx :=
    fun bottomIdx => (Finset.mem_erase.mp (hbottomMem bottomIdx)).1
  have hbottomInjective : Function.Injective bottomEnum := by
    intro leftIdx rightIdx hEq
    rw [hbottomEnumDef] at hEq
    exact ((Finset.univ.erase (posEnum vanishedIdx)).orderIsoOfFin hbottomCard).injective
      (Subtype.ext hEq)
  have hbottomOnto : ∀ label, label ≠ posEnum vanishedIdx →
      ∃ bottomIdx, bottomEnum bottomIdx = label := by
    intro label hne
    obtain ⟨bottomIdx, hidx⟩ :=
      ((Finset.univ.erase (posEnum vanishedIdx)).orderIsoOfFin hbottomCard).surjective
        ⟨label, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩⟩
    refine ⟨bottomIdx, ?_⟩
    rw [hbottomEnumDef]
    exact congrArg Subtype.val hidx
  -- every six-label sum splits off the vanished label
  have hsumSplit : ∀ (carrier : Type) [AddCommMonoid carrier] (summand : Fin 6 → carrier),
      ∑ label, summand label
        = summand (posEnum vanishedIdx) + ∑ bottomIdx, summand (bottomEnum bottomIdx) := by
    intro carrier _ summand
    rw [← Finset.add_sum_erase Finset.univ summand (Finset.mem_univ (posEnum vanishedIdx))]
    congr 1
    rw [← Finset.filter_ne']
    exact sum_filter_eq_sum_enum _ bottomEnum hbottomInjective hbottomNe hbottomOnto summand
  -- the bottom weights are a probability vector
  have hbottomWeightPos : ∀ bottomIdx, 0 < weight (bottomEnum bottomIdx) := by
    intro bottomIdx
    rcases lt_or_lt_iff_ne.mpr (hfull (bottomEnum bottomIdx)) with hneg | hpos
    · exact hweightNegSide _ hneg
    · obtain ⟨posIdx, hposIdx⟩ := hposOnto _ hpos
      have hposNe : posIdx ≠ vanishedIdx := by
        intro hEq
        rw [hEq] at hposIdx
        exact hbottomNe bottomIdx hposIdx.symm
      rw [← hposIdx]
      exact hothersPos posIdx hposNe
  have hbottomWeightSum : ∑ bottomIdx, weight (bottomEnum bottomIdx) = 1 := by
    have hsplit := hsumSplit ℝ weight
    rw [hvanishedZero, zero_add] at hsplit
    rw [← hsplit]
    exact hweightSumOne
  -- the whitened bottom is Parseval
  have hsandwichExpanded : whitenMatrix gram
      * (∑ label, weight label • atomMatrix (baseAtom label))
      * (whitenMatrix gram)ᵀ = 1 := by
    rw [← hgramDef]
    exact hsandwich
  have hwhitenedParseval : ∑ label, weight label
      • atomMatrix (whitenMatrix gram *ᵥ baseAtom label) = 1 :=
    whitened_sum_parseval Finset.univ weight baseAtom hsandwichExpanded
  have hbottomParseval : ∑ bottomIdx, weight (bottomEnum bottomIdx)
      • atomMatrix (whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx)) = 1 := by
    have hsplit := hsumSplit (Matrix (Fin 3) (Fin 3) ℝ)
      (fun label => weight label • atomMatrix (whitenMatrix gram *ᵥ baseAtom label))
    rw [hvanishedZero, zero_smul, zero_add] at hsplit
    rw [← hsplit]
    exact hwhitenedParseval
  -- the whitened stress, split off the spike
  have hbaseStress : ∑ label, stressCoeff label • atomMatrix (baseAtom label) = 0 :=
    stress_of_twoSidedResolutions baseAtom stressCoeff posEnum negEnum hfull
      hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hposSide hnegSide
  have hwhitenedStress : ∑ label, stressCoeff label
      • atomMatrix (whitenMatrix gram *ᵥ baseAtom label) = 0 := by
    rw [sum_smul_atomMatrix_mulVec_eq_conjugate, hbaseStress, Matrix.mul_zero,
      Matrix.zero_mul]
  have hspikedStress : (∑ bottomIdx, stressCoeff (bottomEnum bottomIdx)
        • atomMatrix (whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx)))
      + stressCoeff (posEnum vanishedIdx)
        • atomMatrix (whitenMatrix gram *ᵥ baseAtom (posEnum vanishedIdx)) = 0 := by
    have hsplit := hsumSplit (Matrix (Fin 3) (Fin 3) ℝ)
      (fun label => stressCoeff label • atomMatrix (whitenMatrix gram *ᵥ baseAtom label))
    rw [hwhitenedStress] at hsplit
    rw [add_comm]
    exact hsplit.symm
  -- the zero sum splits off the spike coefficient
  have hzeroSumSplit : (∑ bottomIdx, stressCoeff (bottomEnum bottomIdx))
      + stressCoeff (posEnum vanishedIdx) = 0 := by
    have hsplit := hsumSplit ℝ stressCoeff
    rw [hzeroSum] at hsplit
    linarith [hsplit]
  -- primitivity survives whitening, spike included
  have hbottomPrimitiveRaw : ∀ (keptIdx dropIdx : Fin 5) (ratio : ℝ), keptIdx ≠ dropIdx →
      whitenMatrix gram *ᵥ baseAtom (bottomEnum dropIdx)
        ≠ ratio • (whitenMatrix gram *ᵥ baseAtom (bottomEnum keptIdx)) :=
    fun keptIdx dropIdx ratio hne =>
      mulVec_ne_smul_of_ne_smul hwhitenerDetNe
        (hprimitive (bottomEnum keptIdx) (bottomEnum dropIdx) ratio
          (fun hEq => hne (hbottomInjective hEq)))
  have hspikeNotBottomRaw : ∀ (bottomIdx : Fin 5) (ratio : ℝ),
      whitenMatrix gram *ᵥ baseAtom (posEnum vanishedIdx)
        ≠ ratio • (whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx)) :=
    fun bottomIdx ratio =>
      mulVec_ne_smul_of_ne_smul hwhitenerDetNe
        (hprimitive (bottomEnum bottomIdx) (posEnum vanishedIdx) ratio
          (hbottomNe bottomIdx))
  have hbottomNotSpikeRaw : ∀ (bottomIdx : Fin 5) (ratio : ℝ),
      whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx)
        ≠ ratio • (whitenMatrix gram *ᵥ baseAtom (posEnum vanishedIdx)) :=
    fun bottomIdx ratio =>
      mulVec_ne_smul_of_ne_smul hwhitenerDetNe
        (hprimitive (posEnum vanishedIdx) (bottomEnum bottomIdx) ratio
          (Ne.symm (hbottomNe bottomIdx)))
  -- the layer-1 rigidity gives independence of the whitened bottom atoms
  have hbottomIndependent : ∀ dep : Fin 5 → ℝ,
      (∑ bottomIdx, dep bottomIdx
        • atomMatrix (whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx))) = 0 →
      ∀ bottomIdx, dep bottomIdx = 0 := by
    intro dep hdep
    have hconj : whitenMatrix gram
        * (∑ bottomIdx, dep bottomIdx • atomMatrix (baseAtom (bottomEnum bottomIdx)))
        * (whitenMatrix gram)ᵀ = 0 := by
      rw [sum_smul_atomMatrix_mulVec_eq_conjugate] at hdep
      exact hdep
    have hgapLeft : (∑ bottomIdx, dep bottomIdx
        • atomMatrix (baseAtom (bottomEnum bottomIdx))) * (whitenMatrix gram)ᵀ = 0 := by
      calc (∑ bottomIdx, dep bottomIdx • atomMatrix (baseAtom (bottomEnum bottomIdx)))
            * (whitenMatrix gram)ᵀ
          = ((whitenMatrix gram)⁻¹ * whitenMatrix gram)
            * ((∑ bottomIdx, dep bottomIdx • atomMatrix (baseAtom (bottomEnum bottomIdx)))
              * (whitenMatrix gram)ᵀ) := by
            rw [Matrix.nonsing_inv_mul _ hunitWhitener, Matrix.one_mul]
        _ = (whitenMatrix gram)⁻¹ * (whitenMatrix gram
            * (∑ bottomIdx, dep bottomIdx • atomMatrix (baseAtom (bottomEnum bottomIdx)))
            * (whitenMatrix gram)ᵀ) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = (whitenMatrix gram)⁻¹ * 0 := by rw [hconj]
        _ = 0 := Matrix.mul_zero _
    have hmiddle : ∑ bottomIdx, dep bottomIdx
        • atomMatrix (baseAtom (bottomEnum bottomIdx)) = 0 := by
      calc ∑ bottomIdx, dep bottomIdx • atomMatrix (baseAtom (bottomEnum bottomIdx))
          = (∑ bottomIdx, dep bottomIdx • atomMatrix (baseAtom (bottomEnum bottomIdx)))
            * ((whitenMatrix gram)ᵀ * ((whitenMatrix gram)ᵀ)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ hunitTranspose, Matrix.mul_one]
        _ = ((∑ bottomIdx, dep bottomIdx • atomMatrix (baseAtom (bottomEnum bottomIdx)))
            * (whitenMatrix gram)ᵀ) * ((whitenMatrix gram)ᵀ)⁻¹ := by
            rw [Matrix.mul_assoc]
        _ = 0 * ((whitenMatrix gram)ᵀ)⁻¹ := by rw [hgapLeft]
        _ = 0 := Matrix.zero_mul _
    intro bottomIdx
    have hext := hrigid
      (fun label => ∑ candidateIdx,
        if bottomEnum candidateIdx = label then dep candidateIdx else 0)
      (Finset.sum_eq_zero fun candidateIdx _ => by
        rw [if_neg (hbottomNe candidateIdx)])
      (by
        calc ∑ label, (∑ candidateIdx,
              if bottomEnum candidateIdx = label then dep candidateIdx else 0)
              • atomMatrix (baseAtom label)
            = ∑ label, ∑ candidateIdx,
                (if bottomEnum candidateIdx = label then dep candidateIdx else 0)
                • atomMatrix (baseAtom label) := by
              refine Finset.sum_congr rfl fun label _ => ?_
              rw [Finset.sum_smul]
          _ = ∑ candidateIdx, ∑ label,
                (if bottomEnum candidateIdx = label then dep candidateIdx else 0)
                • atomMatrix (baseAtom label) := Finset.sum_comm
          _ = ∑ candidateIdx, dep candidateIdx
                • atomMatrix (baseAtom (bottomEnum candidateIdx)) := by
              refine Finset.sum_congr rfl fun candidateIdx _ => ?_
              rw [Finset.sum_eq_single (bottomEnum candidateIdx)
                (fun label _ hne => by
                  rw [if_neg (fun hEq => hne hEq.symm), zero_smul])
                (fun habsurd => absurd (Finset.mem_univ _) habsurd), if_pos rfl]
          _ = 0 := hmiddle)
      (bottomEnum bottomIdx)
    rw [Finset.sum_eq_single bottomIdx
      (fun other _ hne => by rw [if_neg (fun hEq => hne (hbottomInjective hEq))])
      (fun habsurd => absurd (Finset.mem_univ _) habsurd), if_pos rfl] at hext
    exact hext
  -- fire the spiked bottom statement
  rcases hspiked
    ⟨fun bottomIdx => whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx),
      fun bottomIdx => weight (bottomEnum bottomIdx), hbottomWeightPos, hbottomWeightSum,
      hbottomParseval⟩
    (whitenMatrix gram *ᵥ baseAtom (posEnum vanishedIdx))
    (fun bottomIdx => stressCoeff (bottomEnum bottomIdx))
    (stressCoeff (posEnum vanishedIdx))
    hspikedStress (fun bottomIdx => hfull _) (hposSign vanishedIdx) hzeroSumSplit
    hbottomPrimitiveRaw hspikeNotBottomRaw hbottomNotSpikeRaw hbottomIndependent
    with ⟨bottomTriple, hcardTriple, hposDefTriple⟩ | ⟨bottomPair, hcardPair, hposDefPair⟩
  · -- a bottom triple dominates: pull it back through the congruence
    have hwhitenedTriple : ((∑ bottomIdx ∈ bottomTriple,
        atomMatrix (whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx))) - 1).PosDef :=
      hposDefTriple
    have hselectedSum : ∑ bottomIdx ∈ bottomTriple,
        atomMatrix (whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx))
        = whitenMatrix gram
          * (∑ bottomIdx ∈ bottomTriple, atomMatrix (baseAtom (bottomEnum bottomIdx)))
          * (whitenMatrix gram)ᵀ := by
      have hstep := sum_smul_atomMatrix_mulVec_eq_conjugate (whitenMatrix gram)
        (fun bottomIdx => baseAtom (bottomEnum bottomIdx)) (fun _ => (1 : ℝ)) bottomTriple
      simpa only [one_smul] using hstep
    have hgapConj : (∑ bottomIdx ∈ bottomTriple,
        atomMatrix (whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx))) - 1
        = ((whitenMatrix gram)ᵀ)ᵀ
          * ((∑ bottomIdx ∈ bottomTriple, atomMatrix (baseAtom (bottomEnum bottomIdx)))
            - gram)
          * (whitenMatrix gram)ᵀ := by
      rw [hselectedSum, ← hsandwich, Matrix.transpose_transpose, Matrix.mul_sub,
        Matrix.sub_mul]
    rw [hgapConj] at hwhitenedTriple
    have hupstairs := (posDef_congruence_iff hunitTranspose).mp hwhitenedTriple
    refine ⟨bottomTriple.image bottomEnum, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hbottomInjective, hcardTriple]
    · rw [Finset.sum_image (fun leftIdx _ rightIdx _ hEq => hbottomInjective hEq)]
      exact hupstairs
  · -- a spike pair dominates: pull it back the same way
    have hwhitenedPair : (atomMatrix (whitenMatrix gram *ᵥ baseAtom (posEnum vanishedIdx))
        + (∑ bottomIdx ∈ bottomPair,
            atomMatrix (whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx)))
        - 1).PosDef := hposDefPair
    have hpairSum : ∑ bottomIdx ∈ bottomPair,
        atomMatrix (whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx))
        = whitenMatrix gram
          * (∑ bottomIdx ∈ bottomPair, atomMatrix (baseAtom (bottomEnum bottomIdx)))
          * (whitenMatrix gram)ᵀ := by
      have hstep := sum_smul_atomMatrix_mulVec_eq_conjugate (whitenMatrix gram)
        (fun bottomIdx => baseAtom (bottomEnum bottomIdx)) (fun _ => (1 : ℝ)) bottomPair
      simpa only [one_smul] using hstep
    have hspikeConj : atomMatrix (whitenMatrix gram *ᵥ baseAtom (posEnum vanishedIdx))
        = whitenMatrix gram * atomMatrix (baseAtom (posEnum vanishedIdx))
          * (whitenMatrix gram)ᵀ :=
      atomMatrix_conj (whitenMatrix gram) (baseAtom (posEnum vanishedIdx))
    have hgapConj : atomMatrix (whitenMatrix gram *ᵥ baseAtom (posEnum vanishedIdx))
        + (∑ bottomIdx ∈ bottomPair,
            atomMatrix (whitenMatrix gram *ᵥ baseAtom (bottomEnum bottomIdx)))
        - 1
        = ((whitenMatrix gram)ᵀ)ᵀ
          * ((atomMatrix (baseAtom (posEnum vanishedIdx))
              + ∑ bottomIdx ∈ bottomPair, atomMatrix (baseAtom (bottomEnum bottomIdx)))
            - gram)
          * (whitenMatrix gram)ᵀ := by
      rw [hspikeConj, hpairSum, ← hsandwich, Matrix.transpose_transpose]
      noncomm_ring
    rw [hgapConj] at hwhitenedPair
    have hupstairs := (posDef_congruence_iff hunitTranspose).mp hwhitenedPair
    have hnotMem : posEnum vanishedIdx ∉ bottomPair.image bottomEnum := by
      intro hmem
      obtain ⟨bottomIdx, -, hEq⟩ := Finset.mem_image.mp hmem
      exact hbottomNe bottomIdx hEq
    refine ⟨insert (posEnum vanishedIdx) (bottomPair.image bottomEnum), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hnotMem,
        Finset.card_image_of_injective _ hbottomInjective, hcardPair]
    · rw [Finset.sum_insert hnotMem,
        Finset.sum_image (fun leftIdx _ rightIdx _ hEq => hbottomInjective hEq)]
      exact hupstairs

/-- **Branch (ii) from the isolated residuals**: the (5,3) spiked bottom
statement and the (4,3)-type two-vanished residual. -/
theorem balancedStratumSelection_six_of_spikedBottom_and_twoVanished
    (hspiked : SpikedStressFreeBottomDominationFiveThree)
    (htwoVanished : TwoVanishedRigidBottomDominationSixThree) :
    BalancedStratumSelection 6 :=
  balancedStratumSelection_six_of_vanishedCases
    (oneVanished_of_spikedBottomDomination hspiked) htwoVanished

/-- **Rank-3 GTZ, endpoint-descended.**  Three premises: the (5,3) TIE
EXCLUSION under the spike, the two-vanished (4,3)-type residual, and the
stress-free hinge. -/
theorem forall_gtzOriginal_rank_three_of_tieExclusion_twoVanished_stressFreeHinge
    (hexclusion : EndpointBottomTieExclusionFiveThree)
    (htwoVanished : TwoVanishedRigidBottomDominationSixThree)
    (hstressFreeHinge : StressFreeHingeHoldsSixThree) :
    ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  forall_gtzOriginal_rank_three_of_vanishedCases_and_stressFreeHinge
    (oneVanished_of_spikedBottomDomination
      (spikedBottomDomination_of_tieExclusion hexclusion))
    htwoVanished hstressFreeHinge

end Gtz
