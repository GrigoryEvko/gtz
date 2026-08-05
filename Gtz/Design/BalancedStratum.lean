/-
# The balanced stratum of the `(6,3)` hinge

The balanced branch of `Gtz.sixThree_stress_trichotomy` is the stratum carrying
a FULL-SUPPORT stress.  There the split law forces exactly three positive and
three negative coefficients, a common middle matrix
`X = sum_{P} z_c A_c = sum_{N} (-z_c) A_c` which is positive definite, and hence
(after whitening) a pair of orthonormal frames.  This file closes the easy
region of that stratum with two independent unconditional certificates and names
what is left.

**The free-minus-bound identity.**  Parseval splits the domination gap of ANY
subset into the selected atoms' unspent weight minus the unselected atoms' spent
weight,
    `S_C - 1 = sum_{c in C} (1 - t_c) A_c  -  sum_{c not in C} t_c A_c`,
with no stress, no size and no rank restriction.  Every certificate below is a
way of dominating the second sum by the first.

**Certificate one, the stress mass gap.**  Rescaling both sums against the
middle matrix compares them through a single quadratic form; the resulting
invariant condition is `max_{c in N} t_c/|z_c| < min_{c in P} (1 - t_c)/z_c`.
On the slice where those ratios are all equal to one constant the criterion
becomes `max_P t_c + max_N t_c < 1`, which six strictly positive weights summing
to one satisfy automatically — so that whole slice is tie-free with no
hypothesis at all.

**Certificate two, the free-mass budget.**  Cauchy-Schwarz in the metric of the
free-mass matrix `Y_C = sum_{c in C} (1 - t_c) A_c` bounds each bound-mass atom
by its own inverse form, giving the trace criterion
    `sum_{c not in C} t_c * g_c^T Y_C^{-1} g_c < 1  ==>  S_C - 1 positive definite`.
It needs no stress at all and holds at every size and rank.  Against the mass
gap it is INCOMPARABLE: the mass gap replaces both sides by scalar multiples of
the middle matrix and therefore sees only the two spectra, while the budget sees
the relative orientation of the two frames but pays a sum where the mass gap
pays a maximum.  Their union is strictly larger than either.

**What is left.**  A primitive balanced configuration escaping both mass-gap
orientations and the budget at all twenty triples is exactly
`BalancedStratumSelection`, and the capstone
`sixThree_hasParallelPair_of_isTie_of_balancedStress` consumes nothing else.
The residual is stated as a positive domination claim and does NOT assume
tightness: a tie admits no strictly dominating triple, so assuming tightness
would make every negative clause free and the obligation would collapse back
onto the goal.
-/
import Gtz.Reduction.StressMassGap
import Gtz.Reduction.HingeFunnel
import Gtz.Design.StratumEmptinessLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Part 1: two weights never exhaust a design -/

/-- **Two distinct weights leave positive mass behind.**  A third label carries
strictly positive weight out of the total one, so no two weights sum to one. -/
theorem weight_add_weight_lt_one (design : WeightedDesign size rank)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hdistinct : firstLabel ≠ secondLabel)
    (hthirdFirst : thirdLabel ≠ firstLabel) (hthirdSecond : thirdLabel ≠ secondLabel) :
    design.weight firstLabel + design.weight secondLabel < 1 := by
  classical
  have hsubset : ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size))
      ⊆ Finset.univ := Finset.subset_univ _
  have hnonneg : ∀ c ∈ Finset.univ,
      c ∉ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)) →
        0 ≤ design.weight c := fun c _ _ => (design.weight_pos c).le
  have hpart : ∑ c ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
      design.weight c ≤ 1 := by
    rw [← design.weight_sum_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have htriple : ∑ c ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
      design.weight c
      = design.weight firstLabel + design.weight secondLabel
        + design.weight thirdLabel := by
    rw [Finset.sum_insert (by simp [hdistinct, Ne.symm hthirdFirst]),
      Finset.sum_insert (by simp [Ne.symm hthirdSecond]), Finset.sum_singleton, add_assoc]
  rw [htriple] at hpart
  have hthirdPos := design.weight_pos thirdLabel
  linarith

/-! ## Part 2: the rigidity law at two independent ceilings -/

/-- **THE RIGIDITY LAW AT TWO CEILINGS.**  On the slice where the free mass of
every positive-side atom and the bound mass of every negative-side atom sit at
the SAME ratio against the stress, the negative side dominates strictly as soon
as the two sides' weight ceilings sum below one.

This is the sharp form of the hypothesis: the criterion driving
`Gtz.posDef_gap_of_stressMassGap` on the flipped stress is
`max_P t_c / (1 - t_c) < min_N (1 - t_c) / t_c`, and since `u / (1 - u)` rises
and `(1 - u) / u` falls, that is literally `ceilingPos + ceilingNeg < 1`.  A
single common ceiling below one half is the special case
`ceilingPos = ceilingNeg`, and it is strictly stronger than needed. -/
theorem posDef_negSide_gap_of_rigidity_of_ceilingSum (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} {ratio : ℝ} (hratioPos : 0 < ratio)
    (hmiddle :
      ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
          (-stressCoeff c) • atomMatrix (design.atom c)
        = ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
            stressCoeff c • atomMatrix (design.atom c))
    (hposDef :
      (∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
          (-stressCoeff c) • atomMatrix (design.atom c)).PosDef)
    (hfull : ∀ c, stressCoeff c ≠ 0)
    (hfreeP : ∀ c, 0 < stressCoeff c → 1 - design.weight c = ratio * stressCoeff c)
    (hboundN : ∀ c, stressCoeff c < 0 → design.weight c = ratio * (-stressCoeff c))
    {ceilingPos ceilingNeg : ℝ}
    (hceilP : ∀ c, 0 < stressCoeff c → design.weight c ≤ ceilingPos)
    (hceilN : ∀ c, stressCoeff c < 0 → design.weight c ≤ ceilingNeg)
    (hceilNegPos : 0 < ceilingNeg) (hceilingSum : ceilingPos + ceilingNeg < 1) :
    (subsetSum design (Finset.univ.filter fun c => stressCoeff c < 0) - 1).PosDef := by
  classical
  have hcoceilPos : (0:ℝ) < 1 - ceilingPos := by linarith
  have hflipFull : ∀ c, (-stressCoeff) c ≠ 0 := fun c => neg_ne_zero.mpr (hfull c)
  have hposFilter : (Finset.univ.filter fun c => 0 < (-stressCoeff) c)
      = Finset.univ.filter fun c => stressCoeff c < 0 := by ext c; simp
  have hnegFilter : (Finset.univ.filter fun c => (-stressCoeff) c < 0)
      = Finset.univ.filter fun c => 0 < stressCoeff c := by ext c; simp
  have main := posDef_gap_of_stressMassGap design (stressCoeff := -stressCoeff)
    (freeFloor := ratio * (1 - ceilingNeg) / ceilingNeg)
    (boundCeiling := ratio * ceilingPos / (1 - ceilingPos))
    (by rw [hposFilter, hnegFilter]; simpa using hmiddle)
    (by rw [hposFilter]; simpa using hposDef)
    hflipFull
    (fun c hc => by
      have hcNeg : stressCoeff c < 0 := by simpa [neg_pos] using hc
      have hceil : design.weight c ≤ ceilingNeg := hceilN c hcNeg
      have hstress : design.weight c = ratio * (-stressCoeff) c := by
        simpa [Pi.neg_apply] using hboundN c hcNeg
      have hkey : (1 - ceilingNeg) * design.weight c / ceilingNeg
          ≤ 1 - design.weight c := by
        rw [div_le_iff₀ hceilNegPos]; nlinarith [hceil]
      calc ratio * (1 - ceilingNeg) / ceilingNeg * (-stressCoeff) c
          = (1 - ceilingNeg) / ceilingNeg * (ratio * (-stressCoeff) c) := by ring
        _ = (1 - ceilingNeg) / ceilingNeg * design.weight c := by rw [← hstress]
        _ = (1 - ceilingNeg) * design.weight c / ceilingNeg := by ring
        _ ≤ 1 - design.weight c := hkey)
    (fun c hc => by
      have hcPos : 0 < stressCoeff c := by simpa [neg_lt_zero] using hc
      have hceil : design.weight c ≤ ceilingPos := hceilP c hcPos
      have hstress : 1 - design.weight c = ratio * (-(-stressCoeff) c) := by
        simpa [Pi.neg_apply] using hfreeP c hcPos
      have hkey : design.weight c
          ≤ ceilingPos * (1 - design.weight c) / (1 - ceilingPos) := by
        rw [le_div_iff₀ hcoceilPos]; nlinarith [hceil]
      calc design.weight c
          ≤ ceilingPos * (1 - design.weight c) / (1 - ceilingPos) := hkey
        _ = ceilingPos / (1 - ceilingPos) * (ratio * (-(-stressCoeff) c)) := by
              rw [← hstress]; ring
        _ = ratio * ceilingPos / (1 - ceilingPos) * (-(-stressCoeff) c) := by ring)
    (by
      rw [div_lt_div_iff₀ hcoceilPos hceilNegPos]
      nlinarith [hratioPos, hceilingSum, hceilNegPos, hcoceilPos])
  rwa [hposFilter] at main

/-! ## Part 3: the equal-ratio slice of `(6,3)` carries no tie, unconditionally -/

/-- **The equal-ratio slice of the balanced stratum is tie-free.**  A `(6,3)`
full-support stress splits `(3,3)`, so the two sides are disjoint and the
positive side retains a label besides its own weight maximiser.  Three strictly
positive weights therefore separate the two maxima from the total, the ceiling
sum lands below one automatically, and the two-ceiling rigidity law fires with
NO hypothesis on the weights.  The strictly dominating negative side contradicts
tightness outright. -/
theorem sixThree_posDef_negSide_of_rigidity (design : WeightedDesign 6 3)
    {stressCoeff : Fin 6 → ℝ} {ratio : ℝ} (hratioPos : 0 < ratio)
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0)
    (hfreeP : ∀ c, 0 < stressCoeff c → 1 - design.weight c = ratio * stressCoeff c)
    (hboundN : ∀ c, stressCoeff c < 0 → design.weight c = ratio * (-stressCoeff c)) :
    (subsetSum design (Finset.univ.filter fun c => stressCoeff c < 0) - 1).PosDef := by
  classical
  have hspan : ∀ probe : Fin 3 → ℝ, (∀ c, design.atom c ⬝ᵥ probe = 0) → probe = 0 :=
    fun probe hprobe => weightedDesign_atoms_span design hprobe
  obtain ⟨hposCard, hnegCard⟩ :=
    sixThree_fullSupport_stress_splits_three_three design.atom hspan hstress hfull
  set posSide := Finset.univ.filter (fun c => 0 < stressCoeff c) with hposSide
  set negSide := Finset.univ.filter (fun c => stressCoeff c < 0) with hnegSide
  have hposNonempty : posSide.Nonempty := Finset.card_pos.mp (by rw [hposCard]; norm_num)
  have hnegNonempty : negSide.Nonempty := Finset.card_pos.mp (by rw [hnegCard]; norm_num)
  obtain ⟨ceilLabelPos, hceilMemPos, hceilMaxPos⟩ :=
    posSide.exists_max_image design.weight hposNonempty
  obtain ⟨ceilLabelNeg, hceilMemNeg, hceilMaxNeg⟩ :=
    negSide.exists_max_image design.weight hnegNonempty
  have hceilPosSign : 0 < stressCoeff ceilLabelPos := (Finset.mem_filter.mp hceilMemPos).2
  have hceilNegSign : stressCoeff ceilLabelNeg < 0 := (Finset.mem_filter.mp hceilMemNeg).2
  have hlabelsDistinct : ceilLabelPos ≠ ceilLabelNeg := by
    intro hEq
    rw [hEq] at hceilPosSign
    exact absurd hceilNegSign (asymm hceilPosSign)
  -- the positive side keeps a third label besides its own maximiser
  have hthirdExists : ∃ thirdLabel ∈ posSide.erase ceilLabelPos, True := by
    refine Finset.card_pos.mp ?_ |>.imp fun _ hmem => ⟨hmem, trivial⟩
    rw [Finset.card_erase_of_mem hceilMemPos, hposCard]
    norm_num
  obtain ⟨thirdLabel, hthirdMem, -⟩ := hthirdExists
  have hthirdPos : thirdLabel ∈ posSide := Finset.mem_of_mem_erase hthirdMem
  have hthirdFirst : thirdLabel ≠ ceilLabelPos := Finset.ne_of_mem_erase hthirdMem
  have hthirdSecond : thirdLabel ≠ ceilLabelNeg := by
    intro hEq
    have hthirdSign : 0 < stressCoeff thirdLabel := (Finset.mem_filter.mp hthirdPos).2
    rw [hEq] at hthirdSign
    exact absurd hceilNegSign (asymm hthirdSign)
  have hceilingSum : design.weight ceilLabelPos + design.weight ceilLabelNeg < 1 :=
    weight_add_weight_lt_one design hlabelsDistinct hthirdFirst hthirdSecond
  have hmiddleForward := posSide_sum_eq_negSide_sum design.atom hstress hfull
  have hposDefPos := posDef_posSide_sum design.atom hspan hstress hfull
  exact posDef_negSide_gap_of_rigidity_of_ceilingSum design hratioPos
    hmiddleForward.symm (hmiddleForward ▸ hposDefPos) hfull hfreeP hboundN
    (fun c hc => hceilMaxPos c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩))
    (fun c hc => hceilMaxNeg c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩))
    (design.weight_pos ceilLabelNeg) hceilingSum

/-! ## Part 4: the domination gap is free mass minus bound mass -/

/-- **THE FREE-MINUS-BOUND SPLIT.**  Parseval turns the domination gap of any
subset into the selected atoms' unspent weight minus the unselected atoms' spent
weight.  No stress, no size and no rank restriction. -/
theorem subsetSum_sub_one_eq_freeMass_sub_boundMass (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    subsetSum design selected - 1
      = (∑ c ∈ selected, (1 - design.weight c) • atomMatrix (design.atom c))
        - ∑ c ∈ selectedᶜ, design.weight c • atomMatrix (design.atom c) := by
  classical
  have hfree : ∑ c ∈ selected, (1 - design.weight c) • atomMatrix (design.atom c)
      = subsetSum design selected
        - ∑ c ∈ selected, design.weight c • atomMatrix (design.atom c) := by
    rw [subsetSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [sub_smul, one_smul]
  have hwhole : (∑ c ∈ selected, design.weight c • atomMatrix (design.atom c))
      + ∑ c ∈ selectedᶜ, design.weight c • atomMatrix (design.atom c)
      = (1 : Matrix (Fin rank) (Fin rank) ℝ) := by
    rw [Finset.sum_add_sum_compl]
    exact design.isParseval
  rw [hfree, ← hwhole]
  abel

/-! ## Part 5: the free-mass budget certificate -/

/-- **Cauchy-Schwarz against a positive definite form.**  Pairing a fixed vector
against a probe is controlled by the vector's inverse form times the probe's
form.  The witness is the solution vector `gramMat⁻¹ *ᵥ source`, and the
inequality is the discriminant of a nonnegative quadratic — no square root. -/
theorem dotProduct_sq_le_inverseForm_mul_form
    {gramMat : Matrix (Fin rank) (Fin rank) ℝ} (hposDef : gramMat.PosDef)
    (source probe : Fin rank → ℝ) :
    (source ⬝ᵥ probe) ^ 2
      ≤ (source ⬝ᵥ (gramMat⁻¹ *ᵥ source)) * (probe ⬝ᵥ (gramMat *ᵥ probe)) := by
  have hdet : IsUnit gramMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have htranspose : gramMatᵀ = gramMat := PosDef.transpose_eq hposDef
  have hformNonneg : ∀ vec : Fin rank → ℝ, 0 ≤ vec ⬝ᵥ (gramMat *ᵥ vec) := by
    intro vec
    have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposDef.posSemidef).2 vec
    rwa [star_trivial] at hstep
  set dual : Fin rank → ℝ := gramMat⁻¹ *ᵥ source with hdual
  have hmulDual : gramMat *ᵥ dual = source := by
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv gramMat hdet,
      Matrix.one_mulVec]
  set inverseForm : ℝ := source ⬝ᵥ (gramMat⁻¹ *ᵥ source) with hinverseForm
  have hdualForm : dual ⬝ᵥ (gramMat *ᵥ dual) = inverseForm := by
    rw [hmulDual, hinverseForm, hdual, dotProduct_comm]
  have hinverseNonneg : 0 ≤ inverseForm := hdualForm ▸ hformNonneg dual
  rcases eq_or_lt_of_le hinverseNonneg with hvanishes | hpositive
  · have hdualZero : dual = 0 := by
      by_contra hne
      have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hne
      rw [star_trivial, hdualForm] at hstep
      exact absurd hvanishes.symm (ne_of_gt hstep)
    have hsourceZero : source = 0 := by
      rw [← hmulDual, hdualZero, Matrix.mulVec_zero]
    simp [hsourceZero, ← hvanishes]
  · set pairing : ℝ := source ⬝ᵥ probe with hpairing
    have hcombination := hformNonneg (inverseForm • probe - pairing • dual)
    have hexpand : (inverseForm • probe - pairing • dual)
        ⬝ᵥ (gramMat *ᵥ (inverseForm • probe - pairing • dual))
        = inverseForm * inverseForm * (probe ⬝ᵥ (gramMat *ᵥ probe))
          - inverseForm * pairing * (probe ⬝ᵥ (gramMat *ᵥ dual))
          - pairing * inverseForm * (dual ⬝ᵥ (gramMat *ᵥ probe))
          + pairing * pairing * (dual ⬝ᵥ (gramMat *ᵥ dual)) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
        sub_dotProduct, smul_dotProduct, smul_dotProduct,
        dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul,
        dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, smul_eq_mul]
      ring
    have hprobeDual : probe ⬝ᵥ (gramMat *ᵥ dual) = pairing := by
      rw [hmulDual, dotProduct_comm, hpairing]
    have hdualProbe : dual ⬝ᵥ (gramMat *ᵥ probe) = pairing := by
      rw [dot_mulVec_comm htranspose dual probe, hmulDual, dotProduct_comm, hpairing]
    rw [hexpand, hprobeDual, hdualProbe, hdualForm] at hcombination
    nlinarith [hcombination, hpositive]

/-- **THE FREE-MASS BUDGET CERTIFICATE.**  If the unselected atoms spend, in
total, less than one unit of the selected atoms' free-mass metric, the selected
subset dominates STRICTLY.

The bound-mass matrix is already a sum of rank-ones, so Cauchy-Schwarz in the
free-mass metric bounds each term by its own inverse form times the probe's
free-mass form; the budget is exactly `trace (Y_C⁻¹ Z_C) < 1`.  Nothing here
mentions a stress, a size or a rank: it is a domination certificate for every
subset of every weighted design. -/
theorem posDef_gap_of_freeMassBudget (design : WeightedDesign size rank)
    (selected : Finset (Fin size))
    (hfreePosDef :
      (∑ c ∈ selected, (1 - design.weight c) • atomMatrix (design.atom c)).PosDef)
    (hbudget :
      ∑ c ∈ selectedᶜ, design.weight c
          * (design.atom c ⬝ᵥ ((∑ d ∈ selected,
              (1 - design.weight d) • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c))
        < 1) :
    (subsetSum design selected - 1).PosDef := by
  classical
  have hsymm : (subsetSum design selected - 1)ᵀ = subsetSum design selected - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, transpose_subsetSum]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  have hfreeForm :
      0 < ∑ c ∈ selected, (1 - design.weight c) * (design.atom c ⬝ᵥ probe) ^ 2 := by
    have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hfreePosDef).2 hprobe
    rwa [star_trivial, atomForm_eq_on_subset] at hstep
  have hbound : ∑ c ∈ selectedᶜ, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      ≤ (∑ c ∈ selectedᶜ, design.weight c
            * (design.atom c ⬝ᵥ ((∑ d ∈ selected,
                (1 - design.weight d) • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c)))
        * ∑ c ∈ selected, (1 - design.weight c) * (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c _ => ?_
    have hcauchy := dotProduct_sq_le_inverseForm_mul_form hfreePosDef
      (design.atom c) probe
    rw [atomForm_eq_on_subset] at hcauchy
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hcauchy (design.weight_pos c).le
  have hmargin : 0 < (1 - ∑ c ∈ selectedᶜ, design.weight c
        * (design.atom c ⬝ᵥ ((∑ d ∈ selected,
            (1 - design.weight d) • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c)))
      * ∑ c ∈ selected, (1 - design.weight c) * (design.atom c ⬝ᵥ probe) ^ 2 :=
    mul_pos (sub_pos.mpr hbudget) hfreeForm
  rw [star_trivial, subsetSum_sub_one_eq_freeMass_sub_boundMass,
    Matrix.sub_mulVec, dotProduct_sub, atomForm_eq_on_subset, atomForm_eq_on_subset]
  nlinarith [hbound, hmargin]

/-! ## Part 6: the two named criteria, the residual, and the capstone -/

/-- **The stress mass gap holds**: the negative side's bound-mass ratios all sit
strictly below the positive side's free-mass ratios, at a common witnessing pair
of levels.  This is the hypothesis pair of `Gtz.posDef_gap_of_stressMassGap`,
packaged so a case split can name its complement. -/
def HasStressMassGap (design : WeightedDesign size rank)
    (stressCoeff : Fin size → ℝ) : Prop :=
  ∃ freeFloor boundCeiling : ℝ,
    (∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - design.weight c)
    ∧ (∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c))
    ∧ boundCeiling < freeFloor

/-- **The free-mass budget holds** for a subset: its free-mass matrix is positive
definite and the complement spends less than one unit in that metric.  This is
the hypothesis pair of `Gtz.posDef_gap_of_freeMassBudget`. -/
def HasFreeMassBudget (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) : Prop :=
  (∑ c ∈ selected, (1 - design.weight c) • atomMatrix (design.atom c)).PosDef
  ∧ ∑ c ∈ selectedᶜ, design.weight c
      * (design.atom c ⬝ᵥ ((∑ d ∈ selected,
          (1 - design.weight d) • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c))
    < 1

/-- Negating a stress is a stress. -/
theorem stress_of_neg_stress {atomCount : ℕ}
    {atomFamily : Fin atomCount → Fin rank → ℝ} {stressCoeff : Fin atomCount → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0) :
    ∑ c, (-stressCoeff) c • atomMatrix (atomFamily c) = 0 := by
  have hpointwise : ∀ c ∈ Finset.univ,
      (-stressCoeff) c • atomMatrix (atomFamily c)
        = -(stressCoeff c • atomMatrix (atomFamily c)) := by
    intro c _
    rw [Pi.neg_apply, neg_smul]
  rw [Finset.sum_congr rfl hpointwise, Finset.sum_neg_distrib, hstress, neg_zero]

/-- The sign filters of a stress and of its negation swap. -/
theorem filter_pos_neg_stress {atomCount : ℕ} (stressCoeff : Fin atomCount → ℝ) :
    (Finset.univ.filter fun c => 0 < (-stressCoeff) c)
      = Finset.univ.filter fun c => stressCoeff c < 0 := by
  ext c; simp

/-- **A balanced `(6,3)` stress with a mass gap produces a strictly dominating
triple.**  The split law makes the positive side a triple, and the trichotomy's
middle-matrix data feeds `Gtz.posDef_gap_of_stressMassGap` directly. -/
theorem sixThree_exists_posDef_triple_of_stressMassGap (design : WeightedDesign 6 3)
    {stressCoeff : Fin 6 → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0)
    (hgap : HasStressMassGap design stressCoeff) :
    ∃ triple : Finset (Fin 6), triple.card = 3
      ∧ (subsetSum design triple - 1).PosDef := by
  classical
  obtain ⟨freeFloor, boundCeiling, hfree, hbound, hstrictGap⟩ := hgap
  have hspan : ∀ probe : Fin 3 → ℝ, (∀ c, design.atom c ⬝ᵥ probe = 0) → probe = 0 :=
    fun probe hprobe => weightedDesign_atoms_span design hprobe
  obtain ⟨hposCard, -⟩ :=
    sixThree_fullSupport_stress_splits_three_three design.atom hspan hstress hfull
  exact ⟨Finset.univ.filter fun c => 0 < stressCoeff c, hposCard,
    posDef_gap_of_stressMassGap design
      (posSide_sum_eq_negSide_sum design.atom hstress hfull)
      (posDef_posSide_sum design.atom hspan hstress hfull)
      hfull hfree hbound hstrictGap⟩

/-- **The named residual of the balanced stratum: the hard cell only.**  A
PRIMITIVE design carrying a full-support stress, for which neither orientation
of the stress mass gap fires and NO triple at all meets the free-mass budget,
still has a strictly dominating triple.

The hypothesis is strictly weaker than the goal.  It is a positive domination
claim on a restricted region and it does NOT assume tightness — assuming
tightness would make the three negative clauses free, since a tie admits no
strictly dominating triple at all and therefore no certificate of any kind can
fire on it.  Every firing region is discharged unconditionally: the mass gap by
`Gtz.sixThree_exists_posDef_triple_of_stressMassGap`, the budget by
`Gtz.posDef_gap_of_freeMassBudget` at each of the twenty triples.  The
equal-ratio slice is excluded outright by
`Gtz.sixThree_posDef_negSide_of_rigidity`, which needs no hypothesis at all.

The budget does NOT cover the residual region: an exact-rational witness
(denominators up to 10^8) exhibits a primitive balanced configuration where no
triple meets the free-mass budget and neither stress mass gap holds, yet seven
triples strictly dominate.  Earlier sampling that suggested full budget
coverage was refuted by that witness.  The hypothesis stands because the budget
is a Cauchy-Schwarz relaxation, not an equivalence: at an exact tie every
budget is at least one, so the cell this names is precisely the tie locus
together with the configurations whose winning triple the relaxation cannot
see. -/
def BalancedStratumSelection (size : ℕ) : Prop :=
  ∀ (design : WeightedDesign size 3) (stressCoeff : Fin size → ℝ),
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0) →
    IsPrimitiveDesign design →
    ¬ HasStressMassGap design stressCoeff →
    ¬ HasStressMassGap design (-stressCoeff) →
    (∀ triple : Finset (Fin size), triple.card = 3 →
      ¬ HasFreeMassBudget design triple) →
    ∃ dominatingTriple : Finset (Fin size), dominatingTriple.card = 3
      ∧ (subsetSum design dominatingTriple - 1).PosDef

/-- **THE BALANCED-STRATUM CAPSTONE, modulo the named selection residual: a
`(6,3)` tie with a full-support stress has a parallel pair.**  Three
unconditional firings are peeled off by case split — the stress mass gap in
each orientation, and the free-mass budget at any of the twenty triples — each
producing a strictly dominating triple that contradicts tightness.  What
survives all three is exactly `BalancedStratumSelection`.

This is the branch-(ii) arm of `Gtz.sixThree_stress_trichotomy`, the sibling of
the branch-(iii) arm `Gtz.sixThree_hasParallelPair_of_isTie_of_coplanarStress`. -/
theorem sixThree_hasParallelPair_of_isTie_of_balancedStress
    (hselection : BalancedStratumSelection 6)
    (design : WeightedDesign 6 3) (htie : IsTie design)
    {stressCoeff : Fin 6 → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) :
    HasParallelPair design := by
  classical
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  have hstressNeg : ∑ c, (-stressCoeff) c • atomMatrix (design.atom c) = 0 :=
    stress_of_neg_stress hstress
  have hfullNeg : ∀ c, (-stressCoeff) c ≠ 0 := fun c => neg_ne_zero.mpr (hfull c)
  by_cases hgapPos : HasStressMassGap design stressCoeff
  · obtain ⟨triple, hcard, hposDef⟩ :=
      sixThree_exists_posDef_triple_of_stressMassGap design hstress hfull hgapPos
    exact htie.2 triple hcard hposDef
  · by_cases hgapNeg : HasStressMassGap design (-stressCoeff)
    · obtain ⟨triple, hcard, hposDef⟩ :=
        sixThree_exists_posDef_triple_of_stressMassGap design hstressNeg hfullNeg hgapNeg
      exact htie.2 triple hcard hposDef
    · by_cases hbudget :
          ∃ triple : Finset (Fin 6), triple.card = 3 ∧ HasFreeMassBudget design triple
      · obtain ⟨triple, hcard, hfree, hspend⟩ := hbudget
        exact htie.2 triple hcard
          (posDef_gap_of_freeMassBudget design triple hfree hspend)
      · push Not at hbudget
        obtain ⟨triple, hcard, hposDef⟩ := hselection design stressCoeff hstress hfull
          hprimitive hgapPos hgapNeg (fun triple hcard => hbudget triple hcard)
        exact htie.2 triple hcard hposDef

/-! ## Part 7: complementary gaps -/

/-- **COMPLEMENTARY GAPS SUM TO ONE FIXED MATRIX.**  Parseval makes the
domination gaps of a subset and of its complement add to the design's
half-spent mass `sum_c (1 - 2 t_c) A_c`, the SAME matrix for every subset. -/
theorem gap_add_complementGap (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    (subsetSum design selected - 1) + (subsetSum design selectedᶜ - 1)
      = ∑ c, (1 - 2 * design.weight c) • atomMatrix (design.atom c) := by
  classical
  have hatoms : subsetSum design selected + subsetSum design selectedᶜ
      = ∑ c, atomMatrix (design.atom c) := by
    rw [subsetSum, subsetSum, Finset.sum_add_sum_compl]
  have hexpand : ∑ c, (1 - 2 * design.weight c) • atomMatrix (design.atom c)
      = (∑ c, atomMatrix (design.atom c))
        - (2 : ℝ) • ∑ c, design.weight c • atomMatrix (design.atom c) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by
      rw [sub_smul, one_smul, smul_smul]
  rw [hexpand, design.isParseval, ← hatoms, two_smul]
  abel

/-- **The half-spent mass is positive definite when no weight reaches one
half.**  Its quadratic form is a positively weighted sum of squared pairings and
the design's atoms span. -/
theorem posDef_halfSpentMass (design : WeightedDesign size rank)
    (hhalf : ∀ c, design.weight c < 1 / 2) :
    (∑ c, (1 - 2 * design.weight c) • atomMatrix (design.atom c)).PosDef := by
  classical
  have hsymm : (∑ c, (1 - 2 * design.weight c) • atomMatrix (design.atom c))ᵀ
      = ∑ c, (1 - 2 * design.weight c) • atomMatrix (design.atom c) := by
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun c _ => by
      rw [Matrix.transpose_smul,
        transpose_eq_of_isHermitian (posSemidef_atomMatrix (design.atom c)).1]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  rw [star_trivial, atomForm_eq_on_subset]
  have hterms : ∀ c ∈ Finset.univ,
      0 ≤ (1 - 2 * design.weight c) * (design.atom c ⬝ᵥ probe) ^ 2 := fun c _ =>
    mul_nonneg (by linarith [hhalf c]) (sq_nonneg _)
  have hwitness : ∃ c ∈ Finset.univ,
      0 < (1 - 2 * design.weight c) * (design.atom c ⬝ᵥ probe) ^ 2 := by
    have hlive : ∃ c, design.atom c ⬝ᵥ probe ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hprobe (weightedDesign_atoms_span design hcon)
    obtain ⟨liveLabel, hlive⟩ := hlive
    exact ⟨liveLabel, Finset.mem_univ liveLabel,
      mul_pos (by linarith [hhalf liveLabel])
        ((sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hlive)))⟩
  exact Finset.sum_pos' hterms hwitness

/-- **THE COMPLEMENTARY DICHOTOMY.**  When no weight reaches one half, a subset
whose gap matrix is negative semidefinite hands strict domination to its
complement: the two gaps add to a positive definite matrix. -/
theorem posDef_complementGap_of_posSemidef_negGap (design : WeightedDesign size rank)
    (hhalf : ∀ c, design.weight c < 1 / 2) (selected : Finset (Fin size))
    (hnonpos : (1 - subsetSum design selected).PosSemidef) :
    (subsetSum design selectedᶜ - 1).PosDef := by
  classical
  have hrewrite : subsetSum design selectedᶜ - 1
      = (∑ c, (1 - 2 * design.weight c) • atomMatrix (design.atom c))
        + (1 - subsetSum design selected) := by
    rw [← gap_add_complementGap design selected]
    abel
  have hmass := posDef_halfSpentMass design hhalf
  rw [hrewrite]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hmass.1.add hnonpos.1, fun probe hprobe => ?_⟩
  have hmassForm := (Matrix.posDef_iff_dotProduct_mulVec.mp hmass).2 hprobe
  have hrestForm := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hnonpos).2 probe
  rw [star_trivial] at hmassForm hrestForm ⊢
  rw [Matrix.add_mulVec, dotProduct_add]
  linarith

/-- **No tie leaves a triple below the identity.**  At `(6,3)` a triple with a
negative semidefinite gap would hand its complementary triple strict
domination, which tightness forbids. -/
theorem sixThree_not_posSemidef_one_sub_subsetSum_of_isTie (design : WeightedDesign 6 3)
    (hhalf : ∀ c, design.weight c < 1 / 2) (htie : IsTie design)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    ¬ (1 - subsetSum design selected).PosSemidef := by
  classical
  intro hnonpos
  have hcompl : selectedᶜ.card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  exact htie.2 selectedᶜ hcompl
    (posDef_complementGap_of_posSemidef_negGap design hhalf selected hnonpos)

end Gtz
