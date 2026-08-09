import Gtz.Core.Sanity
import Gtz.Design.ComplementEngine
import Gtz.Design.ComplementFrame
import Gtz.Design.FirstTouch
import Gtz.Design.OneDeterminantReduction
import Gtz.Design.RhoNormalForm
import Gtz.Design.StressFreeNormalizer
import Gtz.Design.TightAxisPairBudget
import Gtz.Reduction.BranchTransferConstants
import Gtz.Reduction.DiagonalRungs
import Gtz.Reduction.RealVolumeFloor
import Gtz.Ties.TotalTieCorankOne
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The `U(3,6)` disjunction: the balance family, the boundary pins, and the residual

`Gtz.BaseTripleTightLineFreeOffConicWeakToStrict` is the sharpened `U(3,6)`
residual: a line-free, off-conic `(6,3)` design whose BASE TRIPLE `{0,1,2}`
weakly dominates along an explicit tight direction must contain a strictly
dominating triple.  This file splits that statement into a BALANCE family that
is discharged outright and a named residual, and it mechanizes the structural
pins the antecedent hands over for free.

## The quadratic-form reading of the residual matrix

`Gtz.baseResidual design baseSet` is `1 - sum over baseSet of weighted atoms`;
the tree ships it only as a matrix.  Part 1 adds its quadratic form in both
readings — as `|x|^2` minus the base weighted Parseval mass, and (through
Parseval) as the COMPLEMENT weighted Parseval mass.  Everything downstream is a
consequence of those two lines: the residual is squeezed between `0` and the
identity, and its trace is the complement's share sum.

## Family One: balance

`Gtz.posDef_subsetSum_compl_of_residualExceedsMaxWeight` is the sharp form —
if the residual quadratic form strictly exceeds `maxWeight * |x|^2` at every
nonzero probe, where `maxWeight` bounds the complement weights, then the
COMPLEMENT strictly dominates.  This is the landed complement engine
(`Gtz.posDef_subsetSum_of_outside_share_lt`) read in residual coordinates, and
the translation is one line once Part 1 is in hand.

`Gtz.posDef_subsetSum_compl_of_baseShare_lt` is the SCALAR form.  At rank three
every eigenvalue of the residual lies in `[0, 1]`, so the smallest one is at
least `trace - 2`; and the trace is `3` minus the base set's share sum
(`Gtz.trace_baseResidual_eq_rank_sub_sum_baseShare`).  Family One therefore
fires whenever

    sum over the base triple of atomShare  <  1 - (largest complement weight),

a purely scalar test in the design's own six shares and six weights.  The
eigenvalue floor is proved without any spectral theory: an orthonormal frame
resolves the identity (`Gtz.sum_atomMatrix_orthonormalFrame_eq_one`), so the
trace is the sum of three quadratic-form values and two of them are at most one.
The same frame reading run backwards
(`Gtz.trace_baseResidual_le_of_weakDirection`) shows that ONE weak direction
already caps the trace, so the sharp branch is contained in the scalar one.

The obligation asks for SOME strictly dominating triple, so the certificate may
be run at any of the twenty: `Gtz.exists_posDef_cardThree_of_lightTriple` fires
off ONE light triple anywhere in the design.

## The boundary pins the antecedent hands over

The tight direction is not decoration.  A nonzero vector on which a
`PosSemidef` gap vanishes forces the gap to be SINGULAR, so on the whole
antecedent region

* the base triple is weakly but NOT strictly dominating
  (`Gtz.not_posDef_baseTripleGap_of_tightDirection`), hence every design whose
  base triple already dominates strictly is antecedent-VACUOUS;
* the base triple's tie leg vanishes identically,
  `Gtz.discriminantTie_baseTriple_eq_zero_of_tightDirection` — the antecedent
  region sits exactly on the tie hypersurface `discriminantTie _ 0 1 2 = 0`;
* the complement's weighted mass at the tight direction equals the base
  triple's complementarily-weighted mass
  (`Gtz.tightDirection_complementMass_eq_baseComplementaryMass`), and the base
  triple's UNWEIGHTED mass there is exactly `|n|^2`
  (`Gtz.tightDirection_baseMass_eq_normSq`);
* consequently the residual is LARGE at the tight direction — at least
  `1 - (largest base weight)` times `|n|^2` — and since the base and complement
  maxima are attained at distinct labels their sum misses one
  (`Gtz.baseTripleMaxWeight_add_complementTripleMaxWeight_lt_one`), so THE TIGHT
  DIRECTION IS NEVER THE PROBE THAT DEFEATS FAMILY ONE
  (`Gtz.complementTripleMaxWeight_lt_dotProduct_baseResidual_mulVec_tightDirection`);
* running the balance family at the COMPLEMENT triple would make the BASE triple
  strict, which the tight direction forbids, so the base share is also capped
  above (`Gtz.sum_atomShare_baseTriple_le_of_tightDirection`).  The residual
  branch therefore lives in the two-sided window

      1 - (largest complement weight)  <=  base share  <=  2 + (largest base weight).

## Step zero: the residual is positive definite for free

Line-freeness makes every distinct triple's bracket nonzero
(`Gtz.atomBracket_ne_zero_of_lineFree`), in particular the complement triple's,
so `Gtz.posDef_baseResidual_baseTriple_of_lineFree` gives a `PosDef` residual
and `Gtz.complementFrame_baseTriple_of_lineFree` hands over the
residual-inverse-metric orthonormal frame on `{3,4,5}` with no further work.

## The deliverable

`Gtz.baseTripleTightLineFreeOffConicWeakToStrict_of_weakResidualBranch` is the
DISJUNCTION: the obligation follows from the residual restricted to the region
where Family One FAILS, i.e. where some nonzero probe sees the residual
quadratic form at or below the largest complement weight.  Four repackagings
follow:

* `..._of_heavyBaseTripleShare` against the scalar share test;
* `..._of_heavyBaseTripleShareLivePairTie` composing with the landed
  one-determinant reduction, so the surviving obligation is a SINGLE TIE-LEG
  SIGN at one completing label;
* `..._of_separatedWeakResidualBranch`, which hands the residual every pin
  above at once — weak direction, tight-direction separation, both ends of the
  share window, the vanishing tie leg, the failure of the base triple, and the
  `PosDef` residual;
* `..._of_noLightTriple`, the twenty-triple version of the balance family.

## Honest scope

* NOTHING here closes the Skeleton axiom.  Family One is discharged; the
  complementary branch is reduced, not proved.
* Family One is DEAD at the icosahedral seed, and so is its scalar shadow: at
  uniform weight `1/6` and leverage `3` every share is `1/2`, so the base
  triple's share sum is `3/2`, far above `1 - 1/6`; the sharp test fails too
  (the residual's smallest eigenvalue there is about `0.0528`, below `1/6`).
  That seed is however ANTECEDENT-VACUOUS at the pinned base triple, because
  its base gap is strictly positive definite and therefore has no nonzero
  tight direction — see `Gtz.not_posDef_baseTripleGap_of_tightDirection`.
* `Gtz.HasNoCommonQuadric` is carried through every statement but is NOT SPENT
  by any proof here.  It remains available to the residual branch.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Part 1: the residual as a quadratic form

`Gtz.baseResidual` ships as a matrix only.  These two readings are what every
later argument runs on. -/

/-- **The residual quadratic form, base reading.**  The residual measures how
much of Parseval the base set fails to carry. -/
theorem dotProduct_baseResidual_mulVec_eq_sub_baseMass (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    probeVec ⬝ᵥ (baseResidual design baseSet *ᵥ probeVec)
      = probeVec ⬝ᵥ probeVec
        - ∑ label ∈ baseSet, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
  simp only [baseResidual, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [smul_mulVec_eq_smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]

/-- **The residual quadratic form, complement reading.**  Parseval turns the
same number into the COMPLEMENT's weighted mass — the quadratic-form twin of
`Gtz.baseResidual_eq_complementSum`. -/
theorem dotProduct_baseResidual_mulVec_eq_complementMass (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    probeVec ⬝ᵥ (baseResidual design baseSet *ᵥ probeVec)
      = ∑ label ∈ baseSetᶜ, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
  classical
  rw [baseResidual_eq_complementSum, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [smul_mulVec_eq_smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]

/-- The residual is positive semidefinite as a form: it is a weighted sum of
squares. -/
theorem dotProduct_baseResidual_mulVec_nonneg (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    0 ≤ probeVec ⬝ᵥ (baseResidual design baseSet *ᵥ probeVec) := by
  classical
  rw [dotProduct_baseResidual_mulVec_eq_complementMass]
  exact Finset.sum_nonneg fun label _ =>
    mul_nonneg (design.weight_pos label).le (sq_nonneg _)

/-- The residual never exceeds the identity: the base mass it subtracts is
itself a weighted sum of squares. -/
theorem dotProduct_baseResidual_mulVec_le_self (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    probeVec ⬝ᵥ (baseResidual design baseSet *ᵥ probeVec) ≤ probeVec ⬝ᵥ probeVec := by
  rw [dotProduct_baseResidual_mulVec_eq_sub_baseMass]
  have hbaseNonneg : 0 ≤ ∑ label ∈ baseSet,
      design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 :=
    Finset.sum_nonneg fun label _ => mul_nonneg (design.weight_pos label).le (sq_nonneg _)
  linarith

/-! ## Part 2: the share ledger of the residual -/

/-- **The residual's trace is the complement's share sum.**  Taking the trace of
`Gtz.baseResidual_eq_complementSum`. -/
theorem trace_baseResidual_eq_sum_complementShare (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) :
    Matrix.trace (baseResidual design baseSet) = ∑ label ∈ baseSetᶜ, atomShare design label := by
  classical
  rw [baseResidual_eq_complementSum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.trace_smul, trace_atomMatrix, atomShare, smul_eq_mul]

/-- **The share ledger.**  The shares sum to the rank, so the residual's trace is
the rank minus the base set's share sum — the scalar quantity the balance family
is tested on. -/
theorem trace_baseResidual_eq_rank_sub_sum_baseShare (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) :
    Matrix.trace (baseResidual design baseSet)
      = (rank : ℝ) - ∑ label ∈ baseSet, atomShare design label := by
  classical
  have htotal := Finset.sum_add_sum_compl baseSet (atomShare design)
  rw [sum_atomShare_eq_rank] at htotal
  rw [trace_baseResidual_eq_sum_complementShare]
  linarith

/-! ## Part 3: FAMILY ONE, the balance certificate

The landed complement engine, read in residual coordinates.  Its hypothesis
becomes a single Loewner comparison between the residual and the largest
complement weight. -/

/-- **FAMILY ONE, sharp form.**  If the residual quadratic form strictly exceeds
`maxWeight` times the squared length at every nonzero probe, where `maxWeight`
bounds the weights OUTSIDE the base set, then the complement of the base set
strictly dominates.  Any rank, any subset, no heaviness. -/
theorem posDef_subsetSum_compl_of_residualExceedsMaxWeight (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (maxWeight : ℝ) (hmaxPos : 0 < maxWeight)
    (hmaxBound : ∀ label ∈ baseSetᶜ, design.weight label ≤ maxWeight)
    (hresidual : ∀ probeVec : Fin rank → ℝ, probeVec ≠ 0 →
      maxWeight * (probeVec ⬝ᵥ probeVec)
        < probeVec ⬝ᵥ (baseResidual design baseSet *ᵥ probeVec)) :
    (subsetSum design baseSetᶜ - 1).PosDef := by
  classical
  refine posDef_subsetSum_of_outside_share_lt design baseSetᶜ maxWeight hmaxPos hmaxBound ?_
  intro probeVec hprobeNe
  rw [compl_compl]
  have hvalue := hresidual probeVec hprobeNe
  rw [dotProduct_baseResidual_mulVec_eq_sub_baseMass] at hvalue
  have hexpand : (1 - maxWeight) * (probeVec ⬝ᵥ probeVec)
      = probeVec ⬝ᵥ probeVec - maxWeight * (probeVec ⬝ᵥ probeVec) := by ring
  rw [hexpand]
  linarith

/-! ### The eigenvalue floor, without spectral theory

Two facts turn Family One into a scalar test at rank three.  An orthonormal
frame resolves the identity, so the trace of any form is the sum of its three
frame values; and the residual is at most the identity, so two of those three
values are at most one. -/

/-- **An orthonormal frame resolves the identity.**  The rank-one atoms of three
pairwise orthogonal unit vectors of three-space sum to `1`. -/
theorem sum_atomMatrix_orthonormalFrame_eq_one {frameFirst frameSecond frameThird : Fin 3 → ℝ}
    (hFirstSelf : frameFirst ⬝ᵥ frameFirst = 1) (hSecondSelf : frameSecond ⬝ᵥ frameSecond = 1)
    (hThirdSelf : frameThird ⬝ᵥ frameThird = 1) (hFirstSecond : frameFirst ⬝ᵥ frameSecond = 0)
    (hFirstThird : frameFirst ⬝ᵥ frameThird = 0) (hSecondThird : frameSecond ⬝ᵥ frameThird = 0) :
    atomMatrix frameFirst + atomMatrix frameSecond + atomMatrix frameThird = 1 := by
  have hatomEntry : ∀ (vec : Fin 3 → ℝ) (rowIdx colIdx : Fin 3),
      atomMatrix vec rowIdx colIdx = vec rowIdx * vec colIdx := fun _ _ _ => rfl
  ext rowIndex colIndex
  have hexpand := orthonormalFrame_expansion hFirstSelf hSecondSelf hThirdSelf
    hFirstSecond hFirstThird hSecondThird (Pi.single rowIndex (1 : ℝ))
  simp only [single_one_dotProduct] at hexpand
  have hentry := congrFun hexpand colIndex
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at hentry
  rw [Matrix.add_apply, Matrix.add_apply, hatomEntry, hatomEntry, hatomEntry, Matrix.one_apply]
  rcases eq_or_ne rowIndex colIndex with hdiagonal | hoffDiagonal
  · subst hdiagonal
    rw [if_pos rfl]
    rw [if_pos rfl] at hentry
    linarith
  · rw [if_neg hoffDiagonal]
    rw [if_neg (Ne.symm hoffDiagonal)] at hentry
    linarith

/-- **The trace in an orthonormal frame.**  Resolution of the identity turns the
trace into three quadratic-form readings. -/
theorem trace_eq_sum_orthonormalFrame_quadForm {frameFirst frameSecond frameThird : Fin 3 → ℝ}
    (hFirstSelf : frameFirst ⬝ᵥ frameFirst = 1) (hSecondSelf : frameSecond ⬝ᵥ frameSecond = 1)
    (hThirdSelf : frameThird ⬝ᵥ frameThird = 1) (hFirstSecond : frameFirst ⬝ᵥ frameSecond = 0)
    (hFirstThird : frameFirst ⬝ᵥ frameThird = 0) (hSecondThird : frameSecond ⬝ᵥ frameThird = 0)
    (target : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace target
      = frameFirst ⬝ᵥ (target *ᵥ frameFirst) + frameSecond ⬝ᵥ (target *ᵥ frameSecond)
        + frameThird ⬝ᵥ (target *ᵥ frameThird) := by
  have hresolution := sum_atomMatrix_orthonormalFrame_eq_one hFirstSelf hSecondSelf hThirdSelf
    hFirstSecond hFirstThird hSecondThird
  calc Matrix.trace target = Matrix.trace (target * 1) := by rw [Matrix.mul_one]
    _ = Matrix.trace (target
          * (atomMatrix frameFirst + atomMatrix frameSecond + atomMatrix frameThird)) := by
        rw [hresolution]
    _ = frameFirst ⬝ᵥ (target *ᵥ frameFirst) + frameSecond ⬝ᵥ (target *ᵥ frameSecond)
          + frameThird ⬝ᵥ (target *ᵥ frameThird) := by
        rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
          trace_mul_atomMatrix, trace_mul_atomMatrix, trace_mul_atomMatrix]

/-- **The eigenvalue floor, elementary.**  A three-by-three form bounded above by
the identity has every unit value at least its trace minus two.  No spectral
theorem: the two frame directions orthogonal to the probe contribute at most one
each. -/
theorem trace_sub_two_le_dotProduct_of_quadForm_le_self (target : Matrix (Fin 3) (Fin 3) ℝ)
    (hbounded : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ (target *ᵥ probeVec) ≤ probeVec ⬝ᵥ probeVec)
    {unitVec : Fin 3 → ℝ} (hunit : unitVec ⬝ᵥ unitVec = 1) :
    Matrix.trace target - 2 ≤ unitVec ⬝ᵥ (target *ᵥ unitVec) := by
  obtain ⟨planeFirst, planeSecond, hFirstSelf, hSecondSelf, hFirstSecond, hFirstUnit,
    hSecondUnit⟩ := exists_orthonormal_planarFrame hunit
  have htrace := trace_eq_sum_orthonormalFrame_quadForm hFirstSelf hSecondSelf hunit
    hFirstSecond hFirstUnit hSecondUnit target
  have hboundFirst := hbounded planeFirst
  have hboundSecond := hbounded planeSecond
  rw [hFirstSelf] at hboundFirst
  rw [hSecondSelf] at hboundSecond
  linarith

/-- **Normalization, once.**  Every nonzero probe carries a unit vector on which
any quadratic form reads the same value up to the squared length.  The only
square root in this file, and it is a scalar. -/
theorem exists_unitVec_scaling_dotProduct (target : Matrix (Fin 3) (Fin 3) ℝ)
    {probeVec : Fin 3 → ℝ} (hprobeNe : probeVec ≠ 0) :
    ∃ unitVec : Fin 3 → ℝ, unitVec ⬝ᵥ unitVec = 1
      ∧ probeVec ⬝ᵥ (target *ᵥ probeVec)
          = (probeVec ⬝ᵥ probeVec) * (unitVec ⬝ᵥ (target *ᵥ unitVec)) := by
  have hnormPos : 0 < probeVec ⬝ᵥ probeVec := dotProduct_self_pos hprobeNe
  obtain ⟨lengthOf, hlengthPos, hlengthSq⟩ :
      ∃ lengthOf : ℝ, 0 < lengthOf ∧ lengthOf * lengthOf = probeVec ⬝ᵥ probeVec :=
    ⟨Real.sqrt (probeVec ⬝ᵥ probeVec), Real.sqrt_pos.mpr hnormPos,
      Real.mul_self_sqrt hnormPos.le⟩
  have hlengthNe : lengthOf ≠ 0 := ne_of_gt hlengthPos
  refine ⟨lengthOf⁻¹ • probeVec, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hlengthSq]
    field_simp
  · rw [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hlengthSq]
    field_simp

/-- **The trace test implies the sharp test.**  At rank three a residual trace
above `2 + maxWeight` forces the residual form to beat `maxWeight` at every
nonzero probe. -/
theorem residualExceedsMaxWeight_of_trace_gt (design : WeightedDesign size 3)
    (baseSet : Finset (Fin size)) {maxWeight : ℝ}
    (htrace : 2 + maxWeight < Matrix.trace (baseResidual design baseSet))
    {probeVec : Fin 3 → ℝ} (hprobeNe : probeVec ≠ 0) :
    maxWeight * (probeVec ⬝ᵥ probeVec)
      < probeVec ⬝ᵥ (baseResidual design baseSet *ᵥ probeVec) := by
  have hnormPos : 0 < probeVec ⬝ᵥ probeVec := dotProduct_self_pos hprobeNe
  obtain ⟨unitVec, hunitSelf, hscaling⟩ :=
    exists_unitVec_scaling_dotProduct (baseResidual design baseSet) hprobeNe
  have hfloor := trace_sub_two_le_dotProduct_of_quadForm_le_self (baseResidual design baseSet)
    (fun probe => dotProduct_baseResidual_mulVec_le_self design baseSet probe) hunitSelf
  rw [hscaling]
  calc maxWeight * (probeVec ⬝ᵥ probeVec) = (probeVec ⬝ᵥ probeVec) * maxWeight := mul_comm _ _
    _ < (probeVec ⬝ᵥ probeVec) * (unitVec ⬝ᵥ (baseResidual design baseSet *ᵥ unitVec)) :=
        mul_lt_mul_of_pos_left (by linarith) hnormPos

/-- **The converse trace reading.**  A single weak direction caps the whole
trace: the two frame directions orthogonal to it contribute at most one each. -/
theorem trace_baseResidual_le_of_weakDirection (design : WeightedDesign size 3)
    (baseSet : Finset (Fin size)) {bound : ℝ} {weakDir : Fin 3 → ℝ} (hweakNe : weakDir ≠ 0)
    (hweak : weakDir ⬝ᵥ (baseResidual design baseSet *ᵥ weakDir)
      ≤ bound * (weakDir ⬝ᵥ weakDir)) :
    Matrix.trace (baseResidual design baseSet) ≤ bound + 2 := by
  have hnormPos : 0 < weakDir ⬝ᵥ weakDir := dotProduct_self_pos hweakNe
  obtain ⟨unitVec, hunitSelf, hscaling⟩ :=
    exists_unitVec_scaling_dotProduct (baseResidual design baseSet) hweakNe
  rw [hscaling, mul_comm bound] at hweak
  have hunitBound : unitVec ⬝ᵥ (baseResidual design baseSet *ᵥ unitVec) ≤ bound := by
    by_contra hgreater
    have hlifted : (weakDir ⬝ᵥ weakDir) * bound
        < (weakDir ⬝ᵥ weakDir) * (unitVec ⬝ᵥ (baseResidual design baseSet *ᵥ unitVec)) :=
      mul_lt_mul_of_pos_left (not_le.mp hgreater) hnormPos
    linarith
  have hceiling := trace_sub_two_le_dotProduct_of_quadForm_le_self (baseResidual design baseSet)
    (fun probe => dotProduct_baseResidual_mulVec_le_self design baseSet probe) hunitSelf
  linarith

/-- **FAMILY ONE, scalar form.**  At rank three the balance certificate is a test
on the design's own shares and weights: a base set whose share sum falls below
`1 - maxWeight` has a strictly dominating complement. -/
theorem posDef_subsetSum_compl_of_baseShare_lt (design : WeightedDesign size 3)
    (baseSet : Finset (Fin size)) (maxWeight : ℝ) (hmaxPos : 0 < maxWeight)
    (hmaxBound : ∀ label ∈ baseSetᶜ, design.weight label ≤ maxWeight)
    (hshare : ∑ label ∈ baseSet, atomShare design label < 1 - maxWeight) :
    (subsetSum design baseSetᶜ - 1).PosDef := by
  refine posDef_subsetSum_compl_of_residualExceedsMaxWeight design baseSet maxWeight hmaxPos
    hmaxBound fun probeVec hprobeNe => ?_
  refine residualExceedsMaxWeight_of_trace_gt design baseSet ?_ hprobeNe
  rw [trace_baseResidual_eq_rank_sub_sum_baseShare]
  push_cast
  linarith

/-! ## Part 4: the `(6,3)` instance with the base triple pinned -/

/-- The base triple's largest weight. -/
noncomputable def baseTripleMaxWeight (design : WeightedDesign 6 3) : ℝ :=
  max (max (design.weight 0) (design.weight 1)) (design.weight 2)

/-- The complement triple's largest weight. -/
noncomputable def complementTripleMaxWeight (design : WeightedDesign 6 3) : ℝ :=
  max (max (design.weight 3) (design.weight 4)) (design.weight 5)

theorem complementTripleMaxWeight_pos (design : WeightedDesign 6 3) :
    0 < complementTripleMaxWeight design := by
  simp only [complementTripleMaxWeight]
  exact lt_of_lt_of_le (design.weight_pos 5) (le_max_right _ _)

/-- The complement of the base triple, enumerated. -/
theorem mem_baseTripleComplement_iff (label : Fin 6) :
    label ∈ (({0, 1, 2} : Finset (Fin 6))ᶜ) ↔ label = 3 ∨ label = 4 ∨ label = 5 := by
  revert label
  decide

theorem weight_le_complementTripleMaxWeight (design : WeightedDesign 6 3) :
    ∀ label ∈ (({0, 1, 2} : Finset (Fin 6))ᶜ),
      design.weight label ≤ complementTripleMaxWeight design := by
  intro label hlabel
  simp only [complementTripleMaxWeight]
  rcases (mem_baseTripleComplement_iff label).mp hlabel with rfl | rfl | rfl
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

theorem baseTriple_compl_eq_complementTriple :
    (({0, 1, 2} : Finset (Fin 6))ᶜ) = ({3, 4, 5} : Finset (Fin 6)) := by decide

theorem weight_le_baseTripleMaxWeight (design : WeightedDesign 6 3) :
    ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.weight label ≤ baseTripleMaxWeight design := by
  intro label hlabel
  simp only [baseTripleMaxWeight]
  have hcases : label = 0 ∨ label = 1 ∨ label = 2 := by revert hlabel; revert label; decide
  rcases hcases with rfl | rfl | rfl
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

/-- A three-fold maximum is attained. -/
theorem exists_eq_baseTripleMaxWeight (design : WeightedDesign 6 3) :
    baseTripleMaxWeight design = design.weight 0 ∨ baseTripleMaxWeight design = design.weight 1
      ∨ baseTripleMaxWeight design = design.weight 2 := by
  simp only [baseTripleMaxWeight]
  rcases max_choice (max (design.weight 0) (design.weight 1)) (design.weight 2) with
    houter | houter
  · rcases max_choice (design.weight 0) (design.weight 1) with hinner | hinner
    · exact Or.inl (houter.trans hinner)
    · exact Or.inr (Or.inl (houter.trans hinner))
  · exact Or.inr (Or.inr houter)

theorem exists_eq_complementTripleMaxWeight (design : WeightedDesign 6 3) :
    complementTripleMaxWeight design = design.weight 3
      ∨ complementTripleMaxWeight design = design.weight 4
      ∨ complementTripleMaxWeight design = design.weight 5 := by
  simp only [complementTripleMaxWeight]
  rcases max_choice (max (design.weight 3) (design.weight 4)) (design.weight 5) with
    houter | houter
  · rcases max_choice (design.weight 3) (design.weight 4) with hinner | hinner
    · exact Or.inl (houter.trans hinner)
    · exact Or.inr (Or.inl (houter.trans hinner))
  · exact Or.inr (Or.inr houter)

/-- **The two maxima cannot fill the budget.**  They are attained at DISTINCT
labels and the other four weights are strictly positive, so their sum misses one
by the mass of those four. -/
theorem baseTripleMaxWeight_add_complementTripleMaxWeight_lt_one (design : WeightedDesign 6 3) :
    baseTripleMaxWeight design + complementTripleMaxWeight design < 1 := by
  have hbudget : design.weight 0 + design.weight 1 + design.weight 2 + design.weight 3
      + design.weight 4 + design.weight 5 = 1 := by
    have hparseval := design.weight_sum_one
    rw [Fin.sum_univ_six] at hparseval
    linarith
  have hzero := design.weight_pos 0
  have hone := design.weight_pos 1
  have htwo := design.weight_pos 2
  have hthree := design.weight_pos 3
  have hfour := design.weight_pos 4
  have hfive := design.weight_pos 5
  rcases exists_eq_baseTripleMaxWeight design with hbase | hbase | hbase <;>
    rcases exists_eq_complementTripleMaxWeight design with hcompl | hcompl | hcompl <;>
      rw [hbase, hcompl] <;> linarith

/-- **FAMILY ONE at `(6,3)`, sharp form.** -/
theorem posDef_subsetSum_complementTriple_of_residualExceedsMaxWeight
    (design : WeightedDesign 6 3)
    (hresidual : ∀ probeVec : Fin 3 → ℝ, probeVec ≠ 0 →
      complementTripleMaxWeight design * (probeVec ⬝ᵥ probeVec)
        < probeVec ⬝ᵥ (baseResidual design ({0, 1, 2} : Finset (Fin 6)) *ᵥ probeVec)) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  have hgeneral := posDef_subsetSum_compl_of_residualExceedsMaxWeight design
    ({0, 1, 2} : Finset (Fin 6)) (complementTripleMaxWeight design)
    (complementTripleMaxWeight_pos design) (weight_le_complementTripleMaxWeight design) hresidual
  rwa [baseTriple_compl_eq_complementTriple] at hgeneral

/-- **FAMILY ONE at `(6,3)`, scalar form.**  A light base triple hands the
complement triple over. -/
theorem posDef_subsetSum_complementTriple_of_baseTripleShare_lt (design : WeightedDesign 6 3)
    (hshare : ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare design label
      < 1 - complementTripleMaxWeight design) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  have hgeneral := posDef_subsetSum_compl_of_baseShare_lt design ({0, 1, 2} : Finset (Fin 6))
    (complementTripleMaxWeight design) (complementTripleMaxWeight_pos design)
    (weight_le_complementTripleMaxWeight design) hshare
  rwa [baseTriple_compl_eq_complementTriple] at hgeneral

/-! ### The balance family at every triple, not just the pinned one

The obligation's conclusion asks for SOME strictly dominating triple, so the
balance certificate may be run at any of the twenty.  A design with ONE light
triple is done. -/

theorem complementTriple_compl_eq_baseTriple :
    (({3, 4, 5} : Finset (Fin 6))ᶜ) = ({0, 1, 2} : Finset (Fin 6)) := by decide

theorem card_compl_eq_three_of_card_eq_three (triple : Finset (Fin 6)) (hcard : triple.card = 3) :
    (tripleᶜ).card = 3 := by
  rw [Finset.card_compl, Fintype.card_fin, hcard]

/-- **THE BALANCE FAMILY AT AN ARBITRARY TRIPLE.**  One light triple anywhere in
the design produces a strictly dominating triple — its complement. -/
theorem exists_posDef_cardThree_of_lightTriple (design : WeightedDesign 6 3)
    (lightTriple : Finset (Fin 6)) (hcard : lightTriple.card = 3) (maxWeight : ℝ)
    (hmaxPos : 0 < maxWeight)
    (hmaxBound : ∀ label ∈ lightTripleᶜ, design.weight label ≤ maxWeight)
    (hshare : ∑ label ∈ lightTriple, atomShare design label < 1 - maxWeight) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef :=
  ⟨lightTripleᶜ, card_compl_eq_three_of_card_eq_three lightTriple hcard,
    posDef_subsetSum_compl_of_baseShare_lt design lightTriple maxWeight hmaxPos hmaxBound hshare⟩

/-! ## Part 5: the boundary pins the antecedent supplies -/

/-- A nonzero direction on which a form vanishes rules out positive
definiteness. -/
theorem not_posDef_of_tightDirection {dimension : ℕ}
    (target : Matrix (Fin dimension) (Fin dimension) ℝ) {tightDir : Fin dimension → ℝ}
    (htightNe : tightDir ≠ 0) (htight : tightDir ⬝ᵥ (target *ᵥ tightDir) = 0) :
    ¬ target.PosDef := by
  intro hposDef
  have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 htightNe
  rw [star_trivial, htight] at hvalue
  exact lt_irrefl 0 hvalue

/-- **A tight direction makes a semidefinite form singular.**  Positive
semidefiniteness upgrades the vanishing quadratic value to a kernel vector, and a
kernel vector kills the determinant. -/
theorem det_eq_zero_of_posSemidef_tightDirection {dimension : ℕ}
    {target : Matrix (Fin dimension) (Fin dimension) ℝ} (hposSemidef : target.PosSemidef)
    {tightDir : Fin dimension → ℝ} (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ (target *ᵥ tightDir) = 0) :
    target.det = 0 := by
  have hkernel : target *ᵥ tightDir = 0 := by
    rw [← Matrix.PosSemidef.dotProduct_mulVec_zero_iff hposSemidef tightDir, star_trivial]
    exact htight
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨tightDir, htightNe, hkernel⟩

/-- **The antecedent excludes a strictly dominating base triple.**  Every design
in the obligation's antecedent region has a base triple that dominates WEAKLY and
not strictly; contrapositively, a design whose base triple is already strict is
antecedent-vacuous and needs no residual. -/
theorem not_posDef_baseTripleGap_of_tightDirection (design : WeightedDesign 6 3)
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0) :
    ¬ (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
  not_posDef_of_tightDirection _ htightNe htight

/-- **THE ANTECEDENT REGION IS THE TIE HYPERSURFACE.**  On every design the
obligation talks about, the base triple's own tie leg vanishes identically. -/
theorem discriminantTie_baseTriple_eq_zero_of_tightDirection (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0) :
    discriminantTie design 0 1 2 = 0 := by
  rw [← det_subsetSum_sub_one_eq_discriminantTie design (by decide : (0 : Fin 6) ≠ 1)
    (by decide : (0 : Fin 6) ≠ 2) (by decide : (1 : Fin 6) ≠ 2)]
  exact det_eq_zero_of_posSemidef_tightDirection hdominates htightNe htight

/-- **The tight-direction mass identity.**  At a tight direction the complement's
weighted mass equals the selected set's COMPLEMENTARILY weighted mass.  This is
the excess split read at a zero of the gap. -/
theorem tightDirection_complementMass_eq_baseComplementaryMass (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) {tightDir : Fin rank → ℝ}
    (htight : tightDir ⬝ᵥ ((subsetSum design selected - 1) *ᵥ tightDir) = 0) :
    ∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
      = ∑ label ∈ selected, (1 - design.weight label) * (design.atom label ⬝ᵥ tightDir) ^ 2 := by
  classical
  have hsplit := dotProduct_subsetSum_sub_one_mulVec_eq_excessSplit design selected tightDir
  rw [htight] at hsplit
  linarith

/-- **The tight direction is exactly saturated by the selected set.**  Its
unweighted mass there is the squared length. -/
theorem tightDirection_baseMass_eq_normSq (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) {tightDir : Fin rank → ℝ}
    (htight : tightDir ⬝ᵥ ((subsetSum design selected - 1) *ᵥ tightDir) = 0) :
    ∑ label ∈ selected, (design.atom label ⬝ᵥ tightDir) ^ 2 = tightDir ⬝ᵥ tightDir := by
  have hquad : tightDir ⬝ᵥ ((subsetSum design selected - 1) *ᵥ tightDir)
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ tightDir) ^ 2) - tightDir ⬝ᵥ tightDir := by
    rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
      Matrix.one_mulVec]
  rw [hquad] at htight
  linarith

/-- **The residual's tight-direction value.**  Reading the same identity through
Part 1: at a tight direction of the base set the residual form is the base set's
own weight deficit. -/
theorem dotProduct_baseResidual_mulVec_tightDirection (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) {tightDir : Fin rank → ℝ}
    (htight : tightDir ⬝ᵥ ((subsetSum design baseSet - 1) *ᵥ tightDir) = 0) :
    tightDir ⬝ᵥ (baseResidual design baseSet *ᵥ tightDir)
      = ∑ label ∈ baseSet, (1 - design.weight label) * (design.atom label ⬝ᵥ tightDir) ^ 2 := by
  classical
  rw [dotProduct_baseResidual_mulVec_eq_complementMass]
  exact tightDirection_complementMass_eq_baseComplementaryMass design baseSet htight

/-! ### The tight direction is never the balance family's obstruction

A tight direction saturates the base set's UNWEIGHTED Parseval mass, so the
weighted mass it subtracts from the residual is at most the base set's largest
weight.  The residual is therefore LARGE there — and at `(6,3)` the base and
complement maxima are attained at distinct labels, so their sum misses one.  The
direction that defeats Family One can never be the tight direction the
obligation hands over. -/

/-- **The residual floor at a tight direction.**  General over rank, size and
base set. -/
theorem le_dotProduct_baseResidual_mulVec_tightDirection (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (maxBaseWeight : ℝ)
    (hmaxBound : ∀ label ∈ baseSet, design.weight label ≤ maxBaseWeight)
    {tightDir : Fin rank → ℝ}
    (htight : tightDir ⬝ᵥ ((subsetSum design baseSet - 1) *ᵥ tightDir) = 0) :
    (1 - maxBaseWeight) * (tightDir ⬝ᵥ tightDir)
      ≤ tightDir ⬝ᵥ (baseResidual design baseSet *ᵥ tightDir) := by
  have hsaturated := tightDirection_baseMass_eq_normSq design baseSet htight
  have hweighted : ∑ label ∈ baseSet, design.weight label * (design.atom label ⬝ᵥ tightDir) ^ 2
      ≤ maxBaseWeight * ∑ label ∈ baseSet, (design.atom label ⬝ᵥ tightDir) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun label hlabel =>
      mul_le_mul_of_nonneg_right (hmaxBound label hlabel) (sq_nonneg _)
  rw [hsaturated] at hweighted
  have hexpand : (1 - maxBaseWeight) * (tightDir ⬝ᵥ tightDir)
      = tightDir ⬝ᵥ tightDir - maxBaseWeight * (tightDir ⬝ᵥ tightDir) := by ring
  rw [dotProduct_baseResidual_mulVec_eq_sub_baseMass, hexpand]
  linarith

/-- **THE TIGHT DIRECTION IS NOT A WEAK DIRECTION.**  At `(6,3)` with the base
triple pinned, the residual quadratic form at the obligation's own tight
direction STRICTLY exceeds the largest complement weight — unconditionally, with
no line-freeness and no off-conicity.  So the probe that defeats the balance
family is always a different direction. -/
theorem complementTripleMaxWeight_lt_dotProduct_baseResidual_mulVec_tightDirection
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0) :
    complementTripleMaxWeight design * (tightDir ⬝ᵥ tightDir)
      < tightDir ⬝ᵥ (baseResidual design ({0, 1, 2} : Finset (Fin 6)) *ᵥ tightDir) := by
  have hnormPos : 0 < tightDir ⬝ᵥ tightDir := dotProduct_self_pos htightNe
  have hfloor := le_dotProduct_baseResidual_mulVec_tightDirection design
    ({0, 1, 2} : Finset (Fin 6)) (baseTripleMaxWeight design)
    (weight_le_baseTripleMaxWeight design) htight
  have hbudget := baseTripleMaxWeight_add_complementTripleMaxWeight_lt_one design
  have hstrict : complementTripleMaxWeight design * (tightDir ⬝ᵥ tightDir)
      < (1 - baseTripleMaxWeight design) * (tightDir ⬝ᵥ tightDir) :=
    mul_lt_mul_of_pos_right (by linarith) hnormPos
  linarith

/-- **A weak direction forces a heavy base triple.**  So the sharp branch of the
disjunction is contained in the scalar one: whenever Family One fails, the base
triple's share sum has already reached `1 - (largest complement weight)`. -/
theorem heavyBaseTripleShare_of_weakDirection (design : WeightedDesign 6 3)
    {weakDir : Fin 3 → ℝ} (hweakNe : weakDir ≠ 0)
    (hweak : weakDir ⬝ᵥ (baseResidual design ({0, 1, 2} : Finset (Fin 6)) *ᵥ weakDir)
      ≤ complementTripleMaxWeight design * (weakDir ⬝ᵥ weakDir)) :
    1 - complementTripleMaxWeight design
      ≤ ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare design label := by
  have htrace := trace_baseResidual_le_of_weakDirection design ({0, 1, 2} : Finset (Fin 6))
    hweakNe hweak
  rw [trace_baseResidual_eq_rank_sub_sum_baseShare] at htrace
  push_cast at htrace
  linarith

/-! ### The share window on the antecedent region

The balance family run at the COMPLEMENT triple would make the BASE triple
strict — which the tight direction forbids.  So the antecedent also caps the base
share from above, and the residual branch lives inside a two-sided window. -/

theorem sum_atomShare_baseTriple_add_complementTriple (design : WeightedDesign 6 3) :
    (∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare design label)
      + ∑ label ∈ ({3, 4, 5} : Finset (Fin 6)), atomShare design label = 3 := by
  classical
  have hsplit := Finset.sum_add_sum_compl ({0, 1, 2} : Finset (Fin 6)) (atomShare design)
  rw [sum_atomShare_eq_rank, baseTriple_compl_eq_complementTriple] at hsplit
  rw [hsplit]
  norm_num

/-- **The complement triple is share-heavy on the antecedent region.**  Were it
light, the balance family would make the BASE triple strict, contradicting the
tight direction. -/
theorem le_sum_atomShare_complementTriple_of_tightDirection (design : WeightedDesign 6 3)
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0) :
    1 - baseTripleMaxWeight design
      ≤ ∑ label ∈ ({3, 4, 5} : Finset (Fin 6)), atomShare design label := by
  by_contra hlight
  refine not_posDef_baseTripleGap_of_tightDirection design htightNe htight ?_
  have hmaxBound : ∀ label ∈ (({3, 4, 5} : Finset (Fin 6))ᶜ),
      design.weight label ≤ baseTripleMaxWeight design := by
    rw [complementTriple_compl_eq_baseTriple]
    exact weight_le_baseTripleMaxWeight design
  have hbasePos : 0 < baseTripleMaxWeight design := by
    simp only [baseTripleMaxWeight]
    exact lt_of_lt_of_le (design.weight_pos 2) (le_max_right _ _)
  have hstrict := posDef_subsetSum_compl_of_baseShare_lt design ({3, 4, 5} : Finset (Fin 6))
    (baseTripleMaxWeight design) hbasePos hmaxBound (not_le.mp hlight)
  rwa [complementTriple_compl_eq_baseTriple] at hstrict

/-- **THE SHARE WINDOW, upper end.**  On the whole antecedent region the base
triple's share sum is capped by `2 + (largest base-triple weight)`. -/
theorem sum_atomShare_baseTriple_le_of_tightDirection (design : WeightedDesign 6 3)
    {tightDir : Fin 3 → ℝ} (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ tightDir) = 0) :
    ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare design label
      ≤ 2 + baseTripleMaxWeight design := by
  have hledger := sum_atomShare_baseTriple_add_complementTriple design
  have hheavy := le_sum_atomShare_complementTriple_of_tightDirection design htightNe htight
  linarith

/-! ## Part 6: step zero — line-freeness gives the residual for free -/

/-- **Line-freeness is bracket nonvanishing.**  The empty line family is the
everywhere-false pattern, so `Gtz.HasLinePattern` against it says every distinct
triple is a basis. -/
theorem atomBracket_ne_zero_of_lineFree (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {leftLabel midLabel rightLabel : Fin 6} (hleftMid : leftLabel ≠ midLabel)
    (hleftRight : leftLabel ≠ rightLabel) (hmidRight : midLabel ≠ rightLabel) :
    atomBracket design leftLabel midLabel rightLabel ≠ 0 := by
  intro hvanish
  have hpattern :=
    (hlineFree leftLabel midLabel rightLabel hleftMid hleftRight hmidRight).mp hvanish
  simp only [lineFamilyPattern, List.not_mem_nil, false_and, exists_false] at hpattern

/-- **STEP ZERO.**  On the line-free stratum the base triple's residual is
positive definite outright: its complement `{3,4,5}` is a basis. -/
theorem posDef_baseResidual_baseTriple_of_lineFree (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    (baseResidual design ({0, 1, 2} : Finset (Fin 6))).PosDef := by
  have hbracket : tripleBracket (design.atom 3) (design.atom 4) (design.atom 5) ≠ 0 :=
    atomBracket_ne_zero_of_lineFree design hlineFree (by decide) (by decide) (by decide)
  refine (posDef_baseResidual_iff_tripleBracket_ne_zero design ({0, 1, 2} : Finset (Fin 6))
    (![3, 4, 5] : Fin 3 → Fin 6) (by decide) (by decide)).mpr ?_
  simpa using hbracket

/-- **The complement frame, free on the stratum.**  The three complement atoms
are orthonormal for the residual-inverse metric. -/
theorem complementFrame_baseTriple_of_lineFree (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    IsInverseMetricOrthonormalOn design (({0, 1, 2} : Finset (Fin 6))ᶜ)
      (baseResidual design ({0, 1, 2} : Finset (Fin 6))) :=
  complementFrame_sixThree design ({0, 1, 2} : Finset (Fin 6)) (by decide)
    (posDef_baseResidual_baseTriple_of_lineFree design hlineFree)

/-! ## Part 7: THE DISJUNCTION

Family One is discharged.  What remains of the obligation is its complement:
the region where some nonzero probe sees the residual at or below the largest
complement weight. -/

/-- **THE DISJUNCTION, sharp form.**  `Gtz.BaseTripleTightLineFreeOffConicWeakToStrict`
follows from the residual restricted to the designs where FAMILY ONE FAILS.  On
the complementary region the balance certificate already produces the strictly
dominating triple `{3,4,5}`, with no residual spent. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_of_weakResidualBranch
    (hresidual : ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      Dominates design {0, 1, 2} →
      tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design {0, 1, 2} - 1) *ᵥ tightDir) = 0 →
      (∃ weakDir : Fin 3 → ℝ, weakDir ≠ 0 ∧
        weakDir ⬝ᵥ (baseResidual design ({0, 1, 2} : Finset (Fin 6)) *ᵥ weakDir)
          ≤ complementTripleMaxWeight design * (weakDir ⬝ᵥ weakDir)) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    BaseTripleTightLineFreeOffConicWeakToStrict := by
  intro design tightDir hlineFree hoffConic hdominates htightNe htight
  by_cases hweakDirection : ∃ weakDir : Fin 3 → ℝ, weakDir ≠ 0 ∧
      weakDir ⬝ᵥ (baseResidual design ({0, 1, 2} : Finset (Fin 6)) *ᵥ weakDir)
        ≤ complementTripleMaxWeight design * (weakDir ⬝ᵥ weakDir)
  · exact hresidual design tightDir hlineFree hoffConic hdominates htightNe htight hweakDirection
  · push Not at hweakDirection
    exact ⟨({3, 4, 5} : Finset (Fin 6)), by decide,
      posDef_subsetSum_complementTriple_of_residualExceedsMaxWeight design hweakDirection⟩

/-- **THE DISJUNCTION, scalar form.**  The residual only has to be supplied where
the base triple's share sum is at least `1 - (largest complement weight)`. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_of_heavyBaseTripleShare
    (hresidual : ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      Dominates design {0, 1, 2} →
      tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design {0, 1, 2} - 1) *ᵥ tightDir) = 0 →
      1 - complementTripleMaxWeight design
        ≤ ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare design label →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    BaseTripleTightLineFreeOffConicWeakToStrict := by
  intro design tightDir hlineFree hoffConic hdominates htightNe htight
  by_cases hlightBase : ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare design label
      < 1 - complementTripleMaxWeight design
  · exact ⟨({3, 4, 5} : Finset (Fin 6)), by decide,
      posDef_subsetSum_complementTriple_of_baseTripleShare_lt design hlightBase⟩
  · exact hresidual design tightDir hlineFree hoffConic hdominates htightNe htight
      (not_lt.mp hlightBase)

/-- **THE DISJUNCTION against the one-determinant residual.**  Composing with the
landed `Gtz.exists_posDef_cardThree_of_forall_livePair`: on the heavy-base-share
branch it is enough that every live pair completes to a strictly positive tie
leg.  The live pair itself is free. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_of_heavyBaseTripleShareLivePairTie
    (hresidual : ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      Dominates design {0, 1, 2} →
      tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design {0, 1, 2} - 1) *ᵥ tightDir) = 0 →
      1 - complementTripleMaxWeight design
        ≤ ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare design label →
      ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
        IsLivePair design pivotLabel pairFirst →
        ∃ pairSecond : Fin 6, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    BaseTripleTightLineFreeOffConicWeakToStrict :=
  baseTripleTightLineFreeOffConicWeakToStrict_of_heavyBaseTripleShare
    fun design tightDir hlineFree hoffConic hdominates htightNe htight hheavyShare =>
      exists_posDef_cardThree_of_forall_livePair design
        (hresidual design tightDir hlineFree hoffConic hdominates htightNe htight hheavyShare)

/-- **THE DISJUNCTION WITH EVERY PIN CARRIED.**  The strongest packaging: on the
surviving branch the residual receives, besides the obligation's own hypotheses,

* a nonzero weak direction defeating the balance family, together with the fact
  that the TIGHT direction is not one (they are genuinely different probes);
* the heavy-base-share ledger, forced by that weak direction;
* the vanishing of the base triple's tie leg and the failure of the base triple
  to be strict — the antecedent region is the tie hypersurface;
* the base triple's residual `PosDef` and its complement frame, free from
  line-freeness.

Nothing on this list has to be re-derived downstream. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_of_separatedWeakResidualBranch
    (hresidual : ∀ (design : WeightedDesign 6 3) (tightDir weakDir : Fin 3 → ℝ),
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      Dominates design {0, 1, 2} →
      tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design {0, 1, 2} - 1) *ᵥ tightDir) = 0 →
      weakDir ≠ 0 →
      weakDir ⬝ᵥ (baseResidual design ({0, 1, 2} : Finset (Fin 6)) *ᵥ weakDir)
        ≤ complementTripleMaxWeight design * (weakDir ⬝ᵥ weakDir) →
      complementTripleMaxWeight design * (tightDir ⬝ᵥ tightDir)
        < tightDir ⬝ᵥ (baseResidual design ({0, 1, 2} : Finset (Fin 6)) *ᵥ tightDir) →
      1 - complementTripleMaxWeight design
        ≤ ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare design label →
      ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare design label
        ≤ 2 + baseTripleMaxWeight design →
      discriminantTie design 0 1 2 = 0 →
      ¬ (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef →
      (baseResidual design ({0, 1, 2} : Finset (Fin 6))).PosDef →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    BaseTripleTightLineFreeOffConicWeakToStrict := by
  refine baseTripleTightLineFreeOffConicWeakToStrict_of_weakResidualBranch ?_
  rintro design tightDir hlineFree hoffConic hdominates htightNe htight ⟨weakDir, hweakNe, hweak⟩
  exact hresidual design tightDir weakDir hlineFree hoffConic hdominates htightNe htight
    hweakNe hweak
    (complementTripleMaxWeight_lt_dotProduct_baseResidual_mulVec_tightDirection design
      htightNe htight)
    (heavyBaseTripleShare_of_weakDirection design hweakNe hweak)
    (sum_atomShare_baseTriple_le_of_tightDirection design htightNe htight)
    (discriminantTie_baseTriple_eq_zero_of_tightDirection design hdominates htightNe htight)
    (not_posDef_baseTripleGap_of_tightDirection design htightNe htight)
    (posDef_baseResidual_baseTriple_of_lineFree design hlineFree)

/-- **THE DISJUNCTION AGAINST THE TWENTY-TRIPLE BALANCE FAMILY.**  The
conclusion asks for SOME strictly dominating triple, so the balance certificate
may be run at every triple, not only at the pinned one.  What survives is the
region where NO triple of the design is light. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_of_noLightTriple
    (hresidual : ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      Dominates design {0, 1, 2} →
      tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design {0, 1, 2} - 1) *ᵥ tightDir) = 0 →
      (∀ lightTriple : Finset (Fin 6), lightTriple.card = 3 → ∀ maxWeight : ℝ, 0 < maxWeight →
        (∀ label ∈ lightTripleᶜ, design.weight label ≤ maxWeight) →
        1 - maxWeight ≤ ∑ label ∈ lightTriple, atomShare design label) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    BaseTripleTightLineFreeOffConicWeakToStrict := by
  intro design tightDir hlineFree hoffConic hdominates htightNe htight
  by_cases hlight : ∃ lightTriple : Finset (Fin 6), lightTriple.card = 3 ∧ ∃ maxWeight : ℝ,
      0 < maxWeight ∧ (∀ label ∈ lightTripleᶜ, design.weight label ≤ maxWeight)
        ∧ ∑ label ∈ lightTriple, atomShare design label < 1 - maxWeight
  · obtain ⟨lightTriple, hcard, maxWeight, hmaxPos, hmaxBound, hshare⟩ := hlight
    exact exists_posDef_cardThree_of_lightTriple design lightTriple hcard maxWeight hmaxPos
      hmaxBound hshare
  · refine hresidual design tightDir hlineFree hoffConic hdominates htightNe htight ?_
    push Not at hlight
    intro lightTriple hcard maxWeight hmaxPos hmaxBound
    exact hlight lightTriple hcard maxWeight hmaxPos hmaxBound

/-! ## Part 8: non-vacuity of the balance family

`Gtz.selectiveAxisDesign` is the three coordinate axes at length one with weight
`1/9` and again at length two with weight `2/9`.  Its short triple carries share
`1/3`, its long weights are `2/9`, and `1/3 < 7/9`, so FAMILY ONE FIRES and
delivers the long triple.  (That design has parallel pairs, so it is not on the
line-free stratum; it certifies the ENGINE, not the class.) -/

theorem atomShare_selectiveAxisDesign_shortAxes :
    atomShare selectiveAxisDesign 0 = 1 / 9 ∧ atomShare selectiveAxisDesign 1 = 1 / 9
      ∧ atomShare selectiveAxisDesign 2 = 1 / 9 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [atomShare, selectiveAxisDesign, leverageOf, Fin.sum_univ_three]

theorem sum_atomShare_selectiveAxisDesign_shortTriple :
    ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)), atomShare selectiveAxisDesign label = 1 / 3 := by
  obtain ⟨hzero, hone, htwo⟩ := atomShare_selectiveAxisDesign_shortAxes
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    hzero, hone, htwo]
  norm_num

theorem weight_selectiveAxisDesign_longAxes :
    selectiveAxisDesign.weight 3 = 2 / 9 ∧ selectiveAxisDesign.weight 4 = 2 / 9
      ∧ selectiveAxisDesign.weight 5 = 2 / 9 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [selectiveAxisDesign]

theorem complementTripleMaxWeight_selectiveAxisDesign :
    complementTripleMaxWeight selectiveAxisDesign = 2 / 9 := by
  obtain ⟨hthree, hfour, hfive⟩ := weight_selectiveAxisDesign_longAxes
  simp only [complementTripleMaxWeight, hthree, hfour, hfive, max_self]

/-- **The balance family is not vacuous at `(6,3)` with the base triple pinned.** -/
theorem posDef_subsetSum_selectiveAxisDesign_longTriple_via_balanceFamily :
    (subsetSum selectiveAxisDesign ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  refine posDef_subsetSum_complementTriple_of_baseTripleShare_lt selectiveAxisDesign ?_
  rw [sum_atomShare_selectiveAxisDesign_shortTriple,
    complementTripleMaxWeight_selectiveAxisDesign]
  norm_num

/-! ### The witness meets the antecedent's domination half exactly

The short triple of `Gtz.selectiveAxisDesign` is the three coordinate axes, so
its atom sum IS the identity: the base gap is the zero matrix.  That design
therefore satisfies `Dominates {0,1,2}` with EVERY nonzero direction tight — the
whole domination-plus-tightness half of the obligation's antecedent — and the
balance family still fires on it.  What it misses is only the stratum: it has
three parallel pairs, so it is not line-free. -/

theorem subsetSum_selectiveAxisDesign_shortTriple_eq_one :
    subsetSum selectiveAxisDesign ({0, 1, 2} : Finset (Fin 6)) = 1 := by
  rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [atomMatrix, selectiveAxisDesign]

theorem dominates_selectiveAxisDesign_shortTriple :
    Dominates selectiveAxisDesign ({0, 1, 2} : Finset (Fin 6)) := by
  rw [Dominates, subsetSum_selectiveAxisDesign_shortTriple_eq_one, sub_self]
  exact Matrix.PosSemidef.zero

/-- Every direction is tight there: the base gap is identically zero. -/
theorem tightDirection_selectiveAxisDesign_shortTriple (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ ((subsetSum selectiveAxisDesign ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probeVec)
      = 0 := by
  rw [subsetSum_selectiveAxisDesign_shortTriple_eq_one, sub_self, Matrix.zero_mulVec,
    dotProduct_zero]

end Gtz
