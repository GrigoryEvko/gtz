/-
# The spike forbids the shared-line-pair matroid at `(5,3)`

`Gtz.EndpointBottomTieExclusionFiveThree` (the sharpest residual of branch (ii)
of the `(6,3)` stress trichotomy) asserts that the BOTTOM of a spiked
one-vanished configuration is never a tie.  Its bottom is a primitive
`WeightedDesign 5 3` carrying a SPIKE: a sixth direction, parallel to no atom,
whose rank-one matrix completes the five atom matrices into a dependence with
every coefficient nonzero.

What this file proves is a statement about the bottom's MATROID.  A spiked
bottom cannot have two dependent (coplanar) atom triples sharing an atom.

That configuration is not an incidental one.  Both of the tree's primitive
`(5,3)` ties realize it, in the same shape:

* `Gtz.diamondDesign` -- the graphic design of `K4 - e`, whose two triangles are
  the dependent triples `{0,1,3}` and `{0,2,4}`, sharing the edge `0`;
* `Gtz.uniformTieParentDesign` -- atoms
  `(r5,0,0), (-r2,s3,0), (r2,0,s3), (r2,s3,0), (-r2,0,s3)` with
  `r5 = sqrt(5/3)`, `r2 = sqrt(2/3)`, `s3 = sqrt 3`, whose dependent triples are
  `{0,1,3}` (the plane `z = 0`) and `{0,2,4}` (the plane `y = 0`), again sharing
  the atom `0`.

Both were verified independently, in exact arithmetic, to be primitive and
stress-free, with exactly those two dependent triples and no others.  So the
theorem below excludes every `(5,3)` tie the campaign knows.

The mechanism is short and needs neither stress-freeness nor the endpoint
gauge.  Write the spike's expansion `v v^T = sum_i c_i g_i g_i^T` with every
`c_i` nonzero, and let `n1`, `n2` be normals of the two planes, so that `n1` is
orthogonal to the first triple and `n2` to the second.  Pairing the expansion
against `(n1, n2)` kills every term at once -- each label lies on one of the two
planes -- so `(n1 . v)(n2 . v) = 0` and the spike lies on one of the planes.
Say `n1 . v = 0`.  Pairing against `(n1, probe)` for a free `probe` then leaves
only the two labels OFF the first plane, and reads

    c_4 (n1 . g_4) g_4  +  c_5 (n1 . g_5) g_5  =  0 .

Those two atoms are not parallel, so both scalars vanish; the `c` are nonzero,
so `n1` is orthogonal to them too -- hence to all five atoms.  Parseval then
forces `n1 = 0`, and the planes were assumed genuine.

Nothing here is conditional and nothing is assumed.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.PrimitiveTightClassification
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.Completion
import Gtz.Ties.TotalTieCorankOne
import Gtz.Reduction.Naimark
import Gtz.Reduction.Crystallization
import Gtz.Reduction.SplitTransfer
import Gtz.Design.RankTwoTieCriterion
import Gtz.Ties.RankTwoHingeBridge
import Gtz.Reduction.EndpointGaugeDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace EndpointSpike

open Matrix Finset Gtz

/-! ## The bilinear pairing of a weighted rank-one sum -/

/-- Pairing a scaled rank-one atom between two probes splits into the two
pairings.  This is the only matrix computation the file performs. -/
theorem pairing_smul_atomMatrix (coefficient : ℝ)
    (vector leftProbe rightProbe : Fin 3 → ℝ) :
    leftProbe ⬝ᵥ ((coefficient • atomMatrix vector) *ᵥ rightProbe)
      = coefficient * ((leftProbe ⬝ᵥ vector) * (vector ⬝ᵥ rightProbe)) := by
  have hpullScalar : (coefficient • atomMatrix vector) *ᵥ rightProbe
      = coefficient • (atomMatrix vector *ᵥ rightProbe) := by
    funext coordinate
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hpullScalar, atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul]
  ring

/-- The same pairing across a five-term weighted sum of rank-one atoms. -/
theorem pairing_fiveAtoms
    (coeffOne coeffTwo coeffThree coeffFour coeffFive : ℝ)
    (atomOne atomTwo atomThree atomFour atomFive leftProbe rightProbe : Fin 3 → ℝ) :
    leftProbe ⬝ᵥ ((coeffOne • atomMatrix atomOne + coeffTwo • atomMatrix atomTwo
        + coeffThree • atomMatrix atomThree + coeffFour • atomMatrix atomFour
        + coeffFive • atomMatrix atomFive) *ᵥ rightProbe)
      = coeffOne * ((leftProbe ⬝ᵥ atomOne) * (atomOne ⬝ᵥ rightProbe))
        + coeffTwo * ((leftProbe ⬝ᵥ atomTwo) * (atomTwo ⬝ᵥ rightProbe))
        + coeffThree * ((leftProbe ⬝ᵥ atomThree) * (atomThree ⬝ᵥ rightProbe))
        + coeffFour * ((leftProbe ⬝ᵥ atomFour) * (atomFour ⬝ᵥ rightProbe))
        + coeffFive * ((leftProbe ⬝ᵥ atomFive) * (atomFive ⬝ᵥ rightProbe)) := by
  simp only [Matrix.add_mulVec, dotProduct_add, pairing_smul_atomMatrix]

/-- Two non-parallel vectors carry no nontrivial vanishing combination. -/
theorem coeffPair_eq_zero_of_smul_add_smul_eq_zero
    (leftVector rightVector : Fin 3 → ℝ) (leftScalar rightScalar : ℝ)
    (hfree : ∀ ratio : ℝ, rightVector ≠ ratio • leftVector)
    (hleftNonzero : leftVector ≠ 0)
    (hvanish : leftScalar • leftVector + rightScalar • rightVector = 0) :
    leftScalar = 0 ∧ rightScalar = 0 := by
  by_cases hright : rightScalar = 0
  · refine ⟨?_, hright⟩
    rw [hright, zero_smul, add_zero] at hvanish
    rcases smul_eq_zero.mp hvanish with hscalar | hvector
    · exact hscalar
    · exact absurd hvector hleftNonzero
  · exfalso
    refine hfree ((-leftScalar) / rightScalar) ?_
    have hsolve : rightScalar • rightVector = (-leftScalar) • leftVector := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hvanish)
    calc rightVector = rightScalar⁻¹ • (rightScalar • rightVector) := by
          rw [smul_smul, inv_mul_cancel₀ hright, one_smul]
      _ = rightScalar⁻¹ • ((-leftScalar) • leftVector) := by rw [hsolve]
      _ = ((-leftScalar) / rightScalar) • leftVector := by rw [smul_smul, div_eq_inv_mul]

/-! ## The single-plane obstruction

If the spike lies on one of the two planes, the normal of that plane is
orthogonal to every atom, hence zero. -/

/-- **A spike on a plane kills the plane's normal.**  Three atoms lie on the
plane, the spike lies on it too, and the two atoms OFF it are non-parallel with
nonzero shares -- then the normal annihilates all five atoms and Parseval
collapses it to zero. -/
theorem planeNormal_eq_zero_of_spike_on_plane
    (planeAtomOne planeAtomTwo planeAtomThree offAtomOne offAtomTwo : Fin 3 → ℝ)
    (planeShareOne planeShareTwo planeShareThree offShareOne offShareTwo : ℝ)
    (planeWeightOne planeWeightTwo planeWeightThree offWeightOne offWeightTwo : ℝ)
    (spikeDirection planeNormal : Fin 3 → ℝ)
    (hparseval : planeWeightOne • atomMatrix planeAtomOne
        + planeWeightTwo • atomMatrix planeAtomTwo
        + planeWeightThree • atomMatrix planeAtomThree
        + offWeightOne • atomMatrix offAtomOne
        + offWeightTwo • atomMatrix offAtomTwo = 1)
    (hexpansion : atomMatrix spikeDirection
        = planeShareOne • atomMatrix planeAtomOne
          + planeShareTwo • atomMatrix planeAtomTwo
          + planeShareThree • atomMatrix planeAtomThree
          + offShareOne • atomMatrix offAtomOne
          + offShareTwo • atomMatrix offAtomTwo)
    (hnormalPlaneOne : planeNormal ⬝ᵥ planeAtomOne = 0)
    (hnormalPlaneTwo : planeNormal ⬝ᵥ planeAtomTwo = 0)
    (hnormalPlaneThree : planeNormal ⬝ᵥ planeAtomThree = 0)
    (hnormalSpike : planeNormal ⬝ᵥ spikeDirection = 0)
    (hoffShareOne : offShareOne ≠ 0) (hoffShareTwo : offShareTwo ≠ 0)
    (hoffFree : ∀ ratio : ℝ, offAtomTwo ≠ ratio • offAtomOne)
    (hoffNonzero : offAtomOne ≠ 0) :
    planeNormal = 0 := by
  -- pairing the expansion against `(planeNormal, probe)` leaves only the two
  -- labels off the plane
  have hpair : ∀ probe : Fin 3 → ℝ,
      (offShareOne * (planeNormal ⬝ᵥ offAtomOne)) * (offAtomOne ⬝ᵥ probe)
        + (offShareTwo * (planeNormal ⬝ᵥ offAtomTwo)) * (offAtomTwo ⬝ᵥ probe) = 0 := by
    intro probe
    have hleft : planeNormal ⬝ᵥ (atomMatrix spikeDirection *ᵥ probe) = 0 := by
      rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, hnormalSpike,
        mul_zero]
    rw [hexpansion, pairing_fiveAtoms, hnormalPlaneOne, hnormalPlaneTwo,
      hnormalPlaneThree] at hleft
    linear_combination hleft
  -- so the two off-plane atoms carry a vanishing combination
  have hcombo : (offShareOne * (planeNormal ⬝ᵥ offAtomOne)) • offAtomOne
      + (offShareTwo * (planeNormal ⬝ᵥ offAtomTwo)) • offAtomTwo = 0 := by
    refine eq_zero_of_dotProduct_self_eq_zero ?_
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    exact hpair _
  obtain ⟨hfirstScalar, hsecondScalar⟩ :=
    coeffPair_eq_zero_of_smul_add_smul_eq_zero offAtomOne offAtomTwo _ _ hoffFree
      hoffNonzero hcombo
  have hnormalOffOne : planeNormal ⬝ᵥ offAtomOne = 0 := by
    rcases mul_eq_zero.mp hfirstScalar with hshare | hdot
    · exact absurd hshare hoffShareOne
    · exact hdot
  have hnormalOffTwo : planeNormal ⬝ᵥ offAtomTwo = 0 := by
    rcases mul_eq_zero.mp hsecondScalar with hshare | hdot
    · exact absurd hshare hoffShareTwo
    · exact hdot
  -- the normal now annihilates every atom, so Parseval reads it as zero
  refine eq_zero_of_dotProduct_self_eq_zero ?_
  have hself : planeNormal ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ planeNormal)
      = planeNormal ⬝ᵥ planeNormal := by
    rw [Matrix.one_mulVec]
  rw [← hparseval, pairing_fiveAtoms, hnormalPlaneOne, hnormalPlaneTwo, hnormalPlaneThree,
    hnormalOffOne, hnormalOffTwo] at hself
  linarith [hself]

/-! ## The two-plane obstruction -/

/-- **A full-support spike forbids the shared-line-pair shape.**  Five atoms
covered by two planes -- three on each, one shared -- carry no spike direction
whose rank-one expansion in the atoms has every coefficient nonzero. -/
theorem no_spike_of_sharedLinePair
    (sharedAtom firstAtom secondAtom thirdAtom fourthAtom : Fin 3 → ℝ)
    (sharedShare firstShare secondShare thirdShare fourthShare : ℝ)
    (sharedWeight firstWeight secondWeight thirdWeight fourthWeight : ℝ)
    (spikeDirection planeNormalOne planeNormalTwo : Fin 3 → ℝ)
    (hparseval : sharedWeight • atomMatrix sharedAtom + firstWeight • atomMatrix firstAtom
        + secondWeight • atomMatrix secondAtom + thirdWeight • atomMatrix thirdAtom
        + fourthWeight • atomMatrix fourthAtom = 1)
    (hexpansion : atomMatrix spikeDirection
        = sharedShare • atomMatrix sharedAtom + firstShare • atomMatrix firstAtom
          + secondShare • atomMatrix secondAtom + thirdShare • atomMatrix thirdAtom
          + fourthShare • atomMatrix fourthAtom)
    (hfirstShare : firstShare ≠ 0) (hsecondShare : secondShare ≠ 0)
    (hthirdShare : thirdShare ≠ 0) (hfourthShare : fourthShare ≠ 0)
    (honeShared : planeNormalOne ⬝ᵥ sharedAtom = 0)
    (honeFirst : planeNormalOne ⬝ᵥ firstAtom = 0)
    (honeSecond : planeNormalOne ⬝ᵥ secondAtom = 0)
    (htwoShared : planeNormalTwo ⬝ᵥ sharedAtom = 0)
    (htwoThird : planeNormalTwo ⬝ᵥ thirdAtom = 0)
    (htwoFourth : planeNormalTwo ⬝ᵥ fourthAtom = 0)
    (hthirdFourthFree : ∀ ratio : ℝ, fourthAtom ≠ ratio • thirdAtom)
    (hthirdNonzero : thirdAtom ≠ 0)
    (hfirstSecondFree : ∀ ratio : ℝ, secondAtom ≠ ratio • firstAtom)
    (hfirstNonzero : firstAtom ≠ 0)
    (hnormalOneNonzero : planeNormalOne ≠ 0)
    (hnormalTwoNonzero : planeNormalTwo ≠ 0) :
    False := by
  -- every label lies on one of the two planes, so the mixed pairing vanishes
  have hcross : (planeNormalOne ⬝ᵥ spikeDirection) * (spikeDirection ⬝ᵥ planeNormalTwo) = 0 := by
    have hleft : planeNormalOne ⬝ᵥ (atomMatrix spikeDirection *ᵥ planeNormalTwo)
        = (planeNormalOne ⬝ᵥ spikeDirection) * (spikeDirection ⬝ᵥ planeNormalTwo) := by
      rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul]
      ring
    rw [hexpansion, pairing_fiveAtoms, honeShared, honeFirst, honeSecond] at hleft
    rw [dotProduct_comm thirdAtom planeNormalTwo, htwoThird,
      dotProduct_comm fourthAtom planeNormalTwo, htwoFourth] at hleft
    linear_combination - hleft
  rcases mul_eq_zero.mp hcross with hspikeOne | hspikeTwo
  · -- the spike lies on the first plane: its normal dies
    exact hnormalOneNonzero
      (planeNormal_eq_zero_of_spike_on_plane sharedAtom firstAtom secondAtom thirdAtom
        fourthAtom sharedShare firstShare secondShare thirdShare fourthShare sharedWeight
        firstWeight secondWeight thirdWeight fourthWeight spikeDirection planeNormalOne
        hparseval hexpansion honeShared honeFirst honeSecond hspikeOne hthirdShare
        hfourthShare hthirdFourthFree hthirdNonzero)
  · -- the spike lies on the second plane: reassociate and repeat
    refine hnormalTwoNonzero
      (planeNormal_eq_zero_of_spike_on_plane sharedAtom thirdAtom fourthAtom firstAtom
        secondAtom sharedShare thirdShare fourthShare firstShare secondShare sharedWeight
        thirdWeight fourthWeight firstWeight secondWeight spikeDirection planeNormalTwo
        ?_ ?_ htwoShared htwoThird htwoFourth ?_ hfirstShare hsecondShare hfirstSecondFree
        hfirstNonzero)
    · rw [← hparseval]; abel
    · rw [hexpansion]; abel
    · rw [dotProduct_comm planeNormalTwo spikeDirection]; exact hspikeTwo

/-! ## The obstruction in the target Prop's own hypothesis shape

`Gtz.EndpointBottomTieExclusionFiveThree` presents the spike as a dependence
`sum_i b_i A_i + s v v^T = 0` with `s > 0` and every `b_i` nonzero.  Dividing by
`s` turns that into the expansion the obstruction consumes. -/

/-- The dependence of the target Prop, solved for the spike's rank-one matrix. -/
theorem spikeExpansion_of_dependence
    (bottomDesign : WeightedDesign 5 3) (spikeDirection : Fin 3 → ℝ)
    (bottomCoeff : Fin 5 → ℝ) (spikeCoeff : ℝ)
    (hdependence :
      (∑ bottomIdx, bottomCoeff bottomIdx • atomMatrix (bottomDesign.atom bottomIdx))
        + spikeCoeff • atomMatrix spikeDirection = 0)
    (hspikePos : 0 < spikeCoeff) :
    atomMatrix spikeDirection
      = ∑ bottomIdx, (-(bottomCoeff bottomIdx) / spikeCoeff)
          • atomMatrix (bottomDesign.atom bottomIdx) := by
  have hspikeNonzero : spikeCoeff ≠ 0 := ne_of_gt hspikePos
  have hpullOut : ∑ bottomIdx, (-(bottomCoeff bottomIdx) / spikeCoeff)
        • atomMatrix (bottomDesign.atom bottomIdx)
      = (-spikeCoeff⁻¹) • ∑ bottomIdx, bottomCoeff bottomIdx
          • atomMatrix (bottomDesign.atom bottomIdx) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun bottomIdx _ => ?_
    rw [smul_smul]
    congr 1
    field_simp
  have hsolved : ∑ bottomIdx, bottomCoeff bottomIdx • atomMatrix (bottomDesign.atom bottomIdx)
      = -(spikeCoeff • atomMatrix spikeDirection) :=
    eq_neg_of_add_eq_zero_left hdependence
  rw [hpullOut, hsolved, smul_neg, neg_smul, neg_neg, smul_smul,
    inv_mul_cancel₀ hspikeNonzero, one_smul]

/-- **A spiked bottom cannot realize the shared line pair.**  Exactly the
hypotheses of `Gtz.EndpointBottomTieExclusionFiveThree` (dependence, full
support, positive spike coefficient, primitivity) plus two vanishing atom
brackets sharing a label -- and that is already contradictory.  Neither
stress-freeness nor the zero-sum condition is used. -/
theorem no_sharedLinePair_of_spikedBottom
    (bottomDesign : WeightedDesign 5 3) (spikeDirection : Fin 3 → ℝ)
    (bottomCoeff : Fin 5 → ℝ) (spikeCoeff : ℝ)
    (hdependence :
      (∑ bottomIdx, bottomCoeff bottomIdx • atomMatrix (bottomDesign.atom bottomIdx))
        + spikeCoeff • atomMatrix spikeDirection = 0)
    (hfullSupport : ∀ bottomIdx, bottomCoeff bottomIdx ≠ 0)
    (hspikePos : 0 < spikeCoeff)
    (hprimitive : IsPrimitiveDesign bottomDesign)
    (relabel : Equiv.Perm (Fin 5))
    (hfirstLine : atomBracket bottomDesign (relabel 0) (relabel 1) (relabel 2) = 0)
    (hsecondLine : atomBracket bottomDesign (relabel 0) (relabel 3) (relabel 4) = 0) :
    False := by
  classical
  set spikeShare : Fin 5 → ℝ := fun bottomIdx => -(bottomCoeff bottomIdx) / spikeCoeff
    with hspikeShareDef
  have hshareNonzero : ∀ bottomIdx, spikeShare bottomIdx ≠ 0 := fun bottomIdx =>
    div_ne_zero (neg_ne_zero.mpr (hfullSupport bottomIdx)) (ne_of_gt hspikePos)
  have hexpansion : atomMatrix spikeDirection
      = ∑ bottomIdx, spikeShare bottomIdx • atomMatrix (bottomDesign.atom bottomIdx) :=
    spikeExpansion_of_dependence bottomDesign spikeDirection bottomCoeff spikeCoeff
      hdependence hspikePos
  -- reindex the expansion and Parseval along the relabeling, then expand
  have hexpansionRelabelled : atomMatrix spikeDirection
      = spikeShare (relabel 0) • atomMatrix (bottomDesign.atom (relabel 0))
        + spikeShare (relabel 1) • atomMatrix (bottomDesign.atom (relabel 1))
        + spikeShare (relabel 2) • atomMatrix (bottomDesign.atom (relabel 2))
        + spikeShare (relabel 3) • atomMatrix (bottomDesign.atom (relabel 3))
        + spikeShare (relabel 4) • atomMatrix (bottomDesign.atom (relabel 4)) := by
    rw [hexpansion, ← Equiv.sum_comp relabel
      (fun bottomIdx => spikeShare bottomIdx • atomMatrix (bottomDesign.atom bottomIdx)),
      Fin.sum_univ_five]
  have hparsevalRelabelled :
      bottomDesign.weight (relabel 0) • atomMatrix (bottomDesign.atom (relabel 0))
        + bottomDesign.weight (relabel 1) • atomMatrix (bottomDesign.atom (relabel 1))
        + bottomDesign.weight (relabel 2) • atomMatrix (bottomDesign.atom (relabel 2))
        + bottomDesign.weight (relabel 3) • atomMatrix (bottomDesign.atom (relabel 3))
        + bottomDesign.weight (relabel 4) • atomMatrix (bottomDesign.atom (relabel 4)) = 1 := by
    rw [← Fin.sum_univ_five (fun slot =>
      bottomDesign.weight (relabel slot) • atomMatrix (bottomDesign.atom (relabel slot))),
      Equiv.sum_comp relabel
        (fun bottomIdx => bottomDesign.weight bottomIdx • atomMatrix (bottomDesign.atom bottomIdx))]
    exact bottomDesign.isParseval
  -- the two planes
  obtain ⟨planeNormalOne, hnormalOneNonzero, hnormalOneAll⟩ :=
    hasCommonOrthogonal_of_atomBracket_eq_zero bottomDesign (relabel 0) (relabel 1) (relabel 2)
      hfirstLine
  obtain ⟨planeNormalTwo, hnormalTwoNonzero, hnormalTwoAll⟩ :=
    hasCommonOrthogonal_of_atomBracket_eq_zero bottomDesign (relabel 0) (relabel 3) (relabel 4)
      hsecondLine
  have hflipOne : ∀ label ∈ ({relabel 0, relabel 1, relabel 2} : Finset (Fin 5)),
      planeNormalOne ⬝ᵥ bottomDesign.atom label = 0 := fun label hlabel => by
    rw [dotProduct_comm]; exact hnormalOneAll label hlabel
  have hflipTwo : ∀ label ∈ ({relabel 0, relabel 3, relabel 4} : Finset (Fin 5)),
      planeNormalTwo ⬝ᵥ bottomDesign.atom label = 0 := fun label hlabel => by
    rw [dotProduct_comm]; exact hnormalTwoAll label hlabel
  -- primitivity supplies the two non-parallel off-plane pairs
  have hthreeFourDistinct : relabel 3 ≠ relabel 4 :=
    relabel.injective.ne (by decide : (3 : Fin 5) ≠ 4)
  have honeTwoDistinct : relabel 1 ≠ relabel 2 :=
    relabel.injective.ne (by decide : (1 : Fin 5) ≠ 2)
  exact no_spike_of_sharedLinePair (bottomDesign.atom (relabel 0))
    (bottomDesign.atom (relabel 1)) (bottomDesign.atom (relabel 2))
    (bottomDesign.atom (relabel 3)) (bottomDesign.atom (relabel 4))
    (spikeShare (relabel 0)) (spikeShare (relabel 1)) (spikeShare (relabel 2))
    (spikeShare (relabel 3)) (spikeShare (relabel 4))
    (bottomDesign.weight (relabel 0)) (bottomDesign.weight (relabel 1))
    (bottomDesign.weight (relabel 2)) (bottomDesign.weight (relabel 3))
    (bottomDesign.weight (relabel 4))
    spikeDirection planeNormalOne planeNormalTwo hparsevalRelabelled hexpansionRelabelled
    (hshareNonzero _) (hshareNonzero _) (hshareNonzero _) (hshareNonzero _)
    (hflipOne _ (by simp)) (hflipOne _ (by simp)) (hflipOne _ (by simp))
    (hflipTwo _ (by simp)) (hflipTwo _ (by simp)) (hflipTwo _ (by simp))
    (fun ratio => hprimitive (relabel 3) (relabel 4) ratio hthreeFourDistinct)
    (atom_ne_zero_of_isPrimitiveDesign (by norm_num) bottomDesign hprimitive (relabel 3))
    (fun ratio => hprimitive (relabel 1) (relabel 2) ratio honeTwoDistinct)
    (atom_ne_zero_of_isPrimitiveDesign (by norm_num) bottomDesign hprimitive (relabel 1))
    hnormalOneNonzero hnormalTwoNonzero

/-! ## The residual, refactored

Copied verbatim from the endpoint artifact's definition, so that the reduction
below is a statement about the SAME Prop. -/

/-- **The matroid residual.**  Every primitive `(5,3)` tie carries two dependent
atom triples through a common atom -- the shared line pair.  Both of the tree's
primitive `(5,3)` ties satisfy this, with the same two triples `{0,1,3}` and
`{0,2,4}` sharing the atom `0`; and the rank-two shadow of the claim is the
tree's own `Gtz.RankTwoFourDirectionHinge`, whose evidence is one-sided. -/
def SharedLinePairAtEveryTieFiveThree : Prop :=
  ∀ bottomDesign : WeightedDesign 5 3, IsPrimitiveDesign bottomDesign → IsTie bottomDesign →
    ∃ relabel : Equiv.Perm (Fin 5),
      atomBracket bottomDesign (relabel 0) (relabel 1) (relabel 2) = 0
        ∧ atomBracket bottomDesign (relabel 0) (relabel 3) (relabel 4) = 0

/-- **THE REDUCTION.**  The endpoint residual follows from the matroid residual
alone.  The spike, the zero sum, the two non-parallelism clauses and the
stress-freeness clause of the target Prop are not consumed beyond the
dependence, its full support and the positive spike coefficient -- so what the
residual really asks is a question about the MATROID of a `(5,3)` tie, with no
gauge and no spike in it. -/
theorem endpointBottomTieExclusion_of_sharedLinePair
    (hshape : SharedLinePairAtEveryTieFiveThree) :
    EndpointBottomTieExclusionFiveThree := by
  intro bottomDesign spikeDirection bottomCoeff spikeCoeff hdependence hfullSupport
    hspikePos _hzeroSum hprimitive _hspikeNotBottom _hbottomNotSpike _hbottomFree htie
  obtain ⟨relabel, hfirstLine, hsecondLine⟩ := hshape bottomDesign hprimitive htie
  exact no_sharedLinePair_of_spikedBottom bottomDesign spikeDirection bottomCoeff spikeCoeff
    hdependence hfullSupport hspikePos hprimitive relabel hfirstLine hsecondLine

/-! ## Small kit: dependence versus the triple bracket, and common orthogonals -/

/-- **A nontrivial vanishing combination kills the triple bracket.**  Cofactor
expansion along the row whose coefficient survives. -/
theorem tripleBracket_eq_zero_of_dependence
    (leftVec midVec rightVec : Fin 3 → ℝ) (coeffLeft coeffMid coeffRight : ℝ)
    (hnontrivial : coeffLeft ≠ 0 ∨ coeffMid ≠ 0 ∨ coeffRight ≠ 0)
    (hvanish : coeffLeft • leftVec + coeffMid • midVec + coeffRight • rightVec = 0) :
    tripleBracket leftVec midVec rightVec = 0 := by
  have hcoord : ∀ coordIdx : Fin 3,
      coeffLeft * leftVec coordIdx + coeffMid * midVec coordIdx
        + coeffRight * rightVec coordIdx = 0 := by
    intro coordIdx
    have hentry := congrFun hvanish coordIdx
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hentry
  rcases hnontrivial with hleft | hmid | hright
  · have hkey : coeffLeft * tripleBracket leftVec midVec rightVec = 0 := by
      rw [tripleBracket_eq]
      linear_combination
        (midVec 1 * rightVec 2 - midVec 2 * rightVec 1) * hcoord 0
          - (midVec 0 * rightVec 2 - midVec 2 * rightVec 0) * hcoord 1
          + (midVec 0 * rightVec 1 - midVec 1 * rightVec 0) * hcoord 2
    exact (mul_eq_zero.mp hkey).resolve_left hleft
  · have hkey : coeffMid * tripleBracket leftVec midVec rightVec = 0 := by
      rw [tripleBracket_eq]
      linear_combination
        (-(leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1)) * hcoord 0
          + (leftVec 0 * rightVec 2 - leftVec 2 * rightVec 0) * hcoord 1
          - (leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0) * hcoord 2
    exact (mul_eq_zero.mp hkey).resolve_left hmid
  · have hkey : coeffRight * tripleBracket leftVec midVec rightVec = 0 := by
      rw [tripleBracket_eq]
      linear_combination
        (leftVec 1 * midVec 2 - leftVec 2 * midVec 1) * hcoord 0
          - (leftVec 0 * midVec 2 - leftVec 2 * midVec 0) * hcoord 1
          + (leftVec 0 * midVec 1 - leftVec 1 * midVec 0) * hcoord 2
    exact (mul_eq_zero.mp hkey).resolve_left hright

/-- Two vectors of `R^3` always share a nonzero orthogonal direction. -/
theorem exists_commonOrthogonal_pair (leftVec rightVec : Fin 3 → ℝ) :
    ∃ normal : Fin 3 → ℝ, normal ≠ 0
      ∧ leftVec ⬝ᵥ normal = 0 ∧ rightVec ⬝ᵥ normal = 0 := by
  have hdet : (Matrix.of ![leftVec, rightVec, (0 : Fin 3 → ℝ)]).det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero 2 fun colIdx => ?_
    simp [Matrix.cons_val_two, Matrix.tail_cons]
  obtain ⟨normal, hnormalNe, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨normal, hnormalNe, ?_, ?_⟩
  · simpa [Matrix.mulVec, dotProduct] using congrFun hkernel 0
  · simpa [Matrix.mulVec, dotProduct] using congrFun hkernel 1

/-! ## The cover-to-shape combinatorics on five labels

The hinge output at a dual tie is a COVER: every four of the five dual labels
contain a bracket-zero pair.  Two shapes exhaust the covers with no two
disjoint edges eliminated: a two-edge matching, or a full triangle. -/

/-- Any label of `Fin 5` has four pairwise distinct translates avoiding it. -/
theorem fin_five_translates_distinct : ∀ excluded : Fin 5,
    excluded + 1 ≠ excluded + 2 ∧ excluded + 1 ≠ excluded + 3
      ∧ excluded + 1 ≠ excluded + 4 ∧ excluded + 2 ≠ excluded + 3
      ∧ excluded + 2 ≠ excluded + 4 ∧ excluded + 3 ≠ excluded + 4
      ∧ excluded + 1 ≠ excluded ∧ excluded + 2 ≠ excluded
      ∧ excluded + 3 ≠ excluded ∧ excluded + 4 ≠ excluded := by
  decide

/-- **Matching or triangle.**  A symmetric relation on `Fin 5` meeting every
quadruple either contains two disjoint edges or contains a full triangle. -/
theorem matching_or_triangle_of_coveringEdges (edge : Fin 5 → Fin 5 → Prop)
    (hsymm : ∀ leftIdx rightIdx, edge leftIdx rightIdx → edge rightIdx leftIdx)
    (hfour : ∀ quadA quadB quadC quadD : Fin 5,
      quadA ≠ quadB → quadA ≠ quadC → quadA ≠ quadD →
      quadB ≠ quadC → quadB ≠ quadD → quadC ≠ quadD →
      edge quadA quadB ∨ edge quadA quadC ∨ edge quadA quadD
        ∨ edge quadB quadC ∨ edge quadB quadD ∨ edge quadC quadD) :
    (∃ matchAFst matchASnd matchBFst matchBSnd : Fin 5,
        matchAFst ≠ matchASnd ∧ matchBFst ≠ matchBSnd
          ∧ matchAFst ≠ matchBFst ∧ matchAFst ≠ matchBSnd
          ∧ matchASnd ≠ matchBFst ∧ matchASnd ≠ matchBSnd
          ∧ edge matchAFst matchASnd ∧ edge matchBFst matchBSnd)
      ∨ (∃ triA triB triC : Fin 5, triA ≠ triB ∧ triA ≠ triC ∧ triB ≠ triC
          ∧ edge triA triB ∧ edge triA triC ∧ edge triB triC) := by
  classical
  -- an edge avoiding any prescribed label
  have havoiding : ∀ excluded : Fin 5, ∃ endFst endSnd : Fin 5,
      endFst ≠ endSnd ∧ endFst ≠ excluded ∧ endSnd ≠ excluded ∧ edge endFst endSnd := by
    intro excluded
    obtain ⟨h12, h13, h14, h23, h24, h34, h1x, h2x, h3x, h4x⟩ :=
      fin_five_translates_distinct excluded
    rcases hfour (excluded + 1) (excluded + 2) (excluded + 3) (excluded + 4)
        h12 h13 h14 h23 h24 h34 with
      hedge | hedge | hedge | hedge | hedge | hedge
    · exact ⟨excluded + 1, excluded + 2, h12, h1x, h2x, hedge⟩
    · exact ⟨excluded + 1, excluded + 3, h13, h1x, h3x, hedge⟩
    · exact ⟨excluded + 1, excluded + 4, h14, h1x, h4x, hedge⟩
    · exact ⟨excluded + 2, excluded + 3, h23, h2x, h3x, hedge⟩
    · exact ⟨excluded + 2, excluded + 4, h24, h2x, h4x, hedge⟩
    · exact ⟨excluded + 3, excluded + 4, h34, h3x, h4x, hedge⟩
  -- a seed edge
  obtain ⟨seedFst, seedSnd, hseedNe, -, -, hseedEdge⟩ := havoiding 0
  by_cases hmatch : ∃ matchAFst matchASnd matchBFst matchBSnd : Fin 5,
      matchAFst ≠ matchASnd ∧ matchBFst ≠ matchBSnd
        ∧ matchAFst ≠ matchBFst ∧ matchAFst ≠ matchBSnd
        ∧ matchASnd ≠ matchBFst ∧ matchASnd ≠ matchBSnd
        ∧ edge matchAFst matchASnd ∧ edge matchBFst matchBSnd
  · exact Or.inl hmatch
  -- no two disjoint edges: every edge meets the seed edge
  have hmeets : ∀ endFst endSnd : Fin 5, endFst ≠ endSnd → edge endFst endSnd →
      endFst = seedFst ∨ endFst = seedSnd ∨ endSnd = seedFst ∨ endSnd = seedSnd := by
    intro endFst endSnd hne hedge
    by_contra hnone
    push Not at hnone
    obtain ⟨hfs1, hfs2, hss1, hss2⟩ := hnone
    exact hmatch ⟨seedFst, seedSnd, endFst, endSnd, hseedNe, hne, Ne.symm hfs1,
      Ne.symm hss1, Ne.symm hfs2, Ne.symm hss2, hseedEdge, hedge⟩
  -- the edge avoiding seedFst passes through seedSnd
  obtain ⟨avoidFst, avoidSnd, hane, hafs, hasf, haedge⟩ := havoiding seedFst
  have hthroughSnd : ∃ spoke : Fin 5, spoke ≠ seedFst ∧ spoke ≠ seedSnd
      ∧ edge spoke seedSnd := by
    rcases hmeets avoidFst avoidSnd hane haedge with hfs | hfs | hss | hss
    · exact absurd hfs hafs
    · refine ⟨avoidSnd, hasf, ?_, ?_⟩
      · rw [← hfs]; exact (Ne.symm hane)
      · rw [← hfs]; exact hsymm _ _ haedge
    · exact absurd hss hasf
    · refine ⟨avoidFst, hafs, ?_, ?_⟩
      · rw [← hss]; exact hane
      · rw [← hss]; exact haedge
  -- the edge avoiding seedSnd passes through seedFst
  obtain ⟨avoidFst', avoidSnd', hane', hafs', hasf', haedge'⟩ := havoiding seedSnd
  have hthroughFst : ∃ spoke : Fin 5, spoke ≠ seedFst ∧ spoke ≠ seedSnd
      ∧ edge spoke seedFst := by
    rcases hmeets avoidFst' avoidSnd' hane' haedge' with hfs | hfs | hss | hss
    · refine ⟨avoidSnd', ?_, hasf', ?_⟩
      · rw [← hfs]; exact (Ne.symm hane')
      · rw [← hfs]; exact hsymm _ _ haedge'
    · exact absurd hfs hafs'
    · refine ⟨avoidFst', ?_, hafs', ?_⟩
      · rw [← hss]; exact hane'
      · rw [← hss]; exact haedge'
    · exact absurd hss hasf'
  obtain ⟨spokeSnd, hspokeSndFst, hspokeSndSnd, hspokeSndEdge⟩ := hthroughSnd
  obtain ⟨spokeFst, hspokeFstFst, hspokeFstSnd, hspokeFstEdge⟩ := hthroughFst
  -- the two spokes coincide, closing the triangle
  have hspokesEq : spokeSnd = spokeFst := by
    by_contra hspokes
    exact hmatch ⟨spokeSnd, seedSnd, spokeFst, seedFst, hspokeSndSnd, hspokeFstFst,
      hspokes, hspokeSndFst, Ne.symm hspokeFstSnd, Ne.symm hseedNe,
      hspokeSndEdge, hspokeFstEdge⟩
  refine Or.inr ⟨seedFst, seedSnd, spokeSnd, hseedNe, Ne.symm hspokeSndFst,
    Ne.symm hspokeSndSnd, hseedEdge, ?_, hsymm _ _ hspokeSndEdge⟩
  rw [hspokesEq]
  exact hsymm _ _ hspokeFstEdge

end EndpointSpike
