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

The diamond's stress-freeness is now a KERNEL theorem —
`Gtz.diamondDesign_atomMatrices_linearIndependent`
(Gtz/Design/StressFreeClosureFailure.lean); the second design remains verified
in exact rational arithmetic outside the kernel, primitive and stress-free
with exactly those two dependent triples and no others.  So the theorem below
excludes every `(5,3)` tie the campaign knows.

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

/-! ## The residual

The target Prop is the tree's `Gtz.EndpointBottomTieExclusionFiveThree`
(defined in `Gtz.Reduction.EndpointGaugeDescent` and visible here through
`open Gtz`), so the reduction and the closure below are statements about the
SAME Prop the endpoint chain consumes. -/

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

/-! ## The explicit Naimark dual at `(5,3)`, with the bracket dictionary

`Gtz.weighted_naimark_duality` ships the dual design but keeps its atoms
opaque, so nothing can be said about their PARALLELISM.  The residual needs
exactly that: a dual whose bracket-zero pairs certify primal dependent
triples.  The construction below replays the shipped one — whitener of the
co-Parseval operator, slack-scaled co-design rows, orthonormal completion,
weight-rescaled dual atoms — and exports the two facts the endgame consumes:

* **the dictionary**: a vanishing dual pair bracket yields a nontrivial
  primal atom dependence supported off the pair;
* **the transfer**: a strictly dominating dual pair yields a strictly
  dominating primal triple (its complement).

The completion columns span the orthocomplement of the co-design columns, so
a dual parallel pair gives a kernel vector of the co-design transpose
vanishing at both labels — a dependence of the three complementary atoms.
That is the classical Gale dictionary, and it was verified exactly, all ten
pairs, on both shipped `(5,3)` ties before being mechanized here. -/

/-- **The dictionary half.**  All construction data passed explicitly. -/
theorem dependence_of_dualPairBracket_eq_zero (D : WeightedDesign 5 3)
    (whitener : Matrix (Fin 3) (Fin 3) ℝ) (hwhitenerUnit : IsUnit whitener.det)
    (coDesign : Matrix (Fin 5) (Fin 3) ℝ)
    (hcoDesignShape : ∀ (label : Fin 5) (coordIdx : Fin 3), coDesign label coordIdx
        = Real.sqrt (1 - D.weight label) * (whitenerᵀ *ᵥ D.atom label) coordIdx)
    (completion : Matrix (Fin 5) (Fin 2) ℝ)
    (hcompletionOrtho : completionᵀ * completion = 1)
    (hcoDesignPerp : coDesignᵀ * completion = 0)
    (dualDesign : WeightedDesign 5 2)
    (hdualAtom : ∀ label : Fin 5, dualDesign.atom label
        = (Real.sqrt (D.weight label))⁻¹ • (fun colIdx => completion label colIdx))
    (pairFst pairSnd : Fin 5)
    (hbracket : pairBracket dualDesign pairFst pairSnd = 0) :
    ∃ dependence : Fin 5 → ℝ,
      (∃ witnessLabel, dependence witnessLabel ≠ 0)
        ∧ dependence pairFst = 0 ∧ dependence pairSnd = 0
        ∧ (∑ label, dependence label • D.atom label) = 0 := by
  classical
  have hslackPos : ∀ label : Fin 5, 0 < 1 - D.weight label := fun label => by
    linarith [weight_lt_one D (by norm_num) label]
  have hrootPos : ∀ label : Fin 5, 0 < Real.sqrt (D.weight label) := fun label =>
    Real.sqrt_pos.mpr (D.weight_pos label)
  -- the completion rows of the pair are dependent
  have hcompletionDet : completion pairFst 0 * completion pairSnd 1
      - completion pairFst 1 * completion pairSnd 0 = 0 := by
    have hexpand : pairBracket dualDesign pairFst pairSnd
        = (Real.sqrt (D.weight pairFst))⁻¹ * (Real.sqrt (D.weight pairSnd))⁻¹
          * (completion pairFst 0 * completion pairSnd 1
              - completion pairFst 1 * completion pairSnd 0) := by
      rw [pairBracket, hdualAtom pairFst, hdualAtom pairSnd]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hexpand] at hbracket
    rcases mul_eq_zero.mp hbracket with hscale | hdet
    · exfalso
      rcases mul_eq_zero.mp hscale with hfst | hsnd
      · exact (inv_ne_zero (hrootPos pairFst).ne') hfst
      · exact (inv_ne_zero (hrootPos pairSnd).ne') hsnd
    · exact hdet
  -- a common orthogonal of the two completion rows
  obtain ⟨mixCoeff, hmixNe, hrowFst, hrowSnd⟩ :
      ∃ mixCoeff : Fin 2 → ℝ, mixCoeff ≠ 0
        ∧ completion pairFst 0 * mixCoeff 0 + completion pairFst 1 * mixCoeff 1 = 0
        ∧ completion pairSnd 0 * mixCoeff 0 + completion pairSnd 1 * mixCoeff 1 = 0 := by
    by_cases hfstLive : completion pairFst 0 ≠ 0 ∨ completion pairFst 1 ≠ 0
    · refine ⟨![completion pairFst 1, -(completion pairFst 0)], ?_, ?_, ?_⟩
      · intro hzero
        rcases hfstLive with hone | htwo
        · refine hone ?_
          have hentry := congrFun hzero 1
          simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
            neg_eq_zero] at hentry
          exact hentry
        · refine htwo ?_
          have hentry := congrFun hzero 0
          simp only [Matrix.cons_val_zero, Pi.zero_apply] at hentry
          exact hentry
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith [hcompletionDet]
    · push Not at hfstLive
      obtain ⟨hfstZeroA, hfstZeroB⟩ := hfstLive
      by_cases hsndLive : completion pairSnd 0 ≠ 0 ∨ completion pairSnd 1 ≠ 0
      · refine ⟨![completion pairSnd 1, -(completion pairSnd 0)], ?_, ?_, ?_⟩
        · intro hzero
          rcases hsndLive with hone | htwo
          · refine hone ?_
            have hentry := congrFun hzero 1
            simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
              neg_eq_zero] at hentry
            exact hentry
          · refine htwo ?_
            have hentry := congrFun hzero 0
            simp only [Matrix.cons_val_zero, Pi.zero_apply] at hentry
            exact hentry
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          rw [hfstZeroA, hfstZeroB]
          ring
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          ring
      · push Not at hsndLive
        obtain ⟨hsndZeroA, hsndZeroB⟩ := hsndLive
        refine ⟨![1, 0], ?_, ?_, ?_⟩
        · intro hzero
          have hentry := congrFun hzero 0
          simp only [Matrix.cons_val_zero, Pi.zero_apply] at hentry
          exact one_ne_zero hentry
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          rw [hfstZeroA, hfstZeroB]
          ring
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          rw [hsndZeroA, hsndZeroB]
          ring
  -- the kernel vector of the co-design transpose
  set kernelVec : Fin 5 → ℝ := completion *ᵥ mixCoeff with hkernelVecDef
  have hkernelFst : kernelVec pairFst = 0 := by
    rw [hkernelVecDef]
    show ∑ colIdx, completion pairFst colIdx * mixCoeff colIdx = 0
    rw [Fin.sum_univ_two]
    exact hrowFst
  have hkernelSnd : kernelVec pairSnd = 0 := by
    rw [hkernelVecDef]
    show ∑ colIdx, completion pairSnd colIdx * mixCoeff colIdx = 0
    rw [Fin.sum_univ_two]
    exact hrowSnd
  have hkernelNe : kernelVec ≠ 0 := by
    intro hzero
    refine hmixNe ?_
    have hpull := congrArg (fun vec => completionᵀ *ᵥ vec) hzero
    simp only [Matrix.mulVec_zero] at hpull
    rwa [hkernelVecDef, Matrix.mulVec_mulVec, hcompletionOrtho, Matrix.one_mulVec] at hpull
  have hcoKernel : coDesignᵀ *ᵥ kernelVec = 0 := by
    rw [hkernelVecDef, Matrix.mulVec_mulVec, hcoDesignPerp, Matrix.zero_mulVec]
  -- the dependence, with the slack roots folded in
  refine ⟨fun label => kernelVec label * Real.sqrt (1 - D.weight label), ?_, ?_, ?_, ?_⟩
  · obtain ⟨witnessLabel, hwitness⟩ := Function.ne_iff.mp hkernelNe
    simp only [Pi.zero_apply] at hwitness
    exact ⟨witnessLabel,
      mul_ne_zero hwitness (Real.sqrt_pos.mpr (hslackPos witnessLabel)).ne'⟩
  · show kernelVec pairFst * Real.sqrt (1 - D.weight pairFst) = 0
    rw [hkernelFst, zero_mul]
  · show kernelVec pairSnd * Real.sqrt (1 - D.weight pairSnd) = 0
    rw [hkernelSnd, zero_mul]
  · -- the whitener transports the co-design kernel to the atom dependence
    have hcoordZero : ∀ coordIdx : Fin 3,
        ∑ label, (kernelVec label * Real.sqrt (1 - D.weight label))
          * (whitenerᵀ *ᵥ D.atom label) coordIdx = 0 := by
      intro coordIdx
      have hentry := congrFun hcoKernel coordIdx
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hentry
      rw [← hentry]
      refine Finset.sum_congr rfl fun label _ => ?_
      rw [hcoDesignShape label coordIdx]
      ring
    have hwhitenedSum : whitenerᵀ *ᵥ (∑ label,
        (kernelVec label * Real.sqrt (1 - D.weight label)) • D.atom label) = 0 := by
      rw [← Matrix.mulVecLin_apply, map_sum]
      funext coordIdx
      simp only [Finset.sum_apply, LinearMap.map_smul, Matrix.mulVecLin_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hcoordZero coordIdx
    by_contra hsumNe
    have hdetZero : (whitenerᵀ).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hsumNe, hwhitenedSum⟩
    rw [Matrix.det_transpose] at hdetZero
    exact (isUnit_iff_ne_zero.mp hwhitenerUnit) hdetZero

/-- **The transfer half**: a strictly dominating dual pair complements to a
strictly dominating primal triple.  The shipped four-congruence chain, walked
once, in the definite verdict, in the dual-to-primal direction. -/
theorem posDef_primalGap_of_posDef_dualPairGap (D : WeightedDesign 5 3)
    (whitener : Matrix (Fin 3) (Fin 3) ℝ) (hwhitenerUnit : IsUnit whitener.det)
    (hwhitened : whitenerᵀ * (∑ label, (1 - D.weight label) • atomMatrix (D.atom label))
        * whitener = 1)
    (coDesign : Matrix (Fin 5) (Fin 3) ℝ)
    (hcoDesignShape : ∀ (label : Fin 5) (coordIdx : Fin 3), coDesign label coordIdx
        = Real.sqrt (1 - D.weight label) * (whitenerᵀ *ᵥ D.atom label) coordIdx)
    (completion : Matrix (Fin 5) (Fin 2) ℝ)
    (hcomplete : coDesign * coDesignᵀ + completion * completionᵀ = 1)
    (dualDesign : WeightedDesign 5 2)
    (hdualAtom : ∀ label : Fin 5, dualDesign.atom label
        = (Real.sqrt (D.weight label))⁻¹ • (fun colIdx => completion label colIdx))
    (dualPair : Finset (Fin 5)) (hpairCard : dualPair.card = 2)
    (hdom : (Gtz.subsetSum dualDesign dualPair - 1).PosDef) :
    (Gtz.subsetSum D dualPairᶜ - 1).PosDef := by
  classical
  have hslackPos : ∀ label : Fin 5, 0 < 1 - D.weight label := fun label => by
    linarith [weight_lt_one D (by norm_num) label]
  have hrootPos : ∀ label : Fin 5, 0 < Real.sqrt (D.weight label) := fun label =>
    Real.sqrt_pos.mpr (D.weight_pos label)
  -- the pair enumeration and the two stacked row matrices
  set enumPair : Fin 2 → Fin 5 :=
    fun slotIdx => ((dualPair.orderIsoOfFin hpairCard) slotIdx).val with henumPairDef
  have henumMem : ∀ slotIdx, enumPair slotIdx ∈ dualPair := fun slotIdx =>
    ((dualPair.orderIsoOfFin hpairCard) slotIdx).2
  have henumInj : Function.Injective enumPair := fun slotIdx slotIdx' heq =>
    (dualPair.orderIsoOfFin hpairCard).toEquiv.injective (Subtype.val_injective heq)
  set whitenedRows : Matrix (Fin 2) (Fin 3) ℝ :=
    Matrix.of (fun slotIdx coordIdx =>
      (whitenerᵀ *ᵥ D.atom (enumPair slotIdx)) coordIdx) with hwhitenedRowsDef
  set dualRows : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.of (fun slotIdx colIdx =>
      (Real.sqrt (D.weight (enumPair slotIdx)))⁻¹ * completion (enumPair slotIdx) colIdx)
    with hdualRowsDef
  -- STEP 0: the complement dictionary
  have hgapSplit : Gtz.subsetSum D dualPairᶜ - 1
      = (∑ label, (1 - D.weight label) • atomMatrix (D.atom label))
        - Gtz.subsetSum D dualPair := by
    have hweightless : (∑ label, (1 - D.weight label) • atomMatrix (D.atom label))
        = (∑ label, atomMatrix (D.atom label)) - 1 := by
      rw [← D.isParseval, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun label _ => by rw [sub_smul, one_smul]
    have htotalSplit : (∑ label, atomMatrix (D.atom label))
        = Gtz.subsetSum D dualPair + Gtz.subsetSum D dualPairᶜ :=
      (Finset.sum_add_sum_compl dualPair _).symm
    rw [hweightless, htotalSplit]
    abel
  -- STEP 1: congruence by the whitener
  have hcoParsevalSymm : ((∑ label, (1 - D.weight label) • atomMatrix (D.atom label))
      - Gtz.subsetSum D dualPair)ᵀ
      = (∑ label, (1 - D.weight label) • atomMatrix (D.atom label))
        - Gtz.subsetSum D dualPair := by
    rw [Matrix.transpose_sub, Matrix.transpose_sum, Gtz.subsetSum, Matrix.transpose_sum]
    congr 1
    · exact Finset.sum_congr rfl fun label _ => by
        rw [Matrix.transpose_smul,
          transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom label)).1]
    · exact Finset.sum_congr rfl fun label _ =>
        transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom label)).1
  have hwhitenerConj : whitenerᵀ
      * ((∑ label, (1 - D.weight label) • atomMatrix (D.atom label))
          - Gtz.subsetSum D dualPair) * whitener
      = 1 - whitenedRowsᵀ * whitenedRows := by
    have hrowsGram : whitenedRowsᵀ * whitenedRows
        = ∑ label ∈ dualPair, atomMatrix (whitenerᵀ *ᵥ D.atom label) := by
      rw [transpose_mul_self_eq_sum_rows,
        ← sum_orderIsoOfFin dualPair hpairCard
          (fun label => atomMatrix (whitenerᵀ *ᵥ D.atom label))]
      exact Finset.sum_congr rfl fun slotIdx _ =>
        congrArg atomMatrix (funext fun coordIdx => by
          simp [hwhitenedRowsDef, henumPairDef])
    have hconjSum : whitenerᵀ * Gtz.subsetSum D dualPair * whitener
        = ∑ label ∈ dualPair, atomMatrix (whitenerᵀ *ᵥ D.atom label) := by
      rw [Gtz.subsetSum, Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl fun label _ => transpose_mul_atomMatrix_mul whitener _
    rw [Matrix.mul_sub, Matrix.sub_mul, hwhitened, hconjSum, hrowsGram]
  -- STEP 2 entries: the co-design and completion Gram formulas
  have hcoGramEntry : ∀ label label' : Fin 5, (coDesign * coDesignᵀ) label label'
      = Real.sqrt (1 - D.weight label) * Real.sqrt (1 - D.weight label')
        * ((whitenerᵀ *ᵥ D.atom label) ⬝ᵥ (whitenerᵀ *ᵥ D.atom label')) := by
    intro label label'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun coordIdx _ => ?_
    rw [hcoDesignShape label coordIdx, hcoDesignShape label' coordIdx]
    ring
  have hwhitenedGramEntry : ∀ slotIdx slotIdx' : Fin 2,
      (whitenedRows * whitenedRowsᵀ) slotIdx slotIdx'
        = (whitenerᵀ *ᵥ D.atom (enumPair slotIdx))
            ⬝ᵥ (whitenerᵀ *ᵥ D.atom (enumPair slotIdx')) := by
    intro slotIdx slotIdx'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hwhitenedRowsDef,
      Matrix.of_apply, dotProduct]
  have hdualGramEntry : ∀ slotIdx slotIdx' : Fin 2,
      (dualRows * dualRowsᵀ) slotIdx slotIdx'
        = (Real.sqrt (D.weight (enumPair slotIdx)))⁻¹
          * (Real.sqrt (D.weight (enumPair slotIdx')))⁻¹
          * ∑ colIdx, completion (enumPair slotIdx) colIdx
              * completion (enumPair slotIdx') colIdx := by
    intro slotIdx slotIdx'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hdualRowsDef,
      Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun colIdx _ => by ring
  -- STEP 2: diagonal congruence by the slack roots
  have hdiagSlack : (Matrix.diagonal
        (fun slotIdx => Real.sqrt (1 - D.weight (enumPair slotIdx))))ᵀ
        * (1 - whitenedRows * whitenedRowsᵀ)
        * Matrix.diagonal (fun slotIdx => Real.sqrt (1 - D.weight (enumPair slotIdx)))
      = Matrix.diagonal (fun slotIdx => 1 - D.weight (enumPair slotIdx))
        - Matrix.of (fun slotIdx slotIdx' =>
            (coDesign * coDesignᵀ) (enumPair slotIdx) (enumPair slotIdx')) := by
    rw [Matrix.diagonal_transpose]
    ext slotIdx slotIdx'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.of_apply]
    rw [hwhitenedGramEntry slotIdx slotIdx', hcoGramEntry (enumPair slotIdx) (enumPair slotIdx')]
    rcases eq_or_ne slotIdx slotIdx' with rfl | hne
    · rw [if_pos rfl, if_pos rfl]
      have hss := Real.mul_self_sqrt (hslackPos (enumPair slotIdx)).le
      linear_combination hss
    · rw [if_neg hne, if_neg hne]
      ring
  -- STEP 3: completeness swaps the co-design block for the completion block
  have hcompleteEntry : ∀ slotIdx slotIdx' : Fin 2,
      (coDesign * coDesignᵀ) (enumPair slotIdx) (enumPair slotIdx')
        + (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx')
      = if slotIdx = slotIdx' then 1 else 0 := by
    intro slotIdx slotIdx'
    have hentry := congrFun (congrFun hcomplete (enumPair slotIdx)) (enumPair slotIdx')
    rw [Matrix.add_apply, Matrix.one_apply] at hentry
    rwa [if_congr ⟨fun heq => henumInj heq, fun heq => heq ▸ rfl⟩ rfl rfl] at hentry
  have hblockSwap : Matrix.diagonal (fun slotIdx => 1 - D.weight (enumPair slotIdx))
        - Matrix.of (fun slotIdx slotIdx' =>
            (coDesign * coDesignᵀ) (enumPair slotIdx) (enumPair slotIdx'))
      = Matrix.of (fun slotIdx slotIdx' =>
            (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx'))
        - Matrix.diagonal (fun slotIdx => D.weight (enumPair slotIdx)) := by
    ext slotIdx slotIdx'
    simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply]
    have hentry := hcompleteEntry slotIdx slotIdx'
    rcases eq_or_ne slotIdx slotIdx' with rfl | hne
    · rw [if_pos rfl] at hentry
      rw [if_pos rfl, if_pos rfl]
      linarith
    · rw [if_neg hne] at hentry
      rw [if_neg hne, if_neg hne]
      linarith
  -- STEP 4: diagonal congruence by the inverse weight roots
  have hdiagWeight : (Matrix.diagonal
        (fun slotIdx => (Real.sqrt (D.weight (enumPair slotIdx)))⁻¹))ᵀ
        * (Matrix.of (fun slotIdx slotIdx' =>
              (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx'))
            - Matrix.diagonal (fun slotIdx => D.weight (enumPair slotIdx)))
        * Matrix.diagonal (fun slotIdx => (Real.sqrt (D.weight (enumPair slotIdx)))⁻¹)
      = dualRows * dualRowsᵀ - 1 := by
    rw [Matrix.diagonal_transpose]
    ext slotIdx slotIdx'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.of_apply]
    rw [hdualGramEntry slotIdx slotIdx',
      show (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx')
          = ∑ colIdx, completion (enumPair slotIdx) colIdx
              * completion (enumPair slotIdx') colIdx from by
        simp [Matrix.mul_apply, Matrix.transpose_apply]]
    rcases eq_or_ne slotIdx slotIdx' with rfl | hne
    · rw [if_pos rfl, if_pos rfl]
      have hroot := Real.mul_self_sqrt (D.weight_pos (enumPair slotIdx)).le
      have hcancel : (Real.sqrt (D.weight (enumPair slotIdx)))⁻¹
          * D.weight (enumPair slotIdx)
          * (Real.sqrt (D.weight (enumPair slotIdx)))⁻¹ = 1 := by
        rw [show (Real.sqrt (D.weight (enumPair slotIdx)))⁻¹
              * D.weight (enumPair slotIdx)
              * (Real.sqrt (D.weight (enumPair slotIdx)))⁻¹
            = D.weight (enumPair slotIdx) * (Real.sqrt (D.weight (enumPair slotIdx))
                * Real.sqrt (D.weight (enumPair slotIdx)))⁻¹ from by
          rw [mul_inv]; ring,
          hroot, mul_inv_cancel₀ (D.weight_pos (enumPair slotIdx)).ne']
      linear_combination (-1 : ℝ) * hcancel
    · rw [if_neg hne, if_neg hne]
      ring
  -- STEP 5: the dual rows realize the dual subset sum
  have hdualRowsGram : dualRowsᵀ * dualRows = Gtz.subsetSum dualDesign dualPair := by
    rw [transpose_mul_self_eq_sum_rows, Gtz.subsetSum,
      ← sum_orderIsoOfFin dualPair hpairCard
        (fun label => atomMatrix (dualDesign.atom label))]
    refine Finset.sum_congr rfl fun slotIdx _ =>
      congrArg atomMatrix (funext fun colIdx => ?_)
    rw [hdualAtom (enumPair slotIdx)]
    simp [hdualRowsDef, henumPairDef, Pi.smul_apply, smul_eq_mul]
  -- symmetry and determinant side conditions
  have hgapSymmOne : (1 - whitenedRows * whitenedRowsᵀ)ᵀ
      = 1 - whitenedRows * whitenedRowsᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hcompletionGramSymm : (completion * completionᵀ)ᵀ = completion * completionᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hgapSymmTwo : (Matrix.of (fun slotIdx slotIdx' =>
          (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx'))
        - Matrix.diagonal (fun slotIdx => D.weight (enumPair slotIdx)))ᵀ
      = Matrix.of (fun slotIdx slotIdx' =>
            (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx'))
        - Matrix.diagonal (fun slotIdx => D.weight (enumPair slotIdx)) := by
    rw [Matrix.transpose_sub, Matrix.diagonal_transpose]
    congr 1
    ext slotIdx slotIdx'
    rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
    have hsym := congrFun (congrFun hcompletionGramSymm (enumPair slotIdx)) (enumPair slotIdx')
    rw [Matrix.transpose_apply] at hsym
    exact hsym
  have hdetSlack : IsUnit (Matrix.diagonal
      (fun slotIdx => Real.sqrt (1 - D.weight (enumPair slotIdx)))).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun slotIdx _ =>
      (Real.sqrt_pos.mpr (hslackPos (enumPair slotIdx))).ne'
  have hdetWeight : IsUnit (Matrix.diagonal
      (fun slotIdx => (Real.sqrt (D.weight (enumPair slotIdx)))⁻¹)).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun slotIdx _ =>
      inv_ne_zero (hrootPos (enumPair slotIdx)).ne'
  -- the chain, dual to primal, in the definite verdict
  have hstepSix : (dualRowsᵀ * dualRows - 1).PosDef := by
    rw [hdualRowsGram]
    exact hdom
  have hstepFive : (dualRows * dualRowsᵀ - 1).PosDef :=
    (posDef_transpose_mul_sub_one_comm dualRows).mp hstepSix
  have hstepFour : (Matrix.of (fun slotIdx slotIdx' =>
        (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx'))
      - Matrix.diagonal (fun slotIdx => D.weight (enumPair slotIdx))).PosDef :=
    (posDef_congr_right hgapSymmTwo hdetWeight).mpr (by rw [hdiagWeight]; exact hstepFive)
  have hstepThree : (1 - whitenedRows * whitenedRowsᵀ).PosDef :=
    (posDef_congr_right hgapSymmOne hdetSlack).mpr
      (by rw [hdiagSlack, hblockSwap]; exact hstepFour)
  have hstepTwo : (1 - whitenedRowsᵀ * whitenedRows).PosDef :=
    (posDef_one_sub_transpose_comm whitenedRows).mpr hstepThree
  have hstepOne : ((∑ label, (1 - D.weight label) • atomMatrix (D.atom label))
      - Gtz.subsetSum D dualPair).PosDef :=
    (posDef_congr_right hcoParsevalSymm hwhitenerUnit).mpr
      (by rw [hwhitenerConj]; exact hstepTwo)
  rw [hgapSplit]
  exact hstepOne

/-- **The packaged dual.**  Every `(5,3)` design has an explicit Naimark dual
carrying both the bracket dictionary and the strict-domination transfer. -/
theorem exists_naimarkDual_with_bracketDictionary (D : WeightedDesign 5 3) :
    ∃ dualDesign : WeightedDesign 5 2,
      (∀ pairFst pairSnd : Fin 5, pairBracket dualDesign pairFst pairSnd = 0 →
        ∃ dependence : Fin 5 → ℝ,
          (∃ witnessLabel, dependence witnessLabel ≠ 0)
            ∧ dependence pairFst = 0 ∧ dependence pairSnd = 0
            ∧ (∑ label, dependence label • D.atom label) = 0)
        ∧ ∀ dualPair : Finset (Fin 5), dualPair.card = 2 →
            (Gtz.subsetSum dualDesign dualPair - 1).PosDef →
            (Gtz.subsetSum D dualPairᶜ - 1).PosDef := by
  classical
  have hslackPos : ∀ label : Fin 5, 0 < 1 - D.weight label := fun label => by
    linarith [weight_lt_one D (by norm_num) label]
  obtain ⟨whitener, hwhitenerUnit, hwhitened⟩ :=
    exists_congruence_to_one (coParseval_posDef D (by norm_num))
  set coDesign : Matrix (Fin 5) (Fin 3) ℝ :=
    Matrix.of (fun label coordIdx =>
      Real.sqrt (1 - D.weight label) * (whitenerᵀ *ᵥ D.atom label) coordIdx)
    with hcoDesignDef
  have hcoDesignShape : ∀ (label : Fin 5) (coordIdx : Fin 3), coDesign label coordIdx
      = Real.sqrt (1 - D.weight label) * (whitenerᵀ *ᵥ D.atom label) coordIdx :=
    fun label coordIdx => rfl
  have hconjSum : whitenerᵀ * (∑ label, (1 - D.weight label) • atomMatrix (D.atom label))
      * whitener
      = ∑ label, (1 - D.weight label) • atomMatrix (whitenerᵀ *ᵥ D.atom label) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, transpose_mul_atomMatrix_mul]
  have hcoDesignOrtho : coDesignᵀ * coDesign = 1 := by
    rw [← hwhitened, hconjSum]
    ext coordIdx coordIdx'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hcoDesignDef, Matrix.of_apply,
      Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [show Real.sqrt (1 - D.weight label) * (whitenerᵀ *ᵥ D.atom label) coordIdx
          * (Real.sqrt (1 - D.weight label) * (whitenerᵀ *ᵥ D.atom label) coordIdx')
        = (Real.sqrt (1 - D.weight label) * Real.sqrt (1 - D.weight label))
          * ((whitenerᵀ *ᵥ D.atom label) coordIdx
              * (whitenerᵀ *ᵥ D.atom label) coordIdx') from by ring,
      Real.mul_self_sqrt (hslackPos label).le]
  obtain ⟨completion, hcompletionOrtho, hcoDesignPerp, hcomplete⟩ :=
    exists_orthonormal_completion coDesign hcoDesignOrtho
  refine ⟨{ atom := fun label => (Real.sqrt (D.weight label))⁻¹
              • (fun colIdx => completion label colIdx)
            weight := D.weight
            weight_pos := D.weight_pos
            weight_sum_one := D.weight_sum_one
            isParseval := ?_ }, ?_, ?_⟩
  · calc ∑ label, D.weight label
        • atomMatrix ((Real.sqrt (D.weight label))⁻¹ • (fun colIdx => completion label colIdx))
        = ∑ label, atomMatrix (fun colIdx => completion label colIdx) := by
          refine Finset.sum_congr rfl fun label _ => ?_
          rw [atomMatrix_smul, smul_smul, inv_pow,
            Real.sq_sqrt (D.weight_pos label).le,
            mul_inv_cancel₀ (D.weight_pos label).ne', one_smul]
      _ = 1 := by rw [← transpose_mul_self_eq_sum_rows, hcompletionOrtho]
  · intro pairFst pairSnd hbracket
    exact dependence_of_dualPairBracket_eq_zero D whitener hwhitenerUnit coDesign
      hcoDesignShape completion hcompletionOrtho hcoDesignPerp _
      (fun label => rfl) pairFst pairSnd hbracket
  · intro dualPair hpairCard hdom
    exact posDef_primalGap_of_posDef_dualPairGap D whitener hwhitenerUnit hwhitened
      coDesign hcoDesignShape completion hcomplete _
      (fun label => rfl) dualPair hpairCard hdom

/-! ## The endgame: from the dual cover to the shared line pair -/

/-- **The plane absorbs the third label.**  A dependence vanishing on an edge
is supported on the complementary triple; pairing it against a common
orthogonal of two of those atoms forces the third atom onto their plane. -/
theorem atomDot_eq_zero_of_offPairDependence (D : WeightedDesign 5 3)
    (hprimitive : IsPrimitiveDesign D)
    (edgeFst edgeSnd thirdLabel planeFst planeSnd : Fin 5)
    (hplaneNe : planeFst ≠ planeSnd)
    (hcover : ∀ label : Fin 5, label = edgeFst ∨ label = edgeSnd ∨ label = thirdLabel
        ∨ label = planeFst ∨ label = planeSnd)
    (dependence : Fin 5 → ℝ)
    (hwitness : ∃ witnessLabel, dependence witnessLabel ≠ 0)
    (hdepEdgeFst : dependence edgeFst = 0) (hdepEdgeSnd : dependence edgeSnd = 0)
    (hdepSum : (∑ label, dependence label • D.atom label) = 0)
    (normal : Fin 3 → ℝ)
    (hdotPlaneFst : D.atom planeFst ⬝ᵥ normal = 0)
    (hdotPlaneSnd : D.atom planeSnd ⬝ᵥ normal = 0) :
    D.atom thirdLabel ⬝ᵥ normal = 0 := by
  classical
  -- the third coefficient survives, else the plane pair carries a dependence
  have hthirdNe : dependence thirdLabel ≠ 0 := by
    intro hthirdZero
    have hoffSupport : ∀ label ∈ (Finset.univ : Finset (Fin 5)),
        label ∉ ({planeFst, planeSnd} : Finset (Fin 5)) →
        dependence label • D.atom label = 0 := by
      intro label _ hnotPlane
      rcases hcover label with rfl | rfl | rfl | rfl | rfl
      · rw [hdepEdgeFst, zero_smul]
      · rw [hdepEdgeSnd, zero_smul]
      · rw [hthirdZero, zero_smul]
      · exact absurd (Finset.mem_insert_self _ _) hnotPlane
      · exact absurd (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hnotPlane
    have hcollapsed := Finset.sum_subset
      (Finset.subset_univ ({planeFst, planeSnd} : Finset (Fin 5))) hoffSupport
    rw [hdepSum, Finset.sum_pair hplaneNe] at hcollapsed
    obtain ⟨hplaneFstZero, hplaneSndZero⟩ :=
      coeffPair_eq_zero_of_smul_add_smul_eq_zero (D.atom planeFst) (D.atom planeSnd)
        (dependence planeFst) (dependence planeSnd)
        (fun ratio => hprimitive planeFst planeSnd ratio hplaneNe)
        (atom_ne_zero_of_isPrimitiveDesign (by norm_num) D hprimitive planeFst)
        hcollapsed
    obtain ⟨witnessLabel, hwitnessNe⟩ := hwitness
    rcases hcover witnessLabel with rfl | rfl | rfl | rfl | rfl
    · exact hwitnessNe hdepEdgeFst
    · exact hwitnessNe hdepEdgeSnd
    · exact hwitnessNe hthirdZero
    · exact hwitnessNe hplaneFstZero
    · exact hwitnessNe hplaneSndZero
  -- pair the dependence against the normal
  have hdotSum : ∑ label, dependence label * (D.atom label ⬝ᵥ normal) = 0 := by
    have happlied := congrArg (fun vector => vector ⬝ᵥ normal) hdepSum
    simp only [zero_dotProduct] at happlied
    rw [← happlied, sum_dotProduct]
    exact Finset.sum_congr rfl fun label _ => by
      rw [smul_dotProduct, smul_eq_mul]
  have hsingled : ∑ label, dependence label * (D.atom label ⬝ᵥ normal)
      = dependence thirdLabel * (D.atom thirdLabel ⬝ᵥ normal) := by
    refine Finset.sum_eq_single thirdLabel (fun label _ hlabelNe => ?_)
      (fun habsent => absurd (Finset.mem_univ _) habsent)
    rcases hcover label with rfl | rfl | rfl | rfl | rfl
    · rw [hdepEdgeFst, zero_mul]
    · rw [hdepEdgeSnd, zero_mul]
    · exact absurd rfl hlabelNe
    · rw [hdotPlaneFst, mul_zero]
    · rw [hdotPlaneSnd, mul_zero]
  rw [hsingled] at hdotSum
  exact (mul_eq_zero.mp hdotSum).resolve_left hthirdNe

/-- **The edge certifies the complementary collinear triple.**  A dependence
vanishing on an edge collapses to the complementary triple and kills its
bracket. -/
theorem atomBracket_eq_zero_of_offPairDependence (D : WeightedDesign 5 3)
    (edgeFst edgeSnd sharedLabel offFst offSnd : Fin 5)
    (hcover : ∀ label : Fin 5, label = edgeFst ∨ label = edgeSnd ∨ label = sharedLabel
        ∨ label = offFst ∨ label = offSnd)
    (hsharedNeOffFst : sharedLabel ≠ offFst) (hsharedNeOffSnd : sharedLabel ≠ offSnd)
    (hoffNe : offFst ≠ offSnd)
    (dependence : Fin 5 → ℝ)
    (hwitness : ∃ witnessLabel, dependence witnessLabel ≠ 0)
    (hdepEdgeFst : dependence edgeFst = 0) (hdepEdgeSnd : dependence edgeSnd = 0)
    (hdepSum : (∑ label, dependence label • D.atom label) = 0) :
    atomBracket D sharedLabel offFst offSnd = 0 := by
  classical
  have hsharedNotOff : sharedLabel ∉ ({offFst, offSnd} : Finset (Fin 5)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hmem
    rcases hmem with heq | heq
    · exact hsharedNeOffFst heq
    · exact hsharedNeOffSnd heq
  have hoffSupport : ∀ label ∈ (Finset.univ : Finset (Fin 5)),
      label ∉ ({sharedLabel, offFst, offSnd} : Finset (Fin 5)) →
      dependence label • D.atom label = 0 := by
    intro label _ hnotTriple
    rcases hcover label with rfl | rfl | rfl | rfl | rfl
    · rw [hdepEdgeFst, zero_smul]
    · rw [hdepEdgeSnd, zero_smul]
    · exact absurd (Finset.mem_insert_self _ _) hnotTriple
    · exact absurd (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hnotTriple
    · exact absurd (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) hnotTriple
  have hcollapsed := Finset.sum_subset
    (Finset.subset_univ ({sharedLabel, offFst, offSnd} : Finset (Fin 5))) hoffSupport
  rw [hdepSum, Finset.sum_insert hsharedNotOff, Finset.sum_pair hoffNe] at hcollapsed
  have hvanish : dependence sharedLabel • D.atom sharedLabel
      + dependence offFst • D.atom offFst + dependence offSnd • D.atom offSnd = 0 := by
    rw [add_assoc]
    exact hcollapsed
  have hnontrivial : dependence sharedLabel ≠ 0 ∨ dependence offFst ≠ 0
      ∨ dependence offSnd ≠ 0 := by
    obtain ⟨witnessLabel, hwitnessNe⟩ := hwitness
    rcases hcover witnessLabel with rfl | rfl | rfl | rfl | rfl
    · exact absurd hdepEdgeFst hwitnessNe
    · exact absurd hdepEdgeSnd hwitnessNe
    · exact Or.inl hwitnessNe
    · exact Or.inr (Or.inl hwitnessNe)
    · exact Or.inr (Or.inr hwitnessNe)
  show tripleBracket (D.atom sharedLabel) (D.atom offFst) (D.atom offSnd) = 0
  exact tripleBracket_eq_zero_of_dependence _ _ _ _ _ _ hnontrivial hvanish

/-- **THE MATROID RESIDUAL, PROVED.**  Every primitive `(5,3)` tie carries two
dependent triples through a common atom.  Route: the explicit Naimark dual is
tie-locked (no strictly dominating pair), the proved rank-two hinge turns that
into a cover of every dual quadruple by bracket-zero pairs, the cover contains
a two-edge matching or a full triangle, the dictionary pulls each dual edge
back to a primal collinear triple — a matching complements to the shared line
pair, and a triangle would put all five atoms on one plane, which Parseval
forbids. -/
theorem sharedLinePairAtEveryTie_holds : SharedLinePairAtEveryTieFiveThree := by
  intro bottomDesign hprimitive htie
  classical
  obtain ⟨dualDesign, hdictionary, htransfer⟩ :=
    exists_naimarkDual_with_bracketDictionary bottomDesign
  -- the dual is tie-locked: no strictly dominating pair
  have hnoStrictPair : ∀ dualPair : Finset (Fin 5), dualPair.card = 2 →
      ¬ (Gtz.subsetSum dualDesign dualPair - 1).PosDef := by
    intro dualPair hcard hposDef
    have hcomplCard : dualPairᶜ.card = 3 := by
      rw [Finset.card_compl, Fintype.card_fin, hcard]
    exact htie.2 dualPairᶜ hcomplCard (htransfer dualPair hcard hposDef)
  -- bracket vanishing is symmetric
  have hedgeSymm : ∀ leftIdx rightIdx : Fin 5,
      pairBracket dualDesign leftIdx rightIdx = 0 →
      pairBracket dualDesign rightIdx leftIdx = 0 := by
    intro leftIdx rightIdx hzero
    have hanti : pairBracket dualDesign rightIdx leftIdx
        = -(pairBracket dualDesign leftIdx rightIdx) := by
      unfold pairBracket
      ring
    rw [hanti, hzero, neg_zero]
  -- the hinge covers every quadruple with a bracket-zero pair
  have hfour : ∀ quadA quadB quadC quadD : Fin 5,
      quadA ≠ quadB → quadA ≠ quadC → quadA ≠ quadD →
      quadB ≠ quadC → quadB ≠ quadD → quadC ≠ quadD →
      pairBracket dualDesign quadA quadB = 0 ∨ pairBracket dualDesign quadA quadC = 0
        ∨ pairBracket dualDesign quadA quadD = 0 ∨ pairBracket dualDesign quadB quadC = 0
        ∨ pairBracket dualDesign quadB quadD = 0
        ∨ pairBracket dualDesign quadC quadD = 0 := by
    intro quadA quadB quadC quadD hdAB hdAC hdAD hdBC hdBD hdCD
    by_contra hnone
    push Not at hnone
    obtain ⟨hneAB, hneAC, hneAD, hneBC, hneBD, hneCD⟩ := hnone
    obtain ⟨dominatingPair, hpairCard, hpairPosDef⟩ :=
      rankTwoFourDirectionHinge_holds 5 dualDesign quadA quadB quadC quadD
        hdAB hdAC hdAD hdBC hdBD hdCD hneAB hneAC hneAD hneBC hneBD hneCD
    exact hnoStrictPair dominatingPair hpairCard hpairPosDef
  -- matching or triangle
  rcases matching_or_triangle_of_coveringEdges
      (fun leftIdx rightIdx => pairBracket dualDesign leftIdx rightIdx = 0)
      hedgeSymm hfour with
    ⟨pairAFst, pairASnd, pairBFst, pairBSnd, hmatchA, hmatchB, hcrossOne, hcrossTwo,
      hcrossThree, hcrossFour, hedgeA, hedgeB⟩ |
    ⟨triA, triB, triC, htriAB, htriAC, htriBC, hedgeTriAB, hedgeTriAC, hedgeTriBC⟩
  · -- MATCHING: the shared line pair, by construction
    have hquadNotFst : pairAFst ∉ ({pairASnd, pairBFst, pairBSnd} : Finset (Fin 5)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hmem
      rcases hmem with heq | heq | heq
      · exact hmatchA heq
      · exact hcrossOne heq
      · exact hcrossTwo heq
    have hquadNotSnd : pairASnd ∉ ({pairBFst, pairBSnd} : Finset (Fin 5)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hmem
      rcases hmem with heq | heq
      · exact hcrossThree heq
      · exact hcrossFour heq
    have hquadNotThd : pairBFst ∉ ({pairBSnd} : Finset (Fin 5)) := by
      simp only [Finset.mem_singleton]
      exact hmatchB
    have hquadCard : ({pairAFst, pairASnd, pairBFst, pairBSnd} : Finset (Fin 5)).card = 4 := by
      rw [Finset.card_insert_of_notMem hquadNotFst,
        Finset.card_insert_of_notMem hquadNotSnd,
        Finset.card_insert_of_notMem hquadNotThd, Finset.card_singleton]
    have hsharedCard :
        (({pairAFst, pairASnd, pairBFst, pairBSnd} : Finset (Fin 5))ᶜ).card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin, hquadCard]
    obtain ⟨sharedLabel, hsharedEq⟩ := Finset.card_eq_one.mp hsharedCard
    have hsharedNotQuad :
        sharedLabel ∉ ({pairAFst, pairASnd, pairBFst, pairBSnd} : Finset (Fin 5)) := by
      refine Finset.mem_compl.mp ?_
      rw [hsharedEq]
      exact Finset.mem_singleton_self _
    have hsharedSplit : ¬ (sharedLabel = pairAFst ∨ sharedLabel = pairASnd
        ∨ sharedLabel = pairBFst ∨ sharedLabel = pairBSnd) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hsharedNotQuad
    push Not at hsharedSplit
    obtain ⟨hsharedNeAFst, hsharedNeASnd, hsharedNeBFst, hsharedNeBSnd⟩ := hsharedSplit
    have hcover : ∀ label : Fin 5, label = pairAFst ∨ label = pairASnd
        ∨ label = pairBFst ∨ label = pairBSnd ∨ label = sharedLabel := by
      intro label
      by_cases hmem : label ∈ ({pairAFst, pairASnd, pairBFst, pairBSnd} : Finset (Fin 5))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        tauto
      · have hlabelCompl : label ∈ ({pairAFst, pairASnd, pairBFst, pairBSnd}
            : Finset (Fin 5))ᶜ := Finset.mem_compl.mpr hmem
        rw [hsharedEq] at hlabelCompl
        exact Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp hlabelCompl))))
    -- the two dictionary dependences and the two brackets
    obtain ⟨depA, hwitA, hdepAFst, hdepASnd, hsumA⟩ := hdictionary pairAFst pairASnd hedgeA
    obtain ⟨depB, hwitB, hdepBFst, hdepBSnd, hsumB⟩ := hdictionary pairBFst pairBSnd hedgeB
    have hbracketFromA : atomBracket bottomDesign sharedLabel pairBFst pairBSnd = 0 := by
      refine atomBracket_eq_zero_of_offPairDependence bottomDesign pairAFst pairASnd
        sharedLabel pairBFst pairBSnd (fun label => ?_) hsharedNeBFst hsharedNeBSnd
        hmatchB depA hwitA hdepAFst hdepASnd hsumA
      rcases hcover label with heq | heq | heq | heq | heq <;> tauto
    have hbracketFromB : atomBracket bottomDesign sharedLabel pairAFst pairASnd = 0 := by
      refine atomBracket_eq_zero_of_offPairDependence bottomDesign pairBFst pairBSnd
        sharedLabel pairAFst pairASnd (fun label => ?_) hsharedNeAFst hsharedNeASnd
        hmatchA depB hwitB hdepBFst hdepBSnd hsumB
      rcases hcover label with heq | heq | heq | heq | heq <;> tauto
    -- the relabeling permutation
    set relabelFun : Fin 5 → Fin 5 :=
      ![sharedLabel, pairBFst, pairBSnd, pairAFst, pairASnd] with hrelabelDef
    have hsymOne := Ne.symm hsharedNeAFst
    have hsymTwo := Ne.symm hsharedNeASnd
    have hsymThree := Ne.symm hsharedNeBFst
    have hsymFour := Ne.symm hsharedNeBSnd
    have hsymFive := Ne.symm hcrossOne
    have hsymSix := Ne.symm hcrossTwo
    have hsymSeven := Ne.symm hcrossThree
    have hsymEight := Ne.symm hcrossFour
    have hsymNine := Ne.symm hmatchA
    have hsymTen := Ne.symm hmatchB
    have hrelabelInj : Function.Injective relabelFun := by
      intro relabelLeft relabelRight hvalueEq
      fin_cases relabelLeft <;> fin_cases relabelRight <;> simp_all
    refine ⟨Equiv.ofBijective relabelFun (Finite.injective_iff_bijective.mp hrelabelInj),
      ?_, ?_⟩
    · exact hbracketFromA
    · exact hbracketFromB
  · -- TRIANGLE: five coplanar atoms against Parseval
    exfalso
    have htriNotFst : triA ∉ ({triB, triC} : Finset (Fin 5)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hmem
      rcases hmem with heq | heq
      · exact htriAB heq
      · exact htriAC heq
    have htriNotSnd : triB ∉ ({triC} : Finset (Fin 5)) := by
      simp only [Finset.mem_singleton]
      exact htriBC
    have htriCard : ({triA, triB, triC} : Finset (Fin 5)).card = 3 := by
      rw [Finset.card_insert_of_notMem htriNotFst,
        Finset.card_insert_of_notMem htriNotSnd, Finset.card_singleton]
    have hplaneCard : (({triA, triB, triC} : Finset (Fin 5))ᶜ).card = 2 := by
      rw [Finset.card_compl, Fintype.card_fin, htriCard]
    obtain ⟨planeFst, planeSnd, hplaneNe, hplaneEq⟩ := Finset.card_eq_two.mp hplaneCard
    have hcover : ∀ label : Fin 5, label = triA ∨ label = triB ∨ label = triC
        ∨ label = planeFst ∨ label = planeSnd := by
      intro label
      by_cases hmem : label ∈ ({triA, triB, triC} : Finset (Fin 5))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        tauto
      · have hlabelCompl : label ∈ ({triA, triB, triC} : Finset (Fin 5))ᶜ :=
          Finset.mem_compl.mpr hmem
        rw [hplaneEq] at hlabelCompl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hlabelCompl
        tauto
    obtain ⟨normal, hnormalNe, hdotPlaneFst, hdotPlaneSnd⟩ :=
      exists_commonOrthogonal_pair (bottomDesign.atom planeFst) (bottomDesign.atom planeSnd)
    obtain ⟨depAB, hwitAB, hdepABFst, hdepABSnd, hsumAB⟩ := hdictionary triA triB hedgeTriAB
    obtain ⟨depAC, hwitAC, hdepACFst, hdepACSnd, hsumAC⟩ := hdictionary triA triC hedgeTriAC
    obtain ⟨depBC, hwitBC, hdepBCFst, hdepBCSnd, hsumBC⟩ := hdictionary triB triC hedgeTriBC
    have hdotThird : bottomDesign.atom triC ⬝ᵥ normal = 0 := by
      refine atomDot_eq_zero_of_offPairDependence bottomDesign hprimitive triA triB triC
        planeFst planeSnd hplaneNe (fun label => hcover label) depAB hwitAB
        hdepABFst hdepABSnd hsumAB normal hdotPlaneFst hdotPlaneSnd
    have hdotSecond : bottomDesign.atom triB ⬝ᵥ normal = 0 := by
      refine atomDot_eq_zero_of_offPairDependence bottomDesign hprimitive triA triC triB
        planeFst planeSnd hplaneNe (fun label => ?_) depAC hwitAC
        hdepACFst hdepACSnd hsumAC normal hdotPlaneFst hdotPlaneSnd
      rcases hcover label with heq | heq | heq | heq | heq <;> tauto
    have hdotFirst : bottomDesign.atom triA ⬝ᵥ normal = 0 := by
      refine atomDot_eq_zero_of_offPairDependence bottomDesign hprimitive triB triC triA
        planeFst planeSnd hplaneNe (fun label => ?_) depBC hwitBC
        hdepBCFst hdepBCSnd hsumBC normal hdotPlaneFst hdotPlaneSnd
      rcases hcover label with heq | heq | heq | heq | heq <;> tauto
    have hallDots : ∀ label : Fin 5, bottomDesign.atom label ⬝ᵥ normal = 0 := by
      intro label
      rcases hcover label with rfl | rfl | rfl | rfl | rfl
      · exact hdotFirst
      · exact hdotSecond
      · exact hdotThird
      · exact hdotPlaneFst
      · exact hdotPlaneSnd
    exact hnormalNe (eq_zero_of_forall_atom_dot_eq_zero bottomDesign hallDots)

/-- **THE TARGET RESIDUAL, CLOSED.**  `EndpointBottomTieExclusionFiveThree`
holds unconditionally: the matroid residual is a theorem, and the landed
reduction consumes it.  Branch (ii) of the `(6,3)` stress trichotomy now
rests on the two-vanished statement and the hinge alone. -/
theorem endpointBottomTieExclusionFiveThree_holds : EndpointBottomTieExclusionFiveThree :=
  endpointBottomTieExclusion_of_sharedLinePair sharedLinePairAtEveryTie_holds

end EndpointSpike
