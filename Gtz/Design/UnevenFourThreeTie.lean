/-
# A `(4,3)` tie with wildly non-uniform weights

The `(4,3)` rigidity ladder proves that a design with **no strictly dominating
triple** and every weight at most `1/4` must have uniform weights -- but the
weight cap is not a rigidity, it is simplex arithmetic: four positive weights
summing to one and each at most `1/4` are already forced to be `1/4`.  The open
question the ladder leaves is whether the cap can be dropped: does a `(4,3)`
design with NON-uniform weights and no strictly dominating triple exist?

It does.  This file exhibits one, and its weights are `(1/6, 1/6, 1/3, 1/3)` --
a factor of two apart, nowhere near the uniform point.  So the `(4,3)` tie locus
is strictly larger than the regular tetrahedron, and the weight cap in the
rigidity ladder is a genuine hypothesis, not a removable one.

The witness is two mirror pairs,

    g0 = ( p, 0,  r)      g1 = (-p, 0,  r)
    g2 = ( 0, q, -s)      g3 = ( 0,-q, -s)

with `p^2 = 3`, `q^2 = 3/2`, `r^2 = 4/3`, `s^2 = 5/6`.  The mirror symmetry
kills every off-diagonal Parseval sum identically, so only the three diagonal
identities `2*t0*p^2 = 1`, `2*t2*q^2 = 1`, `2*t0*r^2 + 2*t2*s^2 = 1` have to
hold, and they do.  Each atom coordinate is a square root of a rational, but the
mirror structure makes every GTZ-visible quantity rational: the leverages are
`13/3, 13/3, 7/3, 7/3`, the within-pair pairings are `-5/3` and `-2/3`, and the
eight cross pairings are all the same irrational number, which enters the
discriminant only through its square `10/9` -- every triple uses exactly two
cross pairings, never one.

All four triple determinants are then exactly zero.  Since the determinant of a
positive definite matrix is positive, no triple dominates strictly.

Found by solving the locus condition directly: writing the design through its
Parseval frame, the complement of the frame Gram is rank one, `w w^T`, and the
triple omitting label `d` dominates strictly exactly when
`sum_{c != d} w_c^2 / (1 - t_c) < 1`.  Since the four constraints must all fail
and `sum_c w_c^2 = 1`, the weights are pinned to `t_c = 1 - 3 w_c^2` and every
triple lands exactly on the boundary.  The tetrahedron is the point `w_c^2 = 1/4`
of that family; this witness is another point of it.
-/
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Design.RhoNormalForm
import Gtz.Design.KFourChartClosure
import Gtz.Certificates.ResidueDissolution
import Gtz.Quantitative.SixThreeCrux
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

/-! ## The surds beyond the shipped `Gtz.sqrt_three_sq` -/

theorem sqrt_six_sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

theorem sqrt_thirty_sq : Real.sqrt 30 ^ 2 = 30 := Real.sq_sqrt (by norm_num)

/-! ## The design -/

/-- Two mirror pairs: `(p,0,r), (-p,0,r), (0,q,-s), (0,-q,-s)` with
`p^2 = 3`, `q^2 = 3/2`, `r^2 = 4/3`, `s^2 = 5/6`. -/
noncomputable def unevenTieAtom : Fin 4 → Fin 3 → ℝ :=
  ![![Real.sqrt 3, 0, 2 * Real.sqrt 3 / 3],
    ![-Real.sqrt 3, 0, 2 * Real.sqrt 3 / 3],
    ![0, Real.sqrt 6 / 2, -(Real.sqrt 30 / 6)],
    ![0, -(Real.sqrt 6 / 2), -(Real.sqrt 30 / 6)]]

/-- **The witness**: a `(4,3)` weighted design whose weights are
`(1/6, 1/6, 1/3, 1/3)`. -/
noncomputable def unevenTieDesign : WeightedDesign 4 3 where
  atom := unevenTieAtom
  weight := ![1/6, 1/6, 1/3, 1/3]
  weight_pos := by
    intro atomLabel
    fin_cases atomLabel <;> simp
  weight_sum_one := by
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_four, smul_eq_mul, unevenTieAtom, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> simp <;>
      nlinarith [sqrt_three_sq, sqrt_six_sq, sqrt_thirty_sq]

theorem unevenTieDesign_weight (atomLabel : Fin 4) :
    unevenTieDesign.weight atomLabel = ![1/6, 1/6, 1/3, 1/3] atomLabel := rfl

theorem unevenTieDesign_atom (atomLabel : Fin 4) :
    unevenTieDesign.atom atomLabel = unevenTieAtom atomLabel := rfl

/-- **The weights are not uniform** -- they differ by a factor of two. -/
theorem unevenTieDesign_weight_ne :
    unevenTieDesign.weight 0 ≠ unevenTieDesign.weight 2 := by
  simp only [unevenTieDesign_weight, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-! ## The Gram, which is rational despite the irrational atoms -/

/-- The single value taken by all eight cross pairings.  It is irrational, but it
enters every triple determinant an even number of times. -/
noncomputable def unevenTieCrossPairing : ℝ := -(Real.sqrt 3 * Real.sqrt 30) / 9

theorem unevenTieCrossPairing_sq : unevenTieCrossPairing ^ 2 = 10 / 9 := by
  simp only [unevenTieCrossPairing]
  nlinarith [sqrt_three_sq, sqrt_thirty_sq, Real.sqrt_nonneg 3, Real.sqrt_nonneg 30]

/-- The full Gram of the witness, written out. -/
noncomputable def unevenTiePairingTable : Matrix (Fin 4) (Fin 4) ℝ :=
  !![13/3, -5/3, unevenTieCrossPairing, unevenTieCrossPairing;
     -5/3, 13/3, unevenTieCrossPairing, unevenTieCrossPairing;
     unevenTieCrossPairing, unevenTieCrossPairing, 7/3, -2/3;
     unevenTieCrossPairing, unevenTieCrossPairing, -2/3, 7/3]

theorem unevenTieDesign_atomPairing (firstLabel secondLabel : Fin 4) :
    atomPairing unevenTieDesign firstLabel secondLabel
      = unevenTiePairingTable firstLabel secondLabel := by
  simp only [atomPairing, unevenTieDesign_atom, unevenTieAtom, unevenTiePairingTable,
    unevenTieCrossPairing, dotProduct, Fin.sum_univ_three]
  fin_cases firstLabel <;> fin_cases secondLabel <;> simp <;>
    nlinarith [sqrt_three_sq, sqrt_six_sq, sqrt_thirty_sq]

theorem unevenTieDesign_heavyExcess (atomLabel : Fin 4) :
    heavyExcess unevenTieDesign atomLabel = ![10/3, 10/3, 4/3, 4/3] atomLabel := by
  have hdiagonal := unevenTieDesign_atomPairing atomLabel atomLabel
  rw [atomPairing_self] at hdiagonal
  simp only [heavyExcess, hdiagonal, unevenTiePairingTable]
  fin_cases atomLabel <;> simp <;> norm_num

/-! ## Every triple determinant vanishes -/

/-- **All twenty-four ordered triple determinants are zero.**  Every triple uses
exactly one within-pair pairing and two cross pairings, so the cross value enters
only through its square. -/
theorem unevenTieDesign_discriminantTie (pivotLabel firstLabel secondLabel : Fin 4)
    (hpivotFirst : pivotLabel ≠ firstLabel) (hpivotSecond : pivotLabel ≠ secondLabel)
    (hpairDistinct : firstLabel ≠ secondLabel) :
    discriminantTie unevenTieDesign pivotLabel firstLabel secondLabel = 0 := by
  have hcross := unevenTieCrossPairing_sq
  simp only [discriminantTie, unevenTieDesign_heavyExcess, unevenTieDesign_atomPairing,
    unevenTiePairingTable]
  fin_cases pivotLabel <;> fin_cases firstLabel <;> fin_cases secondLabel <;>
    simp_all <;> nlinarith [hcross]

/-! ## No triple dominates strictly -/

/-- **No three-subset dominates strictly**: each one has determinant zero, and a
positive definite matrix has positive determinant. -/
theorem unevenTieDesign_no_strictDominator :
    ∀ candidate : Finset (Fin 4), candidate.card = 3 →
      ¬ (subsetSum unevenTieDesign candidate - 1).PosDef := by
  intro candidate hcard hposDef
  obtain ⟨pivotLabel, firstLabel, secondLabel, hpivotFirst, hpivotSecond, hpairDistinct, rfl⟩ :=
    Finset.card_eq_three.mp hcard
  have hdeterminant := det_subsetSum_sub_one_eq_discriminantTie unevenTieDesign
    hpivotFirst hpivotSecond hpairDistinct
  have hzero := unevenTieDesign_discriminantTie pivotLabel firstLabel secondLabel
    hpivotFirst hpivotSecond hpairDistinct
  have hpositive := hposDef.det_pos
  rw [hdeterminant, hzero] at hpositive
  exact lt_irrefl 0 hpositive

/-! ## Every triple still dominates weakly: the witness is an exact tie -/

/-- A symmetric `3x3` matrix with positive corner, positive leading two by two
minor and vanishing determinant is positive semidefinite.  Same completed square
as `Gtz.posDef_of_leadingMinors_fin_three`, read on the boundary. -/
theorem posSemidef_of_leadingMinors_fin_three_of_det_zero
    (entryOneOne entryOneTwo entryOneThree entryTwoTwo entryTwoThree
      entryThreeThree : ℝ)
    (hcorner : 0 < entryOneOne)
    (hblockMinor : 0 < entryOneOne * entryTwoTwo - entryOneTwo ^ 2)
    (hdetMinor : entryOneOne * entryTwoTwo * entryThreeThree
      - entryOneOne * entryTwoThree ^ 2 - entryOneTwo ^ 2 * entryThreeThree
      + 2 * entryOneTwo * entryOneThree * entryTwoThree
      - entryOneThree ^ 2 * entryTwoTwo = 0) :
    (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq ?_, fun vecArg => ?_⟩
  · ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp [Matrix.transpose_apply]
  · rw [star_trivial]
    have hform : vecArg ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
            entryOneTwo, entryTwoTwo, entryTwoThree;
            entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vecArg)
        = entryOneOne * vecArg 0 ^ 2 + 2 * entryOneTwo * (vecArg 0 * vecArg 1)
          + 2 * entryOneThree * (vecArg 0 * vecArg 2)
          + entryTwoTwo * vecArg 1 ^ 2 + 2 * entryTwoThree * (vecArg 1 * vecArg 2)
          + entryThreeThree * vecArg 2 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    have hcompleted : entryOneOne * (entryOneOne * entryTwoTwo - entryOneTwo ^ 2)
          * (entryOneOne * vecArg 0 ^ 2 + 2 * entryOneTwo * (vecArg 0 * vecArg 1)
              + 2 * entryOneThree * (vecArg 0 * vecArg 2)
              + entryTwoTwo * vecArg 1 ^ 2 + 2 * entryTwoThree * (vecArg 1 * vecArg 2)
              + entryThreeThree * vecArg 2 ^ 2)
        = (entryOneOne * entryTwoTwo - entryOneTwo ^ 2)
            * (entryOneOne * vecArg 0 + entryOneTwo * vecArg 1
                + entryOneThree * vecArg 2) ^ 2
          + ((entryOneOne * entryTwoTwo - entryOneTwo ^ 2) * vecArg 1
              + (entryOneOne * entryTwoThree - entryOneTwo * entryOneThree)
                  * vecArg 2) ^ 2
          + entryOneOne * (entryOneOne * entryTwoTwo * entryThreeThree
              - entryOneOne * entryTwoThree ^ 2 - entryOneTwo ^ 2 * entryThreeThree
              + 2 * entryOneTwo * entryOneThree * entryTwoThree
              - entryOneThree ^ 2 * entryTwoTwo) * vecArg 2 ^ 2 := by
      ring
    rw [hdetMinor] at hcompleted
    nlinarith [hcompleted, mul_pos hcorner hblockMinor, hblockMinor,
      sq_nonneg (entryOneOne * vecArg 0 + entryOneTwo * vecArg 1
        + entryOneThree * vecArg 2),
      sq_nonneg ((entryOneOne * entryTwoTwo - entryOneTwo ^ 2) * vecArg 1
        + (entryOneOne * entryTwoThree - entryOneTwo * entryOneThree) * vecArg 2)]

/-- **Every triple of the witness dominates weakly.** -/
theorem unevenTieDesign_dominates (pivotLabel firstLabel secondLabel : Fin 4)
    (hpivotFirst : pivotLabel ≠ firstLabel) (hpivotSecond : pivotLabel ≠ secondLabel)
    (hpairDistinct : firstLabel ≠ secondLabel) :
    Dominates unevenTieDesign {pivotLabel, firstLabel, secondLabel} := by
  have hcross := unevenTieCrossPairing_sq
  refine (dominates_triple_iff_posSemidef_tripleGapMatrix unevenTieDesign hpivotFirst
    hpivotSecond hpairDistinct).mpr ?_
  have hcorner : 0 < heavyExcess unevenTieDesign pivotLabel := by
    rw [unevenTieDesign_heavyExcess]
    fin_cases pivotLabel <;> simp
  have hblock : 0 < heavyExcess unevenTieDesign pivotLabel
      * heavyExcess unevenTieDesign firstLabel
      - atomPairing unevenTieDesign pivotLabel firstLabel ^ 2 := by
    simp only [unevenTieDesign_heavyExcess, unevenTieDesign_atomPairing,
      unevenTiePairingTable]
    fin_cases pivotLabel <;> fin_cases firstLabel <;> simp_all <;> nlinarith [hcross]
  have hdet : heavyExcess unevenTieDesign pivotLabel
        * heavyExcess unevenTieDesign firstLabel
        * heavyExcess unevenTieDesign secondLabel
      - heavyExcess unevenTieDesign pivotLabel
          * atomPairing unevenTieDesign firstLabel secondLabel ^ 2
      - atomPairing unevenTieDesign pivotLabel firstLabel ^ 2
          * heavyExcess unevenTieDesign secondLabel
      + 2 * atomPairing unevenTieDesign pivotLabel firstLabel
          * atomPairing unevenTieDesign pivotLabel secondLabel
          * atomPairing unevenTieDesign firstLabel secondLabel
      - atomPairing unevenTieDesign pivotLabel secondLabel ^ 2
          * heavyExcess unevenTieDesign firstLabel = 0 := by
    have hzero := unevenTieDesign_discriminantTie pivotLabel firstLabel secondLabel
      hpivotFirst hpivotSecond hpairDistinct
    simp only [discriminantTie] at hzero
    linarith [hzero]
  simpa only [tripleGapMatrix] using
    posSemidef_of_leadingMinors_fin_three_of_det_zero
      (heavyExcess unevenTieDesign pivotLabel)
      (atomPairing unevenTieDesign pivotLabel firstLabel)
      (atomPairing unevenTieDesign pivotLabel secondLabel)
      (heavyExcess unevenTieDesign firstLabel)
      (atomPairing unevenTieDesign firstLabel secondLabel)
      (heavyExcess unevenTieDesign secondLabel) hcorner hblock hdet

/-- **The witness is an exact tie.** -/
theorem unevenTieDesign_isTie : IsTie unevenTieDesign :=
  ⟨⟨{0, 1, 2}, by decide,
     unevenTieDesign_dominates 0 1 2 (by decide) (by decide) (by decide)⟩,
   unevenTieDesign_no_strictDominator⟩

/-- **THE WEIGHT CAP IS A GENUINE HYPOTHESIS.**  There is a `(4,3)` weighted
design whose weights are not uniform and which is nevertheless an exact tie: no
three-subset dominates strictly.  So the `(4,3)` tie locus is strictly larger
than the regular tetrahedron, and the uniformity conclusion of the rigidity
ladder genuinely needs its weight cap. -/
theorem exists_nonUniformWeight_isTie :
    ∃ design : WeightedDesign 4 3,
      (∃ firstLabel secondLabel : Fin 4, design.weight firstLabel ≠ design.weight secondLabel)
        ∧ IsTie design :=
  ⟨unevenTieDesign, ⟨0, 2, unevenTieDesign_weight_ne⟩, unevenTieDesign_isTie⟩

/-- The same, spelled without the tie predicate. -/
theorem exists_nonUniformWeight_without_strictDominator :
    ∃ design : WeightedDesign 4 3,
      (∃ firstLabel secondLabel : Fin 4, design.weight firstLabel ≠ design.weight secondLabel)
        ∧ ∀ candidate : Finset (Fin 4), candidate.card = 3 →
            ¬ (subsetSum design candidate - 1).PosDef :=
  ⟨unevenTieDesign, ⟨0, 2, unevenTieDesign_weight_ne⟩, unevenTieDesign_no_strictDominator⟩

end Gtz
