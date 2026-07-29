/-
# The (7,3) rigidity ladder: block freezes and the sevenths reformulation

At the uniform-share `(7,3)` stratum — every `atomShare` equal to `3/7` — the landed
quadratic law `Gamma * Gamma = (7/3) . Gamma`
(`Gtz.directionGramMatrix_sq_of_uniformShare`) restricts to every principal block of
the hollow correlation matrix `M = Gamma - 1` with an explicit low-rank correction.
This file turns those restrictions into the complete interlacing-free rigidity
ladder of the July 2026 pen campaign (P3), plus the determinant kit that powers it.

## The six-block freeze (drop one atom `d`)

With `z` the dropped atom's correlation profile (`z_c = gamma_{c d}` over the six
kept atoms) and `N = M[B]` the kept 6x6 hollow block:

* `N * N = (1/3) N + (4/3) 1 - z z^T`  (`sixBlockMatrix_sq`);
* `N z = (1/3) z` and `|z|^2 = 4/3`  (`sixBlockMatrix_mulVec_profile`,
  `sixBlockProfile_dotProduct_self`);
* `((4/3) 1 - N) (N + 1) = z z^T` and the cubic annihilation
  `((4/3) 1 - N) (N - (1/3) 1) (N + 1) = 0` — "spectrum inside `{4/3, 1/3, -1}`"
  in kernel form;
* trace pins `tr N = 0`, `tr N^2 = 20/3`, `tr N^3 = 16/9`, `det N = -16/27`;
* **the full charpoly freeze**
  `det(t 1 - N) = (t + 1)^3 (t - 4/3)^2 (t - 1/3)` — the spectrum is
  `{4/3, 4/3, 1/3, -1, -1, -1}` with multiplicities pinned, for EVERY design on
  the stratum and EVERY dropped atom, with the `1/3`-eigenvector equal to the
  dropped atom's profile.

## The five-block law (drop two atoms `e`, `f`, edge weight `w = gamma_{ef}^2`)

* the two-profile restriction identity  (`fiveBlockMatrix_sq`);
* `|z_e|^2 = |z_f|^2 = 4/3 - w`, `tr = 0`, `tr M[B5]^2 = 4 + 2 w`;
* **the full one-parameter factorization**
  `det(t 1 - M[B5]) = (t + 1)^2 (t - 4/3) ((t - 1/3)^2 - w)`
  (`det_smul_one_sub_fiveBlockMatrix`) — the brief's stretch goal, closed;
* `det M[B5] = 4/27 - (4/3) w`.

## The sevenths reformulation (R-7)

For a triple `T` with complementary four-set `F` (both given as injective
enumerations with disjoint ranges): at uniform share and leverage three,

  `T` dominates  ⟺  `2 . 1 - Gamma[F] ⪰ 0`

(`dominates_triple_iff_posSemidef_quadGramCap_sevenThree`).  Spectrally this is
`lambda_max(Gamma[F]) = 7/3 - lambda_min(Gamma[T])` (the four-set Gram appends a
zero eigenvalue to the reflected triple spectrum), landed EXACTLY as the charpoly
reflection

  `det(t 1_4 - Gamma[F]) = -t . det((7/3 - t) 1_3 - Gamma[T])`

(`det_smul_one_sub_quadGram_reflection_sevenThree`), valid for every real `t` —
the raw material for four-set coefficient laws in the middle band.  The
coordinate-space complement flip at uniform WEIGHT is the landed
`Gtz.dominates_iff_posSemidef_smul_one_sub_subsetSum_compl`; the content added
here is the slot-space (Gram) reading through the rectangular transfer.

## The kit

Everything routes through two generic transfer lemmas proved here once, with no
eigenvalues, no interlacing, and no square roots:

* `det_smul_one_sub_transpose_mul_comm`:
  `det(c 1_p - X^T X) = c^(p-r) det(c 1_r - X X^T)` for every rectangular
  `r x p` block `X` with `r <= p` and EVERY `c` — including `c = 0`, by promoting
  the scaling argument to a polynomial identity between characteristic
  polynomials (`Polynomial.eq_of_infinite_eval_eq`);
* `posSemidef_smul_one_sub_transpose_mul_comm`:
  `c 1 - X^T X ⪰ 0 ⟺ c 1 - X X^T ⪰ 0` for every `c >= 0` — the landed
  level-one `Gtz.posSemidef_one_sub_transpose_comm` extended to every
  nonnegative level by the same Cauchy–Schwarz flip.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Design.FrameConservation
import Gtz.Quantitative.WeightProductFloor
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.MinorSumIdentities

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## 1. The determinant transfer kit -/

private theorem scalarSubEqSmulOneSub {dimCount : ℕ} (levelValue : ℝ)
    (squareBlock : Matrix (Fin dimCount) (Fin dimCount) ℝ) :
    Matrix.scalar (Fin dimCount) levelValue - squareBlock
      = levelValue • (1 : Matrix (Fin dimCount) (Fin dimCount) ℝ) - squareBlock := by
  congr 1
  rw [Matrix.scalar_apply]
  ext rowIndex colIndex
  rw [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The scaling engine: at a NONZERO level the two shifted determinants agree up
to the dimension-gap power, by pulling the level out of both sides and flipping
`det(1 + A B) = det(1 + B A)`. -/
private theorem detFlipNonzero {rankCount widthCount : ℕ}
    (frameBlock : Matrix (Fin rankCount) (Fin widthCount) ℝ)
    (hwide : rankCount ≤ widthCount) {levelValue : ℝ} (hnonzero : levelValue ≠ 0) :
    (levelValue • (1 : Matrix (Fin widthCount) (Fin widthCount) ℝ)
        - frameBlockᵀ * frameBlock).det
      = levelValue ^ (widthCount - rankCount)
        * (levelValue • (1 : Matrix (Fin rankCount) (Fin rankCount) ℝ)
            - frameBlock * frameBlockᵀ).det := by
  have hcancel : levelValue * -levelValue⁻¹ = -1 := by
    field_simp
  have hwidthFactor :
      levelValue • (1 : Matrix (Fin widthCount) (Fin widthCount) ℝ) - frameBlockᵀ * frameBlock
        = levelValue • ((1 : Matrix (Fin widthCount) (Fin widthCount) ℝ)
            + ((-levelValue⁻¹) • frameBlockᵀ) * frameBlock) := by
    rw [smul_add, Matrix.smul_mul, smul_smul, hcancel, neg_one_smul, ← sub_eq_add_neg]
  have hrankFactor :
      levelValue • (1 : Matrix (Fin rankCount) (Fin rankCount) ℝ) - frameBlock * frameBlockᵀ
        = levelValue • ((1 : Matrix (Fin rankCount) (Fin rankCount) ℝ)
            + frameBlock * ((-levelValue⁻¹) • frameBlockᵀ)) := by
    rw [smul_add, Matrix.mul_smul, smul_smul, hcancel, neg_one_smul, ← sub_eq_add_neg]
  rw [hwidthFactor, hrankFactor, Matrix.det_smul, Matrix.det_smul, Fintype.card_fin,
    Fintype.card_fin, Matrix.det_one_add_mul_comm,
    show levelValue ^ widthCount
        = levelValue ^ (widthCount - rankCount) * levelValue ^ rankCount from
      (pow_sub_mul_pow levelValue hwide).symm]
  ring

/-- The scaling identity promoted to the characteristic polynomials: agreement at
every nonzero level is agreement at infinitely many points, hence a polynomial
identity — this is what makes the level-zero case free. -/
private theorem charpolyFlip {rankCount widthCount : ℕ}
    (frameBlock : Matrix (Fin rankCount) (Fin widthCount) ℝ)
    (hwide : rankCount ≤ widthCount) :
    (frameBlockᵀ * frameBlock).charpoly
      = Polynomial.X ^ (widthCount - rankCount) * (frameBlock * frameBlockᵀ).charpoly := by
  refine Polynomial.eq_of_infinite_eval_eq _ _
    (Set.Infinite.mono ?_ ((Set.finite_singleton (0 : ℝ)).infinite_compl))
  intro levelValue hlevel
  have hnonzero : levelValue ≠ 0 := by simpa using hlevel
  simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Matrix.eval_charpoly, scalarSubEqSmulOneSub]
  exact detFlipNonzero frameBlock hwide hnonzero

/-- **THE DETERMINANT TRANSFER.**  For a rectangular `r x p` block `X` with
`r <= p` and EVERY real level `c`,

  `det(c 1_p - X^T X) = c^(p - r) . det(c 1_r - X X^T)` :

the two Gram sides share their nonzero spectrum and the wide side pads with
`p - r` zeros.  Proved with no eigenvalues: scaling plus the flip
`det(1 + A B) = det(1 + B A)` at nonzero levels, then promotion to a polynomial
identity in the characteristic polynomials to absorb `c = 0`.  Consumed below at
`(6,1)`-, `(5,2)`-, `(4,1)`- and `(3,0)`-gap shapes; stated generically because it
is the whole ladder's engine. -/
theorem det_smul_one_sub_transpose_mul_comm {rankCount widthCount : ℕ}
    (frameBlock : Matrix (Fin rankCount) (Fin widthCount) ℝ)
    (hwide : rankCount ≤ widthCount) (levelValue : ℝ) :
    (levelValue • (1 : Matrix (Fin widthCount) (Fin widthCount) ℝ)
        - frameBlockᵀ * frameBlock).det
      = levelValue ^ (widthCount - rankCount)
        * (levelValue • (1 : Matrix (Fin rankCount) (Fin rankCount) ℝ)
            - frameBlock * frameBlockᵀ).det := by
  have heval := congrArg (Polynomial.eval levelValue) (charpolyFlip frameBlock hwide)
  simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Matrix.eval_charpoly, scalarSubEqSmulOneSub] using heval

/-- **A WIDE GRAM BLOCK IS SINGULAR**: `det(X^T X) = 0` whenever the `r x p`
block has `r < p`.  The level-zero reading of the determinant transfer. -/
theorem det_transpose_mul_self_eq_zero_of_lt {rankCount widthCount : ℕ}
    (frameBlock : Matrix (Fin rankCount) (Fin widthCount) ℝ)
    (hnarrow : rankCount < widthCount) :
    (frameBlockᵀ * frameBlock).det = 0 := by
  have hkit := det_smul_one_sub_transpose_mul_comm frameBlock hnarrow.le 0
  rw [zero_smul, zero_sub, zero_smul, zero_sub, Matrix.det_neg, Matrix.det_neg,
    Fintype.card_fin, Fintype.card_fin, zero_pow (Nat.sub_ne_zero_of_lt hnarrow),
    zero_mul, mul_eq_zero] at hkit
  rcases hkit with hsign | hdet
  · exact absurd hsign (pow_ne_zero _ (by norm_num))
  · exact hdet

/-! ## 2. The level PSD flip

The landed `Gtz.posSemidef_one_sub_transpose_comm` is the level-one case; the
sevenths reformulation needs level two, so the same Cauchy–Schwarz argument is
run at a general nonnegative level. -/

private theorem levelContractionIff {rankCount widthCount : ℕ}
    (frameBlock : Matrix (Fin rankCount) (Fin widthCount) ℝ) (levelValue : ℝ) :
    (levelValue • (1 : Matrix (Fin widthCount) (Fin widthCount) ℝ)
        - frameBlockᵀ * frameBlock).PosSemidef
      ↔ ∀ probe : Fin widthCount → ℝ,
          (frameBlock *ᵥ probe) ⬝ᵥ (frameBlock *ᵥ probe) ≤ levelValue * (probe ⬝ᵥ probe) := by
  have hquad : ∀ probe : Fin widthCount → ℝ,
      probe ⬝ᵥ ((levelValue • (1 : Matrix (Fin widthCount) (Fin widthCount) ℝ)
          - frameBlockᵀ * frameBlock) *ᵥ probe)
        = levelValue * (probe ⬝ᵥ probe)
          - (frameBlock *ᵥ probe) ⬝ᵥ (frameBlock *ᵥ probe) := by
    intro probe
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
      dotProduct_comm probe (frameBlockᵀ *ᵥ (frameBlock *ᵥ probe)), dotProduct_mulVec_transpose]
  constructor
  · intro hpsd probe
    have hval := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
    rw [star_trivial, hquad probe] at hval
    linarith
  · intro hcontr
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe => ?_⟩
    · refine isHermitian_of_transpose_eq ?_
      rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.transpose_mul, Matrix.transpose_transpose]
    · rw [star_trivial, hquad probe]
      linarith [hcontr probe]

private theorem levelContractionFlip {rankCount widthCount : ℕ}
    (frameBlock : Matrix (Fin rankCount) (Fin widthCount) ℝ) {levelValue : ℝ}
    (hnonneg : 0 ≤ levelValue)
    (hcontr : ∀ probe : Fin widthCount → ℝ,
      (frameBlock *ᵥ probe) ⬝ᵥ (frameBlock *ᵥ probe) ≤ levelValue * (probe ⬝ᵥ probe))
    (witness : Fin rankCount → ℝ) :
    (frameBlockᵀ *ᵥ witness) ⬝ᵥ (frameBlockᵀ *ᵥ witness)
      ≤ levelValue * (witness ⬝ᵥ witness) := by
  have hkey : (frameBlockᵀ *ᵥ witness) ⬝ᵥ (frameBlockᵀ *ᵥ witness)
      = witness ⬝ᵥ (frameBlock *ᵥ (frameBlockᵀ *ᵥ witness)) :=
    dotProduct_mulVec_transpose frameBlock witness (frameBlockᵀ *ᵥ witness)
  have hCS := dotProduct_sq_le_mul witness (frameBlock *ᵥ (frameBlockᵀ *ᵥ witness))
  have hXv := hcontr (frameBlockᵀ *ᵥ witness)
  have hvnn := dotProduct_self_nonneg (frameBlockᵀ *ᵥ witness)
  have hwnn := dotProduct_self_nonneg witness
  rcases eq_or_lt_of_le hvnn with hzero | hpositive
  · rw [← hzero]
    exact mul_nonneg hnonneg hwnn
  · nlinarith [hkey, hCS, hXv, hpositive, hwnn]

/-- **THE LEVEL PSD FLIP**: `c 1 - X^T X ⪰ 0 ⟺ c 1 - X X^T ⪰ 0` for every
rectangular `X` and every level `c >= 0`.  Extends the landed level-one
`Gtz.posSemidef_one_sub_transpose_comm`; same sqrt-free Cauchy–Schwarz flip,
with the level riding along. -/
theorem posSemidef_smul_one_sub_transpose_mul_comm {rankCount widthCount : ℕ}
    (frameBlock : Matrix (Fin rankCount) (Fin widthCount) ℝ) {levelValue : ℝ}
    (hnonneg : 0 ≤ levelValue) :
    (levelValue • (1 : Matrix (Fin widthCount) (Fin widthCount) ℝ)
        - frameBlockᵀ * frameBlock).PosSemidef
      ↔ (levelValue • (1 : Matrix (Fin rankCount) (Fin rankCount) ℝ)
          - frameBlock * frameBlockᵀ).PosSemidef := by
  have hflipped := levelContractionIff frameBlockᵀ levelValue
  rw [Matrix.transpose_transpose] at hflipped
  rw [levelContractionIff frameBlock levelValue, hflipped]
  constructor
  · exact fun hcontr witness => levelContractionFlip frameBlock hnonneg hcontr witness
  · intro hcontr probe
    have hflip := levelContractionFlip frameBlockᵀ hnonneg hcontr probe
    rwa [Matrix.transpose_transpose] at hflip

/-! ## 3. The (7,3) uniform stratum: private plumbing -/

private theorem leveragePositive (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (atomIndex : Fin 7) :
    0 < leverageOf (D.atom atomIndex) :=
  leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)

/-- The design-side `M`-quadratic law `M^2 = (1/3) M + (4/3) 1` at `(7,3)`-uniform
share, from the landed `Gamma^2 = (7/3) Gamma`.  Kept private: the module's public
surface is the BLOCK ladder; the seven-level trace laws belong to the conservation
module (duplication flagged in the workflow report). -/
private theorem hollowSquareLawSevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    correlationInvolution D * correlationInvolution D
      = (1 / 3 : ℝ) • correlationInvolution D
        + (4 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
  have hsquare := directionGramMatrix_sq_of_uniformShare D huniform (by norm_num)
  rw [show ((3 : ℝ) / 7)⁻¹ = 7 / 3 by norm_num] at hsquare
  rw [correlationInvolution, sub_mul, mul_sub, mul_one, one_mul, hsquare]
  module

/-- The `(a,b)` entry of the `M`-square law, in the summed form every block
restriction consumes. -/
private theorem hollowSquareEntry (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (firstIndex secondIndex : Fin 7) :
    (∑ midIndex, correlationInvolution D firstIndex midIndex
        * correlationInvolution D midIndex secondIndex)
      = (1 / 3 : ℝ) * correlationInvolution D firstIndex secondIndex
        + (4 / 3 : ℝ) * (if firstIndex = secondIndex then 1 else 0) := by
  have hentry : (correlationInvolution D * correlationInvolution D) firstIndex secondIndex
      = ((1 / 3 : ℝ) • correlationInvolution D
          + (4 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ)) firstIndex secondIndex := by
    rw [hollowSquareLawSevenThree D huniform]
  rw [Matrix.mul_apply] at hentry
  simpa only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] using hentry

private theorem hollowSymm (D : WeightedDesign 7 3) (firstIndex secondIndex : Fin 7) :
    correlationInvolution D firstIndex secondIndex
      = correlationInvolution D secondIndex firstIndex := by
  rcases eq_or_ne firstIndex secondIndex with heq | hne
  · rw [heq]
  · rw [correlationInvolution_apply_of_ne D hne, correlationInvolution_apply_of_ne D hne.symm,
      directionGram_comm]

private theorem gramBlockBridge (D : WeightedDesign 7 3) {selCount : ℕ}
    (pick : Fin selCount → Fin 7) :
    (directionFrame D pick)ᵀ * directionFrame D pick
      = (directionGramMatrix D).submatrix pick pick := by
  ext slotRow slotCol
  rw [transpose_mul_directionFrame_apply]
  rfl

/-- `det(b 1 + u u^T) = b^2 (b + 1)` for a unit vector in rank three: the
rank-one-update determinant, purely by `det_fin_three` and the norm relation. -/
private theorem detSmulOneAddAtom (baseValue : ℝ) (unitVec : Fin 3 → ℝ)
    (hnorm : unitVec ⬝ᵥ unitVec = 1) :
    (baseValue • (1 : Matrix (Fin 3) (Fin 3) ℝ) + atomMatrix unitVec).det
      = baseValue ^ 2 * (baseValue + 1) := by
  simp only [dotProduct, Fin.sum_univ_three] at hnorm
  rw [Matrix.det_fin_three]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul, Fin.reduceEq, if_true, if_false, mul_one, mul_zero]
  linear_combination (baseValue ^ 2) * hnorm

/-- `det(b 1 + u u^T + v v^T) = b ((b + 1)^2 - <u,v>^2)` for two unit vectors in
rank three: the rank-two-update determinant. -/
private theorem detSmulOneAddAtomPair (baseValue : ℝ) (vecOne vecTwo : Fin 3 → ℝ)
    (hnormOne : vecOne ⬝ᵥ vecOne = 1) (hnormTwo : vecTwo ⬝ᵥ vecTwo = 1) :
    (baseValue • (1 : Matrix (Fin 3) (Fin 3) ℝ) + atomMatrix vecOne + atomMatrix vecTwo).det
      = baseValue * ((baseValue + 1) ^ 2 - (vecOne ⬝ᵥ vecTwo) ^ 2) := by
  simp only [dotProduct, Fin.sum_univ_three] at hnormOne hnormTwo ⊢
  rw [Matrix.det_fin_three]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul, Fin.reduceEq, if_true, if_false, mul_one, mul_zero]
  linear_combination
    (baseValue ^ 2
        + baseValue * (vecTwo 0 * vecTwo 0 + vecTwo 1 * vecTwo 1 + vecTwo 2 * vecTwo 2))
      * hnormOne
    + (baseValue ^ 2 + baseValue) * hnormTwo

/-! ## 4. The six-block freeze -/

/-- **THE SIX-BLOCK.**  The hollow correlation matrix `M = Gamma - 1` compressed
to the six atoms other than `dropIndex`, enumerated by `Fin.succAbove`. -/
noncomputable def sixBlockMatrix (D : WeightedDesign 7 3) (dropIndex : Fin 7) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  (correlationInvolution D).submatrix dropIndex.succAbove dropIndex.succAbove

/-- **THE DROPPED ATOM'S PROFILE** `z_c = gamma_{c d}`: the correlation of each
kept atom with the dropped one. -/
noncomputable def sixBlockProfile (D : WeightedDesign 7 3) (dropIndex : Fin 7) :
    Fin 6 → ℝ :=
  fun keptIndex => directionGram D (dropIndex.succAbove keptIndex) dropIndex

private theorem profileEntry (D : WeightedDesign 7 3) (dropIndex : Fin 7) (keptIndex : Fin 6) :
    correlationInvolution D (dropIndex.succAbove keptIndex) dropIndex
      = sixBlockProfile D dropIndex keptIndex :=
  correlationInvolution_apply_of_ne D (Fin.succAbove_ne dropIndex keptIndex)

/-- **THE PROFILE NORM**: `|z|^2 = 4/3`.  The diagonal reading of the square law
at the dropped atom — in particular the profile never vanishes. -/
theorem sixBlockProfile_dotProduct_self (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7) :
    sixBlockProfile D dropIndex ⬝ᵥ sixBlockProfile D dropIndex = 4 / 3 := by
  have hsplit : (∑ midIndex : Fin 7, correlationInvolution D midIndex dropIndex
        * correlationInvolution D midIndex dropIndex)
      = correlationInvolution D dropIndex dropIndex
          * correlationInvolution D dropIndex dropIndex
        + ∑ keptIndex : Fin 6,
            correlationInvolution D (dropIndex.succAbove keptIndex) dropIndex
              * correlationInvolution D (dropIndex.succAbove keptIndex) dropIndex :=
    Fin.sum_univ_succAbove _ dropIndex
  have hsymmSum : (∑ midIndex : Fin 7, correlationInvolution D midIndex dropIndex
        * correlationInvolution D midIndex dropIndex)
      = ∑ midIndex : Fin 7, correlationInvolution D dropIndex midIndex
          * correlationInvolution D midIndex dropIndex :=
    Finset.sum_congr rfl fun midIndex _ => by rw [hollowSymm D midIndex dropIndex]
  have hdiag := correlationInvolution_apply_self D (leveragePositive D huniform dropIndex)
  rw [hsymmSum, hollowSquareEntry D huniform dropIndex dropIndex, hdiag] at hsplit
  simp only [if_true, mul_zero, zero_add, mul_one] at hsplit
  have hgoal : sixBlockProfile D dropIndex ⬝ᵥ sixBlockProfile D dropIndex
      = ∑ keptIndex : Fin 6,
          correlationInvolution D (dropIndex.succAbove keptIndex) dropIndex
            * correlationInvolution D (dropIndex.succAbove keptIndex) dropIndex := by
    refine Finset.sum_congr rfl fun keptIndex _ => ?_
    rw [profileEntry]
  rw [hgoal]
  linarith [hsplit]

/-- The profile is nonzero — its norm-squared is `4/3`. -/
theorem sixBlockProfile_ne_zero (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7) :
    sixBlockProfile D dropIndex ≠ 0 := by
  intro hzero
  have hnorm := sixBlockProfile_dotProduct_self D huniform dropIndex
  rw [hzero, zero_dotProduct] at hnorm
  norm_num at hnorm

/-- **(1) THE RESTRICTION IDENTITY.**  Dropping one atom restricts the square law
with a rank-one correction by the dropped atom's profile:

  `M[B]^2 = (1/3) M[B] + (4/3) 1 - z z^T`.

This is the six-block freeze's source; everything below is algebra on it. -/
theorem sixBlockMatrix_sq (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7) :
    sixBlockMatrix D dropIndex * sixBlockMatrix D dropIndex
      = (1 / 3 : ℝ) • sixBlockMatrix D dropIndex
        + (4 / 3 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)
        - atomMatrix (sixBlockProfile D dropIndex) := by
  ext rowIndex colIndex
  have hsplit : (∑ midIndex : Fin 7,
        correlationInvolution D (dropIndex.succAbove rowIndex) midIndex
          * correlationInvolution D midIndex (dropIndex.succAbove colIndex))
      = correlationInvolution D (dropIndex.succAbove rowIndex) dropIndex
          * correlationInvolution D dropIndex (dropIndex.succAbove colIndex)
        + ∑ midIndex : Fin 6,
            correlationInvolution D (dropIndex.succAbove rowIndex) (dropIndex.succAbove midIndex)
              * correlationInvolution D (dropIndex.succAbove midIndex)
                  (dropIndex.succAbove colIndex) :=
    Fin.sum_univ_succAbove _ dropIndex
  rw [hollowSquareEntry D huniform (dropIndex.succAbove rowIndex) (dropIndex.succAbove colIndex),
    hollowSymm D dropIndex (dropIndex.succAbove colIndex), profileEntry D dropIndex rowIndex,
    profileEntry D dropIndex colIndex] at hsplit
  simp only [Fin.succAbove_right_inj] at hsplit
  simp only [Matrix.mul_apply, sixBlockMatrix, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, atomMatrix,
    Matrix.vecMulVec_apply]
  linarith [hsplit]

/-- **(2) THE PROFILE IS A `1/3`-EIGENVECTOR**: `M[B] z = (1/3) z`.  The
off-diagonal reading of the square law along the dropped column. -/
theorem sixBlockMatrix_mulVec_profile (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7) :
    sixBlockMatrix D dropIndex *ᵥ sixBlockProfile D dropIndex
      = (1 / 3 : ℝ) • sixBlockProfile D dropIndex := by
  funext rowIndex
  have hsplit : (∑ midIndex : Fin 7,
        correlationInvolution D (dropIndex.succAbove rowIndex) midIndex
          * correlationInvolution D midIndex dropIndex)
      = correlationInvolution D (dropIndex.succAbove rowIndex) dropIndex
          * correlationInvolution D dropIndex dropIndex
        + ∑ midIndex : Fin 6,
            correlationInvolution D (dropIndex.succAbove rowIndex) (dropIndex.succAbove midIndex)
              * correlationInvolution D (dropIndex.succAbove midIndex) dropIndex :=
    Fin.sum_univ_succAbove _ dropIndex
  rw [hollowSquareEntry D huniform (dropIndex.succAbove rowIndex) dropIndex,
    correlationInvolution_apply_self D (leveragePositive D huniform dropIndex),
    profileEntry D dropIndex rowIndex,
    if_neg (Fin.succAbove_ne dropIndex rowIndex)] at hsplit
  simp only [Matrix.mulVec, dotProduct, sixBlockMatrix, Matrix.submatrix_apply,
    Pi.smul_apply, smul_eq_mul]
  have hterms : (∑ midIndex : Fin 6,
        sixBlockMatrix D dropIndex rowIndex midIndex * sixBlockProfile D dropIndex midIndex)
      = ∑ midIndex : Fin 6,
          correlationInvolution D (dropIndex.succAbove rowIndex) (dropIndex.succAbove midIndex)
            * correlationInvolution D (dropIndex.succAbove midIndex) dropIndex := by
    refine Finset.sum_congr rfl fun midIndex _ => ?_
    rw [sixBlockMatrix, Matrix.submatrix_apply, profileEntry]
  have hgoalSum : (∑ midIndex : Fin 6,
        correlationInvolution D (dropIndex.succAbove rowIndex) (dropIndex.succAbove midIndex)
          * sixBlockProfile D dropIndex midIndex)
      = ∑ midIndex : Fin 6,
          correlationInvolution D (dropIndex.succAbove rowIndex) (dropIndex.succAbove midIndex)
            * correlationInvolution D (dropIndex.succAbove midIndex) dropIndex := by
    refine Finset.sum_congr rfl fun midIndex _ => ?_
    rw [profileEntry]
  rw [hgoalSum]
  linarith [hsplit]

/-- **(3a) THE RANK-ONE FACTORIZATION**: `((4/3) 1 - M[B]) (M[B] + 1) = z z^T`.
The restriction identity rearranged into the product form whose two factors
carry the spectral gap readings. -/
theorem smul_one_sub_sixBlockMatrix_mul_add_one (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7) :
    ((4 / 3 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - sixBlockMatrix D dropIndex)
        * (sixBlockMatrix D dropIndex + 1)
      = atomMatrix (sixBlockProfile D dropIndex) := by
  have hsq := sixBlockMatrix_sq D huniform dropIndex
  rw [sub_mul, mul_add, mul_add, mul_one, mul_one, smul_mul_assoc, one_mul, hsq]
  module

private theorem sixBlockMulProfileAtom (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7) :
    sixBlockMatrix D dropIndex * atomMatrix (sixBlockProfile D dropIndex)
      = (1 / 3 : ℝ) • atomMatrix (sixBlockProfile D dropIndex) := by
  have hvec := sixBlockMatrix_mulVec_profile D huniform dropIndex
  ext rowIndex colIndex
  have hrow := congrFun hvec rowIndex
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow
  simp only [Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply, Matrix.smul_apply,
    smul_eq_mul]
  calc (∑ midIndex : Fin 6, sixBlockMatrix D dropIndex rowIndex midIndex
        * (sixBlockProfile D dropIndex midIndex * sixBlockProfile D dropIndex colIndex))
      = (∑ midIndex : Fin 6, sixBlockMatrix D dropIndex rowIndex midIndex
          * sixBlockProfile D dropIndex midIndex) * sixBlockProfile D dropIndex colIndex := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun midIndex _ => by ring
    _ = 1 / 3 * (sixBlockProfile D dropIndex rowIndex * sixBlockProfile D dropIndex colIndex) := by
        rw [hrow]; ring

/-- **(3) THE CUBIC ANNIHILATION**:
`((4/3) 1 - M[B]) (M[B] - (1/3) 1) (M[B] + 1) = 0`.  The minimal polynomial of
every six-block divides `(x - 4/3)(x - 1/3)(x + 1)` — "spectrum inside
`{4/3, 1/3, -1}`" in kernel-friendly form, with no eigenvalue machinery.  The
`z`-direction is absorbed because `(M[B] - (1/3) 1) z = 0`. -/
theorem sixBlockMatrix_cubic_eq_zero (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7) :
    ((4 / 3 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - sixBlockMatrix D dropIndex)
        * ((sixBlockMatrix D dropIndex - (1 / 3 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ))
            * (sixBlockMatrix D dropIndex + 1))
      = 0 := by
  have hsq := sixBlockMatrix_sq D huniform dropIndex
  have hstep : (sixBlockMatrix D dropIndex - (1 / 3 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ))
        * (sixBlockMatrix D dropIndex + 1)
      = sixBlockMatrix D dropIndex + 1 - atomMatrix (sixBlockProfile D dropIndex) := by
    rw [sub_mul, mul_add, mul_one, smul_mul_assoc, one_mul, hsq]
    module
  rw [hstep, mul_sub, smul_one_sub_sixBlockMatrix_mul_add_one D huniform dropIndex, sub_mul,
    smul_mul_assoc, one_mul, sixBlockMulProfileAtom D huniform dropIndex]
  module

/-- **(4a) TRACE PIN**: `tr M[B] = 0` — the block is hollow. -/
theorem trace_sixBlockMatrix (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7) :
    Matrix.trace (sixBlockMatrix D dropIndex) = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun keptIndex _ => ?_
  rw [Matrix.diag_apply, sixBlockMatrix, Matrix.submatrix_apply]
  exact correlationInvolution_apply_self D
    (leveragePositive D huniform (dropIndex.succAbove keptIndex))

/-- **(4b) TRACE PIN**: `tr M[B]^2 = 20/3` — equivalently the six-block's edge
budget is `sigma_B = 10/3`. -/
theorem trace_sixBlockMatrix_sq (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7) :
    Matrix.trace (sixBlockMatrix D dropIndex * sixBlockMatrix D dropIndex) = 20 / 3 := by
  rw [sixBlockMatrix_sq D huniform dropIndex, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
    trace_sixBlockMatrix D huniform dropIndex, atomMatrix, Matrix.trace_vecMulVec,
    sixBlockProfile_dotProduct_self D huniform dropIndex]
  simp only [Fintype.card_fin, smul_eq_mul]
  norm_num

/-- **(4c) TRACE PIN**: `tr M[B]^3 = 16/9`.  Cross-check against the frozen
spectrum: `2 (4/3)^3 + (1/3)^3 + 3 (-1)^3 = 128/27 + 1/27 - 81/27 = 16/9`. -/
theorem trace_sixBlockMatrix_cube (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7) :
    Matrix.trace (sixBlockMatrix D dropIndex * sixBlockMatrix D dropIndex
      * sixBlockMatrix D dropIndex) = 16 / 9 := by
  have hsq := sixBlockMatrix_sq D huniform dropIndex
  rw [hsq, sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    trace_sixBlockMatrix_sq D huniform dropIndex, trace_sixBlockMatrix D huniform dropIndex,
    Matrix.trace_mul_comm, sixBlockMulProfileAtom D huniform dropIndex, Matrix.trace_smul,
    atomMatrix, Matrix.trace_vecMulVec, sixBlockProfile_dotProduct_self D huniform dropIndex]
  norm_num

/-- The six-block against the direction frame of the kept atoms: shifting by one
converts the hollow block into the kept Gram block. -/
private theorem sixBlockShift (D : WeightedDesign 7 3) (dropIndex : Fin 7) (levelValue : ℝ) :
    levelValue • (1 : Matrix (Fin 6) (Fin 6) ℝ) - sixBlockMatrix D dropIndex
      = (levelValue + 1) • (1 : Matrix (Fin 6) (Fin 6) ℝ)
        - (directionFrame D dropIndex.succAbove)ᵀ * directionFrame D dropIndex.succAbove := by
  have hblock : sixBlockMatrix D dropIndex
      = (directionGramMatrix D).submatrix dropIndex.succAbove dropIndex.succAbove
        - (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
    ext rowIndex colIndex
    simp only [sixBlockMatrix, correlationInvolution, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.one_apply, Fin.succAbove_right_inj]
  rw [gramBlockBridge D dropIndex.succAbove, hblock]
  module

/-- **THE SIX-BLOCK CHARPOLY FREEZE (R-6, full form).**  For every design on the
`(7,3)`-uniform stratum and every dropped atom,

  `det(t 1 - M[B]) = (t + 1)^3 (t - 4/3)^2 (t - 1/3)`  for ALL real `t` :

the spectrum is `{4/3, 4/3, 1/3, -1, -1, -1}`, multiplicities pinned, with the
`1/3`-eigenvector the dropped atom's profile (`sixBlockMatrix_mulVec_profile`).
Proof: shift by one to the kept Gram block, transfer `6x6 -> 3x3` through the
determinant kit, evaluate the frame complement
`X X^T = (7/3) 1 - u_d u_d^T`, and finish with the rank-one-update determinant.
No eigenvalues anywhere; the cubic annihilation and all trace pins are
consequences of this single identity. -/
theorem det_smul_one_sub_sixBlockMatrix (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7)
    (levelValue : ℝ) :
    (levelValue • (1 : Matrix (Fin 6) (Fin 6) ℝ) - sixBlockMatrix D dropIndex).det
      = (levelValue + 1) ^ 3 * (levelValue - 4 / 3) ^ 2 * (levelValue - 1 / 3) := by
  rw [sixBlockShift D dropIndex levelValue,
    det_smul_one_sub_transpose_mul_comm (directionFrame D dropIndex.succAbove) (by norm_num)
      (levelValue + 1)]
  have hframe : directionFrame D dropIndex.succAbove * (directionFrame D dropIndex.succAbove)ᵀ
      = (7 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (unitAtom D dropIndex) := by
    rw [directionFrame_mul_transpose]
    have hfull : (∑ atomIndex : Fin 7, atomMatrix (unitAtom D atomIndex))
        = ((3 : ℝ) / 7)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
      sum_atomMatrix_unitAtom_of_uniformShare D huniform (by norm_num)
    have hsplit : (∑ atomIndex : Fin 7, atomMatrix (unitAtom D atomIndex))
        = atomMatrix (unitAtom D dropIndex)
          + ∑ keptIndex : Fin 6, atomMatrix (unitAtom D (dropIndex.succAbove keptIndex)) :=
      Fin.sum_univ_succAbove _ dropIndex
    rw [show ((3 : ℝ) / 7)⁻¹ = 7 / 3 by norm_num] at hfull
    rw [hfull] at hsplit
    exact eq_sub_of_add_eq' hsplit.symm
  have hnorm : unitAtom D dropIndex ⬝ᵥ unitAtom D dropIndex = 1 :=
    directionGram_self D (leveragePositive D huniform dropIndex)
  have hshift : (levelValue + 1) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - ((7 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (unitAtom D dropIndex))
      = (levelValue - 4 / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + atomMatrix (unitAtom D dropIndex) := by
    module
  rw [hframe, hshift, detSmulOneAddAtom (levelValue - 4 / 3) (unitAtom D dropIndex) hnorm]
  ring

/-- **(4d) THE DETERMINANT PIN**: `det M[B] = -16/27` — the charpoly freeze at
level zero; equals `(4/3)^2 (1/3) (-1)^3` on the frozen spectrum. -/
theorem det_sixBlockMatrix (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropIndex : Fin 7) :
    (sixBlockMatrix D dropIndex).det = -(16 / 27) := by
  have hfreeze := det_smul_one_sub_sixBlockMatrix D huniform dropIndex 0
  rw [zero_smul, zero_sub, Matrix.det_neg, Fintype.card_fin] at hfreeze
  norm_num at hfreeze
  exact hfreeze

/-! ## 5. The five-block law -/

/-- **THE FIVE-BLOCK.**  The hollow correlation matrix compressed to the five
atoms other than `dropOne` and `dropOne.succAbove dropTwo`.  Parametrizing the
second dropped atom through the first drop's `succAbove` chart makes the two
dropped atoms distinct BY CONSTRUCTION — no distinctness hypothesis anywhere in
this section. -/
noncomputable def fiveBlockMatrix (D : WeightedDesign 7 3) (dropOne : Fin 7) (dropTwo : Fin 6) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  (correlationInvolution D).submatrix
    (fun keptIndex => dropOne.succAbove (dropTwo.succAbove keptIndex))
    (fun keptIndex => dropOne.succAbove (dropTwo.succAbove keptIndex))

/-- The first dropped atom's correlation profile over the five kept atoms. -/
noncomputable def fiveBlockProfileOne (D : WeightedDesign 7 3) (dropOne : Fin 7)
    (dropTwo : Fin 6) : Fin 5 → ℝ :=
  fun keptIndex => directionGram D (dropOne.succAbove (dropTwo.succAbove keptIndex)) dropOne

/-- The second dropped atom's correlation profile over the five kept atoms. -/
noncomputable def fiveBlockProfileTwo (D : WeightedDesign 7 3) (dropOne : Fin 7)
    (dropTwo : Fin 6) : Fin 5 → ℝ :=
  fun keptIndex => directionGram D (dropOne.succAbove (dropTwo.succAbove keptIndex))
    (dropOne.succAbove dropTwo)

private theorem sumSplitTwoDrops {valueType : Type*} [AddCommMonoid valueType]
    (summand : Fin 7 → valueType) (dropOne : Fin 7) (dropTwo : Fin 6) :
    (∑ fullIndex : Fin 7, summand fullIndex)
      = summand dropOne + summand (dropOne.succAbove dropTwo)
        + ∑ keptIndex : Fin 5, summand (dropOne.succAbove (dropTwo.succAbove keptIndex)) := by
  have houter : (∑ fullIndex : Fin 7, summand fullIndex)
      = summand dropOne + ∑ innerIndex : Fin 6, summand (dropOne.succAbove innerIndex) :=
    Fin.sum_univ_succAbove summand dropOne
  have hinner : (∑ innerIndex : Fin 6, summand (dropOne.succAbove innerIndex))
      = summand (dropOne.succAbove dropTwo)
        + ∑ keptIndex : Fin 5, summand (dropOne.succAbove (dropTwo.succAbove keptIndex)) :=
    Fin.sum_univ_succAbove (fun innerIndex => summand (dropOne.succAbove innerIndex)) dropTwo
  rw [houter, hinner, add_assoc]

private theorem keptNeDropOne (dropOne : Fin 7) (dropTwo : Fin 6) (keptIndex : Fin 5) :
    dropOne.succAbove (dropTwo.succAbove keptIndex) ≠ dropOne :=
  Fin.succAbove_ne dropOne (dropTwo.succAbove keptIndex)

private theorem keptNeDropSecond (dropOne : Fin 7) (dropTwo : Fin 6) (keptIndex : Fin 5) :
    dropOne.succAbove (dropTwo.succAbove keptIndex) ≠ dropOne.succAbove dropTwo :=
  fun hagree => Fin.succAbove_ne dropTwo keptIndex (Fin.succAbove_right_injective hagree)

private theorem profileOneEntry (D : WeightedDesign 7 3) (dropOne : Fin 7) (dropTwo : Fin 6)
    (keptIndex : Fin 5) :
    correlationInvolution D (dropOne.succAbove (dropTwo.succAbove keptIndex)) dropOne
      = fiveBlockProfileOne D dropOne dropTwo keptIndex :=
  correlationInvolution_apply_of_ne D (keptNeDropOne dropOne dropTwo keptIndex)

private theorem profileTwoEntry (D : WeightedDesign 7 3) (dropOne : Fin 7) (dropTwo : Fin 6)
    (keptIndex : Fin 5) :
    correlationInvolution D (dropOne.succAbove (dropTwo.succAbove keptIndex))
        (dropOne.succAbove dropTwo)
      = fiveBlockProfileTwo D dropOne dropTwo keptIndex :=
  correlationInvolution_apply_of_ne D (keptNeDropSecond dropOne dropTwo keptIndex)

/-- The first profile's norm: `|z_e|^2 = 4/3 - w_{ef}` — the row law with the
other dropped atom's edge removed. -/
theorem fiveBlockProfileOne_dotProduct_self (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropOne : Fin 7)
    (dropTwo : Fin 6) :
    fiveBlockProfileOne D dropOne dropTwo ⬝ᵥ fiveBlockProfileOne D dropOne dropTwo
      = 4 / 3 - edgeWeight D dropOne (dropOne.succAbove dropTwo) := by
  have hsplit := sumSplitTwoDrops
    (fun midIndex => correlationInvolution D midIndex dropOne
      * correlationInvolution D midIndex dropOne) dropOne dropTwo
  have hsymmSum : (∑ midIndex : Fin 7, correlationInvolution D midIndex dropOne
        * correlationInvolution D midIndex dropOne)
      = ∑ midIndex : Fin 7, correlationInvolution D dropOne midIndex
          * correlationInvolution D midIndex dropOne :=
    Finset.sum_congr rfl fun midIndex _ => by rw [hollowSymm D midIndex dropOne]
  have hdiag := correlationInvolution_apply_self D (leveragePositive D huniform dropOne)
  have hedge : correlationInvolution D (dropOne.succAbove dropTwo) dropOne
        * correlationInvolution D (dropOne.succAbove dropTwo) dropOne
      = edgeWeight D dropOne (dropOne.succAbove dropTwo) := by
    rw [correlationInvolution_apply_of_ne D (Fin.succAbove_ne dropOne dropTwo),
      directionGram_comm D (dropOne.succAbove dropTwo) dropOne, edgeWeight, pow_two]
  rw [hsymmSum, hollowSquareEntry D huniform dropOne dropOne, hdiag] at hsplit
  simp only [if_true, mul_zero, zero_add, mul_one] at hsplit
  rw [hedge] at hsplit
  have hgoal : fiveBlockProfileOne D dropOne dropTwo ⬝ᵥ fiveBlockProfileOne D dropOne dropTwo
      = ∑ keptIndex : Fin 5,
          correlationInvolution D (dropOne.succAbove (dropTwo.succAbove keptIndex)) dropOne
            * correlationInvolution D (dropOne.succAbove (dropTwo.succAbove keptIndex))
                dropOne := by
    refine Finset.sum_congr rfl fun keptIndex _ => ?_
    rw [profileOneEntry]
  rw [hgoal]
  linarith [hsplit]

/-- The second profile's norm: `|z_f|^2 = 4/3 - w_{ef}`, symmetrically. -/
theorem fiveBlockProfileTwo_dotProduct_self (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropOne : Fin 7)
    (dropTwo : Fin 6) :
    fiveBlockProfileTwo D dropOne dropTwo ⬝ᵥ fiveBlockProfileTwo D dropOne dropTwo
      = 4 / 3 - edgeWeight D dropOne (dropOne.succAbove dropTwo) := by
  have hsplit := sumSplitTwoDrops
    (fun midIndex => correlationInvolution D midIndex (dropOne.succAbove dropTwo)
      * correlationInvolution D midIndex (dropOne.succAbove dropTwo)) dropOne dropTwo
  have hsymmSum : (∑ midIndex : Fin 7,
        correlationInvolution D midIndex (dropOne.succAbove dropTwo)
          * correlationInvolution D midIndex (dropOne.succAbove dropTwo))
      = ∑ midIndex : Fin 7, correlationInvolution D (dropOne.succAbove dropTwo) midIndex
          * correlationInvolution D midIndex (dropOne.succAbove dropTwo) :=
    Finset.sum_congr rfl fun midIndex _ => by
      rw [hollowSymm D midIndex (dropOne.succAbove dropTwo)]
  have hdiag := correlationInvolution_apply_self D
    (leveragePositive D huniform (dropOne.succAbove dropTwo))
  have hedge : correlationInvolution D dropOne (dropOne.succAbove dropTwo)
        * correlationInvolution D dropOne (dropOne.succAbove dropTwo)
      = edgeWeight D dropOne (dropOne.succAbove dropTwo) := by
    rw [correlationInvolution_apply_of_ne D (Fin.ne_succAbove dropOne dropTwo), edgeWeight,
      pow_two]
  rw [hsymmSum, hollowSquareEntry D huniform (dropOne.succAbove dropTwo)
    (dropOne.succAbove dropTwo), hdiag] at hsplit
  simp only [if_true, mul_zero, zero_add, add_zero, mul_one] at hsplit
  rw [hedge] at hsplit
  have hgoal : fiveBlockProfileTwo D dropOne dropTwo ⬝ᵥ fiveBlockProfileTwo D dropOne dropTwo
      = ∑ keptIndex : Fin 5,
          correlationInvolution D (dropOne.succAbove (dropTwo.succAbove keptIndex))
              (dropOne.succAbove dropTwo)
            * correlationInvolution D (dropOne.succAbove (dropTwo.succAbove keptIndex))
                (dropOne.succAbove dropTwo) := by
    refine Finset.sum_congr rfl fun keptIndex _ => ?_
    rw [profileTwoEntry]
  rw [hgoal]
  linarith [hsplit]

/-- **(5) THE FIVE-BLOCK RESTRICTION IDENTITY.**  Dropping two atoms restricts
the square law with a rank-TWO correction:

  `M[B5]^2 = (1/3) M[B5] + (4/3) 1 - z_e z_e^T - z_f z_f^T`. -/
theorem fiveBlockMatrix_sq (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropOne : Fin 7)
    (dropTwo : Fin 6) :
    fiveBlockMatrix D dropOne dropTwo * fiveBlockMatrix D dropOne dropTwo
      = (1 / 3 : ℝ) • fiveBlockMatrix D dropOne dropTwo
        + (4 / 3 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ)
        - atomMatrix (fiveBlockProfileOne D dropOne dropTwo)
        - atomMatrix (fiveBlockProfileTwo D dropOne dropTwo) := by
  ext rowIndex colIndex
  have hsplit := sumSplitTwoDrops
    (fun midIndex =>
      correlationInvolution D (dropOne.succAbove (dropTwo.succAbove rowIndex)) midIndex
        * correlationInvolution D midIndex (dropOne.succAbove (dropTwo.succAbove colIndex)))
    dropOne dropTwo
  rw [hollowSquareEntry D huniform (dropOne.succAbove (dropTwo.succAbove rowIndex))
      (dropOne.succAbove (dropTwo.succAbove colIndex)),
    hollowSymm D dropOne (dropOne.succAbove (dropTwo.succAbove colIndex)),
    hollowSymm D (dropOne.succAbove dropTwo) (dropOne.succAbove (dropTwo.succAbove colIndex)),
    profileOneEntry D dropOne dropTwo rowIndex, profileOneEntry D dropOne dropTwo colIndex,
    profileTwoEntry D dropOne dropTwo rowIndex, profileTwoEntry D dropOne dropTwo colIndex]
    at hsplit
  simp only [Fin.succAbove_right_inj] at hsplit
  simp only [Matrix.mul_apply, fiveBlockMatrix, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, atomMatrix,
    Matrix.vecMulVec_apply]
  linarith [hsplit]

/-- Trace pin: `tr M[B5] = 0`. -/
theorem trace_fiveBlockMatrix (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropOne : Fin 7)
    (dropTwo : Fin 6) :
    Matrix.trace (fiveBlockMatrix D dropOne dropTwo) = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun keptIndex _ => ?_
  rw [Matrix.diag_apply, fiveBlockMatrix, Matrix.submatrix_apply]
  exact correlationInvolution_apply_self D
    (leveragePositive D huniform (dropOne.succAbove (dropTwo.succAbove keptIndex)))

/-- **THE FIVE-BLOCK TRACE LAW**: `tr M[B5]^2 = 4 + 2 w_{ef}` — the one-parameter
family, with the dropped edge's weight as the parameter. -/
theorem trace_fiveBlockMatrix_sq (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropOne : Fin 7)
    (dropTwo : Fin 6) :
    Matrix.trace (fiveBlockMatrix D dropOne dropTwo * fiveBlockMatrix D dropOne dropTwo)
      = 4 + 2 * edgeWeight D dropOne (dropOne.succAbove dropTwo) := by
  rw [fiveBlockMatrix_sq D huniform dropOne dropTwo, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
    trace_fiveBlockMatrix D huniform dropOne dropTwo, atomMatrix, Matrix.trace_vecMulVec,
    atomMatrix, Matrix.trace_vecMulVec,
    fiveBlockProfileOne_dotProduct_self D huniform dropOne dropTwo,
    fiveBlockProfileTwo_dotProduct_self D huniform dropOne dropTwo]
  simp only [Fintype.card_fin, smul_eq_mul]
  ring

/-- The five-block shift to the kept Gram block. -/
private theorem fiveBlockShift (D : WeightedDesign 7 3) (dropOne : Fin 7) (dropTwo : Fin 6)
    (levelValue : ℝ) :
    levelValue • (1 : Matrix (Fin 5) (Fin 5) ℝ) - fiveBlockMatrix D dropOne dropTwo
      = (levelValue + 1) • (1 : Matrix (Fin 5) (Fin 5) ℝ)
        - (directionFrame D
              (fun keptIndex => dropOne.succAbove (dropTwo.succAbove keptIndex)))ᵀ
          * directionFrame D
              (fun keptIndex => dropOne.succAbove (dropTwo.succAbove keptIndex)) := by
  have hblock : fiveBlockMatrix D dropOne dropTwo
      = (directionGramMatrix D).submatrix
          (fun keptIndex => dropOne.succAbove (dropTwo.succAbove keptIndex))
          (fun keptIndex => dropOne.succAbove (dropTwo.succAbove keptIndex))
        - (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
    ext rowIndex colIndex
    simp only [fiveBlockMatrix, correlationInvolution, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.one_apply, Fin.succAbove_right_inj]
  rw [gramBlockBridge D (fun keptIndex => dropOne.succAbove (dropTwo.succAbove keptIndex)),
    hblock]
  module

/-- **THE FIVE-BLOCK CHARPOLY FACTORIZATION (R-5, full form).**  For every design
on the `(7,3)`-uniform stratum and every ordered pair of dropped atoms,

  `det(t 1 - M[B5]) = (t + 1)^2 (t - 4/3) ((t - 1/3)^2 - w_{ef})`  for ALL `t` :

the five-block spectrum is `{4/3, 1/3 + g, 1/3 - g, -1, -1}` with
`g = |gamma_{ef}|` — the frozen part `{4/3, -1, -1}` plus the split pair around
`1/3` whose half-gap is exactly the dropped edge's correlation.  The brief
allowed landing only the trace and `e_3` consequences if this resisted; the
determinant kit closes the full factorization. -/
theorem det_smul_one_sub_fiveBlockMatrix (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropOne : Fin 7)
    (dropTwo : Fin 6) (levelValue : ℝ) :
    (levelValue • (1 : Matrix (Fin 5) (Fin 5) ℝ) - fiveBlockMatrix D dropOne dropTwo).det
      = (levelValue + 1) ^ 2 * (levelValue - 4 / 3)
        * ((levelValue - 1 / 3) ^ 2 - edgeWeight D dropOne (dropOne.succAbove dropTwo)) := by
  rw [fiveBlockShift D dropOne dropTwo levelValue,
    det_smul_one_sub_transpose_mul_comm
      (directionFrame D (fun keptIndex => dropOne.succAbove (dropTwo.succAbove keptIndex)))
      (by norm_num) (levelValue + 1)]
  have hframe : directionFrame D
        (fun keptIndex => dropOne.succAbove (dropTwo.succAbove keptIndex))
      * (directionFrame D
          (fun keptIndex => dropOne.succAbove (dropTwo.succAbove keptIndex)))ᵀ
      = (7 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (unitAtom D dropOne)
        - atomMatrix (unitAtom D (dropOne.succAbove dropTwo)) := by
    rw [directionFrame_mul_transpose]
    have hfull : (∑ atomIndex : Fin 7, atomMatrix (unitAtom D atomIndex))
        = ((3 : ℝ) / 7)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
      sum_atomMatrix_unitAtom_of_uniformShare D huniform (by norm_num)
    have hsplit := sumSplitTwoDrops (fun atomIndex => atomMatrix (unitAtom D atomIndex))
      dropOne dropTwo
    rw [show ((3 : ℝ) / 7)⁻¹ = 7 / 3 by norm_num] at hfull
    rw [hfull] at hsplit
    have hrearranged : (∑ keptIndex : Fin 5,
          atomMatrix (unitAtom D (dropOne.succAbove (dropTwo.succAbove keptIndex))))
        = (7 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (unitAtom D dropOne)
          - atomMatrix (unitAtom D (dropOne.succAbove dropTwo)) := by
      have hmoved := hsplit.symm
      rw [add_assoc] at hmoved
      exact eq_sub_of_add_eq' (eq_sub_of_add_eq' hmoved)
    exact hrearranged
  have hnormOne : unitAtom D dropOne ⬝ᵥ unitAtom D dropOne = 1 :=
    directionGram_self D (leveragePositive D huniform dropOne)
  have hnormTwo : unitAtom D (dropOne.succAbove dropTwo)
      ⬝ᵥ unitAtom D (dropOne.succAbove dropTwo) = 1 :=
    directionGram_self D (leveragePositive D huniform (dropOne.succAbove dropTwo))
  have hshift : (levelValue + 1) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - ((7 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (unitAtom D dropOne)
          - atomMatrix (unitAtom D (dropOne.succAbove dropTwo)))
      = (levelValue - 4 / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + atomMatrix (unitAtom D dropOne)
        + atomMatrix (unitAtom D (dropOne.succAbove dropTwo)) := by
    module
  have hedge : (unitAtom D dropOne ⬝ᵥ unitAtom D (dropOne.succAbove dropTwo)) ^ 2
      = edgeWeight D dropOne (dropOne.succAbove dropTwo) := by
    rw [edgeWeight, directionGram]
  rw [hframe, hshift, detSmulOneAddAtomPair (levelValue - 4 / 3) (unitAtom D dropOne)
    (unitAtom D (dropOne.succAbove dropTwo)) hnormOne hnormTwo, hedge]
  ring

/-- The five-block determinant pin: `det M[B5] = 4/27 - (4/3) w_{ef}` — the
factorization at level zero (positive at orthogonal drops, vanishing exactly at
`w = 1/9`, the light gate). -/
theorem det_fiveBlockMatrix (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (dropOne : Fin 7)
    (dropTwo : Fin 6) :
    (fiveBlockMatrix D dropOne dropTwo).det
      = 4 / 27 - (4 / 3) * edgeWeight D dropOne (dropOne.succAbove dropTwo) := by
  have hfreeze := det_smul_one_sub_fiveBlockMatrix D huniform dropOne dropTwo 0
  rw [zero_smul, zero_sub, Matrix.det_neg, Fintype.card_fin] at hfreeze
  have hexpand : ((-1 : ℝ)) ^ 5 * (fiveBlockMatrix D dropOne dropTwo).det
      = -(fiveBlockMatrix D dropOne dropTwo).det := by ring
  rw [hexpand] at hfreeze
  have hvalue := congrArg Neg.neg hfreeze
  rw [neg_neg] at hvalue
  rw [hvalue]
  ring

/-! ## 6. The sevenths reformulation (R-7) -/

private theorem sumSplitTripleQuad {valueType : Type*} [AddCommMonoid valueType]
    {tripleSelect : Fin 3 → Fin 7} {quadSelect : Fin 4 → Fin 7}
    (hinjTriple : Function.Injective tripleSelect) (hinjQuad : Function.Injective quadSelect)
    (hdisjoint : ∀ pickIndex coIndex, tripleSelect pickIndex ≠ quadSelect coIndex)
    (summand : Fin 7 → valueType) :
    (∑ fullIndex : Fin 7, summand fullIndex)
      = (∑ pickIndex : Fin 3, summand (tripleSelect pickIndex))
        + ∑ coIndex : Fin 4, summand (quadSelect coIndex) := by
  have hbijective : Function.Bijective (Sum.elim tripleSelect quadSelect) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp⟩
    intro leftPick rightPick hagree
    match leftPick, rightPick with
    | Sum.inl leftIndex, Sum.inl rightIndex =>
        simp only [Sum.elim_inl] at hagree
        exact congrArg Sum.inl (hinjTriple hagree)
    | Sum.inl leftIndex, Sum.inr rightIndex =>
        simp only [Sum.elim_inl, Sum.elim_inr] at hagree
        exact absurd hagree (hdisjoint leftIndex rightIndex)
    | Sum.inr leftIndex, Sum.inl rightIndex =>
        simp only [Sum.elim_inl, Sum.elim_inr] at hagree
        exact absurd hagree.symm (hdisjoint rightIndex leftIndex)
    | Sum.inr leftIndex, Sum.inr rightIndex =>
        simp only [Sum.elim_inr] at hagree
        exact congrArg Sum.inr (hinjQuad hagree)
  have hsum := Fintype.sum_bijective (Sum.elim tripleSelect quadSelect) hbijective
    (fun sumIndex => summand (Sum.elim tripleSelect quadSelect sumIndex)) summand
    (fun sumIndex => rfl)
  rw [← hsum, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]

/-- The quad-side complement law at uniform share: the four kept directions' frame
operator is the tight level minus the triple's frame operator. -/
private theorem quadFrameComplement (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {tripleSelect : Fin 3 → Fin 7} {quadSelect : Fin 4 → Fin 7}
    (hinjTriple : Function.Injective tripleSelect) (hinjQuad : Function.Injective quadSelect)
    (hdisjoint : ∀ pickIndex coIndex, tripleSelect pickIndex ≠ quadSelect coIndex) :
    directionFrame D quadSelect * (directionFrame D quadSelect)ᵀ
      = (7 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - ∑ pickIndex : Fin 3, atomMatrix (unitAtom D (tripleSelect pickIndex)) := by
  rw [directionFrame_mul_transpose]
  have hfull : (∑ atomIndex : Fin 7, atomMatrix (unitAtom D atomIndex))
      = ((3 : ℝ) / 7)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
    sum_atomMatrix_unitAtom_of_uniformShare D huniform (by norm_num)
  have hsplit := sumSplitTripleQuad hinjTriple hinjQuad hdisjoint
    (fun atomIndex => atomMatrix (unitAtom D atomIndex))
  rw [show ((3 : ℝ) / 7)⁻¹ = 7 / 3 by norm_num] at hfull
  rw [hfull] at hsplit
  exact eq_sub_of_add_eq' hsplit.symm

/-- **THE SEVENTHS FLIP, unit-frame form.**  At uniform share `3/7`, for any
triple/quad enumeration of the seven atoms:

  `Sum_{c in T} u_c u_c^T ⪰ (1/3) 1  ⟺  Gamma[F] ⪯ 2 . 1` .

The complement identity turns the triple floor into the quad frame cap in
coordinate space, and the level-two PSD flip transfers it to the 4x4 Gram block.
Spectrally: `lambda_max(Gamma[F]) = 7/3 - lambda_min(Gamma[T])`, since the
four-set Gram carries the reflected triple spectrum plus one forced zero. -/
theorem posSemidef_unitFrameSum_sub_iff_quadGramCap_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (tripleSelect : Fin 3 → Fin 7) (quadSelect : Fin 4 → Fin 7)
    (hinjTriple : Function.Injective tripleSelect) (hinjQuad : Function.Injective quadSelect)
    (hdisjoint : ∀ pickIndex coIndex, tripleSelect pickIndex ≠ quadSelect coIndex) :
    ((∑ pickIndex : Fin 3, atomMatrix (unitAtom D (tripleSelect pickIndex)))
        - (1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef
      ↔ ((2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
          - (directionGramMatrix D).submatrix quadSelect quadSelect).PosSemidef := by
  have hcompl : (∑ pickIndex : Fin 3, atomMatrix (unitAtom D (tripleSelect pickIndex)))
        - (1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - directionFrame D quadSelect * (directionFrame D quadSelect)ᵀ := by
    rw [quadFrameComplement D huniform hinjTriple hinjQuad hdisjoint]
    module
  rw [hcompl, ← gramBlockBridge D quadSelect]
  exact (posSemidef_smul_one_sub_transpose_mul_comm (directionFrame D quadSelect)
    (by norm_num)).symm

private theorem posSemidefSmulIff {dimCount : ℕ} {block : Matrix (Fin dimCount) (Fin dimCount) ℝ}
    {scaleValue : ℝ} (hpositive : 0 < scaleValue) :
    (scaleValue • block).PosSemidef ↔ block.PosSemidef := by
  constructor
  · intro hscaled
    have hback := hscaled.smul (a := scaleValue⁻¹) (by positivity)
    rwa [smul_smul, inv_mul_cancel₀ hpositive.ne', one_smul] at hback
  · exact fun hbase => hbase.smul hpositive.le

/-- **THE SEVENTHS THEOREM (R-7).**  On the equal-share `(7,3)` stratum
(uniform share `3/7` and leverage `3`), a triple dominates IF AND ONLY IF the
complementary four-set's direction Gram is capped at two:

  `T dominates  ⟺  2 . 1 - Gamma[F] ⪰ 0`  (equivalently
  `lambda_max(M[F]) <= 1`).

R3 in four-set form: rank-three GTZ at `(7,3)`-uniform says every such design
has a four-set with `lambda_max(Gamma[F]) <= 2` — every rank-3 projection chart
on `R^7` with constant diagonal `3/7` has a `4x4` principal block of norm at
most `6/7`.  The coordinate-space complement flip at uniform weight is landed as
`Gtz.dominates_iff_posSemidef_smul_one_sub_subsetSum_compl`; this is its
slot-space (Gram) upgrade through the rectangular transfer.  Both hypotheses are
load-bearing: uniform share alone does not pin the leverages, and `Dominates` is
not invariant under the rescaling that fixes the shares. -/
theorem dominates_triple_iff_posSemidef_quadGramCap_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    (tripleSelect : Fin 3 → Fin 7) (quadSelect : Fin 4 → Fin 7)
    (hinjTriple : Function.Injective tripleSelect) (hinjQuad : Function.Injective quadSelect)
    (hdisjoint : ∀ pickIndex coIndex, tripleSelect pickIndex ≠ quadSelect coIndex) :
    Dominates D (Finset.image tripleSelect Finset.univ)
      ↔ ((2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
          - (directionGramMatrix D).submatrix quadSelect quadSelect).PosSemidef := by
  have hsubset := subsetSum_eq_smul_sum_atomMatrix_unitAtom D hleverage (by norm_num)
    (Finset.image tripleSelect Finset.univ)
  have himage : (∑ atomIndex ∈ Finset.image tripleSelect Finset.univ,
        atomMatrix (unitAtom D atomIndex))
      = ∑ pickIndex : Fin 3, atomMatrix (unitAtom D (tripleSelect pickIndex)) :=
    Finset.sum_image fun leftPick _ rightPick _ hagree => hinjTriple hagree
  rw [himage] at hsubset
  unfold Dominates
  rw [hsubset]
  have hscaled : (3 : ℝ) • (∑ pickIndex : Fin 3, atomMatrix (unitAtom D (tripleSelect pickIndex)))
        - (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = (3 : ℝ) • ((∑ pickIndex : Fin 3, atomMatrix (unitAtom D (tripleSelect pickIndex)))
          - (1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
    module
  rw [hscaled, posSemidefSmulIff (by norm_num : (0 : ℝ) < 3)]
  exact posSemidef_unitFrameSum_sub_iff_quadGramCap_sevenThree D huniform tripleSelect quadSelect
    hinjTriple hinjQuad hdisjoint

/-- **THE FOUR-SET CHARPOLY REFLECTION.**  At uniform share, for every
triple/quad enumeration and EVERY real level,

  `det(t 1_4 - Gamma[F]) = -t . det((7/3 - t) 1_3 - Gamma[T])` :

the four-set Gram's spectrum is `{0} + (7/3 - spec Gamma[T])` as an exact
polynomial identity — the complete Q-dictionary for four-sets, subsuming the
sevenths eigenvalue reading and the generic rank-degeneracy
`det Gamma[F] = 0` (evaluate at `t = 0`).  Raw material for the middle band's
four-set coefficient laws. -/
theorem det_smul_one_sub_quadGram_reflection_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (tripleSelect : Fin 3 → Fin 7) (quadSelect : Fin 4 → Fin 7)
    (hinjTriple : Function.Injective tripleSelect) (hinjQuad : Function.Injective quadSelect)
    (hdisjoint : ∀ pickIndex coIndex, tripleSelect pickIndex ≠ quadSelect coIndex)
    (levelValue : ℝ) :
    (levelValue • (1 : Matrix (Fin 4) (Fin 4) ℝ)
        - (directionGramMatrix D).submatrix quadSelect quadSelect).det
      = -levelValue
        * ((7 / 3 - levelValue) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
            - (directionGramMatrix D).submatrix tripleSelect tripleSelect).det := by
  rw [← gramBlockBridge D quadSelect,
    det_smul_one_sub_transpose_mul_comm (directionFrame D quadSelect) (by norm_num) levelValue,
    quadFrameComplement D huniform hinjTriple hinjQuad hdisjoint]
  have hswap : levelValue • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - ((7 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
          - ∑ pickIndex : Fin 3, atomMatrix (unitAtom D (tripleSelect pickIndex)))
      = -((7 / 3 - levelValue) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
          - ∑ pickIndex : Fin 3, atomMatrix (unitAtom D (tripleSelect pickIndex))) := by
    module
  rw [hswap, Matrix.det_neg, Fintype.card_fin]
  have hframeTriple : (∑ pickIndex : Fin 3, atomMatrix (unitAtom D (tripleSelect pickIndex)))
      = directionFrame D tripleSelect * (directionFrame D tripleSelect)ᵀ :=
    (directionFrame_mul_transpose D tripleSelect).symm
  have hsquareSwap : ((7 / 3 - levelValue) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - directionFrame D tripleSelect * (directionFrame D tripleSelect)ᵀ).det
      = ((7 / 3 - levelValue) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (directionFrame D tripleSelect)ᵀ * directionFrame D tripleSelect).det := by
    rw [det_smul_one_sub_transpose_mul_comm (directionFrame D tripleSelect) le_rfl
      (7 / 3 - levelValue)]
    norm_num
  rw [hframeTriple, hsquareSwap, gramBlockBridge D tripleSelect]
  norm_num

end Gtz
