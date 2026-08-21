/-
# The hinge is FALSE over `ℂ` — at rank two, and at the target cell `(6,3)`

The campaign's hinge (`Gtz.HingeHoldsAtSize`) says that every exact tie carries a
parallel pair.  Over `ℝ` it is a THEOREM at rank two
(`Gtz.hingeHoldsAtSize_rank_two`), FALSE at `(5,3)` (the diamond,
`Gtz.not_hingeHoldsAtSize_five_three`) and OPEN at `(6,3)`, where it is the
campaign's route to `Gtz.GtzWeighted 6 3`.

This file settles the complex question.  `Gtz.ComplexHingeHoldsAtSize` is the
same sentence with `gᵀ` read as `g*` and the ratio taken in `ℂ`.  It is FALSE at
`(4,2)` and FALSE at `(6,3)`, by two explicit designs.

## Why rank two decides, and what the real ingredient is

Write a rank-two atom as `g g* = (u/2)(1 + n . sigma)` with `u = |g|²` and `n` a
unit vector of `ℝ³` — the Bloch vector.  Then Parseval reads
`Sum_c w_c = 1` and `Sum_c w_c n_c = 0` with `w_c = t_c u_c / 2`, and
`|<g_a,g_b>|² = u_a u_b (1 + n_a . n_b)/2`.  Two atoms are parallel exactly when
their Bloch vectors agree, and the design is unitarily equivalent to a REAL one
exactly when the Bloch vectors lie on one great circle.

With every `u_c = 2` a pair dominates exactly when `n_a . n_b <= -1/2`, so a tie
is `min_{a<b} n_a . n_b = -1/2`.  On a CIRCLE three directions pairwise at 120
degrees are the Mercedes frame and a fourth atom must repeat one of them — that
is the real hinge.  On the SPHERE the same minimum is reached by four DISTINCT
directions, and `Gtz.complexHingeAtom` below is such a configuration.

The dimension count behind that sentence is already shipped:
`Gtz.finrank_symmetricTracelessSubmodule_atRankTwo = 2` against
`Gtz.finrank_hermitianTracelessSubmodule_atRankTwo = 3`
(`Gtz/Quantitative/RankTwoRealnessCount.lean`).  It is the same `2` versus `3`
that the Veronese factorisation of `Gtz/Wave/RankTwoTieClassification.lean`
consumes: `Gtz.couplingVeronese` has THREE columns because
`dim_ℝ Sym₂(ℝ²) = 3`, and its complex counterpart would have FOUR, so
`Gtz.trace_couplingProjection` would read `4` against the field-blind
`Gtz.trace_normalizedCoupling = 2k - 1 = 3` and the trace sandwich
`Gtz.eq_of_trace_sandwich` would have one dimension of slack.  The witness below
lives in exactly that one dimension of slack: it has FOUR parallel classes.

## The two witnesses

`Gtz.complexHingeDesign` — four atoms of `ℂ²`, weights `(5/22, 5/22, 3/11, 3/11)`:

    g₀ = (3e, e)   g₁ = (e, 3e)   g₂ = (1, ω)   g₃ = (1, ω²)

with `e = 1/√5` and `ω = e^{2πi/3}`.  Every squared length is `2`; the six
overlap products `⟨g,h⟩⟨h,g⟩` are `36/25` once, `7/5` four times and `1` once.
The pair excess determinant is `1 - overlap`, so it is `0` at `{2,3}` and
strictly negative at the other five pairs: `{2,3}` dominates, nothing dominates
strictly, and no overlap reaches `4 = u_a u_b`, so no two atoms are parallel.

`Gtz.complexHingeSixDesign` — six atoms of `ℂ³`, weights
`(3/88, 81/440, 16/55, 16/55, 4/25, 1/25)`:

    h_c = (g_c, 0) for c ≤ 3,   h₄ = (f, f/2, 0),   h₅ = (0, 0, 5)

with `f = √2`, so `|h₄|² = 5/2` and `|h₅|² = 25`.  The first five atoms carry no
third coordinate, so a triple that misses `h₅` has `(S_C - 1)₂₂ = -1` and is not
positive definite.  A triple `{a, b, 5}` has
`det (S_C - 1) = 24 · (excess of the pair {a,b})`, and every one of the ten pair
excesses is at most zero.  The triple `{2,3,5}` has gap
`[[1,-1,0],[-1,1,0],[0,0,24]]`, a sum of two rank-one atoms, hence positive
semidefinite.  So the design is a tie, and its largest overlap ratio is
`49/50 < 1`: no parallel pair.

## What this does and does not say

It says the field-blindness ceiling of the campaign holds for the HINGE and not
only for `Gtz.DiscriminantCovering`: any instrument every ingredient of which
survives the passage to `ℂ` admits `Gtz.complexHingeSixDesign` as a feasible
point, so it cannot prove `Gtz.HingeHoldsAtSize 6 3`.  It says NOTHING about the
real hinge, which stays open, and it produces no dominating triple of any real
design.
-/
import Mathlib
import Gtz.Complex.ComplexWitness
import Gtz.Complex.PerRankConstantLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Complex

open scoped ComplexOrder

variable {m k : ℕ}

/-! ## 1. The complex hinge -/

/-- **A complex exact tie.**  The word-for-word transport of `Gtz.IsTie`: some
`k`-subset dominates weakly and none dominates strictly. -/
def ComplexIsTie (D : ComplexWeightedDesign m k) : Prop :=
  (∃ C : Finset (Fin m), C.card = k ∧ ComplexDominates D C) ∧
    ∀ C : Finset (Fin m), C.card = k →
      ¬ ((∑ atomLabel ∈ C, complexAtom (D.atom atomLabel)) - 1).PosDef

/-- **A complex parallel pair.**  The transport of `Gtz.HasParallelPair`, with the
ratio taken in `ℂ`: this is the WEAKEST reading, so refuting it refutes every
stricter one. -/
def ComplexHasParallelPair (D : ComplexWeightedDesign m k) : Prop :=
  ∃ (keptLabel dropLabel : Fin m) (ratio : ℂ),
    keptLabel ≠ dropLabel ∧ D.atom dropLabel = ratio • D.atom keptLabel

/-- **The complex hinge at a size.**  The transport of `Gtz.HingeHoldsAtSize`. -/
def ComplexHingeHoldsAtSize (size rank : ℕ) : Prop :=
  ∀ D : ComplexWeightedDesign size rank, ComplexIsTie D → ComplexHasParallelPair D

/-! ## 2. Two obstructions to positive definiteness -/

/-- A matrix with a negative diagonal entry is not positive definite. -/
theorem not_posDef_of_diag_eq_neg_one {size : ℕ} {gapMatrix : Matrix (Fin size) (Fin size) ℂ}
    {index : Fin size} (hentry : gapMatrix index index = -1) : ¬ gapMatrix.PosDef := by
  intro hposDef
  have hpos : (0 : ℂ) < gapMatrix index index := hposDef.diag_pos
  rw [hentry] at hpos
  have hreal : (0 : ℝ) < ((-1 : ℂ)).re := by
    have := Complex.lt_def.mp hpos
    simpa using this.1
  norm_num at hreal

/-- A matrix whose determinant is a nonpositive real is not positive definite. -/
theorem not_posDef_of_det_eq_ofReal_nonpos {size : ℕ}
    {gapMatrix : Matrix (Fin size) (Fin size) ℂ} {value : ℝ}
    (hdet : gapMatrix.det = (value : ℂ)) (hvalue : value ≤ 0) : ¬ gapMatrix.PosDef := by
  intro hposDef
  have hpos : (0 : ℂ) < gapMatrix.det := hposDef.det_pos
  rw [hdet] at hpos
  have hreal : (0 : ℝ) < value := by
    have := Complex.lt_def.mp hpos
    simpa using this.1
  linarith

/-! ## 3. Parallel atoms saturate Cauchy–Schwarz

The one general fact the no-parallel-pair half needs: if `h = z • g` then the
overlap product `⟨g,h⟩⟨h,g⟩` is exactly `|g|²|h|²`.  So an overlap strictly below
the product of the squared lengths certifies non-parallelism, and that is a
polynomial statement about the Gram. -/

theorem starDot_smul_right (scale : ℂ) (leftVec rightVec : Fin k → ℂ) :
    star leftVec ⬝ᵥ (scale • rightVec) = scale * (star leftVec ⬝ᵥ rightVec) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem starDot_smul_left (scale : ℂ) (leftVec rightVec : Fin k → ℂ) :
    star (scale • leftVec) ⬝ᵥ rightVec
      = (starRingEnd ℂ) scale * (star leftVec ⬝ᵥ rightVec) := by
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, RCLike.star_def,
    map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The saturation law.**  A parallel pair has overlap product equal to the
product of the two squared lengths. -/
theorem overlap_eq_of_parallel {leftVec rightVec : Fin k → ℂ} {scale : ℂ}
    (hparallel : rightVec = scale • leftVec) :
    (star leftVec ⬝ᵥ rightVec) * (star rightVec ⬝ᵥ leftVec)
      = (star leftVec ⬝ᵥ leftVec) * (star rightVec ⬝ᵥ rightVec) := by
  subst hparallel
  simp only [starDot_smul_right, starDot_smul_left]
  ring

/-- The contrapositive, in the shape the witnesses supply: an overlap product
strictly below the product of the squared lengths forbids parallelism. -/
theorem not_parallel_of_overlap_ne {leftVec rightVec : Fin k → ℂ}
    (hne : (star leftVec ⬝ᵥ rightVec) * (star rightVec ⬝ᵥ leftVec)
      ≠ (star leftVec ⬝ᵥ leftVec) * (star rightVec ⬝ᵥ rightVec)) :
    ∀ scale : ℂ, rightVec ≠ scale • leftVec :=
  fun scale hparallel => hne (overlap_eq_of_parallel hparallel)

/-! ## 4. The two amplitudes

`fifthAmp = 1/√5` and `rootTwoAmp = √2`.  Only their squares and their product
ever appear, so the whole certificate is rational arithmetic on top of three
identities. -/

/-- `1/√5`. -/
noncomputable def fifthAmp : ℂ := (((Real.sqrt 5)⁻¹ : ℝ) : ℂ)

/-- `√2`. -/
noncomputable def rootTwoAmp : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

theorem fifthAmp_conj : (starRingEnd ℂ) fifthAmp = fifthAmp := Complex.conj_ofReal _

theorem rootTwoAmp_conj : (starRingEnd ℂ) rootTwoAmp = rootTwoAmp := Complex.conj_ofReal _

theorem fifthAmp_sq : fifthAmp * fifthAmp = 1 / 5 := by
  have hpos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hreal : ((Real.sqrt 5)⁻¹ : ℝ) * ((Real.sqrt 5)⁻¹ : ℝ) = 1 / 5 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 5)]
    norm_num
  rw [fifthAmp, ← Complex.ofReal_mul, hreal]
  norm_num

theorem rootTwoAmp_sq : rootTwoAmp * rootTwoAmp = 2 := by
  rw [rootTwoAmp, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- The conjugated cube root, as the square. -/
theorem omegaRoot_sq_conj : (starRingEnd ℂ) (omegaRoot ^ 2) = omegaRoot := by
  rw [map_pow, omegaRoot_conj_eq, ← pow_mul]
  calc omegaRoot ^ (2 * 2) = omegaRoot ^ 3 * omegaRoot := by ring
    _ = omegaRoot := by rw [omegaRoot_cube, one_mul]

theorem omegaRoot_pair : omegaRoot + omegaRoot ^ 2 = -1 := by
  linear_combination omegaRoot_sum

theorem omegaRoot_sq_star_mul : (starRingEnd ℂ) (omegaRoot ^ 2) * omegaRoot ^ 2 = 1 := by
  rw [omegaRoot_sq_conj]
  calc omegaRoot * omegaRoot ^ 2 = omegaRoot ^ 3 := by ring
    _ = 1 := omegaRoot_cube

/-! ## 5. The `(4,2)` witness -/

/-- The four atoms.  `g₀` and `g₁` are real and carry Bloch vectors
`(3/5, 0, ±4/5)`; `g₂` and `g₃` carry `(-1/2, ±√3/2, 0)`.  The four directions are
distinct and do not lie on one great circle. -/
noncomputable def complexHingeAtom : Fin 4 → Fin 2 → ℂ :=
  ![![3 * fifthAmp, fifthAmp],
    ![fifthAmp, 3 * fifthAmp],
    ![1, omegaRoot],
    ![1, omegaRoot ^ 2]]

/-- The four weights.  Rational: the Bloch barycentre condition is
`2p(3/5) = 2q(1/2)` with `2p + 2q = 1`. -/
noncomputable def complexHingeWeight : Fin 4 → ℝ := ![5 / 22, 5 / 22, 3 / 11, 3 / 11]

theorem complexHingeAtom_zero : complexHingeAtom 0 = ![3 * fifthAmp, fifthAmp] := rfl
theorem complexHingeAtom_one : complexHingeAtom 1 = ![fifthAmp, 3 * fifthAmp] := rfl
theorem complexHingeAtom_two : complexHingeAtom 2 = ![1, omegaRoot] := rfl
theorem complexHingeAtom_three : complexHingeAtom 3 = ![1, omegaRoot ^ 2] := rfl

theorem complexHingeWeight_pos : ∀ atomLabel, 0 < complexHingeWeight atomLabel := by
  intro atomLabel
  fin_cases atomLabel <;> norm_num [complexHingeWeight]

theorem complexHingeWeight_sum_one : ∑ atomLabel, complexHingeWeight atomLabel = 1 := by
  simp only [complexHingeWeight, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_fin_one]
  norm_num

/-! ### The four rank-one atoms, entry by entry -/

theorem complexAtom_hinge_zero :
    complexAtom (complexHingeAtom 0) = !![9 / 5, 3 / 5; 3 / 5, 1 / 5] := by
  have hfifth := fifthAmp_sq
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [complexAtom, Matrix.vecMulVec_apply, complexHingeAtom_zero, Pi.star_apply,
      RCLike.star_def, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.of_apply,
      Matrix.empty_val',
      map_mul, Complex.conj_ofNat, fifthAmp_conj]
  · linear_combination (9 : ℂ) * hfifth
  · linear_combination (3 : ℂ) * hfifth
  · linear_combination (3 : ℂ) * hfifth
  · linear_combination hfifth

theorem complexAtom_hinge_one :
    complexAtom (complexHingeAtom 1) = !![1 / 5, 3 / 5; 3 / 5, 9 / 5] := by
  have hfifth := fifthAmp_sq
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [complexAtom, Matrix.vecMulVec_apply, complexHingeAtom_one, Pi.star_apply,
      RCLike.star_def, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.of_apply,
      Matrix.empty_val',
      map_mul, Complex.conj_ofNat, fifthAmp_conj]
  · linear_combination hfifth
  · linear_combination (3 : ℂ) * hfifth
  · linear_combination (3 : ℂ) * hfifth
  · linear_combination (9 : ℂ) * hfifth

theorem complexAtom_hinge_two :
    complexAtom (complexHingeAtom 2) = !![1, omegaRoot ^ 2; omegaRoot, 1] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [complexAtom, Matrix.vecMulVec_apply, complexHingeAtom_two, Pi.star_apply,
      RCLike.star_def, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.of_apply,
      Matrix.empty_val',
      map_one, omegaRoot_conj_eq]
  · norm_num
  · norm_num
  · norm_num
  · linear_combination omegaRoot_cube

theorem complexAtom_hinge_three :
    complexAtom (complexHingeAtom 3) = !![1, omegaRoot; omegaRoot ^ 2, 1] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [complexAtom, Matrix.vecMulVec_apply, complexHingeAtom_three, Pi.star_apply,
      RCLike.star_def, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.of_apply,
      Matrix.empty_val',
      map_one, omegaRoot_sq_conj]
  · norm_num
  · norm_num
  · norm_num
  · linear_combination omegaRoot_cube

/-- **Parseval.**  The diagonal is `(5/22)(9/5 + 1/5) + 6/11 = 1` and the
off-diagonal is `(5/22)(3/5 + 3/5) + (3/11)(omega + omega^2) = 6/22 - 3/11 = 0`. -/
theorem complexHingeParseval :
    ∑ atomLabel, ((complexHingeWeight atomLabel : ℝ) : ℂ)
      • complexAtom (complexHingeAtom atomLabel) = 1 := by
  have hpair := omegaRoot_pair
  rw [Fin.sum_univ_four, complexAtom_hinge_zero, complexAtom_hinge_one,
    complexAtom_hinge_two, complexAtom_hinge_three]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [complexHingeWeight, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.cons_val', Matrix.of_apply,
      Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, Complex.ofReal_div,
      Complex.ofReal_ofNat] <;>
    norm_num <;>
    linear_combination (3 / 11 : ℂ) * hpair

/-- **The `(4,2)` complex design.** -/
noncomputable def complexHingeDesign : ComplexWeightedDesign 4 2 where
  atom := complexHingeAtom
  weight := complexHingeWeight
  weight_pos := complexHingeWeight_pos
  weight_sum_one := complexHingeWeight_sum_one
  isParseval := complexHingeParseval

@[simp] theorem complexHingeDesign_atom : complexHingeDesign.atom = complexHingeAtom := rfl

/-! ### The Gram of the witness -/

/-- Every squared length is `2`. -/
theorem complexHingeNorm (atomLabel : Fin 4) :
    star (complexHingeAtom atomLabel) ⬝ᵥ complexHingeAtom atomLabel = 2 := by
  have hfifth := fifthAmp_sq
  have hstar := omegaRoot_star_mul
  have hsqstar := omegaRoot_sq_star_mul
  fin_cases atomLabel
  · rw [show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl, complexHingeAtom_zero, starDot_pair,
      map_mul, map_ofNat, fifthAmp_conj]
    linear_combination (10 : ℂ) * hfifth
  · rw [show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl, complexHingeAtom_one, starDot_pair,
      map_mul, map_ofNat, fifthAmp_conj]
    linear_combination (10 : ℂ) * hfifth
  · rw [show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl, complexHingeAtom_two, starDot_pair,
      map_one]
    linear_combination hstar
  · rw [show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl, complexHingeAtom_three, starDot_pair,
      map_one]
    linear_combination hsqstar

/-! ### The six overlap products

Each is one `linear_combination` on top of `e² = 1/5`, `omega + omega² = -1` and
`omega³ = 1`.  The values are `36/25`, `7/5` four times, and `1`. -/

theorem complexHingeOv_zero_one :
    (star (complexHingeAtom 0) ⬝ᵥ complexHingeAtom 1)
      * (star (complexHingeAtom 1) ⬝ᵥ complexHingeAtom 0) = 36 / 25 := by
  have hfifth := fifthAmp_sq
  rw [complexHingeAtom_zero, complexHingeAtom_one, starDot_pair, starDot_pair]
  simp only [map_mul, Complex.conj_ofNat, fifthAmp_conj]
  linear_combination (36 * fifthAmp * fifthAmp + 36 / 5 : ℂ) * hfifth

theorem complexHingeOv_zero_two :
    (star (complexHingeAtom 0) ⬝ᵥ complexHingeAtom 2)
      * (star (complexHingeAtom 2) ⬝ᵥ complexHingeAtom 0) = 7 / 5 := by
  have hfifth := fifthAmp_sq
  have hpair := omegaRoot_pair
  have hcube := omegaRoot_cube
  rw [complexHingeAtom_zero, complexHingeAtom_two, starDot_pair, starDot_pair]
  simp only [map_mul, Complex.conj_ofNat, fifthAmp_conj, map_one, omegaRoot_conj_eq]
  linear_combination (3 * fifthAmp * fifthAmp : ℂ) * hpair
    + (fifthAmp * fifthAmp : ℂ) * hcube + (7 : ℂ) * hfifth

theorem complexHingeOv_zero_three :
    (star (complexHingeAtom 0) ⬝ᵥ complexHingeAtom 3)
      * (star (complexHingeAtom 3) ⬝ᵥ complexHingeAtom 0) = 7 / 5 := by
  have hfifth := fifthAmp_sq
  have hpair := omegaRoot_pair
  have hcube := omegaRoot_cube
  rw [complexHingeAtom_zero, complexHingeAtom_three, starDot_pair, starDot_pair]
  simp only [map_mul, Complex.conj_ofNat, fifthAmp_conj, map_one, omegaRoot_sq_conj]
  linear_combination (3 * fifthAmp * fifthAmp : ℂ) * hpair
    + (fifthAmp * fifthAmp : ℂ) * hcube + (7 : ℂ) * hfifth

theorem complexHingeOv_one_two :
    (star (complexHingeAtom 1) ⬝ᵥ complexHingeAtom 2)
      * (star (complexHingeAtom 2) ⬝ᵥ complexHingeAtom 1) = 7 / 5 := by
  have hfifth := fifthAmp_sq
  have hpair := omegaRoot_pair
  have hcube := omegaRoot_cube
  rw [complexHingeAtom_one, complexHingeAtom_two, starDot_pair, starDot_pair]
  simp only [map_mul, Complex.conj_ofNat, fifthAmp_conj, map_one, omegaRoot_conj_eq]
  linear_combination (3 * fifthAmp * fifthAmp : ℂ) * hpair
    + (9 * fifthAmp * fifthAmp : ℂ) * hcube + (7 : ℂ) * hfifth

theorem complexHingeOv_one_three :
    (star (complexHingeAtom 1) ⬝ᵥ complexHingeAtom 3)
      * (star (complexHingeAtom 3) ⬝ᵥ complexHingeAtom 1) = 7 / 5 := by
  have hfifth := fifthAmp_sq
  have hpair := omegaRoot_pair
  have hcube := omegaRoot_cube
  rw [complexHingeAtom_one, complexHingeAtom_three, starDot_pair, starDot_pair]
  simp only [map_mul, Complex.conj_ofNat, fifthAmp_conj, map_one, omegaRoot_sq_conj]
  linear_combination (3 * fifthAmp * fifthAmp : ℂ) * hpair
    + (9 * fifthAmp * fifthAmp : ℂ) * hcube + (7 : ℂ) * hfifth

theorem complexHingeOv_two_three :
    (star (complexHingeAtom 2) ⬝ᵥ complexHingeAtom 3)
      * (star (complexHingeAtom 3) ⬝ᵥ complexHingeAtom 2) = 1 := by
  have hpair := omegaRoot_pair
  have hcube := omegaRoot_cube
  rw [complexHingeAtom_two, complexHingeAtom_three, starDot_pair, starDot_pair]
  simp only [map_one, omegaRoot_conj_eq, omegaRoot_sq_conj]
  linear_combination (omegaRoot ^ 3 + omegaRoot + 1 : ℂ) * hcube + hpair

/-! ### The six pair excess determinants -/

/-- `det (S_{a,b} - 1) = (u_a - 1)(u_b - 1) - overlap`, and every squared length
here is `2`, so the determinant is `1 - overlap`. -/
theorem complexHingeGapDet_of_overlap {first second : Fin 4} {overlapValue : ℂ} {value : ℝ}
    (hoverlap : (star (complexHingeAtom first) ⬝ᵥ complexHingeAtom second)
        * (star (complexHingeAtom second) ⬝ᵥ complexHingeAtom first) = overlapValue)
    (hvalue : ((value : ℝ) : ℂ) = 1 - overlapValue) :
    (complexAtom (complexHingeAtom first) + complexAtom (complexHingeAtom second) - 1).det
      = ((value : ℝ) : ℂ) := by
  rw [det_pair_excess, complexHingeNorm, complexHingeNorm, hoverlap, hvalue]
  ring

theorem complexHingeOv_one_zero :
    (star (complexHingeAtom 1) ⬝ᵥ complexHingeAtom 0)
      * (star (complexHingeAtom 0) ⬝ᵥ complexHingeAtom 1) = 36 / 25 := by
  rw [mul_comm]; exact complexHingeOv_zero_one

theorem complexHingeOv_two_zero :
    (star (complexHingeAtom 2) ⬝ᵥ complexHingeAtom 0)
      * (star (complexHingeAtom 0) ⬝ᵥ complexHingeAtom 2) = 7 / 5 := by
  rw [mul_comm]; exact complexHingeOv_zero_two

theorem complexHingeOv_three_zero :
    (star (complexHingeAtom 3) ⬝ᵥ complexHingeAtom 0)
      * (star (complexHingeAtom 0) ⬝ᵥ complexHingeAtom 3) = 7 / 5 := by
  rw [mul_comm]; exact complexHingeOv_zero_three

theorem complexHingeOv_two_one :
    (star (complexHingeAtom 2) ⬝ᵥ complexHingeAtom 1)
      * (star (complexHingeAtom 1) ⬝ᵥ complexHingeAtom 2) = 7 / 5 := by
  rw [mul_comm]; exact complexHingeOv_one_two

theorem complexHingeOv_three_one :
    (star (complexHingeAtom 3) ⬝ᵥ complexHingeAtom 1)
      * (star (complexHingeAtom 1) ⬝ᵥ complexHingeAtom 3) = 7 / 5 := by
  rw [mul_comm]; exact complexHingeOv_one_three

theorem complexHingeOv_three_two :
    (star (complexHingeAtom 3) ⬝ᵥ complexHingeAtom 2)
      * (star (complexHingeAtom 2) ⬝ᵥ complexHingeAtom 3) = 1 := by
  rw [mul_comm]; exact complexHingeOv_two_three

/-- **No pair dominates strictly.**  Every one of the six pair excess determinants
is at most zero, and a positive definite matrix has a positive determinant. -/
theorem complexHingeNoStrictPair (first second : Fin 4) (hne : first ≠ second) :
    ¬ (complexAtom (complexHingeAtom first) + complexAtom (complexHingeAtom second)
        - 1).PosDef := by
  fin_cases first <;> fin_cases second
  · exact absurd rfl hne
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := -11 / 25) ?_ (by norm_num)
    rw [show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl,
      show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_zero_one
      (by push_cast; ring)
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := -2 / 5) ?_ (by norm_num)
    rw [show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl,
      show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_zero_two
      (by push_cast; ring)
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := -2 / 5) ?_ (by norm_num)
    rw [show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl,
      show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_zero_three
      (by push_cast; ring)
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := -11 / 25) ?_ (by norm_num)
    rw [show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl,
      show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_one_zero
      (by push_cast; ring)
  · exact absurd rfl hne
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := -2 / 5) ?_ (by norm_num)
    rw [show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl,
      show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_one_two
      (by push_cast; ring)
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := -2 / 5) ?_ (by norm_num)
    rw [show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl,
      show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_one_three
      (by push_cast; ring)
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := -2 / 5) ?_ (by norm_num)
    rw [show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl,
      show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_two_zero
      (by push_cast; ring)
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := -2 / 5) ?_ (by norm_num)
    rw [show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl,
      show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_two_one
      (by push_cast; ring)
  · exact absurd rfl hne
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := 0) ?_ (by norm_num)
    rw [show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl,
      show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_two_three
      (by push_cast; ring)
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := -2 / 5) ?_ (by norm_num)
    rw [show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl,
      show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_three_zero
      (by push_cast; ring)
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := -2 / 5) ?_ (by norm_num)
    rw [show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl,
      show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_three_one
      (by push_cast; ring)
  · refine not_posDef_of_det_eq_ofReal_nonpos (value := 0) ?_ (by norm_num)
    rw [show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl,
      show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl]
    exact complexHingeGapDet_of_overlap complexHingeOv_three_two
      (by push_cast; ring)
  · exact absurd rfl hne

/-- **No pair is parallel.**  A parallel pair saturates Cauchy-Schwarz at
`u_a u_b = 4`, and the largest overlap here is `36/25`. -/
theorem complexHingeOverlap_ne_four (first second : Fin 4) (hne : first ≠ second) :
    (star (complexHingeAtom first) ⬝ᵥ complexHingeAtom second)
      * (star (complexHingeAtom second) ⬝ᵥ complexHingeAtom first) ≠ 4 := by
  fin_cases first <;> fin_cases second
  · exact absurd rfl hne
  · rw [show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl,
      show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl,
      complexHingeOv_zero_one]
    norm_num
  · rw [show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl,
      show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl,
      complexHingeOv_zero_two]
    norm_num
  · rw [show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl,
      show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl,
      complexHingeOv_zero_three]
    norm_num
  · rw [show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl,
      show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl,
      complexHingeOv_one_zero]
    norm_num
  · exact absurd rfl hne
  · rw [show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl,
      show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl,
      complexHingeOv_one_two]
    norm_num
  · rw [show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl,
      show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl,
      complexHingeOv_one_three]
    norm_num
  · rw [show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl,
      show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl,
      complexHingeOv_two_zero]
    norm_num
  · rw [show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl,
      show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl,
      complexHingeOv_two_one]
    norm_num
  · exact absurd rfl hne
  · rw [show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl,
      show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl,
      complexHingeOv_two_three]
    norm_num
  · rw [show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl,
      show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl,
      complexHingeOv_three_zero]
    norm_num
  · rw [show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl,
      show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl,
      complexHingeOv_three_one]
    norm_num
  · rw [show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl,
      show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl,
      complexHingeOv_three_two]
    norm_num
  · exact absurd rfl hne

/-! ### The headline at `(4,2)` -/

/-- The pair `{2,3}` dominates: its gap is the rank-one atom of `(1,-1)`. -/
theorem complexHingeGap_two_three :
    complexAtom (complexHingeAtom 2) + complexAtom (complexHingeAtom 3) - 1
      = complexAtom ![1, -1] := by
  have hpair := omegaRoot_pair
  rw [complexAtom_hinge_two, complexAtom_hinge_three]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [complexAtom, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.of_apply,
      Matrix.empty_val', Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, map_one,
      map_neg] <;>
    norm_num <;>
    linear_combination hpair

theorem complexHingeDominates_two_three : ComplexDominates complexHingeDesign {2, 3} := by
  show ((∑ atomLabel ∈ ({2, 3} : Finset (Fin 4)),
    complexAtom (complexHingeAtom atomLabel)) - 1).PosSemidef
  rw [Finset.sum_pair (by decide : (2 : Fin 4) ≠ 3), complexHingeGap_two_three]
  exact complexAtom_posSemidef _

/-- **The `(4,2)` design is an exact tie.** -/
theorem complexHingeDesign_isTie : ComplexIsTie complexHingeDesign := by
  refine ⟨⟨{2, 3}, by decide, complexHingeDominates_two_three⟩, ?_⟩
  intro selected hcard
  obtain ⟨firstLabel, secondLabel, hne, rfl⟩ := Finset.card_eq_two.mp hcard
  show ¬ ((∑ atomLabel ∈ ({firstLabel, secondLabel} : Finset (Fin 4)),
    complexAtom (complexHingeAtom atomLabel)) - 1).PosDef
  rw [Finset.sum_pair hne]
  exact complexHingeNoStrictPair firstLabel secondLabel hne

/-- **The `(4,2)` design has no parallel pair.** -/
theorem not_complexHingeDesign_hasParallelPair :
    ¬ ComplexHasParallelPair complexHingeDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
  have hsaturate := overlap_eq_of_parallel
    (leftVec := complexHingeAtom keptLabel) (rightVec := complexHingeAtom dropLabel) hparallel
  rw [complexHingeNorm, complexHingeNorm] at hsaturate
  exact complexHingeOverlap_ne_four keptLabel dropLabel hne (by rw [hsaturate]; norm_num)

/-- **THE COMPLEX HINGE IS FALSE AT RANK TWO.**  Over `ℝ` the same sentence is the
theorem `Gtz.hingeHoldsAtSize_rank_two`; the four Bloch directions of
`Gtz.complexHingeAtom` are distinct and off one great circle, which no real
rank-two tie permits. -/
theorem not_complexHingeHoldsAtSize_four_two : ¬ ComplexHingeHoldsAtSize 4 2 :=
  fun hhinge => not_complexHingeDesign_hasParallelPair
    (hhinge complexHingeDesign complexHingeDesign_isTie)

end Gtz
