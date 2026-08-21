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

/-! ## 6. The `(6,3)` witness

Five atoms in the plane `ℂ² × {0}` and one spike on the third axis.  A triple that
misses the spike has a zero third coordinate, so its gap carries `-1` on the
diagonal; a triple `{a, b, spike}` has a block-diagonal gap whose determinant is
`24` times the pair excess of `{a,b}`. -/

/-- The fifth planar atom, of squared length `5/2`. -/
noncomputable def spreadAtom : Fin 2 → ℂ := ![rootTwoAmp, rootTwoAmp / 2]

/-- The spike, of squared length `25`. -/
noncomputable def spikeAtom : Fin 3 → ℂ := ![0, 0, 5]

/-- A planar vector, read in `ℂ³`. -/
noncomputable def liftPlane (planeVec : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![planeVec 0, planeVec 1, 0]

@[simp] theorem liftPlane_apply_two (planeVec : Fin 2 → ℂ) : liftPlane planeVec 2 = 0 := rfl

/-- **Lifting preserves every Gram entry.**  So the whole `(6,3)` Gram is the
rank-two Gram already computed, plus one orthogonal spike. -/
theorem starDot_liftPlane (leftVec rightVec : Fin 2 → ℂ) :
    star (liftPlane leftVec) ⬝ᵥ liftPlane rightVec = star leftVec ⬝ᵥ rightVec := by
  simp [liftPlane, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three]

theorem starDot_liftPlane_spike (planeVec : Fin 2 → ℂ) :
    star (liftPlane planeVec) ⬝ᵥ spikeAtom = 0 := by
  simp [liftPlane, spikeAtom, dotProduct, Fin.sum_univ_three]

theorem starDot_spike_liftPlane (planeVec : Fin 2 → ℂ) :
    star spikeAtom ⬝ᵥ liftPlane planeVec = 0 := by
  simp [liftPlane, spikeAtom, dotProduct, Fin.sum_univ_three]

theorem starDot_spike : star spikeAtom ⬝ᵥ spikeAtom = 25 := by
  simp [spikeAtom, dotProduct, Fin.sum_univ_three, Complex.conj_ofNat]
  norm_num

/-- The lifted rank-one atom, entry by entry. -/
theorem complexAtom_liftPlane (planeVec : Fin 2 → ℂ) :
    complexAtom (liftPlane planeVec)
      = !![planeVec 0 * (starRingEnd ℂ) (planeVec 0),
             planeVec 0 * (starRingEnd ℂ) (planeVec 1), 0;
           planeVec 1 * (starRingEnd ℂ) (planeVec 0),
             planeVec 1 * (starRingEnd ℂ) (planeVec 1), 0;
           0, 0, 0] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [complexAtom, liftPlane, Matrix.vecMulVec_apply]

theorem complexAtom_spike : complexAtom spikeAtom = !![0, 0, 0; 0, 0, 0; 0, 0, 25] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [complexAtom, spikeAtom, Matrix.vecMulVec_apply] <;> norm_num

/-- The squared length of the fifth planar atom. -/
theorem spreadAtom_norm : star spreadAtom ⬝ᵥ spreadAtom = 5 / 2 := by
  have hTwo := rootTwoAmp_sq
  rw [spreadAtom, starDot_pair]
  simp only [map_div₀, Complex.conj_ofNat, rootTwoAmp_conj]
  linear_combination (5 / 4 : ℂ) * hTwo

/-- The six atoms of the `(6,3)` witness. -/
noncomputable def complexHingeSixAtom : Fin 6 → Fin 3 → ℂ :=
  ![liftPlane (complexHingeAtom 0), liftPlane (complexHingeAtom 1),
    liftPlane (complexHingeAtom 2), liftPlane (complexHingeAtom 3),
    liftPlane spreadAtom, spikeAtom]

/-- The planar shadow of an atom.  The sixth entry is a placeholder never read. -/
noncomputable def complexHingePlaneAtom : Fin 6 → (Fin 2 → ℂ) :=
  ![complexHingeAtom 0, complexHingeAtom 1, complexHingeAtom 2, complexHingeAtom 3,
    spreadAtom, ![0, 0]]

theorem complexHingeSixAtom_zero : complexHingeSixAtom 0 = liftPlane (complexHingeAtom 0) := rfl
theorem complexHingeSixAtom_one : complexHingeSixAtom 1 = liftPlane (complexHingeAtom 1) := rfl
theorem complexHingeSixAtom_two : complexHingeSixAtom 2 = liftPlane (complexHingeAtom 2) := rfl
theorem complexHingeSixAtom_three : complexHingeSixAtom 3 = liftPlane (complexHingeAtom 3) := rfl
theorem complexHingeSixAtom_four : complexHingeSixAtom 4 = liftPlane spreadAtom := rfl
theorem complexHingeSixAtom_five : complexHingeSixAtom 5 = spikeAtom := rfl

/-- Away from the spike every atom is a lift. -/
theorem complexHingeSixAtom_eq_liftPlane (atomLabel : Fin 6) (hlabel : atomLabel ≠ 5) :
    complexHingeSixAtom atomLabel = liftPlane (complexHingePlaneAtom atomLabel) := by
  fin_cases atomLabel
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd rfl hlabel

/-- The six weights.  All rational: the design is the `(4,2)` witness reweighted,
plus a fifth planar atom and the spike. -/
noncomputable def complexHingeSixWeight : Fin 6 → ℝ :=
  ![3 / 88, 81 / 440, 16 / 55, 16 / 55, 4 / 25, 1 / 25]

theorem complexHingeSixWeight_pos : ∀ atomLabel, 0 < complexHingeSixWeight atomLabel := by
  intro atomLabel
  fin_cases atomLabel <;> norm_num [complexHingeSixWeight]

theorem complexHingeSixWeight_sum_one : ∑ atomLabel, complexHingeSixWeight atomLabel = 1 := by
  simp [complexHingeSixWeight, Fin.sum_univ_six]
  norm_num

/-- **Parseval at `(6,3)`.**  The third row and column see only the spike, whose
share is `(1/25)·25 = 1`; the `2×2` block is the reweighted rank-two Parseval. -/
theorem complexHingeSixParseval :
    ∑ atomLabel, ((complexHingeSixWeight atomLabel : ℝ) : ℂ)
      • complexAtom (complexHingeSixAtom atomLabel) = 1 := by
  rw [Fin.sum_univ_six, complexHingeSixAtom_zero, complexHingeSixAtom_one,
    complexHingeSixAtom_two, complexHingeSixAtom_three, complexHingeSixAtom_four,
    complexHingeSixAtom_five, complexAtom_liftPlane, complexAtom_liftPlane,
    complexAtom_liftPlane, complexAtom_liftPlane, complexAtom_liftPlane, complexAtom_spike]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [complexHingeAtom_zero, complexHingeAtom_one, complexHingeAtom_two,
      complexHingeAtom_three, spreadAtom, complexHingeSixWeight, Complex.conj_ofNat,
      fifthAmp_conj, rootTwoAmp_conj, omegaRoot_conj_eq, omegaRoot_sq_conj]
  · linear_combination (27 / 55 : ℂ) * fifthAmp_sq + (4 / 25 : ℂ) * rootTwoAmp_sq
  · linear_combination (36 / 55 : ℂ) * fifthAmp_sq + (2 / 25 : ℂ) * rootTwoAmp_sq
      + (16 / 55 : ℂ) * omegaRoot_pair
  · linear_combination (36 / 55 : ℂ) * fifthAmp_sq + (2 / 25 : ℂ) * rootTwoAmp_sq
      + (16 / 55 : ℂ) * omegaRoot_pair
  · linear_combination (93 / 55 : ℂ) * fifthAmp_sq + (1 / 25 : ℂ) * rootTwoAmp_sq
      + (32 / 55 : ℂ) * omegaRoot_cube

/-- **The `(6,3)` complex design.** -/
noncomputable def complexHingeSixDesign : ComplexWeightedDesign 6 3 where
  atom := complexHingeSixAtom
  weight := complexHingeSixWeight
  weight_pos := complexHingeSixWeight_pos
  weight_sum_one := complexHingeSixWeight_sum_one
  isParseval := complexHingeSixParseval

/-! ### The four overlaps against the fifth planar atom -/

theorem complexHingeOv_zero_four :
    (star (complexHingeAtom 0) ⬝ᵥ spreadAtom) * (star spreadAtom ⬝ᵥ complexHingeAtom 0)
      = 49 / 10 := by
  have hfifth := fifthAmp_sq
  have hTwo := rootTwoAmp_sq
  rw [complexHingeAtom_zero, spreadAtom, starDot_pair, starDot_pair]
  simp only [map_mul, map_div₀, Complex.conj_ofNat, fifthAmp_conj, rootTwoAmp_conj]
  linear_combination (49 / 4 * rootTwoAmp * rootTwoAmp : ℂ) * hfifth
    + (49 / 20 : ℂ) * hTwo

theorem complexHingeOv_one_four :
    (star (complexHingeAtom 1) ⬝ᵥ spreadAtom) * (star spreadAtom ⬝ᵥ complexHingeAtom 1)
      = 5 / 2 := by
  have hfifth := fifthAmp_sq
  have hTwo := rootTwoAmp_sq
  rw [complexHingeAtom_one, spreadAtom, starDot_pair, starDot_pair]
  simp only [map_mul, map_div₀, Complex.conj_ofNat, fifthAmp_conj, rootTwoAmp_conj]
  linear_combination (25 / 4 * rootTwoAmp * rootTwoAmp : ℂ) * hfifth + (5 / 4 : ℂ) * hTwo

theorem complexHingeOv_two_four :
    (star (complexHingeAtom 2) ⬝ᵥ spreadAtom) * (star spreadAtom ⬝ᵥ complexHingeAtom 2)
      = 3 / 2 := by
  have hTwo := rootTwoAmp_sq
  have hpair := omegaRoot_pair
  have hcube := omegaRoot_cube
  rw [complexHingeAtom_two, spreadAtom, starDot_pair, starDot_pair]
  simp only [map_mul, map_div₀, map_one, Complex.conj_ofNat, rootTwoAmp_conj,
    omegaRoot_conj_eq]
  linear_combination (1 / 2 * rootTwoAmp * rootTwoAmp : ℂ) * hpair
    + (1 / 4 * rootTwoAmp * rootTwoAmp : ℂ) * hcube + (3 / 4 : ℂ) * hTwo

theorem complexHingeOv_three_four :
    (star (complexHingeAtom 3) ⬝ᵥ spreadAtom) * (star spreadAtom ⬝ᵥ complexHingeAtom 3)
      = 3 / 2 := by
  have hTwo := rootTwoAmp_sq
  have hpair := omegaRoot_pair
  have hcube := omegaRoot_cube
  rw [complexHingeAtom_three, spreadAtom, starDot_pair, starDot_pair]
  simp only [map_mul, map_div₀, map_one, Complex.conj_ofNat, rootTwoAmp_conj,
    omegaRoot_sq_conj]
  linear_combination (1 / 2 * rootTwoAmp * rootTwoAmp : ℂ) * hpair
    + (1 / 4 * rootTwoAmp * rootTwoAmp : ℂ) * hcube + (3 / 4 : ℂ) * hTwo

/-! ### The planar shadows and their fifteen pair excesses -/

theorem complexHingePlaneAtom_zero : complexHingePlaneAtom 0 = complexHingeAtom 0 := rfl
theorem complexHingePlaneAtom_one : complexHingePlaneAtom 1 = complexHingeAtom 1 := rfl
theorem complexHingePlaneAtom_two : complexHingePlaneAtom 2 = complexHingeAtom 2 := rfl
theorem complexHingePlaneAtom_three : complexHingePlaneAtom 3 = complexHingeAtom 3 := rfl
theorem complexHingePlaneAtom_four : complexHingePlaneAtom 4 = spreadAtom := rfl

theorem complexHingeOv_four_zero :
    (star spreadAtom ⬝ᵥ complexHingeAtom 0) * (star (complexHingeAtom 0) ⬝ᵥ spreadAtom)
      = 49 / 10 := by
  rw [mul_comm]; exact complexHingeOv_zero_four

theorem complexHingeOv_four_one :
    (star spreadAtom ⬝ᵥ complexHingeAtom 1) * (star (complexHingeAtom 1) ⬝ᵥ spreadAtom)
      = 5 / 2 := by
  rw [mul_comm]; exact complexHingeOv_one_four

theorem complexHingeOv_four_two :
    (star spreadAtom ⬝ᵥ complexHingeAtom 2) * (star (complexHingeAtom 2) ⬝ᵥ spreadAtom)
      = 3 / 2 := by
  rw [mul_comm]; exact complexHingeOv_two_four

theorem complexHingeOv_four_three :
    (star spreadAtom ⬝ᵥ complexHingeAtom 3) * (star (complexHingeAtom 3) ⬝ᵥ spreadAtom)
      = 3 / 2 := by
  rw [mul_comm]; exact complexHingeOv_three_four

/-- **Every planar pair excess is at most zero.**  The five squared lengths are
`2, 2, 2, 2, 5/2`, and the fifteen overlap products give the excesses `-3` four
times and `-4` once on the diagonal, then `-11/25`, `-2/5` four times, `-17/5`,
`-1`, and `0` three times. -/
theorem complexHingePlaneExcess_nonpos (first second : Fin 6) (hfirst : first ≠ 5)
    (hsecond : second ≠ 5) :
    ∃ value : ℝ, value ≤ 0 ∧
      (star (complexHingePlaneAtom first) ⬝ᵥ complexHingePlaneAtom first - 1)
          * (star (complexHingePlaneAtom second) ⬝ᵥ complexHingePlaneAtom second - 1)
        - (star (complexHingePlaneAtom first) ⬝ᵥ complexHingePlaneAtom second)
          * (star (complexHingePlaneAtom second) ⬝ᵥ complexHingePlaneAtom first)
        = ((value : ℝ) : ℂ) := by
  fin_cases first <;> fin_cases second
  · refine ⟨-3, by norm_num, ?_⟩
    rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      complexHingePlaneAtom_zero, complexHingeNorm 0]
    push_cast
    norm_num
  · refine ⟨-11 / 25, by norm_num, ?_⟩
    rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      complexHingePlaneAtom_zero, complexHingePlaneAtom_one,
      complexHingeNorm 0, complexHingeNorm 1, complexHingeOv_zero_one]
    push_cast
    norm_num
  · refine ⟨-2 / 5, by norm_num, ?_⟩
    rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      complexHingePlaneAtom_zero, complexHingePlaneAtom_two,
      complexHingeNorm 0, complexHingeNorm 2, complexHingeOv_zero_two]
    push_cast
    norm_num
  · refine ⟨-2 / 5, by norm_num, ?_⟩
    rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      complexHingePlaneAtom_zero, complexHingePlaneAtom_three,
      complexHingeNorm 0, complexHingeNorm 3, complexHingeOv_zero_three]
    push_cast
    norm_num
  · refine ⟨-17 / 5, by norm_num, ?_⟩
    rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      complexHingePlaneAtom_zero, complexHingePlaneAtom_four,
      complexHingeNorm 0, spreadAtom_norm, complexHingeOv_zero_four]
    push_cast
    norm_num
  · exact absurd rfl hsecond
  · refine ⟨-11 / 25, by norm_num, ?_⟩
    rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      complexHingePlaneAtom_one, complexHingePlaneAtom_zero,
      complexHingeNorm 1, complexHingeNorm 0, complexHingeOv_one_zero]
    push_cast
    norm_num
  · refine ⟨-3, by norm_num, ?_⟩
    rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      complexHingePlaneAtom_one, complexHingeNorm 1]
    push_cast
    norm_num
  · refine ⟨-2 / 5, by norm_num, ?_⟩
    rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      complexHingePlaneAtom_one, complexHingePlaneAtom_two,
      complexHingeNorm 1, complexHingeNorm 2, complexHingeOv_one_two]
    push_cast
    norm_num
  · refine ⟨-2 / 5, by norm_num, ?_⟩
    rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      complexHingePlaneAtom_one, complexHingePlaneAtom_three,
      complexHingeNorm 1, complexHingeNorm 3, complexHingeOv_one_three]
    push_cast
    norm_num
  · refine ⟨-1, by norm_num, ?_⟩
    rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      complexHingePlaneAtom_one, complexHingePlaneAtom_four,
      complexHingeNorm 1, spreadAtom_norm, complexHingeOv_one_four]
    push_cast
    norm_num
  · exact absurd rfl hsecond
  · refine ⟨-2 / 5, by norm_num, ?_⟩
    rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      complexHingePlaneAtom_two, complexHingePlaneAtom_zero,
      complexHingeNorm 2, complexHingeNorm 0, complexHingeOv_two_zero]
    push_cast
    norm_num
  · refine ⟨-2 / 5, by norm_num, ?_⟩
    rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      complexHingePlaneAtom_two, complexHingePlaneAtom_one,
      complexHingeNorm 2, complexHingeNorm 1, complexHingeOv_two_one]
    push_cast
    norm_num
  · refine ⟨-3, by norm_num, ?_⟩
    rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      complexHingePlaneAtom_two, complexHingeNorm 2]
    push_cast
    norm_num
  · refine ⟨0, by norm_num, ?_⟩
    rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      complexHingePlaneAtom_two, complexHingePlaneAtom_three,
      complexHingeNorm 2, complexHingeNorm 3, complexHingeOv_two_three]
    push_cast
    norm_num
  · refine ⟨0, by norm_num, ?_⟩
    rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      complexHingePlaneAtom_two, complexHingePlaneAtom_four,
      complexHingeNorm 2, spreadAtom_norm, complexHingeOv_two_four]
    push_cast
    norm_num
  · exact absurd rfl hsecond
  · refine ⟨-2 / 5, by norm_num, ?_⟩
    rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      complexHingePlaneAtom_three, complexHingePlaneAtom_zero,
      complexHingeNorm 3, complexHingeNorm 0, complexHingeOv_three_zero]
    push_cast
    norm_num
  · refine ⟨-2 / 5, by norm_num, ?_⟩
    rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      complexHingePlaneAtom_three, complexHingePlaneAtom_one,
      complexHingeNorm 3, complexHingeNorm 1, complexHingeOv_three_one]
    push_cast
    norm_num
  · refine ⟨0, by norm_num, ?_⟩
    rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      complexHingePlaneAtom_three, complexHingePlaneAtom_two,
      complexHingeNorm 3, complexHingeNorm 2, complexHingeOv_three_two]
    push_cast
    norm_num
  · refine ⟨-3, by norm_num, ?_⟩
    rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      complexHingePlaneAtom_three, complexHingeNorm 3]
    push_cast
    norm_num
  · refine ⟨0, by norm_num, ?_⟩
    rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      complexHingePlaneAtom_three, complexHingePlaneAtom_four,
      complexHingeNorm 3, spreadAtom_norm, complexHingeOv_three_four]
    push_cast
    norm_num
  · exact absurd rfl hsecond
  · refine ⟨-17 / 5, by norm_num, ?_⟩
    rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      complexHingePlaneAtom_four, complexHingePlaneAtom_zero,
      spreadAtom_norm, complexHingeNorm 0, complexHingeOv_four_zero]
    push_cast
    norm_num
  · refine ⟨-1, by norm_num, ?_⟩
    rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      complexHingePlaneAtom_four, complexHingePlaneAtom_one,
      spreadAtom_norm, complexHingeNorm 1, complexHingeOv_four_one]
    push_cast
    norm_num
  · refine ⟨0, by norm_num, ?_⟩
    rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      complexHingePlaneAtom_four, complexHingePlaneAtom_two,
      spreadAtom_norm, complexHingeNorm 2, complexHingeOv_four_two]
    push_cast
    norm_num
  · refine ⟨0, by norm_num, ?_⟩
    rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      complexHingePlaneAtom_four, complexHingePlaneAtom_three,
      spreadAtom_norm, complexHingeNorm 3, complexHingeOv_four_three]
    push_cast
    norm_num
  · refine ⟨-4, by norm_num, ?_⟩
    rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      complexHingePlaneAtom_four, spreadAtom_norm]
    push_cast
    norm_num
  · exact absurd rfl hsecond
  · exact absurd rfl hfirst
  · exact absurd rfl hfirst
  · exact absurd rfl hfirst
  · exact absurd rfl hfirst
  · exact absurd rfl hfirst
  · exact absurd rfl hfirst

/-! ### The determinant of a triple that contains the spike -/

/-- **The block determinant.**  A triple `{a, b, spike}` has a block-diagonal gap:
the `2×2` planar block and the scalar `25 - 1 = 24`.  So its determinant is `24`
times the planar pair excess. -/
theorem det_spikeTriple (leftVec rightVec : Fin 2 → ℂ) :
    (complexAtom (liftPlane leftVec)
        + (complexAtom (liftPlane rightVec) + complexAtom spikeAtom) - 1).det
      = 24 * ((star leftVec ⬝ᵥ leftVec - 1) * (star rightVec ⬝ᵥ rightVec - 1)
          - (star leftVec ⬝ᵥ rightVec) * (star rightVec ⬝ᵥ leftVec)) := by
  rw [complexAtom_spike, complexAtom_liftPlane, complexAtom_liftPlane, Matrix.det_fin_three]
  simp [dotProduct, Fin.sum_univ_two, Matrix.one_apply]
  ring

/-- Away from the spike an atom has a vanishing third coordinate, so its rank-one
matrix has a zero third diagonal entry. -/
theorem complexAtomSix_diag_two (atomLabel : Fin 6) (hlabel : atomLabel ≠ 5) :
    complexAtom (complexHingeSixAtom atomLabel) 2 2 = 0 := by
  rw [complexHingeSixAtom_eq_liftPlane atomLabel hlabel]
  simp [complexAtom, Matrix.vecMulVec_apply]

/-- **No triple dominates strictly.**  A triple that misses the spike carries `-1`
on the third diagonal entry; a triple that contains it has determinant `24` times
a nonpositive planar excess. -/
theorem complexHingeSixNoStrict (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    ¬ ((∑ atomLabel ∈ selected, complexAtom (complexHingeSixAtom atomLabel)) - 1).PosDef := by
  classical
  by_cases hspike : (5 : Fin 6) ∈ selected
  · have hcardTwo : (selected.erase 5).card = 2 := by
      rw [Finset.card_erase_of_mem hspike, hcard]
    obtain ⟨firstLabel, secondLabel, hne, herase⟩ := Finset.card_eq_two.mp hcardTwo
    have hfirstMem : firstLabel ∈ selected.erase 5 := by rw [herase]; simp
    have hsecondMem : secondLabel ∈ selected.erase 5 := by rw [herase]; simp
    have hfirst : firstLabel ≠ 5 := (Finset.mem_erase.mp hfirstMem).1
    have hsecond : secondLabel ≠ 5 := (Finset.mem_erase.mp hsecondMem).1
    have hsel : selected = insert firstLabel (insert secondLabel {(5 : Fin 6)}) := by
      have hpair : selected.erase 5 = {firstLabel, secondLabel} := herase
      rw [← Finset.insert_erase hspike, hpair]
      ext probe
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    obtain ⟨value, hle, hexcess⟩ :=
      complexHingePlaneExcess_nonpos firstLabel secondLabel hfirst hsecond
    rw [hsel, Finset.sum_insert (by simp [hne, hfirst]),
      Finset.sum_insert (by simp [hsecond]), Finset.sum_singleton]
    refine not_posDef_of_det_eq_ofReal_nonpos (value := 24 * value) ?_ (by nlinarith)
    rw [complexHingeSixAtom_five, complexHingeSixAtom_eq_liftPlane firstLabel hfirst,
      complexHingeSixAtom_eq_liftPlane secondLabel hsecond, det_spikeTriple, hexcess]
    push_cast
    ring
  · refine not_posDef_of_diag_eq_neg_one (index := 2) ?_
    rw [Matrix.sub_apply, Matrix.sum_apply, Matrix.one_apply_eq,
      Finset.sum_eq_zero fun probe hprobe =>
        complexAtomSix_diag_two probe (by rintro rfl; exact hspike hprobe)]
    ring

/-! ### The dominating triple -/

/-- `√24`, the length of the spike part of the dominating gap. -/
noncomputable def rootTwentyFourAmp : ℂ := ((Real.sqrt 24 : ℝ) : ℂ)

theorem rootTwentyFourAmp_conj : (starRingEnd ℂ) rootTwentyFourAmp = rootTwentyFourAmp :=
  Complex.conj_ofReal _

theorem rootTwentyFourAmp_sq : rootTwentyFourAmp * rootTwentyFourAmp = 24 := by
  rw [rootTwentyFourAmp, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 24)]
  norm_num

/-- The gap of `{2, 3, 5}` is a sum of two rank-one atoms:
`[[1,-1,0],[-1,1,0],[0,0,24]]`. -/
theorem complexHingeSixGap_dominating :
    complexAtom (complexHingeSixAtom 2)
        + (complexAtom (complexHingeSixAtom 3) + complexAtom (complexHingeSixAtom 5)) - 1
      = complexAtom (liftPlane ![1, -1]) + complexAtom ![0, 0, rootTwentyFourAmp] := by
  rw [complexHingeSixAtom_two, complexHingeSixAtom_three, complexHingeSixAtom_five,
    complexAtom_liftPlane, complexAtom_liftPlane, complexAtom_liftPlane, complexAtom_spike]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [complexAtom, complexHingeAtom_two, complexHingeAtom_three, Matrix.vecMulVec_apply,
      omegaRoot_conj_eq, omegaRoot_sq_conj, rootTwentyFourAmp_conj]
  · linear_combination omegaRoot_pair
  · linear_combination omegaRoot_pair
  · linear_combination (2 : ℂ) * omegaRoot_cube
  · linear_combination -rootTwentyFourAmp_sq

theorem complexHingeSixDominates : ComplexDominates complexHingeSixDesign {2, 3, 5} := by
  show ((∑ atomLabel ∈ ({2, 3, 5} : Finset (Fin 6)),
    complexAtom (complexHingeSixAtom atomLabel)) - 1).PosSemidef
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    complexHingeSixGap_dominating]
  exact (complexAtom_posSemidef _).add (complexAtom_posSemidef _)

/-- **The `(6,3)` design is an exact tie.** -/
theorem complexHingeSixDesign_isTie : ComplexIsTie complexHingeSixDesign := by
  refine ⟨⟨{2, 3, 5}, by decide, complexHingeSixDominates⟩, ?_⟩
  intro selected hcard
  exact complexHingeSixNoStrict selected hcard

/-! ### No parallel pair -/

theorem complexHingeSixOrth (atomLabel : Fin 6) (hlabel : atomLabel ≠ 5) :
    star (complexHingeSixAtom atomLabel) ⬝ᵥ complexHingeSixAtom 5 = 0 := by
  rw [complexHingeSixAtom_eq_liftPlane atomLabel hlabel, complexHingeSixAtom_five]
  exact starDot_liftPlane_spike _

theorem complexHingeSixOrth' (atomLabel : Fin 6) (hlabel : atomLabel ≠ 5) :
    star (complexHingeSixAtom 5) ⬝ᵥ complexHingeSixAtom atomLabel = 0 := by
  rw [complexHingeSixAtom_eq_liftPlane atomLabel hlabel, complexHingeSixAtom_five]
  exact starDot_spike_liftPlane _

/-- **No two atoms saturate Cauchy-Schwarz.**  The largest overlap ratio is
`49/50`, at the pair `{0,4}`; the spike is orthogonal to everything. -/
theorem complexHingeSixOverlap_ne (first second : Fin 6) (hne : first ≠ second) :
    (star (complexHingeSixAtom first) ⬝ᵥ complexHingeSixAtom second)
        * (star (complexHingeSixAtom second) ⬝ᵥ complexHingeSixAtom first)
      ≠ (star (complexHingeSixAtom first) ⬝ᵥ complexHingeSixAtom first)
        * (star (complexHingeSixAtom second) ⬝ᵥ complexHingeSixAtom second) := by
  fin_cases first <;> fin_cases second
  · exact absurd rfl hne
  · rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      complexHingeSixAtom_zero, complexHingeSixAtom_one,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 0, complexHingeNorm 1, complexHingeOv_zero_one]
    norm_num
  · rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      complexHingeSixAtom_zero, complexHingeSixAtom_two,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 0, complexHingeNorm 2, complexHingeOv_zero_two]
    norm_num
  · rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      complexHingeSixAtom_zero, complexHingeSixAtom_three,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 0, complexHingeNorm 3, complexHingeOv_zero_three]
    norm_num
  · rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      complexHingeSixAtom_zero, complexHingeSixAtom_four,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 0, spreadAtom_norm, complexHingeOv_zero_four]
    norm_num
  · rw [show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl]
    rw [complexHingeSixOrth 0 (by decide), complexHingeSixOrth' 0 (by decide),
      complexHingeSixAtom_zero, starDot_liftPlane, complexHingeNorm 0,
      complexHingeSixAtom_five, starDot_spike]
    norm_num
  · rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      complexHingeSixAtom_one, complexHingeSixAtom_zero,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 1, complexHingeNorm 0, complexHingeOv_one_zero]
    norm_num
  · exact absurd rfl hne
  · rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      complexHingeSixAtom_one, complexHingeSixAtom_two,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 1, complexHingeNorm 2, complexHingeOv_one_two]
    norm_num
  · rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      complexHingeSixAtom_one, complexHingeSixAtom_three,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 1, complexHingeNorm 3, complexHingeOv_one_three]
    norm_num
  · rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      complexHingeSixAtom_one, complexHingeSixAtom_four,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 1, spreadAtom_norm, complexHingeOv_one_four]
    norm_num
  · rw [show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl]
    rw [complexHingeSixOrth 1 (by decide), complexHingeSixOrth' 1 (by decide),
      complexHingeSixAtom_one, starDot_liftPlane, complexHingeNorm 1,
      complexHingeSixAtom_five, starDot_spike]
    norm_num
  · rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      complexHingeSixAtom_two, complexHingeSixAtom_zero,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 2, complexHingeNorm 0, complexHingeOv_two_zero]
    norm_num
  · rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      complexHingeSixAtom_two, complexHingeSixAtom_one,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 2, complexHingeNorm 1, complexHingeOv_two_one]
    norm_num
  · exact absurd rfl hne
  · rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      complexHingeSixAtom_two, complexHingeSixAtom_three,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 2, complexHingeNorm 3, complexHingeOv_two_three]
    norm_num
  · rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      complexHingeSixAtom_two, complexHingeSixAtom_four,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 2, spreadAtom_norm, complexHingeOv_two_four]
    norm_num
  · rw [show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl]
    rw [complexHingeSixOrth 2 (by decide), complexHingeSixOrth' 2 (by decide),
      complexHingeSixAtom_two, starDot_liftPlane, complexHingeNorm 2,
      complexHingeSixAtom_five, starDot_spike]
    norm_num
  · rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      complexHingeSixAtom_three, complexHingeSixAtom_zero,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 3, complexHingeNorm 0, complexHingeOv_three_zero]
    norm_num
  · rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      complexHingeSixAtom_three, complexHingeSixAtom_one,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 3, complexHingeNorm 1, complexHingeOv_three_one]
    norm_num
  · rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      complexHingeSixAtom_three, complexHingeSixAtom_two,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 3, complexHingeNorm 2, complexHingeOv_three_two]
    norm_num
  · exact absurd rfl hne
  · rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      complexHingeSixAtom_three, complexHingeSixAtom_four,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      complexHingeNorm 3, spreadAtom_norm, complexHingeOv_three_four]
    norm_num
  · rw [show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl]
    rw [complexHingeSixOrth 3 (by decide), complexHingeSixOrth' 3 (by decide),
      complexHingeSixAtom_three, starDot_liftPlane, complexHingeNorm 3,
      complexHingeSixAtom_five, starDot_spike]
    norm_num
  · rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      complexHingeSixAtom_four, complexHingeSixAtom_zero,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      spreadAtom_norm, complexHingeNorm 0, complexHingeOv_four_zero]
    norm_num
  · rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      complexHingeSixAtom_four, complexHingeSixAtom_one,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      spreadAtom_norm, complexHingeNorm 1, complexHingeOv_four_one]
    norm_num
  · rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      complexHingeSixAtom_four, complexHingeSixAtom_two,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      spreadAtom_norm, complexHingeNorm 2, complexHingeOv_four_two]
    norm_num
  · rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      complexHingeSixAtom_four, complexHingeSixAtom_three,
      starDot_liftPlane, starDot_liftPlane, starDot_liftPlane, starDot_liftPlane,
      spreadAtom_norm, complexHingeNorm 3, complexHingeOv_four_three]
    norm_num
  · exact absurd rfl hne
  · rw [show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl]
    rw [complexHingeSixOrth 4 (by decide), complexHingeSixOrth' 4 (by decide),
      complexHingeSixAtom_four, starDot_liftPlane, spreadAtom_norm,
      complexHingeSixAtom_five, starDot_spike]
    norm_num
  · rw [show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl,
      show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl]
    rw [complexHingeSixOrth 0 (by decide), complexHingeSixOrth' 0 (by decide),
      complexHingeSixAtom_zero, starDot_liftPlane, complexHingeNorm 0,
      complexHingeSixAtom_five, starDot_spike]
    norm_num
  · rw [show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl,
      show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl]
    rw [complexHingeSixOrth 1 (by decide), complexHingeSixOrth' 1 (by decide),
      complexHingeSixAtom_one, starDot_liftPlane, complexHingeNorm 1,
      complexHingeSixAtom_five, starDot_spike]
    norm_num
  · rw [show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl,
      show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl]
    rw [complexHingeSixOrth 2 (by decide), complexHingeSixOrth' 2 (by decide),
      complexHingeSixAtom_two, starDot_liftPlane, complexHingeNorm 2,
      complexHingeSixAtom_five, starDot_spike]
    norm_num
  · rw [show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl,
      show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl]
    rw [complexHingeSixOrth 3 (by decide), complexHingeSixOrth' 3 (by decide),
      complexHingeSixAtom_three, starDot_liftPlane, complexHingeNorm 3,
      complexHingeSixAtom_five, starDot_spike]
    norm_num
  · rw [show ((⟨5, by omega⟩ : Fin 6)) = 5 from rfl,
      show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl]
    rw [complexHingeSixOrth 4 (by decide), complexHingeSixOrth' 4 (by decide),
      complexHingeSixAtom_four, starDot_liftPlane, spreadAtom_norm,
      complexHingeSixAtom_five, starDot_spike]
    norm_num
  · exact absurd rfl hne

theorem not_complexHingeSixDesign_hasParallelPair :
    ¬ ComplexHasParallelPair complexHingeSixDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
  exact complexHingeSixOverlap_ne keptLabel dropLabel hne
    (overlap_eq_of_parallel (leftVec := complexHingeSixAtom keptLabel)
      (rightVec := complexHingeSixAtom dropLabel) hparallel)

/-! ## 7. The headline at the target cell -/

/-- **THE COMPLEX HINGE IS FALSE AT `(6,3)`.**  `Gtz.complexHingeSixDesign` is an
exact complex tie with no parallel pair, at the cell that decides rank three over
`ℝ` (`Skeleton.closesThresholdCell_three_iff_sixThree`).  Every instrument whose
ingredients all survive the passage to `ℂ` admits it as a feasible point, so no
such instrument can prove `Gtz.HingeHoldsAtSize 6 3`. -/
theorem not_complexHingeHoldsAtSize_six_three : ¬ ComplexHingeHoldsAtSize 6 3 :=
  fun hhinge => not_complexHingeSixDesign_hasParallelPair
    (hhinge complexHingeSixDesign complexHingeSixDesign_isTie)

/-- **The two refutations together.**  The complex hinge fails at rank two and at
the target cell of rank three. -/
theorem not_complexHingeHoldsAtSize_four_two_and_six_three :
    ¬ ComplexHingeHoldsAtSize 4 2 ∧ ¬ ComplexHingeHoldsAtSize 6 3 :=
  ⟨not_complexHingeHoldsAtSize_four_two, not_complexHingeHoldsAtSize_six_three⟩

end Gtz
