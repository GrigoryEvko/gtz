/-
# The complex refutation: weighted (4,2) is FALSE over ℂ

The realness anchor of the entire campaign, in the kernel. The canonical list
reduces all of GTZ to finitely many weighted cases per rank, and the unique
rank-2 entry is weighted (4,2). Over the reals it is a theorem
(`gtz_rank_two`). Over the complex numbers it is FALSE, and the witness is the
SIC — four equiangular lines in ℂ²:

  `g₀ = (√2, 0)`,  `g_j = (√(2/3), √(4/3)·ω^{j−1})`,  `ω = e^{2πi/3}`,

uniform weights `1/4`. This is a genuine weighted design (the Parseval check
is the cube-root cancellation `1 + ω + ω² = 0`), every atom has squared length
`2`, and EVERY pair has overlap product `⟨g,h⟩⟨h,g⟩ = 4/3`. The 2×2 excess
determinant of every pair is therefore

  `det(S_C − I) = (2−1)(2−1) − 4/3 = −1/3 < 0`,

and a positive semidefinite matrix cannot have negative determinant — so no
pair dominates. Consequences: no field-blind argument can close weighted
(4,2), hence none can close the canonical list, hence every proof of GTZ must
consume realness somewhere. The campaign's field-discipline gate is this
theorem.
-/
import Mathlib

namespace Gtz

open Matrix Complex
open scoped ComplexOrder

/-! ### Complex designs -/

/-- The complex rank-one atom `g g*`. -/
def complexAtom {k : ℕ} (g : Fin k → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.vecMulVec g (star g)

/-- A weighted design over ℂ: the same axioms as the real `WeightedDesign`,
with Hermitian atoms resolving the identity. -/
structure ComplexWeightedDesign (m k : ℕ) where
  atom : Fin m → (Fin k → ℂ)
  weight : Fin m → ℝ
  weight_pos : ∀ c, 0 < weight c
  weight_sum_one : ∑ c, weight c = 1
  isParseval : ∑ c, ((weight c : ℂ)) • complexAtom (atom c) = 1

/-- Complex domination of a subset: the excess is positive semidefinite. -/
def ComplexDominates {m k : ℕ} (D : ComplexWeightedDesign m k)
    (C : Finset (Fin m)) : Prop :=
  ((∑ c ∈ C, complexAtom (D.atom c)) - 1).PosSemidef

/-- The complex analogue of weighted GTZ at size (m, k). -/
def ComplexGtzWeighted (m k : ℕ) : Prop :=
  ∀ D : ComplexWeightedDesign m k, ∃ C : Finset (Fin m),
    C.card = k ∧ ComplexDominates D C

/-! ### The 2×2 pair determinant -/

/-- The pair-excess determinant in Gram data: a pure ring identity. -/
theorem det_pair_excess (g h : Fin 2 → ℂ) :
    (complexAtom g + complexAtom h - 1).det
      = (star g ⬝ᵥ g - 1) * (star h ⬝ᵥ h - 1)
        - (star g ⬝ᵥ h) * (star h ⬝ᵥ g) := by
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.sub_apply,
    complexAtom, Matrix.vecMulVec_apply, Matrix.one_apply, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, RCLike.star_def]
  norm_num
  ring

/-- A pair whose atoms have squared length 2 and overlap product `4/3` has
excess determinant exactly `−1/3`. -/
theorem det_pair_excess_value {g h : Fin 2 → ℂ}
    (hg : star g ⬝ᵥ g = 2) (hh : star h ⬝ᵥ h = 2)
    (hcross : (star g ⬝ᵥ h) * (star h ⬝ᵥ g) = 4 / 3) :
    (complexAtom g + complexAtom h - 1).det = -(1 / 3) := by
  rw [det_pair_excess, hg, hh, hcross]
  norm_num

/-- Such a pair cannot dominate: PSD forces nonnegative determinant, and the
determinant is `−1/3`. -/
theorem pair_not_posSemidef {g h : Fin 2 → ℂ}
    (hg : star g ⬝ᵥ g = 2) (hh : star h ⬝ᵥ h = 2)
    (hcross : (star g ⬝ᵥ h) * (star h ⬝ᵥ g) = 4 / 3) :
    ¬ (complexAtom g + complexAtom h - 1).PosSemidef := by
  intro hpsd
  have hdetNonneg := hpsd.det_nonneg
  rw [det_pair_excess_value hg hh hcross] at hdetNonneg
  have hreal : (0 : ℝ) ≤ -(1 / 3) := by
    have := Complex.le_def.mp hdetNonneg
    simpa using this.1
  linarith

/-! ### The cube root of unity -/

theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- `ω = e^{2πi/3}`, written with explicit real and imaginary parts. -/
noncomputable def omegaRoot : ℂ := ⟨-(1 / 2 : ℝ), Real.sqrt 3 / 2⟩

theorem omegaRoot_star_mul : (starRingEnd ℂ) omegaRoot * omegaRoot = 1 := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, omegaRoot,
      Complex.one_re]
    nlinarith [sqrt_three_sq]
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, omegaRoot,
      Complex.one_im]
    ring

theorem omegaRoot_sq : omegaRoot ^ 2 = (starRingEnd ℂ) omegaRoot := by
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      omegaRoot]
    nlinarith [sqrt_three_sq]
  · simp only [pow_two, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      omegaRoot]
    ring

theorem omegaRoot_cube : omegaRoot ^ 3 = 1 := by
  rw [pow_succ, omegaRoot_sq, mul_comm ((starRingEnd ℂ) omegaRoot) omegaRoot]
  rw [mul_comm]
  exact omegaRoot_star_mul

theorem omegaRoot_sum : 1 + omegaRoot + omegaRoot ^ 2 = 0 := by
  rw [omegaRoot_sq]
  apply Complex.ext
  · simp [omegaRoot, Complex.add_re, Complex.conj_re]
    ring
  · simp [omegaRoot, Complex.add_im, Complex.conj_im]

theorem omegaRoot_conj_sq : (starRingEnd ℂ) (omegaRoot ^ 2) = omegaRoot := by
  rw [omegaRoot_sq, RingHomInvPair.comp_apply_eq]

/-- The overlap-product engine: `(2/3 + 4/3·ω)(2/3 + 4/3·ω²) = 4/3`. -/
theorem omega_overlap_product :
    (2 / 3 + 4 / 3 * omegaRoot) * (2 / 3 + 4 / 3 * omegaRoot ^ 2) = 4 / 3 := by
  have hsum := omegaRoot_sum
  have hcube := omegaRoot_cube
  have hexpand : (2 / 3 + 4 / 3 * omegaRoot) * (2 / 3 + 4 / 3 * omegaRoot ^ 2)
      = 4 / 9 + 8 / 9 * (omegaRoot + omegaRoot ^ 2)
        + 16 / 9 * omegaRoot ^ 3 := by ring
  have hpair : omegaRoot + omegaRoot ^ 2 = -1 := by
    have := hsum
    linear_combination this
  rw [hexpand, hpair, hcube]
  norm_num

/-! ### The SIC design -/

/-- The three amplitudes of the SIC atoms, as complex numbers. -/
noncomputable def topAmpC : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
noncomputable def sideAmpC : ℂ := ((Real.sqrt (2 / 3) : ℝ) : ℂ)
noncomputable def waveAmpC : ℂ := ((Real.sqrt (4 / 3) : ℝ) : ℂ)

theorem topAmpC_conj : (starRingEnd ℂ) topAmpC = topAmpC :=
  Complex.conj_ofReal _
theorem sideAmpC_conj : (starRingEnd ℂ) sideAmpC = sideAmpC :=
  Complex.conj_ofReal _
theorem waveAmpC_conj : (starRingEnd ℂ) waveAmpC = waveAmpC :=
  Complex.conj_ofReal _

theorem topAmpC_sq : topAmpC * topAmpC = 2 := by
  rw [topAmpC, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem sideAmpC_sq : sideAmpC * sideAmpC = 2 / 3 := by
  rw [sideAmpC, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2/3)]
  norm_num

theorem waveAmpC_sq : waveAmpC * waveAmpC = 4 / 3 := by
  rw [waveAmpC, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 4/3)]
  norm_num

/-- The four SIC atoms in ℂ², scaled to leverage 2. -/
noncomputable def sicAtom : Fin 4 → Fin 2 → ℂ :=
  ![![topAmpC, 0],
    ![sideAmpC, waveAmpC],
    ![sideAmpC, waveAmpC * omegaRoot],
    ![sideAmpC, waveAmpC * omegaRoot ^ 2]]

/-- The conjugated cube-root sum, for the Parseval off-diagonal. -/
theorem omegaRoot_conj_sum :
    1 + (starRingEnd ℂ) omegaRoot + (starRingEnd ℂ) (omegaRoot ^ 2) = 0 := by
  have happly := congrArg (starRingEnd ℂ) omegaRoot_sum
  simpa using happly

theorem omegaRoot_conj_eq : (starRingEnd ℂ) omegaRoot = omegaRoot ^ 2 :=
  omegaRoot_sq.symm

/-! ### Reducing the atoms and their pairings -/

theorem starDot_pair (firstTop firstBot secondTop secondBot : ℂ) :
    star ![firstTop, firstBot] ⬝ᵥ ![secondTop, secondBot]
      = (starRingEnd ℂ) firstTop * secondTop
        + (starRingEnd ℂ) firstBot * secondBot := by
  simp [dotProduct, Fin.sum_univ_two, Pi.star_apply, RCLike.star_def]

theorem sicAtom_zero : sicAtom 0 = ![topAmpC, 0] := rfl
theorem sicAtom_one : sicAtom 1 = ![sideAmpC, waveAmpC] := rfl
theorem sicAtom_two : sicAtom 2 = ![sideAmpC, waveAmpC * omegaRoot] := rfl
theorem sicAtom_three : sicAtom 3 = ![sideAmpC, waveAmpC * omegaRoot ^ 2] := rfl

/-! ### Atom norms -/

theorem sicNorm (c : Fin 4) : star (sicAtom c) ⬝ᵥ sicAtom c = 2 := by
  fin_cases c
  · rw [show ((⟨0, by omega⟩ : Fin 4)) = 0 from rfl, sicAtom_zero, starDot_pair,
      topAmpC_conj]
    linear_combination topAmpC_sq
  · rw [show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl, sicAtom_one, starDot_pair,
      sideAmpC_conj, waveAmpC_conj]
    linear_combination sideAmpC_sq + waveAmpC_sq
  · rw [show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl, sicAtom_two, starDot_pair,
      sideAmpC_conj, map_mul, waveAmpC_conj, omegaRoot_conj_eq]
    linear_combination sideAmpC_sq + omegaRoot ^ 3 * waveAmpC_sq
      + (4 / 3) * omegaRoot_cube
  · rw [show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl, sicAtom_three, starDot_pair,
      sideAmpC_conj, map_mul, waveAmpC_conj, map_pow, omegaRoot_conj_eq]
    linear_combination sideAmpC_sq + omegaRoot ^ 6 * waveAmpC_sq
      + (4 / 3) * (omegaRoot ^ 3 + 1) * omegaRoot_cube

/-! ### The six overlap values -/

theorem sicOverlap_zero_side {j : Fin 4} (hj : j ≠ 0) :
    (star (sicAtom 0) ⬝ᵥ sicAtom j) * (star (sicAtom j) ⬝ᵥ sicAtom 0)
      = 4 / 3 := by
  fin_cases j
  · exact absurd rfl hj
  · rw [show ((⟨1, by omega⟩ : Fin 4)) = 1 from rfl, sicAtom_zero, sicAtom_one,
      starDot_pair, starDot_pair, topAmpC_conj, sideAmpC_conj, waveAmpC_conj,
      map_zero]
    linear_combination (sideAmpC * sideAmpC) * topAmpC_sq + 2 * sideAmpC_sq
  · rw [show ((⟨2, by omega⟩ : Fin 4)) = 2 from rfl, sicAtom_zero, sicAtom_two,
      starDot_pair, starDot_pair, topAmpC_conj, sideAmpC_conj, map_mul,
      waveAmpC_conj, omegaRoot_conj_eq, map_zero]
    linear_combination (sideAmpC * sideAmpC) * topAmpC_sq + 2 * sideAmpC_sq
  · rw [show ((⟨3, by omega⟩ : Fin 4)) = 3 from rfl, sicAtom_zero, sicAtom_three,
      starDot_pair, starDot_pair, topAmpC_conj, sideAmpC_conj, map_mul,
      map_pow, waveAmpC_conj, omegaRoot_conj_eq, map_zero]
    linear_combination (sideAmpC * sideAmpC) * topAmpC_sq + 2 * sideAmpC_sq

theorem sicOv_one_two : star (sicAtom 1) ⬝ᵥ sicAtom 2
    = 2 / 3 + 4 / 3 * omegaRoot := by
  rw [sicAtom_one, sicAtom_two, starDot_pair, sideAmpC_conj, waveAmpC_conj]
  linear_combination sideAmpC_sq + omegaRoot * waveAmpC_sq

theorem sicOv_two_one : star (sicAtom 2) ⬝ᵥ sicAtom 1
    = 2 / 3 + 4 / 3 * omegaRoot ^ 2 := by
  rw [sicAtom_two, sicAtom_one, starDot_pair, sideAmpC_conj, map_mul,
    waveAmpC_conj, omegaRoot_conj_eq]
  linear_combination sideAmpC_sq + omegaRoot ^ 2 * waveAmpC_sq

theorem sicOv_one_three : star (sicAtom 1) ⬝ᵥ sicAtom 3
    = 2 / 3 + 4 / 3 * omegaRoot ^ 2 := by
  rw [sicAtom_one, sicAtom_three, starDot_pair, sideAmpC_conj, waveAmpC_conj]
  linear_combination sideAmpC_sq + omegaRoot ^ 2 * waveAmpC_sq

theorem sicOv_three_one : star (sicAtom 3) ⬝ᵥ sicAtom 1
    = 2 / 3 + 4 / 3 * omegaRoot := by
  rw [sicAtom_three, sicAtom_one, starDot_pair, sideAmpC_conj, map_mul,
    map_pow, waveAmpC_conj, omegaRoot_conj_eq]
  linear_combination sideAmpC_sq + omegaRoot ^ 4 * waveAmpC_sq
    + (4 / 3) * omegaRoot * omegaRoot_cube

theorem sicOv_two_three : star (sicAtom 2) ⬝ᵥ sicAtom 3
    = 2 / 3 + 4 / 3 * omegaRoot := by
  rw [sicAtom_two, sicAtom_three, starDot_pair, sideAmpC_conj, map_mul,
    waveAmpC_conj, omegaRoot_conj_eq]
  linear_combination sideAmpC_sq + omegaRoot ^ 4 * waveAmpC_sq
    + (4 / 3) * omegaRoot * omegaRoot_cube

theorem sicOv_three_two : star (sicAtom 3) ⬝ᵥ sicAtom 2
    = 2 / 3 + 4 / 3 * omegaRoot ^ 2 := by
  rw [sicAtom_three, sicAtom_two, starDot_pair, sideAmpC_conj, map_mul,
    map_pow, waveAmpC_conj, omegaRoot_conj_eq]
  linear_combination sideAmpC_sq + omegaRoot ^ 5 * waveAmpC_sq
    + (4 / 3) * omegaRoot ^ 2 * omegaRoot_cube

/-- The reversed zero-side products. -/
theorem sicOverlap_side_zero {j : Fin 4} (hj : j ≠ 0) :
    (star (sicAtom j) ⬝ᵥ sicAtom 0) * (star (sicAtom 0) ⬝ᵥ sicAtom j)
      = 4 / 3 := by
  rw [mul_comm]
  exact sicOverlap_zero_side hj

theorem sicProd_one_two : (star (sicAtom 1) ⬝ᵥ sicAtom 2)
    * (star (sicAtom 2) ⬝ᵥ sicAtom 1) = 4 / 3 := by
  rw [sicOv_one_two, sicOv_two_one]
  exact omega_overlap_product

theorem sicProd_two_one : (star (sicAtom 2) ⬝ᵥ sicAtom 1)
    * (star (sicAtom 1) ⬝ᵥ sicAtom 2) = 4 / 3 := by
  rw [mul_comm]
  exact sicProd_one_two

theorem sicProd_one_three : (star (sicAtom 1) ⬝ᵥ sicAtom 3)
    * (star (sicAtom 3) ⬝ᵥ sicAtom 1) = 4 / 3 := by
  rw [sicOv_one_three, sicOv_three_one, mul_comm]
  exact omega_overlap_product

theorem sicProd_three_one : (star (sicAtom 3) ⬝ᵥ sicAtom 1)
    * (star (sicAtom 1) ⬝ᵥ sicAtom 3) = 4 / 3 := by
  rw [mul_comm]
  exact sicProd_one_three

theorem sicProd_two_three : (star (sicAtom 2) ⬝ᵥ sicAtom 3)
    * (star (sicAtom 3) ⬝ᵥ sicAtom 2) = 4 / 3 := by
  rw [sicOv_two_three, sicOv_three_two]
  exact omega_overlap_product

theorem sicProd_three_two : (star (sicAtom 3) ⬝ᵥ sicAtom 2)
    * (star (sicAtom 2) ⬝ᵥ sicAtom 3) = 4 / 3 := by
  rw [mul_comm]
  exact sicProd_two_three

/-- **Every pair of SIC atoms has overlap product `4/3`** — equiangularity in
Gram form. -/
theorem sicOverlap {first second : Fin 4} (hne : first ≠ second) :
    (star (sicAtom first) ⬝ᵥ sicAtom second)
      * (star (sicAtom second) ⬝ᵥ sicAtom first) = 4 / 3 := by
  fin_cases first <;> fin_cases second
  · exact absurd rfl hne
  · exact sicOverlap_zero_side (by decide)
  · exact sicOverlap_zero_side (by decide)
  · exact sicOverlap_zero_side (by decide)
  · exact sicOverlap_side_zero (by decide)
  · exact absurd rfl hne
  · exact sicProd_one_two
  · exact sicProd_one_three
  · exact sicOverlap_side_zero (by decide)
  · exact sicProd_two_one
  · exact absurd rfl hne
  · exact sicProd_two_three
  · exact sicOverlap_side_zero (by decide)
  · exact sicProd_three_one
  · exact sicProd_three_two
  · exact absurd rfl hne

/-! ### Parseval and the design -/

/-- The SIC atoms at uniform weight resolve the identity — the cube-root
cancellation, entry by entry. -/
theorem sicParseval :
    ∑ c, (((1 : ℝ) / 4 : ℝ) : ℂ) • complexAtom (sicAtom c) = 1 := by
  have hsum := omegaRoot_sum
  have hconjsum := omegaRoot_conj_sum
  have hcube := omegaRoot_cube
  ext rowIndex colIndex
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, complexAtom, Matrix.vecMulVec_apply,
    Pi.star_apply, RCLike.star_def, smul_eq_mul, Fin.sum_univ_four]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [sicAtom_zero, sicAtom_one, sicAtom_two, sicAtom_three,
      map_mul, map_pow, topAmpC_conj, sideAmpC_conj, waveAmpC_conj,
      omegaRoot_conj_eq, Matrix.one_apply]
  · -- (0,0): (1/4)(top² + 3·side²)
    linear_combination (1 / 4) * topAmpC_sq + (3 / 4) * sideAmpC_sq
  · -- (0,1): (1/4)·side·wave·(1 + ω² + ω⁴) = 0
    linear_combination (1 / 4) * sideAmpC * waveAmpC * (1 + omegaRoot) * hsum
      - (1 / 4) * sideAmpC * waveAmpC * omegaRoot * hcube
      - (1 / 4) * sideAmpC * waveAmpC * hsum
      + (omegaRoot / 2 - 1 / 4) * sideAmpC * waveAmpC * hcube
  · -- (1,0): (1/4)·wave·side·(1 + ω + ω²) = 0
    linear_combination (1 / 4) * sideAmpC * waveAmpC * hsum
  · -- (1,1): (1/4)(wave² + 2·wave²·ω³)
    linear_combination (1 / 4) * waveAmpC_sq
      + (omegaRoot ^ 3 / 2) * waveAmpC_sq + (2 / 3) * hcube
      + (omegaRoot ^ 3 / 4) * waveAmpC_sq + (1 / 3) * hcube
      - (1 / 4) * waveAmpC_sq
      + (waveAmpC * waveAmpC * (omegaRoot ^ 3 - 1) / 4) * hcube

/-- The SIC weighted design over ℂ. -/
noncomputable def sicDesign : ComplexWeightedDesign 4 2 where
  atom := sicAtom
  weight := fun _ => 1 / 4
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Fin.sum_univ_four]
    norm_num
  isParseval := sicParseval

/-! ### The headline -/

/-- **Weighted (4,2) is FALSE over ℂ.** The SIC design has no dominating pair:
every pair's excess determinant is `−1/3 < 0`. Since weighted (4,2) is the
canonical list's unique rank-2 entry and a theorem over ℝ (`gtz_rank_two`),
no field-blind argument can prove the canonical list — every proof of GTZ
must consume realness. -/
theorem complexGtzWeighted_four_fails : ¬ ComplexGtzWeighted 4 2 := by
  intro hcontra
  obtain ⟨C, hcard, hdom⟩ := hcontra sicDesign
  obtain ⟨firstIdx, secondIdx, hne, hpair⟩ := Finset.card_eq_two.mp hcard
  rw [ComplexDominates, hpair, Finset.sum_pair hne] at hdom
  exact pair_not_posSemidef (sicNorm firstIdx) (sicNorm secondIdx)
    (sicOverlap hne) hdom

end Gtz
