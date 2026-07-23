/-
# The PSD transfer kit: contraction/expansion flips and invertible congruence

The sqrt-free, spectra-free Loewner toolbox consumed by Theorem N's four
congruence steps (and later by the cap criterion):

* `dotProduct_mulVec_transpose` — the adjoint identity ⟨Xᵀw, u⟩ = ⟨w, Xu⟩;
* `posSemidef_one_sub_iff_contraction` — I − XᵀX ⪰ 0 ⟺ X is a quadratic-form
  contraction (|Xu|² ≤ |u|² for all u);
* `contraction_flip` — contraction of X gives contraction of Xᵀ, by
  Cauchy–Schwarz on squares alone: |Xᵀw|⁴ = ⟨w, X(Xᵀw)⟩² ≤ |w|²·|X(Xᵀw)|²
  ≤ |w|²·|Xᵀw|²;
* `posSemidef_one_sub_transpose_comm` — I − XᵀX ⪰ 0 ⟺ I − XXᵀ ⪰ 0
  (rectangular X, both directions of the flip);
* `posSemidef_congr_right` — X ⪰ 0 ⟺ PᵀXP ⪰ 0 for invertible P (quadratic
  form substitution, both directions via P⁻¹);
* `posSemidef_transpose_mul_sub_one_comm` — MᵀM ⪰ I ⟺ MMᵀ ⪰ I for SQUARE M
  (either side forces invertibility; then contraction of M⁻¹ flips).

Everything is stated over ℝ with the raw `dotProduct` quadratic form; no
matrix square roots, no eigenvalues, no operator norms.
-/
import Mathlib
import Gtz.Basic
import Gtz.SchurRankOne

namespace Gtz

open Matrix

variable {a b : ℕ}

/-- The dot square is nonnegative. -/
theorem dotProduct_self_nonneg (v : Fin a → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- The dot square as a sum of squares. -/
theorem dotProduct_self_eq_sum_sq (v : Fin a → ℝ) : v ⬝ᵥ v = ∑ i, v i ^ 2 :=
  Finset.sum_congr rfl fun i _ => (pow_two (v i)).symm

/-- The adjoint identity for the raw dot product: ⟨Xᵀw, u⟩ = ⟨w, Xu⟩. -/
theorem dotProduct_mulVec_transpose (X : Matrix (Fin a) (Fin b) ℝ)
    (w : Fin a → ℝ) (u : Fin b → ℝ) :
    (Xᵀ *ᵥ w) ⬝ᵥ u = w ⬝ᵥ (X *ᵥ u) := by
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]

/-- I − XᵀX ⪰ 0 says exactly that X contracts the quadratic form. -/
theorem posSemidef_one_sub_iff_contraction (X : Matrix (Fin a) (Fin b) ℝ) :
    (1 - Xᵀ * X).PosSemidef ↔
      ∀ u : Fin b → ℝ, (X *ᵥ u) ⬝ᵥ (X *ᵥ u) ≤ u ⬝ᵥ u := by
  have hquad : ∀ u : Fin b → ℝ,
      u ⬝ᵥ ((1 - Xᵀ * X) *ᵥ u) = u ⬝ᵥ u - (X *ᵥ u) ⬝ᵥ (X *ᵥ u) := by
    intro u
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_comm u (Xᵀ *ᵥ (X *ᵥ u)), dotProduct_mulVec_transpose]
  constructor
  · intro hpsd u
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 u
    rw [star_trivial, hquad u] at h
    linarith
  · intro hcontr
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun u => ?_⟩
    · refine isHermitian_of_transpose_eq ?_
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
        Matrix.transpose_transpose]
    · rw [star_trivial, hquad u]
      linarith [hcontr u]

/-- **The Cauchy–Schwarz flip**: a quadratic-form contraction transposes.
Squares only: |Xᵀw|⁴ = ⟨w, X(Xᵀw)⟩² ≤ |w|²·|X(Xᵀw)|² ≤ |w|²·|Xᵀw|². -/
theorem contraction_flip (X : Matrix (Fin a) (Fin b) ℝ)
    (hcontr : ∀ u : Fin b → ℝ, (X *ᵥ u) ⬝ᵥ (X *ᵥ u) ≤ u ⬝ᵥ u)
    (w : Fin a → ℝ) :
    (Xᵀ *ᵥ w) ⬝ᵥ (Xᵀ *ᵥ w) ≤ w ⬝ᵥ w := by
  have hkey : (Xᵀ *ᵥ w) ⬝ᵥ (Xᵀ *ᵥ w) = w ⬝ᵥ (X *ᵥ (Xᵀ *ᵥ w)) :=
    dotProduct_mulVec_transpose X w (Xᵀ *ᵥ w)
  have hCS : (w ⬝ᵥ (X *ᵥ (Xᵀ *ᵥ w))) ^ 2
      ≤ (w ⬝ᵥ w) * ((X *ᵥ (Xᵀ *ᵥ w)) ⬝ᵥ (X *ᵥ (Xᵀ *ᵥ w))) := by
    calc (w ⬝ᵥ (X *ᵥ (Xᵀ *ᵥ w))) ^ 2
        ≤ (∑ i, w i ^ 2) * (∑ i, (X *ᵥ (Xᵀ *ᵥ w)) i ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (w ⬝ᵥ w) * ((X *ᵥ (Xᵀ *ᵥ w)) ⬝ᵥ (X *ᵥ (Xᵀ *ᵥ w))) := by
          rw [dotProduct_self_eq_sum_sq, dotProduct_self_eq_sum_sq]
  have hXv := hcontr (Xᵀ *ᵥ w)
  have hvnn := dotProduct_self_nonneg (Xᵀ *ᵥ w)
  have hwnn := dotProduct_self_nonneg w
  nlinarith [hCS, hXv, hvnn, hwnn, hkey]

/-- **The rectangular transfer**: I − XᵀX ⪰ 0 ⟺ I − XXᵀ ⪰ 0. -/
theorem posSemidef_one_sub_transpose_comm (X : Matrix (Fin a) (Fin b) ℝ) :
    (1 - Xᵀ * X).PosSemidef ↔ (1 - X * Xᵀ).PosSemidef := by
  have h2 := posSemidef_one_sub_iff_contraction Xᵀ
  rw [Matrix.transpose_transpose] at h2
  rw [posSemidef_one_sub_iff_contraction X, h2]
  constructor
  · exact fun h w => contraction_flip X h w
  · intro h u
    have hflip := contraction_flip Xᵀ h u
    rwa [Matrix.transpose_transpose] at hflip

/-- **Invertible congruence**: X ⪰ 0 ⟺ PᵀXP ⪰ 0 for invertible P — the
quadratic form substitutes along the bijection u ↦ Pu. -/
theorem posSemidef_congr_right {X P : Matrix (Fin a) (Fin a) ℝ}
    (hXT : Xᵀ = X) (hP : IsUnit P.det) :
    X.PosSemidef ↔ (Pᵀ * X * P).PosSemidef := by
  have hquad : ∀ u : Fin a → ℝ,
      u ⬝ᵥ ((Pᵀ * X * P) *ᵥ u) = (P *ᵥ u) ⬝ᵥ (X *ᵥ (P *ᵥ u)) := by
    intro u
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_comm u (Pᵀ *ᵥ (X *ᵥ (P *ᵥ u))), dotProduct_mulVec_transpose,
      dotProduct_comm]
  have hPPT : (Pᵀ * X * P)ᵀ = Pᵀ * X * P := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hXT, Matrix.mul_assoc]
  constructor
  · intro hpsd
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hPPT, fun u => ?_⟩
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 (P *ᵥ u)
    rw [star_trivial] at h
    rw [star_trivial, hquad u]
    exact h
  · intro hpsd
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hXT, fun v => ?_⟩
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 (P⁻¹ *ᵥ v)
    rw [star_trivial, hquad (P⁻¹ *ᵥ v), Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec] at h
    rw [star_trivial]
    exact h

/-- **The square expansion transfer**: MᵀM ⪰ I ⟺ MMᵀ ⪰ I for square M.
Either side forces invertibility (the form dominates |u|² > 0, so the
determinant cannot vanish); then the contraction of M⁻¹ flips by
Cauchy–Schwarz. -/
theorem posSemidef_transpose_mul_sub_one_comm (M : Matrix (Fin a) (Fin a) ℝ) :
    (Mᵀ * M - 1).PosSemidef ↔ (M * Mᵀ - 1).PosSemidef := by
  -- expansion of N ⟺ contraction of N⁻¹, for the two products
  have hexpand : ∀ N : Matrix (Fin a) (Fin a) ℝ,
      (Nᵀ * N - 1).PosSemidef ↔
        ∀ u : Fin a → ℝ, u ⬝ᵥ u ≤ (N *ᵥ u) ⬝ᵥ (N *ᵥ u) := by
    intro N
    have hquad : ∀ u : Fin a → ℝ,
        u ⬝ᵥ ((Nᵀ * N - 1) *ᵥ u) = (N *ᵥ u) ⬝ᵥ (N *ᵥ u) - u ⬝ᵥ u := by
      intro u
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        dotProduct_comm u (Nᵀ *ᵥ (N *ᵥ u)), dotProduct_mulVec_transpose]
    constructor
    · intro hpsd u
      have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 u
      rw [star_trivial, hquad u] at h
      linarith
    · intro hexp
      refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun u => ?_⟩
      · refine isHermitian_of_transpose_eq ?_
        rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
          Matrix.transpose_transpose]
      · rw [star_trivial, hquad u]
        linarith [hexp u]
  -- expansion forces an invertible determinant
  have hdet : ∀ N : Matrix (Fin a) (Fin a) ℝ,
      (∀ u : Fin a → ℝ, u ⬝ᵥ u ≤ (N *ᵥ u) ⬝ᵥ (N *ᵥ u)) → IsUnit N.det := by
    intro N hexp
    have hker : ∀ u : Fin a → ℝ, N *ᵥ u = 0 → u = 0 := by
      intro u hu
      have h := hexp u
      rw [hu] at h
      simp only [dotProduct_zero] at h
      have hz : u ⬝ᵥ u = 0 := le_antisymm h (dotProduct_self_nonneg u)
      funext t
      have hsq := (Finset.sum_eq_zero_iff_of_nonneg
        (fun s _ => mul_self_nonneg (u s))).mp hz
      simpa using mul_self_eq_zero.mp (hsq t (Finset.mem_univ t))
    rw [isUnit_iff_ne_zero]
    intro hdet0
    obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
    exact hvne (hker v hv)
  -- one direction suffices by symmetry of the statement in M ↔ Mᵀ
  have hdir : ∀ N : Matrix (Fin a) (Fin a) ℝ,
      (Nᵀ * N - 1).PosSemidef → (N * Nᵀ - 1).PosSemidef := by
    intro N hpsd
    have hexp := (hexpand N).mp hpsd
    have hNdet := hdet N hexp
    have hNTdet : IsUnit Nᵀ.det := by rwa [Matrix.det_transpose]
    -- contraction of N⁻¹ from expansion of N (substitute u := N⁻¹v)
    have hcontrInv : ∀ v : Fin a → ℝ,
        (N⁻¹ *ᵥ v) ⬝ᵥ (N⁻¹ *ᵥ v) ≤ v ⬝ᵥ v := by
      intro v
      have h := hexp (N⁻¹ *ᵥ v)
      rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hNdet,
        Matrix.one_mulVec] at h
    -- flip: contraction of (N⁻¹)ᵀ = (Nᵀ)⁻¹
    have hcontrInvT := contraction_flip N⁻¹ hcontrInv
    -- expansion of Nᵀ: |Nᵀw|² ≥ |w|² via w = (N⁻¹)ᵀ(Nᵀw)
    refine (hexpand Nᵀ).mpr fun w => ?_
    have h := hcontrInvT (Nᵀ *ᵥ w)
    rwa [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv N hNdet, Matrix.transpose_one,
      Matrix.one_mulVec] at h
  constructor
  · exact fun h => hdir M h
  · intro h
    have := hdir Mᵀ (by rwa [Matrix.transpose_transpose])
    rwa [Matrix.transpose_transpose] at this

/-- **Invertible congruence, definite version**: X ≻ 0 ⟺ PᵀXP ≻ 0 for
invertible P. -/
theorem posDef_congr_right {X P : Matrix (Fin a) (Fin a) ℝ}
    (hXT : Xᵀ = X) (hP : IsUnit P.det) :
    X.PosDef ↔ (Pᵀ * X * P).PosDef := by
  have hquad : ∀ u : Fin a → ℝ,
      u ⬝ᵥ ((Pᵀ * X * P) *ᵥ u) = (P *ᵥ u) ⬝ᵥ (X *ᵥ (P *ᵥ u)) := by
    intro u
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_comm u (Pᵀ *ᵥ (X *ᵥ (P *ᵥ u))), dotProduct_mulVec_transpose,
      dotProduct_comm]
  have hPPT : (Pᵀ * X * P)ᵀ = Pᵀ * X * P := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hXT, Matrix.mul_assoc]
  have hPker : ∀ u : Fin a → ℝ, P *ᵥ u = 0 → u = 0 := by
    intro u hu
    have h := congrArg (fun z => P⁻¹ *ᵥ z) hu
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP,
      Matrix.one_mulVec] using h
  constructor
  · intro hpd
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hPPT, fun u hu => ?_⟩
    have hPu : P *ᵥ u ≠ 0 := fun h0 => hu (hPker u h0)
    have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hPu
    rw [star_trivial] at h
    rw [star_trivial, hquad u]
    exact h
  · intro hpd
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hXT, fun v hv => ?_⟩
    have hv' : P⁻¹ *ᵥ v ≠ 0 := by
      intro h0
      apply hv
      have hrec : P *ᵥ (P⁻¹ *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP,
          Matrix.one_mulVec]
      rw [← hrec, h0, Matrix.mulVec_zero]
    have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hv'
    rw [star_trivial, hquad (P⁻¹ *ᵥ v), Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec] at h
    rw [star_trivial]
    exact h

open scoped MatrixOrder in
/-- **Whitening**: every PD real matrix is congruent to the identity,
RᵀWR = 1 with R invertible. Consumed from the C*-algebra factorization
0 ≤ W ⟺ W = star L·L; positive-definiteness upgrades L to invertible. -/
theorem exists_congruence_to_one {k : ℕ} {W : Matrix (Fin k) (Fin k) ℝ}
    (hW : W.PosDef) :
    ∃ R : Matrix (Fin k) (Fin k) ℝ, IsUnit R.det ∧ Rᵀ * W * R = 1 := by
  obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hW.posSemidef.nonneg
  have hLT : W = Lᵀ * L := by
    rw [hL, Matrix.star_eq_conjTranspose]
    congr 1
  have hdetL : IsUnit L.det := by
    have hdetW := hW.det_pos
    rw [hLT, Matrix.det_mul, Matrix.det_transpose] at hdetW
    rw [isUnit_iff_ne_zero]
    intro hzero
    rw [hzero, mul_zero] at hdetW
    exact lt_irrefl 0 hdetW
  have hdetLT : IsUnit Lᵀ.det := by rwa [Matrix.det_transpose]
  refine ⟨L⁻¹, ?_, ?_⟩
  · exact L.isUnit_nonsing_inv_det hdetL
  · rw [hLT, Matrix.transpose_nonsing_inv, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hdetLT, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hdetL]

end Gtz
