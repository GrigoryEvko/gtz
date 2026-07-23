/-
# The κ₁ brick: perturbed-resolvent bound, norm-free and fully squared

The honest hard part of Theorem A's off-corner chain. The artifact states it
as `‖B̃⁻¹ − B⁻¹‖ ≤ 2δ₁/(1−2δ₁) = κ₁`; here the whole Neumann/congruence
argument is replaced by a sqrt-free quadratic-form chain over the raw
`dotProduct` — no operator norms, no eigenvalues, no series:

* a matrix whose form expands (`|Bx|² ≥ |x|²`, i.e. every eigenvalue has
  magnitude ≥ 1 — signature-agnostic, exactly what the indefinite `(2,1)` cap
  needs) has an invertible determinant and a contracting inverse;
* an entrywise-`δ` noise matrix obeys `|Ex|² ≤ δ²n²|x|²` (Cauchy–Schwarz
  against the all-ones vector, squared throughout);
* the perturbed gate stays coercive: `|(B+E)x|² ≥ (1 − δn(β+1))|x|²` where
  `β` caps the base form (the cross term is absorbed by `4β ≤ (β+1)²`);
* the resolvent difference identity `Ã⁻¹ − B⁻¹ = Ã⁻¹(B − Ã)B⁻¹` is ring
  algebra, and the assembled bound reads, division-free,

  `(1 − δn(β+1)) · ⟨x, (Ã⁻¹ − B⁻¹)x⟩² ≤ δ²n²·⟨x,x⟩²` —

  the kernel-checked κ₁: informally `|⟨x, (Ã⁻¹−B⁻¹)x⟩| ≤ δn/√(1−δn(β+1))·|x|²`.
-/
import Mathlib
import Gtz.PsdKit

namespace Gtz

open Matrix

variable {n : ℕ}

/-- A vector whose dot square vanishes is zero. -/
theorem eq_zero_of_dotProduct_self_eq_zero {probe : Fin n → ℝ}
    (hself : probe ⬝ᵥ probe = 0) : probe = 0 := by
  funext index
  have hsq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun s _ => mul_self_nonneg (probe s))).mp hself
  simpa using mul_self_eq_zero.mp (hsq index (Finset.mem_univ index))

/-- Cauchy–Schwarz for the raw dot product, squared form. -/
theorem dotProduct_sq_le_mul (leftVec rightVec : Fin n → ℝ) :
    (leftVec ⬝ᵥ rightVec) ^ 2
      ≤ (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => leftVec i) (fun i => rightVec i)
  calc (leftVec ⬝ᵥ rightVec) ^ 2
      ≤ (∑ i, leftVec i ^ 2) * (∑ i, rightVec i ^ 2) := hcs
    _ = (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) := by
        rw [dotProduct_self_eq_sum_sq, dotProduct_self_eq_sum_sq]

/-- From `u² ≤ K²` with `K ≥ 0`, the lower square root: `−K ≤ u`. -/
theorem neg_le_of_sq_le_sq {value cap : ℝ}
    (hsq : value ^ 2 ≤ cap ^ 2) (hcapNonneg : 0 ≤ cap) : -cap ≤ value := by
  nlinarith [sq_nonneg (value + cap)]

/-- **Coercivity forces invertibility**: a matrix whose form is bounded below
by a positive multiple of the identity form has nonzero determinant. -/
theorem coercive_isUnit_det {gate : Matrix (Fin n) (Fin n) ℝ} {formFloor : ℝ}
    (hfloorPos : 0 < formFloor)
    (hcoercive : ∀ probe : Fin n → ℝ,
      formFloor * (probe ⬝ᵥ probe) ≤ (gate *ᵥ probe) ⬝ᵥ (gate *ᵥ probe)) :
    IsUnit gate.det := by
  rw [isUnit_iff_ne_zero]
  intro hdetZero
  obtain ⟨witness, hwitnessNe, hkill⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdetZero
  have hbound := hcoercive witness
  rw [hkill] at hbound
  simp only [dotProduct_zero] at hbound
  have hselfZero : witness ⬝ᵥ witness = 0 :=
    le_antisymm (by nlinarith [hbound, hfloorPos])
      (dotProduct_self_nonneg witness)
  exact hwitnessNe (eq_zero_of_dotProduct_self_eq_zero hselfZero)

/-- **The resolvent difference identity**: `A⁻¹ − B⁻¹ = A⁻¹(B − A)B⁻¹`. -/
theorem resolvent_difference {first second : Matrix (Fin n) (Fin n) ℝ}
    (hfirst : IsUnit first.det) (hsecond : IsUnit second.det) :
    first⁻¹ - second⁻¹ = first⁻¹ * (second - first) * second⁻¹ := by
  calc first⁻¹ - second⁻¹
      = first⁻¹ * (second * second⁻¹) - (first⁻¹ * first) * second⁻¹ := by
        rw [Matrix.mul_nonsing_inv second hsecond,
          Matrix.nonsing_inv_mul first hfirst, Matrix.mul_one, Matrix.one_mul]
    _ = first⁻¹ * (second - first) * second⁻¹ := by noncomm_ring

/-- **The coercive inverse contracts**: `formFloor·|A⁻¹y|² ≤ |y|²`. -/
theorem inverse_contraction_of_coercive
    {gate : Matrix (Fin n) (Fin n) ℝ} {formFloor : ℝ}
    (hfloorPos : 0 < formFloor)
    (hcoercive : ∀ probe : Fin n → ℝ,
      formFloor * (probe ⬝ᵥ probe) ≤ (gate *ᵥ probe) ⬝ᵥ (gate *ᵥ probe)) :
    ∀ target : Fin n → ℝ,
      formFloor * ((gate⁻¹ *ᵥ target) ⬝ᵥ (gate⁻¹ *ᵥ target))
        ≤ target ⬝ᵥ target := by
  intro target
  have hdet := coercive_isUnit_det hfloorPos hcoercive
  have hchain := hcoercive (gate⁻¹ *ᵥ target)
  rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv gate hdet,
    Matrix.one_mulVec] at hchain

/-- **Entrywise noise bounds the image form**: `|E i j| ≤ δ` gives
`|Ex|² ≤ δ²n²|x|²` — each entry of `Ex` is capped by `δ·Σ|x|`, and the
absolute sum squares to at most `n·|x|²` against the all-ones vector. -/
theorem noise_mulVec_sq_le {noise : Matrix (Fin n) (Fin n) ℝ}
    {entryBound : ℝ}
    (hnoise : ∀ i j, |noise i j| ≤ entryBound) :
    ∀ probe : Fin n → ℝ,
      (noise *ᵥ probe) ⬝ᵥ (noise *ᵥ probe)
        ≤ entryBound ^ 2 * n ^ 2 * (probe ⬝ᵥ probe) := by
  intro probe
  -- each image entry is capped by the scaled absolute mass of the probe
  have hentry : ∀ i, |(noise *ᵥ probe) i| ≤ entryBound * ∑ j, |probe j| := by
    intro i
    have happly : (noise *ᵥ probe) i = ∑ j, noise i j * probe j := by
      simp [Matrix.mulVec, dotProduct]
    rw [happly]
    calc |∑ j, noise i j * probe j|
        ≤ ∑ j, |noise i j * probe j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, entryBound * |probe j| := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hnoise i j) (abs_nonneg _)
      _ = entryBound * ∑ j, |probe j| := by rw [Finset.mul_sum]
  -- the absolute mass squares against the all-ones vector
  have hmass : (∑ j, |probe j|) ^ 2 ≤ (n : ℝ) * (probe ⬝ᵥ probe) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => |probe j|) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, sq_abs] at hcs
    calc (∑ j, |probe j|) ^ 2 ≤ (∑ j, probe j ^ 2) * n := hcs
      _ = (n : ℝ) * (probe ⬝ᵥ probe) := by
          rw [dotProduct_self_eq_sum_sq]; ring
  -- sum the per-entry squares
  have hbound : ∀ i, ((noise *ᵥ probe) i) ^ 2
      ≤ (entryBound * ∑ j, |probe j|) ^ 2 := by
    intro i
    have habs := hentry i
    have hcapNonneg : 0 ≤ entryBound * ∑ j, |probe j| :=
      le_trans (abs_nonneg _) habs
    exact sq_le_sq' (by linarith [neg_abs_le ((noise *ᵥ probe) i)])
      (le_trans (le_abs_self _) habs)
  calc (noise *ᵥ probe) ⬝ᵥ (noise *ᵥ probe)
      = ∑ i, ((noise *ᵥ probe) i) ^ 2 := dotProduct_self_eq_sum_sq _
    _ ≤ ∑ _i : Fin n, (entryBound * ∑ j, |probe j|) ^ 2 :=
        Finset.sum_le_sum fun i _ => hbound i
    _ = (n : ℝ) * (entryBound * ∑ j, |probe j|) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ = (n : ℝ) * entryBound ^ 2 * (∑ j, |probe j|) ^ 2 := by ring
    _ ≤ (n : ℝ) * entryBound ^ 2 * ((n : ℝ) * (probe ⬝ᵥ probe)) := by
        refine mul_le_mul_of_nonneg_left hmass ?_
        positivity
    _ = entryBound ^ 2 * n ^ 2 * (probe ⬝ᵥ probe) := by ring

/-- **The perturbed gate stays coercive**: an expanding base form capped by
`β`, hit by entrywise-`δ` noise, keeps `|(B+E)x|² ≥ (1 − δn(β+1))|x|²`.
The cross term is absorbed through `4β ≤ (β+1)²`. -/
theorem perturbed_expansion {base noise : Matrix (Fin n) (Fin n) ℝ}
    {entryBound formCap : ℝ}
    (hentryNonneg : 0 ≤ entryBound) (hcapNonneg : 0 ≤ formCap)
    (hlow : ∀ probe : Fin n → ℝ,
      probe ⬝ᵥ probe ≤ (base *ᵥ probe) ⬝ᵥ (base *ᵥ probe))
    (hhigh : ∀ probe : Fin n → ℝ,
      (base *ᵥ probe) ⬝ᵥ (base *ᵥ probe) ≤ formCap * (probe ⬝ᵥ probe))
    (hnoise : ∀ i j, |noise i j| ≤ entryBound) :
    ∀ probe : Fin n → ℝ,
      (1 - entryBound * n * (formCap + 1)) * (probe ⬝ᵥ probe)
        ≤ ((base + noise) *ᵥ probe) ⬝ᵥ ((base + noise) *ᵥ probe) := by
  intro probe
  set baseImage := base *ᵥ probe with hbaseImage
  set noiseImage := noise *ᵥ probe with hnoiseImage
  have hsplit : ((base + noise) *ᵥ probe) ⬝ᵥ ((base + noise) *ᵥ probe)
      = baseImage ⬝ᵥ baseImage + 2 * (baseImage ⬝ᵥ noiseImage)
        + noiseImage ⬝ᵥ noiseImage := by
    rw [Matrix.add_mulVec, ← hbaseImage, ← hnoiseImage, dotProduct_add,
      add_dotProduct, add_dotProduct, dotProduct_comm noiseImage baseImage]
    ring
  have hcross : (baseImage ⬝ᵥ noiseImage) ^ 2
      ≤ (formCap * (probe ⬝ᵥ probe))
        * (entryBound ^ 2 * n ^ 2 * (probe ⬝ᵥ probe)) := by
    calc (baseImage ⬝ᵥ noiseImage) ^ 2
        ≤ (baseImage ⬝ᵥ baseImage) * (noiseImage ⬝ᵥ noiseImage) :=
          dotProduct_sq_le_mul _ _
      _ ≤ (formCap * (probe ⬝ᵥ probe))
            * (entryBound ^ 2 * n ^ 2 * (probe ⬝ᵥ probe)) :=
          mul_le_mul (hhigh probe) (noise_mulVec_sq_le hnoise probe)
            (dotProduct_self_nonneg _)
            (mul_nonneg hcapNonneg (dotProduct_self_nonneg probe))
  -- the cross term is at least −δn(β+1)|x|², via 4β ≤ (β+1)²
  have hprobeNonneg := dotProduct_self_nonneg probe
  have hscaleNonneg : (0 : ℝ)
      ≤ entryBound ^ 2 * (n : ℝ) ^ 2 * (probe ⬝ᵥ probe) ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg entryBound) (sq_nonneg (n : ℝ)))
      (sq_nonneg _)
  have hcrossLow : -(entryBound * n * (formCap + 1) * (probe ⬝ᵥ probe))
      ≤ 2 * (baseImage ⬝ᵥ noiseImage) := by
    refine neg_le_of_sq_le_sq ?_
      (mul_nonneg (mul_nonneg
        (mul_nonneg hentryNonneg (Nat.cast_nonneg n)) (by linarith))
        hprobeNonneg)
    nlinarith [hcross, mul_nonneg (sq_nonneg (formCap - 1)) hscaleNonneg]
  have hnoiseNonneg := dotProduct_self_nonneg noiseImage
  have hbaseLow := hlow probe
  rw [← hbaseImage] at hbaseLow
  linarith [hsplit, hcrossLow, hbaseLow, hnoiseNonneg]

/-- **The κ₁ perturbed-resolvent bound, division-free**: for a symmetric base
whose form expands (all eigenvalue magnitudes ≥ 1 — the indefinite `(2,1)`
cap qualifies) and is capped by `β`, under symmetric entrywise-`δ` noise with
`δn(β+1) < 1`, the quadratic form of the resolvent difference obeys

`(1 − δn(β+1)) · ⟨x, (Ã⁻¹ − B⁻¹)x⟩² ≤ δ²n²·⟨x,x⟩²`.

This is the artifact's `‖B̃⁻¹ − B⁻¹‖ ≤ κ₁` with the Neumann series replaced
by coercivity of the perturbed gate. -/
theorem resolvent_perturbation_bound
    {base noise : Matrix (Fin n) (Fin n) ℝ} {entryBound formCap : ℝ}
    (hbaseSym : baseᵀ = base) (hnoiseSym : noiseᵀ = noise)
    (hentryNonneg : 0 ≤ entryBound) (hcapNonneg : 0 ≤ formCap)
    (hlow : ∀ probe : Fin n → ℝ,
      probe ⬝ᵥ probe ≤ (base *ᵥ probe) ⬝ᵥ (base *ᵥ probe))
    (hhigh : ∀ probe : Fin n → ℝ,
      (base *ᵥ probe) ⬝ᵥ (base *ᵥ probe) ≤ formCap * (probe ⬝ᵥ probe))
    (hnoise : ∀ i j, |noise i j| ≤ entryBound)
    (hsmall : entryBound * n * (formCap + 1) < 1) :
    ∀ probe : Fin n → ℝ,
      (1 - entryBound * n * (formCap + 1))
          * (probe ⬝ᵥ (((base + noise)⁻¹ - base⁻¹) *ᵥ probe)) ^ 2
        ≤ entryBound ^ 2 * n ^ 2 * (probe ⬝ᵥ probe) ^ 2 := by
  intro probe
  set formFloor := 1 - entryBound * n * (formCap + 1) with hformFloor
  have hfloorPos : 0 < formFloor := by rw [hformFloor]; linarith
  have hcoercive := perturbed_expansion hentryNonneg hcapNonneg hlow hhigh
    hnoise
  have hbaseCoercive : ∀ x : Fin n → ℝ,
      (1 : ℝ) * (x ⬝ᵥ x) ≤ (base *ᵥ x) ⬝ᵥ (base *ᵥ x) := by
    intro x; rw [one_mul]; exact hlow x
  have hbaseDet : IsUnit base.det :=
    coercive_isUnit_det one_pos hbaseCoercive
  have hpertDet : IsUnit (base + noise).det :=
    coercive_isUnit_det hfloorPos (fun x => hcoercive x)
  -- the resolvent difference is the sandwiched noise
  have hdiff : (base + noise)⁻¹ - base⁻¹
      = -((base + noise)⁻¹ * noise * base⁻¹) := by
    rw [resolvent_difference hpertDet hbaseDet]
    have hsandwich : base - (base + noise) = -noise := by abel
    rw [hsandwich, Matrix.mul_neg, Matrix.neg_mul]
  -- the quadratic form value, transposed onto the two inverse images
  set pertImage := (base + noise)⁻¹ *ᵥ probe with hpertImage
  set baseImage := base⁻¹ *ᵥ probe with hbaseImage
  have hpertSym : ((base + noise)⁻¹)ᵀ = (base + noise)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_add, hbaseSym,
      hnoiseSym]
  have hvalue : probe ⬝ᵥ (((base + noise)⁻¹ - base⁻¹) *ᵥ probe)
      = -(pertImage ⬝ᵥ (noise *ᵥ baseImage)) := by
    rw [hdiff, Matrix.neg_mulVec, dotProduct_neg, neg_inj,
      Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← dotProduct_mulVec_transpose, hpertSym, ← hpertImage, ← hbaseImage]
  -- Cauchy–Schwarz through the noise, then both inverse contractions
  have hsq : (probe ⬝ᵥ (((base + noise)⁻¹ - base⁻¹) *ᵥ probe)) ^ 2
      ≤ (pertImage ⬝ᵥ pertImage)
        * (entryBound ^ 2 * n ^ 2 * (baseImage ⬝ᵥ baseImage)) := by
    rw [hvalue, neg_sq]
    calc (pertImage ⬝ᵥ (noise *ᵥ baseImage)) ^ 2
        ≤ (pertImage ⬝ᵥ pertImage)
            * ((noise *ᵥ baseImage) ⬝ᵥ (noise *ᵥ baseImage)) :=
          dotProduct_sq_le_mul _ _
      _ ≤ (pertImage ⬝ᵥ pertImage)
            * (entryBound ^ 2 * n ^ 2 * (baseImage ⬝ᵥ baseImage)) :=
          mul_le_mul_of_nonneg_left (noise_mulVec_sq_le hnoise baseImage)
            (dotProduct_self_nonneg _)
  have hpertContr := inverse_contraction_of_coercive hfloorPos
    (fun x => hcoercive x) probe
  have hbaseContr : baseImage ⬝ᵥ baseImage ≤ probe ⬝ᵥ probe := by
    have hchain := inverse_contraction_of_coercive one_pos hbaseCoercive probe
    rwa [one_mul] at hchain
  -- assemble, division-free
  have hpertNonneg := dotProduct_self_nonneg pertImage
  have hbaseNonneg := dotProduct_self_nonneg baseImage
  have hprobeNonneg := dotProduct_self_nonneg probe
  calc formFloor * (probe ⬝ᵥ (((base + noise)⁻¹ - base⁻¹) *ᵥ probe)) ^ 2
      ≤ formFloor * ((pertImage ⬝ᵥ pertImage)
          * (entryBound ^ 2 * n ^ 2 * (baseImage ⬝ᵥ baseImage))) :=
        mul_le_mul_of_nonneg_left hsq hfloorPos.le
    _ = (formFloor * (pertImage ⬝ᵥ pertImage))
          * (entryBound ^ 2 * n ^ 2 * (baseImage ⬝ᵥ baseImage)) := by ring
    _ ≤ (probe ⬝ᵥ probe)
          * (entryBound ^ 2 * n ^ 2 * (baseImage ⬝ᵥ baseImage)) := by
        rw [← hpertImage] at hpertContr
        exact mul_le_mul_of_nonneg_right hpertContr
          (mul_nonneg (mul_nonneg (sq_nonneg entryBound) (sq_nonneg _))
            hbaseNonneg)
    _ ≤ (probe ⬝ᵥ probe)
          * (entryBound ^ 2 * n ^ 2 * (probe ⬝ᵥ probe)) := by
        refine mul_le_mul_of_nonneg_left ?_ hprobeNonneg
        exact mul_le_mul_of_nonneg_left hbaseContr (by positivity)
    _ = entryBound ^ 2 * n ^ 2 * (probe ⬝ᵥ probe) ^ 2 := by ring

end Gtz
