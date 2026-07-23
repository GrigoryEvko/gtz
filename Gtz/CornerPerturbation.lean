/-
# The κ₁ bound at the corner cap: the abstract brick instantiated

`ResolventPerturbation` proved the norm-free perturbed-resolvent bound for any
symmetric base whose form expands (`|Bx|² ≥ |x|²`) and is capped. Here the
corner cap `B = r·I − uuᵀ − vvᵀ` (Gram `⟨u,u⟩ = ⟨v,v⟩ = r`, `⟨u,v⟩ = −1` — the
signature-`(k−1,1)` gate of Theorem A's chain) is shown to satisfy both:

* `|Bx|²` evaluates exactly to `r²|x|² − r(a² + b²) − 2ab` in the frame
  coordinates `a = ⟨u,x⟩`, `b = ⟨v,x⟩`;
* **the expansion `B² ⪰ I`** — every eigenvalue magnitude is at least one —
  via the Gram-projection witness `|(r²−1)x − (ra+b)u − (a+rb)v|² ≥ 0`, whose
  expansion is exactly `(r²−1)·[(r²−1)|x|² − r(a²+b²) − 2ab]`; and
* the cap `|Bx|² ≤ r²|x|²` (the cross term absorbs through `(a+b)² ≥ 0`).

The assembled `corner_resolvent_perturbation` is the artifact's
`‖B̃⁻¹ − B⁻¹‖ ≤ κ₁` at the corner with explicit constants: at `(6,3)`
(`r = k = 3`, `β = 9`) the bound reads `κ₁² ≤ δ²n²/(1 − 10δn)` for entrywise
noise `δ` — coarser than the artifact's structural `2δ₁/(1−2δ₁)` by the
generic entrywise-to-operator factor, and fully kernel-checked.
-/
import Mathlib
import Gtz.CornerResolvent
import Gtz.ResolventPerturbation

namespace Gtz

open Matrix

variable {k : ℕ}

/-- The corner cap acts as `r·x − ⟨u,x⟩·u − ⟨v,x⟩·v`. -/
theorem corner_cap_mulVec (rank : ℝ) (gateFirst gateSecond probe : Fin k → ℝ) :
    (rank • 1 - atomMatrix gateFirst - atomMatrix gateSecond) *ᵥ probe
      = rank • probe - (gateFirst ⬝ᵥ probe) • gateFirst
        - (gateSecond ⬝ᵥ probe) • gateSecond := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, atomMatrix, atomMatrix, vecMulVec_mulVec_general,
    vecMulVec_mulVec_general]

/-- The corner cap is symmetric. -/
theorem corner_cap_transpose (rank : ℝ) (gateFirst gateSecond : Fin k → ℝ) :
    (rank • 1 - atomMatrix gateFirst - atomMatrix gateSecond)ᵀ
      = rank • 1 - atomMatrix gateFirst - atomMatrix gateSecond := by
  rw [Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix gateFirst).1,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix gateSecond).1]

/-- **The cap's squared form in frame coordinates**:
`|Bx|² = r²|x|² − r(a² + b²) − 2ab`. -/
theorem corner_cap_form_sq {rank : ℝ} {gateFirst gateSecond : Fin k → ℝ}
    (hfirst : gateFirst ⬝ᵥ gateFirst = rank)
    (hsecond : gateSecond ⬝ᵥ gateSecond = rank)
    (hcross : gateFirst ⬝ᵥ gateSecond = -1) (probe : Fin k → ℝ) :
    ((rank • 1 - atomMatrix gateFirst - atomMatrix gateSecond) *ᵥ probe)
        ⬝ᵥ ((rank • 1 - atomMatrix gateFirst - atomMatrix gateSecond) *ᵥ probe)
      = rank ^ 2 * (probe ⬝ᵥ probe)
        - rank * ((gateFirst ⬝ᵥ probe) ^ 2 + (gateSecond ⬝ᵥ probe) ^ 2)
        - 2 * (gateFirst ⬝ᵥ probe) * (gateSecond ⬝ᵥ probe) := by
  rw [corner_cap_mulVec]
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  rw [hfirst, hsecond, hcross, dotProduct_comm gateSecond gateFirst, hcross,
    dotProduct_comm probe gateFirst, dotProduct_comm probe gateSecond]
  ring

/-- **The corner cap expands, `B² ⪰ I`**: for `r > 1` every probe satisfies
`|x|² ≤ |Bx|²` — the Gram-projection witness
`|(r²−1)x − (ra+b)u − (a+rb)v|² ≥ 0` carries the whole bound. -/
theorem corner_cap_expansion {rank : ℝ} {gateFirst gateSecond : Fin k → ℝ}
    (hrankGt : 1 < rank)
    (hfirst : gateFirst ⬝ᵥ gateFirst = rank)
    (hsecond : gateSecond ⬝ᵥ gateSecond = rank)
    (hcross : gateFirst ⬝ᵥ gateSecond = -1) (probe : Fin k → ℝ) :
    probe ⬝ᵥ probe
      ≤ ((rank • 1 - atomMatrix gateFirst - atomMatrix gateSecond) *ᵥ probe)
        ⬝ᵥ ((rank • 1 - atomMatrix gateFirst
          - atomMatrix gateSecond) *ᵥ probe) := by
  rw [corner_cap_form_sq hfirst hsecond hcross]
  have hwitness := dotProduct_self_nonneg
    ((rank ^ 2 - 1) • probe
      - (rank * (gateFirst ⬝ᵥ probe) + gateSecond ⬝ᵥ probe) • gateFirst
      - (gateFirst ⬝ᵥ probe + rank * (gateSecond ⬝ᵥ probe)) • gateSecond)
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul] at hwitness
  rw [hfirst, hsecond, hcross, dotProduct_comm gateSecond gateFirst, hcross,
    dotProduct_comm probe gateFirst, dotProduct_comm probe gateSecond]
    at hwitness
  have hgap : 0 < rank ^ 2 - 1 := by nlinarith [hrankGt]
  nlinarith [hwitness, hgap]

/-- **The corner cap is bounded, `|Bx|² ≤ r²|x|²`**: the subtracted terms are
nonnegative for `r ≥ 1` since `r(a²+b²) + 2ab ≥ (a+b)² ≥ 0`. -/
theorem corner_cap_form_le {rank : ℝ} {gateFirst gateSecond : Fin k → ℝ}
    (hrankOne : 1 ≤ rank)
    (hfirst : gateFirst ⬝ᵥ gateFirst = rank)
    (hsecond : gateSecond ⬝ᵥ gateSecond = rank)
    (hcross : gateFirst ⬝ᵥ gateSecond = -1) (probe : Fin k → ℝ) :
    ((rank • 1 - atomMatrix gateFirst - atomMatrix gateSecond) *ᵥ probe)
        ⬝ᵥ ((rank • 1 - atomMatrix gateFirst
          - atomMatrix gateSecond) *ᵥ probe)
      ≤ rank ^ 2 * (probe ⬝ᵥ probe) := by
  rw [corner_cap_form_sq hfirst hsecond hcross]
  have habsorb : (0 : ℝ)
      ≤ (rank - 1) * ((gateFirst ⬝ᵥ probe) ^ 2 + (gateSecond ⬝ᵥ probe) ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [sq_nonneg (gateFirst ⬝ᵥ probe + gateSecond ⬝ᵥ probe), habsorb]

/-- **The κ₁ bound at the corner**: entrywise-`δ` symmetric noise on the
corner cap obeys the division-free perturbed-resolvent bound with
`β = rank²` — the kernel-checked cap error of Theorem A's off-corner chain. -/
theorem corner_resolvent_perturbation {rank : ℝ}
    {gateFirst gateSecond : Fin k → ℝ}
    {noise : Matrix (Fin k) (Fin k) ℝ} {entryBound : ℝ}
    (hrankGt : 1 < rank)
    (hfirst : gateFirst ⬝ᵥ gateFirst = rank)
    (hsecond : gateSecond ⬝ᵥ gateSecond = rank)
    (hcross : gateFirst ⬝ᵥ gateSecond = -1)
    (hnoiseSym : noiseᵀ = noise)
    (hentryNonneg : 0 ≤ entryBound)
    (hnoise : ∀ i j, |noise i j| ≤ entryBound)
    (hsmall : entryBound * k * (rank ^ 2 + 1) < 1) :
    ∀ probe : Fin k → ℝ,
      (1 - entryBound * k * (rank ^ 2 + 1))
          * (probe ⬝ᵥ ((((rank • 1 - atomMatrix gateFirst
              - atomMatrix gateSecond) + noise)⁻¹
            - (rank • 1 - atomMatrix gateFirst
              - atomMatrix gateSecond)⁻¹) *ᵥ probe)) ^ 2
        ≤ entryBound ^ 2 * k ^ 2 * (probe ⬝ᵥ probe) ^ 2 :=
  resolvent_perturbation_bound
    (corner_cap_transpose rank gateFirst gateSecond) hnoiseSym
    hentryNonneg (sq_nonneg rank)
    (corner_cap_expansion hrankGt hfirst hsecond hcross)
    (corner_cap_form_le hrankGt.le hfirst hsecond hcross)
    hnoise hsmall

end Gtz
