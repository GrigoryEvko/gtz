/-
# The corner resolvent and the covering functional

The middle of the off-window chain: at the exact corner the cap base of the
gate omitting the pair `{i,j}` is `B = k·I − h_ih_iᵀ − h_jh_jᵀ`, and its
inverse is rank-two-corrected identity

  `B⁻¹ = (I + h_ih_jᵀ + h_jh_iᵀ)/k`,

verified by one multiplication in the operator algebra of the simplex frame —
the six cross terms cancel in pairs. The normal form follows: the cap depth of
a probe is `(|u|² + 2·x_i x_j)/k` with `x = h·u`, so the best cap over the
gates is the MINIMUM PAIRWISE PRODUCT on the zero-sum sphere. Feeding the
kernel-checked Bhatia–Davis floor (`exists_pair_mul_le_neg_one`) through this
resolvent yields the covering theorem: **at the corner, every unit direction
is caught by some gate at depth at most `−1/k`** — the quantitative anchor of
the off-window fire, at every rank, with no eigenvalue ever computed.
-/
import Mathlib
import Gtz.Basic
import Gtz.BhatiaDavis
import Gtz.CornerFiber

namespace Gtz

open Matrix

variable {k : ℕ}

/-! ### The operator algebra -/

/-- The product of two rank-one operators contracts through the middle. -/
theorem vecMulVec_mul_vecMulVec (leftVec innerLeft innerRight rightVec :
    Fin k → ℝ) :
    Matrix.vecMulVec leftVec innerLeft * Matrix.vecMulVec innerRight rightVec
      = (innerLeft ⬝ᵥ innerRight) • Matrix.vecMulVec leftVec rightVec := by
  ext rowIndex colIndex
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
    smul_eq_mul, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Rank-one action on a vector. -/
theorem vecMulVec_mulVec_general (leftVec rightVec probe : Fin k → ℝ) :
    Matrix.vecMulVec leftVec rightVec *ᵥ probe
      = (rightVec ⬝ᵥ probe) • leftVec := by
  ext rowIndex
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-! ### The resolvent -/

/-- **The corner cap multiplies to the scalar**: with `⟨u,u⟩ = ⟨v,v⟩ = r` and
`⟨u,v⟩ = −1`, the product `(r·I − uuᵀ − vvᵀ)(I + uvᵀ + vuᵀ)` collapses to
`r·I` — the six cross terms cancel in pairs. -/
theorem corner_cap_mul {rank : ℝ} {gateFirst gateSecond : Fin k → ℝ}
    (hfirst : gateFirst ⬝ᵥ gateFirst = rank)
    (hsecond : gateSecond ⬝ᵥ gateSecond = rank)
    (hcross : gateFirst ⬝ᵥ gateSecond = -1) :
    (rank • 1 - atomMatrix gateFirst - atomMatrix gateSecond)
        * (1 + Matrix.vecMulVec gateFirst gateSecond
          + Matrix.vecMulVec gateSecond gateFirst)
      = rank • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hcross' : gateSecond ⬝ᵥ gateFirst = -1 := by
    rw [dotProduct_comm]; exact hcross
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_one, atomMatrix, vecMulVec_mul_vecMulVec, hfirst, hsecond,
    hcross, hcross']
  module

/-- **The corner resolvent**: `B⁻¹ = (I + uvᵀ + vuᵀ)/r`. -/
theorem corner_cap_inv {rank : ℝ} {gateFirst gateSecond : Fin k → ℝ}
    (hrank : rank ≠ 0)
    (hfirst : gateFirst ⬝ᵥ gateFirst = rank)
    (hsecond : gateSecond ⬝ᵥ gateSecond = rank)
    (hcross : gateFirst ⬝ᵥ gateSecond = -1) :
    (rank • 1 - atomMatrix gateFirst - atomMatrix gateSecond)⁻¹
      = rank⁻¹ • (1 + Matrix.vecMulVec gateFirst gateSecond
        + Matrix.vecMulVec gateSecond gateFirst) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_smul, corner_cap_mul hfirst hsecond hcross, smul_smul,
    inv_mul_cancel₀ hrank, one_smul]

/-- **The normal form**: the cap depth of a probe against the corner gate is
`(|u|² + 2·x_i·x_j)/r` in the frame coordinates `x = h·u`. -/
theorem corner_normal_form {rank : ℝ} {gateFirst gateSecond : Fin k → ℝ}
    (hrank : rank ≠ 0)
    (hfirst : gateFirst ⬝ᵥ gateFirst = rank)
    (hsecond : gateSecond ⬝ᵥ gateSecond = rank)
    (hcross : gateFirst ⬝ᵥ gateSecond = -1) (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((rank • 1 - atomMatrix gateFirst - atomMatrix gateSecond)⁻¹
        *ᵥ probe)
      = (probe ⬝ᵥ probe
        + 2 * (gateFirst ⬝ᵥ probe) * (gateSecond ⬝ᵥ probe)) / rank := by
  rw [corner_cap_inv hrank hfirst hsecond hcross, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.add_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, vecMulVec_mulVec_general, vecMulVec_mulVec_general,
    dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, dotProduct_comm probe gateFirst,
    dotProduct_comm probe gateSecond]
  field_simp
  ring

/-! ### The covering theorem -/

/-- **The corner covering**: at the exact simplex corner, every unit probe is
caught by some gate at depth at most `−1/k` — the Bhatia–Davis floor read
through the resolvent. This is the quantitative anchor of the off-window fire
at every rank. -/
theorem corner_covering (hk : 1 ≤ k)
    (simplex : Fin (k + 1) → (Fin k → ℝ))
    (hdiag : ∀ i, simplex i ⬝ᵥ simplex i = (k : ℝ))
    (hoff : ∀ i j, i ≠ j → simplex i ⬝ᵥ simplex j = -1)
    (probe : Fin k → ℝ) (hprobe : probe ⬝ᵥ probe = 1) :
    ∃ gateFirst gateSecond, gateFirst ≠ gateSecond
      ∧ probe ⬝ᵥ (((k : ℝ) • 1 - atomMatrix (simplex gateFirst)
          - atomMatrix (simplex gateSecond))⁻¹ *ᵥ probe)
        ≤ -(1 / k) := by
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  -- frame coordinates of the probe
  set coords := fun c => simplex c ⬝ᵥ probe with hcoords
  have hsumZero : ∑ c, coords c = 0 := by
    have hvecs := simplex_sum_eq_zero simplex hdiag hoff
    calc ∑ c, coords c = (∑ c, simplex c) ⬝ᵥ probe := by
          rw [sum_dotProduct]
      _ = 0 := by rw [hvecs, zero_dotProduct]
  have hsumSq : ∑ c, coords c ^ 2 = ((k + 1 : ℕ) : ℝ) := by
    have hframe := simplex_frame_operator simplex hdiag hoff
    have hpaired := congrArg (fun M => probe ⬝ᵥ (M *ᵥ probe)) hframe
    simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hpaired
    have hterms : ∀ c, probe ⬝ᵥ (atomMatrix (simplex c) *ᵥ probe)
        = coords c ^ 2 := by
      intro c
      rw [atomMatrix, vecMulVec_mulVec_general, dotProduct_smul, smul_eq_mul,
        dotProduct_comm probe (simplex c), hcoords]
      ring
    rw [Finset.sum_congr rfl fun c _ => hterms c] at hpaired
    rw [hpaired, hprobe]
    push_cast
    ring
  -- the Bhatia–Davis pair
  obtain ⟨gateFirst, gateSecond, hne, _, _, hproduct⟩ :=
    exists_extremal_pair (n := k + 1) (by omega) coords hsumZero hsumSq
  refine ⟨gateFirst, gateSecond, hne, ?_⟩
  have hneSimplex : simplex gateFirst ⬝ᵥ simplex gateSecond = -1 :=
    hoff gateFirst gateSecond hne
  rw [corner_normal_form (ne_of_gt hkPos) (hdiag gateFirst)
    (hdiag gateSecond) hneSimplex probe, hprobe]
  -- (1 + 2·x_i·x_j)/k ≤ −1/k because x_i·x_j ≤ −1
  rw [div_le_iff₀ hkPos]
  have hexpand : -(1 / (k : ℝ)) * k = -1 := by
    field_simp
  rw [hexpand]
  have hpair := hproduct
  nlinarith [hpair]

/-- **Every heavy extra is caught at the corner**: an extra atom of leverage at
least `k` has cap value at most `−1` against some gate — the fire threshold of
the cap criterion, met with the exact corner's own geometry. This is the
per-extra cap fact of Theorem B_k's deformed program, now quantitative. -/
theorem corner_extra_caught (hk : 1 ≤ k)
    (simplex : Fin (k + 1) → (Fin k → ℝ))
    (hdiag : ∀ i, simplex i ⬝ᵥ simplex i = (k : ℝ))
    (hoff : ∀ i j, i ≠ j → simplex i ⬝ᵥ simplex j = -1)
    (extra : Fin k → ℝ) (hheavy : (k : ℝ) ≤ extra ⬝ᵥ extra) :
    ∃ gateFirst gateSecond, gateFirst ≠ gateSecond
      ∧ extra ⬝ᵥ (((k : ℝ) • 1 - atomMatrix (simplex gateFirst)
          - atomMatrix (simplex gateSecond))⁻¹ *ᵥ extra)
        ≤ -1 := by
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  have hlevPos : 0 < extra ⬝ᵥ extra := lt_of_lt_of_le hkPos hheavy
  set lev := extra ⬝ᵥ extra with hlev
  set scale := Real.sqrt lev with hscale
  have hscalePos : 0 < scale := Real.sqrt_pos.mpr hlevPos
  have hscaleSq : scale * scale = lev := Real.mul_self_sqrt hlevPos.le
  set unit := scale⁻¹ • extra with hunit
  have hunitNorm : unit ⬝ᵥ unit = 1 := by
    rw [hunit, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← hlev]
    field_simp
    rw [← hscaleSq]
    ring
  obtain ⟨gateFirst, gateSecond, hne, hdepth⟩ :=
    corner_covering hk simplex hdiag hoff unit hunitNorm
  refine ⟨gateFirst, gateSecond, hne, ?_⟩
  -- the quadratic form scales by the leverage
  have hrewrite : extra = scale • unit := by
    rw [hunit, smul_smul, mul_inv_cancel₀ (ne_of_gt hscalePos), one_smul]
  have hform : extra ⬝ᵥ (((k : ℝ) • 1 - atomMatrix (simplex gateFirst)
      - atomMatrix (simplex gateSecond))⁻¹ *ᵥ extra)
      = lev * (unit ⬝ᵥ (((k : ℝ) • 1 - atomMatrix (simplex gateFirst)
        - atomMatrix (simplex gateSecond))⁻¹ *ᵥ unit)) := by
    rw [hrewrite, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, ← mul_assoc, hscaleSq]
  rw [hform]
  -- lev · depth ≤ lev · (−1/k) ≤ −1
  have hstep : lev * (unit ⬝ᵥ (((k : ℝ) • 1 - atomMatrix (simplex gateFirst)
      - atomMatrix (simplex gateSecond))⁻¹ *ᵥ unit))
      ≤ lev * (-(1 / k)) :=
    mul_le_mul_of_nonneg_left hdepth hlevPos.le
  have hthreshold : lev * (-(1 / k)) ≤ -1 := by
    rw [div_eq_inv_mul, mul_one]
    have hratio : (k : ℝ) * (k : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hkPos)
    nlinarith [hheavy, hkPos, hratio]
  linarith

/-- **The cap base's negative direction**: the difference of the two omitted
simplex vectors is an exact `−1`-eigenvector of the gate cap base, with form
value `−(2k+2)`. This is the witness the de-spectralized cap criterion's
signature pair consumes — produced by Gram algebra, not by a spectrum. -/
theorem corner_cap_negative_direction {gateFirst gateSecond : Fin k → ℝ}
    (hfirst : gateFirst ⬝ᵥ gateFirst = (k : ℝ))
    (hsecond : gateSecond ⬝ᵥ gateSecond = (k : ℝ))
    (hcross : gateFirst ⬝ᵥ gateSecond = -1) :
    (gateFirst - gateSecond) ⬝ᵥ
        (((k : ℝ) • 1 - atomMatrix gateFirst - atomMatrix gateSecond)
          *ᵥ (gateFirst - gateSecond))
      = -(2 * k + 2) := by
  have hcross' : gateSecond ⬝ᵥ gateFirst = -1 := by
    rw [dotProduct_comm]; exact hcross
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    atomMatrix, vecMulVec_mulVec_general, dotProduct_sub, sub_dotProduct,
    dotProduct_smul, smul_eq_mul, hfirst, hsecond, hcross, hcross']
  ring

end Gtz
