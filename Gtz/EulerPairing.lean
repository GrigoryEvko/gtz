/-
# The global Euler pairing

The certificate frame's sign-fixing identity. Pairing every atom's stress
equation with its own square and summing telescopes through the design
equations to the constant `2`; symmetrizing the double sum converts each
edge's two contributions into the kernel-checked per-edge value `2(σ_e + 1)`.
The result:

  `Σ_{c,d} λ_cd·(σ_cd + 1) = 2`,

and on a certificate supported on tight pairs (`σ = 0` wherever `λ ≠ 0`) the
stress mass is pinned: `Σ_{c,d} λ_cd = 2` — ordered count, so `Σ_e λ_e = 1`
over unordered edges. This is what forces the Gordan certificate's `β` to be
positive and normalizes the focal conic; no equality design can carry a
certificate of zero or negative stress mass.
-/
import Mathlib
import Gtz.Pushoff
import Gtz.StressFrame

namespace Gtz

variable {m : ℕ}

/-- The pair slack of two squares, in the platform's normalization. -/
noncomputable def slackOf (square : Fin m → Fin 2 → ℝ) (c d : Fin m) : ℝ :=
  (planarNorm (square c) + planarNorm (square d)
    - planarNorm (square c + square d)) / 2 - 1

/-- **The global Euler pairing**: a stress system over the design pairs to
`Σ λ·(σ + 1) = 2` through the design equations. -/
theorem euler_pairing_global
    (weight : Fin m → ℝ) (square : Fin m → Fin 2 → ℝ)
    (lambda : Fin m → Fin m → ℝ) (moment : Fin 2 → ℝ)
    (hlevPos : ∀ c, planarNorm (square c) ≠ 0)
    (hchordPos : ∀ c d, lambda c d ≠ 0
      → planarNorm (square c + square d) ≠ 0)
    (hsym : ∀ c d, lambda c d = lambda d c)
    (hdiagFree : ∀ c, lambda c c = 0)
    (hstress : ∀ c, ∑ d, lambda c d
        • ((planarNorm (square c))⁻¹ • square c
          - (planarNorm (square c + square d))⁻¹ • (square c + square d))
      = weight c • ((planarNorm (square c))⁻¹ • square c
          - (2 : ℝ) • moment))
    (htrace : ∑ c, weight c * planarNorm (square c) = 2)
    (hclosure : ∑ c, weight c • square c = 0) :
    ∑ c, ∑ d, lambda c d * (slackOf square c d + 1) = 2 := by
  -- pair each atom's stress equation with its own square
  have hpaired : ∀ c, ∑ d, lambda c d
      * (((planarNorm (square c))⁻¹ • square c
          - (planarNorm (square c + square d))⁻¹ • (square c + square d))
        ⬝ᵥ square c)
      = weight c * (planarNorm (square c) - 2 * (moment ⬝ᵥ square c)) := by
    intro c
    have happly := congrArg (fun planarVec => planarVec ⬝ᵥ square c)
      (hstress c)
    simp only [smul_dotProduct, smul_eq_mul, sub_dotProduct]
    simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, sub_dotProduct]
      at happly
    rw [happly]
    -- the self-pairing of the unit direction is the leverage
    have hself : (planarNorm (square c))⁻¹ * (square c ⬝ᵥ square c)
        = planarNorm (square c) := by
      rw [← planarNorm_sq (square c), pow_two]
      field_simp
    rw [hself]
  -- summing the paired equations telescopes through the design equations
  have hsumPaired : ∑ c, ∑ d, lambda c d
      * (((planarNorm (square c))⁻¹ • square c
          - (planarNorm (square c + square d))⁻¹ • (square c + square d))
        ⬝ᵥ square c) = 2 := by
    rw [Finset.sum_congr rfl fun c _ => hpaired c]
    have hmomentSum : ∑ c, weight c * (moment ⬝ᵥ square c)
        = moment ⬝ᵥ (∑ c, weight c • square c) := by
      rw [dotProduct_sum]
      exact Finset.sum_congr rfl fun c _ => by
        rw [dotProduct_smul, smul_eq_mul]
    have hexpand : ∑ c, weight c
        * (planarNorm (square c) - 2 * (moment ⬝ᵥ square c))
        = (∑ c, weight c * planarNorm (square c))
          - 2 * ∑ c, weight c * (moment ⬝ᵥ square c) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [hexpand, hmomentSum, hclosure, dotProduct_zero, htrace]
    ring
  -- symmetrize: each unordered pair contributes the per-edge pairing value
  have hsymmetrize : ∑ c, ∑ d, lambda c d
      * (((planarNorm (square c))⁻¹ • square c
          - (planarNorm (square c + square d))⁻¹ • (square c + square d))
        ⬝ᵥ square c)
      = ∑ c, ∑ d, lambda c d * (slackOf square c d + 1) := by
    -- double both sides and pair the (c,d)/(d,c) contributions
    have hdouble : (2 : ℝ) * ∑ c, ∑ d, lambda c d
        * (((planarNorm (square c))⁻¹ • square c
            - (planarNorm (square c + square d))⁻¹ • (square c + square d))
          ⬝ᵥ square c)
        = ∑ c, ∑ d, lambda c d
          * ((((planarNorm (square c))⁻¹ • square c
              - (planarNorm (square c + square d))⁻¹
                • (square c + square d)) ⬝ᵥ square c)
            + (((planarNorm (square d))⁻¹ • square d
              - (planarNorm (square d + square c))⁻¹
                • (square d + square c)) ⬝ᵥ square d)) := by
      rw [two_mul]
      nth_rewrite 2 [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hsym d c]
      ring
    have hedgeValue : ∀ c d, lambda c d
        * ((((planarNorm (square c))⁻¹ • square c
            - (planarNorm (square c + square d))⁻¹
              • (square c + square d)) ⬝ᵥ square c)
          + (((planarNorm (square d))⁻¹ • square d
            - (planarNorm (square d + square c))⁻¹
              • (square d + square c)) ⬝ᵥ square d))
        = lambda c d * (2 * (slackOf square c d + 1)) := by
      intro c d
      rcases eq_or_ne (lambda c d) 0 with hzero | hsupported
      · rw [hzero, zero_mul, zero_mul]
      · have hchord := hchordPos c d hsupported
        have hchordComm : square d + square c = square c + square d := by
          rw [add_comm]
        rw [hchordComm]
        have hedge := edge_pairing_eq_slack (square c) (square d)
          (hlevPos c) (hlevPos d) hchord
        rw [slackOf, hedge]
    have hdoubled : (2 : ℝ) * ∑ c, ∑ d, lambda c d
        * (((planarNorm (square c))⁻¹ • square c
            - (planarNorm (square c + square d))⁻¹ • (square c + square d))
          ⬝ᵥ square c)
        = 2 * ∑ c, ∑ d, lambda c d * (slackOf square c d + 1) := by
      rw [hdouble]
      rw [Finset.sum_congr rfl fun c _ =>
        Finset.sum_congr rfl fun d _ => hedgeValue c d]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    linarith [hdoubled]
  rw [← hsymmetrize]
  exact hsumPaired

/-- **The stress mass is pinned**: a certificate supported on tight pairs has
`Σ_{c,d} λ_cd = 2` — the Euler pairing with every slack zero. No equality
design carries a certificate of zero stress mass. -/
theorem stress_mass_pinned
    (weight : Fin m → ℝ) (square : Fin m → Fin 2 → ℝ)
    (lambda : Fin m → Fin m → ℝ) (moment : Fin 2 → ℝ)
    (hlevPos : ∀ c, planarNorm (square c) ≠ 0)
    (hchordPos : ∀ c d, lambda c d ≠ 0
      → planarNorm (square c + square d) ≠ 0)
    (hsym : ∀ c d, lambda c d = lambda d c)
    (hdiagFree : ∀ c, lambda c c = 0)
    (hstress : ∀ c, ∑ d, lambda c d
        • ((planarNorm (square c))⁻¹ • square c
          - (planarNorm (square c + square d))⁻¹ • (square c + square d))
      = weight c • ((planarNorm (square c))⁻¹ • square c
          - (2 : ℝ) • moment))
    (htrace : ∑ c, weight c * planarNorm (square c) = 2)
    (hclosure : ∑ c, weight c • square c = 0)
    (htight : ∀ c d, lambda c d ≠ 0 → slackOf square c d = 0) :
    ∑ c, ∑ d, lambda c d = 2 := by
  have hpairing := euler_pairing_global weight square lambda moment hlevPos
    hchordPos hsym hdiagFree hstress htrace hclosure
  have hterms : ∀ c d, lambda c d * (slackOf square c d + 1)
      = lambda c d := by
    intro c d
    rcases eq_or_ne (lambda c d) 0 with hzero | hsupported
    · rw [hzero, zero_mul]
    · rw [htight c d hsupported, zero_add, mul_one]
  rw [Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => hterms c d] at hpairing
  exact hpairing

end Gtz
