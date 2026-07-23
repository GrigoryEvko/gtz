/-
# The splitting rule

The u-component scalar reduction of the stress system: pairing an atom's
stress equation with its own unit direction, under tightness of the supported
pairs and the focal conic, collapses to

  `Σ_{d~c} λ_cd · β_d/(β_c + β_d) = t_c`,   `β = ℓ − 1`.

The geometric content is one chord projection: on a tight pair the chord's
component along an endpoint's direction is `1 − 2β_d/((β_c+β_d)·ℓ_c)` — the
excess leverage of the OTHER endpoint, split by the joint excess. Summed
against the stress and read through the conic value `⟨ξ,u_c⟩ = ν_c − 1/2`,
the atom's weight is exactly the β-weighted stress it carries. Together with
the pinned stress mass this makes the certificate's weight bookkeeping
(`Σt = Σλ` on tight triangles) automatic rather than assumed.
-/
import Mathlib
import Gtz.Pushoff
import Gtz.EulerPairing

namespace Gtz

variable {m : ℕ}

/-! ### The chord projection under tightness -/

/-- **The chord projection**: on a tight pair (`n = ℓ_c + ℓ_d − 2`) the unit
chord's component along an endpoint's unit direction is
`1 − 2(ℓ_d − 1)/(n·ℓ_c)`. -/
theorem chord_projection_tight {firstSquare secondSquare : Fin 2 → ℝ}
    (hfirstPos : planarNorm firstSquare ≠ 0)
    (hchordPos : planarNorm (firstSquare + secondSquare) ≠ 0)
    (htight : planarNorm (firstSquare + secondSquare)
      = planarNorm firstSquare + planarNorm secondSquare - 2) :
    ((planarNorm (firstSquare + secondSquare))⁻¹
        • (firstSquare + secondSquare))
      ⬝ᵥ ((planarNorm firstSquare)⁻¹ • firstSquare)
      = 1 - 2 * (planarNorm secondSquare - 1)
        / (planarNorm (firstSquare + secondSquare) * planarNorm firstSquare) := by
  set firstLen := planarNorm firstSquare with hfirstLen
  set secondLen := planarNorm secondSquare with hsecondLen
  set chordLen := planarNorm (firstSquare + secondSquare) with hchordLen
  -- the cross Gram entry from the chord length
  have hchordSq : (firstSquare + secondSquare) ⬝ᵥ (firstSquare + secondSquare)
      = chordLen ^ 2 := (planarNorm_sq _).symm
  have hfirstSq : firstSquare ⬝ᵥ firstSquare = firstLen ^ 2 :=
    (planarNorm_sq _).symm
  have hsecondSq : secondSquare ⬝ᵥ secondSquare = secondLen ^ 2 :=
    (planarNorm_sq _).symm
  have hcross : firstSquare ⬝ᵥ secondSquare
      = (chordLen ^ 2 - firstLen ^ 2 - secondLen ^ 2) / 2 := by
    have hexpand : (firstSquare + secondSquare)
        ⬝ᵥ (firstSquare + secondSquare)
        = firstSquare ⬝ᵥ firstSquare + 2 * (firstSquare ⬝ᵥ secondSquare)
          + secondSquare ⬝ᵥ secondSquare := by
      rw [dotProduct_add, add_dotProduct, add_dotProduct,
        dotProduct_comm secondSquare firstSquare]
      ring
    rw [hexpand, hfirstSq, hsecondSq] at hchordSq
    linarith
  -- expand the projection
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    add_dotProduct, hfirstSq, dotProduct_comm secondSquare firstSquare,
    hcross]
  rw [htight] at hchordPos ⊢
  field_simp
  ring

/-! ### The splitting rule -/

/-- **The splitting rule**: an atom's stress equation, paired with its own
unit direction under tightness of the supported pairs and the focal conic,
yields `Σ_d λ_cd·β_d/(β_c + β_d) = t_c`. The certificate's weight bookkeeping
is forced, not assumed. -/
theorem splitting_rule
    (weight : Fin m → ℝ) (square : Fin m → Fin 2 → ℝ)
    (lambda : Fin m → Fin m → ℝ) (moment : Fin 2 → ℝ) (c : Fin m)
    (hlevPos : ∀ e, planarNorm (square e) ≠ 0)
    (hchordPos : ∀ d, lambda c d ≠ 0
      → planarNorm (square c + square d) ≠ 0)
    (htightSupport : ∀ d, lambda c d ≠ 0
      → planarNorm (square c + square d)
        = planarNorm (square c) + planarNorm (square d) - 2)
    (hconic : moment ⬝ᵥ ((planarNorm (square c))⁻¹ • square c)
      = 1 / 2 - 1 / planarNorm (square c))
    (hstress : ∑ d, lambda c d
        • ((planarNorm (square c))⁻¹ • square c
          - (planarNorm (square c + square d))⁻¹ • (square c + square d))
      = weight c • ((planarNorm (square c))⁻¹ • square c
          - (2 : ℝ) • moment)) :
    ∑ d, lambda c d * ((planarNorm (square d) - 1)
        / (planarNorm (square c) + planarNorm (square d) - 2))
      = weight c := by
  have hlevC := hlevPos c
  -- pair the stress equation with the atom's own unit direction
  have hpaired := congrArg
    (fun planarVec => planarVec ⬝ᵥ ((planarNorm (square c))⁻¹ • square c))
    hstress
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, sub_dotProduct]
    at hpaired
  -- the self term is one
  have hself : ((planarNorm (square c))⁻¹ • square c)
      ⬝ᵥ ((planarNorm (square c))⁻¹ • square c) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← planarNorm_sq (square c), pow_two]
    field_simp
  -- per-term: the chord projection collapses each supported summand
  have hterm : ∀ d, lambda c d
      * (((planarNorm (square c))⁻¹ • square c)
          ⬝ᵥ ((planarNorm (square c))⁻¹ • square c)
        - ((planarNorm (square c + square d))⁻¹ • (square c + square d))
          ⬝ᵥ ((planarNorm (square c))⁻¹ • square c))
      = lambda c d * (2 * ((planarNorm (square d) - 1)
          / ((planarNorm (square c) + planarNorm (square d) - 2)
            * planarNorm (square c)))) := by
    intro d
    rcases eq_or_ne (lambda c d) 0 with hzero | hsupported
    · rw [hzero, zero_mul, zero_mul]
    · rw [hself, chord_projection_tight hlevC (hchordPos d hsupported)
        (htightSupport d hsupported), htightSupport d hsupported]
      ring
  -- the conic collapses the right side
  have hright : weight c
      * (((planarNorm (square c))⁻¹ • square c)
          ⬝ᵥ ((planarNorm (square c))⁻¹ • square c)
        - (2 : ℝ) * (moment ⬝ᵥ ((planarNorm (square c))⁻¹ • square c)))
      = weight c * (2 / planarNorm (square c)) := by
    rw [hself, dotProduct_comm moment, dotProduct_comm]
    rw [hconic]
    ring
  -- assemble, then clear the common 2/ℓ_c factor
  have hassembled : ∑ d, lambda c d
      * (2 * ((planarNorm (square d) - 1)
        / ((planarNorm (square c) + planarNorm (square d) - 2)
          * planarNorm (square c))))
      = weight c * (2 / planarNorm (square c)) := by
    rw [← hright]
    rw [← Finset.sum_congr rfl fun d _ => hterm d]
    -- reshape hpaired to the summed form
    have hshape : ∑ d, lambda c d
        * (((planarNorm (square c))⁻¹ • square c)
            ⬝ᵥ ((planarNorm (square c))⁻¹ • square c)
          - ((planarNorm (square c + square d))⁻¹ • (square c + square d))
            ⬝ᵥ ((planarNorm (square c))⁻¹ • square c))
        = weight c
          * (((planarNorm (square c))⁻¹ • square c)
              ⬝ᵥ ((planarNorm (square c))⁻¹ • square c)
            - (2 : ℝ) * (moment ⬝ᵥ ((planarNorm (square c))⁻¹ • square c))) := by
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul,
        sub_dotProduct]
      simp only [dotProduct_smul, smul_eq_mul] at hpaired
      refine Eq.trans (Eq.trans
        (Finset.sum_congr rfl fun d _ => by ring) hpaired) (by ring)
    exact hshape
  -- multiply through by ℓ_c/2
  have hscale := congrArg (fun value => value * (planarNorm (square c) / 2))
    hassembled
  rw [Finset.sum_mul] at hscale
  calc ∑ d, lambda c d * ((planarNorm (square d) - 1)
        / (planarNorm (square c) + planarNorm (square d) - 2))
      = ∑ d, lambda c d
        * (2 * ((planarNorm (square d) - 1)
          / ((planarNorm (square c) + planarNorm (square d) - 2)
            * planarNorm (square c)))) * (planarNorm (square c) / 2) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        field_simp
    _ = weight c * (2 / planarNorm (square c))
        * (planarNorm (square c) / 2) := hscale
    _ = weight c := by
        field_simp

/-! ### The harmonic rule -/

/-- **The harmonic rule**: multiplying each atom's splitting rule by its
excess `β_c` and summing against the design trace pins the harmonic stress
mass, `Σ_{c,d} λ_cd·β_cβ_d/(β_c+β_d) = 1` — the certificate's second scalar
invariant, forced by weight one and trace two alone. -/
theorem harmonic_rule
    (weight : Fin m → ℝ) (square : Fin m → Fin 2 → ℝ)
    (lambda : Fin m → Fin m → ℝ) (moment : Fin 2 → ℝ)
    (hlevPos : ∀ e, planarNorm (square e) ≠ 0)
    (hchordPos : ∀ c d, lambda c d ≠ 0
      → planarNorm (square c + square d) ≠ 0)
    (htightSupport : ∀ c d, lambda c d ≠ 0
      → planarNorm (square c + square d)
        = planarNorm (square c) + planarNorm (square d) - 2)
    (hconic : ∀ c, moment ⬝ᵥ ((planarNorm (square c))⁻¹ • square c)
      = 1 / 2 - 1 / planarNorm (square c))
    (hstress : ∀ c, ∑ d, lambda c d
        • ((planarNorm (square c))⁻¹ • square c
          - (planarNorm (square c + square d))⁻¹ • (square c + square d))
      = weight c • ((planarNorm (square c))⁻¹ • square c
          - (2 : ℝ) • moment))
    (hweightSum : ∑ c, weight c = 1)
    (htrace : ∑ c, weight c * planarNorm (square c) = 2) :
    ∑ c, ∑ d, lambda c d
        * ((planarNorm (square c) - 1) * (planarNorm (square d) - 1)
          / (planarNorm (square c) + planarNorm (square d) - 2))
      = 1 := by
  -- each atom's splitting rule, scaled by its excess
  have hscaled : ∀ c, ∑ d, lambda c d
      * ((planarNorm (square c) - 1) * (planarNorm (square d) - 1)
        / (planarNorm (square c) + planarNorm (square d) - 2))
      = (planarNorm (square c) - 1) * weight c := by
    intro c
    have hsplit := splitting_rule weight square lambda moment c hlevPos
      (fun d => hchordPos c d) (fun d => htightSupport c d) (hconic c)
      (hstress c)
    calc ∑ d, lambda c d
        * ((planarNorm (square c) - 1) * (planarNorm (square d) - 1)
          / (planarNorm (square c) + planarNorm (square d) - 2))
        = (planarNorm (square c) - 1) * ∑ d, lambda c d
          * ((planarNorm (square d) - 1)
            / (planarNorm (square c) + planarNorm (square d) - 2)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun d _ => by ring
      _ = (planarNorm (square c) - 1) * weight c := by rw [hsplit]
  rw [Finset.sum_congr rfl fun c _ => hscaled c]
  -- the excess-weighted mass is trace minus weight
  have hexpand : ∑ c, (planarNorm (square c) - 1) * weight c
      = (∑ c, weight c * planarNorm (square c)) - ∑ c, weight c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hexpand, htrace, hweightSum]
  norm_num

end Gtz
