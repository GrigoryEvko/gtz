/-
# The certificate frame's scalar layer

The exact algebra underneath the Gordan certificate of an equality design —
the pieces of the stress frame that are pure identities once stated, isolated
from the graph bookkeeping.

**The conic normalization.** The t-block of the certificate says every atom
lies on a conic `μ₀ + ⟨ξ,S_c⟩ + βℓ_c = 0`. Pairing with the weights and using
the three design equations collapses the free constant: `μ₀ = −2β`. Dividing
each atom's equation by its leverage then puts every atom on the focal conic
`ν = 1/2 + ⟨ξ̃, u⟩` with `ξ̃ = −ξ/(2β)` — Theorem V's covector, now derived for
every equality design from the certificate alone.

**The Euler pairing, per edge.** Pairing the stress equation with the squares
and summing telescopes to the tight-pair slacks: each edge contributes exactly
`2(σ_e + 1)`, because `⟨u_c − v_e, S_c⟩ + ⟨u_d − v_e, S_d⟩ = ℓ_c + ℓ_d − n_e`.
On tight pairs this is `2`, which is what forces `Σλ_e = 2β` and fixes the
certificate's sign.

**The uncovered-atom pole.** An atom carrying no stressed edge has stress
equation `t_c(u_c − 2ξ̃) = 0`, so its direction is `2ξ̃` and the covector sits
on the parabola `|ξ̃| = 1/2` — the kill-step of the Gordan covering argument,
whose margin against the cap is what the quantified covering consumes.
-/
import Mathlib
import Gtz.Pushoff

namespace Gtz

/-! ### The conic normalization -/

/-- **The t-block collapse**: atoms on the conic
`μ₀ + ⟨ξ,S_c⟩ + βℓ_c = 0`, paired against the three design equations, force
`μ₀ = −2β`. -/
theorem conic_normalization {atomCount : ℕ}
    (weight leverage : Fin atomCount → ℝ)
    (square : Fin atomCount → Fin 2 → ℝ) (freeConst beta : ℝ)
    (moment : Fin 2 → ℝ)
    (hweight : ∑ c, weight c = 1)
    (hclosure : ∑ c, weight c • square c = 0)
    (htrace : ∑ c, weight c * leverage c = 2)
    (hconic : ∀ c, freeConst + moment ⬝ᵥ square c + beta * leverage c = 0) :
    freeConst = -(2 * beta) := by
  have hpaired : ∑ c, weight c
      * (freeConst + moment ⬝ᵥ square c + beta * leverage c) = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [hconic c, mul_zero]
  have hsplit : ∑ c, weight c
      * (freeConst + moment ⬝ᵥ square c + beta * leverage c)
      = freeConst * (∑ c, weight c)
        + moment ⬝ᵥ (∑ c, weight c • square c)
        + beta * (∑ c, weight c * leverage c) := by
    rw [dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, hweight, hclosure, htrace, dotProduct_zero] at hpaired
  linarith

/-- **The focal conic**: an atom on the normalized conic has
`ν = 1/2 + ⟨ξ̃, u⟩` for the rescaled covector `ξ̃ = −ξ/(2β)` — the Theorem-V
relation, derived rather than assumed. -/
theorem focal_conic_form {freeConst beta lev : ℝ} {moment unit : Fin 2 → ℝ}
    (hconic : freeConst + moment ⬝ᵥ (lev • unit) + beta * lev = 0)
    (hnorm : freeConst = -(2 * beta)) (hlev : lev ≠ 0) (hbeta : beta ≠ 0) :
    1 - 1 / lev = 1 / 2 + ((-(2 * beta))⁻¹ • moment) ⬝ᵥ unit := by
  rw [dotProduct_smul, smul_eq_mul] at hconic
  rw [smul_dotProduct, smul_eq_mul]
  have hdot : moment ⬝ᵥ unit = (2 * beta - beta * lev) / lev := by
    rw [eq_div_iff hlev]
    linarith [hconic, hnorm]
  rw [hdot]
  field_simp
  ring

/-! ### The per-edge Euler pairing -/

/-- **The edge pairing telescopes to the slack**: pairing the two endpoint
stress directions `u − v_e` against their own squares gives exactly
`ℓ_c + ℓ_d − n_e = 2(σ_e + 1)`. On a tight pair this is `2` — the per-edge
contribution that makes the certificate's stress sum to `2β`. -/
theorem edge_pairing_eq_slack (firstSquare secondSquare : Fin 2 → ℝ)
    (hfirst : planarNorm firstSquare ≠ 0)
    (hsecond : planarNorm secondSquare ≠ 0)
    (hchord : planarNorm (firstSquare + secondSquare) ≠ 0) :
    ((planarNorm firstSquare)⁻¹ • firstSquare
        - (planarNorm (firstSquare + secondSquare))⁻¹
          • (firstSquare + secondSquare)) ⬝ᵥ firstSquare
      + ((planarNorm secondSquare)⁻¹ • secondSquare
        - (planarNorm (firstSquare + secondSquare))⁻¹
          • (firstSquare + secondSquare)) ⬝ᵥ secondSquare
      = 2 * (((planarNorm firstSquare + planarNorm secondSquare
          - planarNorm (firstSquare + secondSquare)) / 2 - 1) + 1) := by
    set firstLen := planarNorm firstSquare with hfirstLen
    set secondLen := planarNorm secondSquare with hsecondLen
    set chordLen := planarNorm (firstSquare + secondSquare) with hchordLen
    have hfirstSq : firstSquare ⬝ᵥ firstSquare = firstLen ^ 2 :=
      (planarNorm_sq firstSquare).symm
    have hsecondSq : secondSquare ⬝ᵥ secondSquare = secondLen ^ 2 :=
      (planarNorm_sq secondSquare).symm
    have hchordSq : (firstSquare + secondSquare)
        ⬝ᵥ (firstSquare + secondSquare) = chordLen ^ 2 :=
      (planarNorm_sq (firstSquare + secondSquare)).symm
    -- expand every dot product against the three squared lengths
    have hcross : (firstSquare + secondSquare) ⬝ᵥ firstSquare
        + (firstSquare + secondSquare) ⬝ᵥ secondSquare = chordLen ^ 2 := by
      rw [← hchordSq, dotProduct_add]
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hfirstSq, hsecondSq]
    have hexpand : (firstLen)⁻¹ * firstLen ^ 2 = firstLen := by
      field_simp
    have hexpandSecond : (secondLen)⁻¹ * secondLen ^ 2 = secondLen := by
      field_simp
    have hchordPart : chordLen⁻¹ * ((firstSquare + secondSquare) ⬝ᵥ firstSquare)
        + chordLen⁻¹ * ((firstSquare + secondSquare) ⬝ᵥ secondSquare)
        = chordLen := by
      rw [← mul_add, hcross]
      field_simp
    linarith [hexpand, hexpandSecond, hchordPart]

/-! ### The uncovered-atom pole -/

/-- **The Gordan kill-step**: an atom with no stressed edge has stress
equation `t_c·(u_c − 2ξ̃) = 0`; positive weight forces its direction onto the
covector's double, and unit length then pins `|ξ̃|² = 1/4` — the parabola.
Every uncovered atom is a pole, which is the contradiction margin the
quantified covering runs on. -/
theorem uncovered_atom_forces_pole {weight : ℝ} {unit rescaled : Fin 2 → ℝ}
    (hweight : 0 < weight)
    (hstress : weight • (unit - (2 : ℝ) • rescaled) = 0)
    (hunit : unit ⬝ᵥ unit = 1) :
    unit = (2 : ℝ) • rescaled ∧ rescaled ⬝ᵥ rescaled = 1 / 4 := by
  have hdirection : unit - (2 : ℝ) • rescaled = 0 := by
    have hcomponents := congrFun hstress
    refine funext fun i => ?_
    have hentry := hcomponents i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hentry
    have hfactor := mul_eq_zero.mp hentry
    rcases hfactor with hzero | hgap
    · exact absurd hzero (ne_of_gt hweight)
    · simpa using hgap
  have hpole : unit = (2 : ℝ) • rescaled := by
    have := sub_eq_zero.mp hdirection
    exact this
  refine ⟨hpole, ?_⟩
  have hlen := hunit
  rw [hpole] at hlen
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hlen
  linarith

/-- **The pole contradicts the conic**: an atom sitting at the covector's pole
has conic value `1/2 + 2|ξ̃|² = 1`, i.e. infinite leverage — impossible. -/
theorem pole_contradicts_conic {lev : ℝ} {rescaled unit : Fin 2 → ℝ}
    (hconic : 1 - 1 / lev = 1 / 2 + rescaled ⬝ᵥ unit)
    (hpole : unit = (2 : ℝ) • rescaled)
    (hquarter : rescaled ⬝ᵥ rescaled = 1 / 4) (hlev : 0 < lev) : False := by
  rw [hpole, dotProduct_smul, smul_eq_mul, hquarter] at hconic
  have hzero : 1 / lev = 0 := by linarith
  have hpos : 0 < 1 / lev := by positivity
  linarith

/-- **The Gordan covering kill, β ≠ 0 branch**: an atom of positive weight and
finite positive leverage on the focal conic CANNOT be uncovered — its empty
stress equation would pin it to the pole, and the pole forces infinite
leverage. Every atom of an equality design lies in a tight pair. -/
theorem covered_of_conic {weight lev : ℝ} {unit rescaled : Fin 2 → ℝ}
    (hweight : 0 < weight) (hlev : 0 < lev)
    (hconic : 1 - 1 / lev = 1 / 2 + rescaled ⬝ᵥ unit)
    (hunit : unit ⬝ᵥ unit = 1)
    (hstress : weight • (unit - (2 : ℝ) • rescaled) = 0) : False := by
  obtain ⟨hpole, hquarter⟩ := uncovered_atom_forces_pole hweight hstress hunit
  exact pole_contradicts_conic hconic hpole hquarter hlev

end Gtz
