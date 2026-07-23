/-
# The antipode identity and the moment bound |ξ| < 1/2

The unconditional discharge of the covector-length hypothesis that
`TightGraph` consumes. On the focal conic `ν(u) = 1/2 + ⟨ξ,u⟩` the values at
antipodal directions pair to one — so a conic that stays positive on the whole
circle pins the covector strictly inside the radius-`1/2` disk: evaluating at
the antipode of `ξ`'s own direction gives `1/2 − |ξ| > 0`. Positivity of the
conic values is exactly "every direction's leverage is finite and positive",
which Theorem V supplies at every tight triangle; the chord geometry that
previously carried this bound is not needed.
-/
import Mathlib
import Gtz.Pushoff

namespace Gtz

/-- **The antipode identity**: focal conic values at antipodal directions pair
to one. `ν(−u) = 1 − ν(u)` is the reflection that sends leverage `ℓ` to its
conjugate `ℓ/(ℓ−1)`. -/
theorem focal_conic_antipode (moment unit : Fin 2 → ℝ) :
    (1 / 2 + moment ⬝ᵥ unit) + (1 / 2 + moment ⬝ᵥ (-unit)) = 1 := by
  rw [dotProduct_neg]
  ring

/-- **The moment bound**: a focal conic positive at every unit direction pins
the covector strictly inside the radius-`1/2` disk. -/
theorem moment_short_of_conic_pos {moment : Fin 2 → ℝ}
    (hconicPos : ∀ unit : Fin 2 → ℝ, unit ⬝ᵥ unit = 1
      → 0 < 1 / 2 + moment ⬝ᵥ unit) :
    moment ⬝ᵥ moment < 1 / 4 := by
  rcases eq_or_ne moment 0 with hzero | hnonzero
  · rw [hzero]
    norm_num
  · -- test the conic at the antipode of the covector's own direction
    have hnormPos : 0 < planarNorm moment := by
      rcases lt_or_eq_of_le (planarNorm_nonneg moment) with hpos | hdegenerate
      · exact hpos
      · exfalso
        have hsq : moment ⬝ᵥ moment = 0 := by
          have := planarNorm_sq moment
          rw [← hdegenerate] at this
          simpa using this.symm
        have hexpand : moment 0 ^ 2 + moment 1 ^ 2 = 0 := by
          have := hsq
          simp only [dotProduct, Fin.sum_univ_two] at this
          nlinarith [this]
        have hheadZero : moment 0 = 0 := by
          nlinarith [sq_nonneg (moment 0), sq_nonneg (moment 1)]
        have htailZero : moment 1 = 0 := by
          nlinarith [sq_nonneg (moment 0), sq_nonneg (moment 1)]
        refine hnonzero (funext fun i => ?_)
        fin_cases i
        · exact hheadZero
        · exact htailZero
    set antipode := (-(planarNorm moment)⁻¹) • moment with hantipode
    have hunit : antipode ⬝ᵥ antipode = 1 := by
      rw [hantipode, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, ← planarNorm_sq]
      field_simp
    have hvalue := hconicPos antipode hunit
    rw [hantipode, dotProduct_smul, smul_eq_mul] at hvalue
    -- the conic value there is 1/2 − |ξ|
    have hdot : moment ⬝ᵥ moment = planarNorm moment ^ 2 :=
      (planarNorm_sq moment).symm
    have hlen : planarNorm moment < 1 / 2 := by
      have hcollapse : -(planarNorm moment)⁻¹ * (moment ⬝ᵥ moment)
          = -planarNorm moment := by
        rw [hdot]
        field_simp
      rw [hcollapse] at hvalue
      linarith
    rw [hdot]
    nlinarith [hnormPos, hlen]

/-- **The clean pushoff**: with the moment bound `|ξ| < 1/2` the Lipschitz
constant of the Zero-Atom Pushoff drops below one — the zero atom's weight is
outright dominated by the others' weighted distance to the tight manifold:
`t_e ≤ Σ t_c·|S_c − X_c|`. The mechanism of the τ₀-collar, in one line. -/
theorem zeroAtom_pushoff_clean {m : ℕ} (atoms : Finset (Fin m))
    (zeroAtom : Fin m) (hmem : zeroAtom ∈ atoms)
    (weight : Fin m → ℝ) (planarSquare : Fin m → Fin 2 → ℝ)
    (moment : Fin 2 → ℝ) (nearestZero : Fin m → Fin 2 → ℝ)
    (hweightSum : ∑ c ∈ atoms, weight c = 1)
    (hclosure : (∑ c ∈ atoms, weight c • planarSquare c) = 0)
    (htrace : ∑ c ∈ atoms, weight c * planarNorm (planarSquare c) = 2)
    (hzeroSquare : planarSquare zeroAtom = 0)
    (hweightNonneg : ∀ c ∈ atoms, 0 ≤ weight c)
    (hnearestZero : ∀ c ∈ atoms.erase zeroAtom,
      planarDefect moment (nearestZero c) = 0)
    (hmomentShort : planarNorm moment ≤ 1 / 2) :
    weight zeroAtom
      ≤ ∑ c ∈ atoms.erase zeroAtom,
          weight c * planarNorm (planarSquare c - nearestZero c) := by
  have hpushoff := zeroAtom_pushoff atoms zeroAtom hmem weight planarSquare
    moment nearestZero hweightSum hclosure htrace hzeroSquare hweightNonneg
    hnearestZero
  have hdistNonneg : 0 ≤ ∑ c ∈ atoms.erase zeroAtom,
      weight c * planarNorm (planarSquare c - nearestZero c) :=
    Finset.sum_nonneg fun c hc =>
      mul_nonneg (hweightNonneg c (Finset.mem_of_mem_erase hc))
        (planarNorm_nonneg _)
  nlinarith [hpushoff, hdistNonneg, hmomentShort]

end Gtz
