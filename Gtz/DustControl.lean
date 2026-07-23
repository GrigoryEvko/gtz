/-
# Proposition D: unconditional dust control on the planar platform

The two per-pair inequalities of the audited Proposition D (diary §68) and
the summed dust-deficit bound with the repaired tight constant:

* `pairEntry_bloch_nonneg_of_mixed` — D.1, mixed positivity: a heavy/dust
  pair has nonnegative entry unconditionally (no silence needed);
* `pairEntry_bloch_ge_of_dust` — the dust-pair floor
  `M_cd ≥ −2(a−ℓ_c)(a−ℓ_d)`;
* `dust_deficit_bloch` — D.3 with the AUDIT-REPAIRED constant: the dust-dust
  half pair-sum is `≥ −2δ₀δ₂`, via the expansion identity
  `Σ f_c f_d |S_c−S_d|² = 2δ₀δ₂ − 2|Σ f S|² ≤ 2δ₀δ₂` (the printed route of
  the informal artifact only reached `−4δ₀δ₂`; the repair is §68's G1).
-/
import Mathlib
import Gtz.PlanarPlatform
import Gtz.BlochDictionary
import Gtz.PsdKit

namespace Gtz

open Matrix

variable {m : ℕ}

/-- **Proposition D.1 (mixed positivity)**: a pair with `ℓ_c ≥ a ≥ ℓ_d` has
nonnegative entry — unconditionally, no silence hypothesis. -/
theorem pairEntry_bloch_nonneg_of_mixed (atoms : Fin m → Fin 2 → ℝ)
    (a : ℝ) (c d : Fin m)
    (hheavyC : a ≤ atoms c ⬝ᵥ atoms c) (hdustD : atoms d ⬝ᵥ atoms d ≤ a) :
    0 ≤ pairEntry (fun e => blochSquare (atoms e))
        (fun e => atoms e ⬝ᵥ atoms e - 2 * a) a c d := by
  rw [pairEntry_bloch]
  nlinarith [sq_nonneg (atoms c ⬝ᵥ atoms d),
    mul_nonneg (sub_nonneg.mpr hheavyC) (sub_nonneg.mpr hdustD)]

/-- The dust-pair floor: `M_cd ≥ −2(a−ℓ_c)(a−ℓ_d)` for any pair (the product
term is all that can go negative; the pairing square only helps). -/
theorem pairEntry_bloch_ge_of_dust (atoms : Fin m → Fin 2 → ℝ)
    (a : ℝ) (c d : Fin m) :
    -(2 * ((a - atoms c ⬝ᵥ atoms c) * (a - atoms d ⬝ᵥ atoms d)))
      ≤ pairEntry (fun e => blochSquare (atoms e))
          (fun e => atoms e ⬝ᵥ atoms e - 2 * a) a c d := by
  rw [pairEntry_bloch]
  nlinarith [sq_nonneg (atoms c ⬝ᵥ atoms d)]

/-- **Proposition D.3 (dust deficit, tight constant)**: the half pair-sum
over any subfamily with nonnegative weights is bounded below by `−2δ₀δ₂`
with `δ_j = Σ_D t_c (a−ℓ_c) ℓ_c^j` — the audit-repaired constant, through
the expansion identity, not the crude norm bound. Statement hygiene: the
informal statement assumed every leverage `≤ a` (dust), but the chain never
uses it — dust-ness only makes `δ₀, δ₂` nonnegative, i.e. makes the bound
worth having. -/
theorem dust_deficit_bloch (dustSet : Finset (Fin m))
    (atoms : Fin m → Fin 2 → ℝ) (weight : Fin m → ℝ) (a : ℝ)
    (hweight : ∀ c ∈ dustSet, 0 ≤ weight c) :
    -(2 * (∑ c ∈ dustSet, weight c * (a - atoms c ⬝ᵥ atoms c))
        * (∑ c ∈ dustSet, weight c * (a - atoms c ⬝ᵥ atoms c)
            * (atoms c ⬝ᵥ atoms c) ^ 2))
      ≤ (1 / 2) * ∑ c ∈ dustSet, ∑ d ∈ dustSet,
          pairEntry (fun e => blochSquare (atoms e))
              (fun e => atoms e ⬝ᵥ atoms e - 2 * a) a c d
            * weight c * weight d
            * ((blochSquare (atoms c) - blochSquare (atoms d)) ⬝ᵥ
               (blochSquare (atoms c) - blochSquare (atoms d))) := by
  -- Per-term floor: entry ≥ −2(a−ℓ_c)(a−ℓ_d), and the squared difference is
  -- nonnegative, so each term is ≥ −(deficit coefficient)·|ΔS|².
  have hterm : ∀ c ∈ dustSet, ∀ d ∈ dustSet,
      -((weight c * (a - atoms c ⬝ᵥ atoms c))
          * (weight d * (a - atoms d ⬝ᵥ atoms d))
          * ((blochSquare (atoms c) - blochSquare (atoms d)) ⬝ᵥ
             (blochSquare (atoms c) - blochSquare (atoms d))))
        ≤ (1 / 2) * (pairEntry (fun e => blochSquare (atoms e))
              (fun e => atoms e ⬝ᵥ atoms e - 2 * a) a c d
            * weight c * weight d
            * ((blochSquare (atoms c) - blochSquare (atoms d)) ⬝ᵥ
               (blochSquare (atoms c) - blochSquare (atoms d)))) := by
    intro c hc d hd
    have hfloor := pairEntry_bloch_ge_of_dust atoms a c d
    have hnormSq := dotProduct_self_nonneg
      (blochSquare (atoms c) - blochSquare (atoms d))
    have hwc := hweight c hc
    have hwd := hweight d hd
    nlinarith [mul_nonneg hwc hwd,
      mul_nonneg (mul_nonneg hwc hwd) hnormSq]
  -- Sum the floors, then close with the expansion identity and `|Σ f S|² ≥ 0`.
  have hsum :
      -(∑ c ∈ dustSet, ∑ d ∈ dustSet,
          (weight c * (a - atoms c ⬝ᵥ atoms c))
            * (weight d * (a - atoms d ⬝ᵥ atoms d))
            * ((blochSquare (atoms c) - blochSquare (atoms d)) ⬝ᵥ
               (blochSquare (atoms c) - blochSquare (atoms d))))
        ≤ (1 / 2) * ∑ c ∈ dustSet, ∑ d ∈ dustSet,
            pairEntry (fun e => blochSquare (atoms e))
                (fun e => atoms e ⬝ᵥ atoms e - 2 * a) a c d
              * weight c * weight d
              * ((blochSquare (atoms c) - blochSquare (atoms d)) ⬝ᵥ
                 (blochSquare (atoms c) - blochSquare (atoms d))) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun c hc => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun d hd => hterm c hc d hd
  refine le_trans ?_ hsum
  -- The expansion identity with `f_c = t_c(a−ℓ_c)` and `|S_c|² = ℓ_c²`.
  have hexpansion := sum_sub_normSq_expansion dustSet
    (fun c => weight c * (a - atoms c ⬝ᵥ atoms c))
    (fun c => blochSquare (atoms c))
  have hnormSqAll : (∑ c ∈ dustSet, (weight c * (a - atoms c ⬝ᵥ atoms c))
      * (blochSquare (atoms c) ⬝ᵥ blochSquare (atoms c)))
        = ∑ c ∈ dustSet, weight c * (a - atoms c ⬝ᵥ atoms c)
            * (atoms c ⬝ᵥ atoms c) ^ 2 :=
    Finset.sum_congr rfl fun c _ => by rw [blochSquare_normSq]
  rw [hnormSqAll] at hexpansion
  have hcenter := dotProduct_self_nonneg
    (∑ c ∈ dustSet, (weight c * (a - atoms c ⬝ᵥ atoms c)) •
      blochSquare (atoms c))
  rw [neg_le_neg_iff]
  calc (∑ c ∈ dustSet, ∑ d ∈ dustSet,
        (weight c * (a - atoms c ⬝ᵥ atoms c))
          * (weight d * (a - atoms d ⬝ᵥ atoms d))
          * ((blochSquare (atoms c) - blochSquare (atoms d)) ⬝ᵥ
             (blochSquare (atoms c) - blochSquare (atoms d))))
      = 2 * (∑ c ∈ dustSet, weight c * (a - atoms c ⬝ᵥ atoms c))
          * (∑ c ∈ dustSet, weight c * (a - atoms c ⬝ᵥ atoms c)
              * (atoms c ⬝ᵥ atoms c) ^ 2)
        - 2 * ((∑ c ∈ dustSet, (weight c * (a - atoms c ⬝ᵥ atoms c)) •
              blochSquare (atoms c)) ⬝ᵥ
            (∑ c ∈ dustSet, (weight c * (a - atoms c ⬝ᵥ atoms c)) •
              blochSquare (atoms c))) := hexpansion
    _ ≤ 2 * (∑ c ∈ dustSet, weight c * (a - atoms c ⬝ᵥ atoms c))
          * (∑ c ∈ dustSet, weight c * (a - atoms c ⬝ᵥ atoms c)
              * (atoms c ⬝ᵥ atoms c) ^ 2) := by linarith

end Gtz
