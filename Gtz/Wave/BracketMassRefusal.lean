/-
# The bracket mass of a pair refuses its own dominators

Two landed laws meet here, and neither lane spent them together.

`Gtz.pair_bracket_mass` is an EXACT identity: the weighted squared brackets
through a pair, summed over the whole design, total that pair's wedge,

  `Σ_f t_a*t_b*t_f*[a b f]^2 = t_a*t_b*(l_a*l_b - (g_a.g_b)^2)` .

`Gtz.crossNormSq_le_tripleBracket_sq_of_posSemidef` is a CEILING with no tie
hypothesis: a triple whose gap is positive semidefinite has each of its pair
wedges at most its own squared bracket.

Put together, a weakly dominating triple caps the ENTIRE bracket mass of one of
its pairs by its own single squared bracket:

  **`Σ_f t_f*[a b f]^2  <=  [a b c]^2`** .

The sum contains the `c` term itself, so what is left over for every other atom
is the complement of `c`'s weight:

  **`t_e*[a b e]^2  <=  (1 - t_c)*[a b c]^2`**   (`Gtz.bracket_mass_refusal`).

## Why this is a refusal producer

Read backwards it manufactures refusals for free.  If ONE other atom `e` carries
too much bracket through the pair `{a, b}`, the triple `{a, b, c}` cannot even
weakly dominate — `Gtz.not_posSemidef_of_bracket_mass_excess`.  No tie, no
corner, no domination assumption, no adjugate and no eigenvalue: two atoms, a
weight, and two brackets decide it.

Both currencies are terminal for the campaign.  The bracket is the realness
carrier, and the wedge behind the identity is the parallelism detector, so the
test is stated entirely in the alphabet the endgame already uses.
-/
import Gtz.Wave.PairBracketMass
import Gtz.Wave.KOneWedgeCeiling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The whole bracket mass of a pair is capped by one dominator -/

/-- **THE DOMINATOR CAPS THE PAIR'S WHOLE BRACKET MASS.**  If the gap of
`{a, b, c}` is positive semidefinite then the design's total weighted squared
bracket through the pair `{a, b}` is at most the single squared bracket of that
triple.  The exact pair mass identity against the landed wedge ceiling. -/
theorem bracket_mass_le_dominator_bracket_sq (D : WeightedDesign m 3) (a b c : Fin m)
    (hgap : (atomMatrix (D.atom a) + atomMatrix (D.atom b) + atomMatrix (D.atom c)
      - 1).PosSemidef) :
    ∑ f, D.weight a * (D.weight b * (D.weight f * atomBracket D a b f ^ 2))
      ≤ D.weight a * (D.weight b * atomBracket D a b c ^ 2) := by
  have hmass := pair_bracket_mass D a b
  have hceil := crossNormSq_le_tripleBracket_sq_of_posSemidef
    (D.atom a) (D.atom b) (D.atom c) hgap
  rw [crossNormSq_eq_leverage_mul_sub_sq] at hceil
  have hab : (0 : ℝ) < D.weight a * D.weight b :=
    mul_pos (D.weight_pos a) (D.weight_pos b)
  rw [hmass, atomPairing]
  rw [atomBracket]
  nlinarith [hceil, hab]

/-! ## 2. The refusal producer -/

/-- **THE BRACKET MASS REFUSAL.**  At a weakly dominating triple `{a, b, c}`,
every OTHER atom's weighted squared bracket through the pair `{a, b}` is capped
by the complement of `c`'s weight times the triple's own squared bracket.  The
`c` term of the exact mass identity is subtracted off before the drop, so no
weight is wasted. -/
theorem bracket_mass_refusal (D : WeightedDesign m 3) (a b c e : Fin m) (hce : c ≠ e)
    (hgap : (atomMatrix (D.atom a) + atomMatrix (D.atom b) + atomMatrix (D.atom c)
      - 1).PosSemidef) :
    D.weight e * atomBracket D a b e ^ 2
      ≤ (1 - D.weight c) * atomBracket D a b c ^ 2 := by
  classical
  have hcap := bracket_mass_le_dominator_bracket_sq D a b c hgap
  -- the two named terms are already in the total
  have hsub : ({c, e} : Finset (Fin m)) ⊆ (Finset.univ : Finset (Fin m)) :=
    Finset.subset_univ _
  have hnn : ∀ f ∈ (Finset.univ : Finset (Fin m)), f ∉ ({c, e} : Finset (Fin m)) →
      0 ≤ D.weight a * (D.weight b * (D.weight f * atomBracket D a b f ^ 2)) := by
    intro f _ _
    exact mul_nonneg (D.weight_pos a).le (mul_nonneg (D.weight_pos b).le
      (mul_nonneg (D.weight_pos f).le (sq_nonneg _)))
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have hcmem : c ∉ ({e} : Finset (Fin m)) := by
    simp only [Finset.mem_singleton]; exact hce
  rw [Finset.sum_insert hcmem, Finset.sum_singleton] at hle
  have hchain : D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
      + D.weight a * (D.weight b * (D.weight e * atomBracket D a b e ^ 2))
      ≤ D.weight a * (D.weight b * atomBracket D a b c ^ 2) := le_trans hle hcap
  have hab : (0 : ℝ) < D.weight a * D.weight b :=
    mul_pos (D.weight_pos a) (D.weight_pos b)
  nlinarith [hchain, hab]

/-- **THE CONTRAPOSITIVE — REFUSALS FOR FREE.**  One atom carrying more bracket
mass through a pair than the complement of a candidate's weight allows refuses
that candidate outright.  Two atoms, one weight and two brackets, with no tie
hypothesis anywhere. -/
theorem not_posSemidef_of_bracket_mass_excess (D : WeightedDesign m 3)
    (a b c e : Fin m) (hce : c ≠ e)
    (hex : (1 - D.weight c) * atomBracket D a b c ^ 2
      < D.weight e * atomBracket D a b e ^ 2) :
    ¬ (atomMatrix (D.atom a) + atomMatrix (D.atom b) + atomMatrix (D.atom c)
      - 1).PosSemidef := fun hgap =>
  absurd (bracket_mass_refusal D a b c e hce hgap) (not_le.mpr hex)

end Gtz
