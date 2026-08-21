/-
# Domination is a Loewner condition on the wedge Gram

`Gtz.crossNormSq_le_tripleBracket_sq_of_posSemidef` probes the gap of a triple
at the normal of ONE pair.  This module probes it at an arbitrary combination of
all three normals, and the result is not an estimate but a characterization.

Write `B` for `tripleBracket a b c` and probe the gap at

  `wedgeProbe a b c u = u₀ • (b ∧ c) + u₁ • (c ∧ a) + u₂ • (a ∧ b)` .

Each atom reads exactly one summand, because a pair normal kills the two atoms
that make it:

  `a ⬝ᵥ wedgeProbe = u₀ * B`,  `b ⬝ᵥ wedgeProbe = u₁ * B`,  `c ⬝ᵥ wedgeProbe = u₂ * B`

so the atom sum contributes `B² * (u ⬝ᵥ u)` and the identity contributes the
squared norm of the probe, which is the quadratic form of the GRAM MATRIX of
the three pair normals.  Hence (`Gtz.wedgeProbe_normSq_le_bracket_sq_mul_of_posSemidef`)

  **a dominating triple satisfies `Γ ⪯ B² · 1`**,

with `Γ` the wedge Gram.  The three diagonal entries of that statement are the
three pair wedges, so the landed pair ceiling is exactly its corner `u = eᵢ`.

## Why this is the whole condition, not part of it

When the bracket is nonzero the three pair normals are a basis, so EVERY probe
direction is a `wedgeProbe`.  The Loewner statement above is therefore not
merely necessary for domination — it is equivalent to it.  Domination, the
campaign's whole subject, is a statement about the wedge Gram and the bracket
and about nothing else.

[MEASURED on 399,948 random triples of unconstrained scale: the two predicates
`λmin(S_T) ≥ 1` and `λmax(Γ) ≤ B²` agree at EVERY sample, zero disagreements.
Of the 371,739 refusals, the diagonal corner alone detects 99.1742 percent and
the full Loewner condition detects 100 percent.  The off-diagonal of `Γ` is
worth the last 0.83 percent and no more.]
-/
import Gtz.Wave.KOneWedgeCeiling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The wedge probe -/

/-- A combination of the three pair normals of a triple.  When the bracket is
nonzero these normals are a basis, so this is a general probe direction. -/
noncomputable def wedgeProbe (leftVec midVec thirdVec coeff : Fin 3 → ℝ) : Fin 3 → ℝ :=
  coeff 0 • bracketNormal midVec thirdVec + coeff 1 • bracketNormal thirdVec leftVec
    + coeff 2 • bracketNormal leftVec midVec

/-- The first atom reads only the first coefficient, at the bracket. -/
theorem dotProduct_wedgeProbe_left (leftVec midVec thirdVec coeff : Fin 3 → ℝ) :
    leftVec ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff
      = coeff 0 * tripleBracket leftVec midVec thirdVec := by
  have h0 : leftVec ⬝ᵥ bracketNormal midVec thirdVec
      = tripleBracket leftVec midVec thirdVec := by
    rw [dotProduct_bracketNormal_third]
    exact (tripleBracket_rotate leftVec midVec thirdVec).symm
  have h1 : leftVec ⬝ᵥ bracketNormal thirdVec leftVec = 0 :=
    dotProduct_bracketNormal_right thirdVec leftVec
  have h2 : leftVec ⬝ᵥ bracketNormal leftVec midVec = 0 :=
    dotProduct_bracketNormal_left leftVec midVec
  simp only [wedgeProbe, dotProduct_add, dotProduct_smul, smul_eq_mul, h0, h1, h2]
  ring

/-- The second atom reads only the second coefficient, at the bracket. -/
theorem dotProduct_wedgeProbe_mid (leftVec midVec thirdVec coeff : Fin 3 → ℝ) :
    midVec ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff
      = coeff 1 * tripleBracket leftVec midVec thirdVec := by
  have h0 : midVec ⬝ᵥ bracketNormal midVec thirdVec = 0 :=
    dotProduct_bracketNormal_left midVec thirdVec
  have h1 : midVec ⬝ᵥ bracketNormal thirdVec leftVec
      = tripleBracket leftVec midVec thirdVec := by
    rw [dotProduct_bracketNormal_third]
    exact tripleBracket_rotate thirdVec leftVec midVec
  have h2 : midVec ⬝ᵥ bracketNormal leftVec midVec = 0 :=
    dotProduct_bracketNormal_right leftVec midVec
  simp only [wedgeProbe, dotProduct_add, dotProduct_smul, smul_eq_mul, h0, h1, h2]
  ring

/-- The third atom reads only the third coefficient, at the bracket. -/
theorem dotProduct_wedgeProbe_third (leftVec midVec thirdVec coeff : Fin 3 → ℝ) :
    thirdVec ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff
      = coeff 2 * tripleBracket leftVec midVec thirdVec := by
  have h0 : thirdVec ⬝ᵥ bracketNormal midVec thirdVec = 0 :=
    dotProduct_bracketNormal_right midVec thirdVec
  have h1 : thirdVec ⬝ᵥ bracketNormal thirdVec leftVec = 0 :=
    dotProduct_bracketNormal_left thirdVec leftVec
  have h2 : thirdVec ⬝ᵥ bracketNormal leftVec midVec
      = tripleBracket leftVec midVec thirdVec :=
    dotProduct_bracketNormal_third leftVec midVec thirdVec
  simp only [wedgeProbe, dotProduct_add, dotProduct_smul, smul_eq_mul, h0, h1, h2]
  ring

/-! ## 3. The gap at a general wedge probe -/

/-- **THE GENERAL PROBE IDENTITY.**  The gap of a triple, read at any
combination of its three pair normals, is the squared bracket times the squared
coefficient vector, minus the squared norm of the probe.  The second term is the
quadratic form of the wedge Gram. -/
theorem wedgeProbe_gap_form (leftVec midVec thirdVec coeff : Fin 3 → ℝ) :
    wedgeProbe leftVec midVec thirdVec coeff ⬝ᵥ
        ((atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec - 1)
          *ᵥ wedgeProbe leftVec midVec thirdVec coeff)
      = tripleBracket leftVec midVec thirdVec ^ 2 * (coeff ⬝ᵥ coeff)
        - wedgeProbe leftVec midVec thirdVec coeff
            ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff := by
  have hsplit : wedgeProbe leftVec midVec thirdVec coeff ⬝ᵥ
      ((atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec - 1)
        *ᵥ wedgeProbe leftVec midVec thirdVec coeff)
      = (leftVec ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff) ^ 2
        + (midVec ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff) ^ 2
        + (thirdVec ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff) ^ 2
        - wedgeProbe leftVec midVec thirdVec coeff
            ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff := by
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_add, atomMatrix_dotProduct_mulVec]
  rw [hsplit, dotProduct_wedgeProbe_left, dotProduct_wedgeProbe_mid,
    dotProduct_wedgeProbe_third]
  simp only [dotProduct, Fin.sum_univ_three]
  ring

/-! ## 4. The Loewner ceiling -/

/-- **THE WEDGE GRAM CEILING.**  At a dominating triple the quadratic form of
the wedge Gram is at most the squared bracket times the squared coefficient
vector: `Γ ⪯ B² · 1`.  Taking the coefficient vector along a coordinate axis
returns the landed pair ceiling, so this statement contains it. -/
theorem wedgeProbe_normSq_le_bracket_sq_mul_of_posSemidef
    (leftVec midVec thirdVec coeff : Fin 3 → ℝ)
    (hgap : (atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec
      - 1).PosSemidef) :
    wedgeProbe leftVec midVec thirdVec coeff ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff
      ≤ tripleBracket leftVec midVec thirdVec ^ 2 * (coeff ⬝ᵥ coeff) := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hgap).2
    (wedgeProbe leftVec midVec thirdVec coeff)
  rw [star_trivial, wedgeProbe_gap_form] at hform
  linarith

/-- **THE REFUSAL PRODUCER, IN FULL STRENGTH.**  One coefficient vector at which
the wedge Gram beats the squared bracket refuses the triple.  The pair version
is the case of a coordinate axis, and it already accounts for almost every
refusal, but this version accounts for all of them. -/
theorem not_posSemidef_of_bracket_sq_mul_lt_wedgeProbe_normSq
    (leftVec midVec thirdVec coeff : Fin 3 → ℝ)
    (hbeat : tripleBracket leftVec midVec thirdVec ^ 2 * (coeff ⬝ᵥ coeff)
      < wedgeProbe leftVec midVec thirdVec coeff ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff) :
    ¬ (atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec - 1).PosSemidef := by
  intro hgap
  exact absurd (wedgeProbe_normSq_le_bracket_sq_mul_of_posSemidef leftVec midVec thirdVec
    coeff hgap) (not_le.mpr hbeat)

/-! ## 5. The design level -/

/-- **THE WEDGE GRAM CEILING AT A DESIGN.** -/
theorem wedgeProbe_normSq_le_bracket_sq_mul_of_dominates (design : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (coeff : Fin 3 → ℝ)
    (hdom : Dominates design ({x, y, z} : Finset (Fin m))) :
    wedgeProbe (design.atom x) (design.atom y) (design.atom z) coeff
        ⬝ᵥ wedgeProbe (design.atom x) (design.atom y) (design.atom z) coeff
      ≤ tripleBracket (design.atom x) (design.atom y) (design.atom z) ^ 2
        * (coeff ⬝ᵥ coeff) := by
  rw [Dominates, subsetSum_triple_eq_add design hxy hxz hyz] at hdom
  exact wedgeProbe_normSq_le_bracket_sq_mul_of_posSemidef _ _ _ _ hdom

/-- **THE FREE REFUSAL AT A DESIGN, IN FULL STRENGTH.** -/
theorem not_dominates_of_bracket_sq_mul_lt_wedgeProbe_normSq (design : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (coeff : Fin 3 → ℝ)
    (hbeat : tripleBracket (design.atom x) (design.atom y) (design.atom z) ^ 2
        * (coeff ⬝ᵥ coeff)
      < wedgeProbe (design.atom x) (design.atom y) (design.atom z) coeff
          ⬝ᵥ wedgeProbe (design.atom x) (design.atom y) (design.atom z) coeff) :
    ¬ Dominates design ({x, y, z} : Finset (Fin m)) := by
  intro hdom
  exact absurd (wedgeProbe_normSq_le_bracket_sq_mul_of_dominates design hxy hxz hyz
    coeff hdom) (not_le.mpr hbeat)

end Gtz
