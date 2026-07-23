/-
# The chord theorem's skeleton

Theorem S's three mechanizable bones, stripped of the convexity narrative.

**The chord functions.** `f_X(u) = (1 + ⟨u_X,u⟩)/2 − ν_X(1/2 + ⟨ξ,u⟩)` is
affine in `u`; tightness plus the focal conic make it vanish at the OTHER two
cluster directions (its zero line is the chord through them), and at its own
vertex it equals `1 − ν_X² > 0`.

**The vertex theorem.** The geometric step — the closed inscribed triangle
meets the circle only at its vertices — is here a two-line scalar argument:
for a unit convex combination of distinct unit vectors, subtracting
`|p|² = 1` from `(Σα)² = 1` leaves `Σ_{X<Y} α_Xα_Y(1 − ⟨u_X,u_Y⟩) = 0`, a sum
of nonnegative terms with strictly positive gaps, so at most one coefficient
survives and it is one. No convexity library, no strict-convexity axiom —
the circle's strict convexity IS the pairwise gap `⟨u_X,u_Y⟩ < 1`.
-/
import Mathlib

namespace Gtz

/-! ### The chord functions -/

/-- The chord function of cluster `X`, affine in the probe direction. -/
noncomputable def chordFn (clusterDir moment : Fin 2 → ℝ) (conicVal : ℝ)
    (probe : Fin 2 → ℝ) : ℝ :=
  (1 + clusterDir ⬝ᵥ probe) / 2 - conicVal * (1 / 2 + moment ⬝ᵥ probe)

/-- **The chord vanishes at the other clusters**: tightness plus the focal
conic annihilate `f_X` at `u_Y` — the zero line of `f_X` is the chord through
the other two cluster points. -/
theorem chordFn_vanishes {clusterDir otherDir moment : Fin 2 → ℝ}
    {conicValX conicValY : ℝ}
    (htight : (1 + clusterDir ⬝ᵥ otherDir) / 2 = conicValX * conicValY)
    (hconic : conicValY = 1 / 2 + moment ⬝ᵥ otherDir) :
    chordFn clusterDir moment conicValX otherDir = 0 := by
  rw [chordFn, htight, ← hconic]
  ring

/-- **The chord is positive at its own vertex**: `f_X(u_X) = 1 − ν_X²`. -/
theorem chordFn_at_vertex {clusterDir moment : Fin 2 → ℝ} {conicValX : ℝ}
    (hunit : clusterDir ⬝ᵥ clusterDir = 1)
    (hconic : conicValX = 1 / 2 + moment ⬝ᵥ clusterDir) :
    chordFn clusterDir moment conicValX clusterDir = 1 - conicValX ^ 2 := by
  rw [chordFn, hunit, ← hconic]
  ring

/-! ### The vertex theorem -/

/-- **The inscribed triangle meets the circle only at its vertices**: a UNIT
convex combination of three pairwise-distinct unit vectors is one of them.
Subtracting the squared-length identities kills every cross term against the
strictly positive gaps `1 − ⟨u_X,u_Y⟩`. -/
theorem inscribed_triangle_vertex
    {vertexA vertexB vertexC probe : Fin 2 → ℝ}
    {coefA coefB coefC : ℝ}
    (hunitA : vertexA ⬝ᵥ vertexA = 1) (hunitB : vertexB ⬝ᵥ vertexB = 1)
    (hunitC : vertexC ⬝ᵥ vertexC = 1) (hunitP : probe ⬝ᵥ probe = 1)
    (hgapAB : vertexA ⬝ᵥ vertexB < 1) (hgapAC : vertexA ⬝ᵥ vertexC < 1)
    (hgapBC : vertexB ⬝ᵥ vertexC < 1)
    (hnonnegA : 0 ≤ coefA) (hnonnegB : 0 ≤ coefB) (hnonnegC : 0 ≤ coefC)
    (hsum : coefA + coefB + coefC = 1)
    (hcombo : probe = coefA • vertexA + coefB • vertexB + coefC • vertexC) :
    probe = vertexA ∨ probe = vertexB ∨ probe = vertexC := by
  -- expand |p|² through the combination
  have hlen : coefA ^ 2 + coefB ^ 2 + coefC ^ 2
      + 2 * (coefA * coefB * (vertexA ⬝ᵥ vertexB))
      + 2 * (coefA * coefC * (vertexA ⬝ᵥ vertexC))
      + 2 * (coefB * coefC * (vertexB ⬝ᵥ vertexC)) = 1 := by
    have hexpand := hunitP
    rw [hcombo] at hexpand
    simp only [dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul] at hexpand
    rw [hunitA, hunitB, hunitC, dotProduct_comm vertexB vertexA,
      dotProduct_comm vertexC vertexA, dotProduct_comm vertexC vertexB]
      at hexpand
    nlinarith [hexpand]
  -- subtract (Σα)² = 1: the cross terms against the gaps vanish
  have hcross : coefA * coefB * (1 - vertexA ⬝ᵥ vertexB)
      + coefA * coefC * (1 - vertexA ⬝ᵥ vertexC)
      + coefB * coefC * (1 - vertexB ⬝ᵥ vertexC) = 0 := by
    nlinarith [hlen, hsum]
  -- each summand is nonnegative, so each product of coefficients vanishes
  have htermAB : coefA * coefB = 0 := by
    nlinarith [mul_nonneg hnonnegA hnonnegB, mul_nonneg hnonnegA hnonnegC,
      mul_nonneg hnonnegB hnonnegC, hgapAB, hgapAC, hgapBC, hcross]
  have htermAC : coefA * coefC = 0 := by
    nlinarith [mul_nonneg hnonnegA hnonnegB, mul_nonneg hnonnegA hnonnegC,
      mul_nonneg hnonnegB hnonnegC, hgapAB, hgapAC, hgapBC, hcross]
  have htermBC : coefB * coefC = 0 := by
    nlinarith [mul_nonneg hnonnegA hnonnegB, mul_nonneg hnonnegA hnonnegC,
      mul_nonneg hnonnegB hnonnegC, hgapAB, hgapAC, hgapBC, hcross]
  -- at most one coefficient survives, and the sum forces it to be one
  rcases eq_or_ne coefA 0 with hzeroA | hposA
  · rcases eq_or_ne coefB 0 with hzeroB | hposB
    · -- only C survives
      refine Or.inr (Or.inr ?_)
      have hone : coefC = 1 := by rw [hzeroA, hzeroB] at hsum; linarith
      rw [hcombo, hzeroA, hzeroB, hone, zero_smul, zero_smul, one_smul,
        zero_add, zero_add]
    · -- only B survives
      refine Or.inr (Or.inl ?_)
      have hzeroC : coefC = 0 := by
        rcases mul_eq_zero.mp htermBC with hb | hc
        · exact absurd hb hposB
        · exact hc
      have hone : coefB = 1 := by rw [hzeroA, hzeroC] at hsum; linarith
      rw [hcombo, hzeroA, hzeroC, hone, zero_smul, zero_smul, one_smul,
        zero_add, add_zero]
  · -- only A survives
    refine Or.inl ?_
    have hzeroB : coefB = 0 := by
      rcases mul_eq_zero.mp htermAB with ha | hb
      · exact absurd ha hposA
      · exact hb
    have hzeroC : coefC = 0 := by
      rcases mul_eq_zero.mp htermAC with ha | hc
      · exact absurd ha hposA
      · exact hc
    have hone : coefA = 1 := by rw [hzeroB, hzeroC] at hsum; linarith
    rw [hcombo, hzeroB, hzeroC, hone, zero_smul, zero_smul, one_smul,
      add_zero, add_zero]

end Gtz
