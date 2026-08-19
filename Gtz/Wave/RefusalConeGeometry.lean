import Gtz.Wave.RefusalDirectionSelector

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The refusal cone of a corank-two corner, and the exact obstruction to a short
selector

The complement triple of a corank-two corner carries refusal directions
(`Gtz.exists_refusal_direction`), and at a NON-PLANAR corner every one of them
reads the gap direction: the outside plane cover makes the complement gap
strictly positive on `u^⊥`, so a direction where it is nonpositive cannot be
orthogonal to `u` (`Gtz.refusal_reads_axis`).

The inside atoms of the corner read every direction with a fixed total
(`Gtz.inside_quadForm_of_rankOneGap`)

  `Σ_{c∈C} (g_c·z)² = |z|² + lam·(u·z)²` ,

because the inside atom sum IS `1 + lam·u uᵀ`.  Combining this with
`Gtz.ghostBlockShort_argmax_of_refusal` gives a floor on the selector's reading
(`Gtz.selector_reading_floor`): a short selector reads any refusal direction at
more than one third of the whole inside budget.

## The exact obstruction

The same argmax law gives the exact obstruction, and it is a TIE INSIDE THE
TIE.  A short ghost block at `e` makes `(g_e·z)²` strictly larger than the two
ghost readings, so the maximum of the inside readings at a refusal direction is
attained at `e` alone.  If two inside atoms read some refusal direction equally
hard, and that reading is the largest, then NO selector carries a short ghost
block (`Gtz.not_ghostBlockShort_of_tied_readings`).  That is exactly the
configuration a producer of `Gtz.NonplanarDeficitResidual` has to exclude.

The foil `Gtz.residualFoil` is a different matter: its complement triple
`{3,4,5}` dominates STRICTLY, so it carries no refusal direction at all, which
is why it is not a tie and why the tie is what the residual needs.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The quadratic form of an atom sum -/

/-- The quadratic form of a subset atom sum is the sum of the squared readings. -/
theorem subsetSum_quadForm_eq_sum_sq (D : WeightedDesign m 3) (T : Finset (Fin m))
    (z : Fin 3 → ℝ) :
    z ⬝ᵥ (subsetSum D T *ᵥ z) = ∑ c ∈ T, (D.atom c ⬝ᵥ z) ^ 2 := by
  rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => quadForm_atomMatrix (D.atom c) z

/-- **The inside reading budget.**  At a corank-two corner the inside atoms read
every direction with the total `|z|² + lam·(u·z)²`. -/
theorem inside_quadForm_of_rankOneGap (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (z : Fin 3 → ℝ) :
    ∑ c ∈ C, (D.atom c ⬝ᵥ z) ^ 2 = z ⬝ᵥ z + lam * (u ⬝ᵥ z) ^ 2 := by
  have hsum : subsetSum D C = 1 + lam • atomMatrix u := by
    rw [← hgap]; abel
  have h1 := subsetSum_quadForm_eq_sum_sq D C z
  rw [hsum, Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, show atomMatrix u = Matrix.vecMulVec u u from rfl,
    quadForm_atomMatrix] at h1
  exact h1.symm

/-! ## 2. Every refusal direction reads the gap direction -/

/-- **A refusal direction is never orthogonal to the gap direction.**  The
outside plane cover makes the complement gap strictly positive on `u^⊥`. -/
theorem refusal_reads_axis (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) (hne : Cᶜ.Nonempty) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {z : Fin 3 → ℝ} (hz : z ≠ 0)
    (hrefuse : z ⬝ᵥ ((subsetSum D Cᶜ - 1) *ᵥ z) ≤ 0) : z ⬝ᵥ u ≠ 0 := by
  intro hzu
  have hcover := outside_plane_cover_of_rankOneGap D C hcard hne hlam hunit hgap hzu hz
  have hquad := subsetSum_quadForm_eq_sum_sq D Cᶜ z
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hquad] at hrefuse
  linarith

/-! ## 3. The floor on the selector's reading -/

/-- **A short selector reads more than a third of the inside budget.** -/
theorem selector_reading_floor (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e f h : Fin 6} (he : e ∈ C) (hfh : f ≠ h) (herase : C.erase e = {f, h})
    (hshort : GhostBlockShort D f h) {z : Fin 3 → ℝ} (hz : z ≠ 0)
    (hrefuse : z ⬝ᵥ ((subsetSum D Cᶜ - 1) *ᵥ z) ≤ 0) :
    z ⬝ᵥ z + lam * (u ⬝ᵥ z) ^ 2 < 3 * (D.atom e ⬝ᵥ z) ^ 2 := by
  classical
  obtain ⟨hf, hh⟩ := ghostBlockShort_argmax_of_refusal D C he hfh herase hshort hz hrefuse
  have hbudget := inside_quadForm_of_rankOneGap D C hgap z
  have hsplit : ∑ c ∈ C, (D.atom c ⬝ᵥ z) ^ 2
      = (D.atom e ⬝ᵥ z) ^ 2 + ((D.atom f ⬝ᵥ z) ^ 2 + (D.atom h ⬝ᵥ z) ^ 2) := by
    rw [← Finset.add_sum_erase C _ he, herase,
      Finset.sum_insert (by simp [hfh]), Finset.sum_singleton]
  rw [hsplit] at hbudget
  linarith

/-! ## 4. The exact obstruction -/

/-- **A tie among the inside readings kills every selector.**  A short ghost
block makes its selector the strict maximiser of the inside readings at a
refusal direction, so a maximum attained twice leaves no selector at all. -/
theorem not_ghostBlockShort_of_tied_readings (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) {a b : Fin 6} (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b)
    {z : Fin 3 → ℝ} (hz : z ≠ 0)
    (hrefuse : z ⬝ᵥ ((subsetSum D Cᶜ - 1) *ᵥ z) ≤ 0)
    (htied : (D.atom a ⬝ᵥ z) ^ 2 = (D.atom b ⬝ᵥ z) ^ 2)
    (hmax : ∀ c ∈ C, (D.atom c ⬝ᵥ z) ^ 2 ≤ (D.atom a ⬝ᵥ z) ^ 2)
    {e f h : Fin 6} (he : e ∈ C) (hfh : f ≠ h) (herase : C.erase e = {f, h})
    (hshort : GhostBlockShort D f h) : False := by
  classical
  obtain ⟨hf, hh⟩ := ghostBlockShort_argmax_of_refusal D C he hfh herase hshort hz hrefuse
  -- the selector strictly beats both ghosts, so it beats every other inside atom
  have hbeat : ∀ c ∈ C, c ≠ e → (D.atom c ⬝ᵥ z) ^ 2 < (D.atom e ⬝ᵥ z) ^ 2 := by
    intro c hc hce
    have hmem : c ∈ C.erase e := Finset.mem_erase.mpr ⟨hce, hc⟩
    rw [herase] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hf
    · exact hh
  -- one of `a`, `b` differs from `e`, and it is a strict maximiser, a contradiction
  rcases eq_or_ne a e with rfl | hae
  · have := hbeat b hb (Ne.symm hab)
    linarith
  · have h1 := hbeat a ha hae
    have h2 := hmax e he
    linarith

end Gtz
