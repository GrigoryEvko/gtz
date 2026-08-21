/-
# The resolvent block criterion: domination with the weights removed

`Gtz/Wave/ResolventProjectionLaw.lean` proves that the resolvent readings
`Pi a b = g_a ⬝ᵥ (W⁻¹ *ᵥ g_b)` of the full excess `W = subsetSum D univ - 1`
satisfy `Pi · diag(1 - t) · Pi = Pi`, and records in its own docstring what that
law is FOR: a subset dominates exactly when the principal block of `Pi` on the
complement sits below the identity.  That criterion was measured but not proved,
because the step it needs -- transferring a Loewner bound from `Nᵀ N` to
`N W⁻¹ Nᵀ` -- had no theorem behind it.

This module proves the criterion.  The general statement is
`Gtz.posSemidef_sub_atomSum_iff_resolventForm`:

  **`W ≻ 0`  implies
   `W - Σ_{c ∈ S} g_c g_cᵀ ⪰ 0`  ⟺  `Σ_{c ∈ S} y_c g_c` reads `W⁻¹` at most
   `Σ_{c ∈ S} y_c²`, for every coefficient vector `y`.**

The right side is the quadratic form of the principal block `Pi[S, S]` against
the identity, written without any submatrix.  At a design, with `S` the
complement of a selection, it is `Gtz.dominates_iff_resolventForm_le`:

  **`Dominates D C  ⟺  Σ_{a,b ∈ Cᶜ} y_a y_b · Pi a b  ≤  Σ_{a ∈ Cᶜ} y_a²`
   for every `y`.**

## No weights survive inside the block

This is the point.  The landed `Gtz.dominates_iff_posSemidef_projectionBlock`
reads domination off `V Vᵀ` with `diag(t)` on the other side, so the weights sit
in the statement twice: once inside `V` and once beside the block.  Here they
sit only inside `W`.  The block condition itself compares `Pi[S,S]` with the
IDENTITY, and no weight appears in it.  Everything the design knows has been
pushed into one matrix.

At `(6,3)` the complement of a triple is a triple, so
`Gtz.gtzWeighted_six_three_iff_resolventBlock` reads:

  **`GtzWeighted 6 3` holds iff every design has a triple `T` with
   `Pi[T, T] ⪯ 1`.**

## The proof is one Cauchy-Schwarz, used twice

`Gtz.quadForm_mixed_le_of_posDef` pairs the form of `W` against the form of its
inverse: `(a ⬝ᵥ b)² ≤ (a ⬝ᵥ W a)·(b ⬝ᵥ W⁻¹ b)`.  It follows from the landed
`Gtz.quadForm_sq_le_mul_of_posSemidef` applied at `a` and `W⁻¹ b`, because `W`
cancels one resolvent.  Both directions of the criterion are then the same three
lines: name the quantity `Q` that appears on both sides, bound `Q²` by `(the
other side)·Q`, and divide -- the case `Q = 0` being immediate.  Neither
direction inverts anything else, and no matrix square root appears.

[MEASURED before proving.  The harness reproduces the `(5,3)` diamond exactly:
leverages `(2, 13/4, 13/4, 13/4, 13/4)`, pair minors `{0.75, 2.0, 4.5}`, eight
of ten dominating triples.  The criterion was then checked with ZERO mismatches
on 15960 subsets -- `(6,3)` 4000, `(5,3)` 1500, `(7,3)` 3500, `(6,4)` 1500,
`(5,2)` 1500, `(4,3)` 600, `(8,3)` 3360 -- with `|Pi - Piᵀ| ≤ 2.9e-15` and
`|Pi·diag(1-t)·Pi - Pi| ≤ 1.8e-14` throughout.]
-/
import Gtz.Wave.ResolventProjectionLaw
import Gtz.Reduction.StrengthenedInductionHypothesis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. Cauchy-Schwarz across a form and its inverse -/

/-- **THE MIXED CAUCHY-SCHWARZ.**  A positive definite form and its inverse
split the plain pairing between them.  The landed
`Gtz.quadForm_sq_le_mul_of_posSemidef` supplies it once the second probe is
routed through the resolvent, because the form then cancels one inverse. -/
theorem quadForm_mixed_le_of_posDef {W : Matrix (Fin k) (Fin k) ℝ} (hW : W.PosDef)
    (a b : Fin k → ℝ) :
    (a ⬝ᵥ b) ^ 2 ≤ (a ⬝ᵥ (W *ᵥ a)) * (b ⬝ᵥ (W⁻¹ *ᵥ b)) := by
  have hdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det _).mp hW.isUnit
  have hcancel : W *ᵥ (W⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hCS := quadForm_sq_le_mul_of_posSemidef hW.posSemidef a (W⁻¹ *ᵥ b)
  rw [hcancel] at hCS
  have hfirst : (W⁻¹ *ᵥ b) ⬝ᵥ b = b ⬝ᵥ (W⁻¹ *ᵥ b) := dotProduct_comm _ _
  rw [hfirst] at hCS
  calc (a ⬝ᵥ b) ^ 2 ≤ (b ⬝ᵥ (W⁻¹ *ᵥ b)) * (a ⬝ᵥ (W *ᵥ a)) := hCS
    _ = (a ⬝ᵥ (W *ᵥ a)) * (b ⬝ᵥ (W⁻¹ *ᵥ b)) := mul_comm _ _

/-! ## 2. A weighted atom sum, read at a probe -/

/-- A sum of rank-one atoms sends a probe to the combination of those atoms with
the probe's own readings as coefficients. -/
theorem atomSum_mulVec (S : Finset (Fin m)) (g : Fin m → (Fin k → ℝ)) (x : Fin k → ℝ) :
    (∑ c ∈ S, atomMatrix (g c)) *ᵥ x = ∑ c ∈ S, (g c ⬝ᵥ x) • g c := by
  rw [Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun c _ => by rw [atomMatrix, vecMulVec_mulVec_eq]

/-- The quadratic form of a sum of rank-one atoms totals the squared readings. -/
theorem atomSumForm (S : Finset (Fin m)) (g : Fin m → (Fin k → ℝ)) (x : Fin k → ℝ) :
    x ⬝ᵥ ((∑ c ∈ S, atomMatrix (g c)) *ᵥ x) = ∑ c ∈ S, (g c ⬝ᵥ x) ^ 2 := by
  rw [atomSum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm x (g c)]; ring

/-- A sum of rank-one atoms is symmetric. -/
theorem atomSum_transpose (S : Finset (Fin m)) (g : Fin m → (Fin k → ℝ)) :
    (∑ c ∈ S, atomMatrix (g c))ᵀ = ∑ c ∈ S, atomMatrix (g c) := by
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ext i j
  simp [atomMatrix, Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]

/-- The scalar Cauchy-Schwarz over a finite index set, in the squared form the
two transfers below consume. -/
theorem sum_mul_sq_le (S : Finset (Fin m)) (f h : Fin m → ℝ) :
    (∑ c ∈ S, f c * h c) ^ 2 ≤ (∑ c ∈ S, f c ^ 2) * (∑ c ∈ S, h c ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S f h
  nlinarith [hcs]

/-! ## 3. The transfer

Both directions name a quantity that appears on both sides of a Cauchy-Schwarz
step, bound its square by the other side times itself, and divide. -/

/-- **THE RESOLVENT BLOCK CRITERION.**  A positive definite form dominates a sum
of rank-one atoms exactly when the atoms read the form's INVERSE at most as
loudly as their own coefficients.  No square root and no submatrix: the right
side is the quadratic form of the block `Pi[S, S]` against the identity, and no
weight appears in it. -/
theorem posSemidef_sub_atomSum_iff_resolventForm {W : Matrix (Fin k) (Fin k) ℝ}
    (hW : W.PosDef) (S : Finset (Fin m)) (g : Fin m → (Fin k → ℝ)) :
    (W - ∑ c ∈ S, atomMatrix (g c)).PosSemidef
      ↔ ∀ y : Fin m → ℝ,
          (∑ c ∈ S, y c • g c) ⬝ᵥ (W⁻¹ *ᵥ (∑ c ∈ S, y c • g c))
            ≤ ∑ c ∈ S, (y c) ^ 2 := by
  have hdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det _).mp hW.isUnit
  have hWsymm : Wᵀ = W := transpose_eq_of_isHermitian hW.1
  have hsymm : (W - ∑ c ∈ S, atomMatrix (g c))ᵀ = W - ∑ c ∈ S, atomMatrix (g c) := by
    rw [Matrix.transpose_sub, hWsymm, atomSum_transpose]
  rw [posSemidef_iff_quadForm_nonneg _ hsymm]
  constructor
  · -- domination gives the block bound
    intro hgap y
    set v : Fin k → ℝ := ∑ c ∈ S, y c • g c with hv
    set z : Fin k → ℝ := W⁻¹ *ᵥ v with hz
    have hWz : W *ᵥ z = v := by
      rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have hQ : v ⬝ᵥ z = z ⬝ᵥ (W *ᵥ z) := by rw [hWz, dotProduct_comm]
    have hQ0 : 0 ≤ v ⬝ᵥ z := by
      rw [hQ]
      exact quadForm_nonneg_of_posSemidef hW.posSemidef z
    -- the atoms read the resolvent image at most as loudly as the form does
    have hread : ∑ c ∈ S, (g c ⬝ᵥ z) ^ 2 ≤ v ⬝ᵥ z := by
      have hstep := hgap z
      rw [Matrix.sub_mulVec, dotProduct_sub, atomSumForm] at hstep
      rw [hQ]; linarith
    -- the pairing is the same quantity, read through the coefficients
    have hpair : v ⬝ᵥ z = ∑ c ∈ S, y c * (g c ⬝ᵥ z) := by
      rw [hv, sum_dotProduct]
      exact Finset.sum_congr rfl fun c _ => by rw [smul_dotProduct, smul_eq_mul]
    have hCS := sum_mul_sq_le S y (fun c => g c ⬝ᵥ z)
    rw [← hpair] at hCS
    have hy0 : 0 ≤ ∑ c ∈ S, (y c) ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
    rcases eq_or_lt_of_le hQ0 with hzero | hpos
    · rw [← hzero]; exact hy0
    · nlinarith [hCS, hread, hpos, hy0]
  · -- the block bound gives domination
    intro hblock x
    set R : ℝ := ∑ c ∈ S, (g c ⬝ᵥ x) ^ 2 with hR
    set v : Fin k → ℝ := ∑ c ∈ S, (g c ⬝ᵥ x) • g c with hv
    have hAx : (∑ c ∈ S, atomMatrix (g c)) *ᵥ x = v := atomSum_mulVec S g x
    have hxv : x ⬝ᵥ v = R := by rw [← hAx, atomSumForm]
    have hR0 : 0 ≤ R := Finset.sum_nonneg fun c _ => sq_nonneg _
    have hWx0 : 0 ≤ x ⬝ᵥ (W *ᵥ x) := quadForm_nonneg_of_posSemidef hW.posSemidef x
    have hres : v ⬝ᵥ (W⁻¹ *ᵥ v) ≤ R := by
      have := hblock (fun c => g c ⬝ᵥ x)
      rwa [← hv, ← hR] at this
    have hres0 : 0 ≤ v ⬝ᵥ (W⁻¹ *ᵥ v) :=
      quadForm_nonneg_of_posSemidef hW.inv.posSemidef v
    have hCS := quadForm_mixed_le_of_posDef hW x v
    rw [hxv] at hCS
    rw [Matrix.sub_mulVec, dotProduct_sub, hAx, hxv]
    rcases eq_or_lt_of_le hR0 with hzero | hpos
    · rw [← hzero]; linarith
    · nlinarith [hCS, hres, hpos, hWx0]

/-! ## 4. The criterion at a design -/

/-- The full excess splits off a selection: what the complement does not carry,
the selection's own gap does. -/
theorem fullExcess_sub_subsetSum_compl (D : WeightedDesign m k) (C : Finset (Fin m)) :
    (subsetSum D Finset.univ - 1) - subsetSum D Cᶜ = subsetSum D C - 1 := by
  have hsplit : subsetSum D C + subsetSum D Cᶜ = subsetSum D Finset.univ := by
    rw [subsetSum, subsetSum, subsetSum, Finset.sum_add_sum_compl]
  rw [← hsplit]; abel

/-- The resolvent form of a coefficient vector, expanded into the landed
readings `Gtz.resolventReading`. -/
theorem resolventForm_eq_sum (D : WeightedDesign m k) (S : Finset (Fin m))
    (y : Fin m → ℝ) :
    (∑ c ∈ S, y c • D.atom c)
        ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ (∑ c ∈ S, y c • D.atom c))
      = ∑ a ∈ S, ∑ b ∈ S, y a * y b * resolventReading D a b := by
  rw [Matrix.mulVec_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_dotProduct, smul_eq_mul, dotProduct_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, resolventReading]
  ring

/-- **DOMINATION IS A BLOCK OF THE READING MATRIX.**  A selection dominates
exactly when the principal block of the resolvent readings on its COMPLEMENT
sits below the identity.  The weights have left the condition entirely: they
survive only inside the resolvent. -/
theorem dominates_iff_resolventForm_le (D : WeightedDesign m k) (hm : 2 ≤ m)
    (C : Finset (Fin m)) :
    Dominates D C
      ↔ ∀ y : Fin m → ℝ,
          (∑ a ∈ Cᶜ, ∑ b ∈ Cᶜ, y a * y b * resolventReading D a b)
            ≤ ∑ a ∈ Cᶜ, (y a) ^ 2 := by
  have hgap : subsetSum D C - 1
      = (subsetSum D Finset.univ - 1) - ∑ c ∈ Cᶜ, atomMatrix (D.atom c) :=
    (fullExcess_sub_subsetSum_compl D C).symm
  rw [Dominates, hgap,
    posSemidef_sub_atomSum_iff_resolventForm (posDef_fullExcess D hm) Cᶜ D.atom]
  exact forall_congr' fun y => by rw [resolventForm_eq_sum D Cᶜ y]

/-- The same criterion read on the selection itself rather than its complement:
a subset whose own reading block sits below the identity is the complement of a
dominating selection. -/
theorem dominates_compl_iff_resolventForm_le (D : WeightedDesign m k) (hm : 2 ≤ m)
    (S : Finset (Fin m)) :
    Dominates D Sᶜ
      ↔ ∀ y : Fin m → ℝ,
          (∑ a ∈ S, ∑ b ∈ S, y a * y b * resolventReading D a b)
            ≤ ∑ a ∈ S, (y a) ^ 2 := by
  rw [dominates_iff_resolventForm_le D hm Sᶜ, compl_compl]

/-! ## 5. The `(6,3)` reading -/

/-- **THE `(6,3)` FRONTIER AS A BLOCK QUESTION.**  Weighted GTZ at six points and
rank three holds exactly when every design carries three labels whose principal
block of resolvent readings sits below the identity.

Every trace of the design has been pushed into one matrix: the statement
compares a three by three block with the IDENTITY, and no weight, no leverage
and no pair minor appears in it. -/
theorem gtzWeighted_six_three_iff_resolventBlock :
    GtzWeighted 6 3
      ↔ ∀ D : WeightedDesign 6 3, ∃ S : Finset (Fin 6), S.card = 3 ∧
          ∀ y : Fin 6 → ℝ,
            (∑ a ∈ S, ∑ b ∈ S, y a * y b * resolventReading D a b)
              ≤ ∑ a ∈ S, (y a) ^ 2 := by
  constructor
  · intro hgtz D
    obtain ⟨C, hcard, hdom⟩ := hgtz D
    refine ⟨Cᶜ, card_compl_three_of_card_three _ hcard, ?_⟩
    exact (dominates_iff_resolventForm_le D (by norm_num) C).mp hdom
  · intro hblock D
    obtain ⟨S, hcard, hS⟩ := hblock D
    refine ⟨Sᶜ, card_compl_three_of_card_three _ hcard, ?_⟩
    exact (dominates_compl_iff_resolventForm_le D (by norm_num) S).mpr hS

end Gtz
