/-
# The Gordan alternative: convex balance or a uniformly negative functional

The frame-existence germ of the certificate frame (the p4c5 audit's D4: the
one step of the zero-set classification that was still a hand proof). For any
finite family in a real normed space, EITHER zero is a convex combination of
the family — the Gordan multipliers that seed the stress system — OR some
continuous linear functional is strictly negative on every member — the
slack-decreasing direction whose impossibility at an equality design is
exactly what `gtz_rank_two` supplies.

Fully generic: no inner product, no completeness, no dimension. The left
branch extracts per-index weights from the abstract hull membership by
fiberwise summation over a chosen index map; the right branch is geometric
Hahn–Banach separation of the point from the (closed, finite-generated) hull,
negated.
-/
import Mathlib

namespace Gtz

open Finset

/-- **The Gordan alternative**: for a finite family in a real normed space,
either zero is a convex combination of the family, or some continuous linear
functional is strictly negative at every member. -/
theorem gordan_alternative {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (family : Fin n → E) :
    (∃ coeff : Fin n → ℝ, (∀ i, 0 ≤ coeff i) ∧ ∑ i, coeff i = 1
        ∧ ∑ i, coeff i • family i = 0)
      ∨ ∃ functional : E →L[ℝ] ℝ, ∀ i, functional (family i) < 0 := by
  by_cases hmem : (0 : E) ∈ convexHull ℝ (Set.range family)
  · -- zero is in the hull: extract per-index convex weights
    left
    obtain ⟨indexType, indexFintype, w, member, hwNonneg, hwSum, hmemRange,
      hcombination⟩ := mem_convexHull_iff_exists_fintype.mp hmem
    letI := indexFintype
    choose pick hpick using fun i => Set.mem_range.mp (hmemRange i)
    refine ⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => pick i = j), w i,
      fun j => Finset.sum_nonneg fun i _ => hwNonneg i, ?_, ?_⟩
    · rw [Finset.sum_fiberwise Finset.univ pick w]
      exact hwSum
    · calc ∑ j, (∑ i ∈ Finset.univ.filter (fun i => pick i = j), w i)
            • family j
          = ∑ j, ∑ i ∈ Finset.univ.filter (fun i => pick i = j),
              w i • family (pick i) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_smul]
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [(Finset.mem_filter.mp hi).2]
        _ = ∑ i, w i • family (pick i) :=
            Finset.sum_fiberwise Finset.univ pick
              (fun i => w i • family (pick i))
        _ = ∑ i, w i • member i :=
            Finset.sum_congr rfl fun i _ => by rw [hpick i]
        _ = 0 := hcombination
  · -- zero is outside the (closed) hull: separate and negate
    right
    have hclosed : IsClosed (convexHull ℝ (Set.range family)) :=
      Set.Finite.isClosed_convexHull ℝ (Set.finite_range family)
    obtain ⟨functional, gap, hatZero, honHull⟩ :=
      geometric_hahn_banach_point_closed
        (convex_convexHull ℝ (Set.range family)) hclosed hmem
    have hgapPos : 0 < gap := by
      have hzero := hatZero
      rw [map_zero] at hzero
      exact hzero
    refine ⟨-functional, fun i => ?_⟩
    have hmemberHull : family i ∈ convexHull ℝ (Set.range family) :=
      subset_convexHull ℝ _ (Set.mem_range_self i)
    have hpositive := honHull (family i) hmemberHull
    simp only [ContinuousLinearMap.neg_apply]
    linarith

/-- **The Gordan alternative in the repo's dot-product vocabulary**: for a
finite family of vectors, either zero is a convex combination, or some probe
vector has strictly negative overlap with every member — Riesz representation
of the separating functional through `EuclideanSpace`. -/
theorem gordan_alternative_dotProduct {n k : ℕ}
    (family : Fin n → (Fin k → ℝ)) :
    (∃ coeff : Fin n → ℝ, (∀ i, 0 ≤ coeff i) ∧ ∑ i, coeff i = 1
        ∧ ∑ i, coeff i • family i = 0)
      ∨ ∃ probe : Fin k → ℝ, ∀ i, family i ⬝ᵥ probe < 0 := by
  rcases gordan_alternative
      (fun i => (WithLp.toLp 2 (family i) : EuclideanSpace ℝ (Fin k))) with
    ⟨coeff, hnonneg, hsum, hcombination⟩ | ⟨functional, hneg⟩
  · left
    refine ⟨coeff, hnonneg, hsum, ?_⟩
    have hpush := congrArg
      (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)) hcombination
    rwa [map_sum, map_zero] at hpush
  · right
    set rieszVec :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm functional
      with hrieszVec
    refine ⟨rieszVec.ofLp, fun i => ?_⟩
    have hrepresent := InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin k)) (y := functional)
      (x := WithLp.toLp 2 (family i))
    have hdot := EuclideanSpace.inner_eq_star_dotProduct
      rieszVec (WithLp.toLp 2 (family i) : EuclideanSpace ℝ (Fin k))
    rw [← hrieszVec] at hrepresent
    rw [hrepresent] at hdot
    have hstar : star rieszVec.ofLp = rieszVec.ofLp := by
      funext index
      simp
    rw [WithLp.ofLp_toLp, hstar] at hdot
    rw [← hdot]
    exact hneg i

end Gtz
