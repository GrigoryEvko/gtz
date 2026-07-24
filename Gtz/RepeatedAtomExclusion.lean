/-
# A 3-subset with a repeated atom never dominates

Two equal atoms leave a card-3 subset with at most two distinct vectors, whose moment
`S_C = 2·g gᵀ + h hᵀ` annihilates every direction orthogonal to both — and in `ℝ³` a
nonzero such direction always exists: the `3×3` matrix with rows `g, h, h` has a
repeated row, hence determinant zero, hence a nonzero kernel vector. At that direction
the gap form is `−|x|² < 0`, so `S_C − I` is not positive semidefinite: duplicated
atoms never dominate (`not_dominates_of_repeated_atom`), in particular never strictly
(`not_strictDominator_of_repeated_atom`).

This is the general form of the copy-pair exclusion at the split-tetrahedron ties:
every 3-subset an atom-splitting adds beyond the original ones contains both copies,
hence is inactive — splitting can never create a new dominator.
-/
import Mathlib
import Gtz.Basic
import Gtz.RayleighCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-- In `ℝ³` every pair of vectors has a nonzero common annihilator: the matrix with
rows `u, v, v` has a repeated row, hence determinant zero, hence a nonzero kernel
vector — which the first two rows pair to zero. -/
theorem exists_ne_zero_dotProduct_pair_eq_zero (u v : Fin 3 → ℝ) :
    ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ u ⬝ᵥ x = 0 ∧ v ⬝ᵥ x = 0 := by
  have hdet : (Matrix.of ![u, v, v]).det = 0 :=
    Matrix.det_zero_of_row_eq (show (1 : Fin 3) ≠ 2 by decide) rfl
  obtain ⟨x, hxne, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨x, hxne, ?_, ?_⟩
  · simpa [Matrix.mulVec, Matrix.of_apply] using congrFun hx 0
  · simpa [Matrix.mulVec, Matrix.of_apply] using congrFun hx 1

/-- **Duplicated atoms never dominate.** A 3-subset containing two atoms with the same
vector has moment of rank at most two: at a nonzero direction orthogonal to both
distinct vectors the gap form is `−|x|² < 0`. -/
theorem not_dominates_of_repeated_atom {m : ℕ} (D : WeightedDesign m 3)
    {cOne cTwo cThree : Fin m} (hOneTwo : cOne ≠ cTwo) (hOneThree : cOne ≠ cThree)
    (hTwoThree : cTwo ≠ cThree) (hatom : D.atom cOne = D.atom cTwo) :
    ¬ Dominates D {cOne, cTwo, cThree} := by
  intro hdom
  obtain ⟨x, hxne, hxOne, hxThree⟩ :=
    exists_ne_zero_dotProduct_pair_eq_zero (D.atom cOne) (D.atom cThree)
  have hxTwo : D.atom cTwo ⬝ᵥ x = 0 := by rw [← hatom]; exact hxOne
  have hxpos : 0 < x ⬝ᵥ x := by
    obtain ⟨coord, hcoord⟩ := Function.ne_iff.mp hxne
    have hsum : x ⬝ᵥ x = ∑ j, x j * x j := rfl
    rw [hsum]
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg (x j))
      ⟨coord, Finset.mem_univ coord, mul_self_pos.mpr (by simpa using hcoord)⟩
  have hnn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdom).2 x
  rw [star_trivial, dominationGap_form,
    Finset.sum_insert (by simp [hOneTwo, hOneThree]),
    Finset.sum_insert (by simp [hTwoThree]), Finset.sum_singleton,
    hxOne, hxTwo, hxThree] at hnn
  norm_num at hnn
  linarith

/-- **Duplicated atoms never dominate strictly** — the `IsTie`-facing form. -/
theorem not_strictDominator_of_repeated_atom {m : ℕ} (D : WeightedDesign m 3)
    {cOne cTwo cThree : Fin m} (hOneTwo : cOne ≠ cTwo) (hOneThree : cOne ≠ cThree)
    (hTwoThree : cTwo ≠ cThree) (hatom : D.atom cOne = D.atom cTwo) :
    ¬ (subsetSum D {cOne, cTwo, cThree} - 1).PosDef :=
  fun hpd => not_dominates_of_repeated_atom D hOneTwo hOneThree hTwoThree hatom
    hpd.posSemidef

end Gtz
