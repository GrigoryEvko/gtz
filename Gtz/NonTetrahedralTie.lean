/-
# A tie whose atoms are not a rotated regular tetrahedron

The `(4,3)` design with atoms

    g₀ = (2, 2, 2)/3,  g₁ = (2, 2, −7)/3,  g₂ = (−7, 2, 2)/3,  g₃ = (2, −7, 2)/3

and weights `(2/3, 1/9, 1/9, 1/9)` is an exact tie (`sharpDesign_isTie`): the subset
`{1,2,3}` dominates weakly — its gap is `(8/3)[(x₀−x₁)² + (x₀−x₂)² + (x₁−x₂)²]` — and
each of the four 3-subsets has an explicit null direction, `(1,1,1)`, `(1,1,4)`,
`(4,1,1)`, `(1,4,1)` respectively, so none dominates strictly.

Its leverages are `4/3, 19/3, 19/3, 19/3` — NOT all equal, while the regular
tetrahedron's are all `3`. Since an orthogonal image preserves leverage
(`leverageOf_orthogonal_image`), this tie is not a rotated, relabelled regular
tetrahedron (`sharpDesign_not_rotated_tetrahedron`): exact ties are a genuinely wider
family than the simplex orbit, already at four atoms, and they occur at strongly
non-uniform weights.

The design sits on the corank-one tie criterion: with the atom dependency
`3g₀ + 2g₁ + 2g₂ + 2g₃ = 0` (`sharpDesign_dependency`) the quantity
`y_c²/(t_c(1 − t_c))` equals `81/2` at every atom.
-/
import Mathlib
import Gtz.Basic
import Gtz.LeverageBound
import Gtz.PsdKit
import Gtz.RayleighCertificate
import Gtz.ResidueDissolution
import Gtz.Sanity
import Gtz.SplitTetrahedronTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-- The four atoms: one short vector along `(1,1,1)` carrying most of the weight, and
three long ones. -/
noncomputable def sharpAtom : Fin 4 → Fin 3 → ℝ :=
  ![![2/3, 2/3, 2/3], ![2/3, 2/3, -7/3], ![-7/3, 2/3, 2/3], ![2/3, -7/3, 2/3]]

/-- The `(4,3)` design with strongly non-uniform weights `(2/3, 1/9, 1/9, 1/9)`. -/
noncomputable def sharpDesign : WeightedDesign 4 3 where
  atom := sharpAtom
  weight := ![2/3, 1/9, 1/9, 1/9]
  weight_pos := by
    intro c
    fin_cases c
    · exact (by norm_num : (0 : ℝ) < 2/3)
    · exact (by norm_num : (0 : ℝ) < 1/9)
    · exact (by norm_num : (0 : ℝ) < 1/9)
    · exact (by norm_num : (0 : ℝ) < 1/9)
  weight_sum_one := by
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_four, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    fin_cases i <;> fin_cases j <;> simp [sharpAtom] <;> ring

@[simp] theorem sharpDesign_atom : sharpDesign.atom = sharpAtom := rfl

@[simp] theorem sharpDesign_weight :
    sharpDesign.weight = ![2/3, 1/9, 1/9, 1/9] := rfl

/-- The atoms carry the dependency `3g₀ + 2g₁ + 2g₂ + 2g₃ = 0` — the unique linear
relation among four vectors spanning `ℝ³`. -/
theorem sharpDesign_dependency :
    (3 : ℝ) • sharpAtom 0 + (2 : ℝ) • sharpAtom 1 + (2 : ℝ) • sharpAtom 2
      + (2 : ℝ) • sharpAtom 3 = 0 := by
  funext i
  fin_cases i <;> simp [sharpAtom] <;> ring

/-! ### The four 3-subsets and their null directions -/

private theorem vec_ne_zero (a b c : ℝ) (ha : a ≠ 0) : (![a, b, c] : Fin 3 → ℝ) ≠ 0 :=
  fun hzero => ha (by simpa using congrFun hzero 0)

private theorem card_three_cases :
    ∀ C : Finset (Fin 4), C.card = 3 →
      C = {1, 2, 3} ∨ C = {0, 2, 3} ∨ C = {0, 1, 3} ∨ C = {0, 1, 2} := by
  decide

/-- **The subset `{1,2,3}` dominates weakly** — its gap is
`(8/3)[(x₀−x₁)² + (x₀−x₂)² + (x₁−x₂)²]`. -/
theorem sharpDesign_dominates : Dominates sharpDesign {1, 2, 3} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · exact ((Matrix.posSemidef_sum ({1, 2, 3} : Finset (Fin 4)) fun c _ =>
      posSemidef_atomMatrix (sharpDesign.atom c)).1).sub Matrix.isHermitian_one
  · rw [star_trivial, dominationGap_form,
      show ({1, 2, 3} : Finset (Fin 4)) = insert 1 (insert 2 {3}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp only [sharpDesign_atom, sharpAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2)]

/-- **No 3-subset dominates strictly**: each of the four has an explicit null
direction of its gap form. -/
theorem sharpDesign_no_strictDominator :
    ∀ C : Finset (Fin 4), C.card = 3 → ¬(subsetSum sharpDesign C - 1).PosDef := by
  intro C hcard hpd
  rcases card_three_cases C hcard with rfl | rfl | rfl | rfl
  · have hzero : (![1, 1, 1] : Fin 3 → ℝ) ⬝ᵥ
        ((subsetSum sharpDesign {1, 2, 3} - 1) *ᵥ ![1, 1, 1]) = 0 := by
      rw [dominationGap_form,
        show ({1, 2, 3} : Finset (Fin 4)) = insert 1 (insert 2 {3}) from rfl,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
      simp only [sharpDesign_atom, sharpAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
        dotProduct, Fin.sum_univ_three]
      norm_num
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2
      (vec_ne_zero 1 1 1 one_ne_zero)
    rw [star_trivial, hzero] at hpos
    exact lt_irrefl 0 hpos
  · have hzero : (![1, 1, 4] : Fin 3 → ℝ) ⬝ᵥ
        ((subsetSum sharpDesign {0, 2, 3} - 1) *ᵥ ![1, 1, 4]) = 0 := by
      rw [dominationGap_form,
        show ({0, 2, 3} : Finset (Fin 4)) = insert 0 (insert 2 {3}) from rfl,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
      simp only [sharpDesign_atom, sharpAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
        dotProduct, Fin.sum_univ_three]
      norm_num
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2
      (vec_ne_zero 1 1 4 one_ne_zero)
    rw [star_trivial, hzero] at hpos
    exact lt_irrefl 0 hpos
  · have hzero : (![4, 1, 1] : Fin 3 → ℝ) ⬝ᵥ
        ((subsetSum sharpDesign {0, 1, 3} - 1) *ᵥ ![4, 1, 1]) = 0 := by
      rw [dominationGap_form,
        show ({0, 1, 3} : Finset (Fin 4)) = insert 0 (insert 1 {3}) from rfl,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
      simp only [sharpDesign_atom, sharpAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
        dotProduct, Fin.sum_univ_three]
      norm_num
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2
      (vec_ne_zero 4 1 1 (by norm_num))
    rw [star_trivial, hzero] at hpos
    exact lt_irrefl 0 hpos
  · have hzero : (![1, 4, 1] : Fin 3 → ℝ) ⬝ᵥ
        ((subsetSum sharpDesign {0, 1, 2} - 1) *ᵥ ![1, 4, 1]) = 0 := by
      rw [dominationGap_form,
        show ({0, 1, 2} : Finset (Fin 4)) = insert 0 (insert 1 {2}) from rfl,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
      simp only [sharpDesign_atom, sharpAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
        dotProduct, Fin.sum_univ_three]
      norm_num
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2
      (vec_ne_zero 1 4 1 one_ne_zero)
    rw [star_trivial, hzero] at hpos
    exact lt_irrefl 0 hpos

/-- **The design is an exact tie.** -/
theorem sharpDesign_isTie : IsTie sharpDesign :=
  ⟨⟨{1, 2, 3}, by decide, sharpDesign_dominates⟩, sharpDesign_no_strictDominator⟩

/-! ### The tie is not a rotated regular tetrahedron -/

theorem sharpDesign_leverage_zero : leverageOf (sharpDesign.atom 0) = 4/3 := by
  norm_num [sharpDesign_atom, sharpAtom, leverageOf, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem sharpDesign_leverage_one : leverageOf (sharpDesign.atom 1) = 19/3 := by
  norm_num [sharpDesign_atom, sharpAtom, leverageOf, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- Orthogonal images preserve leverage. -/
theorem leverageOf_orthogonal_image {R : Matrix (Fin 3) (Fin 3) ℝ} (hortho : Rᵀ * R = 1)
    (v : Fin 3 → ℝ) : leverageOf (R *ᵥ v) = leverageOf v := by
  have hback : Rᵀ *ᵥ (R *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hortho, Matrix.one_mulVec]
  rw [leverageOf_eq_dotProduct, leverageOf_eq_dotProduct,
    ← dotProduct_mulVec_transpose R (R *ᵥ v) v, hback]

/-- **The tie is not a rotated, relabelled regular tetrahedron.** Every tetrahedron
direction has leverage `3`, and an orthogonal image preserves leverage, whereas the
design's first atom has leverage `4/3`. -/
theorem sharpDesign_not_rotated_tetrahedron (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hortho : Rᵀ * R = 1) (relabel : Fin 4 → Fin 4) :
    sharpDesign.atom ≠ fun c => R *ᵥ tetraAtom (relabel c) := by
  intro hEq
  have hlev : leverageOf (sharpDesign.atom 0) = 3 := by
    rw [hEq, leverageOf_orthogonal_image hortho, leverageOf_eq_dotProduct,
      tetraAtom_dot_self]
  rw [sharpDesign_leverage_zero] at hlev
  norm_num at hlev

/-- **Exact ties are wider than the simplex orbit.** There is a `(4,3)` tie whose atom
leverages are not all equal — so no rotation and relabelling carries the regular
tetrahedron onto it. -/
theorem exists_isTie_leverages_unequal :
    ∃ D : WeightedDesign 4 3, IsTie D ∧
      leverageOf (D.atom 0) ≠ leverageOf (D.atom 1) :=
  ⟨sharpDesign, sharpDesign_isTie, by
    rw [sharpDesign_leverage_zero, sharpDesign_leverage_one]; norm_num⟩

end Gtz
