/-
# The wedge-bracket tax: the tie law in the invariant arena

The block tax of `Gtz.InvariantTaxTeeth` prices a projection block by its
determinant and second invariant.  This module translates the two sides into
the design invariants:

* the block determinant is the weighted squared bracket
  `t_a t_b t_c·[abc]²`;
* the block second invariant is the weighted wedge mass
  `t_at_b·w_{ab} + t_at_c·w_{ac} + t_bt_c·w_{bc}` with
  `w_{xy} = |g_x|²|g_y|² − ⟨g_x,g_y⟩²` the squared pair wedge.

THE WEDGE-BRACKET TAX: at every triple of a `(m,3)` tie with positive wedge
mass, some member weight `t` satisfies

  `t_a t_b t_c·[abc]² ≤ t·(t_at_b w_{ab} + t_at_c w_{ac} + t_bt_c w_{bc})` .

The producer twin: a triple whose EVERY member weight violates the bound
dominates strictly.  Both sides are polynomial in the currencies of the
hinge — the wedge `w_{xy}` vanishes exactly at a parallel pair, and the
bracket vanishes on the stress conics.  Primitivity is `w > 0` everywhere.
-/
import Gtz.Wave.InvariantTaxTeeth
import Gtz.Design.PrimitiveTightClassification
import Gtz.Quantitative.SixThreeCruxSigns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The two pure scaled-Gram laws -/

set_option linter.unusedSimpArgs false in
/-- The determinant of a scaled Gram is the squared scale product times the
squared bracket. -/
theorem det_scaledGram (sa sb sc : ℝ) (ga gb gc : Fin 3 → ℝ) :
    (Matrix.of ![![sa*sa*(ga ⬝ᵥ ga), sa*sb*(ga ⬝ᵥ gb), sa*sc*(ga ⬝ᵥ gc)],
        ![sb*sa*(gb ⬝ᵥ ga), sb*sb*(gb ⬝ᵥ gb), sb*sc*(gb ⬝ᵥ gc)],
        ![sc*sa*(gc ⬝ᵥ ga), sc*sb*(gc ⬝ᵥ gb), sc*sc*(gc ⬝ᵥ gc)]]).det
      = (sa*sa) * ((sb*sb) * ((sc*sc) * tripleBracket ga gb gc ^ 2)) := by
  simp only [Matrix.det_fin_three, tripleBracket_eq, dotProduct,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  ring

set_option linter.unusedSimpArgs false in
/-- The second invariant of a scaled Gram is the scaled wedge mass. -/
theorem e2_scaledGram (sa sb sc : ℝ) (ga gb gc : Fin 3 → ℝ) :
    (((Matrix.trace (Matrix.of ![![sa*sa*(ga ⬝ᵥ ga), sa*sb*(ga ⬝ᵥ gb), sa*sc*(ga ⬝ᵥ gc)],
          ![sb*sa*(gb ⬝ᵥ ga), sb*sb*(gb ⬝ᵥ gb), sb*sc*(gb ⬝ᵥ gc)],
          ![sc*sa*(gc ⬝ᵥ ga), sc*sb*(gc ⬝ᵥ gb), sc*sc*(gc ⬝ᵥ gc)]]))^2
      - Matrix.trace ((Matrix.of ![![sa*sa*(ga ⬝ᵥ ga), sa*sb*(ga ⬝ᵥ gb), sa*sc*(ga ⬝ᵥ gc)],
          ![sb*sa*(gb ⬝ᵥ ga), sb*sb*(gb ⬝ᵥ gb), sb*sc*(gb ⬝ᵥ gc)],
          ![sc*sa*(gc ⬝ᵥ ga), sc*sb*(gc ⬝ᵥ gb), sc*sc*(gc ⬝ᵥ gc)]])
        * (Matrix.of ![![sa*sa*(ga ⬝ᵥ ga), sa*sb*(ga ⬝ᵥ gb), sa*sc*(ga ⬝ᵥ gc)],
          ![sb*sa*(gb ⬝ᵥ ga), sb*sb*(gb ⬝ᵥ gb), sb*sc*(gb ⬝ᵥ gc)],
          ![sc*sa*(gc ⬝ᵥ ga), sc*sb*(gc ⬝ᵥ gb), sc*sc*(gc ⬝ᵥ gc)]])))/2)
      = (sa*sa) * ((sb*sb) * ((ga ⬝ᵥ ga) * (gb ⬝ᵥ gb) - (ga ⬝ᵥ gb)^2))
        + (sa*sa) * ((sc*sc) * ((ga ⬝ᵥ ga) * (gc ⬝ᵥ gc) - (ga ⬝ᵥ gc)^2))
        + (sb*sb) * ((sc*sc) * ((gb ⬝ᵥ gb) * (gc ⬝ᵥ gc) - (gb ⬝ᵥ gc)^2)) := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, dotProduct]
  ring

/-! ## 2. The block instantiation -/

set_option linter.unusedSimpArgs false in
/-- The projection block at a pick is the scaled Gram of the picked atoms. -/
theorem projectionBlock_eq_scaledGram (D : WeightedDesign m 3)
    (pick : Fin 3 → Fin m) :
    (projectionOfDesign D).submatrix pick pick
      = Matrix.of ![![Real.sqrt (D.weight (pick 0)) * Real.sqrt (D.weight (pick 0))
            * (D.atom (pick 0) ⬝ᵥ D.atom (pick 0)),
          Real.sqrt (D.weight (pick 0)) * Real.sqrt (D.weight (pick 1))
            * (D.atom (pick 0) ⬝ᵥ D.atom (pick 1)),
          Real.sqrt (D.weight (pick 0)) * Real.sqrt (D.weight (pick 2))
            * (D.atom (pick 0) ⬝ᵥ D.atom (pick 2))],
        ![Real.sqrt (D.weight (pick 1)) * Real.sqrt (D.weight (pick 0))
            * (D.atom (pick 1) ⬝ᵥ D.atom (pick 0)),
          Real.sqrt (D.weight (pick 1)) * Real.sqrt (D.weight (pick 1))
            * (D.atom (pick 1) ⬝ᵥ D.atom (pick 1)),
          Real.sqrt (D.weight (pick 1)) * Real.sqrt (D.weight (pick 2))
            * (D.atom (pick 1) ⬝ᵥ D.atom (pick 2))],
        ![Real.sqrt (D.weight (pick 2)) * Real.sqrt (D.weight (pick 0))
            * (D.atom (pick 2) ⬝ᵥ D.atom (pick 0)),
          Real.sqrt (D.weight (pick 2)) * Real.sqrt (D.weight (pick 1))
            * (D.atom (pick 2) ⬝ᵥ D.atom (pick 1)),
          Real.sqrt (D.weight (pick 2)) * Real.sqrt (D.weight (pick 2))
            * (D.atom (pick 2) ⬝ᵥ D.atom (pick 2))]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix_apply, projectionOfDesign_apply]

/-- **The block determinant is the weighted squared bracket.** -/
theorem projectionBlock_det_eq (D : WeightedDesign m 3) (pick : Fin 3 → Fin m) :
    ((projectionOfDesign D).submatrix pick pick).det
      = D.weight (pick 0) * (D.weight (pick 1) * (D.weight (pick 2)
        * atomBracket D (pick 0) (pick 1) (pick 2) ^ 2)) := by
  rw [projectionBlock_eq_scaledGram, det_scaledGram,
    Real.mul_self_sqrt (D.weight_pos (pick 0)).le,
    Real.mul_self_sqrt (D.weight_pos (pick 1)).le,
    Real.mul_self_sqrt (D.weight_pos (pick 2)).le, atomBracket]

/-- **The block second invariant is the weighted wedge mass.** -/
theorem projectionBlock_e2_eq (D : WeightedDesign m 3) (pick : Fin 3 → Fin m) :
    (((Matrix.trace ((projectionOfDesign D).submatrix pick pick))^2
      - Matrix.trace ((projectionOfDesign D).submatrix pick pick
        * (projectionOfDesign D).submatrix pick pick))/2)
      = D.weight (pick 0) * (D.weight (pick 1)
          * (leverageOf (D.atom (pick 0)) * leverageOf (D.atom (pick 1))
            - atomPairing D (pick 0) (pick 1) ^ 2))
        + D.weight (pick 0) * (D.weight (pick 2)
          * (leverageOf (D.atom (pick 0)) * leverageOf (D.atom (pick 2))
            - atomPairing D (pick 0) (pick 2) ^ 2))
        + D.weight (pick 1) * (D.weight (pick 2)
          * (leverageOf (D.atom (pick 1)) * leverageOf (D.atom (pick 2))
            - atomPairing D (pick 1) (pick 2) ^ 2)) := by
  rw [projectionBlock_eq_scaledGram, e2_scaledGram,
    Real.mul_self_sqrt (D.weight_pos (pick 0)).le,
    Real.mul_self_sqrt (D.weight_pos (pick 1)).le,
    Real.mul_self_sqrt (D.weight_pos (pick 2)).le,
    leverageOf_eq_dotProduct, leverageOf_eq_dotProduct,
    leverageOf_eq_dotProduct, atomPairing, atomPairing, atomPairing]

/-! ## 3. The wedge-bracket tax -/

/-- **THE WEDGE-BRACKET TAX OF A TIE.**  At every triple of a tie whose
weighted wedge mass is positive, some member weight prices the weighted
squared bracket by the wedge mass:

  `t_a t_b t_c·[abc]² ≤ t·(t_at_b w_{ab} + t_at_c w_{ac} + t_bt_c w_{bc})` .

Polynomial on both sides, in the currencies of the hinge. -/
theorem isTie_wedgeBracket_tax (D : WeightedDesign m 3) (htie : IsTie D)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmass : 0 < D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b) - atomPairing D a b ^ 2))
      + D.weight a * (D.weight c
        * (leverageOf (D.atom a) * leverageOf (D.atom c) - atomPairing D a c ^ 2))
      + D.weight b * (D.weight c
        * (leverageOf (D.atom b) * leverageOf (D.atom c) - atomPairing D b c ^ 2))) :
    ∃ member ∈ ({a, b, c} : Finset (Fin m)),
      D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
        ≤ D.weight member
          * (D.weight a * (D.weight b
              * (leverageOf (D.atom a) * leverageOf (D.atom b) - atomPairing D a b ^ 2))
            + D.weight a * (D.weight c
              * (leverageOf (D.atom a) * leverageOf (D.atom c) - atomPairing D a c ^ 2))
            + D.weight b * (D.weight c
              * (leverageOf (D.atom b) * leverageOf (D.atom c) - atomPairing D b c ^ 2))) := by
  have hinj := injective_tripleSlots hab hac hbc
  have hdet := projectionBlock_det_eq D ![a, b, c]
  have he2 := projectionBlock_e2_eq D ![a, b, c]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hdet he2
  obtain ⟨slot, hslot⟩ := isTie_block_tax D htie ![a, b, c] hinj (by rw [he2]; exact hmass)
  rw [hdet, he2] at hslot
  refine ⟨![a, b, c] slot, ?_, ?_⟩
  · fin_cases slot <;> simp
  · exact hslot

/-- **THE WEDGE-BRACKET PRODUCER.**  A triple whose EVERY member weight
undercuts the bracket-to-wedge ratio dominates strictly. -/
theorem posDef_subsetSum_of_wedgeBracket_light (D : WeightedDesign m 3)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmass : 0 < D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b) - atomPairing D a b ^ 2))
      + D.weight a * (D.weight c
        * (leverageOf (D.atom a) * leverageOf (D.atom c) - atomPairing D a c ^ 2))
      + D.weight b * (D.weight c
        * (leverageOf (D.atom b) * leverageOf (D.atom c) - atomPairing D b c ^ 2)))
    (hlight : ∀ member ∈ ({a, b, c} : Finset (Fin m)),
      D.weight member
          * (D.weight a * (D.weight b
              * (leverageOf (D.atom a) * leverageOf (D.atom b) - atomPairing D a b ^ 2))
            + D.weight a * (D.weight c
              * (leverageOf (D.atom a) * leverageOf (D.atom c) - atomPairing D a c ^ 2))
            + D.weight b * (D.weight c
              * (leverageOf (D.atom b) * leverageOf (D.atom c) - atomPairing D b c ^ 2)))
        < D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))) :
    (subsetSum D ({a, b, c} : Finset (Fin m)) - 1).PosDef := by
  have hinj := injective_tripleSlots hab hac hbc
  have hdet := projectionBlock_det_eq D ![a, b, c]
  have he2 := projectionBlock_e2_eq D ![a, b, c]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hdet he2
  have himg := image_tripleSlots a b c
  rw [← himg]
  refine posDef_subsetSum_of_invariant_light D ![a, b, c] hinj
    (by rw [he2]; exact hmass) (fun slot => ?_)
  rw [hdet, he2]
  refine hlight (![a, b, c] slot) ?_
  fin_cases slot <;> simp

end Gtz
