/-
# The invariant budgets: the conservation laws of the tax currencies

The wedge-bracket tax prices each triple of a tie in two currencies — the
weighted squared bracket and the weighted wedge mass.  This module lands the
EXACT GLOBAL BUDGETS of the two currencies, at every size, from Parseval
alone:

* the Parseval moments — the traces of the first three powers of the
  resolved identity: `Σ_a t_a·ℓ_a = 3` (landed at every rank in
  `Gtz.sum_weighted_leverage`), `Σ_{ab} t_at_b·⟨g_a,g_b⟩² = 3`, and
  `Σ_{abc} t_at_bt_c·⟨g_a,g_b⟩⟨g_b,g_c⟩⟨g_c,g_a⟩ = 3`;
* THE WEDGE BUDGET, MASS FORM (`Gtz.wedge_mass_budget`): over ordered pairs,
  `Σ_{ab} t_at_b·w_{ab} = 6`.  The diagonal vanishes by itself, so the
  fifteen unordered pair wedges of a six-atom design total exactly three;
* THE BRACKET BUDGET (`Gtz.bracket_budget`): over ordered triples,
  `Σ_{abc} t_at_bt_c·[abc]² = 6`.  Repeated labels vanish by themselves, so
  the twenty unordered triple brackets total exactly one.  This is
  Cauchy–Binet at the identity, proved with no compound matrices: the
  squared bracket is the Gram determinant, and the Gram expansion turns the
  triple sum into the three Parseval moments — `27 + 2·3 − 3·9 = 6`.

The budgets are the resource side of every aggregation of the tax: at a tie
the taxes cap each weighted squared bracket by a member weight times wedge
mass, while the budgets force the brackets to total six against a wedge
total of six.
-/
import Gtz.Wave.WedgeBracketTax

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The trace monomial of a triple atom product -/

/-- The trace of a product of three atoms is the pairing cycle.  The
two-product law is the landed `Gtz.trace_atomMatrix_mul_atomMatrix`. -/
theorem trace_atomMatrix_mul_three (f g h : Fin 3 → ℝ) :
    Matrix.trace (atomMatrix f * atomMatrix g * atomMatrix h)
      = (f ⬝ᵥ g) * ((g ⬝ᵥ h) * (h ⬝ᵥ f)) := by
  simp only [atomMatrix, Matrix.trace_fin_three, Matrix.mul_apply,
    Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_three]
  ring

/-! ## 2. The second and third Parseval moments -/

/-- **THE SECOND PARSEVAL MOMENT.**  The weighted squared pairings total the
rank: `Σ_{ab} t_at_b·⟨g_a,g_b⟩² = 3`.  The trace of the square of the
resolved identity. -/
theorem parseval_pairing_sq_total (D : WeightedDesign m 3) :
    ∑ a, ∑ b, D.weight a * (D.weight b * atomPairing D a b ^ 2) = 3 := by
  have hexpand : Matrix.trace
      ((∑ a, D.weight a • atomMatrix (D.atom a))
        * (∑ b, D.weight b • atomMatrix (D.atom b)))
      = ∑ a, ∑ b, D.weight a * (D.weight b * atomPairing D a b ^ 2) := by
    rw [Finset.sum_mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.trace_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
    rw [trace_atomMatrix_mul_atomMatrix, atomPairing]
    ring
  rw [← hexpand, D.isParseval, one_mul, Matrix.trace_one]
  norm_num

/-- **THE THIRD PARSEVAL MOMENT.**  The weighted pairing cycles total the
rank: `Σ_{abc} t_at_bt_c·⟨g_a,g_b⟩⟨g_b,g_c⟩⟨g_c,g_a⟩ = 3`.  The trace of
the cube of the resolved identity. -/
theorem parseval_pairing_cycle_total (D : WeightedDesign m 3) :
    ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c
        * (atomPairing D a b * (atomPairing D b c * atomPairing D c a)))) = 3 := by
  have hexpand : Matrix.trace
      ((∑ a, D.weight a • atomMatrix (D.atom a))
        * (∑ b, D.weight b • atomMatrix (D.atom b))
        * (∑ c, D.weight c • atomMatrix (D.atom c)))
      = ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c
          * (atomPairing D a b * (atomPairing D b c * atomPairing D c a)))) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
    rw [trace_atomMatrix_mul_three, atomPairing, atomPairing, atomPairing]
    ring
  rw [← hexpand, D.isParseval, one_mul, one_mul, Matrix.trace_one]
  norm_num

/-! ## 3. The wedge budget -/

/-- **THE WEDGE BUDGET, MASS FORM.**  Over ordered pairs the weighted wedge
masses total six: `Σ_{ab} t_at_b·w_{ab} = 6`.  The diagonal self-wedge
vanishes by itself, so the unordered pair wedges of any design total exactly
three.  The cross-product form is the landed `Gtz.wedge_budget`; this is the
leverage-and-pairing form that `Gtz.isTie_wedgeBracket_tax` prices. -/
theorem wedge_mass_budget (D : WeightedDesign m 3) :
    ∑ a, ∑ b, D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b)
          - atomPairing D a b ^ 2)) = 6 := by
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = 3 := by
    have h := sum_weighted_leverage D
    norm_num at h
    exact h
  have hsplit : ∑ a, ∑ b, D.weight a * (D.weight b
      * (leverageOf (D.atom a) * leverageOf (D.atom b) - atomPairing D a b ^ 2))
      = (∑ a, ∑ b, (D.weight a * leverageOf (D.atom a))
          * (D.weight b * leverageOf (D.atom b)))
        - ∑ a, ∑ b, D.weight a * (D.weight b * atomPairing D a b ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsplit, ← Finset.sum_mul_sum, hlev, parseval_pairing_sq_total]
  norm_num

/-! ## 4. The Gram expansion of the squared bracket -/

/-- The squared bracket is the Gram determinant, expanded: leverages,
pairing cycle, and the three leverage-square corrections. -/
theorem tripleBracket_sq_gram (u v w : Fin 3 → ℝ) :
    tripleBracket u v w ^ 2
      = leverageOf u * (leverageOf v * leverageOf w)
        + 2 * ((u ⬝ᵥ v) * ((v ⬝ᵥ w) * (w ⬝ᵥ u)))
        - leverageOf u * (v ⬝ᵥ w) ^ 2
        - leverageOf v * (w ⬝ᵥ u) ^ 2
        - leverageOf w * (u ⬝ᵥ v) ^ 2 := by
  simp only [tripleBracket_eq, leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-! ## 5. The bracket budget -/

/-- **THE BRACKET BUDGET.**  Over ordered triples the weighted squared
brackets total six: `Σ_{abc} t_at_bt_c·[abc]² = 6`.  Repeated labels vanish
by themselves, so the unordered triple brackets of any design total exactly
one — Cauchy–Binet at the identity, with no compound matrices: the Gram
expansion reduces the sum to the three Parseval moments,
`27 + 2·3 − 3·9 = 6`. -/
theorem bracket_budget (D : WeightedDesign m 3) :
    ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c
        * atomBracket D a b c ^ 2)) = 6 := by
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = 3 := by
    have h := sum_weighted_leverage D
    norm_num at h
    exact h
  -- the five-piece Gram expansion of every summand
  have hexp : ∀ a b c : Fin m, D.weight a * (D.weight b * (D.weight c
      * atomBracket D a b c ^ 2))
      = (D.weight a * leverageOf (D.atom a)) * ((D.weight b * leverageOf (D.atom b))
          * (D.weight c * leverageOf (D.atom c)))
        + 2 * (D.weight a * (D.weight b * (D.weight c
            * (atomPairing D a b * (atomPairing D b c * atomPairing D c a)))))
        - (D.weight a * leverageOf (D.atom a))
            * (D.weight b * (D.weight c * atomPairing D b c ^ 2))
        - (D.weight b * leverageOf (D.atom b))
            * (D.weight c * (D.weight a * atomPairing D c a ^ 2))
        - (D.weight c * leverageOf (D.atom c))
            * (D.weight a * (D.weight b * atomPairing D a b ^ 2)) := by
    intro a b c
    rw [atomBracket, tripleBracket_sq_gram, atomPairing, atomPairing, atomPairing]
    ring
  have hrw : ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c
      * atomBracket D a b c ^ 2))
      = ∑ a, ∑ b, ∑ c, ((D.weight a * leverageOf (D.atom a))
            * ((D.weight b * leverageOf (D.atom b))
              * (D.weight c * leverageOf (D.atom c)))
          + 2 * (D.weight a * (D.weight b * (D.weight c
              * (atomPairing D a b * (atomPairing D b c * atomPairing D c a)))))
          - (D.weight a * leverageOf (D.atom a))
              * (D.weight b * (D.weight c * atomPairing D b c ^ 2))
          - (D.weight b * leverageOf (D.atom b))
              * (D.weight c * (D.weight a * atomPairing D c a ^ 2))
          - (D.weight c * leverageOf (D.atom c))
              * (D.weight a * (D.weight b * atomPairing D a b ^ 2))) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => hexp a b c
  rw [hrw]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- piece 1: the leverage cube
  have hT1 : ∑ a, ∑ b, ∑ c, (D.weight a * leverageOf (D.atom a))
      * ((D.weight b * leverageOf (D.atom b))
        * (D.weight c * leverageOf (D.atom c))) = 27 := by
    have hbc : ∑ b, ∑ c, (D.weight b * leverageOf (D.atom b))
        * (D.weight c * leverageOf (D.atom c)) = 9 := by
      rw [← Finset.sum_mul_sum, hlev]
      norm_num
    have hstep : ∀ a : Fin m, ∑ b, ∑ c, (D.weight a * leverageOf (D.atom a))
        * ((D.weight b * leverageOf (D.atom b))
          * (D.weight c * leverageOf (D.atom c)))
        = (D.weight a * leverageOf (D.atom a)) * 9 := by
      intro a
      rw [← hbc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => hstep a, ← Finset.sum_mul, hlev]
    norm_num
  -- piece 2: the pairing cycle
  have hT2 : ∑ a, ∑ b, ∑ c, 2 * (D.weight a * (D.weight b * (D.weight c
      * (atomPairing D a b * (atomPairing D b c * atomPairing D c a))))) = 6 := by
    have h := parseval_pairing_cycle_total D
    calc ∑ a, ∑ b, ∑ c, 2 * (D.weight a * (D.weight b * (D.weight c
          * (atomPairing D a b * (atomPairing D b c * atomPairing D c a)))))
        = 2 * ∑ a, ∑ b, ∑ c, D.weight a * (D.weight b * (D.weight c
            * (atomPairing D a b * (atomPairing D b c * atomPairing D c a)))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
      _ = 6 := by rw [h]; norm_num
  -- piece 3: leverage of the first against the opposite pairing
  have hT3 : ∑ a, ∑ b, ∑ c, (D.weight a * leverageOf (D.atom a))
      * (D.weight b * (D.weight c * atomPairing D b c ^ 2)) = 9 := by
    have hstep : ∀ a : Fin m, ∑ b, ∑ c, (D.weight a * leverageOf (D.atom a))
        * (D.weight b * (D.weight c * atomPairing D b c ^ 2))
        = (D.weight a * leverageOf (D.atom a)) * 3 := by
      intro a
      rw [← parseval_pairing_sq_total D, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => hstep a, ← Finset.sum_mul, hlev]
    norm_num
  -- piece 4: leverage of the second against the opposite pairing
  have hT4 : ∑ a, ∑ b, ∑ c, (D.weight b * leverageOf (D.atom b))
      * (D.weight c * (D.weight a * atomPairing D c a ^ 2)) = 9 := by
    rw [Finset.sum_comm]
    have hstep : ∀ b : Fin m, ∑ a, ∑ c, (D.weight b * leverageOf (D.atom b))
        * (D.weight c * (D.weight a * atomPairing D c a ^ 2))
        = (D.weight b * leverageOf (D.atom b)) * 3 := by
      intro b
      have hca : ∑ a, ∑ c, D.weight c * (D.weight a * atomPairing D c a ^ 2) = 3 := by
        rw [Finset.sum_comm]
        exact parseval_pairing_sq_total D
      rw [← hca, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun b _ => hstep b, ← Finset.sum_mul, hlev]
    norm_num
  -- piece 5: leverage of the third against the opposite pairing
  have hT5 : ∑ a, ∑ b, ∑ c, (D.weight c * leverageOf (D.atom c))
      * (D.weight a * (D.weight b * atomPairing D a b ^ 2)) = 9 := by
    have hstep : ∀ (a b : Fin m), ∑ c, (D.weight c * leverageOf (D.atom c))
        * (D.weight a * (D.weight b * atomPairing D a b ^ 2))
        = 3 * (D.weight a * (D.weight b * atomPairing D a b ^ 2)) := by
      intro a b
      rw [← Finset.sum_mul, hlev]
    have hmid : ∑ a, ∑ b, ∑ c, (D.weight c * leverageOf (D.atom c))
        * (D.weight a * (D.weight b * atomPairing D a b ^ 2))
        = ∑ a, ∑ b, 3 * (D.weight a * (D.weight b * atomPairing D a b ^ 2)) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hstep a b
    rw [hmid]
    have hpull : ∑ a, ∑ b, 3 * (D.weight a * (D.weight b * atomPairing D a b ^ 2))
        = 3 * ∑ a, ∑ b, D.weight a * (D.weight b * atomPairing D a b ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
    rw [hpull, parseval_pairing_sq_total]
    norm_num
  rw [hT1, hT2, hT3, hT4, hT5]
  norm_num

end Gtz
