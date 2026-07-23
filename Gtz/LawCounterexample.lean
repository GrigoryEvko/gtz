/-
# Kernel-checked counterexample: the B-form law with constant C_B fails at cap 10

The σ-free-core artifact (diary §70) displayed the local law
`B_E(σ*) ≤ C_B(ℓ̄)·σ*` with `C_B(ℓ̄) = C_2cap(ℓ̄) + 4(ℓ̄−2)²/(2ℓ̄−3)` as if global;
its adversarial audit refuted the display for ℓ̄ ≥ 7 with a quad-precision
design. This file settles the numerical dispute in the kernel: an EXACT
rational 4-atom planar design (tan-half-angle circle points, weights solved
exactly from the design equations) with leverage cap 10 and every atom
τ-essential at τ = 1/20, whose max pair slack σ* is bracketed by rational
squared-norm certificates, and whose budget exceeds `C_B(10)·σ` for EVERY σ
in the bracket — hence at σ* itself:

  `C_B(10) · σ* < B(σ*)`,  `C_B(10) = 1250352/5491 = 227.709…`,
  `B(σ*)/σ* ≥ 228.15`.

The failed display was first-order-exact only: `C_B` is the σ* → 0 limit
constant, and the second-order coefficient changes sign between caps 5 and 7.
The law's hedged form `B_E ≤ C_B σ*(1 + O(σ*))` is untouched by this file.
-/
import Mathlib
import Gtz.PlanarPlatform

namespace Gtz

open Matrix

/-- The four atom squares (exact rational points of the double-angle circle,
scaled by the leverages): two cap atoms at ℓ = 10 and two light atoms. -/
def cexSquare : Fin 4 → Fin 2 → ℚ :=
  ![![24208710/2699129, -11936000/2699129],
    ![9480100718310/1051989928169, 4560260000000/1051989928169],
    ![-5155833988517284359/4909805244652100000, 3686101516905/49098052446521],
    ![-1642699036559691035491/1547911013744329000000,
      -41762860750017/1547911013744329]]

/-- The exact weights, solved from `Σt = 1`, closure, and trace. -/
def cexWeight : Fin 4 → ℚ :=
  ![1824487532061660728209844308269053840310446849587123/
      34652036675942734828022911956974541491543884787200000,
    1823185482113662146021911745830234653992997576409677/
      34652036675942734828022911956974541491543884787200000,
    255744196467524049401366443597618759481497/
      903180448004727488030210878518473213267000,
    55236227427211406289738278945763856559403/
      90318044800472748803021087851847321326700]

/-- The leverages: `|S_c| = ℓ_c`. -/
def cexLev : Fin 4 → ℚ := ![10, 10, 105279/100000, 1061579/1000000]

/-- The lower bracket endpoint for the max slack. -/
def cexSlackLo : ℚ := 4779/500000

/-- The upper bracket endpoint for the max slack. -/
def cexSlackHi : ℚ := 9559/1000000

/-- The law constant at cap 10:
`C_B(10) = C_2cap(10) + 4·(10−2)²/(2·10−3) = 1250352/5491`. -/
theorem lawConstant_cap_ten :
    (1250352/5491 : ℚ)
      = 4 * 10 ^ 3 / (2 * 10 - 1)
        + 2 * (2 * 10 - 2) ^ 3 / ((2 * 10 - 1) * (2 * 10 - 3) ^ 2)
        + 4 * (10 - 2) ^ 2 / (2 * 10 - 3) := by norm_num

/-- The design is valid: positive weights summing to one, exact closure,
trace two, and every square's norm equals its leverage. -/
theorem cexDesign_valid :
    (∀ c, 0 < cexWeight c) ∧ (∑ c, cexWeight c) = 1
      ∧ (∀ i, (∑ c, cexWeight c * cexSquare c i) = 0)
      ∧ (∑ c, cexWeight c * cexLev c) = 2
      ∧ (∀ c, (∑ i, cexSquare c i ^ 2) = cexLev c ^ 2) := by
  refine ⟨fun c => ?_, ?_, fun i => ?_, ?_, fun c => ?_⟩
  · fin_cases c <;> norm_num [cexWeight]
  · norm_num [Fin.sum_univ_four, cexWeight, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
  · fin_cases i <;>
      norm_num [Fin.sum_univ_four, cexWeight, cexSquare, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons]
  · norm_num [Fin.sum_univ_four, cexWeight, cexLev, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
  · fin_cases c <;>
      norm_num [Fin.sum_univ_two, cexSquare, cexLev, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons]

/-- Every atom respects the leverage cap 10 and is τ-essential at τ = 1/20:
`t_c ℓ_c > 1/20` and `ℓ_c > 1 + 1/20`. -/
theorem cexDesign_capped_essential :
    ∀ c, cexLev c ≤ 10 ∧ 1/20 < cexWeight c * cexLev c
        ∧ 1 + 1/20 < cexLev c := by
  intro c
  fin_cases c <;>
    refine ⟨by norm_num [cexLev], by norm_num [cexWeight, cexLev],
      by norm_num [cexLev]⟩

/-- The real-cast squares. -/
noncomputable def cexSquareR : Fin 4 → Fin 2 → ℝ :=
  fun c i => (cexSquare c i : ℝ)

/-- The B-form budget of the design at level `1 + shift` — exactly the
pair-sum the platform's `planarMaster_trace` equates to `tr R_E`. -/
noncomputable def cexBudget (shift : ℝ) : ℝ :=
  (1 / 2) * ∑ c, ∑ d,
    pairEntry cexSquareR (fun e => (cexLev e : ℝ) - 2 * (1 + shift))
        (1 + shift) c d
      * (cexWeight c : ℝ) * (cexWeight d : ℝ)
      * ((cexSquareR c - cexSquareR d) ⬝ᵥ (cexSquareR c - cexSquareR d))

/-- The budget IS the trace of the platform master matrix at this design. -/
theorem cexBudget_eq_trace (shift : ℝ) :
    cexBudget shift
      = Matrix.trace (planarMaster Finset.univ cexSquareR
          (fun e => (cexWeight e : ℝ))
          (fun e => (cexLev e : ℝ) - 2 * (1 + shift)) (1 + shift)) :=
  (planarMaster_trace Finset.univ cexSquareR (fun e => (cexWeight e : ℝ))
    (fun e => (cexLev e : ℝ) - 2 * (1 + shift)) (1 + shift)).symm

set_option maxHeartbeats 1600000 in
/-- The budget as an explicit quadratic in the level shift (exact rational
coefficients; the σ²-coefficient is negative — the pinch concavity). -/
theorem cexBudget_quadratic (shift : ℝ) :
    cexBudget shift
      = (17901981838829203036174858563445742845150215514748504781417670437118553146385541650525441094066431035755614006088960902403267935372665461044979 : ℝ)
          / 118998429535623292462454320656142160476587773978067975096451079816084449748509230503249564420766191199934113546017594849343316676000000000000000
        + ((9603321603765499681364070724769543093912053526599619288997517 : ℝ)
          / 45159022400236374401510543925923660663350000000000000000000) * shift
        - ((1041334074931018262980527192706575527641087994511314893 : ℝ)
          / 45159022400236374401510543925923660663350000000000000) * shift ^ 2 := by
  unfold cexBudget cexSquareR pairEntry
  simp only [Fin.sum_univ_four, Fin.sum_univ_two, dotProduct, Pi.sub_apply,
    cexSquare, cexWeight, cexLev, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
/-- **The law fails on the whole slack bracket**: for every level shift in
`[σLo, σHi]`, the budget strictly exceeds `C_B(10)·shift`. Concavity of the
quadratic reduces this to the two (exact rational) endpoint evaluations. -/
theorem cexBudget_exceeds_law {shift : ℝ}
    (hLo : (cexSlackLo : ℝ) ≤ shift) (hHi : shift ≤ (cexSlackHi : ℝ)) :
    (1250352/5491 : ℝ) * shift < cexBudget shift := by
  rw [cexBudget_quadratic]
  have hLo' : (4779/500000 : ℝ) ≤ shift := by
    rw [show ((cexSlackLo : ℚ) : ℝ) = 4779/500000 by norm_num [cexSlackLo]]
      at hLo
    exact hLo
  have hHi' : shift ≤ (9559/1000000 : ℝ) := by
    rw [show ((cexSlackHi : ℚ) : ℝ) = 9559/1000000 by norm_num [cexSlackHi]]
      at hHi
    exact hHi
  nlinarith [mul_nonneg (sub_nonneg.mpr hLo') (sub_nonneg.mpr hHi')]

/-- The pair slack of the design at a pair: `(ℓ_c + ℓ_d − |S_c + S_d|)/2 − 1`. -/
noncomputable def cexPairSlack (c d : Fin 4) : ℝ :=
  ((cexLev c : ℝ) + (cexLev d : ℝ)
    - Real.sqrt (∑ i, ((cexSquare c i : ℝ) + (cexSquare d i : ℝ)) ^ 2)) / 2 - 1

/-- The max slack `σ*` over the six pairs. -/
noncomputable def cexMaxSlack : ℝ :=
  (cexPairSlack 0 1 ⊔ cexPairSlack 0 2 ⊔ cexPairSlack 0 3)
    ⊔ (cexPairSlack 1 2 ⊔ cexPairSlack 1 3 ⊔ cexPairSlack 2 3)

/-- Slack lower bound from a squared-norm certificate: the norm is at most
the (nonnegative) affine gap, so the slack is at least the target. -/
private theorem pairSlack_ge_of_sq_le (c d : Fin 4) (target : ℚ)
    (hgap : 0 ≤ ((cexLev c : ℝ) + (cexLev d : ℝ) - 2 - 2 * (target : ℝ)))
    (hcert : (∑ i, ((cexSquare c i : ℝ) + (cexSquare d i : ℝ)) ^ 2)
      ≤ ((cexLev c : ℝ) + (cexLev d : ℝ) - 2 - 2 * (target : ℝ)) ^ 2) :
    (target : ℝ) ≤ cexPairSlack c d := by
  unfold cexPairSlack
  have hsqrt : Real.sqrt (∑ i, ((cexSquare c i : ℝ) + (cexSquare d i : ℝ)) ^ 2)
      ≤ (cexLev c : ℝ) + (cexLev d : ℝ) - 2 - 2 * (target : ℝ) := by
    calc Real.sqrt (∑ i, ((cexSquare c i : ℝ) + (cexSquare d i : ℝ)) ^ 2)
        ≤ Real.sqrt (((cexLev c : ℝ) + (cexLev d : ℝ) - 2
            - 2 * (target : ℝ)) ^ 2) := Real.sqrt_le_sqrt hcert
      _ = (cexLev c : ℝ) + (cexLev d : ℝ) - 2 - 2 * (target : ℝ) :=
          Real.sqrt_sq hgap
  linarith

/-- Slack upper bound from a squared-norm certificate: the (nonnegative)
affine gap is at most the norm, so the slack is at most the target. -/
private theorem pairSlack_le_of_le_sq (c d : Fin 4) (target : ℚ)
    (hgap : 0 ≤ ((cexLev c : ℝ) + (cexLev d : ℝ) - 2 - 2 * (target : ℝ)))
    (hnonneg : 0 ≤ (∑ i, ((cexSquare c i : ℝ) + (cexSquare d i : ℝ)) ^ 2))
    (hcert : ((cexLev c : ℝ) + (cexLev d : ℝ) - 2 - 2 * (target : ℝ)) ^ 2
      ≤ (∑ i, ((cexSquare c i : ℝ) + (cexSquare d i : ℝ)) ^ 2)) :
    cexPairSlack c d ≤ (target : ℝ) := by
  unfold cexPairSlack
  have hsqrt : (cexLev c : ℝ) + (cexLev d : ℝ) - 2 - 2 * (target : ℝ)
      ≤ Real.sqrt (∑ i, ((cexSquare c i : ℝ) + (cexSquare d i : ℝ)) ^ 2) :=
    (Real.le_sqrt hgap hnonneg).mpr hcert
  linarith

/-- Sum-of-squares terms are nonnegative. -/
private theorem cexNormSq_nonneg (c d : Fin 4) :
    0 ≤ (∑ i, ((cexSquare c i : ℝ) + (cexSquare d i : ℝ)) ^ 2) :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **σ\* ≥ σLo**: the (0,1) cap pair carries at least the bracketed slack. -/
theorem cexMaxSlack_ge : (cexSlackLo : ℝ) ≤ cexMaxSlack := by
  have h01 : (cexSlackLo : ℝ) ≤ cexPairSlack 0 1 := by
    refine pairSlack_ge_of_sq_le 0 1 cexSlackLo ?_ ?_
    · norm_num [cexLev, cexSlackLo, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
    · norm_num [Fin.sum_univ_two, cexSquare, cexLev, cexSlackLo,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  calc (cexSlackLo : ℝ) ≤ cexPairSlack 0 1 := h01
    _ ≤ cexMaxSlack :=
        le_sup_of_le_left (le_sup_of_le_left le_sup_left)

set_option maxHeartbeats 800000 in
/-- **σ\* ≤ σHi**: every pair's slack is certified below the upper bracket. -/
theorem cexMaxSlack_le : cexMaxSlack ≤ (cexSlackHi : ℝ) := by
  have hbound : ∀ c d : Fin 4, c < d → cexPairSlack c d ≤ (cexSlackHi : ℝ) := by
    intro c d _
    refine pairSlack_le_of_le_sq c d cexSlackHi ?_ (cexNormSq_nonneg c d) ?_
    · fin_cases c <;> fin_cases d <;>
        norm_num [cexLev, cexSlackHi, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
          Matrix.tail_cons]
    · fin_cases c <;> fin_cases d <;>
        norm_num [Fin.sum_univ_two, cexSquare, cexLev, cexSlackHi,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  exact sup_le
    (sup_le (sup_le (hbound 0 1 (by decide)) (hbound 0 2 (by decide)))
      (hbound 0 3 (by decide)))
    (sup_le (sup_le (hbound 1 2 (by decide)) (hbound 1 3 (by decide)))
      (hbound 2 3 (by decide)))

/-- The max slack is strictly positive. -/
theorem cexMaxSlack_pos : 0 < cexMaxSlack :=
  lt_of_lt_of_le (by norm_num [cexSlackLo]) cexMaxSlack_ge

/-- **The kernel-checked refutation**: at this valid, cap-10, τ-essential
planar design, the B-form budget at the design's own max slack strictly
exceeds `C_B(10) · σ*` — the boxed law `B_E(σ*) ≤ C_B(ℓ̄)σ*` is FALSE at
`ℓ̄ = 10` (`C_B` is only the σ* → 0 limit constant). -/
theorem bForm_law_fails_at_cap_ten :
    (1250352/5491 : ℝ) * cexMaxSlack < cexBudget cexMaxSlack :=
  cexBudget_exceeds_law cexMaxSlack_ge cexMaxSlack_le

end Gtz
