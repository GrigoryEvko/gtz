/-
# Lemma F-quant, Lemma T, and the z-mass floor

Three quantitative pieces of the corner layer, each a short consequence of an
identity already in the kernel.

**Lemma F-quant.** The Bhatia–Davis telescope says the extremal products sum to
`−n(Mm + 1)`, so a near-tie `Mm ≥ −1−η` caps every single term at `nη`. Since
each term's two factors add to the spread `M − m`, the smaller factor — the
distance to the nearer endpoint — obeys `min·(M−m) ≤ 2nη`. This is the
quantitative rigidity behind the corner's realness: near a tie every coordinate
is pinned near one of the two extremal values.

**Lemma T.** On a `κ·I` quadruple the excess is scalar, so every pivot is
`ℓ_d/(κ−1)` and complementary pair sums commute for free. The consequence with
teeth: if no insider of the `(k+1)`-set is droppable, then `κ < k+1` — the
insider-silent fibers exist only strictly below the corner value, which is why
the corner `κ = k+1` is the unique covering point of the tight-quadruple
family.

**The z-mass floor.** The one-surface identity `depth = 1 − zmass` turns wall
silence (`depth < 1/ℓ`) into a lower bound on the z-mass, `zmass > 1 − 1/ℓ` —
the Gatecap floor, now a sign reading of a kernel-checked identity.
-/
import Mathlib
import Gtz.Basic
import Gtz.BhatiaDavis
import Gtz.TraceIdentity
import Gtz.TwoByTwo
import Gtz.PsdKit

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### Lemma F-quant -/

/-- **The per-term cap**: a near-tie bounds every extremal product. With the
sandwich `m′ ≤ x_i ≤ M` and `M·m′ ≥ −1−η`, each `(M − x_i)(x_i − m′) ≤ nη`. -/
theorem fquant_term_le {n : ℕ} (x : Fin n → ℝ) (bigM smallM eta : ℝ)
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = n)
    (hupper : ∀ i, x i ≤ bigM) (hlower : ∀ i, smallM ≤ x i)
    (hnear : -1 - eta ≤ bigM * smallM) (chosen : Fin n) :
    (bigM - x chosen) * (x chosen - smallM) ≤ n * eta := by
  have htelescope := bhatiaDavis_telescope x bigM smallM hsum hsq
  have hterms : ∀ i ∈ Finset.univ,
      0 ≤ (bigM - x i) * (x i - smallM) := fun i _ =>
    mul_nonneg (sub_nonneg.mpr (hupper i)) (sub_nonneg.mpr (hlower i))
  have hsingle : (bigM - x chosen) * (x chosen - smallM)
      ≤ ∑ i, (bigM - x i) * (x i - smallM) :=
    Finset.single_le_sum hterms (Finset.mem_univ chosen)
  have hnat : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [hsingle, htelescope, hnat, hnear]

/-- **Lemma F-quant**: near a tie, every coordinate is pinned near an extremal
value — the distance to the nearer endpoint times the spread is at most `2nη`.
Stated division-free so the spread needs no positivity hypothesis. -/
theorem fquant_dist_mul_gap_le {n : ℕ} (x : Fin n → ℝ) (bigM smallM eta : ℝ)
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = n)
    (hupper : ∀ i, x i ≤ bigM) (hlower : ∀ i, smallM ≤ x i)
    (hnear : -1 - eta ≤ bigM * smallM) (chosen : Fin n) :
    min (bigM - x chosen) (x chosen - smallM) * (bigM - smallM)
      ≤ 2 * (n * eta) := by
  have hterm := fquant_term_le x bigM smallM eta hsum hsq hupper hlower hnear
    chosen
  set upperGap := bigM - x chosen with hupperGap
  set lowerGap := x chosen - smallM with hlowerGap
  have hupperNonneg : 0 ≤ upperGap := sub_nonneg.mpr (hupper chosen)
  have hlowerNonneg : 0 ≤ lowerGap := sub_nonneg.mpr (hlower chosen)
  have hspread : bigM - smallM = upperGap + lowerGap := by
    rw [hupperGap, hlowerGap]; ring
  rw [hspread]
  rcases le_total upperGap lowerGap with hmin | hmin
  · rw [min_eq_left hmin]
    nlinarith [hterm, hupperNonneg]
  · rw [min_eq_right hmin]
    nlinarith [hterm, hlowerNonneg]

/-! ### Lemma T: the κ·I fiber -/

/-- On a `κ·I` base the excess is the scalar `κ − 1`, positive definite as soon
as `κ > 1`. -/
theorem posDef_excess_of_kappa (D : WeightedDesign m k) (Q : Finset (Fin m))
    {kappa : ℝ} (hfiber : subsetSum D Q = kappa • 1) (hkappa : 1 < kappa) :
    (subsetSum D Q - 1).PosDef := by
  rw [hfiber]
  have hform : ∀ u : Fin k → ℝ,
      u ⬝ᵥ ((kappa • 1 - 1 : Matrix (Fin k) (Fin k) ℝ) *ᵥ u)
        = (kappa - 1) * (u ⬝ᵥ u) := by
    intro u
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
    ring
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun u hu => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  · rw [star_trivial, hform]
    have hnorm : 0 < u ⬝ᵥ u := by
      rcases lt_or_eq_of_le (dotProduct_self_nonneg u) with hpos | hzero
      · exact hpos
      · exfalso
        refine hu (funext fun i => ?_)
        have hsq : ∑ j, u j ^ 2 = 0 := by
          rw [← dotProduct_self_eq_sum_sq, ← hzero]
      -- each square vanishes inside a zero sum of squares
        have hall := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => sq_nonneg (u j))).mp hsq
        have := hall i (Finset.mem_univ i)
        exact pow_eq_zero_iff (n := 2) (by omega) |>.mp this
    exact mul_pos (by linarith) hnorm

/-- **Every pivot on the κ·I fiber is `ℓ_d/(κ−1)`** — the excess inverse is the
scalar `(κ−1)⁻¹`, so the pivot reads the leverage directly. -/
theorem pivot_eq_leverage_div_of_kappa (D : WeightedDesign m k)
    (Q : Finset (Fin m)) {kappa : ℝ} (hfiber : subsetSum D Q = kappa • 1)
    (hkappa : 1 < kappa) (d : Fin m) :
    pivot D Q d = leverageOf (D.atom d) / (kappa - 1) := by
  have hgap : kappa - 1 ≠ 0 := by linarith
  have hexcess : subsetSum D Q - 1 = (kappa - 1) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [hfiber, sub_smul, one_smul]
  have hinverse : (subsetSum D Q - 1)⁻¹
      = (kappa - 1)⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hexcess, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ hgap, one_smul]
  rw [pivot, hinverse, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    trace_atomMatrix, smul_eq_mul, div_eq_inv_mul]

/-- Complementary halves of a `κ·I` split commute — one is a polynomial in the
other. -/
theorem complementary_commute {firstHalf secondHalf : Matrix (Fin k) (Fin k) ℝ}
    {kappa : ℝ} (hsplit : firstHalf + secondHalf = kappa • 1) :
    firstHalf * secondHalf = secondHalf * firstHalf := by
  have hsecond : secondHalf = kappa • 1 - firstHalf := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsplit
  rw [hsecond, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-- **Lemma T's bound with teeth**: on a `(k+1)`-atom `κ·I` fiber where NO
insider is droppable (every leverage exceeds `κ−1`), necessarily `κ < k+1`.
The insider-silent fibers live strictly below the corner value — the corner
`κ = k+1` is the unique covering point of the tight-quadruple family. -/
theorem kappa_lt_of_insiders_silent (D : WeightedDesign m k)
    (Q : Finset (Fin m)) {kappa : ℝ} (hfiber : subsetSum D Q = kappa • 1)
    (hcard : Q.card = k + 1)
    (hsilent : ∀ d ∈ Q, kappa - 1 < leverageOf (D.atom d)) :
    kappa < k + 1 := by
  -- the trace of the fiber equation: Σ_{d∈Q} ℓ_d = κ·k
  have htrace : ∑ d ∈ Q, leverageOf (D.atom d) = kappa * k := by
    have htr := congrArg Matrix.trace hfiber
    rw [subsetSum, Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_one] at htr
    simpa [trace_atomMatrix, smul_eq_mul, Fintype.card_fin] using htr
  -- summing the strict silence bounds over the k+1 insiders
  have hnonempty : Q.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict : ∑ _d ∈ Q, (kappa - 1) < ∑ d ∈ Q, leverageOf (D.atom d) :=
    Finset.sum_lt_sum_of_nonempty hnonempty hsilent
  rw [Finset.sum_const, hcard, nsmul_eq_mul, htrace] at hstrict
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hstrict
  nlinarith [hstrict]

/-! ### The z-mass floor -/

/-- **The Gatecap z-mass floor**: wall silence at leverage `ℓ` — the depth
staying below `1/ℓ` — forces the z-mass above `1 − 1/ℓ`. A sign reading of the
one-surface identity `depth = 1 − zmass`. -/
theorem zmass_floor_of_wall_silent (base : Matrix (Fin 2) (Fin 2) ℝ)
    (direction : Fin 2 → ℝ) {lev : ℝ} (hdet : base.det ≠ 0)
    (hsilent : (base - Matrix.vecMulVec direction direction).det / base.det
      < 1 / lev) :
    1 - 1 / lev < direction ⬝ᵥ (base⁻¹ *ᵥ direction) := by
  rw [depth_eq_one_sub_zmass base direction hdet] at hsilent
  linarith

end Gtz
