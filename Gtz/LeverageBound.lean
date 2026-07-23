/-
# The per-atom leverage bound: no atom dominates a tight frame

The isotropy constraint `Σ_c t_c g_c g_cᵀ = I` forces a hard ceiling on every
individual atom's leverage share: for each atom, `t_c · ℓ_c ≤ 1` where
`ℓ_c = |g_c|²`. Equivalently, `t_c g_c g_cᵀ ⪯ I` (one rank-one term of a PSD
resolution of the identity cannot exceed the whole), so its single nonzero
eigenvalue `t_c ℓ_c` is at most 1. This is the frame-theoretic foundation of
the leverage-decay story (`ρ(ℓ̄)`): a design's pivots and cap dictionary are
all controlled by leverage, and leverage is universally bounded here.

Proof is elementary and matrix-agnostic: the erased sum
`I − t_e g_e g_eᵀ = Σ_{c≠e} t_c g_c g_cᵀ` evaluated at `g_e` is a sum of
nonnegative terms `t_c ⟨g_c, g_e⟩² ≥ 0`, giving `ℓ_e − t_e ℓ_e² ≥ 0`.
-/
import Mathlib
import Gtz.Basic
import Gtz.MarginTransfer

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-- `leverageOf` in dot-product form. -/
theorem leverageOf_eq_dotProduct (g : Fin k → ℝ) : leverageOf g = g ⬝ᵥ g := by
  simp only [leverageOf, dotProduct, pow_two]

/-- **Single-atom Loewner domination**: `t_e · g_e g_eᵀ ⪯ I` — one weighted
rank-one term of a resolution of the identity is dominated by the whole. The
erased sum `I − t_e g_e g_eᵀ = Σ_{c≠e} t_c g_c g_cᵀ` is a sum of PSD terms. -/
theorem single_atom_dominated (D : WeightedDesign m k) (e : Fin m) :
    ((1 : Matrix (Fin k) (Fin k) ℝ)
      - D.weight e • atomMatrix (D.atom e)).PosSemidef := by
  rw [← parseval_erase D e]
  exact Matrix.posSemidef_sum _ fun c _ =>
    (posSemidef_atomMatrix (D.atom c)).smul (D.weight_pos c).le

/-- **The per-atom leverage bound**: in any weighted design (tight frame),
each atom's weighted leverage is at most one — `t_e · ℓ_e ≤ 1`. No single
atom can carry more than the whole identity's worth of a direction. -/
theorem weighted_leverage_le_one (D : WeightedDesign m k) (e : Fin m) :
    D.weight e * leverageOf (D.atom e) ≤ 1 := by
  set probe := D.atom e with hprobe
  set lev := probe ⬝ᵥ probe with hlev
  -- the erased quadratic form at the atom is a sum of nonnegative terms
  have herasedNonneg :
      0 ≤ probe ⬝ᵥ ((∑ c ∈ univ.erase e,
        D.weight c • atomMatrix (D.atom c)) *ᵥ probe) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]
    exact mul_nonneg (D.weight_pos c).le (sq_nonneg _)
  -- read the same form through Parseval's erased identity
  have hreading : probe ⬝ᵥ ((∑ c ∈ univ.erase e,
        D.weight c • atomMatrix (D.atom c)) *ᵥ probe)
      = lev - D.weight e * lev ^ 2 := by
    rw [parseval_erase, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]
  rw [hreading] at herasedNonneg
  -- `lev - t·lev² ≥ 0` with `lev ≥ 0` gives `t·lev ≤ 1`
  have hlevNonneg : 0 ≤ lev := by
    rw [hlev]; exact dotProduct_self_nonneg probe
  have hlevEq : leverageOf (D.atom e) = lev := by
    rw [hlev, hprobe, leverageOf_eq_dotProduct]
  rw [hlevEq]
  rcases eq_or_lt_of_le hlevNonneg with hzero | hpos
  · rw [← hzero]; simpa using zero_le_one
  · have hcancel : D.weight e * lev * lev ≤ 1 * lev := by
      rw [one_mul]; nlinarith [herasedNonneg]
    exact le_of_mul_le_mul_right hcancel hpos

/-- **Leverage decay**: with all weights at least `weightFloor > 0`, every
atom's raw leverage is bounded by `1/weightFloor` — the uniform ceiling that
the `ρ(ℓ̄)` pivot-spread argument consumes. -/
theorem leverage_le_of_weight_floor (D : WeightedDesign m k)
    {weightFloor : ℝ} (hfloor : 0 < weightFloor)
    (hweights : ∀ c, weightFloor ≤ D.weight c) (e : Fin m) :
    leverageOf (D.atom e) ≤ 1 / weightFloor := by
  have hshare := weighted_leverage_le_one D e
  have hlevNonneg : 0 ≤ leverageOf (D.atom e) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hfloorShare : weightFloor * leverageOf (D.atom e)
      ≤ D.weight e * leverageOf (D.atom e) :=
    mul_le_mul_of_nonneg_right (hweights e) hlevNonneg
  rw [le_div_iff₀ hfloor, mul_comm]
  linarith [hshare, hfloorShare]

/-- **The pivot prices leverage over the margin** (resolvent monotonicity,
solution form — no inverse): if the Gram is coercive at `margin` and
`gram · x = atom`, then the pivot form `⟨atom, x⟩` is at most
`|atom|²/margin`. This is the cap dictionary the collar-rate architecture
consumes: at working margin `m`, no atom's pivot exceeds its leverage
divided by `m`. Proof: coercivity floors `⟨atom,x⟩ = ⟨x, gram·x⟩` by
`m·|x|²`, Cauchy–Schwarz caps `⟨atom,x⟩² ≤ |atom|²·|x|²`, and the two
squeeze out `|x|²`. -/
theorem pivot_form_le_leverage_div_margin {k : ℕ}
    {gram : Matrix (Fin k) (Fin k) ℝ} {margin : ℝ}
    (hmarginPos : 0 < margin)
    (hcoercive : ∀ probe : Fin k → ℝ,
      margin * (probe ⬝ᵥ probe) ≤ probe ⬝ᵥ (gram *ᵥ probe))
    {atom solutionVec : Fin k → ℝ}
    (hsolves : gram *ᵥ solutionVec = atom) :
    atom ⬝ᵥ solutionVec ≤ (atom ⬝ᵥ atom) / margin := by
  have hpairs : atom ⬝ᵥ solutionVec
      = solutionVec ⬝ᵥ (gram *ᵥ solutionVec) := by
    rw [hsolves]
    exact dotProduct_comm atom solutionVec
  have hlower : margin * (solutionVec ⬝ᵥ solutionVec)
      ≤ atom ⬝ᵥ solutionVec := by
    rw [hpairs]
    exact hcoercive solutionVec
  have hsolutionNonneg : 0 ≤ solutionVec ⬝ᵥ solutionVec := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun index _ => mul_self_nonneg _
  have hleverageNonneg : 0 ≤ atom ⬝ᵥ atom := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun index _ => mul_self_nonneg _
  have hpivotNonneg : 0 ≤ atom ⬝ᵥ solutionVec :=
    le_trans (mul_nonneg hmarginPos.le hsolutionNonneg) hlower
  have hcauchySchwarz : (atom ⬝ᵥ solutionVec) ^ 2
      ≤ (atom ⬝ᵥ atom) * (solutionVec ⬝ᵥ solutionVec) := by
    have hraw := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ atom solutionVec
    simp only [dotProduct]
    calc (∑ index, atom index * solutionVec index) ^ 2
        ≤ (∑ index, atom index ^ 2) * (∑ index, solutionVec index ^ 2) :=
          hraw
      _ = (∑ index, atom index * atom index)
            * (∑ index, solutionVec index * solutionVec index) := by
          congr 1
          · exact Finset.sum_congr rfl fun index _ => pow_two (atom index)
          · exact Finset.sum_congr rfl fun index _ =>
              pow_two (solutionVec index)
  rcases eq_or_lt_of_le hsolutionNonneg with hsolutionZero | hsolutionPos
  · have hsolutionVecZero : solutionVec = 0 :=
      dotProduct_self_eq_zero.mp hsolutionZero.symm
    rw [hsolutionVecZero, dotProduct_zero]
    exact div_nonneg hleverageNonneg hmarginPos.le
  · rw [le_div_iff₀ hmarginPos]
    nlinarith [hcauchySchwarz, hpivotNonneg, hsolutionPos,
      mul_le_mul_of_nonneg_left hlower hpivotNonneg]

/-- Unit-margin reading: over a dominated Gram (`E ⪰ 1`), every pivot form
is bounded by its own leverage — the seam-side cap at working margin one. -/
theorem pivot_form_le_leverage_of_dominated {k : ℕ}
    {gram : Matrix (Fin k) (Fin k) ℝ}
    (hcoercive : ∀ probe : Fin k → ℝ,
      probe ⬝ᵥ probe ≤ probe ⬝ᵥ (gram *ᵥ probe))
    {atom solutionVec : Fin k → ℝ}
    (hsolves : gram *ᵥ solutionVec = atom) :
    atom ⬝ᵥ solutionVec ≤ atom ⬝ᵥ atom := by
  have hbound := pivot_form_le_leverage_div_margin one_pos
    (fun probe => by rw [one_mul]; exact hcoercive probe) hsolves
  rwa [div_one] at hbound

end Gtz
