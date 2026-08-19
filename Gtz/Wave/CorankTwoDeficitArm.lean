import Gtz.Wave.GhostWeightedDeficit
import Gtz.Wave.CorankTwoArm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The corank-two arm on the weighted deficit, and the swap-bracket form

`Gtz.corankTwoGap_absurd` closes the corank-two arm from
`Gtz.NonplanarGhostResidual`, which asks a ghost pair to have a SHORT block:
both swaps positive definite.  The four-set descent
(`Gtz.tie_forces_ghost_reading`) supplies much less than that.  It supplies one
weighted combination, and `Gtz.not_isTie_of_weightedGhostDeficit` refutes the
tie from that combination alone.  This module rebuilds the arm on the weighted
surface.

## The swap brackets

Write `a = P_ff`, `b = P_hh`, `c = P_fh` for the ghost block of six-set pivots.
Moving the whole weighted deficit to one side factors it into the two SWAP
BRACKETS (`Gtz.weightedDeficit_eq_swapBrackets`)

  `t_f·[(1−b)(2a−1) + 2c²] + t_h·[(1−a)(2b−1) + 2c²]` ,

and each bracket is the negated Sylvester condition of its own swap
(`Gtz.swapPD_iff_ghostBlock`).  So `Gtz.GhostBlockShort` asks BOTH brackets to
be negative, while `Gtz.GhostDeficitShort` asks only their weighted sum to be
negative.  The second is strictly weaker
(`Gtz.ghostDeficitShort_of_ghostBlockShort`), and it is what the descent
actually refutes.

## The tie belongs in the residual

`Gtz.NonplanarGhostResidual` carries no tie hypothesis, so it asks for a short
ghost block at EVERY non-planar corank-two corner of every design.  That is
false: `Gtz.not_nonplanarGhostResidual` exhibits a design whose corner admits no
short selector at all, with every weight above `1/20`.  The arm applies the
residual only under a tie and a primitive design, so
`Gtz.NonplanarDeficitResidual` carries both hypotheses, which weakens what a
producer must prove.
`Gtz.corankTwoGap_absurd'` and `Gtz.gapKernel_subsingleton_of_isTie'` are the
arm and the arm statement over the widened, correctly hypothesised residual.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The swap brackets -/

/-- **The weighted deficit is the weighted sum of the swap brackets.**  A ring
identity: the deficit of `Gtz.not_isTie_of_weightedGhostDeficit`, moved to one
side, is `t_f` times the swap bracket at `f` plus `t_h` times the swap bracket
at `h`. -/
theorem weightedDeficit_eq_swapBrackets (a b c tf th : ℝ) :
    tf * (a * (1 - b) + c ^ 2) + th * (b * (1 - a) + c ^ 2)
        - (tf + th) * ((1 - a) * (1 - b) - c ^ 2)
      = tf * ((1 - b) * (2 * a - 1) + 2 * c ^ 2)
        + th * ((1 - a) * (2 * b - 1) + 2 * c ^ 2) := by
  ring

/-- **The swap bracket in cofactor form.**  `(1−b)(2a−1) + 2c² = 2a + b − 1 − 2(ab − c²)`:
the bracket is the trace of the ghost block plus its own pivot, less one, less
twice the block determinant. -/
theorem swapBracket_eq_traceForm (a b c : ℝ) :
    (1 - b) * (2 * a - 1) + 2 * c ^ 2 = 2 * a + b - 1 - 2 * (a * b - c ^ 2) := by
  ring

/-! ## 2. The weighted ghost deficit at a pair -/

/-- **The ghost pair is deficient.**  The two ghost pivots sit below one, the
block determinant is positive, and the weighted sum of the swap brackets is
negative.  `Gtz.GhostBlockShort` asks each bracket to be negative separately. -/
def GhostDeficitShort (D : WeightedDesign 6 3) (f h : Fin 6) : Prop :=
  sixSetPivot D f f < 1 ∧ sixSetPivot D h h < 1
    ∧ 0 < (1 - sixSetPivot D f f) * (1 - sixSetPivot D h h)
        - sixSetPivot D f h ^ 2
    ∧ D.weight f * ((1 - sixSetPivot D h h) * (2 * sixSetPivot D f f - 1)
          + 2 * sixSetPivot D f h ^ 2)
        + D.weight h * ((1 - sixSetPivot D f f) * (2 * sixSetPivot D h h - 1)
          + 2 * sixSetPivot D f h ^ 2) < 0

/-- **A short block is deficient.**  Both swap brackets negative forces their
weighted sum negative, and the block determinant is at least half the co-pivot
of the smaller ghost. -/
theorem ghostDeficitShort_of_ghostBlockShort (D : WeightedDesign 6 3)
    {f h : Fin 6} (hshort : GhostBlockShort D f h) : GhostDeficitShort D f h := by
  obtain ⟨hf2, hh2, hcf, hch⟩ := hshort
  have hfpos : 0 < D.weight f := D.weight_pos f
  have hhpos : 0 < D.weight h := D.weight_pos h
  have ha1 : sixSetPivot D f f < 1 := by linarith
  have hb1 : sixSetPivot D h h < 1 := by linarith
  refine ⟨ha1, hb1, by nlinarith [hcf, hb1], ?_⟩
  have hBf : (1 - sixSetPivot D h h) * (2 * sixSetPivot D f f - 1)
      + 2 * sixSetPivot D f h ^ 2 < 0 := by nlinarith [hcf]
  have hBh : (1 - sixSetPivot D f f) * (2 * sixSetPivot D h h - 1)
      + 2 * sixSetPivot D f h ^ 2 < 0 := by nlinarith [hch]
  have h1 := mul_neg_of_pos_of_neg hfpos hBf
  have h2 := mul_neg_of_pos_of_neg hhpos hBh
  linarith

/-- **The non-planar corner closes from a deficient ghost pair.**  The four-set
descent needs only the weighted combination. -/
theorem corankTwoNonplanar_absurd_of_ghostDeficit (D : WeightedDesign 6 3)
    (htie : IsTie D) (C : Finset (Fin 6)) (hcard : C.card = 3)
    {e f h : Fin 6} (he : e ∈ C) (hfh : f ≠ h) (herase : C.erase e = {f, h})
    (hdef : GhostDeficitShort D f h) : False := by
  obtain ⟨ha, hb, hdet, hbrackets⟩ := hdef
  refine not_isTie_of_weightedGhostDeficit D C hcard he hfh herase ha hb hdet
    ?_ htie
  have hkey := weightedDeficit_eq_swapBrackets (sixSetPivot D f f)
    (sixSetPivot D h h) (sixSetPivot D f h) (D.weight f) (D.weight h)
  linarith

/-! ## 3. The residual, with the hypotheses the arm supplies -/

/-- **The residual of the corank-two arm on the weighted surface.**  At every
non-planar corner of a primitive tie, some inside atom leaves a ghost pair whose
weighted swap brackets are deficient. -/
def NonplanarDeficitResidual (D : WeightedDesign 6 3) : Prop :=
  IsTie D → IsPrimitiveDesign D →
    ∀ C : Finset (Fin 6), C.card = 3 → ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ,
      u ⬝ᵥ u = 1 → subsetSum D C - 1 = lam • atomMatrix u →
      (∃ d ∈ Cᶜ, D.atom d ⬝ᵥ u ≠ 0) →
      ∃ e ∈ C, ∃ f h : Fin 6, f ≠ h ∧ C.erase e = {f, h} ∧ GhostDeficitShort D f h

/-- **The weighted residual is wider.**  A short ghost block at every corner
gives a deficient ghost pair at every corner of a primitive tie. -/
theorem nonplanarDeficitResidual_of_ghostResidual (D : WeightedDesign 6 3)
    (hres : NonplanarGhostResidual D) : NonplanarDeficitResidual D := by
  intro _ _ C hcard lam hlam u hunit hgap hnp
  obtain ⟨e, he, f, h, hfh, herase, hshort⟩ := hres C hcard lam hlam u hunit hgap hnp
  exact ⟨e, he, f, h, hfh, herase, ghostDeficitShort_of_ghostBlockShort D hshort⟩

/-! ## 4. The arm -/

/-- **A corank-two gap is impossible, on the weighted surface.** -/
theorem corankTwoGap_absurd' (D : WeightedDesign 6 3) (htie : IsTie D)
    (hprimitive : IsPrimitiveDesign D) (hres : NonplanarDeficitResidual D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) (hdom : Dominates D C)
    {kernelOne kernelTwo : Fin 3 → ℝ}
    (hone : (subsetSum D C - 1) *ᵥ kernelOne = 0)
    (htwo : (subsetSum D C - 1) *ᵥ kernelTwo = 0)
    (hcross : crossProduct kernelOne kernelTwo ≠ 0) : False := by
  classical
  obtain ⟨lam, u, hlam, hunit, hgap⟩ :=
    exists_rankOneGap_of_twoKernel hdom
      (transpose_subsetSum_sub_one D C) hone htwo hcross
  rcases eq_or_lt_of_le hlam with hzero | hpos
  · refine subsetSum_ne_one_of_isTie_sixThree D htie C hcard ?_
    have hgapzero : subsetSum D C - 1 = 0 := by
      rw [hgap, ← hzero, zero_smul]
    exact sub_eq_zero.mp hgapzero
  · by_cases hplanar : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0
    · exact corankTwoPlanar_absurd D htie hprimitive C hcard hlam hunit hgap hplanar
    · push_neg at hplanar
      obtain ⟨d0, hd0, hread⟩ := hplanar
      obtain ⟨e, he, f, h, hfh, herase, hdef⟩ :=
        hres htie hprimitive C hcard lam hpos u hunit hgap ⟨d0, hd0, hread⟩
      exact corankTwoNonplanar_absurd_of_ghostDeficit D htie C hcard he hfh herase hdef

/-- **The arm statement on the weighted surface.**  Every weak dominator of a
primitive `(6,3)` tie has a gap of corank exactly one. -/
theorem gapKernel_subsingleton_of_isTie' (D : WeightedDesign 6 3) (htie : IsTie D)
    (hprimitive : IsPrimitiveDesign D) (hres : NonplanarDeficitResidual D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) (hdom : Dominates D C)
    (kernelOne kernelTwo : Fin 3 → ℝ)
    (hone : (subsetSum D C - 1) *ᵥ kernelOne = 0)
    (htwo : (subsetSum D C - 1) *ᵥ kernelTwo = 0) :
    crossProduct kernelOne kernelTwo = 0 := by
  by_contra hcross
  exact corankTwoGap_absurd' D htie hprimitive hres C hcard hdom hone htwo hcross

end Gtz
