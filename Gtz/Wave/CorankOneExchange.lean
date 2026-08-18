/-
# The corank-one exchange system

A tie refuses every triple.  At a weakly dominating triple `C` whose gap has a
null LINE (corank one), each refusal of a one-atom exchange has an exact scalar
form, because the exchanged gap is a rank-one downdate of a positive definite
anchor.  This module lands that scalar form and its aggregate.

## The anchor

`exchangeAnchor D C d = (S_C - 1) + g_d g_d^T` for an outside atom `d`.  The
gap is positive semidefinite at a weak dominator and vanishes only on the null
line.  If the added atom reads the null direction (`g_d . u /= 0`), the anchor
is positive definite (`Gtz.exchangeAnchor_posDef`) — the atom plugs the one
soft direction.

## The three laws

* **The exchange law** (`Gtz.one_le_exchange_reading_of_isTie`).  The swapped
  triple `C - e + d` is a rank-one downdate of the anchor by the dropped atom.
  The tie refuses it, and the landed rank-one Schur step
  (`Gtz.posDef_sub_vecMulVec_iff`) prices the refusal exactly:

    `1 <= g_e . (anchor⁻¹ g_e)`   for every `e` in `C`, every `d` off `C`.

  Nine inequalities at `(6,3)`, six at `(5,3)`.  No slack is lost: the scalar
  form is equivalent to the refusal, not merely implied by it.

* **The self-reading collapses** (`Gtz.anchor_selfReading_eq_one`).  The added
  atom itself reads exactly one in the anchor metric:
  `g_d . (anchor⁻¹ g_d) = 1`.  The null component of `g_d` saturates the
  anchor.  As a corollary, every inside atom is at least as long as the added
  atom in the anchor metric.

* **The harmonic law** (`Gtz.one_le_trace_anchorInv_of_isTie`).  The three
  exchange readings sum to `trace(anchor⁻¹) + card C - 1`.  Three refusals
  give `trace(anchor⁻¹) >= 1`: the anchor of a tie can not be uniformly
  large.  In eigenvalues, `1/mu_1 + 1/mu_2 + 1/mu_3 >= 1` at every anchor.

## The plane reading, for the record

Split every atom along a unit null direction: `g_c = a_c u + h_c` with
`h_c ⊥ u`.  Write `B` for the plane block of the gap, positive definite at
corank one.  The Schur complement of the anchor at the `u` coordinate is `B`,
independent of the added atom.  The exchange law then reads

    `(a_e h_d - a_d h_e)^T B⁻¹ (a_e h_d - a_d h_e)  >=  a_d^2 - a_e^2`,

and `a_e h_d - a_d h_e` is the kernel-plane component of the wedge
`g_e ∧ g_d`.  The refusals bound from below the exact functional that vanishes
at a parallel pair — the conclusion of the hinge.  The kernel form above stays
coordinate-free; the plane form guides the search and the calibration.

## Scope

Everything is stated at rank three and any size, so the `(5,3)` diamond
calibrates the system.  The size-six content — the refusal of the complement
triple — is NOT here; it needs `|C^c| = 3` and lives with the assembly.
-/
import Gtz.Wave.CorankOneNormalForm
import Gtz.LinAlg.SchurRankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. A positive semidefinite form vanishes only with its vector -/

/-- **A null form direction is a null vector.**  At a positive semidefinite
symmetric matrix, a direction where the quadratic form vanishes is in the
kernel.  The proof is the discriminant of the form along a perturbation. -/
theorem mulVec_eq_zero_of_form_eq_zero {k : ℕ} {G : Matrix (Fin k) (Fin k) ℝ}
    (hpsd : G.PosSemidef) (hsym : Gᵀ = G) {u : Fin k → ℝ}
    (hform : u ⬝ᵥ (G *ᵥ u) = 0) : G *ᵥ u = 0 := by
  have hforms : ∀ x : Fin k → ℝ, 0 ≤ x ⬝ᵥ (G *ᵥ x) := by
    intro x
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 x
    rwa [star_trivial] at h
  have hswap : ∀ x : Fin k → ℝ, u ⬝ᵥ (G *ᵥ x) = x ⬝ᵥ (G *ᵥ u) := by
    intro x
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]
  have hkey : ∀ x : Fin k → ℝ, x ⬝ᵥ (G *ᵥ u) = 0 := by
    intro x
    have hquad : ∀ t : ℝ, 0 ≤ (x ⬝ᵥ (G *ᵥ x)) * (t * t)
        + (2 * (x ⬝ᵥ (G *ᵥ u))) * t + 0 := by
      intro t
      have h0 := hforms (u + t • x)
      have hexpand : (u + t • x) ⬝ᵥ (G *ᵥ (u + t • x))
          = (x ⬝ᵥ (G *ᵥ x)) * (t * t) + (2 * (x ⬝ᵥ (G *ᵥ u))) * t + 0 := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
        rw [dotProduct_add, add_dotProduct, add_dotProduct]
        rw [dotProduct_smul, smul_dotProduct, smul_dotProduct]
        rw [dotProduct_smul]
        rw [hswap x]
        rw [hform]
        ring
      rw [hexpand] at h0
      exact h0
    have hdisc := discrim_le_zero hquad
    rw [discrim] at hdisc
    nlinarith [sq_nonneg (x ⬝ᵥ (G *ᵥ u)), hdisc]
  funext coord
  have hcoord := hkey (Pi.single coord 1)
  rw [single_dotProduct, one_mul] at hcoord
  simpa using hcoord

/-! ## 2. The exchange anchor -/

/-- **The exchange anchor**: the gap of the dominating triple plus one outside
atom.  The swapped triples are rank-one downdates of this matrix. -/
noncomputable def exchangeAnchor (D : WeightedDesign m 3) (C : Finset (Fin m))
    (d : Fin m) : Matrix (Fin 3) (Fin 3) ℝ :=
  subsetSum D C - 1 + atomMatrix (D.atom d)

/-- The anchor is symmetric. -/
theorem transpose_exchangeAnchor (D : WeightedDesign m 3) (C : Finset (Fin m))
    (d : Fin m) : (exchangeAnchor D C d)ᵀ = exchangeAnchor D C d := by
  rw [exchangeAnchor, Matrix.transpose_add, transpose_subsetSum_sub_one]
  congr 1
  ext firstIndex secondIndex
  simp [atomMatrix, Matrix.vecMulVec_apply, mul_comm]

/-- The quadratic form of the anchor splits into the gap form and the squared
reading of the added atom. -/
theorem exchangeAnchor_form (D : WeightedDesign m 3) (C : Finset (Fin m))
    (d : Fin m) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (exchangeAnchor D C d *ᵥ probe)
      = probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) + (D.atom d ⬝ᵥ probe) ^ 2 := by
  rw [exchangeAnchor, Matrix.add_mulVec, dotProduct_add]
  congr 1
  rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    dotProduct_comm]
  ring

/-- **The anchor is positive definite.**  The gap form is nonnegative at a weak
dominator and vanishes only on the null line.  An added atom that reads the
null direction removes the one soft direction. -/
theorem exchangeAnchor_posDef (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) {d : Fin m}
    (hread : D.atom d ⬝ᵥ nullDir ≠ 0) : (exchangeAnchor D C d).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_exchangeAnchor D C d),
      fun probe hprobe => ?_⟩
  rw [star_trivial, exchangeAnchor_form]
  have hgap : 0 ≤ probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    rwa [star_trivial] at h
  rcases lt_or_eq_of_le hgap with hgapPos | hgapZero
  · nlinarith [sq_nonneg (D.atom d ⬝ᵥ probe)]
  rcases lt_or_eq_of_le (sq_nonneg (D.atom d ⬝ᵥ probe)) with hreadPos | hreadZero
  · nlinarith
  exfalso
  obtain ⟨scale, hscale⟩ := hline.2.2 probe hgapZero.symm
  have hzero : D.atom d ⬝ᵥ probe = 0 := by
    have := hreadZero.symm
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  rw [hscale, dotProduct_smul, smul_eq_mul] at hzero
  rcases mul_eq_zero.mp hzero with hscaleZero | hreadNull
  · exact hprobe (by rw [hscale, hscaleZero, zero_smul])
  · exact hread hreadNull

/-- The swapped gap is the rank-one downdate of the anchor by the dropped
atom. -/
theorem subsetSum_swap_sub_one (D : WeightedDesign m 3) (C : Finset (Fin m))
    {e d : Fin m} (he : e ∈ C) (hd : d ∉ C) :
    subsetSum D (insert d (C.erase e)) - 1
      = exchangeAnchor D C d - Matrix.vecMulVec (D.atom e) (D.atom e) := by
  have hdErase : d ∉ C.erase e := fun hmem => hd (Finset.mem_of_mem_erase hmem)
  rw [exchangeAnchor, subsetSum, Finset.sum_insert hdErase,
    Finset.sum_erase_eq_sub he]
  show atomMatrix (D.atom d) + (subsetSum D C - atomMatrix (D.atom e)) - 1
      = subsetSum D C - 1 + atomMatrix (D.atom d)
        - Matrix.vecMulVec (D.atom e) (D.atom e)
  rw [show Matrix.vecMulVec (D.atom e) (D.atom e) = atomMatrix (D.atom e) from rfl]
  abel

/-! ## 3. The exchange law -/

/-- **THE EXCHANGE LAW.**  At a tie, the refusal of every one-atom exchange of
a corank-one weak dominator is one scalar inequality: the dropped atom reads at
least one in the anchor metric.

The law is exact.  The rank-one Schur step is an equivalence, so the scalar
form carries the whole content of the refusal — no selector loss. -/
theorem one_le_exchange_reading_of_isTie (D : WeightedDesign m 3)
    (htie : IsTie D) (C : Finset (Fin m)) (hcard : C.card = 3)
    (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) {e d : Fin m} (he : e ∈ C) (hd : d ∉ C)
    (hread : D.atom d ⬝ᵥ nullDir ≠ 0) :
    1 ≤ D.atom e ⬝ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) := by
  have hanchor := exchangeAnchor_posDef D C hdominates hline hread
  have hcardSwap : (insert d (C.erase e)).card = 3 := by
    rw [card_swap_eq_card hd he, hcard]
  have hrefusal := htie.2 (insert d (C.erase e)) hcardSwap
  rw [subsetSum_swap_sub_one D C he hd] at hrefusal
  by_contra hless
  push Not at hless
  exact hrefusal ((posDef_sub_vecMulVec_iff (exchangeAnchor D C d) hanchor
    (D.atom e)).mpr hless)

/-- **The self-reading is exactly one.**  The added atom saturates its own
anchor: its null component is the whole kernel budget of the gap. -/
theorem anchor_selfReading_eq_one (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) {d : Fin m}
    (hread : D.atom d ⬝ᵥ nullDir ≠ 0) :
    D.atom d ⬝ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom d) = 1 := by
  have hanchor := exchangeAnchor_posDef D C hdominates hline hread
  have hdet : IsUnit (exchangeAnchor D C d).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hanchor.det_pos)
  set solved : Fin 3 → ℝ := (exchangeAnchor D C d)⁻¹ *ᵥ D.atom d with hsolved
  have happly : exchangeAnchor D C d *ᵥ solved = D.atom d := by
    rw [hsolved, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
  have hgapNull : (subsetSum D C - 1) *ᵥ nullDir = 0 :=
    mulVec_eq_zero_of_form_eq_zero hdominates
      (transpose_subsetSum_sub_one D C) hline.2.1
  have hexpand : exchangeAnchor D C d *ᵥ solved
      = (subsetSum D C - 1) *ᵥ solved + (D.atom d ⬝ᵥ solved) • D.atom d := by
    rw [exchangeAnchor, Matrix.add_mulVec, atomMatrix, vecMulVec_mulVec_eq]
  have hsplit : (subsetSum D C - 1) *ᵥ solved
      + (D.atom d ⬝ᵥ solved) • D.atom d = D.atom d := by
    rw [← hexpand, happly]
  have hnullRead := congrArg (fun vec => nullDir ⬝ᵥ vec) hsplit
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hnullRead
  have hgapTerm : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ solved) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      transpose_subsetSum_sub_one, hgapNull]
    simp
  rw [hgapTerm, zero_add] at hnullRead
  have hreadComm : nullDir ⬝ᵥ D.atom d = D.atom d ⬝ᵥ nullDir := dotProduct_comm _ _
  rw [hreadComm] at hnullRead
  have hone : D.atom d ⬝ᵥ solved * (D.atom d ⬝ᵥ nullDir)
      = 1 * (D.atom d ⬝ᵥ nullDir) := by
    rw [one_mul]
    exact hnullRead
  exact mul_right_cancel₀ hread hone

/-! ## 4. The harmonic law -/

/-- The sum of the readings over a subset is a trace against the subset sum.
The per-atom step is the landed `Gtz.trace_mul_atomMatrix`
(Gtz/Design/StressFreeNormalizer.lean). -/
theorem sum_readings_eq_trace (D : WeightedDesign m 3) (C : Finset (Fin m))
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ e ∈ C, D.atom e ⬝ᵥ (A *ᵥ D.atom e) = (A * subsetSum D C).trace := by
  rw [subsetSum, Finset.mul_sum, Matrix.trace_sum]
  exact (Finset.sum_congr rfl fun e _ => (trace_mul_atomMatrix A (D.atom e)).symm)

/-- **THE HARMONIC LAW.**  At a tie, the inverse anchor of every outside atom
that reads the null direction has trace at least one.  The three exchange
refusals sum against the Parseval structure of the dominating triple: the
anchor of a tie is never uniformly large. -/
theorem one_le_trace_anchorInv_of_isTie (D : WeightedDesign m 3)
    (htie : IsTie D) (C : Finset (Fin m)) (hcard : C.card = 3)
    (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) {d : Fin m} (hd : d ∉ C)
    (hread : D.atom d ⬝ᵥ nullDir ≠ 0) :
    1 ≤ ((exchangeAnchor D C d)⁻¹).trace := by
  have hanchor := exchangeAnchor_posDef D C hdominates hline hread
  have hdet : IsUnit (exchangeAnchor D C d).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hanchor.det_pos)
  have hlower : (3 : ℝ)
      ≤ ∑ e ∈ C, D.atom e ⬝ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) := by
    have hbound : ∀ e ∈ C,
        (1 : ℝ) ≤ D.atom e ⬝ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) :=
      fun e he => one_le_exchange_reading_of_isTie D htie C hcard hdominates
        hline he hd hread
    calc (3 : ℝ) = ∑ _e ∈ C, (1 : ℝ) := by
          rw [Finset.sum_const, hcard]; norm_num
      _ ≤ _ := Finset.sum_le_sum hbound
  have hsubset : subsetSum D C
      = 1 + exchangeAnchor D C d - atomMatrix (D.atom d) := by
    rw [exchangeAnchor]; abel
  have hidentity : ∑ e ∈ C, D.atom e ⬝ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e)
      = ((exchangeAnchor D C d)⁻¹).trace + 2 := by
    rw [sum_readings_eq_trace, hsubset, Matrix.mul_sub, Matrix.mul_add,
      Matrix.mul_one, Matrix.trace_sub, Matrix.trace_add,
      Matrix.nonsing_inv_mul _ hdet, trace_mul_atomMatrix,
      anchor_selfReading_eq_one D C hdominates hline hread]
    have hone : (1 : Matrix (Fin 3) (Fin 3) ℝ).trace = (3 : ℝ) := by
      simp [Matrix.trace_one]
    rw [hone]
    ring
  linarith [hidentity ▸ hlower]

/-- **Every inside atom dominates the added atom in the anchor metric.**  The
exchange law against the collapsed self-reading. -/
theorem selfReading_le_exchange_reading_of_isTie (D : WeightedDesign m 3)
    (htie : IsTie D) (C : Finset (Fin m)) (hcard : C.card = 3)
    (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) {e d : Fin m} (he : e ∈ C) (hd : d ∉ C)
    (hread : D.atom d ⬝ᵥ nullDir ≠ 0) :
    D.atom d ⬝ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom d)
      ≤ D.atom e ⬝ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) := by
  rw [anchor_selfReading_eq_one D C hdominates hline hread]
  exact one_le_exchange_reading_of_isTie D htie C hcard hdominates hline he hd
    hread

end Gtz
