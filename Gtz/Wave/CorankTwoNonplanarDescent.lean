import Gtz.Wave.CorankTwoNonplanarSystem
import Gtz.Design.UThreeSixDisjunction
import Gtz.Design.StressFreeNormalizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The four-set descent at the non-planar corner

The ten informative refusals of a corank-two `(6,3)` tie — the nine
one-shared triples and the complement — are exactly the erase-one triples of
the three FOUR-SETS `F_e := {e} ∪ Cᶜ`, one for each inside atom.  This module
prices them through the pivot calculus of the four-set gap
`B_e := S_{F_e} − 1`.

## The descent identity

Two exact trace identities meet.  Parseval reads any matrix through the
weighted atoms (`Gtz.sum_weight_quadForm_eq_trace`):

  `Σ_c t_c g_cᵀ M g_c = tr M` ,

and the four-set reads its own inverse gap through `S_{F_e} = B_e + 1`:

  `Σ_{a ∈ F_e} g_aᵀ B_e⁻¹ g_a = 3 + tr B_e⁻¹` .

Subtracting, the co-weighted pivots of the four-set balance against the two
GHOST readings `x_f := g_fᵀ B_e⁻¹ g_f` (`f` the inside atoms off `F_e`):

  `Σ_{a ∈ F_e} (1 − t_a)(pivot_a − 1) = Σ_f t_f (x_f − 1)` .

## The forced reading, and the reduction

When `B_e ≻ 0`, a tie's refusal of the erase-one triple at `a` reads as
`pivot_a ≥ 1` (`Gtz.posDef_sub_vecMulVec_iff`), and every co-weight
`1 − t_a` is positive, so the left side is nonnegative: a tie FORCES

  `Σ_f t_f (x_f − 1) ≥ 0` — some ghost atom reads the four-set metric at `≥ 1`
  (`Gtz.tie_forces_ghost_reading`).

The reduction (`Gtz.corankTwoNonplanar_absurd_of_core`): if some inside atom
has a positive definite four-set gap on which BOTH ghosts read strictly below
one, the design is not a tie.  The non-planar closure is thereby reduced to
producing that four-set — the geometric core.

Every statement here quantifies over the complement triple, so nothing can
be stated at `(5,3)`: there is no diamond hazard, by construction.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The trace readings

The pairing `tr(M · g gᵀ) = gᵀ M g` is `Gtz.trace_mul_atomMatrix`
(`Gtz.Design.StressFreeNormalizer`). -/

/-- **Parseval reads any matrix.**  The weighted quadratic forms of the atoms
sum to the trace. -/
theorem sum_weight_quadForm_eq_trace (D : WeightedDesign m k)
    (M : Matrix (Fin k) (Fin k) ℝ) :
    ∑ c, D.weight c * (D.atom c ⬝ᵥ (M *ᵥ D.atom c)) = Matrix.trace M := by
  have h := congrArg (fun A => Matrix.trace (M * A)) D.isParseval
  simp only [Matrix.mul_one] at h
  rw [← h, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_mul_atomMatrix]

/-- A subset reads any matrix: the unweighted quadratic forms sum to the
trace against the subset's atom sum. -/
theorem sum_subset_quadForm_eq_trace (D : WeightedDesign m k)
    (F : Finset (Fin m)) (M : Matrix (Fin k) (Fin k) ℝ) :
    ∑ a ∈ F, D.atom a ⬝ᵥ (M *ᵥ D.atom a)
      = Matrix.trace (M * subsetSum D F) := by
  rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun a _ => (trace_mul_atomMatrix M (D.atom a)).symm

/-! ## 2. The four-set and its erase-one triples -/

/-- The complement of the four-set `{e} ∪ Cᶜ` is the inside pair. -/
theorem compl_insert_compl (C : Finset (Fin m)) {e : Fin m} (he : e ∈ C) :
    (insert e Cᶜ)ᶜ = C.erase e := by
  ext c
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_erase]
  constructor
  · intro h
    push_neg at h
    exact h
  · intro h hor
    rcases hor with rfl | hc
    · exact h.1 rfl
    · exact hc h.2

/-- Erasing a label peels its atom off the subset gap. -/
theorem subsetSum_erase_sub_one (D : WeightedDesign m k) (F : Finset (Fin m))
    {a : Fin m} (ha : a ∈ F) :
    subsetSum D (F.erase a) - 1
      = (subsetSum D F - 1) - Matrix.vecMulVec (D.atom a) (D.atom a) := by
  have hstep : subsetSum D (F.erase a) = subsetSum D F - atomMatrix (D.atom a) := by
    rw [subsetSum, subsetSum, ← Finset.sum_erase_add F _ ha]
    abel
  rw [hstep, atomMatrix]
  abel

/-- At `(6,3)` the four-set `{e} ∪ Cᶜ` of an inside atom has card four and
its erase-one subsets have card three. -/
theorem card_insert_compl (C : Finset (Fin 6)) (hcard : C.card = 3)
    {e : Fin 6} (he : e ∈ C) : (insert e Cᶜ).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [he]),
    card_compl_eq_three_of_card_eq_three C hcard]

/-! ## 3. The descent: a tie forces a ghost reading -/

/-- **A tie forces the ghost reading.**  If the four-set gap of an inside
atom is positive definite, the tie's refusal of its four erase-one triples
forces the weighted ghost readings to reach the ghost weight:

  `Σ_{f ∈ C \ {e}} t_f ≤ Σ_{f ∈ C \ {e}} t_f · g_fᵀ B_e⁻¹ g_f` . -/
theorem tie_forces_ghost_reading (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {e : Fin 6} (he : e ∈ C)
    (hPD : (subsetSum D (insert e Cᶜ) - 1).PosDef) :
    ∑ f ∈ C.erase e, D.weight f
      ≤ ∑ f ∈ C.erase e, D.weight f
          * (D.atom f ⬝ᵥ ((subsetSum D (insert e Cᶜ) - 1)⁻¹ *ᵥ D.atom f)) := by
  classical
  set F : Finset (Fin 6) := insert e Cᶜ with hF
  set B : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hB
  have hcardF : F.card = 4 := card_insert_compl C hcard he
  -- every pivot of the four-set is at least one
  have hpivot : ∀ a ∈ F, 1 ≤ D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a) := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    have hstrict : (subsetSum D (F.erase a) - 1).PosDef := by
      rw [subsetSum_erase_sub_one D F ha, ← hB]
      exact (posDef_sub_vecMulVec_iff B hPD (D.atom a)).mpr hlt
    have hcarda : (F.erase a).card = 3 := by
      rw [Finset.card_erase_of_mem ha, hcardF]
    exact htie.2 (F.erase a) hcarda hstrict
  -- the weighted trace reading, split at the four-set
  have hweighted := sum_weight_quadForm_eq_trace D B⁻¹
  rw [← Finset.sum_add_sum_compl F, compl_insert_compl C he] at hweighted
  -- the unweighted four-set reading
  have hunweighted := sum_subset_quadForm_eq_trace D F B⁻¹
  have hSF : subsetSum D F = B + 1 := by rw [hB]; abel
  have hBinvB : B⁻¹ * B = 1 :=
    Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos))
  have htraceSF : Matrix.trace (B⁻¹ * subsetSum D F)
      = 3 + Matrix.trace B⁻¹ := by
    rw [hSF, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add, hBinvB,
      Matrix.trace_one]
    norm_num
  rw [htraceSF] at hunweighted
  -- each weight is strictly below one
  have hwlt : ∀ a : Fin 6, D.weight a < 1 := by
    intro a
    have hsum := D.weight_sum_one
    have hsplit : ∑ c, D.weight c
        = D.weight a + ∑ c ∈ Finset.univ.erase a, D.weight c := by
      rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    have hne : (Finset.univ.erase a).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, Fintype.card_fin]
      norm_num
    have hpos : 0 < ∑ c ∈ Finset.univ.erase a, D.weight c :=
      Finset.sum_pos (fun c _ => D.weight_pos c) hne
    linarith [hsum, hsplit, hpos]
  -- the co-weighted pivot surplus is nonnegative
  have hsurplus : 0 ≤ ∑ a ∈ F, (1 - D.weight a)
      * (D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a) - 1) :=
    Finset.sum_nonneg fun a ha =>
      mul_nonneg (by linarith [hwlt a]) (by linarith [hpivot a ha])
  -- expand the surplus through the two trace identities
  have hexpand : ∑ a ∈ F, (1 - D.weight a)
        * (D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a) - 1)
      = (∑ a ∈ F, D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a))
        - (∑ a ∈ F, D.weight a * (D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a)))
        - (F.card : ℝ) + ∑ a ∈ F, D.weight a := by
    have h1 : ∀ a ∈ F, (1 - D.weight a) * (D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a) - 1)
        = D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a)
          - D.weight a * (D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a)) - 1 + D.weight a :=
      fun a _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  have hwsum := D.weight_sum_one
  rw [← Finset.sum_add_sum_compl F, compl_insert_compl C he] at hwsum
  rw [hexpand, hunweighted, hcardF] at hsurplus
  -- close by linear arithmetic over the two ledger readings
  have hW := hweighted
  push_cast at hsurplus
  linarith [hsurplus, hW, hwsum]

/-! ## 4. The reduction -/

/-- **The reduction of the non-planar corner.**  If some inside atom carries
a positive definite four-set gap on which both ghost atoms read strictly
below one, the design is not a tie.  The closure is reduced to producing
that four-set. -/
theorem not_isTie_of_ghost_readings_lt (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {e : Fin 6} (he : e ∈ C)
    (hPD : (subsetSum D (insert e Cᶜ) - 1).PosDef)
    (hghost : ∀ f ∈ C.erase e,
      D.atom f ⬝ᵥ ((subsetSum D (insert e Cᶜ) - 1)⁻¹ *ᵥ D.atom f) < 1) :
    ¬ IsTie D := by
  intro htie
  have hforced := tie_forces_ghost_reading D htie C hcard he hPD
  have hlt : ∑ f ∈ C.erase e, D.weight f
      * (D.atom f ⬝ᵥ ((subsetSum D (insert e Cᶜ) - 1)⁻¹ *ᵥ D.atom f))
      < ∑ f ∈ C.erase e, D.weight f := by
    have hne : (C.erase e).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem he, hcard]
      norm_num
    refine Finset.sum_lt_sum_of_nonempty hne fun f hf => ?_
    have := hghost f hf
    nlinarith [D.weight_pos f, this]
  linarith [hforced, hlt]

end Gtz
