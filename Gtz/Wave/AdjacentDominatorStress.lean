import Gtz.Wave.CorankOneExchange
import Gtz.Wave.CorankOnePropagation
import Gtz.Wave.DiamondConicStress
import Gtz.Wave.ShareRigidity
import Gtz.Design.LineFreeConicBridge
import Gtz.LinAlg.SchurRankOne
import Gtz.Reduction.RayleighCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The shared anchor of adjacent dominators, and the four-set exchange ledger

Two weakly dominating triples of one design that differ by a single swap share
one positive definite matrix: the gap of their four-atom union.
`Gtz.exchangeAnchor_eq_insert` reads the exchange anchor as that four-set gap,
and `Gtz.exchangeAnchor_swap` shows the swap and its reverse use the SAME
anchor.  Everything an adjacency says is geometry of one metric `M⁻¹`.

The ledger of that metric, at a tie:

* every one-atom removal of the four-set has reading at least one
  (`Gtz.one_le_removal_reading_of_isTie`), a removal weakly dominates exactly
  at reading at most one (`Gtz.removal_dominates_iff_reading_le_one`), and
  strictly below one is impossible at a tie — so removals that dominate sit
  EXACTLY at reading one;
* the readings of the four atoms total `3 + tr M⁻¹`
  (`Gtz.fourSet_reading_sum`);
* the weighted readings of ALL atoms total `tr M⁻¹`
  (`Gtz.weighted_reading_trace`), so the free readings of the four-set beat
  the outside spend by exactly three (`Gtz.anchor_budget_identity`) — the
  free-mass budget of `Gtz/Wave/CorankOneNormalForm.lean`, transported into
  the anchor metric, where it holds with a POSITIVE DEFINITE anchor and no
  corank hypothesis;
* at a tie the free readings of the four-set are at least three
  (`Gtz.three_le_freeReading_of_isTie`).

The kernel of every one-atom downdate of the anchor is computed exactly
(`Gtz.anchor_downdate_kernel`), so an equality swap hands the next dominator a
full `Gtz.GapNullLine` (`Gtz.gapNullLine_swap_of_reading_eq_one`) and the whole
corank-one machinery iterates along equality swaps with no new hypothesis.

## Step zero of the campaign, and the corrected residual

`Gtz/Wave/DiamondConicStress.lean` decides the mandated step-zero question:
`Gtz.diamondDesign` is STRESS-FREE (`Gtz.diamondDesign_stressFree`) and lies on
an explicit conic (`Gtz.diamondDesign_on_conic`).  The diamond is a primitive
tie with equality readings, so the conjecture "adjacency forces a parallel
pair or a stress" is FALSE at `(5,3)`.  The correct dichotomy must read the
CONIC: at `(6,3)` a common conic is a stress and a primitive tie has neither,
while at `(5,3)` every design lies on a conic and the diamond escapes.  The
open residual of this lane is therefore: at a `(6,3)` tie, an equality swap
forces the six atoms onto a common conic or two atoms parallel.  The split
diamond calibrates it — its equality swaps live on the diamond part and its
parallel pair sits outside the four-set, so the conclusion cannot localize to
the four atoms of the swap and any proof must spend refusals beyond them.
-/

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The anchor is the four-set gap, shared by the swap and its reverse -/

/-- The exchange anchor is the gap of the four-atom union. -/
theorem exchangeAnchor_eq_insert (D : WeightedDesign m 3) (C : Finset (Fin m))
    {d : Fin m} (hd : d ∉ C) :
    exchangeAnchor D C d = subsetSum D (insert d C) - 1 := by
  have hins : subsetSum D (insert d C)
      = atomMatrix (D.atom d) + subsetSum D C := by
    rw [subsetSum, subsetSum, Finset.sum_insert hd]
  rw [exchangeAnchor, hins]
  abel

/-- **THE SWAP AND ITS REVERSE SHARE ONE ANCHOR.**  Exchanging `e` out and `d`
in, and the reverse exchange at the swapped triple, read the same matrix. -/
theorem exchangeAnchor_swap (D : WeightedDesign m 3) (C : Finset (Fin m))
    {e d : Fin m} (he : e ∈ C) (hd : d ∉ C) :
    exchangeAnchor D (insert d (C.erase e)) e = exchangeAnchor D C d := by
  have hne : e ≠ d := fun h => hd (h ▸ he)
  have he' : e ∉ insert d (C.erase e) := by
    simp [Finset.mem_insert, hne]
  have hset : insert e (insert d (C.erase e)) = insert d C := by
    rw [Finset.insert_comm, Finset.insert_erase he]
  rw [exchangeAnchor_eq_insert D _ he', hset, exchangeAnchor_eq_insert D C hd]

/-- Removing one atom from a set moves the gap down by one atom matrix. -/
theorem erase_gap_eq (D : WeightedDesign m 3) {F : Finset (Fin m)} {z : Fin m}
    (hz : z ∈ F) :
    subsetSum D (F.erase z) - 1
      = (subsetSum D F - 1) - Matrix.vecMulVec (D.atom z) (D.atom z) := by
  have hsum : subsetSum D (F.erase z) = subsetSum D F - atomMatrix (D.atom z) := by
    rw [subsetSum, subsetSum, Finset.sum_erase_eq_sub hz]
  rw [hsum]
  simp only [atomMatrix]
  abel

/-! ## 2. The removal ledger of a positive definite four-set gap -/

/-- A one-atom removal weakly dominates exactly at reading at most one. -/
theorem removal_dominates_iff_reading_le_one (D : WeightedDesign m 3)
    {F : Finset (Fin m)} (hM : (subsetSum D F - 1).PosDef) {z : Fin m}
    (hz : z ∈ F) :
    Dominates D (F.erase z)
      ↔ D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z) ≤ 1 := by
  show (subsetSum D (F.erase z) - 1).PosSemidef ↔ _
  rw [erase_gap_eq D hz]
  exact posSemidef_sub_vecMulVec_iff _ hM _

/-- A one-atom removal dominates strictly exactly at reading below one. -/
theorem removal_posDef_iff_reading_lt_one (D : WeightedDesign m 3)
    {F : Finset (Fin m)} (hM : (subsetSum D F - 1).PosDef) {z : Fin m}
    (hz : z ∈ F) :
    (subsetSum D (F.erase z) - 1).PosDef
      ↔ D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z) < 1 := by
  rw [erase_gap_eq D hz]
  exact posDef_sub_vecMulVec_iff _ hM _

/-- **AT A TIE, EVERY REMOVAL READING IS AT LEAST ONE.**  The tie refuses the
removed triple, and a reading below one would dominate it strictly. -/
theorem one_le_removal_reading_of_isTie (D : WeightedDesign m 3)
    (htie : IsTie D) {F : Finset (Fin m)} (hcard : F.card = 4)
    (hM : (subsetSum D F - 1).PosDef) {z : Fin m} (hz : z ∈ F) :
    1 ≤ D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z) := by
  rcases lt_or_ge (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z)) 1 with hlt | hge
  · exact absurd ((removal_posDef_iff_reading_lt_one D hM hz).mpr hlt)
      (htie.2 (F.erase z) (by simp [Finset.card_erase_of_mem hz, hcard]))
  · exact hge

/-- **DOMINATING REMOVALS OF A TIE SIT EXACTLY AT READING ONE.** -/
theorem removal_reading_eq_one_of_isTie_of_dominates (D : WeightedDesign m 3)
    (htie : IsTie D) {F : Finset (Fin m)} (hcard : F.card = 4)
    (hM : (subsetSum D F - 1).PosDef) {z : Fin m} (hz : z ∈ F)
    (hdom : Dominates D (F.erase z)) :
    D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z) = 1 :=
  le_antisymm ((removal_dominates_iff_reading_le_one D hM hz).mp hdom)
    (one_le_removal_reading_of_isTie D htie hcard hM hz)

/-! ## 3. The trace ledger -/

/-- **THE WEIGHTED READINGS OF ANY MATRIX TOTAL ITS TRACE.**  Parseval, read
against an arbitrary quadratic form. -/
theorem weighted_reading_trace {k : ℕ} (D : WeightedDesign m k)
    (Q : Matrix (Fin k) (Fin k) ℝ) :
    ∑ c, D.weight c * (D.atom c ⬝ᵥ (Q *ᵥ D.atom c)) = Matrix.trace Q := by
  have hterm : ∀ c, D.weight c * (D.atom c ⬝ᵥ (Q *ᵥ D.atom c))
      = Matrix.trace ((D.weight c • atomMatrix (D.atom c)) * Q) := by
    intro c
    rw [Matrix.smul_mul, Matrix.trace_smul, atomMatrix_trace_pairing, smul_eq_mul]
  calc ∑ c, D.weight c * (D.atom c ⬝ᵥ (Q *ᵥ D.atom c))
      = ∑ c, Matrix.trace ((D.weight c • atomMatrix (D.atom c)) * Q) :=
        Finset.sum_congr rfl fun c _ => hterm c
    _ = Matrix.trace ((∑ c, D.weight c • atomMatrix (D.atom c)) * Q) := by
        rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace Q := by rw [D.isParseval, Matrix.one_mul]

/-- **THE FOUR READINGS TOTAL `3 + tr M⁻¹`.**  True for any subset whose gap is
positive definite; the cardinality never enters. -/
theorem fourSet_reading_sum (D : WeightedDesign m 3) {F : Finset (Fin m)}
    (hM : (subsetSum D F - 1).PosDef) :
    ∑ z ∈ F, D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z)
      = 3 + Matrix.trace (subsetSum D F - 1)⁻¹ := by
  have hunit : IsUnit (subsetSum D F - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  set Minv := (subsetSum D F - 1)⁻¹ with hMinv
  calc ∑ z ∈ F, D.atom z ⬝ᵥ (Minv *ᵥ D.atom z)
      = ∑ z ∈ F, Matrix.trace (atomMatrix (D.atom z) * Minv) :=
        Finset.sum_congr rfl fun z _ => (atomMatrix_trace_pairing Minv (D.atom z)).symm
    _ = Matrix.trace ((∑ z ∈ F, atomMatrix (D.atom z)) * Minv) := by
        rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace (subsetSum D F * Minv) := rfl
    _ = Matrix.trace (((subsetSum D F - 1) + 1) * Minv) := by rw [sub_add_cancel]
    _ = 3 + Matrix.trace Minv := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, hMinv,
          Matrix.mul_nonsing_inv _ hunit, Matrix.trace_one]
        norm_num

/-- **THE ANCHOR BUDGET IDENTITY.**  The free readings of the subset beat the
weighted outside readings by exactly three.  This is the free-mass budget of
the corank-one normal form, transported into the anchor metric, where the
anchor is positive definite and no corank hypothesis is needed. -/
theorem anchor_budget_identity (D : WeightedDesign m 3) {F : Finset (Fin m)}
    (hM : (subsetSum D F - 1).PosDef) :
    ∑ z ∈ F, (1 - D.weight z)
        * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z))
      - ∑ w ∈ Fᶜ, D.weight w
        * (D.atom w ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom w))
      = 3 := by
  have htrace := weighted_reading_trace D (subsetSum D F - 1)⁻¹
  have hfour := fourSet_reading_sum D hM
  have hsplit : ∑ c, D.weight c
      * (D.atom c ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom c))
    = ∑ z ∈ F, D.weight z
        * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z))
      + ∑ w ∈ Fᶜ, D.weight w
        * (D.atom w ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom w)) :=
    (Finset.sum_add_sum_compl F _).symm
  have hfree : ∑ z ∈ F, (1 - D.weight z)
      * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z))
    = ∑ z ∈ F, D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z)
      - ∑ z ∈ F, D.weight z
        * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [hfree, hfour]
  linarith [htrace, hsplit]

/-- **AT A TIE THE FREE READINGS OF A FOUR-SET ARE AT LEAST THREE.**  Every
outside reading is nonnegative because the anchor inverse is positive
definite. -/
theorem three_le_freeReading_of_isTie (D : WeightedDesign m 3)
    (htie : IsTie D) {F : Finset (Fin m)} (hcard : F.card = 4)
    (hM : (subsetSum D F - 1).PosDef) :
    3 ≤ ∑ z ∈ F, (1 - D.weight z)
      * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z)) := by
  have hinv : ((subsetSum D F - 1)⁻¹).PosDef := hM.inv
  have houtside : 0 ≤ ∑ w ∈ Fᶜ, D.weight w
      * (D.atom w ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom w)) := by
    refine Finset.sum_nonneg fun w _ => mul_nonneg (D.weight_pos w).le ?_
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hinv.posSemidef).2
      (D.atom w)
    rwa [star_trivial] at h
  linarith [anchor_budget_identity D hM]

/-! ## 4. The exact kernel of a one-atom downdate, and the propagated null line -/

/-- **THE KERNEL OF A DOWNDATE IS ONE EXPLICIT LINE.**  For a positive definite
`M` and reading one at `g`, the kernel of `M - g gᵀ` is the line of `M⁻¹ g`. -/
theorem anchor_downdate_kernel {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.PosDef)
    (g : Fin 3 → ℝ) (hread : g ⬝ᵥ (M⁻¹ *ᵥ g) = 1) (v : Fin 3 → ℝ) :
    (M - Matrix.vecMulVec g g) *ᵥ v = 0 ↔ ∃ s : ℝ, v = s • (M⁻¹ *ᵥ g) := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  constructor
  · intro hnull
    refine ⟨g ⬝ᵥ v, ?_⟩
    have hMv : M *ᵥ v = (g ⬝ᵥ v) • g := by
      have hsplit := hnull
      rw [Matrix.sub_mulVec, vecMulVec_mulVec_eq, sub_eq_zero] at hsplit
      exact hsplit
    calc v = M⁻¹ *ᵥ (M *ᵥ v) := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
            Matrix.one_mulVec]
      _ = (g ⬝ᵥ v) • (M⁻¹ *ᵥ g) := by rw [hMv, Matrix.mulVec_smul]
  · rintro ⟨s, rfl⟩
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, vecMulVec_mulVec_eq,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec,
      hread, one_smul, sub_self, smul_zero]

/-- **AN EQUALITY SWAP HANDS THE NEXT DOMINATOR A FULL NULL LINE.**  The
propagated null vector is not only null: it spans the kernel, so the swapped
dominator carries `Gtz.GapNullLine` and the corank-one machinery iterates. -/
theorem gapNullLine_swap_of_reading_eq_one (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) {e d : Fin m} (he : e ∈ C) (hd : d ∉ C)
    (hread : D.atom d ⬝ᵥ nullDir ≠ 0)
    (hone : D.atom e ⬝ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) = 1) :
    GapNullLine D (insert d (C.erase e))
      ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) := by
  have hM : (exchangeAnchor D C d).PosDef :=
    exchangeAnchor_posDef D C hdominates hline hread
  have hMdet : IsUnit (exchangeAnchor D C d).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  have hne : e ≠ d := fun h => hd (h ▸ he)
  have hd' : d ∉ C.erase e := fun hmem => hd (Finset.mem_of_mem_erase hmem)
  have hgap : subsetSum D (insert d (C.erase e)) - 1
      = exchangeAnchor D C d - Matrix.vecMulVec (D.atom e) (D.atom e) := by
    have he' : e ∈ insert d C := Finset.mem_insert_of_mem he
    have herase : (insert d C).erase e = insert d (C.erase e) := by
      rw [Finset.erase_insert_of_ne hne.symm]
    rw [← herase, erase_gap_eq D he', ← exchangeAnchor_eq_insert D C hd]
  have hatomNe : D.atom e ≠ 0 := by
    intro hzero
    rw [hzero] at hone
    simp at hone
  have hvecNe : (exchangeAnchor D C d)⁻¹ *ᵥ D.atom e ≠ 0 := by
    intro hzero
    have hback : D.atom e = 0 := by
      calc D.atom e
          = exchangeAnchor D C d *ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) := by
            rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hMdet,
              Matrix.one_mulVec]
        _ = 0 := by rw [hzero, Matrix.mulVec_zero]
    exact hatomNe hback
  refine ⟨hvecNe, ?_, ?_⟩
  · have hnull : (subsetSum D (insert d (C.erase e)) - 1)
        *ᵥ ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom e) = 0 := by
      rw [hgap]
      exact (anchor_downdate_kernel hM (D.atom e) hone _).mpr ⟨1, (one_smul _ _).symm⟩
    rw [hnull, dotProduct_zero]
  · intro probe hprobe
    have hpsd : (subsetSum D (insert d (C.erase e)) - 1).PosSemidef := by
      rw [hgap]
      exact (posSemidef_sub_vecMulVec_iff _ hM _).mpr (le_of_eq hone)
    have hnullProbe : (subsetSum D (insert d (C.erase e)) - 1) *ᵥ probe = 0 := by
      have hsymm : (subsetSum D (insert d (C.erase e)) - 1)ᵀ
          = subsetSum D (insert d (C.erase e)) - 1 := transpose_subsetSum_sub_one D _
      exact mulVec_eq_zero_of_form_eq_zero hpsd hsymm hprobe
    have hker := (anchor_downdate_kernel hM (D.atom e) hone probe).mp
      (by rw [← hgap]; exact hnullProbe)
    exact hker

/-! ## 5. Both null lines are anchor images of the two swapped atoms -/

/-- **THE NULL LINE OF THE DOMINATOR IS THE ANCHOR IMAGE OF THE OUTSIDE
ATOM.**  Together with the propagated null `M⁻¹ g_e` of the swapped dominator,
the two null lines of an adjacent pair are the `M⁻¹` images of the two swapped
atoms — the whole adjacency is geometry of one metric. -/
theorem nullDir_eq_smul_anchorInv (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) {d : Fin m}
    (hread : D.atom d ⬝ᵥ nullDir ≠ 0) :
    nullDir = (D.atom d ⬝ᵥ nullDir) • ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom d) := by
  have hM : (exchangeAnchor D C d).PosDef :=
    exchangeAnchor_posDef D C hdominates hline hread
  have hunit : IsUnit (exchangeAnchor D C d).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  have hgapNull : (subsetSum D C - 1) *ᵥ nullDir = 0 :=
    mulVec_eq_zero_of_form_eq_zero hdominates
      (transpose_subsetSum_sub_one D C) hline.2.1
  have hMv : exchangeAnchor D C d *ᵥ nullDir
      = (D.atom d ⬝ᵥ nullDir) • D.atom d := by
    rw [exchangeAnchor, Matrix.add_mulVec, hgapNull, zero_add]
    simp only [atomMatrix]
    rw [vecMulVec_mulVec_eq]
  calc nullDir
      = (exchangeAnchor D C d)⁻¹ *ᵥ (exchangeAnchor D C d *ᵥ nullDir) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
          Matrix.one_mulVec]
    _ = (D.atom d ⬝ᵥ nullDir) • ((exchangeAnchor D C d)⁻¹ *ᵥ D.atom d) := by
        rw [hMv, Matrix.mulVec_smul]

/-! ## 6. Parseval transported into the anchor metric -/

/-- **THE ANCHOR IMAGES OF THE ATOMS ARE A DESIGN FOR `Q⁻²`.**  Sandwiching
Parseval with any symmetric invertible form: the transported atoms `Q⁻¹ g_c`
with the original weights have frame operator `Q⁻¹ * Q⁻¹`.  The exchange
machinery iterates inside the transported system with no new hypothesis. -/
theorem transported_parseval {k : ℕ} (D : WeightedDesign m k)
    {Q : Matrix (Fin k) (Fin k) ℝ} (hsymm : Qᵀ = Q) (hunit : IsUnit Q.det) :
    ∑ c, D.weight c • atomMatrix (Q⁻¹ *ᵥ D.atom c) = Q⁻¹ * Q⁻¹ := by
  have hinvSymm : (Q⁻¹)ᵀ = Q⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsymm]
  have hterm : ∀ c, atomMatrix (Q⁻¹ *ᵥ D.atom c)
      = Q⁻¹ * atomMatrix (D.atom c) * Q⁻¹ := by
    intro c
    have h := transpose_mul_atomMatrix_mul (Q⁻¹) (D.atom c)
    rw [hinvSymm] at h
    exact h.symm
  calc ∑ c, D.weight c • atomMatrix (Q⁻¹ *ᵥ D.atom c)
      = ∑ c, D.weight c • (Q⁻¹ * atomMatrix (D.atom c) * Q⁻¹) :=
        Finset.sum_congr rfl fun c _ => by rw [hterm]
    _ = Q⁻¹ * (∑ c, D.weight c • atomMatrix (D.atom c)) * Q⁻¹ := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = Q⁻¹ * Q⁻¹ := by rw [D.isParseval, Matrix.mul_one]

/-! ## 7. The outside floor at a tie -/

/-- **THE OUTSIDE ATOMS OF A FOUR-SET READ AT LEAST THEIR WEIGHT.**  At a tie
the four inside readings are at least one, so the budget identity pushes the
weighted outside readings up to the outside weight total.  At `(6,3)` the
outside is a pair, and at `(5,3)` a single atom — the floor holds at every
size. -/
theorem outside_weighted_floor_of_isTie (D : WeightedDesign m 3)
    (htie : IsTie D) {F : Finset (Fin m)} (hcard : F.card = 4)
    (hM : (subsetSum D F - 1).PosDef) :
    ∑ w ∈ Fᶜ, D.weight w
      ≤ ∑ w ∈ Fᶜ, D.weight w
          * (D.atom w ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom w)) := by
  have hm : 2 ≤ m := by
    have hle := Finset.card_le_univ F
    rw [hcard, Fintype.card_fin] at hle
    omega
  have hstep : ∀ z ∈ F, (1 : ℝ) - D.weight z
      ≤ (1 - D.weight z)
        * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z)) := by
    intro z hz
    have hw := weight_lt_one D hm z
    have hfloor := one_le_removal_reading_of_isTie D htie hcard hM hz
    nlinarith
  have hfreeLower : (4 : ℝ) - ∑ z ∈ F, D.weight z
      ≤ ∑ z ∈ F, (1 - D.weight z)
        * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z)) := by
    calc (4 : ℝ) - ∑ z ∈ F, D.weight z
        = ∑ z ∈ F, ((1 : ℝ) - D.weight z) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, hcard]
          norm_num
      _ ≤ _ := Finset.sum_le_sum hstep
  have hbudget := anchor_budget_identity D hM
  have hsplitW : ∑ z ∈ F, D.weight z + ∑ w ∈ Fᶜ, D.weight w = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact D.weight_sum_one
  linarith

/-! ## 8. The six-basis rigidity: at most one all-ones subset -/

/-- **AT MOST ONE SUBSET PUTS ALL SIX ATOMS AT READING ONE.**  Two distinct
subsets with positive definite gaps and all readings one would force their
inverse gaps apart by a symmetric form vanishing at all six atoms.  Off a
common conic that form is zero, and stress-freeness then reads the subsets off
the atom matrices.  This consumes both halves of the `6 = dim Sym³` rigidity.
It is inapplicable at the diamond, which lies ON a conic
(`Gtz.diamondDesign_on_conic`) — the exact legality shape. -/
theorem allOnes_subset_unique (D : WeightedDesign 6 3)
    (hquad : HasNoCommonQuadric D.atom) (hfree : IsStressFreeDesign D)
    {F F' : Finset (Fin 6)}
    (hM : (subsetSum D F - 1).PosDef) (hM' : (subsetSum D F' - 1).PosDef)
    (hone : ∀ c, D.atom c ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom c) = 1)
    (hone' : ∀ c, D.atom c ⬝ᵥ ((subsetSum D F' - 1)⁻¹ *ᵥ D.atom c) = 1) :
    F = F' := by
  have hsymmF : ((subsetSum D F - 1)⁻¹)ᵀ = (subsetSum D F - 1)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, transpose_subsetSum_sub_one]
  have hsymmF' : ((subsetSum D F' - 1)⁻¹)ᵀ = (subsetSum D F' - 1)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, transpose_subsetSum_sub_one]
  have hdiff : (subsetSum D F - 1)⁻¹ - (subsetSum D F' - 1)⁻¹ = 0 := by
    refine hquad _ ?_ ?_
    · rw [Matrix.transpose_sub, hsymmF, hsymmF']
    · intro c
      rw [Matrix.sub_mulVec, dotProduct_sub, hone c, hone' c, sub_self]
  have hunitF : IsUnit (subsetSum D F - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  have hunitF' : IsUnit (subsetSum D F' - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hM'.det_pos)
  have hgapEq : subsetSum D F - 1 = subsetSum D F' - 1 := by
    calc subsetSum D F - 1
        = ((subsetSum D F - 1)⁻¹)⁻¹ :=
          (Matrix.nonsing_inv_nonsing_inv _ hunitF).symm
      _ = ((subsetSum D F' - 1)⁻¹)⁻¹ := by rw [sub_eq_zero.mp hdiff]
      _ = subsetSum D F' - 1 := Matrix.nonsing_inv_nonsing_inv _ hunitF'
  have hsumEq : subsetSum D F = subsetSum D F' := sub_left_inj.mp hgapEq
  have hindicator : ∀ G : Finset (Fin 6),
      ∑ c, (if c ∈ G then (1 : ℝ) else 0) • atomMatrix (D.atom c)
        = subsetSum D G := by
    intro G
    rw [subsetSum]
    simp [ite_smul, one_smul, zero_smul, Finset.sum_ite_mem, Finset.univ_inter]
  have hstress : ∑ c, ((if c ∈ F then (1 : ℝ) else 0)
      - if c ∈ F' then (1 : ℝ) else 0) • atomMatrix (D.atom c) = 0 := by
    have hsub : ∑ c, ((if c ∈ F then (1 : ℝ) else 0)
        - if c ∈ F' then (1 : ℝ) else 0) • atomMatrix (D.atom c)
        = subsetSum D F - subsetSum D F' := by
      rw [← hindicator F, ← hindicator F', ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by rw [sub_smul]
    rw [hsub, hsumEq, sub_self]
  have hzero := hfree _ hstress
  ext c
  have hc := congrFun hzero c
  by_cases hcF : c ∈ F <;> by_cases hcF' : c ∈ F' <;>
    simp [hcF, hcF', Pi.zero_apply] at hc ⊢

/-! ## 9. The defect vector against the null direction -/

/-- **THE COVERING DEFECTS ARE ORTHOGONAL TO THE DUAL READINGS OF A NULL
DIRECTION.**  The gap of any subset expands in the dual conics with the
covering defects as coefficients; reading that expansion at a direction where
the gap form vanishes gives an exact orthogonality.  At a weak dominator the
defects are all nonnegative (`Gtz.coveringDefect_nonneg_of_dominates`), so the
dual readings of the null direction cannot be one-signed unless every defect
with a nonzero reading vanishes. -/
theorem coveringDefect_dual_null_orthogonality (D : WeightedDesign 6 3)
    (hfree : IsStressFreeDesign D) {C : Finset (Fin 6)}
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) :
    ∑ label, coveringDefect D C label
      * (nullDir ⬝ᵥ (dualAtom D label *ᵥ nullDir)) = 0 := by
  have hexp := subsetSum_sub_one_eq_sum_coveringDefect_smul_dualAtom D hfree C
  calc ∑ label, coveringDefect D C label
        * (nullDir ⬝ᵥ (dualAtom D label *ᵥ nullDir))
      = nullDir ⬝ᵥ ((∑ label, coveringDefect D C label • dualAtom D label)
          *ᵥ nullDir) := by
        simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
          dotProduct_smul, smul_eq_mul]
    _ = nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) := by rw [← hexp]
    _ = 0 := hnull

end Gtz
