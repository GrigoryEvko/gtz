/-
# The cross ledger of a four-set, and its three degeneration markers

At a `(6,3)` design the complement of a weak dominator is itself a triple.  Add
one inside atom `c` to that complement and the four-set `{c} ∪ E` has three
one-atom removals, each a triple of the tie's refusal budget.  This module
prices those three determinants against the four-set, the complement and ONE
cross-product family, and then characterizes exactly when the price
degenerates.

## The ledger

With `M = S_E − 1` the complement gap and `A_F = M + g_c g_cᵀ` the four-set gap,

  `Σ_{d ∈ E} det(S_{{c} ∪ E∖d} − 1)
     = 3·det A_F − 3·det M − tr(adj M) − Σ_{d ∈ E} (g_c × q_d)ᵀ M (g_c × q_d)` .

`Gtz.cross_ledger` is that identity, at every rank-three design, every triple
`E` and every atom `c ∉ E`.  Three landed pieces carry it: the rank-two
determinant exchange law `Gtz.det_add_atomMatrix_sub_atomMatrix_cross`, the
rank-one determinant expansion through the adjugate
(`Gtz.det_add_atomMatrix_adjugate`, here), and the reading-to-trace collapse
`Gtz.sum_readings_eq_trace`.  The complement's own Parseval enters exactly once,
through `S_E = M + 1`, which is what turns the three adjugate readings into
`3·det M + tr(adj M)`.

## The degeneration markers

The only term of the ledger that is not a determinant of the configuration is
the cross reading `(g_c × q_d)ᵀ M (g_c × q_d)`, and it is where the ledger goes
tight.  Three statements pin it:

* `Gtz.cross_reading_eq_zero_of_parallel` — a parallel pair kills the reading
  outright, at every base matrix;
* `Gtz.cross_reading_eq_zero_iff_mulVec_eq_zero` — at a positive SEMIdefinite
  base the reading vanishes exactly when the cross product lies in `ker M`, so
  at a corank-one complement gap the vanishing locus is exactly
  "the cross product is parallel to the null direction";
* `Gtz.cross_reading_eq_zero_iff_parallel_of_posDef` — at a positive DEFINITE
  base the reading vanishes exactly when the two atoms are parallel.

## Calibration [MEASURED, `scratchpad/corank1/fix.jl`, exact rationals]

At the `(6,3)` split diamond with `E` the complement of the spine dominator, the
ledger holds at all three inside atoms: `Σ det = −7.5` at the spine and `−10` at
each of the other two, matching `3 det A_F − 3 det M − tr adj M − Σ cross`
exactly.  There `M` is positive semidefinite of corank one (`det M = 0`,
`tr adj M = 6`), and the cross reading vanishes at exactly one pair — the spine
against its own copy.  That same triple carries `det(S_T − 1) = 0` and zero swap
`w`-form (`Gtz.sixSplit_copySwap_wform_zero`).  THREE INDEPENDENT DEGENERATION
MARKERS COINCIDE ON THE PARALLEL PAIR, and the two theorems above say the
coincidence is not an accident of the fixture: the cross marker IS parallelism
whenever the complement gap is definite, and is parallelism-modulo-the-null-line
whenever it is corank one.
-/
import Gtz.Wave.CorankOneGramMirror
import Gtz.Wave.HeavyInsideCapGap
import Gtz.Wave.ErasedDeflationFloor
import Gtz.Design.SphereExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The rank-one determinant expansion -/

/-- **The rank-one determinant expansion.**  Adding an atom to a `3×3` base
raises the determinant by the atom's reading in the adjugate metric.  A
polynomial identity — no invertibility. -/
theorem det_add_atomMatrix_adjugate (M : Matrix (Fin 3) (Fin 3) ℝ)
    (q : Fin 3 → ℝ) :
    (M + atomMatrix q).det = M.det + q ⬝ᵥ (M.adjugate *ᵥ q) := by
  simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.add_apply,
    atomMatrix, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **The three complement readings collapse.**  Over a card-three set the
rank-one expansions total the complement determinant three times plus the
adjugate trace against the set's own atom sum. -/
theorem sum_det_add_atomMatrix_eq (D : WeightedDesign m 3) (E : Finset (Fin m))
    (hE : E.card = 3) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ d ∈ E, (M + atomMatrix (D.atom d)).det
      = 3 * M.det + (M.adjugate * subsetSum D E).trace := by
  have hstep : ∀ d ∈ E, (M + atomMatrix (D.atom d)).det
      = M.det + D.atom d ⬝ᵥ (M.adjugate *ᵥ D.atom d) :=
    fun d _ => det_add_atomMatrix_adjugate M (D.atom d)
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_const, hE,
    sum_readings_eq_trace D E M.adjugate]
  norm_num

/-- **The complement's own Parseval, read through the adjugate.**  With `M` the
gap of `E` itself, the collapse above becomes six copies of the determinant plus
the adjugate trace. -/
theorem sum_det_add_atomMatrix_gap (D : WeightedDesign m 3) (E : Finset (Fin m))
    (hE : E.card = 3) :
    ∑ d ∈ E, ((subsetSum D E - 1) + atomMatrix (D.atom d)).det
      = 6 * (subsetSum D E - 1).det + (subsetSum D E - 1).adjugate.trace := by
  set M : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D E - 1 with hM
  have hsum : subsetSum D E = M + 1 := by rw [hM]; abel
  rw [sum_det_add_atomMatrix_eq D E hE M, hsum, Matrix.mul_add, Matrix.mul_one,
    Matrix.trace_add, Matrix.adjugate_mul, Matrix.trace_smul, Matrix.trace_one]
  simp only [smul_eq_mul, Fintype.card_fin]
  push_cast
  ring

/-! ## 2. The ledger -/

/-- The removal of an outside atom from the four-set, as a two-update of the
complement gap. -/
theorem fourSet_removal_gap (D : WeightedDesign m 3) (E : Finset (Fin m))
    {c d : Fin m} (hc : c ∉ E) (hd : d ∈ E) :
    subsetSum D (insert c (E.erase d)) - 1
      = (subsetSum D E - 1) + atomMatrix (D.atom c) - atomMatrix (D.atom d) := by
  have hcErase : c ∉ E.erase d := fun hmem => hc (Finset.mem_of_mem_erase hmem)
  rw [subsetSum, Finset.sum_insert hcErase, Finset.sum_erase_eq_sub hd]
  show atomMatrix (D.atom c) + (subsetSum D E - atomMatrix (D.atom d)) - 1
      = subsetSum D E - 1 + atomMatrix (D.atom c) - atomMatrix (D.atom d)
  abel

/-- The four-set gap, as a one-update of the complement gap. -/
theorem fourSet_gap (D : WeightedDesign m 3) (E : Finset (Fin m))
    {c : Fin m} (hc : c ∉ E) :
    subsetSum D (insert c E) - 1
      = (subsetSum D E - 1) + atomMatrix (D.atom c) := by
  rw [subsetSum, Finset.sum_insert hc]
  show atomMatrix (D.atom c) + subsetSum D E - 1
      = subsetSum D E - 1 + atomMatrix (D.atom c)
  abel

/-- **THE CROSS LEDGER.**  The three one-atom removals of a four-set built from
a triple `E` and an outside atom `c` total the four-set and complement
determinants against ONE cross-product family.  Unconditional at every
rank-three design. -/
theorem cross_ledger (D : WeightedDesign m 3) (E : Finset (Fin m))
    (hE : E.card = 3) {c : Fin m} (hc : c ∉ E) :
    ∑ d ∈ E, (subsetSum D (insert c (E.erase d)) - 1).det
      = 3 * (subsetSum D (insert c E) - 1).det
        - 3 * (subsetSum D E - 1).det
        - (subsetSum D E - 1).adjugate.trace
        - ∑ d ∈ E, crossProduct (D.atom c) (D.atom d)
            ⬝ᵥ ((subsetSum D E - 1) *ᵥ crossProduct (D.atom c) (D.atom d)) := by
  classical
  set M : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D E - 1 with hM
  have hstep : ∀ d ∈ E, (subsetSum D (insert c (E.erase d)) - 1).det
      = (M + atomMatrix (D.atom c)).det + M.det
        - crossProduct (D.atom c) (D.atom d)
            ⬝ᵥ (M *ᵥ crossProduct (D.atom c) (D.atom d))
        - (M + atomMatrix (D.atom d)).det := by
    intro d hd
    have hgap := fourSet_removal_gap D E hc hd
    rw [← hM] at hgap
    have hexchange := det_add_atomMatrix_sub_atomMatrix_cross M (D.atom c) (D.atom d)
    rw [hgap]
    linarith [hexchange]
  rw [Finset.sum_congr rfl hstep]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.sum_const, hE]
  rw [sum_det_add_atomMatrix_gap D E hE, ← hM, fourSet_gap D E hc, ← hM]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-! ## 3. The degeneration markers -/

/-- **A parallel pair kills the cross reading**, at every base matrix.  This is
the marker's easy half, and it is what fires at the split diamond's doubled
spine. -/
theorem cross_reading_eq_zero_of_parallel (M : Matrix (Fin 3) (Fin 3) ℝ)
    (p q : Fin 3 → ℝ) {ratio : ℝ} (hpar : q = ratio • p) :
    crossProduct p q ⬝ᵥ (M *ᵥ crossProduct p q) = 0 := by
  have hcross : crossProduct p q = 0 := by
    rw [hpar, map_smul, cross_self, smul_zero]
  rw [hcross, Matrix.mulVec_zero, dotProduct_zero]

/-- **At a positive semidefinite base the cross reading vanishes exactly on the
kernel.**  So at a corank-one complement gap the ledger degenerates at `(c, d)`
precisely when `g_c × q_d` is parallel to the null direction. -/
theorem cross_reading_eq_zero_iff_mulVec_eq_zero {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hpsd : M.PosSemidef) (hsymm : Mᵀ = M) (p q : Fin 3 → ℝ) :
    crossProduct p q ⬝ᵥ (M *ᵥ crossProduct p q) = 0
      ↔ M *ᵥ crossProduct p q = 0 := by
  constructor
  · intro hform
    exact mulVec_eq_zero_of_form_eq_zero hpsd hsymm hform
  · intro hker
    rw [hker, dotProduct_zero]

/-- **At a positive definite base the cross reading IS parallelism.**  The
ledger degenerates at `(c, d)` exactly when the two atoms are parallel — the
rigidity marker in its sharpest local form. -/
theorem cross_reading_eq_zero_iff_parallel_of_posDef
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hpd : M.PosDef) {p q : Fin 3 → ℝ}
    (hp : p ≠ 0) :
    crossProduct p q ⬝ᵥ (M *ᵥ crossProduct p q) = 0
      ↔ ∃ ratio : ℝ, q = ratio • p := by
  constructor
  · intro hform
    refine eq_smul_of_crossProduct_eq_zero hp ?_
    by_contra hne
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hne
    rw [star_trivial] at hpos
    exact absurd hform (ne_of_gt hpos)
  · rintro ⟨ratio, hratio⟩
    exact cross_reading_eq_zero_of_parallel M p q hratio

/-- **The ledger at a tie.**  Every removal determinant of a STRICTLY dominating
four-set is nonpositive at a tie, so the ledger's left side is nonpositive and
the four-set is priced from above by the complement data and the cross family:

  `3·det A_F ≤ 3·det M + tr(adj M) + Σ_d (g_c × q_d)ᵀ M (g_c × q_d)` .

The cross family therefore CARRIES the four-set determinant, and every pair it
degenerates on removes its own share of the carrying capacity. -/
theorem cross_ledger_le_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    (E : Finset (Fin m)) (hE : E.card = 3) {c : Fin m} (hc : c ∉ E)
    (hPD : (subsetSum D (insert c E) - 1).PosDef) :
    3 * (subsetSum D (insert c E) - 1).det
      ≤ 3 * (subsetSum D E - 1).det + (subsetSum D E - 1).adjugate.trace
        + ∑ d ∈ E, crossProduct (D.atom c) (D.atom d)
            ⬝ᵥ ((subsetSum D E - 1) *ᵥ crossProduct (D.atom c) (D.atom d)) := by
  classical
  have hcard : (insert c E).card = 4 := by
    rw [Finset.card_insert_of_notMem hc, hE]
  have hnonpos : ∀ d ∈ E, (subsetSum D (insert c (E.erase d)) - 1).det ≤ 0 := by
    intro d hd
    have hmem : d ∈ insert c E := Finset.mem_insert_of_mem hd
    have hdc : d ≠ c := fun h => hc (by rw [← h]; exact hd)
    have herase : (insert c E).erase d = insert c (E.erase d) := by
      rw [Finset.erase_insert_of_ne hdc.symm]
    have := tie_fourSet_member_det_nonpos D htie (insert c E) hcard hPD hmem
    rwa [herase] at this
  have hsum : ∑ d ∈ E, (subsetSum D (insert c (E.erase d)) - 1).det ≤ 0 :=
    Finset.sum_nonpos hnonpos
  rw [cross_ledger D E hE hc] at hsum
  linarith

/-! ## 4. The markers coincide on a parallel pair -/

/-- **A unit-ratio parallel pair flattens the swap `w`-form.**  If the added
atom is `±` the dropped one, the exchange leaves the null form at zero: the
swap lands on another weak dominator.  Together with
`Gtz.cross_reading_eq_zero_of_parallel` this is the coincidence measured at the
split diamond's doubled spine — two independent degeneration markers firing on
the same pair, for two independent reasons. -/
theorem swapGapForm_eq_zero_of_unit_parallel (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0)
    {e d : Fin m} (he : e ∈ C) (hd : d ∉ C) {ratio : ℝ}
    (hpar : D.atom d = ratio • D.atom e) (hunitRatio : ratio ^ 2 = 1) :
    nullDir ⬝ᵥ ((subsetSum D (insert d (C.erase e)) - 1) *ᵥ nullDir) = 0 := by
  rw [swapGapForm_at_nullDir D C hnull he hd, hpar, smul_dotProduct, smul_eq_mul,
    mul_pow, hunitRatio, one_mul, sub_self]

/-- **THE PARALLEL PAIR COSTS THE LEDGER ITS SHARE.**  At a tie whose four-set
dominates strictly, a pair `(c, d₀)` of parallel atoms contributes nothing to
the cross family, so the SURVIVING crosses alone must carry the whole four-set
determinant.  Each degeneration of the family tightens the ledger on the rest —
this is the quantitative form of the rigidity backbone. -/
theorem cross_ledger_le_of_isTie_of_parallel (D : WeightedDesign m 3)
    (htie : IsTie D) (E : Finset (Fin m)) (hE : E.card = 3) {c : Fin m}
    (hc : c ∉ E) (hPD : (subsetSum D (insert c E) - 1).PosDef)
    {d₀ : Fin m} (hd₀ : d₀ ∈ E) {ratio : ℝ}
    (hpar : D.atom d₀ = ratio • D.atom c) :
    3 * (subsetSum D (insert c E) - 1).det
      ≤ 3 * (subsetSum D E - 1).det + (subsetSum D E - 1).adjugate.trace
        + ∑ d ∈ E.erase d₀, crossProduct (D.atom c) (D.atom d)
            ⬝ᵥ ((subsetSum D E - 1) *ᵥ crossProduct (D.atom c) (D.atom d)) := by
  classical
  have hfull := cross_ledger_le_of_isTie D htie E hE hc hPD
  have hzero : crossProduct (D.atom c) (D.atom d₀)
      ⬝ᵥ ((subsetSum D E - 1) *ᵥ crossProduct (D.atom c) (D.atom d₀)) = 0 :=
    cross_reading_eq_zero_of_parallel _ _ _ hpar
  have hsplit : ∑ d ∈ E, crossProduct (D.atom c) (D.atom d)
        ⬝ᵥ ((subsetSum D E - 1) *ᵥ crossProduct (D.atom c) (D.atom d))
      = ∑ d ∈ E.erase d₀, crossProduct (D.atom c) (D.atom d)
        ⬝ᵥ ((subsetSum D E - 1) *ᵥ crossProduct (D.atom c) (D.atom d)) := by
    rw [← Finset.sum_erase_add E _ hd₀, hzero, add_zero]
  rw [hsplit] at hfull
  exact hfull

/-! ## 5. The all-nonzero stratum

The `(5,3)` diamond and the `(6,3)` split diamond both live here
(`Gtz.diamondNull_spine_readings_ne_zero`,
`Gtz.sixSplit_spine_readings_ne_zero`), so the stratum is INHABITED and its
target is rigidity — `tie ⟹ parallel pair` — never emptiness.  What the
leverage ladder gives unconditionally is that the stratum is strictly heavy on
the inside. -/

/-- **THE ALL-NONZERO STRATUM IS STRICTLY HEAVY.**  When no inside null reading
vanishes, every atom of the corank-one weak dominator has leverage STRICTLY
above one.  The floor `Gtz.one_le_leverage_of_mem_dominating_triple` is never
attained here, and by `Gtz.eq_nullDir_of_leverage_eq_one` attainment is exactly
the two-zero stratum — so the two strata are separated by the leverage alone,
with no tie hypothesis and no size restriction. -/
theorem k0_leverage_gt_one_of_readings_ne_zero (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) nullDir)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hx : D.atom x ⬝ᵥ nullDir ≠ 0) (hy : D.atom y ⬝ᵥ nullDir ≠ 0)
    (hz : D.atom z ⬝ᵥ nullDir ≠ 0) :
    1 < leverageOf (D.atom x) ∧ 1 < leverageOf (D.atom y)
      ∧ 1 < leverageOf (D.atom z) := by
  classical
  have hyxz : ({y, x, z} : Finset (Fin m)) = ({x, y, z} : Finset (Fin m)) :=
    Finset.insert_comm y x {z}
  have hzxy : ({z, x, y} : Finset (Fin m)) = ({x, y, z} : Finset (Fin m)) := by
    rw [Finset.insert_comm z x {y}, Finset.pair_comm z y]
  refine ⟨?_, ?_, ?_⟩
  · exact one_lt_leverage_of_nullReading_ne_zero D hxy hxz hyz hdominates hline
      hunit (fun hcon => hy hcon.1)
  · refine one_lt_leverage_of_nullReading_ne_zero D hxy.symm hyz hxz
      (by rw [hyxz]; exact hdominates) (by rw [hyxz]; exact hline) hunit
      (fun hcon => hx hcon.1)
  · refine one_lt_leverage_of_nullReading_ne_zero D hxz.symm hyz.symm hxy
      (by rw [hzxy]; exact hdominates) (by rw [hzxy]; exact hline) hunit
      (fun hcon => hx hcon.1)

/-! ## 6. The two-zero stratum in the anchor metric

In the two-zero stratum the triple `{y, z, d}` IS a one-atom exchange of the
dominator: it drops `x` and adds `d`.  The landed exchange law therefore prices
it with no new machinery, and because `x` carries the null direction itself the
price is a statement about `w`. -/

/-- **THE `K2` ANCHOR LAW.**  At a two-zero corank-one tie the NULL DIRECTION
reads at least one in the metric of every exchange anchor that sees it:

  `1 ≤ wᵀ (S_C − 1 + q_d q_dᵀ)⁻¹ w` .

The dropped atom of the exchange is `x`, which is `±w`
(`Gtz.eq_nullDir_of_leverage_eq_one`), so the exchange law of
`Gtz.Wave.CorankOneExchange` becomes a law about the null line.  Against the
landed `Gtz.anchor_selfReading_eq_one` — the added atom reads EXACTLY one — the
stratum is pinned between two unit readings in one positive definite metric. -/
theorem k2_one_le_nullDir_anchor_reading_of_isTie (D : WeightedDesign m 3)
    (htie : IsTie D) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) nullDir)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0)
    {d : Fin m} (hd : d ∉ ({x, y, z} : Finset (Fin m)))
    (hread : D.atom d ⬝ᵥ nullDir ≠ 0) :
    1 ≤ nullDir ⬝ᵥ
      ((exchangeAnchor D ({x, y, z} : Finset (Fin m)) d)⁻¹ *ᵥ nullDir) := by
  classical
  obtain ⟨-, hxw⟩ :=
    leverage_eq_one_of_nullReadings_zero D hxy hxz hyz hdominates hline.2.1 hunit hy hz
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hmem : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hexch := one_le_exchange_reading_of_isTie D htie
    ({x, y, z} : Finset (Fin m)) hcard hdominates hline hmem hd hread
  rcases hxw with hxw | hxw
  · rwa [hxw] at hexch
  · rw [hxw] at hexch
    simpa only [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
      using hexch

end Gtz
