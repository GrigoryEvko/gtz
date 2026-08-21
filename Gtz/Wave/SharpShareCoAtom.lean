/-
# The sharp share is the co-atom reading

The sharp design of `Gtz/Wave/NaimarkSharpDesign.lean` is built through a
whitener and exported as an existential, so none of its NUMBERS are available.
This module computes the one number that matters.

**THE CRITERION.**  For every design with two or more atoms and every Naimark
dual `N`,

    **`1 - shat_c = (1 - t_c) * rho_c`**   (`Gtz.one_sub_naimarkSharpShare`)

where `shat_c` is the sharp share at `c` and `rho_c = g_c . (S_all - 1)^{-1} g_c`
is the co-atom reading of `Gtz/Wave/SharpFiveSetCriterion.lean`.  Two corollaries
are immediate and they are what the campaign wanted:

* the sharp design has a UNIT atom at `c` exactly when the co-atom set omitting
  `c` is singular (`Gtz.naimarkSharpLeverage_eq_one_iff`), and
* the sharp design is ALL-HEAVY exactly when every co-atom set of the design
  dominates strictly (`Gtz.forall_one_lt_naimarkSharpLeverage_iff`).

At `(6,3)` that reads: the sharp dual of a design is all-heavy iff every five-set
of the design dominates strictly.

## The proof: two orthogonal hats

Nothing here is an eigenvalue argument.  Put

    `A_c = sqrt(1 - t_c) * g_c`     (`Gtz.totalGapFrame`,  `m x k`)
    `B_c = (t_c / sqrt(1 - t_c)) * cotilde_c`   (`Gtz.sharpFrame`,  `m x r`)

Three products are computed outright:

* `A^T A = S_all - 1`, because Parseval turns `Sum_c g_c g_c^T - 1` into
  `Sum_c (1 - t_c) g_c g_c^T` (`Gtz.transpose_mul_totalGapFrame`).
* `B^T B` is the sharp target `Omega - 1`, because the dual Parseval law turns it
  into `Sum_c (t_c^2/(1 - t_c)) cotilde_c cotilde_c^T`
  (`Gtz.transpose_mul_sharpFrame`).
* `A^T B = 0`, because the two square roots cancel and what is left is exactly the
  dependency law of the Naimark dual, `Sum_c t_c g_c cotilde_c^T = 0`
  (`Gtz.transpose_totalGapFrame_mul_sharpFrame`).

So the two hat matrices `Pi_1 = A (A^T A)^{-1} A^T` and `Pi_2 = B (B^T B)^{-1} B^T`
are symmetric idempotents with `Pi_1 Pi_2 = 0` and traces `k` and `r`.  Their sum
is a symmetric idempotent of trace `k + r = m`, and

    **a symmetric idempotent of full trace is the identity**
    (`Gtz.eq_one_of_symmIdem_of_trace_eq`),

because `1 - Pi` is then a symmetric idempotent whose diagonal entries are the
squared row norms and whose trace is zero, so every row vanishes.  No spectral
theorem, no rank theory, no block reindexing.  Reading the identity
`Pi_1 + Pi_2 = 1` on the diagonal is the criterion.

## The two caps of a pair

The chart of a design is a determinantal point process, and the two pair
determinants are the two caps:

    `det P[{p,q}]     = s_p s_q - P_pq^2`      (`Gtz.chartPairDet_eq`)
    `det (1 - P)[{p,q}] = u_p u_q - P_pq^2`    (`Gtz.chartCoPairDet_eq`)

both nonnegative because `P` and `1 - P` are positive semidefinite.  A PARALLEL
PAIR saturates the first and a COPLANAR FOUR-SET saturates the second, so the two
halves of the `(6,3)` hinge dictionary are one pair saturating one of its two
caps, with no dual design in the statement at all.

## Measured, and NOT proved

`Phat = 1 - Pi_1` — the chart of the sharp design is the complementary hat.  It
follows from `Pi_1 + Pi_2 = 1` above once the sharp ATOMS are identified with the
rows of `B` up to the whitener, which needs `W W^T = (Omega - 1)^{-1}` from
`W^T (Omega - 1) W = 1`.  Verified at `2.4e-14`; the share identity that this
module proves is the part that carries the campaign's corollaries.

The twenty-triple linear system was RUN (`scratchpad/NOTES-fiveset.txt`): the
relaxation is feasible with min-slack `0.2`, so the hinge obstruction is not
linear in the triple volumes, and the structural reason is that those volumes are
a function of the projection alone while a tie compares the projection to the
weights.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Wave.NaimarkDualDesign
import Gtz.Wave.NaimarkSharpDesign
import Gtz.Wave.SharpFiveSetCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k r : ℕ}

/-! ## Part A — a symmetric idempotent of full trace is the identity -/

/-- The diagonal of a symmetric idempotent is the squared row norm. -/
theorem diag_eq_sum_sq_of_symmIdem {size : ℕ} {proj : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : projᵀ = proj) (hidem : proj * proj = proj) (index : Fin size) :
    proj index index = ∑ other, proj index other ^ 2 := by
  have hentry := congrFun (congrFun hidem index) index
  rw [Matrix.mul_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl fun other _ => ?_
  have hflip : proj other index = proj index other := by
    have h := congrFun (congrFun hsymm index) other
    rwa [Matrix.transpose_apply] at h
  rw [hflip]
  ring

/-- **A SYMMETRIC IDEMPOTENT OF FULL TRACE IS THE IDENTITY.**  Its complement is a
symmetric idempotent whose diagonal entries are squared row norms and whose trace
is zero, so every row vanishes.  No spectral theorem. -/
theorem eq_one_of_symmIdem_of_trace_eq {size : ℕ} {proj : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : projᵀ = proj) (hidem : proj * proj = proj)
    (htrace : Matrix.trace proj = (size : ℝ)) :
    proj = 1 := by
  set gap : Matrix (Fin size) (Fin size) ℝ := 1 - proj with hgap
  have hgapSymm : gapᵀ = gap := by
    rw [hgap, Matrix.transpose_sub, Matrix.transpose_one, hsymm]
  have hgapIdem : gap * gap = gap := by
    rw [hgap, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, hidem]
    abel
  have hgapTrace : ∑ index, gap index index = 0 := by
    have hstep : Matrix.trace gap = 0 := by
      rw [hgap, Matrix.trace_sub, Matrix.trace_one, htrace]
      simp
    simpa [Matrix.trace, Matrix.diag_apply] using hstep
  have hdiag : ∀ index : Fin size, gap index index = ∑ other, gap index other ^ 2 :=
    fun index => diag_eq_sum_sq_of_symmIdem hgapSymm hgapIdem index
  have hnonneg : ∀ index : Fin size, 0 ≤ gap index index := by
    intro index
    rw [hdiag index]
    exact Finset.sum_nonneg fun other _ => sq_nonneg _
  have hzero : ∀ index : Fin size, gap index index = 0 := by
    intro index
    by_contra hne
    have hpos : 0 < gap index index := lt_of_le_of_ne (hnonneg index) (Ne.symm hne)
    have hsum : 0 < ∑ other, gap other other :=
      Finset.sum_pos' (fun other _ => hnonneg other) ⟨index, Finset.mem_univ index, hpos⟩
    rw [hgapTrace] at hsum
    exact lt_irrefl 0 hsum
  have hrow : ∀ index other : Fin size, gap index other = 0 := by
    intro index other
    have hsq : ∑ probe, gap index probe ^ 2 = 0 := by rw [← hdiag index, hzero index]
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun probe (_ : probe ∈ Finset.univ) => sq_nonneg (gap index probe))).mp hsq other
      (Finset.mem_univ other)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hgapZero : (1 : Matrix (Fin size) (Fin size) ℝ) - proj = 0 := by
    rw [← hgap]
    ext index other
    exact hrow index other
  rw [sub_eq_zero] at hgapZero
  exact hgapZero.symm

/-! ## Part B — the two frames of a design and its Naimark dual -/

variable {D : WeightedDesign m k}

/-- The co-weight square root, `sqrt(1 - t_c)`. -/
noncomputable def coRoot (D : WeightedDesign m k) (label : Fin m) : ℝ :=
  Real.sqrt (1 - D.weight label)

theorem coRoot_pos (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    0 < coRoot D label :=
  Real.sqrt_pos.mpr (by linarith [weight_lt_one D hm label])

theorem coRoot_mul_self (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    coRoot D label * coRoot D label = 1 - D.weight label :=
  Real.mul_self_sqrt (by linarith [weight_lt_one D hm label])

theorem coRoot_sq (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    coRoot D label ^ 2 = 1 - D.weight label := by
  rw [sq]; exact coRoot_mul_self D hm label

/-- **THE TOTAL-GAP FRAME**: the design's atoms scaled by the co-weight roots. -/
noncomputable def totalGapFrame (D : WeightedDesign m k) : Matrix (Fin m) (Fin k) ℝ :=
  Matrix.of fun label coord => coRoot D label * D.atom label coord

/-- **THE SHARP FRAME**: the dual atoms scaled so that their Gram is the sharp
target. -/
noncomputable def sharpFrame (D : WeightedDesign m k) (N : NaimarkDual D r) :
    Matrix (Fin m) (Fin r) ℝ :=
  Matrix.of fun label coord => (D.weight label / coRoot D label) * N.co label coord

/-- The total gap is the co-weighted atom total. -/
theorem totalGap_eq_sum (D : WeightedDesign m k) :
    totalGap D = ∑ label, (1 - D.weight label) • atomMatrix (D.atom label) := by
  have hsplit : ∑ label, (1 - D.weight label) • atomMatrix (D.atom label)
      = (∑ label, atomMatrix (D.atom label))
        - ∑ label, D.weight label • atomMatrix (D.atom label) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by rw [sub_smul, one_smul]
  rw [hsplit, D.isParseval, totalGap, subsetSum]

/-- **THE GRAM OF THE TOTAL-GAP FRAME IS THE TOTAL GAP.** -/
theorem transpose_mul_totalGapFrame (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (totalGapFrame D)ᵀ * totalGapFrame D = totalGap D := by
  ext rowCoord colCoord
  rw [Matrix.mul_apply, totalGap_eq_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.transpose_apply, totalGapFrame, Matrix.of_apply, Matrix.of_apply,
    Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul, ← coRoot_mul_self D hm label]
  ring

/-- **THE GRAM OF THE SHARP FRAME IS THE SHARP TARGET.** -/
theorem transpose_mul_sharpFrame (D : WeightedDesign m k) (N : NaimarkDual D r) (hm : 2 ≤ m) :
    (sharpFrame D N)ᵀ * sharpFrame D N = naimarkSharpTarget N := by
  ext rowCoord colCoord
  rw [Matrix.mul_apply, naimarkSharpTarget_eq N hm, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun label _ => ?_
  have hroot := coRoot_mul_self D hm label
  have hne : coRoot D label ≠ 0 := ne_of_gt (coRoot_pos D hm label)
  have hco : (0 : ℝ) < 1 - D.weight label := by linarith [weight_lt_one D hm label]
  rw [Matrix.transpose_apply, sharpFrame, Matrix.of_apply, Matrix.of_apply,
    Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul, naimarkSharpCoeff,
    ← hroot]
  field_simp

/-- **THE TWO FRAMES ARE ORTHOGONAL.**  The two square roots cancel and what is
left is the dependency law of the Naimark dual. -/
theorem transpose_totalGapFrame_mul_sharpFrame (D : WeightedDesign m k) (N : NaimarkDual D r)
    (hm : 2 ≤ m) : (totalGapFrame D)ᵀ * sharpFrame D N = 0 := by
  ext rowCoord colCoord
  rw [Matrix.mul_apply, Matrix.zero_apply]
  have hterm : ∀ label : Fin m,
      (totalGapFrame D)ᵀ rowCoord label * sharpFrame D N label colCoord
        = D.weight label * D.atom label rowCoord * N.co label colCoord := by
    intro label
    have hne : coRoot D label ≠ 0 := ne_of_gt (coRoot_pos D hm label)
    rw [Matrix.transpose_apply, totalGapFrame, sharpFrame, Matrix.of_apply, Matrix.of_apply]
    field_simp
  rw [Finset.sum_congr rfl fun label _ => hterm label]
  exact N.dependency rowCoord colCoord

/-! ## Part C — the two hats, and the criterion -/

/-- The hat matrix of the total-gap frame. -/
noncomputable def totalGapHat (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  totalGapFrame D * (totalGap D)⁻¹ * (totalGapFrame D)ᵀ

/-- The hat matrix of the sharp frame. -/
noncomputable def sharpHat (D : WeightedDesign m k) (N : NaimarkDual D r) :
    Matrix (Fin m) (Fin m) ℝ :=
  sharpFrame D N * (naimarkSharpTarget N)⁻¹ * (sharpFrame D N)ᵀ

theorem totalGapHat_transpose (D : WeightedDesign m k) (_hm : 2 ≤ m) :
    (totalGapHat D)ᵀ = totalGapHat D := by
  rw [totalGapHat, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, totalGap_transpose, Matrix.mul_assoc]

theorem sharpHat_transpose (D : WeightedDesign m k) (N : NaimarkDual D r) (hm : 2 ≤ m) :
    (sharpHat D N)ᵀ = sharpHat D N := by
  have hsymm : (naimarkSharpTarget N)ᵀ = naimarkSharpTarget N :=
    PosDef.transpose_eq (naimarkSharpTarget_posDef N hm)
  rw [sharpHat, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, hsymm, Matrix.mul_assoc]

theorem totalGapHat_idem (D : WeightedDesign m k) (hm : 2 ≤ m) :
    totalGapHat D * totalGapHat D = totalGapHat D := by
  have hunit := isUnit_det_totalGap D hm
  rw [totalGapHat]
  calc totalGapFrame D * (totalGap D)⁻¹ * (totalGapFrame D)ᵀ
        * (totalGapFrame D * (totalGap D)⁻¹ * (totalGapFrame D)ᵀ)
      = totalGapFrame D * ((totalGap D)⁻¹ * ((totalGapFrame D)ᵀ * totalGapFrame D)
          * (totalGap D)⁻¹) * (totalGapFrame D)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = totalGapFrame D * (totalGap D)⁻¹ * (totalGapFrame D)ᵀ := by
        rw [transpose_mul_totalGapFrame D hm, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul,
          Matrix.mul_assoc]

theorem sharpHat_idem (D : WeightedDesign m k) (N : NaimarkDual D r) (hm : 2 ≤ m) :
    sharpHat D N * sharpHat D N = sharpHat D N := by
  have hunit : IsUnit (naimarkSharpTarget N).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (naimarkSharpTarget_posDef N hm).det_pos)
  rw [sharpHat]
  calc sharpFrame D N * (naimarkSharpTarget N)⁻¹ * (sharpFrame D N)ᵀ
        * (sharpFrame D N * (naimarkSharpTarget N)⁻¹ * (sharpFrame D N)ᵀ)
      = sharpFrame D N * ((naimarkSharpTarget N)⁻¹
          * ((sharpFrame D N)ᵀ * sharpFrame D N) * (naimarkSharpTarget N)⁻¹)
          * (sharpFrame D N)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = sharpFrame D N * (naimarkSharpTarget N)⁻¹ * (sharpFrame D N)ᵀ := by
        rw [transpose_mul_sharpFrame D N hm, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul,
          Matrix.mul_assoc]

/-- **THE TWO HATS ANNIHILATE EACH OTHER**, because the two frames are
orthogonal. -/
theorem totalGapHat_mul_sharpHat (D : WeightedDesign m k) (N : NaimarkDual D r) (hm : 2 ≤ m) :
    totalGapHat D * sharpHat D N = 0 := by
  rw [totalGapHat, sharpHat]
  calc totalGapFrame D * (totalGap D)⁻¹ * (totalGapFrame D)ᵀ
        * (sharpFrame D N * (naimarkSharpTarget N)⁻¹ * (sharpFrame D N)ᵀ)
      = totalGapFrame D * (totalGap D)⁻¹ * ((totalGapFrame D)ᵀ * sharpFrame D N)
          * ((naimarkSharpTarget N)⁻¹ * (sharpFrame D N)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by
        rw [transpose_totalGapFrame_mul_sharpFrame D N hm]
        simp

theorem trace_totalGapHat (D : WeightedDesign m k) (hm : 2 ≤ m) :
    Matrix.trace (totalGapHat D) = (k : ℝ) := by
  rw [totalGapHat, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    transpose_mul_totalGapFrame D hm, Matrix.mul_nonsing_inv _ (isUnit_det_totalGap D hm),
    Matrix.trace_one]
  simp

theorem trace_sharpHat (D : WeightedDesign m k) (N : NaimarkDual D r) (hm : 2 ≤ m) :
    Matrix.trace (sharpHat D N) = (r : ℝ) := by
  have hunit : IsUnit (naimarkSharpTarget N).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (naimarkSharpTarget_posDef N hm).det_pos)
  rw [sharpHat, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    transpose_mul_sharpFrame D N hm, Matrix.mul_nonsing_inv _ hunit, Matrix.trace_one]
  simp

/-- **THE TWO HATS RESOLVE THE IDENTITY.**  Two symmetric idempotents that
annihilate each other and whose traces fill the size sum to the identity. -/
theorem totalGapHat_add_sharpHat (D : WeightedDesign m k) (N : NaimarkDual D r) (hm : 2 ≤ m) :
    totalGapHat D + sharpHat D N = 1 := by
  have hcross := totalGapHat_mul_sharpHat D N hm
  have hcrossFlip : sharpHat D N * totalGapHat D = 0 := by
    have hstep := congrArg Matrix.transpose hcross
    rw [Matrix.transpose_mul, totalGapHat_transpose D hm, sharpHat_transpose D N hm,
      Matrix.transpose_zero] at hstep
    exact hstep
  refine eq_one_of_symmIdem_of_trace_eq ?_ ?_ ?_
  · rw [Matrix.transpose_add, totalGapHat_transpose D hm, sharpHat_transpose D N hm]
  · rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, totalGapHat_idem D hm,
      sharpHat_idem D N hm, hcross, hcrossFlip]
    abel
  · rw [Matrix.trace_add, trace_totalGapHat D hm, trace_sharpHat D N hm]
    have hcast : ((k : ℝ) + (r : ℝ)) = ((k + r : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, N.rankAdd]

/-! ### The diagonal reading -/

/-- **THE SHARP SHARE** at a label: the sharp design's own share, computed without
its whitener. -/
noncomputable def naimarkSharpShare (D : WeightedDesign m k) (N : NaimarkDual D r)
    (label : Fin m) : ℝ :=
  naimarkSharpCoeff D label * (N.co label ⬝ᵥ ((naimarkSharpTarget N)⁻¹ *ᵥ N.co label))

/-- **A HAT DIAGONAL IS THE ROW READ IN THE INVERSE METRIC.** -/
theorem hat_diag_eq {rows cols : ℕ} (frame : Matrix (Fin rows) (Fin cols) ℝ)
    (metric : Matrix (Fin cols) (Fin cols) ℝ) (label : Fin rows) :
    (frame * metric * frameᵀ) label label
      = (fun coord => frame label coord) ⬝ᵥ (metric *ᵥ (fun coord => frame label coord)) := by
  have hleft : (frame * metric * frameᵀ) label label
      = ∑ rowCoord, ∑ colCoord,
          frame label rowCoord * metric rowCoord colCoord * frame label colCoord := by
    rw [Matrix.mul_apply]
    have hterm : ∀ colCoord : Fin cols,
        (frame * metric) label colCoord * frameᵀ colCoord label
          = ∑ rowCoord, frame label rowCoord * metric rowCoord colCoord
              * frame label colCoord := by
      intro colCoord
      rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun colCoord _ => hterm colCoord, Finset.sum_comm]
  have hright : (fun coord => frame label coord)
        ⬝ᵥ (metric *ᵥ (fun coord => frame label coord))
      = ∑ rowCoord, ∑ colCoord,
          frame label rowCoord * metric rowCoord colCoord * frame label colCoord := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun rowCoord _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun colCoord _ => by ring
  rw [hleft, hright]

/-- Scaling a row scales its reading by the square of the scale. -/
theorem reading_smul {cols : ℕ} (metric : Matrix (Fin cols) (Fin cols) ℝ)
    (vec : Fin cols → ℝ) (scale : ℝ) :
    (fun coord => scale * vec coord) ⬝ᵥ (metric *ᵥ (fun coord => scale * vec coord))
      = scale ^ 2 * (vec ⬝ᵥ (metric *ᵥ vec)) := by
  have hsmul : (fun coord => scale * vec coord) = scale • vec := by
    funext coord; rw [Pi.smul_apply, smul_eq_mul]
  rw [hsmul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/-- **THE TOTAL-GAP HAT READS THE CO-ATOM READING.** -/
theorem totalGapHat_diag (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    totalGapHat D label label = (1 - D.weight label) * totalGapReading D label := by
  rw [totalGapHat, hat_diag_eq]
  have hrow : (fun coord => totalGapFrame D label coord)
      = fun coord => coRoot D label * D.atom label coord := by
    funext coord; rw [totalGapFrame, Matrix.of_apply]
  rw [hrow, reading_smul, totalGapReading, coRoot_sq D hm label]

/-- **THE SHARP HAT READS THE SHARP SHARE.** -/
theorem sharpHat_diag (D : WeightedDesign m k) (N : NaimarkDual D r) (hm : 2 ≤ m)
    (label : Fin m) :
    sharpHat D N label label = naimarkSharpShare D N label := by
  have hroot := coRoot_mul_self D hm label
  have hne : coRoot D label ≠ 0 := ne_of_gt (coRoot_pos D hm label)
  have hco : (0 : ℝ) < 1 - D.weight label := by linarith [weight_lt_one D hm label]
  rw [sharpHat, hat_diag_eq]
  have hrow : (fun coord => sharpFrame D N label coord)
      = fun coord => (D.weight label / coRoot D label) * N.co label coord := by
    funext coord; rw [sharpFrame, Matrix.of_apply]
  rw [hrow, reading_smul, naimarkSharpShare, naimarkSharpCoeff]
  have hsq : (D.weight label / coRoot D label) ^ 2
      = D.weight label * (D.weight label / (1 - D.weight label)) := by
    rw [div_pow, coRoot_sq D hm label]
    field_simp
  rw [hsq]

/-! ### The criterion -/

/-- **THE SHARP SHARE IS THE CO-ATOM READING.**  Reading the resolution of the
identity on the diagonal.  This is the load-bearing identity of the lane. -/
theorem one_sub_naimarkSharpShare (D : WeightedDesign m k) (N : NaimarkDual D r) (hm : 2 ≤ m)
    (label : Fin m) :
    1 - naimarkSharpShare D N label = (1 - D.weight label) * totalGapReading D label := by
  have hsum := congrFun (congrFun (totalGapHat_add_sharpHat D N hm) label) label
  rw [Matrix.add_apply, Matrix.one_apply_eq, totalGapHat_diag D hm label,
    sharpHat_diag D N hm label] at hsum
  linarith

/-- The sharp shares total the dual rank. -/
theorem sum_naimarkSharpShare (D : WeightedDesign m k) (N : NaimarkDual D r) (hm : 2 ≤ m) :
    ∑ label, naimarkSharpShare D N label = (r : ℝ) := by
  have hstep : ∀ label : Fin m,
      naimarkSharpShare D N label = 1 - (1 - D.weight label) * totalGapReading D label :=
    fun label => by linarith [one_sub_naimarkSharpShare D N hm label]
  rw [Finset.sum_congr rfl fun label _ => hstep label, Finset.sum_sub_distrib,
    sum_one_sub_weight_mul_totalGapReading D hm, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hcast : ((m : ℝ)) - (k : ℝ) = (r : ℝ) := by
    have := N.rankAdd
    have hc : ((k + r : ℕ) : ℝ) = (m : ℝ) := by rw [this]
    push_cast at hc
    linarith
  exact hcast

/-- **THE SHARP DESIGN HAS A UNIT ATOM EXACTLY AT A SINGULAR CO-ATOM SET.**  The
sharp leverage at `c` is one exactly when the co-atom set omitting `c` is a
corank-one weak dominator of the design. -/
theorem naimarkSharpShare_eq_weight_iff (D : WeightedDesign m k) (N : NaimarkDual D r)
    (hm : 2 ≤ m) (label : Fin m) :
    naimarkSharpShare D N label = D.weight label ↔ totalGapReading D label = 1 := by
  have hkey := one_sub_naimarkSharpShare D N hm label
  have hco : (0 : ℝ) < 1 - D.weight label := by linarith [weight_lt_one D hm label]
  constructor
  · intro heq
    rw [heq] at hkey
    have hone : (1 - D.weight label) * totalGapReading D label = 1 - D.weight label := by
      linarith
    have := mul_left_cancel₀ (ne_of_gt hco) (by linarith [hone] :
      (1 - D.weight label) * totalGapReading D label = (1 - D.weight label) * 1)
    exact this
  · intro heq
    rw [heq, mul_one] at hkey
    linarith

/-- **THE SHARP DESIGN IS ALL-HEAVY EXACTLY WHEN EVERY CO-ATOM SET DOMINATES
STRICTLY.**  At `(6,3)`: the sharp dual is all-heavy iff every five-set of the
design dominates strictly. -/
theorem forall_weight_lt_naimarkSharpShare_iff (D : WeightedDesign m k) (N : NaimarkDual D r)
    (hm : 2 ≤ m) :
    (∀ label : Fin m, D.weight label < naimarkSharpShare D N label)
      ↔ ∀ label : Fin m, (subsetSum D (Finset.univ.erase label) - 1).PosDef := by
  constructor
  · intro hall label
    refine (posDef_gap_erase_iff D hm label).mpr ?_
    have hkey := one_sub_naimarkSharpShare D N hm label
    have hco : (0 : ℝ) < 1 - D.weight label := by linarith [weight_lt_one D hm label]
    nlinarith [hall label, hkey, hco]
  · intro hall label
    have hlt := (posDef_gap_erase_iff D hm label).mp (hall label)
    have hkey := one_sub_naimarkSharpShare D N hm label
    have hco : (0 : ℝ) < 1 - D.weight label := by linarith [weight_lt_one D hm label]
    nlinarith [hlt, hkey, hco]

/-! ## Part D — the two caps of a pair

The chart of a design is a determinantal point process, and the two two-by-two
determinants are the two caps.  A parallel pair saturates the first, a coplanar
four-set the second. -/

/-- The chart entry of a pair: `P_pq = sqrt(t_p t_q) * p_pq`. -/
noncomputable def chartPairEntry (D : WeightedDesign m k) (leftLabel rightLabel : Fin m) : ℝ :=
  Real.sqrt (D.weight leftLabel * D.weight rightLabel)
    * (D.atom leftLabel ⬝ᵥ D.atom rightLabel)

theorem chartPairEntry_sq (D : WeightedDesign m k) (leftLabel rightLabel : Fin m) :
    chartPairEntry D leftLabel rightLabel ^ 2
      = D.weight leftLabel * D.weight rightLabel
        * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 := by
  have hroot : Real.sqrt (D.weight leftLabel * D.weight rightLabel)
      * Real.sqrt (D.weight leftLabel * D.weight rightLabel)
      = D.weight leftLabel * D.weight rightLabel :=
    Real.mul_self_sqrt (mul_nonneg (D.weight_pos leftLabel).le (D.weight_pos rightLabel).le)
  rw [chartPairEntry]
  nlinarith [hroot]

/-- **THE FIRST CAP.**  The share product against the squared chart entry is the
weighted leverage defect of the pair, so it vanishes exactly at a parallel
pair. -/
theorem sharePairForm_eq (D : WeightedDesign m k) (leftLabel rightLabel : Fin m) :
    D.weight leftLabel * leverageOf (D.atom leftLabel)
        * (D.weight rightLabel * leverageOf (D.atom rightLabel))
        - chartPairEntry D leftLabel rightLabel ^ 2
      = D.weight leftLabel * D.weight rightLabel
        * (leverageOf (D.atom leftLabel) * leverageOf (D.atom rightLabel)
          - (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2) := by
  rw [chartPairEntry_sq]
  ring

/-- **A PARALLEL PAIR SATURATES THE FIRST CAP**, and only a parallel pair does. -/
theorem sharePairForm_eq_zero_iff (D : WeightedDesign m k) (leftLabel rightLabel : Fin m) :
    D.weight leftLabel * leverageOf (D.atom leftLabel)
        * (D.weight rightLabel * leverageOf (D.atom rightLabel))
        - chartPairEntry D leftLabel rightLabel ^ 2 = 0
      ↔ (D.atom leftLabel = 0 ∨ ∃ scale : ℝ, D.atom rightLabel = scale • D.atom leftLabel) := by
  rw [sharePairForm_eq]
  have hpos : 0 < D.weight leftLabel * D.weight rightLabel :=
    mul_pos (D.weight_pos leftLabel) (D.weight_pos rightLabel)
  rw [mul_eq_zero]
  constructor
  · rintro (hbad | hgood)
    · exact absurd hbad (ne_of_gt hpos)
    · exact (leverageDefect_eq_zero_iff (D.atom leftLabel) (D.atom rightLabel)).mp hgood
  · intro hdep
    exact Or.inr ((leverageDefect_eq_zero_iff (D.atom leftLabel) (D.atom rightLabel)).mpr hdep)

/-- **THE SECOND CAP** is the co-share pair form of
`Gtz/Wave/SharpFiveSetCriterion.lean`, read through the chart entry. -/
theorem coSharePairForm_eq_chart (D : WeightedDesign m k) (leftLabel rightLabel : Fin m) :
    coSharePairForm D leftLabel rightLabel
      = coShareOf D leftLabel * coShareOf D rightLabel
        - chartPairEntry D leftLabel rightLabel ^ 2 := by
  rw [coSharePairForm, chartPairEntry_sq]

end Gtz
