import Gtz.Wave.KFourTreeWindowResidual
import Gtz.Design.ChartDesignWhitening

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The wall collapse

The two walls of the orbit-free A3 residual carry more structure than their
definitions state.  This module extracts that structure.

* `kernel_split_of_bump_kernel` — a kernel vector of a positive-semidefinite
  matrix plus one positive atom is a kernel vector of the matrix, and it is
  orthogonal to the atom direction.
* `corankTwo_kernel_split` — at the corank-two wall the second direction lies
  in the kernel of the TREE gap itself and is orthogonal to the pointer
  direction.  With the first direction, the tree gap kills a full plane: its
  rank is at most one.
* `corankTwo_exists_second_pointer` — the second direction carries its own
  outside pointer, and that pointer is distinct from the first.  The wall
  holds TWO pointers with transverse strict-positivity guarantees.
* `pivotWall_all_pivots_ge_one` — at the pivot wall the pointer's own deletion
  returns the weak tree, so its pivot joins the three wall pivots: all four
  window pivots are at least one.
* `mixedOnly_orthPlane_iff` — a plane through the origin meets the two closed
  sign orthants only at zero exactly when its normal is strictly one-signed.
  This is the classification that the corank-two sign analysis consumes.
-/

namespace Gtz

open Matrix

/-! ## The bump-kernel split -/

/-- A kernel vector of `A + scale • atom` splits: it is a kernel vector of `A`
and it is orthogonal to the atom direction. -/
theorem kernel_split_of_bump_kernel {A : Matrix (Fin 3) (Fin 3) ℝ}
    (htrans : Aᵀ = A) (hpsd : A.PosSemidef) {scale : ℝ} (hscale : 0 < scale)
    {bump probe : Fin 3 → ℝ}
    (hker : (A + scale • atomMatrix bump) *ᵥ probe = 0) :
    A *ᵥ probe = 0 ∧ bump ⬝ᵥ probe = 0 := by
  have hquad : probe ⬝ᵥ ((A + scale • atomMatrix bump) *ᵥ probe) = 0 := by
    rw [hker, dotProduct_zero]
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, dotProduct_atomMatrix_mulVec] at hquad
  have hA : 0 ≤ probe ⬝ᵥ (A *ᵥ probe) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
    rwa [star_trivial] at h
  have hB : 0 ≤ scale * (bump ⬝ᵥ probe) ^ 2 :=
    mul_nonneg hscale.le (sq_nonneg _)
  have hAzero : probe ⬝ᵥ (A *ᵥ probe) = 0 := by linarith
  have hBzero : (bump ⬝ᵥ probe) ^ 2 = 0 := by
    have hzero : scale * (bump ⬝ᵥ probe) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp hzero with hs | hsq
    · exact absurd hs (ne_of_gt hscale)
    · exact hsq
  exact ⟨mulVec_eq_zero_of_quadForm_eq_zero htrans hpsd hAzero,
    sq_eq_zero_iff.mp hBzero⟩

/-- Two kernel vectors span a kernel plane. -/
theorem mulVec_combination_eq_zero {G : Matrix (Fin 3) (Fin 3) ℝ}
    {x y : Fin 3 → ℝ} (hx : G *ᵥ x = 0) (hy : G *ᵥ y = 0) (a b : ℝ) :
    G *ᵥ (a • x + b • y) = 0 := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hy,
    smul_zero, smul_zero, add_zero]

/-! ## The corank-two collapse -/

/-- At the corank-two wall the window kernel vector collapses: it is a kernel
vector of the TREE gap and it is orthogonal to the pointer direction. -/
theorem corankTwo_kernel_split (point : DirectionChartPoint 6)
    {tree : Finset (Fin 6)} {pointer : Fin 6} (hpout : pointer ∉ tree)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    {probe : Fin 3 → ℝ}
    (hker : directionChartGap kFourDirection point.mass point.weight
      (insert pointer tree) *ᵥ probe = 0) :
    directionChartGap kFourDirection point.mass point.weight tree *ᵥ probe = 0 ∧
      kFourDirection pointer ⬝ᵥ probe = 0 := by
  rw [directionChartGap_insert kFourDirection point.mass point.weight tree hpout]
    at hker
  exact kernel_split_of_bump_kernel
    (directionChartGap_transpose kFourDirection point.mass point.weight tree)
    hweak (div_pos (point.mass_pos pointer) (point.weight_pos pointer)) hker

/-- The chart gap of one label reads strictly negatively at every nonzero probe
orthogonal to that label's direction.  The moment matrix eats the reading. -/
theorem singleton_gap_reading_neg (point : DirectionChartPoint 6)
    {label : Fin 6} {probe : Fin 3 → ℝ} (hne : probe ≠ 0)
    (horth : kFourDirection label ⬝ᵥ probe = 0) :
    probe ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
      {label} *ᵥ probe) < 0 := by
  have hmoment : 0 < probe ⬝ᵥ (kFourMomentMatrix point *ᵥ probe) := by
    have h := (Matrix.posDef_iff_dotProduct_mulVec.mp
      (kFourMomentMatrix_posDef point)).2 hne
    rwa [star_trivial] at h
  rw [dotProduct_kFourMomentMatrix_mulVec] at hmoment
  rw [dotProduct_directionChartGap_mulVec_eq, Finset.sum_singleton, horth]
  simpa using hmoment

/-- **THE SECOND POINTER.**  At the corank-two wall both tight directions lie
in the tree kernel, and each carries its own outside pointer.  The two
pointers are distinct: the first pointer's direction is orthogonal to the
second tight direction, so no selection through the first pointer can read
positively there. -/
theorem corankTwo_exists_second_pointer (point : DirectionChartPoint 6)
    {tree : Finset (Fin 6)} (htree : tree ∈ kFourSpanningTreeList)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hwall : KFourTreeWindowCorankTwoData point tree) :
    ∃ (firstPointer secondPointer : Fin 6)
      (tightDirection secondDirection : Fin 3 → ℝ),
      firstPointer ∉ tree ∧ secondPointer ∉ tree ∧
      secondPointer ≠ firstPointer ∧
      tightDirection ≠ 0 ∧ secondDirection ≠ 0 ∧
      directionChartGap kFourDirection point.mass point.weight tree
        *ᵥ tightDirection = 0 ∧
      directionChartGap kFourDirection point.mass point.weight tree
        *ᵥ secondDirection = 0 ∧
      kFourDirection firstPointer ⬝ᵥ secondDirection = 0 ∧
      (¬ ∃ scale : ℝ, secondDirection = scale • tightDirection) ∧
      (∀ swap : Finset (Fin 6), firstPointer ∈ swap →
        0 < tightDirection ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight swap *ᵥ tightDirection)) ∧
      (∀ swap : Finset (Fin 6), secondPointer ∈ swap →
        0 < secondDirection ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight swap *ᵥ secondDirection)) := by
  obtain ⟨tightDirection, secondDirection, pointer, htightNe, hpout,
    htightKernel, hpointerReads, hsecondNe, hwindowKernel, hnotCollinear⟩ := hwall
  obtain ⟨hsecondKernel, horth⟩ :=
    corankTwo_kernel_split point hpout hweak hwindowKernel
  have hcard : 2 ≤ tree.card := by
    rw [kFourSpanningTree_card tree htree]
    omega
  obtain ⟨second, hsecondOut, hsecondReads⟩ :=
    kFour_pointer_of_kernel point hcard hsecondNe hsecondKernel
  have hne : second ≠ pointer := by
    intro heq
    have hread := hsecondReads {pointer} (by rw [heq]; exact Finset.mem_singleton_self pointer)
    have hneg := singleton_gap_reading_neg point hsecondNe horth
    linarith
  exact ⟨pointer, second, tightDirection, secondDirection, hpout, hsecondOut,
    hne, htightNe, hsecondNe, htightKernel, hsecondKernel, horth,
    hnotCollinear, hpointerReads, hsecondReads⟩

/-! ## The pivot wall sharpening -/

/-- Deleting the pointer from a positive-definite window returns the weak
tree, so the pointer's own ladder pivot is at least one. -/
theorem pivotWall_pointer_pivot_ge_one (point : DirectionChartPoint 6)
    {tree : Finset (Fin 6)} {pointer : Fin 6} (hpout : pointer ∉ tree)
    (hnotPD : ¬ (directionChartGap kFourDirection point.mass point.weight
      tree).PosDef)
    (hwindow : (directionChartGap kFourDirection point.mass point.weight
      (insert pointer tree)).PosDef) :
    1 ≤ chartLadderPivot kFourDirection point.mass point.weight
      (insert pointer tree) pointer := by
  by_contra hlt
  push Not at hlt
  have hpd := (posDef_directionChartGap_erase_iff kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos (insert pointer tree)
    (Finset.mem_insert_self pointer tree) hwindow).mpr hlt
  rw [Finset.erase_insert hpout] at hpd
  exact hnotPD hpd

/-- **ALL FOUR PIVOTS.**  At the pivot wall over a weak non-strict tree, every
label of the window has ladder pivot at least one: the three wall pivots from
the data, and the pointer's own pivot from the weak tree. -/
theorem pivotWall_all_pivots_ge_one (point : DirectionChartPoint 6)
    {tree : Finset (Fin 6)}
    (hnotPD : ¬ (directionChartGap kFourDirection point.mass point.weight
      tree).PosDef)
    (hwall : KFourTreeWindowPivotWallData point tree) :
    ∃ pointer : Fin 6, pointer ∉ tree ∧
      (directionChartGap kFourDirection point.mass point.weight
        (insert pointer tree)).PosDef ∧
      ∀ label ∈ insert pointer tree,
        1 ≤ chartLadderPivot kFourDirection point.mass point.weight
          (insert pointer tree) label := by
  obtain ⟨pointer, hpout, hwindow, hpivots⟩ := hwall
  refine ⟨pointer, hpout, hwindow, ?_⟩
  intro label hlabel
  rcases Finset.mem_insert.mp hlabel with hp | ht
  · subst hp
    exact pivotWall_pointer_pivot_ge_one point hpout hnotPD hwindow
  · exact hpivots label ht

/-! ## The mixed-only plane classification -/

/-- A strictly positive normal forces a negative entry on every nonzero
orthogonal vector. -/
theorem exists_neg_entry_of_pos_normal_of_orth {normal : Fin 3 → ℝ}
    (hnormal : ∀ index, 0 < normal index) {probe : Fin 3 → ℝ}
    (hdot : normal ⬝ᵥ probe = 0) (hne : probe ≠ 0) :
    ∃ index, probe index < 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨witness, hwitness⟩ := Function.ne_iff.mp hne
  have hwitnessPos : 0 < probe witness :=
    lt_of_le_of_ne (hno witness) (by simpa using (Ne.symm hwitness))
  have hsum : 0 < normal ⬝ᵥ probe := by
    refine Finset.sum_pos' (fun index _ => mul_nonneg (hnormal index).le
      (hno index)) ⟨witness, Finset.mem_univ witness, ?_⟩
    exact mul_pos (hnormal witness) hwitnessPos
  linarith

/-- **THE MIXED-ONLY PLANE CLASSIFICATION.**  Every nonzero vector orthogonal
to a normal carries both signs exactly when the normal is strictly one-signed. -/
theorem mixedOnly_orthPlane_iff (normal : Fin 3 → ℝ) :
    (∀ probe : Fin 3 → ℝ, probe ≠ 0 → normal ⬝ᵥ probe = 0 →
      (∃ index, 0 < probe index) ∧ ∃ index, probe index < 0)
    ↔ ((∀ index, 0 < normal index) ∨ ∀ index, normal index < 0) := by
  constructor
  · intro hmixed
    by_contra hnot
    push Not at hnot
    obtain ⟨⟨lower, hlower⟩, ⟨upper, hupper⟩⟩ := hnot
    rcases eq_or_lt_of_le hlower with hzero | hneg
    · -- A vanishing normal entry admits the nonnegative basis probe.
      obtain ⟨_, ⟨index, hindex⟩⟩ := hmixed (Pi.single lower 1)
        (by
          intro hcontra
          have := congrFun hcontra lower
          simp [Pi.single_eq_same] at this)
        (by
          have hdot : normal ⬝ᵥ Pi.single lower (1 : ℝ) = normal lower := by
            simp [dotProduct, Pi.single_apply]
          rw [hdot]
          exact hzero)
      rw [Pi.single_apply] at hindex
      split_ifs at hindex <;> linarith
    · rcases eq_or_lt_of_le hupper with hzero | hpos
      · obtain ⟨_, ⟨index, hindex⟩⟩ := hmixed (Pi.single upper 1)
          (by
            intro hcontra
            have := congrFun hcontra upper
            simp [Pi.single_eq_same] at this)
          (by
            have hdot : normal ⬝ᵥ Pi.single upper (1 : ℝ) = normal upper := by
              simp [dotProduct, Pi.single_apply]
            rw [hdot]
            exact hzero.symm)
        rw [Pi.single_apply] at hindex
        split_ifs at hindex <;> linarith
      · -- Mixed normal entries admit the two-coordinate nonnegative probe.
        have hlu : lower ≠ upper := by
          intro heq
          rw [heq] at hneg
          linarith
        set probe : Fin 3 → ℝ :=
          (-normal lower) • Pi.single upper (1 : ℝ)
            + normal upper • Pi.single lower (1 : ℝ) with hprobe
        have hupperEntry : probe upper = -normal lower := by
          simp [hprobe, hlu.symm]
        have hdotSingle : ∀ index : Fin 3,
            normal ⬝ᵥ Pi.single index (1 : ℝ) = normal index := by
          intro index
          simp [dotProduct, Pi.single_apply]
        obtain ⟨_, ⟨index, hindex⟩⟩ := hmixed probe
          (by
            intro hcontra
            have := congrFun hcontra upper
            rw [hupperEntry] at this
            simp at this
            linarith)
          (by
            rw [hprobe, dotProduct_add, dotProduct_smul, dotProduct_smul,
              hdotSingle, hdotSingle, smul_eq_mul, smul_eq_mul]
            ring)
        have hentry : probe index =
            (-normal lower) * (if index = upper then 1 else 0)
              + normal upper * (if index = lower then 1 else 0) := by
          rw [hprobe]
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        rw [hentry] at hindex
        split_ifs at hindex <;> nlinarith
  · intro hsigned probe hne hdot
    rcases hsigned with hpos | hneg
    · refine ⟨?_, exists_neg_entry_of_pos_normal_of_orth hpos hdot hne⟩
      obtain ⟨index, hindex⟩ := exists_neg_entry_of_pos_normal_of_orth hpos
        (by rw [dotProduct_neg, hdot, neg_zero]) (neg_ne_zero.mpr hne)
      exact ⟨index, by simpa using hindex⟩
    · have hposNeg : ∀ index, 0 < (-normal) index := by
        intro index
        simpa using hneg index
      have hdotNeg : (-normal) ⬝ᵥ probe = 0 := by
        rw [neg_dotProduct, hdot, neg_zero]
      refine ⟨?_, exists_neg_entry_of_pos_normal_of_orth hposNeg hdotNeg hne⟩
      obtain ⟨index, hindex⟩ := exists_neg_entry_of_pos_normal_of_orth hposNeg
        (by rw [dotProduct_neg, hdotNeg, neg_zero]) (neg_ne_zero.mpr hne)
      exact ⟨index, by simpa using hindex⟩

end Gtz
