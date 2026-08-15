import Gtz.Design.StarOnlyLaw
import Gtz.Design.StratumSqueeze
import Gtz.Wave.KFourTreeWindowCorankReduction
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The star-wall transport

The chart grounds at vertex `d`, so the naive vertex relabeling does not act
on the chart coordinates.  But the vertex four-cycle `a → d → c → b → a`
lifts to an explicit unimodular congruence: the edge permutation
`0 → 3 → 5 → 2 → 0, 1 → 4 → 1` together with the matrix
`N = !![0,1,0; 0,0,1; -1,-1,-1]` satisfies `N *ᵥ v c = ± v (π c)` at all six
chart directions.  The consequences land here.

* `kFourChartGap_image` — the congruence: the chart gap of the relabeled data
  at the image selection is `N * gap * Nᵀ`.
* `kFourGap_image_posSemidef_iff`, `kFourGap_image_posDef_iff` — semidefinite
  and definite transport, both directions, through the `PsdKit` congruence.
* `kFourCorankData_image` — the corank-two wall data transports to the image
  tree at the relabeled point.
* `kFourStarWall_strictTree_of_gauge` — **the reduction**: a strict-tree law
  at the gauge-star wall alone gives the strict-tree law at all four star
  walls.  The star walls cycle onto the gauge wall under one, two, or three
  applications of the relabeling.

The star-A wall family in its own coordinates is the gauge family under the
axis substitution `(y 0, y 1, y 2) ↦ (y 1, y 2, y 0 - y 1 - y 2)`; the
transport makes the per-family case work unnecessary.
-/

namespace Gtz

open Matrix

/-! ## 1. The edge four-cycle -/

/-- The edge action of the vertex four-cycle `a → d → c → b → a`. -/
def kFourEdgeCycle : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 0
  | 3 => 5
  | 4 => 1
  | 5 => 2

/-- The inverse edge action. -/
def kFourEdgeCycleInv : Fin 6 → Fin 6
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 3

/-- The edge four-cycle as a permutation. -/
def kFourEdgeCycleEquiv : Equiv.Perm (Fin 6) :=
  ⟨kFourEdgeCycle, kFourEdgeCycleInv, by decide, by decide⟩

theorem kFourEdgeCycleInv_comp (c : Fin 6) :
    kFourEdgeCycleInv (kFourEdgeCycle c) = c := by
  revert c; decide

theorem kFourEdgeCycle_comp (c : Fin 6) :
    kFourEdgeCycle (kFourEdgeCycleInv c) = c := by
  revert c; decide

theorem kFourEdgeCycle_injective : Function.Injective kFourEdgeCycle :=
  Function.LeftInverse.injective kFourEdgeCycleInv_comp

/-- Membership in the image selection reads on the source selection. -/
theorem kFourEdgeCycle_mem_image_iff (C : Finset (Fin 6)) (c : Fin 6) :
    kFourEdgeCycle c ∈ C.image kFourEdgeCycle ↔ c ∈ C := by
  constructor
  · intro h
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp h
    rwa [kFourEdgeCycle_injective hae] at ha
  · exact fun h => Finset.mem_image_of_mem _ h

/-- The image under the inverse recovers the preimage selection. -/
theorem kFourEdgeCycle_image_image (C : Finset (Fin 6)) :
    (C.image kFourEdgeCycleInv).image kFourEdgeCycle = C := by
  rw [Finset.image_image]
  have : kFourEdgeCycle ∘ kFourEdgeCycleInv = id := by
    funext c; exact kFourEdgeCycle_comp c
  rw [this, Finset.image_id]

/-! ## 2. The chart lift of the cycle -/

/-- The unimodular chart lift of the vertex four-cycle. -/
def kFourCycleMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 0, 0, 1; -1, -1, -1]

/-- The inverse of the chart lift. -/
def kFourCycleInv : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, -1, -1; 1, 0, 0; 0, 1, 0]

theorem kFourCycleInv_mul :
    kFourCycleInv * kFourCycleMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kFourCycleInv, kFourCycleMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem kFourCycleMatrix_mul_inv :
    kFourCycleMatrix * kFourCycleInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kFourCycleInv, kFourCycleMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem kFourCycleMatrixT_mul_invT :
    kFourCycleMatrixᵀ * kFourCycleInvᵀ = 1 := by
  rw [← Matrix.transpose_mul, kFourCycleInv_mul, Matrix.transpose_one]

theorem kFourCycleMatrixT_det : (kFourCycleMatrixᵀ).det = -1 := by
  rw [Matrix.det_transpose]
  simp [kFourCycleMatrix, Matrix.det_fin_three]

theorem isUnit_kFourCycleMatrixT_det : IsUnit (kFourCycleMatrixᵀ).det := by
  rw [kFourCycleMatrixT_det]
  exact isUnit_one.neg

/-! ## 3. The six direction identities -/

theorem kFourCycle_dir_zero :
    kFourCycleMatrix *ᵥ kFourDirection 0 = -kFourDirection 3 := by
  funext i; fin_cases i <;>
    simp [kFourCycleMatrix, kFourDirection, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

theorem kFourCycle_dir_one :
    kFourCycleMatrix *ᵥ kFourDirection 1 = -kFourDirection 4 := by
  funext i; fin_cases i <;>
    simp [kFourCycleMatrix, kFourDirection, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

theorem kFourCycle_dir_two :
    kFourCycleMatrix *ᵥ kFourDirection 2 = kFourDirection 0 := by
  funext i; fin_cases i <;>
    simp [kFourCycleMatrix, kFourDirection, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

theorem kFourCycle_dir_three :
    kFourCycleMatrix *ᵥ kFourDirection 3 = -kFourDirection 5 := by
  funext i; fin_cases i <;>
    simp [kFourCycleMatrix, kFourDirection, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

theorem kFourCycle_dir_four :
    kFourCycleMatrix *ᵥ kFourDirection 4 = kFourDirection 1 := by
  funext i; fin_cases i <;>
    simp [kFourCycleMatrix, kFourDirection, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

theorem kFourCycle_dir_five :
    kFourCycleMatrix *ᵥ kFourDirection 5 = kFourDirection 2 := by
  funext i; fin_cases i <;>
    simp [kFourCycleMatrix, kFourDirection, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-! ## 4. The atom conjugation -/

/-- The atom of a matrix image is the matrix conjugate of the atom. -/
theorem atomMatrix_mulVec_conj (M : Matrix (Fin 3) (Fin 3) ℝ)
    (v : Fin 3 → ℝ) :
    atomMatrix (M *ᵥ v) = M * atomMatrix v * Mᵀ := by
  ext i j
  simp [atomMatrix, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]
  ring

/-- Each direction atom at the image label is the conjugate of the source
atom: the sign of the lift is invisible to the atom. -/
theorem atomMatrix_direction_image (c : Fin 6) :
    atomMatrix (kFourDirection (kFourEdgeCycle c))
      = kFourCycleMatrix * atomMatrix (kFourDirection c) * kFourCycleMatrixᵀ := by
  fin_cases c
  · show atomMatrix (kFourDirection 3)
        = kFourCycleMatrix * atomMatrix (kFourDirection 0) * kFourCycleMatrixᵀ
    have h : kFourDirection 3 = -(kFourCycleMatrix *ᵥ kFourDirection 0) := by
      rw [kFourCycle_dir_zero, neg_neg]
    rw [h, atomMatrix_neg, atomMatrix_mulVec_conj]
  · show atomMatrix (kFourDirection 4)
        = kFourCycleMatrix * atomMatrix (kFourDirection 1) * kFourCycleMatrixᵀ
    have h : kFourDirection 4 = -(kFourCycleMatrix *ᵥ kFourDirection 1) := by
      rw [kFourCycle_dir_one, neg_neg]
    rw [h, atomMatrix_neg, atomMatrix_mulVec_conj]
  · show atomMatrix (kFourDirection 0)
        = kFourCycleMatrix * atomMatrix (kFourDirection 2) * kFourCycleMatrixᵀ
    rw [← kFourCycle_dir_two, atomMatrix_mulVec_conj]
  · show atomMatrix (kFourDirection 5)
        = kFourCycleMatrix * atomMatrix (kFourDirection 3) * kFourCycleMatrixᵀ
    have h : kFourDirection 5 = -(kFourCycleMatrix *ᵥ kFourDirection 3) := by
      rw [kFourCycle_dir_three, neg_neg]
    rw [h, atomMatrix_neg, atomMatrix_mulVec_conj]
  · show atomMatrix (kFourDirection 1)
        = kFourCycleMatrix * atomMatrix (kFourDirection 4) * kFourCycleMatrixᵀ
    rw [← kFourCycle_dir_four, atomMatrix_mulVec_conj]
  · show atomMatrix (kFourDirection 2)
        = kFourCycleMatrix * atomMatrix (kFourDirection 5) * kFourCycleMatrixᵀ
    rw [← kFourCycle_dir_five, atomMatrix_mulVec_conj]

/-! ## 5. The gap congruence -/

/-- **The congruence.**  The chart gap of the relabeled data at the image
selection is the unimodular conjugate of the source gap. -/
theorem kFourChartGap_image (mass weight : Fin 6 → ℝ) (C : Finset (Fin 6)) :
    directionChartGap kFourDirection (fun c => mass (kFourEdgeCycleInv c))
        (fun c => weight (kFourEdgeCycleInv c)) (C.image kFourEdgeCycle)
      = kFourCycleMatrix
          * directionChartGap kFourDirection mass weight C
          * kFourCycleMatrixᵀ := by
  rw [directionChartGap_eq_coeff_sum, directionChartGap_eq_coeff_sum,
    Finset.mul_sum, Finset.sum_mul]
  rw [← Equiv.sum_comp kFourEdgeCycleEquiv
    (fun label => chartCoeff (fun c => mass (kFourEdgeCycleInv c))
      (fun c => weight (kFourEdgeCycleInv c)) (C.image kFourEdgeCycle) label
        • atomMatrix (kFourDirection label))]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hcoeff : chartCoeff (fun c' => mass (kFourEdgeCycleInv c'))
      (fun c' => weight (kFourEdgeCycleInv c')) (C.image kFourEdgeCycle)
      (kFourEdgeCycleEquiv c) = chartCoeff mass weight C c := by
    show chartCoeff _ _ _ (kFourEdgeCycle c) = _
    unfold chartCoeff
    simp only [kFourEdgeCycleInv_comp]
    by_cases h : c ∈ C
    · rw [if_pos h, if_pos ((kFourEdgeCycle_mem_image_iff C c).mpr h)]
    · rw [if_neg h,
        if_neg (fun hc => h ((kFourEdgeCycle_mem_image_iff C c).mp hc))]
  show chartCoeff _ _ _ (kFourEdgeCycleEquiv c)
      • atomMatrix (kFourDirection (kFourEdgeCycleEquiv c)) = _
  rw [hcoeff, show (kFourEdgeCycleEquiv c : Fin 6) = kFourEdgeCycle c from rfl,
    atomMatrix_direction_image, Matrix.mul_smul, Matrix.smul_mul]

/-! ## 6. The relabeled point and the definite transports -/

/-- The relabeled chart point. -/
def kFourRelabelPoint (point : DirectionChartPoint 6) :
    DirectionChartPoint 6 where
  mass c := point.mass (kFourEdgeCycleInv c)
  weight c := point.weight (kFourEdgeCycleInv c)
  mass_pos c := point.mass_pos _
  weight_pos c := point.weight_pos _
  weight_sum_one := by
    have hbij : Function.Bijective kFourEdgeCycleInv :=
      Function.bijective_iff_has_inverse.mpr
        ⟨kFourEdgeCycle, kFourEdgeCycle_comp, kFourEdgeCycleInv_comp⟩
    exact (Fintype.sum_bijective kFourEdgeCycleInv hbij _ point.weight
      (fun x => rfl)).trans point.weight_sum_one

theorem kFourChartGap_relabel (point : DirectionChartPoint 6)
    (C : Finset (Fin 6)) :
    directionChartGap kFourDirection (kFourRelabelPoint point).mass
        (kFourRelabelPoint point).weight (C.image kFourEdgeCycle)
      = kFourCycleMatrix
          * directionChartGap kFourDirection point.mass point.weight C
          * kFourCycleMatrixᵀ :=
  kFourChartGap_image point.mass point.weight C

/-- Semidefinite transport across the relabeling, both directions. -/
theorem kFourGap_relabel_posSemidef_iff (point : DirectionChartPoint 6)
    (C : Finset (Fin 6)) :
    (directionChartGap kFourDirection (kFourRelabelPoint point).mass
        (kFourRelabelPoint point).weight (C.image kFourEdgeCycle)).PosSemidef
      ↔ (directionChartGap kFourDirection point.mass point.weight C).PosSemidef
    := by
  rw [kFourChartGap_relabel]
  have hsym := directionChartGap_transpose kFourDirection point.mass
    point.weight C
  have h := posSemidef_congr_right (X := directionChartGap kFourDirection
      point.mass point.weight C) (P := kFourCycleMatrixᵀ) hsym
    isUnit_kFourCycleMatrixT_det
  rw [Matrix.transpose_transpose] at h
  exact h.symm

/-- Definite transport across the relabeling, both directions. -/
theorem kFourGap_relabel_posDef_iff (point : DirectionChartPoint 6)
    (C : Finset (Fin 6)) :
    (directionChartGap kFourDirection (kFourRelabelPoint point).mass
        (kFourRelabelPoint point).weight (C.image kFourEdgeCycle)).PosDef
      ↔ (directionChartGap kFourDirection point.mass point.weight C).PosDef
    := by
  rw [kFourChartGap_relabel]
  have hsym := directionChartGap_transpose kFourDirection point.mass
    point.weight C
  have h := posDef_congr_right (X := directionChartGap kFourDirection
      point.mass point.weight C) (P := kFourCycleMatrixᵀ) hsym
    isUnit_kFourCycleMatrixT_det
  rw [Matrix.transpose_transpose] at h
  exact h.symm

/-! ## 7. The corank-data transport -/

theorem kFourCycleInvT_cancel (x : Fin 3 → ℝ) :
    kFourCycleMatrixᵀ *ᵥ (kFourCycleInvᵀ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, kFourCycleMatrixT_mul_invT, Matrix.one_mulVec]

/-- The inverse-transpose pairing against the lift is the source pairing. -/
theorem kFourCycle_pairing (a b : Fin 3 → ℝ) :
    (kFourCycleInvᵀ *ᵥ a) ⬝ᵥ (kFourCycleMatrix *ᵥ b) = a ⬝ᵥ b := by
  rw [dotProduct_mulVec_transpose kFourCycleInv a (kFourCycleMatrix *ᵥ b),
    Matrix.mulVec_mulVec, kFourCycleInv_mul, Matrix.one_mulVec]

/-- **The wall-data transport.**  Corank-two data at any selection moves to
the image selection at the relabeled point. -/
theorem kFourCorankData_image (point : DirectionChartPoint 6)
    (T : Finset (Fin 6)) (h : KFourTreeGapCorankTwoData point T) :
    KFourTreeGapCorankTwoData (kFourRelabelPoint point)
      (T.image kFourEdgeCycle) := by
  obtain ⟨tight, second, pointer, htne, hpout, hker, hswap, hsne, hker2,
    hperp, hprop⟩ := h
  refine ⟨kFourCycleInvᵀ *ᵥ tight, kFourCycleInvᵀ *ᵥ second,
    kFourEdgeCycle pointer, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply htne
    have := congrArg (fun x => kFourCycleMatrixᵀ *ᵥ x) h0
    simpa [Matrix.mulVec_mulVec, kFourCycleMatrixT_mul_invT,
      Matrix.one_mulVec, Matrix.mulVec_zero] using this
  · intro hc
    exact hpout ((kFourEdgeCycle_mem_image_iff T pointer).mp hc)
  · rw [kFourChartGap_relabel, ← Matrix.mulVec_mulVec, kFourCycleInvT_cancel,
      ← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]
  · intro swap hpmem
    have hswapimg : swap = (swap.image kFourEdgeCycleInv).image kFourEdgeCycle :=
      (kFourEdgeCycle_image_image swap).symm
    have hpmem0 : pointer ∈ swap.image kFourEdgeCycleInv := by
      have := Finset.mem_image_of_mem kFourEdgeCycleInv hpmem
      rwa [kFourEdgeCycleInv_comp pointer] at this
    rw [hswapimg, kFourChartGap_relabel, ← Matrix.mulVec_mulVec,
      kFourCycleInvT_cancel, ← Matrix.mulVec_mulVec, kFourCycle_pairing]
    exact hswap (swap.image kFourEdgeCycleInv) hpmem0
  · intro h0
    apply hsne
    have := congrArg (fun x => kFourCycleMatrixᵀ *ᵥ x) h0
    simpa [Matrix.mulVec_mulVec, kFourCycleMatrixT_mul_invT,
      Matrix.one_mulVec, Matrix.mulVec_zero] using this
  · rw [kFourChartGap_relabel, ← Matrix.mulVec_mulVec, kFourCycleInvT_cancel,
      ← Matrix.mulVec_mulVec, hker2, Matrix.mulVec_zero]
  · have hpair : ∀ c : Fin 6, ∀ s : Fin 3 → ℝ,
        kFourDirection (kFourEdgeCycle c) ⬝ᵥ (kFourCycleInvᵀ *ᵥ s)
          = kFourDirection c ⬝ᵥ s ∨
        kFourDirection (kFourEdgeCycle c) ⬝ᵥ (kFourCycleInvᵀ *ᵥ s)
          = -(kFourDirection c ⬝ᵥ s) := by
      intro c s
      have hflip : ∀ v : Fin 3 → ℝ,
          (kFourCycleMatrix *ᵥ v) ⬝ᵥ (kFourCycleInvᵀ *ᵥ s) = v ⬝ᵥ s := by
        intro v
        rw [dotProduct_comm, kFourCycle_pairing, dotProduct_comm]
      fin_cases c
      · right
        show kFourDirection 3 ⬝ᵥ (kFourCycleInvᵀ *ᵥ s)
            = -(kFourDirection 0 ⬝ᵥ s)
        rw [show kFourDirection 3 = -(kFourCycleMatrix *ᵥ kFourDirection 0) by
            rw [kFourCycle_dir_zero, neg_neg],
          neg_dotProduct, hflip]
      · right
        show kFourDirection 4 ⬝ᵥ (kFourCycleInvᵀ *ᵥ s)
            = -(kFourDirection 1 ⬝ᵥ s)
        rw [show kFourDirection 4 = -(kFourCycleMatrix *ᵥ kFourDirection 1) by
            rw [kFourCycle_dir_one, neg_neg],
          neg_dotProduct, hflip]
      · left
        show kFourDirection 0 ⬝ᵥ (kFourCycleInvᵀ *ᵥ s)
            = kFourDirection 2 ⬝ᵥ s
        rw [← kFourCycle_dir_two, hflip]
      · right
        show kFourDirection 5 ⬝ᵥ (kFourCycleInvᵀ *ᵥ s)
            = -(kFourDirection 3 ⬝ᵥ s)
        rw [show kFourDirection 5 = -(kFourCycleMatrix *ᵥ kFourDirection 3) by
            rw [kFourCycle_dir_three, neg_neg],
          neg_dotProduct, hflip]
      · left
        show kFourDirection 1 ⬝ᵥ (kFourCycleInvᵀ *ᵥ s)
            = kFourDirection 4 ⬝ᵥ s
        rw [← kFourCycle_dir_four, hflip]
      · left
        show kFourDirection 2 ⬝ᵥ (kFourCycleInvᵀ *ᵥ s)
            = kFourDirection 5 ⬝ᵥ s
        rw [← kFourCycle_dir_five, hflip]
    rcases hpair pointer second with hcase | hcase
    · rw [hcase, hperp]
    · rw [hcase, hperp, neg_zero]
  · rintro ⟨scale, hs⟩
    apply hprop
    refine ⟨scale, ?_⟩
    have := congrArg (fun x => kFourCycleMatrixᵀ *ᵥ x) hs
    simpa [Matrix.mulVec_mulVec, kFourCycleMatrixT_mul_invT,
      Matrix.one_mulVec, Matrix.mulVec_smul] using this

/-! ## 8. The strict-tree pull-back and the four-star reduction -/

theorem kFourTreeList_image_inv :
    ∀ T ∈ kFourSpanningTreeList,
      T.image kFourEdgeCycleInv ∈ kFourSpanningTreeList := by
  decide

/-- A strict tree at the relabeled point pulls back to a strict tree at the
source point. -/
theorem kFourStrict_pullback (point : DirectionChartPoint 6)
    (h : ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection (kFourRelabelPoint point).mass
        (kFourRelabelPoint point).weight tree).PosDef) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef
    := by
  obtain ⟨tree, htree, hpd⟩ := h
  refine ⟨tree.image kFourEdgeCycleInv, kFourTreeList_image_inv tree htree, ?_⟩
  have himg : (tree.image kFourEdgeCycleInv).image kFourEdgeCycle = tree :=
    kFourEdgeCycle_image_image tree
  rw [← kFourGap_relabel_posDef_iff point (tree.image kFourEdgeCycleInv), himg]
  exact hpd

/-- **The four-star reduction.**  A strict-tree law at the gauge-star wall
gives the strict-tree law at every star wall: the star walls cycle onto the
gauge wall under one, two, or three relabelings. -/
theorem kFourStarWall_strictTree_of_gauge
    (hgauge : ∀ point : DirectionChartPoint 6,
      (directionChartGap kFourDirection point.mass point.weight
        ({3, 4, 5} : Finset (Fin 6))).PosSemidef →
      KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)) →
      ∃ tree ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight
          tree).PosDef)
    (point : DirectionChartPoint 6) (tree : Finset (Fin 6))
    (hstar : tree ∈ kFourStarList)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hdata : KFourTreeGapCorankTwoData point tree) :
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight
        winner).PosDef := by
  have hstep : ∀ (q : DirectionChartPoint 6) (T : Finset (Fin 6)),
      (directionChartGap kFourDirection q.mass q.weight T).PosSemidef →
      KFourTreeGapCorankTwoData q T →
      (directionChartGap kFourDirection (kFourRelabelPoint q).mass
          (kFourRelabelPoint q).weight (T.image kFourEdgeCycle)).PosSemidef ∧
        KFourTreeGapCorankTwoData (kFourRelabelPoint q)
          (T.image kFourEdgeCycle) := by
    intro q T hq hd
    exact ⟨(kFourGap_relabel_posSemidef_iff q T).mpr hq,
      kFourCorankData_image q T hd⟩
  have hlist : kFourStarList
      = [({0, 1, 3} : Finset (Fin 6)), {0, 2, 4}, {1, 2, 5}, {3, 4, 5}] := rfl
  rw [hlist] at hstar
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hstar
  rcases hstar with h013 | h024 | h125 | h345
  · -- one relabeling reaches the gauge wall
    subst h013
    obtain ⟨hpsd1, hdata1⟩ := hstep point _ hpsd hdata
    rw [show (({0, 1, 3} : Finset (Fin 6)).image kFourEdgeCycle)
        = ({3, 4, 5} : Finset (Fin 6)) from by decide] at hpsd1 hdata1
    exact kFourStrict_pullback point (hgauge _ hpsd1 hdata1)
  · -- two relabelings
    subst h024
    obtain ⟨hpsd1, hdata1⟩ := hstep point _ hpsd hdata
    rw [show (({0, 2, 4} : Finset (Fin 6)).image kFourEdgeCycle)
        = ({0, 1, 3} : Finset (Fin 6)) from by decide] at hpsd1 hdata1
    obtain ⟨hpsd2, hdata2⟩ := hstep (kFourRelabelPoint point) _ hpsd1 hdata1
    rw [show (({0, 1, 3} : Finset (Fin 6)).image kFourEdgeCycle)
        = ({3, 4, 5} : Finset (Fin 6)) from by decide] at hpsd2 hdata2
    exact kFourStrict_pullback point
      (kFourStrict_pullback (kFourRelabelPoint point)
        (hgauge _ hpsd2 hdata2))
  · -- three relabelings
    subst h125
    obtain ⟨hpsd1, hdata1⟩ := hstep point _ hpsd hdata
    rw [show (({1, 2, 5} : Finset (Fin 6)).image kFourEdgeCycle)
        = ({0, 2, 4} : Finset (Fin 6)) from by decide] at hpsd1 hdata1
    obtain ⟨hpsd2, hdata2⟩ := hstep (kFourRelabelPoint point) _ hpsd1 hdata1
    rw [show (({0, 2, 4} : Finset (Fin 6)).image kFourEdgeCycle)
        = ({0, 1, 3} : Finset (Fin 6)) from by decide] at hpsd2 hdata2
    obtain ⟨hpsd3, hdata3⟩ := hstep
      (kFourRelabelPoint (kFourRelabelPoint point)) _ hpsd2 hdata2
    rw [show (({0, 1, 3} : Finset (Fin 6)).image kFourEdgeCycle)
        = ({3, 4, 5} : Finset (Fin 6)) from by decide] at hpsd3 hdata3
    exact kFourStrict_pullback point
      (kFourStrict_pullback (kFourRelabelPoint point)
        (kFourStrict_pullback
          (kFourRelabelPoint (kFourRelabelPoint point))
          (hgauge _ hpsd3 hdata3)))
  · -- already the gauge wall
    subst h345
    exact hgauge point hpsd hdata

end Gtz
