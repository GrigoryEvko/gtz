import Gtz.Design.PivotEndpointStarCore
import Gtz.Design.StarWallTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace Gtz

open Matrix

structure KFourSignedKernelEndpointData
    (coefficient : Fin 6 → ℝ) (probe : Fin 3 → ℝ)
    (tree : Finset (Fin 6)) (added : Fin 6) : Prop where
  tree_mem : tree ∈ kFourSpanningTreeList
  added_notMem : added ∉ tree
  coefficient_pos : ∀ label ∈ tree, 0 < coefficient label
  coefficient_neg : ∀ label ∉ tree, coefficient label < 0
  probe_ne : probe ≠ 0
  kernel : (∑ label, coefficient label • atomMatrix (kFourDirection label))
    *ᵥ probe = 0
  unique_zero : ∀ label, kFourDirection label ⬝ᵥ probe = 0 ↔ label = added
  form_posSemidef :
    (∑ label, coefficient label • atomMatrix (kFourDirection label)).PosSemidef

theorem kFourTreeList_image_cycle :
    ∀ tree ∈ kFourSpanningTreeList,
      tree.image kFourEdgeCycle ∈ kFourSpanningTreeList := by
  decide

theorem kFourStarList_image_cycle_iff (tree : Finset (Fin 6)) :
    tree.image kFourEdgeCycle ∈ kFourStarList ↔ tree ∈ kFourStarList := by
  revert tree
  decide

theorem kFourOppositeEdge_cycle (edge : Fin 6) :
    kFourOppositeEdge (kFourEdgeCycle edge) =
      kFourEdgeCycle (kFourOppositeEdge edge) := by
  fin_cases edge <;> rfl

theorem kFourEdgeCycle_mem_image_iff_inv (tree : Finset (Fin 6))
    (label : Fin 6) :
    label ∈ tree.image kFourEdgeCycle ↔ kFourEdgeCycleInv label ∈ tree := by
  constructor
  · intro h
    obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp h
    have : source = kFourEdgeCycleInv label := by
      rw [← hsourceEq, kFourEdgeCycleInv_comp]
    rwa [← this]
  · intro h
    have himage := Finset.mem_image_of_mem kFourEdgeCycle h
    simpa [kFourEdgeCycle_comp] using himage

theorem kFourEdgeCycleInv_eq_iff (left right : Fin 6) :
    kFourEdgeCycleInv left = right ↔ left = kFourEdgeCycle right := by
  constructor
  · intro h
    rw [← h, kFourEdgeCycle_comp]
  · intro h
    rw [h, kFourEdgeCycleInv_comp]

def kFourCycleCoefficient (coefficient : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun label => coefficient (kFourEdgeCycleInv label)

def kFourCycleProbe (probe : Fin 3 → ℝ) : Fin 3 → ℝ :=
  kFourCycleInvᵀ *ᵥ probe

theorem kFour_coeffSum_cycle (coefficient : Fin 6 → ℝ) :
    (∑ label, kFourCycleCoefficient coefficient label •
        atomMatrix (kFourDirection label))
      = kFourCycleMatrix
          * (∑ label, coefficient label • atomMatrix (kFourDirection label))
          * kFourCycleMatrixᵀ := by
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [← Equiv.sum_comp kFourEdgeCycleEquiv
    (fun label => kFourCycleCoefficient coefficient label •
      atomMatrix (kFourDirection label))]
  refine Finset.sum_congr rfl fun label _ => ?_
  show kFourCycleCoefficient coefficient (kFourEdgeCycle label) •
      atomMatrix (kFourDirection (kFourEdgeCycle label)) = _
  rw [show kFourCycleCoefficient coefficient (kFourEdgeCycle label)
      = coefficient label by simp [kFourCycleCoefficient,
        kFourEdgeCycleInv_comp],
    atomMatrix_direction_image, Matrix.mul_smul, Matrix.smul_mul]

theorem kFourDirection_cycle_pairing_zero_iff_source (probe : Fin 3 → ℝ)
    (source : Fin 6) :
    kFourDirection (kFourEdgeCycle source) ⬝ᵥ kFourCycleProbe probe = 0 ↔
      kFourDirection source ⬝ᵥ probe = 0 := by
  have hpair : (kFourCycleMatrix *ᵥ kFourDirection source) ⬝ᵥ
      kFourCycleProbe probe = kFourDirection source ⬝ᵥ probe := by
    rw [dotProduct_comm, kFourCycleProbe, kFourCycle_pairing,
      dotProduct_comm]
  rcases fin_six_cases source with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show kFourDirection (kFourEdgeCycle 0) =
        -(kFourCycleMatrix *ᵥ kFourDirection 0) by
      rw [kFourEdgeCycle, kFourCycle_dir_zero, neg_neg],
      neg_dotProduct, hpair]
    simp
  · rw [show kFourDirection (kFourEdgeCycle 1) =
        -(kFourCycleMatrix *ᵥ kFourDirection 1) by
      rw [kFourEdgeCycle, kFourCycle_dir_one, neg_neg],
      neg_dotProduct, hpair]
    simp
  · rw [show kFourDirection (kFourEdgeCycle 2) =
        kFourCycleMatrix *ᵥ kFourDirection 2 by
      rw [kFourEdgeCycle, kFourCycle_dir_two], hpair]
  · rw [show kFourDirection (kFourEdgeCycle 3) =
        -(kFourCycleMatrix *ᵥ kFourDirection 3) by
      rw [kFourEdgeCycle, kFourCycle_dir_three, neg_neg],
      neg_dotProduct, hpair]
    simp
  · rw [show kFourDirection (kFourEdgeCycle 4) =
        kFourCycleMatrix *ᵥ kFourDirection 4 by
      rw [kFourEdgeCycle, kFourCycle_dir_four], hpair]
  · rw [show kFourDirection (kFourEdgeCycle 5) =
        kFourCycleMatrix *ᵥ kFourDirection 5 by
      rw [kFourEdgeCycle, kFourCycle_dir_five], hpair]

theorem kFourDirection_cycle_pairing_zero_iff (probe : Fin 3 → ℝ)
    (label : Fin 6) :
    kFourDirection label ⬝ᵥ kFourCycleProbe probe = 0 ↔
      kFourDirection (kFourEdgeCycleInv label) ⬝ᵥ probe = 0 := by
  have h := kFourDirection_cycle_pairing_zero_iff_source probe
    (kFourEdgeCycleInv label)
  rwa [kFourEdgeCycle_comp] at h

theorem KFourSignedKernelEndpointData.cycle
    {coefficient : Fin 6 → ℝ} {probe : Fin 3 → ℝ}
    {tree : Finset (Fin 6)} {added : Fin 6}
    (data : KFourSignedKernelEndpointData coefficient probe tree added) :
    KFourSignedKernelEndpointData (kFourCycleCoefficient coefficient)
      (kFourCycleProbe probe) (tree.image kFourEdgeCycle)
        (kFourEdgeCycle added) where
  tree_mem := kFourTreeList_image_cycle tree data.tree_mem
  added_notMem := by
    rw [kFourEdgeCycle_mem_image_iff]
    exact data.added_notMem
  coefficient_pos := by
    intro label hmem
    exact data.coefficient_pos _
      ((kFourEdgeCycle_mem_image_iff_inv tree label).mp hmem)
  coefficient_neg := by
    intro label hnot
    exact data.coefficient_neg _ fun hmem =>
      hnot ((kFourEdgeCycle_mem_image_iff_inv tree label).mpr hmem)
  probe_ne := by
    intro hzero
    apply data.probe_ne
    have := congrArg (fun vector => kFourCycleMatrixᵀ *ᵥ vector) hzero
    simpa [kFourCycleProbe, Matrix.mulVec_mulVec,
      kFourCycleMatrixT_mul_invT, Matrix.one_mulVec, Matrix.mulVec_zero]
      using this
  kernel := by
    rw [kFour_coeffSum_cycle]
    have hcancel : kFourCycleMatrixᵀ *ᵥ kFourCycleProbe probe = probe := by
      exact kFourCycleInvT_cancel probe
    calc
      (kFourCycleMatrix
          * (∑ label, coefficient label • atomMatrix (kFourDirection label))
          * kFourCycleMatrixᵀ) *ᵥ kFourCycleProbe probe
          = kFourCycleMatrix *ᵥ
              ((∑ label, coefficient label • atomMatrix (kFourDirection label))
                *ᵥ (kFourCycleMatrixᵀ *ᵥ kFourCycleProbe probe)) := by
              simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = kFourCycleMatrix *ᵥ
              ((∑ label, coefficient label • atomMatrix (kFourDirection label))
                *ᵥ probe) := by rw [hcancel]
      _ = 0 := by rw [data.kernel, Matrix.mulVec_zero]
  unique_zero := by
    intro label
    rw [kFourDirection_cycle_pairing_zero_iff, data.unique_zero,
      kFourEdgeCycleInv_eq_iff]
  form_posSemidef := by
    rw [kFour_coeffSum_cycle]
    have hconj : kFourCycleMatrixᴴ = kFourCycleMatrixᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [← hconj]
    exact data.form_posSemidef.mul_mul_conjTranspose_same kFourCycleMatrix

theorem KFourSignedKernelEndpointData.classified_of_cycle
    {coefficient : Fin 6 → ℝ} {probe : Fin 3 → ℝ}
    {tree : Finset (Fin 6)} {added : Fin 6}
    (_data : KFourSignedKernelEndpointData coefficient probe tree added)
    (hclassified : tree.image kFourEdgeCycle ∈ kFourStarList ∧
      kFourOppositeEdge (kFourEdgeCycle added) ∈
        tree.image kFourEdgeCycle) :
    tree ∈ kFourStarList ∧ kFourOppositeEdge added ∈ tree := by
  refine ⟨(kFourStarList_image_cycle_iff tree).mp hclassified.1, ?_⟩
  have himage : kFourEdgeCycle (kFourOppositeEdge added) ∈
      tree.image kFourEdgeCycle := by
    rw [← kFourOppositeEdge_cycle]
    exact hclassified.2
  exact (kFourEdgeCycle_mem_image_iff tree _).mp himage

/-! Reflection swapping the grounded and first K4 vertices. -/

def kFourEdgeReflection : Fin 6 → Fin 6
  | 0 => 4
  | 1 => 5
  | 2 => 2
  | 3 => 3
  | 4 => 0
  | 5 => 1

def kFourEdgeReflectionEquiv : Equiv.Perm (Fin 6) :=
  ⟨kFourEdgeReflection, kFourEdgeReflection, by decide, by decide⟩

theorem kFourEdgeReflection_involutive (edge : Fin 6) :
    kFourEdgeReflection (kFourEdgeReflection edge) = edge := by
  fin_cases edge <;> rfl

theorem kFourEdgeReflection_injective : Function.Injective kFourEdgeReflection :=
  Function.LeftInverse.injective kFourEdgeReflection_involutive

def kFourReflectionMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, -1, -1; 0, 1, 0; 0, 0, 1]

theorem kFourReflectionMatrix_mul_self :
    kFourReflectionMatrix * kFourReflectionMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kFourReflectionMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem kFourReflectionMatrixT_mul_selfT :
    kFourReflectionMatrixᵀ * kFourReflectionMatrixᵀ = 1 := by
  rw [← Matrix.transpose_mul, kFourReflectionMatrix_mul_self,
    Matrix.transpose_one]

theorem kFourReflection_dir (edge : Fin 6) :
    kFourReflectionMatrix *ᵥ kFourDirection edge =
      if edge = 2 then kFourDirection (kFourEdgeReflection edge)
      else -kFourDirection (kFourEdgeReflection edge) := by
  fin_cases edge <;>
    funext i <;> fin_cases i <;>
    simp [kFourReflectionMatrix, kFourDirection, kFourEdgeReflection,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem atomMatrix_direction_reflection (edge : Fin 6) :
    atomMatrix (kFourDirection (kFourEdgeReflection edge))
      = kFourReflectionMatrix * atomMatrix (kFourDirection edge)
          * kFourReflectionMatrixᵀ := by
  by_cases htwo : edge = 2
  · subst edge
    have hdir := kFourReflection_dir 2
    simp at hdir
    rw [← hdir, atomMatrix_mulVec_conj]
  · have hdir := kFourReflection_dir edge
    simp [htwo] at hdir
    have himage : kFourDirection (kFourEdgeReflection edge) =
        -(kFourReflectionMatrix *ᵥ kFourDirection edge) := by
      rw [hdir, neg_neg]
    rw [himage, atomMatrix_neg, atomMatrix_mulVec_conj]

theorem kFourTreeList_image_reflection :
    ∀ tree ∈ kFourSpanningTreeList,
      tree.image kFourEdgeReflection ∈ kFourSpanningTreeList := by
  decide

theorem kFourStarList_image_reflection_iff (tree : Finset (Fin 6)) :
    tree.image kFourEdgeReflection ∈ kFourStarList ↔ tree ∈ kFourStarList := by
  revert tree
  decide

theorem kFourOppositeEdge_reflection (edge : Fin 6) :
    kFourOppositeEdge (kFourEdgeReflection edge) =
      kFourEdgeReflection (kFourOppositeEdge edge) := by
  fin_cases edge <;> rfl

theorem kFourEdgeReflection_mem_image_iff (tree : Finset (Fin 6))
    (edge : Fin 6) :
    kFourEdgeReflection edge ∈ tree.image kFourEdgeReflection ↔ edge ∈ tree := by
  constructor
  · intro h
    obtain ⟨source, hsource, heq⟩ := Finset.mem_image.mp h
    exact (kFourEdgeReflection_injective heq).symm ▸ hsource
  · exact Finset.mem_image_of_mem _

theorem kFourEdgeReflection_mem_image_iff_inv (tree : Finset (Fin 6))
    (label : Fin 6) :
    label ∈ tree.image kFourEdgeReflection ↔
      kFourEdgeReflection label ∈ tree := by
  constructor
  · intro h
    obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp h
    have : source = kFourEdgeReflection label := by
      rw [← hsourceEq, kFourEdgeReflection_involutive]
    rwa [← this]
  · intro h
    have himage := Finset.mem_image_of_mem kFourEdgeReflection h
    simpa [kFourEdgeReflection_involutive] using himage

def kFourReflectionCoefficient (coefficient : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun label => coefficient (kFourEdgeReflection label)

def kFourReflectionProbe (probe : Fin 3 → ℝ) : Fin 3 → ℝ :=
  kFourReflectionMatrixᵀ *ᵥ probe

theorem kFour_coeffSum_reflection (coefficient : Fin 6 → ℝ) :
    (∑ label, kFourReflectionCoefficient coefficient label •
        atomMatrix (kFourDirection label))
      = kFourReflectionMatrix
          * (∑ label, coefficient label • atomMatrix (kFourDirection label))
          * kFourReflectionMatrixᵀ := by
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [← Equiv.sum_comp kFourEdgeReflectionEquiv
    (fun label => kFourReflectionCoefficient coefficient label •
      atomMatrix (kFourDirection label))]
  refine Finset.sum_congr rfl fun label _ => ?_
  show kFourReflectionCoefficient coefficient (kFourEdgeReflection label) •
      atomMatrix (kFourDirection (kFourEdgeReflection label)) = _
  rw [show kFourReflectionCoefficient coefficient (kFourEdgeReflection label)
      = coefficient label by simp [kFourReflectionCoefficient,
        kFourEdgeReflection_involutive],
    atomMatrix_direction_reflection, Matrix.mul_smul, Matrix.smul_mul]

theorem kFourReflection_pairing (left right : Fin 3 → ℝ) :
    (kFourReflectionMatrixᵀ *ᵥ left) ⬝ᵥ
        (kFourReflectionMatrix *ᵥ right) = left ⬝ᵥ right := by
  rw [dotProduct_mulVec_transpose kFourReflectionMatrix left
      (kFourReflectionMatrix *ᵥ right),
    Matrix.mulVec_mulVec, kFourReflectionMatrix_mul_self,
    Matrix.one_mulVec]

theorem kFourDirection_reflection_pairing_zero_iff_source
    (probe : Fin 3 → ℝ) (source : Fin 6) :
    kFourDirection (kFourEdgeReflection source) ⬝ᵥ
        kFourReflectionProbe probe = 0 ↔
      kFourDirection source ⬝ᵥ probe = 0 := by
  have hpair : (kFourReflectionMatrix *ᵥ kFourDirection source) ⬝ᵥ
      kFourReflectionProbe probe = kFourDirection source ⬝ᵥ probe := by
    rw [dotProduct_comm, kFourReflectionProbe, kFourReflection_pairing,
      dotProduct_comm]
  by_cases htwo : source = 2
  · subst source
    have hdir := kFourReflection_dir 2
    simp at hdir
    rw [← hdir, hpair]
  · have hdir := kFourReflection_dir source
    simp [htwo] at hdir
    rw [show kFourDirection (kFourEdgeReflection source) =
        -(kFourReflectionMatrix *ᵥ kFourDirection source) by
      rw [hdir, neg_neg], neg_dotProduct, hpair]
    simp

theorem kFourDirection_reflection_pairing_zero_iff (probe : Fin 3 → ℝ)
    (label : Fin 6) :
    kFourDirection label ⬝ᵥ kFourReflectionProbe probe = 0 ↔
      kFourDirection (kFourEdgeReflection label) ⬝ᵥ probe = 0 := by
  have h := kFourDirection_reflection_pairing_zero_iff_source probe
    (kFourEdgeReflection label)
  rwa [kFourEdgeReflection_involutive] at h

theorem KFourSignedKernelEndpointData.reflect
    {coefficient : Fin 6 → ℝ} {probe : Fin 3 → ℝ}
    {tree : Finset (Fin 6)} {added : Fin 6}
    (data : KFourSignedKernelEndpointData coefficient probe tree added) :
    KFourSignedKernelEndpointData (kFourReflectionCoefficient coefficient)
      (kFourReflectionProbe probe) (tree.image kFourEdgeReflection)
        (kFourEdgeReflection added) where
  tree_mem := kFourTreeList_image_reflection tree data.tree_mem
  added_notMem := by
    rw [kFourEdgeReflection_mem_image_iff]
    exact data.added_notMem
  coefficient_pos := by
    intro label hmem
    exact data.coefficient_pos _
      ((kFourEdgeReflection_mem_image_iff_inv tree label).mp hmem)
  coefficient_neg := by
    intro label hnot
    exact data.coefficient_neg _ fun hmem =>
      hnot ((kFourEdgeReflection_mem_image_iff_inv tree label).mpr hmem)
  probe_ne := by
    intro hzero
    apply data.probe_ne
    have := congrArg (fun vector => kFourReflectionMatrixᵀ *ᵥ vector) hzero
    simpa [kFourReflectionProbe, Matrix.mulVec_mulVec,
      kFourReflectionMatrixT_mul_selfT, Matrix.one_mulVec,
      Matrix.mulVec_zero] using this
  kernel := by
    rw [kFour_coeffSum_reflection]
    calc
      (kFourReflectionMatrix
          * (∑ label, coefficient label • atomMatrix (kFourDirection label))
          * kFourReflectionMatrixᵀ) *ᵥ kFourReflectionProbe probe
          = kFourReflectionMatrix *ᵥ
              ((∑ label, coefficient label • atomMatrix (kFourDirection label))
                *ᵥ (kFourReflectionMatrixᵀ *ᵥ
                  kFourReflectionProbe probe)) := by
              simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = kFourReflectionMatrix *ᵥ
              ((∑ label, coefficient label • atomMatrix (kFourDirection label))
                *ᵥ probe) := by
              simp [kFourReflectionProbe, Matrix.mulVec_mulVec,
                kFourReflectionMatrixT_mul_selfT]
      _ = 0 := by rw [data.kernel, Matrix.mulVec_zero]
  unique_zero := by
    intro label
    rw [kFourDirection_reflection_pairing_zero_iff, data.unique_zero]
    constructor
    · intro h
      rw [← h, kFourEdgeReflection_involutive]
    · intro h
      rw [h, kFourEdgeReflection_involutive]
  form_posSemidef := by
    rw [kFour_coeffSum_reflection]
    have hconj : kFourReflectionMatrixᴴ = kFourReflectionMatrixᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [← hconj]
    exact data.form_posSemidef.mul_mul_conjTranspose_same kFourReflectionMatrix

theorem KFourSignedKernelEndpointData.classified_of_reflect
    {coefficient : Fin 6 → ℝ} {probe : Fin 3 → ℝ}
    {tree : Finset (Fin 6)} {added : Fin 6}
    (_data : KFourSignedKernelEndpointData coefficient probe tree added)
    (hclassified : tree.image kFourEdgeReflection ∈ kFourStarList ∧
      kFourOppositeEdge (kFourEdgeReflection added) ∈
        tree.image kFourEdgeReflection) :
    tree ∈ kFourStarList ∧ kFourOppositeEdge added ∈ tree := by
  refine ⟨(kFourStarList_image_reflection_iff tree).mp hclassified.1, ?_⟩
  have himage : kFourEdgeReflection (kFourOppositeEdge added) ∈
      tree.image kFourEdgeReflection := by
    rw [← kFourOppositeEdge_reflection]
    exact hclassified.2
  exact (kFourEdgeReflection_mem_image_iff tree _).mp himage

theorem KFourSignedKernelEndpointData.classify_added_five
    {coefficient : Fin 6 → ℝ} {probe : Fin 3 → ℝ}
    {tree : Finset (Fin 6)} {added : Fin 6}
    (data : KFourSignedKernelEndpointData coefficient probe tree added)
    (hadded : added = 5) :
    tree ∈ kFourStarList ∧ kFourOppositeEdge added ∈ tree := by
  subst added
  have htree := kFour_tree_star_of_addedFive coefficient probe tree
    data.tree_mem data.added_notMem data.coefficient_pos data.coefficient_neg
      data.probe_ne data.kernel data.unique_zero data.form_posSemidef
  rcases htree with htree | htree <;> subst tree <;>
    simp [kFourStarList, kFourOppositeEdge]

theorem KFourSignedKernelEndpointData.classify
    {coefficient : Fin 6 → ℝ} {probe : Fin 3 → ℝ}
    {tree : Finset (Fin 6)} {added : Fin 6}
    (data : KFourSignedKernelEndpointData coefficient probe tree added) :
    tree ∈ kFourStarList ∧ kFourOppositeEdge added ∈ tree := by
  rcases fin_six_cases added with rfl | rfl | rfl | rfl | rfl | rfl
  · apply data.classified_of_cycle
    apply data.cycle.classified_of_cycle
    exact data.cycle.cycle.classify_added_five rfl
  · apply data.classified_of_reflect
    exact data.reflect.classify_added_five rfl
  · apply data.classified_of_cycle
    apply data.cycle.classified_of_cycle
    apply data.cycle.cycle.classified_of_cycle
    exact data.cycle.cycle.cycle.classify_added_five rfl
  · apply data.classified_of_cycle
    exact data.cycle.classify_added_five rfl
  · apply data.classified_of_cycle
    apply data.cycle.classified_of_reflect
    exact data.cycle.reflect.classify_added_five rfl
  · exact data.classify_added_five rfl

/-! ## The chart endpoint specialization -/

/-- **THE PRICED ENDPOINT IS A STAR.**  At an exact one-edge contraction
endpoint, the old weak tree is forced to be a vertex star, and it contains the
edge opposite the inserted contraction edge.

The proof is label-free.  It reads the old tree gap as a signed K4 Laplacian,
uses the exact unique-zero law from the contraction layer, and transports the
canonical edge-`5` classification through two explicit K4 automorphisms. -/
theorem KFourPivotWallPricedContractedEndpointData.tree_star_and_opposite_mem
    {point : DirectionChartPoint 6} {tree : Finset (Fin 6)}
    (data : KFourPivotWallPricedContractedEndpointData point tree)
    (htree : tree ∈ kFourSpanningTreeList)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef) :
    tree ∈ kFourStarList ∧
      kFourOppositeEdge data.endpoint.endpoint.added ∈ tree := by
  let coefficient := chartCoeff point.mass point.weight tree
  have haddedNotTree : data.endpoint.endpoint.added ∉ tree := by
    intro hmem
    exact data.endpoint.endpoint.added_notMem
      (Finset.mem_insert_of_mem hmem)
  let raw : KFourSignedKernelEndpointData coefficient
      data.endpoint.tightDirection tree data.endpoint.endpoint.added :=
    { tree_mem := htree
      added_notMem := haddedNotTree
      coefficient_pos := by
        intro label hmem
        exact chartCoeff_pos_of_mem point hmem
      coefficient_neg := by
        intro label hnot
        exact chartCoeff_neg_of_not_mem point hnot
      probe_ne := data.endpoint.tightDirection_ne
      kernel := by
        rw [← directionChartGap_eq_coeff_sum]
        exact data.endpoint.tree_kernel
      unique_zero := data.orthogonal_iff_eq_added
      form_posSemidef := by
        rw [← directionChartGap_eq_coeff_sum]
        exact hgap }
  exact raw.classify

end Gtz
