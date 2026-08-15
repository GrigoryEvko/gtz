import Gtz.Design.PivotEndpointOrthogonality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The priced pivot endpoint contracts exactly one K4 edge

`PivotEndpointOrthogonality` proves that the edge inserted at the priced
endpoint is orthogonal to the old tight direction.  This module proves that it
is the only such edge.

The proof is finite but structural.  Regard a vector in `R^3` as a potential
on the three non-ground vertices of `K4`.  A zero reading of a chart direction
means that the two endpoint potentials agree.  Once one edge has zero reading,
a second zero edge is either

* adjacent, in which case transitivity gives a zero-voltage triangle; or
* opposite, in which case the kernel equations force the four cross-edge
  coefficients into an alternating checkerboard.

The first case is incompatible with the nonzero sign of every chart
coefficient.  In the second case the determinant of the positive-definite
pointer window is a strictly negative product.  Hence neither case occurs.
The endpoint therefore descends to a genuine one-edge contraction rather than
an unspecified orthogonality locus.
-/

namespace Gtz

open Matrix

/-! ## K4 voltage readings -/

/-- The edge opposite a K4 chart label. -/
def kFourOppositeEdge : Fin 6 → Fin 6
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0

/-- Opposite-edge pairing is an involution. -/
theorem kFourOppositeEdge_involutive (edge : Fin 6) :
    kFourOppositeEdge (kFourOppositeEdge edge) = edge := by
  rcases fin_six_cases edge with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- An edge is never opposite to itself. -/
theorem kFourOppositeEdge_ne (edge : Fin 6) :
    kFourOppositeEdge edge ≠ edge := by
  rcases fin_six_cases edge with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The six K4 edge readings are the six pairwise potential differences among
the three coordinates and the grounded fourth coordinate. -/
theorem kFourDirection_readings (probe : Fin 3 → ℝ) :
    kFourDirection 0 ⬝ᵥ probe = probe 0 - probe 1 ∧
    kFourDirection 1 ⬝ᵥ probe = probe 0 - probe 2 ∧
    kFourDirection 2 ⬝ᵥ probe = probe 1 - probe 2 ∧
    kFourDirection 3 ⬝ᵥ probe = probe 0 ∧
    kFourDirection 4 ⬝ᵥ probe = probe 1 ∧
    kFourDirection 5 ⬝ᵥ probe = probe 2 := by
  simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  simp

/-! ## Finite zero-voltage classification -/

/-- The four ways a K4 potential can be constant on three vertices. -/
def KFourZeroTriangle (probe : Fin 3 → ℝ) : Prop :=
  (kFourDirection 0 ⬝ᵥ probe = 0 ∧
      kFourDirection 1 ⬝ᵥ probe = 0 ∧
      kFourDirection 2 ⬝ᵥ probe = 0) ∨
  (kFourDirection 0 ⬝ᵥ probe = 0 ∧
      kFourDirection 3 ⬝ᵥ probe = 0 ∧
      kFourDirection 4 ⬝ᵥ probe = 0) ∨
  (kFourDirection 1 ⬝ᵥ probe = 0 ∧
      kFourDirection 3 ⬝ᵥ probe = 0 ∧
      kFourDirection 5 ⬝ᵥ probe = 0) ∨
  (kFourDirection 2 ⬝ᵥ probe = 0 ∧
      kFourDirection 4 ⬝ᵥ probe = 0 ∧
      kFourDirection 5 ⬝ᵥ probe = 0)

/-- Once one K4 edge has zero voltage, any additional zero-voltage edge is
either its opposite or belongs with it to one of the four K4 triangles. -/
theorem kFour_second_zero_is_opposite_or_triangle (probe : Fin 3 → ℝ)
    (_hprobe : probe ≠ 0) (edge other : Fin 6)
    (hedge : kFourDirection edge ⬝ᵥ probe = 0)
    (hother : kFourDirection other ⬝ᵥ probe = 0)
    (hne : other ≠ edge) :
    other = kFourOppositeEdge edge ∨ KFourZeroTriangle probe := by
  rcases fin_six_cases edge with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_six_cases other with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [KFourZeroTriangle, kFourOppositeEdge, kFourDirection, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      at hedge hother hne ⊢
  all_goals aesop (add safe (by linarith))

/-! ## A zero-voltage triangle is impossible -/

/-- The coordinate Kirchhoff equations for a K4 coefficient combination. -/
theorem kFour_coeffSum_kernel_equations (coefficient : Fin 6 → ℝ)
    (probe : Fin 3 → ℝ)
    (hkernel : (∑ label, coefficient label • atomMatrix (kFourDirection label))
      *ᵥ probe = 0) :
    coefficient 0 * (probe 0 - probe 1)
        + coefficient 1 * (probe 0 - probe 2)
        + coefficient 3 * probe 0 = 0 ∧
    -(coefficient 0 * (probe 0 - probe 1))
        + coefficient 2 * (probe 1 - probe 2)
        + coefficient 4 * probe 1 = 0 ∧
    -(coefficient 1 * (probe 0 - probe 2))
        - coefficient 2 * (probe 1 - probe 2)
        + coefficient 5 * probe 2 = 0 := by
  have h0 := congrFun hkernel 0
  have h1 := congrFun hkernel 1
  have h2 := congrFun hkernel 2
  simp [Matrix.mulVec, atomMatrix, kFourDirection, Fin.sum_univ_six,
    dotProduct, Fin.sum_univ_three] at h0 h1 h2
  exact ⟨by ring_nf at h0 ⊢; exact h0,
    by ring_nf at h1 ⊢; exact h1,
    by ring_nf at h2 ⊢; exact h2⟩

/-- A nonzero K4 kernel potential cannot be constant on a triangle when all
six edge coefficients are nonzero.  At each vertex of the triangle, the sole
edge leaving it would otherwise carry zero current with nonzero voltage. -/
theorem kFour_no_zero_triangle_of_coeffSum_kernel
    (coefficient : Fin 6 → ℝ) (probe : Fin 3 → ℝ)
    (hcoefficient : ∀ label, coefficient label ≠ 0)
    (hprobe : probe ≠ 0)
    (hkernel : (∑ label, coefficient label • atomMatrix (kFourDirection label))
      *ᵥ probe = 0)
    (hzero : KFourZeroTriangle probe) : False := by
  have heq := kFour_coeffSum_kernel_equations coefficient probe hkernel
  simp [KFourZeroTriangle, kFourDirection, dotProduct,
    Fin.sum_univ_three] at hzero
  rcases hzero with hzero | hzero | hzero | hzero
  · have hp1 : probe 1 = probe 0 := by linarith [hzero.1]
    have hp2 : probe 2 = probe 0 := by linarith [hzero.2.1]
    rw [hp1, hp2] at heq
    have hproduct : coefficient 3 * probe 0 = 0 := by
      nlinarith [heq.1]
    have hp0 : probe 0 = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left (hcoefficient 3)
    apply hprobe
    funext index
    rcases fin_three_cases index with rfl | rfl | rfl <;> simp [hp0, hp1, hp2]
  · have hp0 : probe 0 = 0 := hzero.2.1
    have hp1 : probe 1 = 0 := hzero.2.2
    rw [hp0, hp1] at heq
    have hproduct : coefficient 1 * probe 2 = 0 := by
      nlinarith [heq.1]
    have hp2 : probe 2 = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left (hcoefficient 1)
    apply hprobe
    funext index
    rcases fin_three_cases index with rfl | rfl | rfl <;> simp [hp0, hp1, hp2]
  · have hp0 : probe 0 = 0 := hzero.2.1
    have hp2 : probe 2 = 0 := hzero.2.2
    rw [hp0, hp2] at heq
    have hproduct : coefficient 0 * probe 1 = 0 := by
      nlinarith [heq.1]
    have hp1 : probe 1 = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left (hcoefficient 0)
    apply hprobe
    funext index
    rcases fin_three_cases index with rfl | rfl | rfl <;> simp [hp0, hp1, hp2]
  · have hp1 : probe 1 = 0 := hzero.2.1
    have hp2 : probe 2 = 0 := hzero.2.2
    rw [hp1, hp2] at heq
    have hproduct : coefficient 0 * probe 0 = 0 := by
      nlinarith [heq.2.1]
    have hp0 : probe 0 = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left (hcoefficient 0)
    apply hprobe
    funext index
    rcases fin_three_cases index with rfl | rfl | rfl <;> simp [hp0, hp1, hp2]

/-! ## The opposite-pair checkerboard -/

/-- The coefficient pattern forced when the kernel potential is constant on
two opposite vertex pairs.  The two remaining opposite edge pairs carry
constant coefficients of opposite signs. -/
def KFourOppositeCheckerboard (coefficient : Fin 6 → ℝ) (edge : Fin 6) : Prop :=
  (((edge = 0 ∨ edge = 5) ∧
      coefficient 1 = coefficient 4 ∧
      coefficient 2 = coefficient 3 ∧
      coefficient 1 = -coefficient 2) ∨
   ((edge = 1 ∨ edge = 4) ∧
      coefficient 0 = coefficient 5 ∧
      coefficient 2 = coefficient 3 ∧
      coefficient 0 = -coefficient 2) ∨
   ((edge = 2 ∨ edge = 3) ∧
      coefficient 0 = coefficient 5 ∧
      coefficient 1 = coefficient 4 ∧
      coefficient 0 = -coefficient 1))

/-- The Kirchhoff equations force the checkerboard pattern on every
opposite-zero potential. -/
theorem kFour_opposite_checkerboard_of_coeffSum_kernel
    (coefficient : Fin 6 → ℝ) (probe : Fin 3 → ℝ) (edge : Fin 6)
    (hprobe : probe ≠ 0)
    (hkernel : (∑ label, coefficient label • atomMatrix (kFourDirection label))
      *ᵥ probe = 0)
    (hedge : kFourDirection edge ⬝ᵥ probe = 0)
    (hopposite : kFourDirection (kFourOppositeEdge edge) ⬝ᵥ probe = 0) :
    KFourOppositeCheckerboard coefficient edge := by
  have heq := kFour_coeffSum_kernel_equations coefficient probe hkernel
  have probe_eq_zero (h0 : probe 0 = 0) (h1 : probe 1 = 0)
      (h2 : probe 2 = 0) : probe = 0 := by
    funext index
    rcases fin_three_cases index with rfl | rfl | rfl <;> simp_all
  rcases fin_six_cases edge with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [kFourOppositeEdge, kFourDirection, dotProduct,
      Fin.sum_univ_three] at hedge hopposite
  · have hp : probe 0 ≠ 0 := by
      intro hp
      apply hprobe
      apply probe_eq_zero <;> linarith only [hp, hedge, hopposite]
    have hy : probe 1 = probe 0 := by linarith [hedge]
    have hz : probe 2 = 0 := hopposite
    have h13 : coefficient 1 + coefficient 3 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 1 + coefficient 3) * probe 0 = 0 by
          calc
            (coefficient 1 + coefficient 3) * probe 0
                = coefficient 0 * (probe 0 - probe 1)
                    + coefficient 1 * (probe 0 - probe 2)
                    + coefficient 3 * probe 0 := by rw [hy, hz]; ring
            _ = 0 := heq.1)).resolve_right hp
    have h24 : coefficient 2 + coefficient 4 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 2 + coefficient 4) * probe 0 = 0 by
          calc
            (coefficient 2 + coefficient 4) * probe 0
                = -(coefficient 0 * (probe 0 - probe 1))
                    + coefficient 2 * (probe 1 - probe 2)
                    + coefficient 4 * probe 1 := by rw [hy, hz]; ring
            _ = 0 := heq.2.1)).resolve_right hp
    have h12 : coefficient 1 + coefficient 2 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 1 + coefficient 2) * probe 0 = 0 by
          calc
            (coefficient 1 + coefficient 2) * probe 0
                = -(-(coefficient 1 * (probe 0 - probe 2))
                    - coefficient 2 * (probe 1 - probe 2)
                    + coefficient 5 * probe 2) := by rw [hy, hz]; ring
            _ = 0 := by rw [heq.2.2]; ring)).resolve_right hp
    exact Or.inl ⟨Or.inl rfl, by linarith, by linarith, by linarith⟩
  · have hp : probe 0 ≠ 0 := by
      intro hp
      apply hprobe
      apply probe_eq_zero <;> linarith only [hp, hedge, hopposite]
    have hz : probe 2 = probe 0 := by linarith [hedge]
    have hy : probe 1 = 0 := hopposite
    have h03 : coefficient 0 + coefficient 3 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 0 + coefficient 3) * probe 0 = 0 by
          calc
            (coefficient 0 + coefficient 3) * probe 0
                = coefficient 0 * (probe 0 - probe 1)
                    + coefficient 1 * (probe 0 - probe 2)
                    + coefficient 3 * probe 0 := by rw [hy, hz]; ring
            _ = 0 := heq.1)).resolve_right hp
    have h02 : coefficient 0 + coefficient 2 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 0 + coefficient 2) * probe 0 = 0 by
          calc
            (coefficient 0 + coefficient 2) * probe 0
                = -(-(coefficient 0 * (probe 0 - probe 1))
                    + coefficient 2 * (probe 1 - probe 2)
                    + coefficient 4 * probe 1) := by rw [hy, hz]; ring
            _ = 0 := by rw [heq.2.1]; ring)).resolve_right hp
    have h25 : coefficient 2 + coefficient 5 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 2 + coefficient 5) * probe 0 = 0 by
          calc
            (coefficient 2 + coefficient 5) * probe 0
                = -(coefficient 1 * (probe 0 - probe 2))
                    - coefficient 2 * (probe 1 - probe 2)
                    + coefficient 5 * probe 2 := by rw [hy, hz]; ring
            _ = 0 := heq.2.2)).resolve_right hp
    exact Or.inr (Or.inl
      ⟨Or.inl rfl, by linarith, by linarith, by linarith⟩)
  · have hp : probe 1 ≠ 0 := by
      intro hp
      apply hprobe
      apply probe_eq_zero <;> linarith only [hp, hedge, hopposite]
    have hz : probe 2 = probe 1 := by linarith [hedge]
    have hx : probe 0 = 0 := hopposite
    have h01 : coefficient 0 + coefficient 1 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 0 + coefficient 1) * probe 1 = 0 by
          calc
            (coefficient 0 + coefficient 1) * probe 1
                = -(coefficient 0 * (probe 0 - probe 1)
                    + coefficient 1 * (probe 0 - probe 2)
                    + coefficient 3 * probe 0) := by rw [hx, hz]; ring
            _ = 0 := by rw [heq.1]; ring)).resolve_right hp
    have h04 : coefficient 0 + coefficient 4 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 0 + coefficient 4) * probe 1 = 0 by
          calc
            (coefficient 0 + coefficient 4) * probe 1
                = -(coefficient 0 * (probe 0 - probe 1))
                    + coefficient 2 * (probe 1 - probe 2)
                    + coefficient 4 * probe 1 := by rw [hx, hz]; ring
            _ = 0 := heq.2.1)).resolve_right hp
    have h15 : coefficient 1 + coefficient 5 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 1 + coefficient 5) * probe 1 = 0 by
          calc
            (coefficient 1 + coefficient 5) * probe 1
                = -(coefficient 1 * (probe 0 - probe 2))
                    - coefficient 2 * (probe 1 - probe 2)
                    + coefficient 5 * probe 2 := by rw [hx, hz]; ring
            _ = 0 := heq.2.2)).resolve_right hp
    exact Or.inr (Or.inr
      ⟨Or.inl rfl, by linarith, by linarith, by linarith⟩)
  · have hp : probe 1 ≠ 0 := by
      intro hp
      apply hprobe
      apply probe_eq_zero <;> linarith only [hp, hedge, hopposite]
    have hx : probe 0 = 0 := hedge
    have hz : probe 2 = probe 1 := by linarith [hopposite]
    have h01 : coefficient 0 + coefficient 1 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 0 + coefficient 1) * probe 1 = 0 by
          calc
            (coefficient 0 + coefficient 1) * probe 1
                = -(coefficient 0 * (probe 0 - probe 1)
                    + coefficient 1 * (probe 0 - probe 2)
                    + coefficient 3 * probe 0) := by rw [hx, hz]; ring
            _ = 0 := by rw [heq.1]; ring)).resolve_right hp
    have h04 : coefficient 0 + coefficient 4 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 0 + coefficient 4) * probe 1 = 0 by
          calc
            (coefficient 0 + coefficient 4) * probe 1
                = -(coefficient 0 * (probe 0 - probe 1))
                    + coefficient 2 * (probe 1 - probe 2)
                    + coefficient 4 * probe 1 := by rw [hx, hz]; ring
            _ = 0 := heq.2.1)).resolve_right hp
    have h15 : coefficient 1 + coefficient 5 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 1 + coefficient 5) * probe 1 = 0 by
          calc
            (coefficient 1 + coefficient 5) * probe 1
                = -(coefficient 1 * (probe 0 - probe 2))
                    - coefficient 2 * (probe 1 - probe 2)
                    + coefficient 5 * probe 2 := by rw [hx, hz]; ring
            _ = 0 := heq.2.2)).resolve_right hp
    exact Or.inr (Or.inr
      ⟨Or.inr rfl, by linarith, by linarith, by linarith⟩)
  · have hp : probe 0 ≠ 0 := by
      intro hp
      apply hprobe
      apply probe_eq_zero <;> linarith only [hp, hedge, hopposite]
    have hy : probe 1 = 0 := hedge
    have hz : probe 2 = probe 0 := by linarith [hopposite]
    have h03 : coefficient 0 + coefficient 3 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 0 + coefficient 3) * probe 0 = 0 by
          calc
            (coefficient 0 + coefficient 3) * probe 0
                = coefficient 0 * (probe 0 - probe 1)
                    + coefficient 1 * (probe 0 - probe 2)
                    + coefficient 3 * probe 0 := by rw [hy, hz]; ring
            _ = 0 := heq.1)).resolve_right hp
    have h02 : coefficient 0 + coefficient 2 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 0 + coefficient 2) * probe 0 = 0 by
          calc
            (coefficient 0 + coefficient 2) * probe 0
                = -(-(coefficient 0 * (probe 0 - probe 1))
                    + coefficient 2 * (probe 1 - probe 2)
                    + coefficient 4 * probe 1) := by rw [hy, hz]; ring
            _ = 0 := by rw [heq.2.1]; ring)).resolve_right hp
    have h25 : coefficient 2 + coefficient 5 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 2 + coefficient 5) * probe 0 = 0 by
          calc
            (coefficient 2 + coefficient 5) * probe 0
                = -(coefficient 1 * (probe 0 - probe 2))
                    - coefficient 2 * (probe 1 - probe 2)
                    + coefficient 5 * probe 2 := by rw [hy, hz]; ring
            _ = 0 := heq.2.2)).resolve_right hp
    exact Or.inr (Or.inl
      ⟨Or.inr rfl, by linarith, by linarith, by linarith⟩)
  · have hp : probe 0 ≠ 0 := by
      intro hp
      apply hprobe
      apply probe_eq_zero <;> linarith only [hp, hedge, hopposite]
    have hz : probe 2 = 0 := hedge
    have hy : probe 1 = probe 0 := by linarith [hopposite]
    have h13 : coefficient 1 + coefficient 3 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 1 + coefficient 3) * probe 0 = 0 by
          calc
            (coefficient 1 + coefficient 3) * probe 0
                = coefficient 0 * (probe 0 - probe 1)
                    + coefficient 1 * (probe 0 - probe 2)
                    + coefficient 3 * probe 0 := by rw [hy, hz]; ring
            _ = 0 := heq.1)).resolve_right hp
    have h24 : coefficient 2 + coefficient 4 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 2 + coefficient 4) * probe 0 = 0 by
          calc
            (coefficient 2 + coefficient 4) * probe 0
                = -(coefficient 0 * (probe 0 - probe 1))
                    + coefficient 2 * (probe 1 - probe 2)
                    + coefficient 4 * probe 1 := by rw [hy, hz]; ring
            _ = 0 := heq.2.1)).resolve_right hp
    have h12 : coefficient 1 + coefficient 2 = 0 := by
      apply (mul_eq_zero.mp (show
        (coefficient 1 + coefficient 2) * probe 0 = 0 by
          calc
            (coefficient 1 + coefficient 2) * probe 0
                = -(-(coefficient 1 * (probe 0 - probe 2))
                    - coefficient 2 * (probe 1 - probe 2)
                    + coefficient 5 * probe 2) := by rw [hy, hz]; ring
            _ = 0 := by rw [heq.2.2]; ring)).resolve_right hp
    exact Or.inl ⟨Or.inr rfl, by linarith, by linarith, by linarith⟩

/-! ## The forbidden pointer window -/

/-- Replace the coefficient at the contracted edge by `-removedMass` and the
coefficient at the pointer by its positive window coefficient. -/
def kFourPointerWindowCoefficient (coefficient : Fin 6 → ℝ)
    (contracted pointer : Fin 6) (removedMass pointerCoefficient : ℝ) :
    Fin 6 → ℝ := fun label =>
  if label = contracted then -removedMass
  else if label = pointer then pointerCoefficient
  else coefficient label

/-- **THE NEGATIVE WINDOW FACTOR.**  Start from an opposite-pair checkerboard,
remove one of its zero-voltage edges from the selection, and insert any
nonzero-voltage pointer.  If the other zero-voltage coefficient is positive,
then the resulting K4 determinant is strictly negative.

In every one of the twenty-four labelled cases the determinant is

`-(pointerCoefficient - oldPointerCoefficient)
    * (removedMass * oppositeCoefficient + oldPointerCoefficient^2)`.
-/
theorem det_kFour_pointerWindowCoefficient_neg
    (coefficient : Fin 6 → ℝ) (contracted pointer : Fin 6)
    (removedMass pointerCoefficient : ℝ)
    (hchecker : KFourOppositeCheckerboard coefficient contracted)
    (hpointerContracted : pointer ≠ contracted)
    (hpointerOpposite : pointer ≠ kFourOppositeEdge contracted)
    (hremoved : 0 < removedMass)
    (hpointerOld : coefficient pointer < 0)
    (hpointerNew : 0 < pointerCoefficient)
    (hopposite : 0 < coefficient (kFourOppositeEdge contracted)) :
    (∑ label, kFourPointerWindowCoefficient coefficient contracted pointer
      removedMass pointerCoefficient label • atomMatrix (kFourDirection label)).det < 0 := by
  rcases hchecker with ⟨h05, h14, h23, h12⟩ |
      ⟨h14, h05, h23, h02⟩ | ⟨h23, h05, h14, h01⟩
  · have hc1 : coefficient 1 = -coefficient 2 := h12
    have hc3 : coefficient 3 = coefficient 2 := h23.symm
    have hc4 : coefficient 4 = -coefficient 2 := by linarith [h14, h12]
    rcases h05 with rfl | rfl
    all_goals
      rcases fin_six_cases pointer with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [kFourOppositeEdge] at hpointerContracted hpointerOpposite hopposite
    all_goals
      simp [kFourPointerWindowCoefficient, Fin.sum_univ_six, atomMatrix,
        Matrix.det_fin_three, kFourDirection, hc1, hc3, hc4];
      nlinarith [sq_nonneg (coefficient 0), sq_nonneg (coefficient 1),
        sq_nonneg (coefficient 2), sq_nonneg (coefficient 3),
        sq_nonneg (coefficient 4), sq_nonneg (coefficient 5),
        mul_pos hremoved hopposite]
  · have hc0 : coefficient 0 = -coefficient 2 := h02
    have hc3 : coefficient 3 = coefficient 2 := h23.symm
    have hc5 : coefficient 5 = -coefficient 2 := by linarith [h05, h02]
    rcases h14 with rfl | rfl
    all_goals
      rcases fin_six_cases pointer with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [kFourOppositeEdge] at hpointerContracted hpointerOpposite hopposite
    all_goals
      simp [kFourPointerWindowCoefficient, Fin.sum_univ_six, atomMatrix,
        Matrix.det_fin_three, kFourDirection, hc0, hc3, hc5];
      nlinarith [sq_nonneg (coefficient 0), sq_nonneg (coefficient 1),
        sq_nonneg (coefficient 2), sq_nonneg (coefficient 3),
        sq_nonneg (coefficient 4), sq_nonneg (coefficient 5),
        mul_pos hremoved hopposite]
  · have hc0 : coefficient 0 = -coefficient 1 := h01
    have hc4 : coefficient 4 = coefficient 1 := h14.symm
    have hc5 : coefficient 5 = -coefficient 1 := by linarith [h05, h01]
    rcases h23 with rfl | rfl
    all_goals
      rcases fin_six_cases pointer with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [kFourOppositeEdge] at hpointerContracted hpointerOpposite hopposite
    all_goals
      simp [kFourPointerWindowCoefficient, Fin.sum_univ_six, atomMatrix,
        Matrix.det_fin_three, kFourDirection, hc0, hc4, hc5];
      nlinarith [sq_nonneg (coefficient 0), sq_nonneg (coefficient 1),
        sq_nonneg (coefficient 2), sq_nonneg (coefficient 3),
        sq_nonneg (coefficient 4), sq_nonneg (coefficient 5),
        mul_pos hremoved hopposite]

/-- On a positive-semidefinite checkerboard the coefficient of the other
zero-voltage edge is strictly positive.  The relevant quadratic form is a
single diagonal after the cross-edge cancellation. -/
theorem kFour_opposite_coefficient_pos_of_checkerboard
    (coefficient : Fin 6 → ℝ) (contracted : Fin 6)
    (hchecker : KFourOppositeCheckerboard coefficient contracted)
    (hcoefficient : ∀ label, coefficient label ≠ 0)
    (hpsd : (∑ label, coefficient label • atomMatrix (kFourDirection label)).PosSemidef) :
    0 < coefficient (kFourOppositeEdge contracted) := by
  have hform (test : Fin 3 → ℝ) :
      0 ≤ test ⬝ᵥ
        ((∑ label, coefficient label • atomMatrix (kFourDirection label)) *ᵥ test) := by
    have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 test
    simpa [star_trivial] using this
  rcases hchecker with h05 | h14 | h23
  · rcases h05.1 with rfl | rfl
    · have hnonneg := hform ![0, 0, 1]
      simp [Fin.sum_univ_six, atomMatrix, kFourDirection, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three] at hnonneg
      have : 0 ≤ coefficient 5 := by
        nlinarith [hnonneg, h05.2.1, h05.2.2.1, h05.2.2.2]
      simpa [kFourOppositeEdge] using
        (lt_of_le_of_ne this (Ne.symm (hcoefficient 5)))
    · have hnonneg := hform ![1, -1, 0]
      simp [Fin.sum_univ_six, atomMatrix, kFourDirection, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three] at hnonneg
      have : 0 ≤ coefficient 0 := by nlinarith [h05.2.1, h05.2.2.1,
        h05.2.2.2]
      simpa [kFourOppositeEdge] using
        (lt_of_le_of_ne this (Ne.symm (hcoefficient 0)))
  · rcases h14.1 with rfl | rfl
    · have hnonneg := hform ![0, 1, 0]
      simp [Fin.sum_univ_six, atomMatrix, kFourDirection, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three] at hnonneg
      have : 0 ≤ coefficient 4 := by nlinarith [h14.2.1, h14.2.2.1,
        h14.2.2.2]
      simpa [kFourOppositeEdge] using
        (lt_of_le_of_ne this (Ne.symm (hcoefficient 4)))
    · have hnonneg := hform ![1, 0, -1]
      simp [Fin.sum_univ_six, atomMatrix, kFourDirection, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three] at hnonneg
      have : 0 ≤ coefficient 1 := by nlinarith [h14.2.1, h14.2.2.1,
        h14.2.2.2]
      simpa [kFourOppositeEdge] using
        (lt_of_le_of_ne this (Ne.symm (hcoefficient 1)))
  · rcases h23.1 with rfl | rfl
    · have hnonneg := hform ![1, 0, 0]
      simp [Fin.sum_univ_six, atomMatrix, kFourDirection, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three] at hnonneg
      have : 0 ≤ coefficient 3 := by nlinarith [h23.2.1, h23.2.2.1,
        h23.2.2.2]
      simpa [kFourOppositeEdge] using
        (lt_of_le_of_ne this (Ne.symm (hcoefficient 3)))
    · have hnonneg := hform ![0, 1, -1]
      simp [Fin.sum_univ_six, atomMatrix, kFourDirection, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three] at hnonneg
      have : 0 ≤ coefficient 2 := by nlinarith [h23.2.1, h23.2.2.1,
        h23.2.2.2]
      simpa [kFourOppositeEdge] using
        (lt_of_le_of_ne this (Ne.symm (hcoefficient 2)))

/-! ## Chart selection exchange -/

/-- Swapping two labels in a chart selection has exactly the coefficient
replacement used by `kFourPointerWindowCoefficient`. -/
theorem chartCoeff_insert_swap_eq_pointerWindowCoefficient {size : ℕ}
    (mass weight : Fin size → ℝ) (tree : Finset (Fin size))
    (removed inserted : Fin size) (hremoved : removed ∉ tree)
    (_hinserted : inserted ∉ tree) (hne : inserted ≠ removed) :
    chartCoeff mass weight (insert inserted tree)
      = fun label =>
          if label = removed then -mass removed
          else if label = inserted then
            chartCoeff mass weight (insert inserted tree) inserted
          else chartCoeff mass weight (insert removed tree) label := by
  funext label
  unfold chartCoeff
  by_cases hr : label = removed
  · subst label
    simp [hremoved, Ne.symm hne]
  by_cases hi : label = inserted
  · subst label
    simp [hne]
  simp [hr, hi]

/-! ## The endpoint has a unique zero-voltage edge -/

/-- All six coefficients of the singular four-label endpoint are nonzero. -/
theorem KFourPivotWallPricedOrthogonalEndpointData.added_coeff_ne
    {point : DirectionChartPoint 6} {tree : Finset (Fin 6)}
    (data : KFourPivotWallPricedOrthogonalEndpointData point tree) :
    ∀ label, chartCoeff point.mass point.weight
      (insert data.endpoint.added tree) label ≠ 0 := by
  intro label
  by_cases hmem : label ∈ insert data.endpoint.added tree
  · exact ne_of_gt (chartCoeff_pos_of_mem point hmem)
  · exact ne_of_lt (chartCoeff_neg_of_not_mem point hmem)

/-- A second orthogonal edge at the endpoint must be the opposite edge.  The
adjacent alternative would be a forbidden zero-voltage triangle. -/
theorem KFourPivotWallPricedOrthogonalEndpointData.second_orthogonal_eq_opposite
    {point : DirectionChartPoint 6} {tree : Finset (Fin 6)}
    (data : KFourPivotWallPricedOrthogonalEndpointData point tree)
    (other : Fin 6) (hother : other ≠ data.endpoint.added)
    (horthogonal : kFourDirection other ⬝ᵥ data.tightDirection = 0) :
    other = kFourOppositeEdge data.endpoint.added := by
  let coefficient := chartCoeff point.mass point.weight
    (insert data.endpoint.added tree)
  have hkernel :
      (∑ label, coefficient label • atomMatrix (kFourDirection label)) *ᵥ
        data.tightDirection = 0 := by
    rw [← directionChartGap_eq_coeff_sum]
    exact data.added_gap_kernel
  rcases kFour_second_zero_is_opposite_or_triangle data.tightDirection
      data.tightDirection_ne data.endpoint.added other data.added_orthogonal
      horthogonal hother with hopposite | htriangle
  · exact hopposite
  · exact False.elim (kFour_no_zero_triangle_of_coeffSum_kernel coefficient
      data.tightDirection data.added_coeff_ne data.tightDirection_ne hkernel
        htriangle)

/-- The opposite-zero branch is impossible: its checkerboard makes the old
positive-definite pointer window have negative determinant. -/
theorem KFourPivotWallPricedOrthogonalEndpointData.opposite_not_orthogonal
    {point : DirectionChartPoint 6} {tree : Finset (Fin 6)}
    (data : KFourPivotWallPricedOrthogonalEndpointData point tree) :
    kFourDirection (kFourOppositeEdge data.endpoint.added) ⬝ᵥ
      data.tightDirection ≠ 0 := by
  intro hoppositeOrthogonal
  let coefficient := chartCoeff point.mass point.weight
    (insert data.endpoint.added tree)
  have hkernel :
      (∑ label, coefficient label • atomMatrix (kFourDirection label)) *ᵥ
        data.tightDirection = 0 := by
    rw [← directionChartGap_eq_coeff_sum]
    exact data.added_gap_kernel
  have hchecker := kFour_opposite_checkerboard_of_coeffSum_kernel coefficient
    data.tightDirection data.endpoint.added data.tightDirection_ne hkernel
      data.added_orthogonal hoppositeOrthogonal
  have hoppositePos := kFour_opposite_coefficient_pos_of_checkerboard coefficient
    data.endpoint.added hchecker data.added_coeff_ne (by
      rw [← directionChartGap_eq_coeff_sum]
      exact data.added_gap_posSemidef)
  have hpointerNeAdded : data.endpoint.pointer ≠ data.endpoint.added := by
    intro heq
    exact data.endpoint.added_notMem (heq ▸ Finset.mem_insert_self _ tree)
  have hpointerNeOpposite :
      data.endpoint.pointer ≠ kFourOppositeEdge data.endpoint.added := by
    intro heq
    apply data.pointer_reads
    rw [heq]
    exact hoppositeOrthogonal
  have hpointerOld : coefficient data.endpoint.pointer < 0 := by
    apply chartCoeff_neg_of_not_mem point
    simp [data.endpoint.pointer_notMem, hpointerNeAdded]
  have hpointerNew : 0 < chartCoeff point.mass point.weight
      (insert data.endpoint.pointer tree) data.endpoint.pointer :=
    chartCoeff_pos_of_mem point (Finset.mem_insert_self _ _)
  have hdetNeg := det_kFour_pointerWindowCoefficient_neg coefficient
    data.endpoint.added data.endpoint.pointer (point.mass data.endpoint.added)
      (chartCoeff point.mass point.weight (insert data.endpoint.pointer tree)
        data.endpoint.pointer) hchecker hpointerNeAdded hpointerNeOpposite
      (point.mass_pos data.endpoint.added) hpointerOld hpointerNew hoppositePos
  have hcoeffSwap := chartCoeff_insert_swap_eq_pointerWindowCoefficient
    point.mass point.weight tree data.endpoint.added data.endpoint.pointer
      (fun hmem => data.endpoint.added_notMem
        (Finset.mem_insert_of_mem hmem)) data.endpoint.pointer_notMem
      hpointerNeAdded
  have hgapWindow : directionChartGap kFourDirection point.mass point.weight
      (insert data.endpoint.pointer tree)
      = ∑ label, kFourPointerWindowCoefficient coefficient data.endpoint.added
          data.endpoint.pointer (point.mass data.endpoint.added)
            (chartCoeff point.mass point.weight (insert data.endpoint.pointer tree)
              data.endpoint.pointer) label • atomMatrix (kFourDirection label) := by
    rw [directionChartGap_eq_coeff_sum, hcoeffSwap]
    apply Finset.sum_congr rfl
    intro label _
    congr 1
    simp [kFourPointerWindowCoefficient, coefficient, hpointerNeAdded]
  have hdetPos := data.endpoint.window_posDef.det_pos
  rw [hgapWindow] at hdetPos
  linarith

/-- **THE EXACT CONTRACTION LAW.**  The inserted edge is the unique K4 edge
orthogonal to the tight direction at a priced endpoint. -/
theorem KFourPivotWallPricedOrthogonalEndpointData.orthogonal_iff_eq_added
    {point : DirectionChartPoint 6} {tree : Finset (Fin 6)}
    (data : KFourPivotWallPricedOrthogonalEndpointData point tree)
    (label : Fin 6) :
    kFourDirection label ⬝ᵥ data.tightDirection = 0 ↔
      label = data.endpoint.added := by
  constructor
  · intro horthogonal
    by_contra hne
    have hopposite := data.second_orthogonal_eq_opposite label hne horthogonal
    exact data.opposite_not_orthogonal (hopposite ▸ horthogonal)
  · rintro rfl
    exact data.added_orthogonal

/-! ## Package the exact contraction endpoint -/

/-- The final geometric endpoint interface: all data produced previously,
plus the proof that its inserted edge is the unique zero-voltage edge. -/
structure KFourPivotWallPricedContractedEndpointData
    (point : DirectionChartPoint 6) (tree : Finset (Fin 6)) where
  endpoint : KFourPivotWallPricedOrthogonalEndpointData point tree
  orthogonal_iff_eq_added : ∀ label : Fin 6,
    kFourDirection label ⬝ᵥ endpoint.tightDirection = 0 ↔
      label = endpoint.endpoint.added

/-- Every orthogonal endpoint produced by the pivot propagation has the exact
one-edge contraction form. -/
theorem kFourPivotWall_pricedContractedEndpointData
    {point : DirectionChartPoint 6} {tree : Finset (Fin 6)}
    (data : KFourPivotWallPricedOrthogonalEndpointData point tree) :
    Nonempty (KFourPivotWallPricedContractedEndpointData point tree) :=
  ⟨⟨data, data.orthogonal_iff_eq_added⟩⟩

/-- Direct producer from the original priced endpoint at a genuine pivot
wall. -/
theorem kFourPivotWall_pricedContractedEndpointData_of_priced
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hwindow : KFourTreeWindowData point tree)
    (data : KFourPivotWallPricedEndpointData point tree) :
    Nonempty (KFourPivotWallPricedContractedEndpointData point tree) := by
  obtain ⟨orthogonal⟩ :=
    kFourPivotWall_pricedOrthogonalEndpointData point hgap hwindow data
  exact kFourPivotWall_pricedContractedEndpointData orthogonal

end Gtz
