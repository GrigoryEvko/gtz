import Gtz.Design.KernelPointer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The star sign rigidity

The four vertex stars are the only unclassified branch of the committed A3
residual.  This module proves that the branch is sign-rigid.

The engine is elementary.  In the balanced per-edge sign gauge, a star gap is
congruent to a matrix with strictly positive off-diagonal entries: the three
opposite-triangle masses.  A nonnegative nonzero kernel vector of such a
matrix makes some row read strictly positively against its zero row equation.
The positive semidefinite diagonal then gives a contradiction.  As a result:

* `kernelVec_signMixed_of_offDiag_pos` — a kernel vector of a matrix with
  nonnegative diagonal and positive off-diagonals has a strictly positive
  coordinate and a strictly negative coordinate.
* `quadForm_pos_on_nonneg_of_offDiag_pos` — such a matrix, when positive
  semidefinite, is strictly positive on the nonnegative orthant minus zero.
* `kernel_readings_signMixed_of_dualSystem` — the transport: a weak-not-strict
  chart gap with a Metzler dual-pairing matrix has a kernel probe whose basis
  readings carry both signs.
* `kFourStar{Gauge,A,B,C}_kernel_readings_signMixed` — the four star
  instances, with the balanced gauge written into explicit basis and dual
  vectors.
* `kFour_pointer_of_kernel` — every kernel probe hands the landed pointer.

The reading vectors use the balanced gauge: the direction of each tree edge
is flipped where necessary so that all three fundamental cycles cross their
two tree edges with opposite signs.  The gap does not see the flip, because
the atom of a direction equals the atom of its negation.
-/

namespace Gtz

open Matrix

/-! ## 1. Symmetric quadratic-form tools -/

/-- The quadratic form along a ray through a base point. -/
theorem quadForm_add_smul {A : Matrix (Fin 3) (Fin 3) ℝ} (htrans : Aᵀ = A)
    (x v : Fin 3 → ℝ) (t : ℝ) :
    (x + t • v) ⬝ᵥ (A *ᵥ (x + t • v))
      = x ⬝ᵥ (A *ᵥ x) + 2 * t * (v ⬝ᵥ (A *ᵥ x)) + t ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  have hswap := dotProduct_mulVec_comm_of_transpose_eq htrans x v
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hswap]
  ring

/-- A zero of the form of a positive semidefinite symmetric matrix is a
kernel vector. -/
theorem mulVec_eq_zero_of_quadForm_eq_zero {A : Matrix (Fin 3) (Fin 3) ℝ}
    (htrans : Aᵀ = A) (hpsd : A.PosSemidef) {x : Fin 3 → ℝ}
    (hzero : x ⬝ᵥ (A *ᵥ x) = 0) : A *ᵥ x = 0 := by
  have hform : ∀ v : Fin 3 → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    intro v
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 v
    rwa [star_trivial] at h
  have hentry : ∀ v : Fin 3 → ℝ, v ⬝ᵥ (A *ᵥ x) = 0 := by
    intro v
    set b := v ⬝ᵥ (A *ᵥ x) with hb
    set c := v ⬝ᵥ (A *ᵥ v) with hc
    have hcnn : 0 ≤ c := hform v
    have hsq : b ^ 2 ≤ 0 := by
      rcases eq_or_lt_of_le hcnn with hczero | hcpos
      · have hkey := hform (x + (-b) • v)
        rw [quadForm_add_smul htrans, hzero, ← hb, ← hc, ← hczero] at hkey
        nlinarith
      · have hkey := hform (x + (-(b / c)) • v)
        rw [quadForm_add_smul htrans, hzero, ← hb, ← hc] at hkey
        have hexp : (0 : ℝ) + 2 * (-(b / c)) * b + (-(b / c)) ^ 2 * c
            = -(b ^ 2) / c := by
          field_simp
          ring
        rw [hexp] at hkey
        have hmul : 0 ≤ (-(b ^ 2) / c) * c := mul_nonneg hkey hcpos.le
        rw [div_mul_cancel₀ _ (ne_of_gt hcpos)] at hmul
        linarith
    have hzero' : b ^ 2 = 0 := le_antisymm hsq (sq_nonneg b)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hzero'
  funext index
  have h := hentry (Pi.single index 1)
  simpa [dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using h

/-- A positive semidefinite matrix that is not positive definite has a
nonzero kernel vector. -/
theorem exists_kernelVec_of_posSemidef_not_posDef {A : Matrix (Fin 3) (Fin 3) ℝ}
    (htrans : Aᵀ = A) (hpsd : A.PosSemidef) (hnot : ¬ A.PosDef) :
    ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ A *ᵥ x = 0 := by
  have hform : ∀ v : Fin 3 → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    intro v
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 v
    rwa [star_trivial] at h
  have hwitness : ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ x ⬝ᵥ (A *ᵥ x) ≤ 0 := by
    by_contra hall
    push Not at hall
    refine hnot (Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hpsd.1, fun x hx => ?_⟩)
    rw [star_trivial]
    exact hall x hx
  obtain ⟨x, hx, hle⟩ := hwitness
  exact ⟨x, hx, mulVec_eq_zero_of_quadForm_eq_zero htrans hpsd
    (le_antisymm hle (hform x))⟩

/-! ## 2. The sign-rigidity core -/

/-- A matrix with nonnegative diagonal and strictly positive off-diagonals
has no nonnegative nonzero kernel vector.  One row of the kernel equation
reads strictly positively. -/
theorem kernelVec_not_nonneg_of_offDiag_pos {A : Matrix (Fin 3) (Fin 3) ℝ}
    {y : Fin 3 → ℝ} (hdiag : ∀ index, 0 ≤ A index index)
    (hoff : ∀ row col, row ≠ col → 0 < A row col)
    (hker : A *ᵥ y = 0) (hy : y ≠ 0) : ¬ ∀ index, 0 ≤ y index := by
  intro hnn
  have hrow : ∀ row : Fin 3,
      A row 0 * y 0 + A row 1 * y 1 + A row 2 * y 2 = 0 := by
    intro row
    have h := congrFun hker row
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have hsome : ∃ index, y index ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hy (funext hall)
  obtain ⟨index, hindex⟩ := hsome
  have hpos : 0 < y index := lt_of_le_of_ne (hnn index) (Ne.symm hindex)
  fin_cases index
  · have h := hrow 1
    have hterm : 0 < A 1 0 * y 0 := mul_pos (hoff 1 0 (by decide)) hpos
    have hone : 0 ≤ A 1 1 * y 1 := mul_nonneg (hdiag 1) (hnn 1)
    have htwo : 0 ≤ A 1 2 * y 2 := mul_nonneg (hoff 1 2 (by decide)).le (hnn 2)
    linarith
  · have h := hrow 0
    have hterm : 0 < A 0 1 * y 1 := mul_pos (hoff 0 1 (by decide)) hpos
    have hone : 0 ≤ A 0 0 * y 0 := mul_nonneg (hdiag 0) (hnn 0)
    have htwo : 0 ≤ A 0 2 * y 2 := mul_nonneg (hoff 0 2 (by decide)).le (hnn 2)
    linarith
  · have h := hrow 0
    have hterm : 0 < A 0 2 * y 2 := mul_pos (hoff 0 2 (by decide)) hpos
    have hone : 0 ≤ A 0 0 * y 0 := mul_nonneg (hdiag 0) (hnn 0)
    have htwo : 0 ≤ A 0 1 * y 1 := mul_nonneg (hoff 0 1 (by decide)).le (hnn 1)
    linarith

/-- **THE SIGN LEMMA.**  A nonzero kernel vector of a matrix with nonnegative
diagonal and strictly positive off-diagonals carries both signs. -/
theorem kernelVec_signMixed_of_offDiag_pos {A : Matrix (Fin 3) (Fin 3) ℝ}
    {y : Fin 3 → ℝ} (hdiag : ∀ index, 0 ≤ A index index)
    (hoff : ∀ row col, row ≠ col → 0 < A row col)
    (hker : A *ᵥ y = 0) (hy : y ≠ 0) :
    (∃ index, 0 < y index) ∧ ∃ index, y index < 0 := by
  have hnegker : A *ᵥ (-y) = 0 := by
    rw [Matrix.mulVec_neg, hker, neg_zero]
  have hnegne : (-y : Fin 3 → ℝ) ≠ 0 := fun h => hy (by simpa using congrArg Neg.neg h)
  have hnotnn := kernelVec_not_nonneg_of_offDiag_pos hdiag hoff hker hy
  have hnotnp := kernelVec_not_nonneg_of_offDiag_pos hdiag hoff hnegker hnegne
  push Not at hnotnn hnotnp
  obtain ⟨row, hrow⟩ := hnotnn
  obtain ⟨col, hcol⟩ := hnotnp
  exact ⟨⟨col, by simpa using hcol⟩, ⟨row, hrow⟩⟩

/-- **THE COPOSITIVITY UPGRADE.**  A positive semidefinite matrix with
strictly positive off-diagonals is strictly positive on the nonnegative
orthant minus zero. -/
theorem quadForm_pos_on_nonneg_of_offDiag_pos {A : Matrix (Fin 3) (Fin 3) ℝ}
    (htrans : Aᵀ = A) (hpsd : A.PosSemidef)
    (hoff : ∀ row col, row ≠ col → 0 < A row col)
    {z : Fin 3 → ℝ} (hz : ∀ index, 0 ≤ z index) (hzne : z ≠ 0) :
    0 < z ⬝ᵥ (A *ᵥ z) := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 z
  rw [star_trivial] at hform
  rcases eq_or_lt_of_le hform with hzero | hpos
  · exfalso
    have hker := mulVec_eq_zero_of_quadForm_eq_zero htrans hpsd hzero.symm
    have hdiag : ∀ index, 0 ≤ A index index := by
      intro index
      have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 (Pi.single index 1)
      rw [star_trivial] at h
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply,
        Finset.sum_ite_eq', Fin.sum_univ_three] using h
    obtain ⟨_, index, hneg⟩ :=
      kernelVec_signMixed_of_offDiag_pos hdiag hoff hker hzne
    exact absurd (hz index) (not_le.mpr hneg)
  · exact hpos

/-! ## 3. The dual-system transport -/

/-- **THE TRANSPORT.**  A symmetric positive semidefinite, not positive
definite matrix whose dual-pairing matrix has strictly positive off-diagonals
has a nonzero kernel vector whose basis readings carry both signs.  The
hypothesis `hrecon` is the dual-basis reconstruction of the identity. -/
theorem kernel_readings_signMixed_of_dualSystem {G : Matrix (Fin 3) (Fin 3) ℝ}
    (htrans : Gᵀ = G) (hpsd : G.PosSemidef) (hnot : ¬ G.PosDef)
    (basisVec dualVec : Fin 3 → (Fin 3 → ℝ))
    (hrecon : ∀ x : Fin 3 → ℝ,
      (basisVec 0 ⬝ᵥ x) • dualVec 0 + (basisVec 1 ⬝ᵥ x) • dualVec 1
        + (basisVec 2 ⬝ᵥ x) • dualVec 2 = x)
    (hoff : ∀ row col, row ≠ col → 0 < dualVec row ⬝ᵥ (G *ᵥ dualVec col)) :
    ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ G *ᵥ x = 0
      ∧ (∃ index, 0 < basisVec index ⬝ᵥ x)
      ∧ ∃ index, basisVec index ⬝ᵥ x < 0 := by
  obtain ⟨x, hxne, hker⟩ := exists_kernelVec_of_posSemidef_not_posDef htrans hpsd hnot
  set pairing : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun row col => dualVec row ⬝ᵥ (G *ᵥ dualVec col) with hpairing
  set readings : Fin 3 → ℝ := fun index => basisVec index ⬝ᵥ x with hreadings
  have hdiag : ∀ index, 0 ≤ pairing index index := by
    intro index
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 (dualVec index)
    rwa [star_trivial] at h
  have hkerP : pairing *ᵥ readings = 0 := by
    funext row
    have hlhs : (pairing *ᵥ readings) row
        = (dualVec row ⬝ᵥ (G *ᵥ dualVec 0)) * readings 0
          + (dualVec row ⬝ᵥ (G *ᵥ dualVec 1)) * readings 1
          + (dualVec row ⬝ᵥ (G *ᵥ dualVec 2)) * readings 2 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hpairing]
    have hmid : dualVec row ⬝ᵥ (G *ᵥ x)
        = (dualVec row ⬝ᵥ (G *ᵥ dualVec 0)) * readings 0
          + (dualVec row ⬝ᵥ (G *ᵥ dualVec 1)) * readings 1
          + (dualVec row ⬝ᵥ (G *ᵥ dualVec 2)) * readings 2 := by
      conv_lhs => rw [← hrecon x]
      rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_smul]
      simp only [smul_eq_mul, hreadings]
      ring
    have hzero : dualVec row ⬝ᵥ (G *ᵥ x) = 0 := by
      rw [hker]
      simp
    rw [hlhs, ← hmid, hzero]
    simp
  have hrne : readings ≠ 0 := by
    intro hzero
    apply hxne
    have hx := hrecon x
    rw [show basisVec 0 ⬝ᵥ x = 0 from congrFun hzero 0,
      show basisVec 1 ⬝ᵥ x = 0 from congrFun hzero 1,
      show basisVec 2 ⬝ᵥ x = 0 from congrFun hzero 2] at hx
    simpa using hx.symm
  have hoffP : ∀ row col, row ≠ col → 0 < pairing row col := by
    intro row col hne
    exact hoff row col hne
  obtain ⟨hposIdx, hnegIdx⟩ :=
    kernelVec_signMixed_of_offDiag_pos hdiag hoffP hkerP hrne
  exact ⟨x, hxne, hker, hposIdx, hnegIdx⟩

/-! ## 4. The bilinear chart reading -/

/-- The bilinear form of the chart gap in direction readings. -/
theorem dotProduct_directionChartGap_mulVec_pair {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (left right : Fin 3 → ℝ) :
    left ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ right)
      = (∑ label ∈ selected, mass label / weight label
          * ((direction label ⬝ᵥ left) * (direction label ⬝ᵥ right)))
        - ∑ label, mass label
          * ((direction label ⬝ᵥ left) * (direction label ⬝ᵥ right)) := by
  rw [directionChartGap, Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec,
    dotProduct_sum, Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  · exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        dotProduct_atomMatrix_mulVec_pair]
  · exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        dotProduct_atomMatrix_mulVec_pair]

/-! ## 5. The four star instances

Each star is given its balanced gauge: explicit basis vectors (the tree
directions, flipped where the gauge demands) and explicit dual vectors.  The
dual-pairing off-diagonals are exactly the three opposite-triangle masses. -/

section StarInstances

variable (point : DirectionChartPoint 6)

/-- The gauge star `{3, 4, 5}`: basis and dual are the coordinate vectors. -/
theorem kFourStarGauge_kernel_readings_signMixed
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      {3, 4, 5}).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      {3, 4, 5}).PosDef) :
    ∃ x : Fin 3 → ℝ, x ≠ 0
      ∧ directionChartGap kFourDirection point.mass point.weight {3, 4, 5} *ᵥ x = 0
      ∧ (∃ index : Fin 3, 0 < ![kFourDirection 3, kFourDirection 4,
          kFourDirection 5] index ⬝ᵥ x)
      ∧ ∃ index : Fin 3, ![kFourDirection 3, kFourDirection 4,
          kFourDirection 5] index ⬝ᵥ x < 0 := by
  refine kernel_readings_signMixed_of_dualSystem
    (directionChartGap_transpose _ _ _ _) hpsd hnot _
    ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] (fun x => ?_) (fun row col hne => ?_)
  · funext coord
    fin_cases coord <;>
      simp [kFourDirection, dotProduct, Fin.sum_univ_three]
  · rw [dotProduct_directionChartGap_mulVec_pair]
    rw [show ({3, 4, 5} : Finset (Fin 6)) = insert 3 (insert 4 {5}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Fin.sum_univ_six]
    fin_cases row <;> fin_cases col <;> simp_all [kFourDirection, dotProduct,
      Fin.sum_univ_three] <;>
      first
      | linarith [point.mass_pos 0]
      | linarith [point.mass_pos 1]
      | linarith [point.mass_pos 2]

/-- The star `{0, 1, 3}` at vertex `a`.  The gauge keeps all three tree
directions.  The duals are `(0,-1,0)`, `(0,0,-1)`, `(1,1,1)`. -/
theorem kFourStarA_kernel_readings_signMixed
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      {0, 1, 3}).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      {0, 1, 3}).PosDef) :
    ∃ x : Fin 3 → ℝ, x ≠ 0
      ∧ directionChartGap kFourDirection point.mass point.weight {0, 1, 3} *ᵥ x = 0
      ∧ (∃ index : Fin 3, 0 < ![kFourDirection 0, kFourDirection 1,
          kFourDirection 3] index ⬝ᵥ x)
      ∧ ∃ index : Fin 3, ![kFourDirection 0, kFourDirection 1,
          kFourDirection 3] index ⬝ᵥ x < 0 := by
  refine kernel_readings_signMixed_of_dualSystem
    (directionChartGap_transpose _ _ _ _) hpsd hnot _
    ![![0, -1, 0], ![0, 0, -1], ![1, 1, 1]] (fun x => ?_) (fun row col hne => ?_)
  · funext coord
    fin_cases coord <;>
      · simp [kFourDirection, dotProduct, Fin.sum_univ_three]
        try ring
  · rw [dotProduct_directionChartGap_mulVec_pair]
    rw [show ({0, 1, 3} : Finset (Fin 6)) = insert 0 (insert 1 {3}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Fin.sum_univ_six]
    fin_cases row <;> fin_cases col <;> simp_all [kFourDirection, dotProduct,
      Fin.sum_univ_three] <;>
      first
      | linarith [point.mass_pos 2]
      | linarith [point.mass_pos 4]
      | linarith [point.mass_pos 5]

/-- The star `{0, 2, 4}` at vertex `b`.  The gauge flips directions `2` and
`4`.  The duals are `(1,0,0)`, `(0,0,1)`, `(-1,-1,-1)`. -/
theorem kFourStarB_kernel_readings_signMixed
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      {0, 2, 4}).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      {0, 2, 4}).PosDef) :
    ∃ x : Fin 3 → ℝ, x ≠ 0
      ∧ directionChartGap kFourDirection point.mass point.weight {0, 2, 4} *ᵥ x = 0
      ∧ (∃ index : Fin 3, 0 < ![kFourDirection 0, -kFourDirection 2,
          -kFourDirection 4] index ⬝ᵥ x)
      ∧ ∃ index : Fin 3, ![kFourDirection 0, -kFourDirection 2,
          -kFourDirection 4] index ⬝ᵥ x < 0 := by
  refine kernel_readings_signMixed_of_dualSystem
    (directionChartGap_transpose _ _ _ _) hpsd hnot _
    ![![1, 0, 0], ![0, 0, 1], ![-1, -1, -1]] (fun x => ?_) (fun row col hne => ?_)
  · funext coord
    fin_cases coord <;>
      · simp [kFourDirection, dotProduct, Fin.sum_univ_three]
        try ring
  · rw [dotProduct_directionChartGap_mulVec_pair]
    rw [show ({0, 2, 4} : Finset (Fin 6)) = insert 0 (insert 2 {4}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Fin.sum_univ_six]
    fin_cases row <;> fin_cases col <;> simp_all [kFourDirection, dotProduct,
      Fin.sum_univ_three] <;>
      first
      | linarith [point.mass_pos 1]
      | linarith [point.mass_pos 3]
      | linarith [point.mass_pos 5]

/-- The star `{1, 2, 5}` at vertex `c`.  The gauge flips direction `5`.  The
duals are `(1,0,0)`, `(0,1,0)`, `(-1,-1,-1)`. -/
theorem kFourStarC_kernel_readings_signMixed
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      {1, 2, 5}).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      {1, 2, 5}).PosDef) :
    ∃ x : Fin 3 → ℝ, x ≠ 0
      ∧ directionChartGap kFourDirection point.mass point.weight {1, 2, 5} *ᵥ x = 0
      ∧ (∃ index : Fin 3, 0 < ![kFourDirection 1, kFourDirection 2,
          -kFourDirection 5] index ⬝ᵥ x)
      ∧ ∃ index : Fin 3, ![kFourDirection 1, kFourDirection 2,
          -kFourDirection 5] index ⬝ᵥ x < 0 := by
  refine kernel_readings_signMixed_of_dualSystem
    (directionChartGap_transpose _ _ _ _) hpsd hnot _
    ![![1, 0, 0], ![0, 1, 0], ![-1, -1, -1]] (fun x => ?_) (fun row col hne => ?_)
  · funext coord
    fin_cases coord <;>
      · simp [kFourDirection, dotProduct, Fin.sum_univ_three]
        try ring
  · rw [dotProduct_directionChartGap_mulVec_pair]
    rw [show ({1, 2, 5} : Finset (Fin 6)) = insert 1 (insert 2 {5}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Fin.sum_univ_six]
    fin_cases row <;> fin_cases col <;> simp_all [kFourDirection, dotProduct,
      Fin.sum_univ_three] <;>
      first
      | linarith [point.mass_pos 0]
      | linarith [point.mass_pos 3]
      | linarith [point.mass_pos 4]

end StarInstances

/-! ## 6. The pointer at a kernel probe -/

/-- Every kernel probe of a selection gap hands the landed outside pointer:
some outside label makes every selection through it read strictly positively
at the same probe. -/
theorem kFour_pointer_of_kernel (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} (hcard : 2 ≤ selected.card)
    {x : Fin 3 → ℝ} (hx : x ≠ 0)
    (hker : directionChartGap kFourDirection point.mass point.weight selected
      *ᵥ x = 0) :
    ∃ pointer, pointer ∉ selected ∧
      ∀ swap : Finset (Fin 6), pointer ∈ swap →
        0 < x ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight swap
          *ᵥ x) := by
  refine exists_outside_pointer_of_nonpos_reading kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos point.weight_sum_one
    kFourDirection_span hcard hx ?_
  rw [hker]
  simp

end Gtz
