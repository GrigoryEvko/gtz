import Gtz.Wave.PlaneTieDesignBridge
import Gtz.Wave.BalancedCutSelection
import Gtz.Wave.PentagonFloorProof
import Gtz.Wave.AtomVertexSelection
import Gtz.Ties.ComplementJawWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The projection dictionary, the light region, and the strict engine at four lines

This module lands the diagonal-shift dictionary of the descent and its first
three payoffs.

## 1. The leveled square transpose law

The landed transpose law reads at level one.  The dictionary needs it at every
positive level, and in the strict form.  The proof is one Cauchy-Schwarz step
against a preimage.  No eigenvalue, no singular value, no spectral theorem.

## 2. The dictionary

For a picked triple of a rank-three design, domination of the identity by the
block sum is EQUIVALENT to the synthesis floor of the three atom blends, and
to the weighted Gram reading: the Gram block of the scaled atoms beats the
weight diagonal.  The block determinant equals the Gram block determinant.

## 3. The payoffs

* The uniform `(4,2)` cell: an equal-leverage design at uniform weights carries
  a dominating pair.  This is the first SELF-DUAL cell instance in the tree,
  and the point where the real spread pair beats the complex SIC.
* The light region of the `(6,3)` cell: weights below one tenth force a strict
  triple.  The landed tenth floor crosses the dictionary and fires the weld
  rivet.  This is the first A-side conclusion produced by a B-side floor.
* The strict engine at four lines: four pairwise-nonparallel active slots push
  the no-strict budget STRICTLY below the active mass minus one.  The equality
  face of the engine is all-tied, and the landed four-atom kill removes it.
-/

namespace Gtz

open Matrix Finset

/-! ## Layer 1 — dot product bookkeeping -/

theorem dot_self_nonneg {n : ℕ} (vec : Fin n → ℝ) : 0 ≤ vec ⬝ᵥ vec :=
  Finset.sum_nonneg fun index _ => mul_self_nonneg (vec index)

theorem eq_zero_of_dot_self_eq_zero {n : ℕ} {vec : Fin n → ℝ}
    (hzero : vec ⬝ᵥ vec = 0) : vec = 0 := by
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun index _ => mul_self_nonneg (vec index))).mp hzero
  funext index
  exact mul_self_eq_zero.mp (hterm index (Finset.mem_univ index))

theorem dot_self_pos {n : ℕ} {vec : Fin n → ℝ} (hne : vec ≠ 0) : 0 < vec ⬝ᵥ vec :=
  lt_of_le_of_ne (dot_self_nonneg vec)
    fun heq => hne (eq_zero_of_dot_self_eq_zero heq.symm)

/-- Cauchy-Schwarz for the dot product, in the square form. -/
theorem dot_sq_le_dot_mul_dot {n : ℕ} (vecOne vecTwo : Fin n → ℝ) :
    (vecOne ⬝ᵥ vecTwo) ^ 2 ≤ (vecOne ⬝ᵥ vecOne) * (vecTwo ⬝ᵥ vecTwo) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ vecOne vecTwo
  simp only [dotProduct]
  have hone : (∑ index, vecOne index ^ 2) = ∑ index, vecOne index * vecOne index :=
    Finset.sum_congr rfl fun index _ => pow_two (vecOne index)
  have htwo : (∑ index, vecTwo index ^ 2) = ∑ index, vecTwo index * vecTwo index :=
    Finset.sum_congr rfl fun index _ => pow_two (vecTwo index)
  rw [← hone, ← htwo]
  exact hcs

/-! ## Layer 2 — the leveled square transpose law -/

/-- **THE LEVELED SQUARE TRANSPOSE LAW.**  A square matrix with an expansion
floor carries the same floor on its transpose.  The floor makes the map
injective, a square injective map is surjective, and one Cauchy-Schwarz step
against the preimage moves the floor across the transpose. -/
theorem mulVec_floor_transpose {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) {level : ℝ}
    (hlevel : 0 < level)
    (hfloor : ∀ u : Fin n → ℝ, level * (u ⬝ᵥ u) ≤ (K *ᵥ u) ⬝ᵥ (K *ᵥ u)) :
    ∀ w : Fin n → ℝ, level * (w ⬝ᵥ w) ≤ (Kᵀ *ᵥ w) ⬝ᵥ (Kᵀ *ᵥ w) := by
  have hker : ∀ u : Fin n → ℝ, K *ᵥ u = 0 → u = 0 := by
    intro u hu
    have hread := hfloor u
    rw [hu] at hread
    simp only [dotProduct_zero] at hread
    have hself : u ⬝ᵥ u ≤ 0 := by nlinarith [hlevel, dot_self_nonneg u]
    exact eq_zero_of_dot_self_eq_zero (le_antisymm hself (dot_self_nonneg u))
  have hinj : Function.Injective K.mulVecLin := by
    intro u v huv
    have huv' : K *ᵥ u = K *ᵥ v := by
      simpa [Matrix.mulVecLin_apply] using huv
    have hzero : K *ᵥ (u - v) = 0 := by
      rw [Matrix.mulVec_sub, huv', sub_self]
    exact sub_eq_zero.mp (hker _ hzero)
  have hsurj : Function.Surjective K.mulVecLin :=
    (LinearMap.injective_iff_surjective).mp hinj
  intro w
  obtain ⟨u, hu⟩ := hsurj w
  have huVec : K *ᵥ u = w := by simpa [Matrix.mulVecLin_apply] using hu
  have hdual : u ⬝ᵥ (Kᵀ *ᵥ w) = w ⬝ᵥ w := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, huVec]
  rcases eq_or_ne w 0 with hwzero | hwne
  · subst hwzero
    simp only [Matrix.mulVec_zero, dotProduct_zero, mul_zero, le_refl]
  · have hwpos : 0 < w ⬝ᵥ w := dot_self_pos hwne
    have hcs := dot_sq_le_dot_mul_dot u (Kᵀ *ᵥ w)
    rw [hdual] at hcs
    have hfl := hfloor u
    rw [huVec] at hfl
    have hQ : 0 ≤ (Kᵀ *ᵥ w) ⬝ᵥ (Kᵀ *ᵥ w) := dot_self_nonneg _
    nlinarith [hcs, hfl, hwpos, hQ, dot_self_nonneg u,
      mul_le_mul_of_nonneg_right hfl hQ]

/-- **THE STRICT LEVELED TRANSPOSE LAW.** -/
theorem mulVec_floor_transpose_strict {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) {level : ℝ}
    (hlevel : 0 < level)
    (hfloor : ∀ u : Fin n → ℝ, u ≠ 0 → level * (u ⬝ᵥ u) < (K *ᵥ u) ⬝ᵥ (K *ᵥ u)) :
    ∀ w : Fin n → ℝ, w ≠ 0 → level * (w ⬝ᵥ w) < (Kᵀ *ᵥ w) ⬝ᵥ (Kᵀ *ᵥ w) := by
  have hker : ∀ u : Fin n → ℝ, K *ᵥ u = 0 → u = 0 := by
    intro u hu
    by_contra hune
    have hread := hfloor u hune
    rw [hu] at hread
    simp only [dotProduct_zero] at hread
    nlinarith [dot_self_pos hune, hlevel]
  have hinj : Function.Injective K.mulVecLin := by
    intro u v huv
    have huv' : K *ᵥ u = K *ᵥ v := by
      simpa [Matrix.mulVecLin_apply] using huv
    have hzero : K *ᵥ (u - v) = 0 := by
      rw [Matrix.mulVec_sub, huv', sub_self]
    exact sub_eq_zero.mp (hker _ hzero)
  have hsurj : Function.Surjective K.mulVecLin :=
    (LinearMap.injective_iff_surjective).mp hinj
  intro w hwne
  obtain ⟨u, hu⟩ := hsurj w
  have huVec : K *ᵥ u = w := by simpa [Matrix.mulVecLin_apply] using hu
  have hune : u ≠ 0 := by
    intro huzero
    rw [huzero, Matrix.mulVec_zero] at huVec
    exact hwne huVec.symm
  have hdual : u ⬝ᵥ (Kᵀ *ᵥ w) = w ⬝ᵥ w := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, huVec]
  have hwpos : 0 < w ⬝ᵥ w := dot_self_pos hwne
  have hcs := dot_sq_le_dot_mul_dot u (Kᵀ *ᵥ w)
  rw [hdual] at hcs
  have hfl := hfloor u hune
  rw [huVec] at hfl
  have hupos : 0 < u ⬝ᵥ u := dot_self_pos hune
  have hQpos : 0 < (Kᵀ *ᵥ w) ⬝ᵥ (Kᵀ *ᵥ w) := by
    rcases lt_or_eq_of_le (dot_self_nonneg (Kᵀ *ᵥ w)) with hpos | heq
    · exact hpos
    · exfalso
      rw [← heq] at hcs
      nlinarith [hwpos]
  nlinarith [hcs, hfl, hwpos, hupos, hQpos, hlevel,
    mul_lt_mul_of_pos_right hfl hQpos]

/-! ## Layer 3 — analysis and synthesis floors of a square family -/

section FamilyFloors

variable {n : ℕ} {level : ℝ}

/-- **ANALYSIS FROM SYNTHESIS.**  A leveled synthesis floor of a square family
is a leveled analysis floor: the summed squared readings beat the level. -/
theorem analysis_floor_of_synthesis_floor (hlevel : 0 < level)
    (fam : Fin n → Fin n → ℝ)
    (hsyn : ∀ u : Fin n → ℝ,
      level * (u ⬝ᵥ u) ≤ atomBlend fam u ⬝ᵥ atomBlend fam u) :
    ∀ probe : Fin n → ℝ, level * (probe ⬝ᵥ probe) ≤ ∑ slot, (fam slot ⬝ᵥ probe) ^ 2 := by
  intro probe
  have hcore := mulVec_floor_transpose (familyMatrix fam) hlevel
    (fun u => by rw [familyMatrix_mulVec]; exact hsyn u) probe
  rwa [familyMatrix_transpose_energy] at hcore

/-- **SYNTHESIS FROM ANALYSIS.** -/
theorem synthesis_floor_of_analysis_floor (hlevel : 0 < level)
    (fam : Fin n → Fin n → ℝ)
    (hana : ∀ probe : Fin n → ℝ,
      level * (probe ⬝ᵥ probe) ≤ ∑ slot, (fam slot ⬝ᵥ probe) ^ 2) :
    ∀ u : Fin n → ℝ,
      level * (u ⬝ᵥ u) ≤ atomBlend fam u ⬝ᵥ atomBlend fam u := by
  intro u
  have hcore := mulVec_floor_transpose (familyMatrix fam)ᵀ hlevel
    (fun probe => by rw [familyMatrix_transpose_energy]; exact hana probe) u
  rwa [Matrix.transpose_transpose, familyMatrix_mulVec] at hcore

/-- **STRICT ANALYSIS FROM STRICT SYNTHESIS.** -/
theorem analysis_strict_of_synthesis_strict (hlevel : 0 < level)
    (fam : Fin n → Fin n → ℝ)
    (hsyn : ∀ u : Fin n → ℝ, u ≠ 0 →
      level * (u ⬝ᵥ u) < atomBlend fam u ⬝ᵥ atomBlend fam u) :
    ∀ probe : Fin n → ℝ, probe ≠ 0 →
      level * (probe ⬝ᵥ probe) < ∑ slot, (fam slot ⬝ᵥ probe) ^ 2 := by
  intro probe hprobe
  have hcore := mulVec_floor_transpose_strict (familyMatrix fam) hlevel
    (fun u hu => by rw [familyMatrix_mulVec]; exact hsyn u hu) probe hprobe
  rwa [familyMatrix_transpose_energy] at hcore

/-- **STRICT SYNTHESIS FROM STRICT ANALYSIS.** -/
theorem synthesis_strict_of_analysis_strict (hlevel : 0 < level)
    (fam : Fin n → Fin n → ℝ)
    (hana : ∀ probe : Fin n → ℝ, probe ≠ 0 →
      level * (probe ⬝ᵥ probe) < ∑ slot, (fam slot ⬝ᵥ probe) ^ 2) :
    ∀ u : Fin n → ℝ, u ≠ 0 →
      level * (u ⬝ᵥ u) < atomBlend fam u ⬝ᵥ atomBlend fam u := by
  intro u hu
  have hcore := mulVec_floor_transpose_strict (familyMatrix fam)ᵀ hlevel
    (fun probe hprobe => by
      rw [familyMatrix_transpose_energy]; exact hana probe hprobe) u hu
  rwa [Matrix.transpose_transpose, familyMatrix_mulVec] at hcore

end FamilyFloors

/-! ## Layer 4 — the dictionary of a rank-three triple -/

section TripleDictionary

variable {m : ℕ}

theorem quadForm_pickGap (D : WeightedDesign m 3) (pick : Fin 3 → Fin m)
    (hinj : Function.Injective pick) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((subsetSum D (Finset.image pick Finset.univ) - 1) *ᵥ probe)
      = (∑ slot, (D.atom (pick slot) ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum, Matrix.one_mulVec,
    Finset.sum_image (fun x _ y _ h => hinj h)]
  simp only [momentCoord]

/-- **THE WEAK DICTIONARY.**  A picked triple dominates exactly when the three
atoms carry the unit synthesis floor: every blend keeps at least its own
coefficient energy. -/
theorem dominates_pick_iff_synthesis (D : WeightedDesign m 3) (pick : Fin 3 → Fin m)
    (hinj : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosSemidef
      ↔ ∀ u : Fin 3 → ℝ,
          u ⬝ᵥ u ≤ atomBlend (fun slot => D.atom (pick slot)) u
            ⬝ᵥ atomBlend (fun slot => D.atom (pick slot)) u := by
  constructor
  · intro hpsd u
    have hana : ∀ probe : Fin 3 → ℝ,
        (1 : ℝ) * (probe ⬝ᵥ probe) ≤ ∑ slot, (D.atom (pick slot) ⬝ᵥ probe) ^ 2 := by
      intro probe
      have hread := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
      rw [star_trivial, quadForm_pickGap D pick hinj] at hread
      linarith [hread]
    have hsyn := synthesis_floor_of_analysis_floor one_pos
      (fun slot => D.atom (pick slot)) hana u
    linarith [hsyn]
  · intro hsyn
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D _), fun probe => ?_⟩
    rw [star_trivial, quadForm_pickGap D pick hinj]
    have hsyn' : ∀ u : Fin 3 → ℝ,
        (1 : ℝ) * (u ⬝ᵥ u) ≤ atomBlend (fun slot => D.atom (pick slot)) u
          ⬝ᵥ atomBlend (fun slot => D.atom (pick slot)) u := by
      intro u
      rw [one_mul]
      exact hsyn u
    have hana := analysis_floor_of_synthesis_floor one_pos
      (fun slot => D.atom (pick slot)) hsyn' probe
    linarith [hana]

/-- **THE STRICT DICTIONARY.** -/
theorem posDef_pick_iff_synthesis (D : WeightedDesign m 3) (pick : Fin 3 → Fin m)
    (hinj : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef
      ↔ ∀ u : Fin 3 → ℝ, u ≠ 0 →
          u ⬝ᵥ u < atomBlend (fun slot => D.atom (pick slot)) u
            ⬝ᵥ atomBlend (fun slot => D.atom (pick slot)) u := by
  constructor
  · intro hpd u hu
    have hana : ∀ probe : Fin 3 → ℝ, probe ≠ 0 →
        (1 : ℝ) * (probe ⬝ᵥ probe) < ∑ slot, (D.atom (pick slot) ⬝ᵥ probe) ^ 2 := by
      intro probe hprobe
      have hread := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hprobe
      rw [star_trivial, quadForm_pickGap D pick hinj] at hread
      linarith [hread]
    have hsyn := synthesis_strict_of_analysis_strict one_pos
      (fun slot => D.atom (pick slot)) hana u hu
    linarith [hsyn]
  · intro hsyn
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D _), fun probe hprobe => ?_⟩
    rw [star_trivial, quadForm_pickGap D pick hinj]
    have hsyn' : ∀ u : Fin 3 → ℝ, u ≠ 0 →
        (1 : ℝ) * (u ⬝ᵥ u) < atomBlend (fun slot => D.atom (pick slot)) u
          ⬝ᵥ atomBlend (fun slot => D.atom (pick slot)) u := by
      intro u hu
      rw [one_mul]
      exact hsyn u hu
    have hana := analysis_strict_of_synthesis_strict one_pos
      (fun slot => D.atom (pick slot)) hsyn' probe hprobe
    linarith [hana]

/-- **THE WEIGHTED GRAM READING.**  Strict domination of a picked triple says
the scaled Gram block beats the weight diagonal, in quadratic form. -/
theorem posDef_pick_iff_weightGram (D : WeightedDesign m 3) (pick : Fin 3 → Fin m)
    (hinj : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef
      ↔ ∀ v : Fin 3 → ℝ, v ≠ 0 →
          (∑ slot, D.weight (pick slot) * v slot ^ 2)
            < atomBlend (fun slot => scaledAtomRows D (pick slot)) v
                ⬝ᵥ atomBlend (fun slot => scaledAtomRows D (pick slot)) v := by
  rw [posDef_pick_iff_synthesis D pick hinj]
  have hsqrtPos : ∀ slot : Fin 3, 0 < Real.sqrt (D.weight (pick slot)) :=
    fun slot => Real.sqrt_pos.mpr (D.weight_pos (pick slot))
  have hsq : ∀ slot : Fin 3,
      Real.sqrt (D.weight (pick slot)) ^ 2 = D.weight (pick slot) :=
    fun slot => Real.sq_sqrt (D.weight_pos (pick slot)).le
  constructor
  · intro hsyn v hv
    set u : Fin 3 → ℝ := fun slot => Real.sqrt (D.weight (pick slot)) * v slot with hudef
    have hune : u ≠ 0 := by
      intro huzero
      apply hv
      funext slot
      have hslot : u slot = 0 := congrFun huzero slot
      simp only [hudef] at hslot
      exact (mul_eq_zero.mp hslot).resolve_left (hsqrtPos slot).ne'
    have hkey := hsyn u hune
    have hdot : u ⬝ᵥ u = ∑ slot, D.weight (pick slot) * v slot ^ 2 := by
      simp only [dotProduct, hudef]
      refine Finset.sum_congr rfl fun slot _ => ?_
      calc Real.sqrt (D.weight (pick slot)) * v slot
            * (Real.sqrt (D.weight (pick slot)) * v slot)
          = Real.sqrt (D.weight (pick slot)) ^ 2 * v slot ^ 2 := by ring
        _ = D.weight (pick slot) * v slot ^ 2 := by rw [hsq slot]
    have hblend : atomBlend (fun slot => D.atom (pick slot)) u
        = atomBlend (fun slot => scaledAtomRows D (pick slot)) v := by
      funext index
      simp only [atomBlend, hudef, scaledAtomRows_row, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun slot _ => by ring
    rw [hdot, hblend] at hkey
    exact hkey
  · intro hgram u hu
    set v : Fin 3 → ℝ := fun slot => u slot / Real.sqrt (D.weight (pick slot)) with hvdef
    have hvne : v ≠ 0 := by
      intro hvzero
      apply hu
      funext slot
      have hslot : v slot = 0 := congrFun hvzero slot
      simp only [hvdef] at hslot
      exact (div_eq_zero_iff.mp hslot).resolve_right (hsqrtPos slot).ne'
    have hkey := hgram v hvne
    have hdot : (∑ slot, D.weight (pick slot) * v slot ^ 2) = u ⬝ᵥ u := by
      simp only [dotProduct, hvdef]
      refine Finset.sum_congr rfl fun slot _ => ?_
      rw [div_pow, hsq slot]
      have hne := (D.weight_pos (pick slot)).ne'
      field_simp
    have hblend : atomBlend (fun slot => scaledAtomRows D (pick slot)) v
        = atomBlend (fun slot => D.atom (pick slot)) u := by
      funext index
      simp only [atomBlend, hvdef, scaledAtomRows_row, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun slot _ => ?_
      rw [← mul_assoc, div_mul_cancel₀ _ (hsqrtPos slot).ne']
    rw [hdot, hblend] at hkey
    exact hkey

/-- **THE BLOCK DETERMINANT LAW.**  The determinant of the picked gap equals
the determinant of the Gram-block gap: the diagonal shift moves across the
square factorization. -/
theorem det_subsetSum_pick_sub_one (D : WeightedDesign m 3) (pick : Fin 3 → Fin m)
    (hinj : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).det
      = ((Matrix.of fun x y => D.atom (pick x) ⬝ᵥ D.atom (pick y))
          - (1 : Matrix (Fin 3) (Fin 3) ℝ)).det := by
  set K : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun index slot => D.atom (pick slot) index with hK
  have hsub : subsetSum D (Finset.image pick Finset.univ) = K * Kᵀ := by
    ext rowIndex colIndex
    rw [subsetSum, Matrix.sum_apply, Finset.sum_image (fun x _ y _ h => hinj h),
      Matrix.mul_apply]
    refine Finset.sum_congr rfl fun slot _ => ?_
    simp only [atomMatrix, Matrix.vecMulVec_apply, hK, Matrix.transpose_apply,
      Matrix.of_apply]
  have hgram : (Matrix.of fun x y => D.atom (pick x) ⬝ᵥ D.atom (pick y)) = Kᵀ * K := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [hK, Matrix.transpose_apply, Matrix.of_apply, dotProduct]
  rw [hsub, hgram]
  have hcomm := det_mul_sub_scalar_comm_fin_three K Kᵀ 1
  rwa [one_smul] at hcomm

end TripleDictionary

/-! ## Layer 5 — the plane pair bridge at every size, and the uniform `(4,2)` cell -/

section FourTwo

variable {m : ℕ}

theorem quadForm_pairGap (D : WeightedDesign m 2) {left right : Fin m}
    (hne : left ≠ right) (probe : Fin 2 → ℝ) :
    probe ⬝ᵥ ((subsetSum D ({left, right} : Finset (Fin m)) - 1) *ᵥ probe)
      = (D.atom left ⬝ᵥ probe) ^ 2 + (D.atom right ⬝ᵥ probe) ^ 2
          - probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum, Matrix.one_mulVec,
    Finset.sum_pair hne]
  simp only [momentCoord]

/-- The weak plane pair bridge, at every design size. -/
theorem pairDominates_scaledAtomRows_iff_posSemidef (D : WeightedDesign m 2)
    {left right : Fin m} (hne : left ≠ right) :
    PlanePairDominates (scaledAtomRows D left) (scaledAtomRows D right)
        (D.weight left) (D.weight right)
      ↔ (subsetSum D ({left, right} : Finset (Fin m)) - 1).PosSemidef := by
  have hweightLeft := D.weight_pos left
  have hweightRight := D.weight_pos right
  have hleftSq : ∀ value : ℝ,
      (Real.sqrt (D.weight left) * value) ^ 2 = D.weight left * value ^ 2 := by
    intro value
    rw [mul_pow, Real.sq_sqrt hweightLeft.le]
  have hrightSq : ∀ value : ℝ,
      (Real.sqrt (D.weight right) * value) ^ 2 = D.weight right * value ^ 2 := by
    intro value
    rw [mul_pow, Real.sq_sqrt hweightRight.le]
  constructor
  · intro hdom
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D _), fun probe => ?_⟩
    have hread := hdom probe
    rw [star_trivial, quadForm_pairGap D hne]
    rw [scaledAtomRows_dotProduct, scaledAtomRows_dotProduct] at hread
    rw [hleftSq, hrightSq] at hread
    nlinarith [mul_pos hweightLeft hweightRight]
  · intro hpsd probe
    have hread := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
    rw [star_trivial, quadForm_pairGap D hne] at hread
    rw [scaledAtomRows_dotProduct, scaledAtomRows_dotProduct]
    rw [hleftSq, hrightSq]
    nlinarith [mul_pos hweightLeft hweightRight]

/-- **THE UNIFORM `(4,2)` CELL.**  A four-atom rank-two design with uniform
weights and equal atom leverages carries a dominating pair.  This is the first
SELF-DUAL cell instance in the tree.  The spread pair reads sixty degrees, the
budgets read one half, and the criterion closes exactly.  Over the complex
field the SIC blocks every pair: the instance is real. -/
theorem exists_dominatingPair_uniform_fourTwo (D : WeightedDesign 4 2)
    (hweight : ∀ label, D.weight label = 1 / 4)
    (hlev : ∀ labelOne labelTwo,
      leverageOf (D.atom labelOne) = leverageOf (D.atom labelTwo)) :
    ∃ left right : Fin 4, left ≠ right ∧ Dominates D {left, right} := by
  have hframe : PlaneParseval (fun slot => scaledAtomRows D slot) :=
    scaledAtomRows_planeParseval D
  have hequal : ∀ slotOne slotTwo : Fin 4,
      scaledAtomRows D slotOne ⬝ᵥ scaledAtomRows D slotOne
        = scaledAtomRows D slotTwo ⬝ᵥ scaledAtomRows D slotTwo := by
    intro slotOne slotTwo
    rw [scaledAtomRows_mass, scaledAtomRows_mass, hweight slotOne, hweight slotTwo,
      hlev slotOne slotTwo]
  obtain ⟨left, right, hne, hdom⟩ :=
    exists_dominatingPlanePair_uniform (by norm_num)
      (fun slot => scaledAtomRows D slot) hframe hequal
      (scaleValue := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨left, right, hne, ?_⟩
  have hdom' : PlanePairDominates (scaledAtomRows D left) (scaledAtomRows D right)
      (D.weight left) (D.weight right) := by
    rw [hweight left, hweight right]
    exact hdom
  exact (pairDominates_scaledAtomRows_iff_posSemidef D hne).mp hdom'

end FourTwo

/-! ## Layer 6 — the light region of the `(6,3)` cell -/

section LightRegion

variable {m k : ℕ}

/-- The scaled atom rows obey the abstract frame law: the summed products of
their readings reproduce the dot product. -/
theorem scaledAtomRows_frame (D : WeightedDesign m k) :
    ∀ probe direction : Fin k → ℝ,
      (∑ slot, (scaledAtomRows D slot ⬝ᵥ probe)
          * (scaledAtomRows D slot ⬝ᵥ direction))
        = probe ⬝ᵥ direction := by
  intro probe direction
  have hleft : (∑ slot, (scaledAtomRows D slot ⬝ᵥ probe)
      * (scaledAtomRows D slot ⬝ᵥ direction))
      = (scaledAtomRows D *ᵥ probe) ⬝ᵥ (scaledAtomRows D *ᵥ direction) := rfl
  rw [hleft, Matrix.dotProduct_mulVec]
  have hpull : (scaledAtomRows D *ᵥ probe) ᵥ* scaledAtomRows D = probe := by
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      transpose_mul_scaledAtomRows, Matrix.vecMul_one]
  rw [hpull]

/-- **THE LIGHT REGION OF THE `(6,3)` CELL.**  When every weight stays at or
below a bound strictly below one tenth, some triple strictly dominates.  The
landed tenth floor supplies a carrier on the Gram side, the dictionary moves
the floor to the analysis side, and the weld rivet converts the floor above
the weights into strict domination.  This is the first A-side conclusion
produced by a B-side floor. -/
theorem exists_posDef_triple_of_light_weights (D : WeightedDesign 6 3) {bound : ℝ}
    (hbound : bound < 1 / 10) (hlight : ∀ label, D.weight label ≤ bound) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ (subsetSum D C - 1).PosDef := by
  have hboundPos : 0 < bound := lt_of_lt_of_le (D.weight_pos 0) (hlight 0)
  obtain ⟨slotOne, slotTwo, slotThree, hOneTwo, hOneThree, hTwoThree, hblend⟩ :=
    atomSpectralSupply_tenth (fun slot => scaledAtomRows D slot) (scaledAtomRows_frame D)
  have hnotMemOne : slotOne ∉ ({slotTwo, slotThree} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨hOneTwo, hOneThree⟩
  have hnotMemTwo : slotTwo ∉ ({slotThree} : Finset (Fin 6)) := by
    simp only [Finset.mem_singleton]
    exact hTwoThree
  refine ⟨{slotOne, slotTwo, slotThree}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hnotMemOne,
      Finset.card_insert_of_notMem hnotMemTwo, Finset.card_singleton]
  · refine posDef_subsetSum_of_weighted_floor D _ bound hboundPos
      (fun label _ => hlight label) ?_
    intro probe hprobe
    set fam : Fin 3 → (Fin 3 → ℝ) :=
      ![scaledAtomRows D slotOne, scaledAtomRows D slotTwo,
        scaledAtomRows D slotThree] with hfam
    have hsyn : ∀ u : Fin 3 → ℝ, (1 / 10 : ℝ) * (u ⬝ᵥ u)
        ≤ atomBlend fam u ⬝ᵥ atomBlend fam u := by
      intro u
      have hkey := hblend (u 0) (u 1) (u 2)
      have hblendEq : atomBlend fam u
          = atomSlotBlend (fun slot => scaledAtomRows D slot)
              slotOne slotTwo slotThree (u 0) (u 1) (u 2) := by
        funext index
        simp only [atomBlend, atomSlotBlend, Fin.sum_univ_three, hfam,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
      have hdotEq : u ⬝ᵥ u = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
        simp only [dotProduct, Fin.sum_univ_three]
        ring
      rw [hblendEq, hdotEq]
      exact hkey
    have hana := analysis_floor_of_synthesis_floor (by norm_num) fam hsyn probe
    have hthree : (∑ slot, (fam slot ⬝ᵥ probe) ^ 2)
        = (scaledAtomRows D slotOne ⬝ᵥ probe) ^ 2
          + (scaledAtomRows D slotTwo ⬝ᵥ probe) ^ 2
          + (scaledAtomRows D slotThree ⬝ᵥ probe) ^ 2 := by
      simp only [Fin.sum_univ_three, hfam, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    have hsum : (∑ label ∈ ({slotOne, slotTwo, slotThree} : Finset (Fin 6)),
        D.weight label * (D.atom label ⬝ᵥ probe) ^ 2)
        = (scaledAtomRows D slotOne ⬝ᵥ probe) ^ 2
          + (scaledAtomRows D slotTwo ⬝ᵥ probe) ^ 2
          + (scaledAtomRows D slotThree ⬝ᵥ probe) ^ 2 := by
      rw [Finset.sum_insert hnotMemOne, Finset.sum_insert hnotMemTwo,
        Finset.sum_singleton]
      have hterm : ∀ label : Fin 6, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2
          = (scaledAtomRows D label ⬝ᵥ probe) ^ 2 := by
        intro label
        rw [scaledAtomRows_dotProduct, mul_pow, Real.sq_sqrt (D.weight_pos label).le]
      rw [hterm slotOne, hterm slotTwo, hterm slotThree]
      ring
    rw [hsum]
    have hfloor : (1 / 10 : ℝ) * (probe ⬝ᵥ probe)
        ≤ (scaledAtomRows D slotOne ⬝ᵥ probe) ^ 2
          + (scaledAtomRows D slotTwo ⬝ᵥ probe) ^ 2
          + (scaledAtomRows D slotThree ⬝ᵥ probe) ^ 2 := by
      rw [← hthree]
      exact hana
    have hprobePos : 0 < probe ⬝ᵥ probe := dot_self_pos hprobe
    nlinarith [hfloor, hprobePos, hbound]

/-- The light region with a per-label strict bound: the maximum weight is the
bound. -/
theorem exists_posDef_triple_of_weights_lt_tenth (D : WeightedDesign 6 3)
    (hlight : ∀ label, D.weight label < 1 / 10) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ (subsetSum D C - 1).PosDef := by
  obtain ⟨top, -, htop⟩ := Finset.exists_max_image Finset.univ D.weight
    ⟨0, Finset.mem_univ 0⟩
  exact exists_posDef_triple_of_light_weights D (hlight top)
    (fun label => htop label (Finset.mem_univ label))

end LightRegion

/-! ## Layer 7 — scale monotonicity and the aggregation lift -/

/-- Strict plane domination is monotone under smaller positive scales. -/
theorem planePairDominatesStrict_mono_scales {atomOne atomTwo : Fin 2 → ℝ}
    {scaleOne scaleTwo smallOne smallTwo : ℝ}
    (hposOne : 0 < smallOne) (hposTwo : 0 < smallTwo)
    (hleOne : smallOne ≤ scaleOne) (hleTwo : smallTwo ≤ scaleTwo)
    (hdom : PlanePairDominatesStrict atomOne atomTwo scaleOne scaleTwo) :
    PlanePairDominatesStrict atomOne atomTwo smallOne smallTwo := by
  have hscaleOne : 0 < scaleOne := lt_of_lt_of_le hposOne hleOne
  have hscaleTwo : 0 < scaleTwo := lt_of_lt_of_le hposTwo hleTwo
  obtain ⟨hgapOne, hgapTwo, hdet⟩ :=
    (planePairDominatesStrict_iff hscaleOne hscaleTwo).mp hdom
  refine (planePairDominatesStrict_iff hposOne hposTwo).mpr
    ⟨lt_of_le_of_lt hleOne hgapOne, lt_of_le_of_lt hleTwo hgapTwo, ?_⟩
  have hfactorOne : atomOne ⬝ᵥ atomOne - scaleOne ≤ atomOne ⬝ᵥ atomOne - smallOne := by
    linarith
  have hfactorTwo : atomTwo ⬝ᵥ atomTwo - scaleTwo ≤ atomTwo ⬝ᵥ atomTwo - smallTwo := by
    linarith
  nlinarith [hdet, hgapOne, hgapTwo, hfactorOne, hfactorTwo]

/-- **THE AGGREGATION LIFT.**  A strict pair of aggregate atoms lifts to a
strict pair of parallel representatives whose scale-to-mass ratios do not pass
the aggregate ratios.  This is the core of the line-grouping reduction: the
minimizing atom of each line inherits strictness from its line aggregate. -/
theorem planePairDominatesStrict_of_ray {atomOne atomTwo : Fin 2 → ℝ}
    {scaleOne scaleTwo : ℝ} {factorOne factorTwo : ℝ}
    {repScaleOne repScaleTwo : ℝ}
    (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo)
    (hfacOne : factorOne ≠ 0) (hfacTwo : factorTwo ≠ 0)
    (hrepPosOne : 0 < repScaleOne) (hrepPosTwo : 0 < repScaleTwo)
    (hratioOne : repScaleOne * (atomOne ⬝ᵥ atomOne)
      ≤ scaleOne * ((factorOne • atomOne) ⬝ᵥ (factorOne • atomOne)))
    (hratioTwo : repScaleTwo * (atomTwo ⬝ᵥ atomTwo)
      ≤ scaleTwo * ((factorTwo • atomTwo) ⬝ᵥ (factorTwo • atomTwo)))
    (hdom : PlanePairDominatesStrict atomOne atomTwo scaleOne scaleTwo) :
    PlanePairDominatesStrict (factorOne • atomOne) (factorTwo • atomTwo)
      repScaleOne repScaleTwo := by
  obtain ⟨hgapOne, hgapTwo, hdet⟩ :=
    (planePairDominatesStrict_iff hposOne hposTwo).mp hdom
  have hmassOne : 0 < atomOne ⬝ᵥ atomOne := lt_trans hposOne hgapOne
  have hmassTwo : 0 < atomTwo ⬝ᵥ atomTwo := lt_trans hposTwo hgapTwo
  have hsqOne : (factorOne • atomOne) ⬝ᵥ (factorOne • atomOne)
      = factorOne ^ 2 * (atomOne ⬝ᵥ atomOne) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hsqTwo : (factorTwo • atomTwo) ⬝ᵥ (factorTwo • atomTwo)
      = factorTwo ^ 2 * (atomTwo ⬝ᵥ atomTwo) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hcross : (factorOne • atomOne) ⬝ᵥ (factorTwo • atomTwo)
      = factorOne * factorTwo * (atomOne ⬝ᵥ atomTwo) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hfacSqOne : 0 < factorOne ^ 2 := by positivity
  have hfacSqTwo : 0 < factorTwo ^ 2 := by positivity
  rw [hsqOne] at hratioOne
  rw [hsqTwo] at hratioTwo
  have hrepLeOne : repScaleOne ≤ scaleOne * factorOne ^ 2 := by
    have hkey : repScaleOne * (atomOne ⬝ᵥ atomOne)
        ≤ scaleOne * factorOne ^ 2 * (atomOne ⬝ᵥ atomOne) := by
      nlinarith [hratioOne]
    exact le_of_mul_le_mul_right (by nlinarith [hkey]) hmassOne
  have hrepLeTwo : repScaleTwo ≤ scaleTwo * factorTwo ^ 2 := by
    have hkey : repScaleTwo * (atomTwo ⬝ᵥ atomTwo)
        ≤ scaleTwo * factorTwo ^ 2 * (atomTwo ⬝ᵥ atomTwo) := by
      nlinarith [hratioTwo]
    exact le_of_mul_le_mul_right (by nlinarith [hkey]) hmassTwo
  refine (planePairDominatesStrict_iff hrepPosOne hrepPosTwo).mpr ⟨?_, ?_, ?_⟩
  · rw [hsqOne]
    nlinarith [hgapOne, hfacSqOne, hrepLeOne]
  · rw [hsqTwo]
    nlinarith [hgapTwo, hfacSqTwo, hrepLeTwo]
  · rw [hsqOne, hsqTwo, hcross]
    have hgapFacOne : factorOne ^ 2 * (atomOne ⬝ᵥ atomOne) - repScaleOne
        ≥ factorOne ^ 2 * (atomOne ⬝ᵥ atomOne - scaleOne) := by
      nlinarith [hrepLeOne]
    have hgapFacTwo : factorTwo ^ 2 * (atomTwo ⬝ᵥ atomTwo) - repScaleTwo
        ≥ factorTwo ^ 2 * (atomTwo ⬝ᵥ atomTwo - scaleTwo) := by
      nlinarith [hrepLeTwo]
    have hgapPosOne : 0 < factorOne ^ 2 * (atomOne ⬝ᵥ atomOne - scaleOne) := by
      nlinarith [hgapOne]
    have hgapPosTwo : 0 < factorTwo ^ 2 * (atomTwo ⬝ᵥ atomTwo - scaleTwo) := by
      nlinarith [hgapTwo]
    calc (factorOne * factorTwo * (atomOne ⬝ᵥ atomTwo)) ^ 2
        = factorOne ^ 2 * factorTwo ^ 2 * (atomOne ⬝ᵥ atomTwo) ^ 2 := by ring
      _ < factorOne ^ 2 * factorTwo ^ 2
          * ((atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo)) := by
          have hfac : 0 < factorOne ^ 2 * factorTwo ^ 2 := by positivity
          exact mul_lt_mul_of_pos_left hdet hfac
      _ = (factorOne ^ 2 * (atomOne ⬝ᵥ atomOne - scaleOne))
          * (factorTwo ^ 2 * (atomTwo ⬝ᵥ atomTwo - scaleTwo)) := by ring
      _ ≤ (factorOne ^ 2 * (atomOne ⬝ᵥ atomOne) - repScaleOne)
          * (factorTwo ^ 2 * (atomTwo ⬝ᵥ atomTwo) - repScaleTwo) := by
          nlinarith [hgapFacOne, hgapFacTwo, hgapPosOne, hgapPosTwo]

/-! ## Layer 8 — the strict engine at four nonparallel lines -/

section StrictEngine

variable {slotCount : ℕ}

/-- **THE SLACK CHAIN.**  One strictly slack active pair pushes the no-strict
budget STRICTLY below the active mass minus one.  This is the engine chain
with the slack pair carried through the double sum. -/
theorem plane_budget_lt_of_slack_pair
    (atom : Fin slotCount → (Fin 2 → ℝ)) (scale : Fin slotCount → ℝ)
    (hframe : PlaneParseval atom) (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) ≤ 1)
    (hnone : ∀ slotOne slotTwo, slotOne ≠ slotTwo →
      ¬ PlanePairDominatesStrict (atom slotOne) (atom slotTwo)
          (scale slotOne) (scale slotTwo))
    {slackOne slackTwo : Fin slotCount} (hslackNe : slackOne ≠ slackTwo)
    (hslackMemOne : slackOne ∈ planeActiveSet atom scale)
    (hslackMemTwo : slackTwo ∈ planeActiveSet atom scale)
    (hslack : (atom slackOne ⬝ᵥ atom slackOne - scale slackOne)
        * (atom slackTwo ⬝ᵥ atom slackTwo - scale slackTwo)
      < (atom slackOne ⬝ᵥ atom slackTwo) ^ 2) :
    (∑ slot ∈ planeActiveSet atom scale,
        scale slot * (2 * (atom slot ⬝ᵥ atom slot) - scale slot))
      < (∑ slot ∈ planeActiveSet atom scale, atom slot ⬝ᵥ atom slot) - 1 := by
  classical
  have hfail : ∀ slotOne ∈ planeActiveSet atom scale,
      ∀ slotTwo ∈ planeActiveSet atom scale, slotOne ≠ slotTwo →
      (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)
        ≤ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := by
    intro slotOne hone slotTwo htwo hne
    by_contra hbig
    rw [not_le] at hbig
    exact hnone slotOne slotTwo hne
      (planePairDominatesStrict_of_certificate (hpos slotOne) (hpos slotTwo)
        (mem_planeActiveSet.mp hone) (mem_planeActiveSet.mp htwo) hbig)
  have hrow : ∀ slotOne ∈ planeActiveSet atom scale,
      (∑ slotTwo ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
        ≤ atom slotOne ⬝ᵥ atom slotOne := by
    intro slotOne _
    have hsub : (∑ slotTwo ∈ planeActiveSet atom scale,
        (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
        ≤ ∑ slotTwo, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun slotTwo _ _ => sq_nonneg _)
    have hfull : (∑ slotTwo, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
        = atom slotOne ⬝ᵥ atom slotOne := by
      rw [← hframe.rowEnergy slotOne]
      exact Finset.sum_congr rfl fun slotTwo _ => by
        rw [dotProduct_comm (atom slotOne) (atom slotTwo), pow_two]
    rw [← hfull]
    exact hsub
  have hdouble : (∑ slotOne ∈ planeActiveSet atom scale,
      ∑ slotTwo ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
      ≤ ∑ slotOne ∈ planeActiveSet atom scale, atom slotOne ⬝ᵥ atom slotOne :=
    Finset.sum_le_sum hrow
  have hoffStrict : (∑ slotOne ∈ planeActiveSet atom scale,
      ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
        (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo))
      < ∑ slotOne ∈ planeActiveSet atom scale,
          ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
            (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro slotOne hone
      refine Finset.sum_le_sum fun slotTwo htwo => ?_
      exact hfail slotOne hone slotTwo (Finset.mem_of_mem_erase htwo)
        (Finset.ne_of_mem_erase htwo).symm
    · refine ⟨slackOne, hslackMemOne, Finset.sum_lt_sum ?_ ?_⟩
      · intro slotTwo htwo
        exact hfail slackOne hslackMemOne slotTwo (Finset.mem_of_mem_erase htwo)
          (Finset.ne_of_mem_erase htwo).symm
      · exact ⟨slackTwo, Finset.mem_erase.mpr ⟨hslackNe.symm, hslackMemTwo⟩, hslack⟩
  have hsplitAlign : ∀ slotOne ∈ planeActiveSet atom scale,
      (∑ slotTwo ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
        = (atom slotOne ⬝ᵥ atom slotOne) ^ 2
          + ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
              (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := fun slotOne hone =>
    (Finset.add_sum_erase _ (fun slotTwo => (atom slotOne ⬝ᵥ atom slotTwo) ^ 2) hone).symm
  have hsplitGap : ∀ slotOne ∈ planeActiveSet atom scale,
      (∑ slotTwo ∈ planeActiveSet atom scale,
        (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo))
        = (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          + ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
              (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
                * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) := fun slotOne hone =>
    (Finset.add_sum_erase _
      (fun slotTwo => (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
        * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)) hone).symm
  have hsquare : (∑ slotOne ∈ planeActiveSet atom scale,
        (atom slotOne ⬝ᵥ atom slotOne - scale slotOne))
      * (∑ slotTwo ∈ planeActiveSet atom scale,
          (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo))
      = ∑ slotOne ∈ planeActiveSet atom scale,
          ∑ slotTwo ∈ planeActiveSet atom scale,
            (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
              * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) :=
    Finset.sum_mul_sum _ _ _ _
  have htotalAlign : (∑ slotOne ∈ planeActiveSet atom scale,
      ∑ slotTwo ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
      = (∑ slotOne ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotOne) ^ 2)
        + ∑ slotOne ∈ planeActiveSet atom scale,
            ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
              (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hsplitAlign
  have htotalGap : (∑ slotOne ∈ planeActiveSet atom scale,
      ∑ slotTwo ∈ planeActiveSet atom scale,
        (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo))
      = (∑ slotOne ∈ planeActiveSet atom scale,
          (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotOne ⬝ᵥ atom slotOne - scale slotOne))
        + ∑ slotOne ∈ planeActiveSet atom scale,
            ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
              (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
                * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hsplitGap
  have hgapFloor := hframe.one_le_sum_active_gap scale hsmall
  have hgapSq : (∑ slotOne ∈ planeActiveSet atom scale,
        (atom slotOne ⬝ᵥ atom slotOne - scale slotOne))
      ≤ (∑ slotOne ∈ planeActiveSet atom scale,
          (atom slotOne ⬝ᵥ atom slotOne - scale slotOne))
        * (∑ slotTwo ∈ planeActiveSet atom scale,
            (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)) := by
    nlinarith [hgapFloor]
  have hpoint : (∑ slotOne ∈ planeActiveSet atom scale,
        (atom slotOne ⬝ᵥ atom slotOne) ^ 2)
      - ∑ slotOne ∈ planeActiveSet atom scale,
          (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
      = ∑ slotOne ∈ planeActiveSet atom scale,
          scale slotOne * (2 * (atom slotOne ⬝ᵥ atom slotOne) - scale slotOne) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun slotOne _ => by ring
  linarith [hdouble, htotalAlign, hoffStrict, htotalGap, hsquare, hgapSq, hgapFloor,
    hpoint]

/-- **THE STRICT ENGINE AT FOUR NONPARALLEL LINES.**  Four pairwise-nonparallel
active slots push the no-strict budget STRICTLY below the active mass minus
one.  The equality face of the engine forces every active pair tied, and the
landed four-atom kill turns four tied nonparallel atoms into a parallel pair:
the face is empty. -/
theorem plane_fourNonparallel_budget_lt
    (atom : Fin slotCount → (Fin 2 → ℝ)) (scale : Fin slotCount → ℝ)
    (hframe : PlaneParseval atom) (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) ≤ 1)
    (quad : Fin 4 → Fin slotCount) (hquadInj : Function.Injective quad)
    (hactive : ∀ corner, quad corner ∈ planeActiveSet atom scale)
    (hwedge : ∀ cornerOne cornerTwo, cornerOne ≠ cornerTwo →
      planeWedge (atom (quad cornerOne)) (atom (quad cornerTwo)) ≠ 0)
    (hnone : ∀ slotOne slotTwo, slotOne ≠ slotTwo →
      ¬ PlanePairDominatesStrict (atom slotOne) (atom slotTwo)
          (scale slotOne) (scale slotTwo)) :
    (∑ slot ∈ planeActiveSet atom scale,
        scale slot * (2 * (atom slot ⬝ᵥ atom slot) - scale slot))
      < (∑ slot ∈ planeActiveSet atom scale, atom slot ⬝ᵥ atom slot) - 1 := by
  classical
  have hfail : ∀ slotOne ∈ planeActiveSet atom scale,
      ∀ slotTwo ∈ planeActiveSet atom scale, slotOne ≠ slotTwo →
      (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)
        ≤ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := by
    intro slotOne hone slotTwo htwo hne
    by_contra hbig
    rw [not_le] at hbig
    exact hnone slotOne slotTwo hne
      (planePairDominatesStrict_of_certificate (hpos slotOne) (hpos slotTwo)
        (mem_planeActiveSet.mp hone) (mem_planeActiveSet.mp htwo) hbig)
  by_cases hslack : ∃ slackOne ∈ planeActiveSet atom scale,
      ∃ slackTwo ∈ planeActiveSet atom scale, slackOne ≠ slackTwo
        ∧ (atom slackOne ⬝ᵥ atom slackOne - scale slackOne)
            * (atom slackTwo ⬝ᵥ atom slackTwo - scale slackTwo)
          < (atom slackOne ⬝ᵥ atom slackTwo) ^ 2
  · obtain ⟨slackOne, honeMem, slackTwo, htwoMem, hne, hstrict⟩ := hslack
    exact plane_budget_lt_of_slack_pair atom scale hframe hpos hsmall hnone
      hne honeMem htwoMem hstrict
  · exfalso
    push Not at hslack
    have htied : ∀ slotOne ∈ planeActiveSet atom scale,
        ∀ slotTwo ∈ planeActiveSet atom scale, slotOne ≠ slotTwo →
        (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
          = (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
              * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) := by
      intro slotOne hone slotTwo htwo hne
      exact le_antisymm (hslack slotOne hone slotTwo htwo hne)
        (hfail slotOne hone slotTwo htwo hne)
    have hgap : ∀ corner : Fin 4,
        0 < atom (quad corner) ⬝ᵥ atom (quad corner) - scale (quad corner) := by
      intro corner
      have hmem := mem_planeActiveSet.mp (hactive corner)
      linarith
    have hpair : ∀ cornerOne cornerTwo : Fin 4, cornerOne ≠ cornerTwo →
        (atom (quad cornerOne) ⬝ᵥ atom (quad cornerTwo)) ^ 2
          = (atom (quad cornerOne) ⬝ᵥ atom (quad cornerOne) - scale (quad cornerOne))
              * (atom (quad cornerTwo) ⬝ᵥ atom (quad cornerTwo)
                  - scale (quad cornerTwo)) := by
      intro cornerOne cornerTwo hne
      exact htied (quad cornerOne) (hactive cornerOne) (quad cornerTwo)
        (hactive cornerTwo) fun heq => hne (hquadInj heq)
    rcases plane_four_allTied_parallel (hgap 0) (hgap 1) (hgap 2) (hgap 3)
        (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 0 3 (by decide))
        (hpair 1 2 (by decide)) (hpair 1 3 (by decide)) (hpair 2 3 (by decide)) with
      hzero | hzero | hzero | hzero | hzero | hzero
    · exact hwedge 0 1 (by decide) hzero
    · exact hwedge 0 2 (by decide) hzero
    · exact hwedge 0 3 (by decide) hzero
    · exact hwedge 1 2 (by decide) hzero
    · exact hwedge 1 3 (by decide) hzero
    · exact hwedge 2 3 (by decide) hzero

/-- **THE STRICT SELECTION AT FOUR NONPARALLEL LINES.**  When the budget
reaches the active mass minus one, four pairwise-nonparallel active slots
return a strict pair.  This upgrades the landed engine from a strict budget
hypothesis to a weak one on the four-line stratum. -/
theorem exists_strictDominatingPlanePair_of_fourNonparallel
    (atom : Fin slotCount → (Fin 2 → ℝ)) (scale : Fin slotCount → ℝ)
    (hframe : PlaneParseval atom) (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) ≤ 1)
    (quad : Fin 4 → Fin slotCount) (hquadInj : Function.Injective quad)
    (hactive : ∀ corner, quad corner ∈ planeActiveSet atom scale)
    (hwedge : ∀ cornerOne cornerTwo, cornerOne ≠ cornerTwo →
      planeWedge (atom (quad cornerOne)) (atom (quad cornerTwo)) ≠ 0)
    (hbudget : (∑ slot ∈ planeActiveSet atom scale, atom slot ⬝ᵥ atom slot) - 1
      ≤ ∑ slot ∈ planeActiveSet atom scale,
          scale slot * (2 * (atom slot ⬝ᵥ atom slot) - scale slot)) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominatesStrict (atom slotOne) (atom slotTwo)
          (scale slotOne) (scale slotTwo) := by
  by_contra hnone
  push Not at hnone
  have hnone' : ∀ slotOne slotTwo, slotOne ≠ slotTwo →
      ¬ PlanePairDominatesStrict (atom slotOne) (atom slotTwo)
          (scale slotOne) (scale slotTwo) := fun slotOne slotTwo hne hdom =>
    (hnone slotOne slotTwo hne) hdom
  have hlt := plane_fourNonparallel_budget_lt atom scale hframe hpos hsmall
    quad hquadInj hactive hwedge hnone'
  linarith [hbudget, hlt]

end StrictEngine

end Gtz
