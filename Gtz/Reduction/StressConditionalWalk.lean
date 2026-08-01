/-
# The stress-conditional walk, and the conic that manufactures a stress

`Gtz.exists_rescaledReducedDesign` (`Gtz.Reduction.StressWalk`) reduces a design
above the Veronese dimension by walking its weights along a direction that leaves
Parseval fixed.  Its size hypothesis `rank * (rank + 1) / 2 < size` is spent in
exactly ONE place -- manufacturing that direction out of a finrank count.  Take
the direction as a HYPOTHESIS and the walk runs at every size, in particular at
`(6, 3)`, where the count gives nothing because `3 * 4 / 2 = 6` on the nose.

That is worth doing because below six every cell is already a theorem.  So a
`(6,3)` design that HAPPENS to carry a stress reduces to size at most five and
`Gtz.gtzWeighted_of_le_five` closes it: `exists_dominating_sixThree_of_stress`.

The geometric reading is classical.  A stress is a linear dependency among the
six Veronese images `g_c g_c^T` inside the six-dimensional `Sym_3(R)`; dually,
six vectors of a six-dimensional space are dependent as soon as they all
annihilate one nonzero functional, and the functionals are the symmetric forms
`Q` under the Frobenius pairing `<g g^T, Q> = g^T Q g`.  So a common quadric
through all six directions -- six points of `RP^2` on one conic -- manufactures a
stress, and `exists_dominating_of_commonQuadric` turns it into a dominating
triple.  The half landed here is the half that EXCLUDES designs.

`exists_dominating_of_twoPlanes` spells out the degenerate line-pair case with no
conic vocabulary at all: two normals, each atom orthogonal to one of them.  It is
NOT visible to `Gtz.HasParallelPair` -- the atoms may be pairwise non-parallel and
still split into two coplanar triples.

NO COMPLEX ANALOGUE, and this is orientation prose, not a theorem of this file.
Over `C` the Veronese images are Hermitian and live in a NINE-dimensional real
space, so six of them carry no forced dependency and the conic reading is vacuous
-- the same dimension gap `6 = dim Sym_3(R)` against `9 = dim Herm_3(C)` that
powers the shipped fourth-moment realness quantum
`Gtz.hermitianMomentFloor_lt_realMomentFloor`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.SchurRankOne
import Gtz.Reduction.Crystallization
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.StressWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The walk with the stress supplied by hand -/

/-- **THE STRESS-CONDITIONAL WALK.**  `Gtz.exists_rescaledReducedDesign` with the
finrank count replaced by an explicit stress.  The body is the shipped proof from
the sign normalisation onward: the size hypothesis was consumed only by
`Gtz.exists_parsevalNullDirection`, and nothing downstream of that call mentions
the size at all. -/
theorem exists_rescaledReducedDesign_of_stress (design : WeightedDesign size rank)
    (hrankPos : 1 ≤ rank) {rawStress : Fin size → ℝ} (hrawNonzero : rawStress ≠ 0)
    (hrawParseval : (∑ c, rawStress c • atomMatrix (design.atom c)) = 0) :
    ∃ scale : ℝ, 0 < scale ∧ scale ≤ 1 ∧
      ∃ smallSize : ℕ, smallSize < size ∧ ∃ smallDesign : WeightedDesign smallSize rank,
        ∃ inject : Fin smallSize → Fin size, Function.Injective inject ∧
          ∀ i, smallDesign.atom i = Real.sqrt scale • design.atom (inject i) := by
  obtain ⟨stress, hnonzero, hstressParseval, hsumNonneg⟩ :
      ∃ stress : Fin size → ℝ, stress ≠ 0
        ∧ (∑ c, stress c • atomMatrix (design.atom c)) = 0 ∧ 0 ≤ ∑ c, stress c := by
    rcases le_or_gt 0 (∑ c, rawStress c) with hnonneg | hnegative
    · exact ⟨rawStress, hrawNonzero, hrawParseval, hnonneg⟩
    · refine ⟨-rawStress, neg_ne_zero.mpr hrawNonzero, ?_, ?_⟩
      · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrawParseval, neg_zero]
      · simp only [Pi.neg_apply, Finset.sum_neg_distrib]
        linarith
  obtain ⟨raiseLabel, hraiseLabel⟩ := exists_pos_of_sum_nonneg hnonzero hsumNonneg
  set raisers : Finset (Fin size) := Finset.univ.filter (fun c => 0 < stress c) with hraisers
  have hraisersNonempty : raisers.Nonempty :=
    ⟨raiseLabel, Finset.mem_filter.mpr ⟨Finset.mem_univ raiseLabel, hraiseLabel⟩⟩
  obtain ⟨stopLabel, hstopMem, hstopMin⟩ :=
    Finset.exists_min_image raisers (fun c => design.weight c / stress c) hraisersNonempty
  have hstressStop : 0 < stress stopLabel := (Finset.mem_filter.mp hstopMem).2
  set walkLength : ℝ := design.weight stopLabel / stress stopLabel with hwalkLength
  have hwalkLengthPos : 0 < walkLength := div_pos (design.weight_pos stopLabel) hstressStop
  set walked : Fin size → ℝ := fun c => design.weight c - walkLength * stress c with hwalked
  have hwalkedNonneg : ∀ c, 0 ≤ walked c := by
    intro c
    rcases le_or_gt (stress c) 0 with hnonpos | hpos
    · have hweight := design.weight_pos c
      simp only [hwalked]
      nlinarith
    · have hmem : c ∈ raisers := Finset.mem_filter.mpr ⟨Finset.mem_univ c, hpos⟩
      have hbound := (le_div_iff₀ hpos).mp (hstopMin c hmem)
      simp only [hwalked]
      linarith
  have hwalkedStop : walked stopLabel = 0 := by
    simp only [hwalked, hwalkLength]
    rw [div_mul_cancel₀ _ (ne_of_gt hstressStop), sub_self]
  have hwalkedParseval : ∑ c, walked c • atomMatrix (design.atom c) = 1 := by
    simp only [hwalked, sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hstressParseval, smul_zero, sub_zero,
      design.isParseval]
  set mass : ℝ := ∑ c, walked c with hmass
  have hmassLaw : mass = 1 - walkLength * (∑ c, stress c) := by
    simp only [hmass, hwalked]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, design.weight_sum_one]
  have hmassLeOne : mass ≤ 1 := by
    rw [hmassLaw]
    nlinarith [hwalkLengthPos, hsumNonneg]
  have hmassNonneg : 0 ≤ mass := Finset.sum_nonneg fun c _ => hwalkedNonneg c
  have hmassPos : 0 < mass := by
    rcases eq_or_lt_of_le hmassNonneg with hzero | hpos
    · exfalso
      have hallZero : ∀ c ∈ Finset.univ, walked c = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun c _ => hwalkedNonneg c).mp hzero.symm
      have hcollapse : (0 : Matrix (Fin rank) (Fin rank) ℝ) = 1 := by
        rw [← hwalkedParseval]
        exact (Finset.sum_eq_zero fun c hc => by
          rw [hallZero c hc, zero_smul]).symm
      have hentry := congrFun (congrFun hcollapse ⟨0, hrankPos⟩) ⟨0, hrankPos⟩
      rw [Matrix.zero_apply, Matrix.one_apply_eq] at hentry
      exact zero_ne_one hentry
    · exact hpos
  set support : Finset (Fin size) := Finset.univ.filter (fun c => 0 < walked c) with hsupport
  have hstopOutside : stopLabel ∉ support := by simp [hsupport, hwalkedStop]
  have hsizePos : 0 < size := Fin.pos stopLabel
  have hsupportLt : support.card < size := by
    have hsubset : support ⊆ Finset.univ.erase stopLabel := fun c hc =>
      Finset.mem_erase.mpr ⟨fun heq => hstopOutside (heq ▸ hc), Finset.mem_univ c⟩
    calc support.card ≤ (Finset.univ.erase stopLabel).card := Finset.card_le_card hsubset
      _ < size := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ stopLabel), Finset.card_univ,
            Fintype.card_fin]
          omega
  have houtside : ∀ c ∈ Finset.univ, c ∉ support → walked c = 0 := by
    intro c _ hc
    have hnotPos : ¬ 0 < walked c := fun hpos =>
      hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hpos⟩)
    exact le_antisymm (not_lt.mp hnotPos) (hwalkedNonneg c)
  have hsupportSum : ∑ c ∈ support, walked c = mass := by
    rw [Finset.sum_subset (Finset.subset_univ support) houtside]
  have hsupportParseval : ∑ c ∈ support, walked c • atomMatrix (design.atom c) = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ support)
      (fun c hcu hcs => by rw [houtside c hcu hcs, zero_smul])]
    exact hwalkedParseval
  have hatomScale : ∀ v : Fin rank → ℝ,
      atomMatrix (Real.sqrt mass • v) = mass • atomMatrix v := fun v => by
    rw [atomMatrix_smul, Real.sq_sqrt hmassPos.le]
  refine ⟨mass, hmassPos, hmassLeOne, support.card, hsupportLt,
    { atom := fun i => Real.sqrt mass • design.atom (support.orderIsoOfFin rfl i).val
      weight := fun i => walked (support.orderIsoOfFin rfl i).val / mass
      weight_pos := fun i =>
        div_pos (Finset.mem_filter.mp (support.orderIsoOfFin rfl i).2).2 hmassPos
      weight_sum_one := ?_
      isParseval := ?_ },
    fun i => (support.orderIsoOfFin rfl i).val,
    fun a b hab => (support.orderIsoOfFin rfl).toEquiv.injective
      (Subtype.val_injective hab),
    fun i => rfl⟩
  · rw [← Finset.sum_div, sum_orderIsoOfFin support rfl walked, hsupportSum,
      div_self (ne_of_gt hmassPos)]
  · calc ∑ i, (walked (support.orderIsoOfFin rfl i).val / mass)
            • atomMatrix (Real.sqrt mass • design.atom (support.orderIsoOfFin rfl i).val)
        = ∑ i, walked (support.orderIsoOfFin rfl i).val
            • atomMatrix (design.atom (support.orderIsoOfFin rfl i).val) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hatomScale, smul_smul, div_mul_cancel₀ _ (ne_of_gt hmassPos)]
      _ = 1 := by
          rw [sum_orderIsoOfFin support rfl
            (fun c => walked c • atomMatrix (design.atom c))]
          exact hsupportParseval

/-- **THE STRESS-CONDITIONAL RELATIVE STEP.**  `Gtz.gtzWeighted_of_forall_smaller` for
a single stressed design.  No size hypothesis at all: the walk lands strictly below
the design's own size, and every smaller cell is assumed. -/
theorem exists_dominating_of_stress (hrankPos : 1 ≤ rank)
    (hsmaller : ∀ smallSize, smallSize < size → GtzWeighted smallSize rank)
    (design : WeightedDesign size rank) {stress : Fin size → ℝ} (hnonzero : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0) :
    ∃ selected : Finset (Fin size), selected.card = rank ∧ Dominates design selected := by
  obtain ⟨scale, hpos, hle, smallSize, hlt, smallDesign, inject, hinject, hatoms⟩ :=
    exists_rescaledReducedDesign_of_stress design hrankPos hnonzero hstress
  obtain ⟨smallSelected, hcard, hdominates⟩ := hsmaller smallSize hlt smallDesign
  refine ⟨smallSelected.image inject, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinject, hcard]
  · show (subsetSum design (smallSelected.image inject) - 1).PosSemidef
    have hsums : subsetSum smallDesign smallSelected
        = scale • subsetSum design (smallSelected.image inject) := by
      rw [subsetSum, subsetSum, Finset.sum_image fun x _ y _ hxy => hinject hxy,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hatoms i, atomMatrix_smul, Real.sq_sqrt hpos.le]
    refine posSemidef_sub_one_of_smul_sub_one hpos hle ?_
    rw [← hsums]
    exact hdominates

/-- **A STRESSED `(6,3)` DESIGN IS DOMINATED**, with no open hypothesis: the walk
lands at size at most five and `Gtz.gtzWeighted_of_le_five` closes it.  This is the
whole transport of the reduction tool onto the terminal cell of rank three. -/
theorem exists_dominating_sixThree_of_stress (design : WeightedDesign 6 3)
    {stress : Fin 6 → ℝ} (hnonzero : stress ≠ 0)
    (hstress : (∑ c, stress c • atomMatrix (design.atom c)) = 0) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected :=
  exists_dominating_of_stress (by norm_num)
    (fun smallSize hlt => gtzWeighted_of_le_five smallSize 3 (by norm_num) (by omega))
    design hnonzero hstress

/-- **STRESS-FREENESS SUBSUMES `Gtz.HasParallelPair`.**  A parallel pair IS a stress:
`g_d = ratio . g_c` makes `atomMatrix g_d = ratio ^ 2 . atomMatrix g_c`, so
`e_d - ratio ^ 2 . e_c` annihilates Parseval. -/
theorem not_hasParallelPair_of_no_stress (design : WeightedDesign 6 3)
    (hnoStress : ∀ stress : Fin 6 → ℝ,
      (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0) :
    ¬ HasParallelPair design := by
  rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
  obtain ⟨stress, hstressValue⟩ : ∃ stress : Fin 6 → ℝ, ∀ c, stress c
      = (if c = dropLabel then (1 : ℝ) else 0) - (if c = keptLabel then ratio ^ 2 else 0) :=
    ⟨_, fun _ => rfl⟩
  have hnonzero : stress ≠ 0 := by
    intro hzero
    have hentry : stress dropLabel = 0 := congrFun hzero dropLabel
    rw [hstressValue dropLabel, if_pos rfl, if_neg (Ne.symm hdistinct)] at hentry
    norm_num at hentry
  refine hnonzero (hnoStress stress ?_)
  have hdrop : atomMatrix (design.atom dropLabel)
      = ratio ^ 2 • atomMatrix (design.atom keptLabel) := by
    rw [hparallel, atomMatrix_smul]
  rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) =>
    show stress c • atomMatrix (design.atom c)
        = (if c = dropLabel then atomMatrix (design.atom dropLabel) else 0)
          - (if c = keptLabel then ratio ^ 2 • atomMatrix (design.atom keptLabel) else 0) from by
      rw [hstressValue c]
      by_cases hdropCase : c = dropLabel
      · by_cases hkeptCase : c = keptLabel
        · exact absurd (hkeptCase ▸ hdropCase) hdistinct
        · rw [if_pos hdropCase, if_neg hkeptCase, if_pos hdropCase, if_neg hkeptCase, hdropCase]
          norm_num
      · by_cases hkeptCase : c = keptLabel
        · rw [if_neg hdropCase, if_pos hkeptCase, if_neg hdropCase, if_pos hkeptCase, hkeptCase,
            zero_sub, zero_sub, neg_smul]
        · rw [if_neg hdropCase, if_neg hkeptCase, if_neg hdropCase, if_neg hkeptCase,
            sub_zero, sub_zero, zero_smul]]
  rw [Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ dropLabel (fun _ => atomMatrix (design.atom dropLabel)),
    Finset.sum_ite_eq' Finset.univ keptLabel
      (fun _ => ratio ^ 2 • atomMatrix (design.atom keptLabel)),
    if_pos (Finset.mem_univ dropLabel), if_pos (Finset.mem_univ keptLabel), hdrop, sub_self]

/-! ## Seven symmetric forms in `Sym_3(R)` are dependent -/

/-- The upper-triangle coordinates of a linear combination of a fixed family: the
linear map whose kernel is the family's dependency space. -/
noncomputable def familyCoordMap (family : Fin size → Matrix (Fin rank) (Fin rank) ℝ) :
    (Fin size → ℝ) →ₗ[ℝ] ({ p : Fin rank × Fin rank // p.1 ≤ p.2 } → ℝ) where
  toFun coefficient := upperTriangleCoords (∑ index, coefficient index • family index)
  map_add' leftCoefficient rightCoefficient := by
    simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scale coefficient := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, ← Finset.smul_sum,
      map_smul]

/-- **MORE SYMMETRIC MATRICES THAN `rank * (rank + 1) / 2` ARE DEPENDENT.**  The
finrank count that powers `Gtz.exists_parsevalNullDirection`, freed from the
assumption that the family is made of rank-one atoms. -/
theorem exists_dependency_of_symmetric_family
    (family : Fin size → Matrix (Fin rank) (Fin rank) ℝ)
    (hsymmetric : ∀ index, (family index)ᵀ = family index)
    (hsize : rank * (rank + 1) / 2 < size) :
    ∃ coefficient : Fin size → ℝ, coefficient ≠ 0
      ∧ (∑ index, coefficient index • family index) = 0 := by
  have hnotInjective : ¬ Function.Injective (familyCoordMap family) := by
    intro hinjective
    have hbound := LinearMap.finrank_le_finrank_of_injective hinjective
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_fin, card_orderedPairs] at hbound
    exact absurd hsize (not_lt.mpr hbound)
  rw [← LinearMap.ker_eq_bot] at hnotInjective
  obtain ⟨coefficient, hmem, hnonzero⟩ := (Submodule.ne_bot_iff _).mp hnotInjective
  refine ⟨coefficient, hnonzero, ?_⟩
  have hcoords : upperTriangleCoords (∑ index, coefficient index • family index) = 0 :=
    LinearMap.mem_ker.mp hmem
  have hsymmetricSum : (∑ index, coefficient index • family index)ᵀ
      = ∑ index, coefficient index • family index := by
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun index _ => by
      rw [Matrix.transpose_smul, hsymmetric index]
  exact symmetric_eq_zero_of_coords_eq_zero hsymmetricSum hcoords

/-! ## The Frobenius pairing against a rank-one atom -/

/-- `<Q, g g^T>_F = g^T Q g`. -/
theorem trace_transpose_mul_atomMatrix (form : Matrix (Fin 3) (Fin 3) ℝ)
    (vector : Fin 3 → ℝ) :
    Matrix.trace (formᵀ * atomMatrix vector) = vector ⬝ᵥ (formᵀ *ᵥ vector) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    atomMatrix, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- A real square matrix with vanishing Frobenius norm is zero. -/
theorem eq_zero_of_trace_transpose_mul_self {form : Matrix (Fin rank) (Fin rank) ℝ}
    (htrace : Matrix.trace (formᵀ * form) = 0) : form = 0 := by
  have hexpand : Matrix.trace (formᵀ * form)
      = ∑ colIndex, ∑ rowIndex, form rowIndex colIndex ^ 2 := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun colIndex _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun rowIndex _ => by
      rw [Matrix.transpose_apply]; ring
  rw [hexpand] at htrace
  ext rowIndex colIndex
  have hcolumn : ∑ row, form row colIndex ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun col _ => Finset.sum_nonneg fun row _ => sq_nonneg (form row col))).mp
      htrace colIndex (Finset.mem_univ colIndex)
  have hentry : form rowIndex colIndex ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun row _ => sq_nonneg (form row colIndex))).mp hcolumn rowIndex (Finset.mem_univ rowIndex)
  rw [Matrix.zero_apply]
  exact pow_eq_zero_iff two_ne_zero |>.mp hentry

/-! ## A conic through all six directions manufactures a stress -/

/-- **A COMMON QUADRIC GIVES A STRESS.**  If a nonzero symmetric `form` kills every
atom's quadratic form, the six Veronese images live in the five-dimensional
hyperplane orthogonal to it inside `Sym_3(R)` and are therefore dependent.

The proof does not mention hyperplanes: it appends the form to the six images,
applies the seven-in-six dependency count, and pairs the resulting relation with
the form itself.  Every image pairs to zero by hypothesis, so the form's own
coefficient is killed by its nonzero Frobenius norm, and what survives is a
genuine stress. -/
theorem exists_stress_of_commonQuadric (atoms : Fin 6 → (Fin 3 → ℝ))
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form) (hnonzero : form ≠ 0)
    (hquadric : ∀ atomIndex, atoms atomIndex ⬝ᵥ (form *ᵥ atoms atomIndex) = 0) :
    ∃ stress : Fin 6 → ℝ, stress ≠ 0 ∧ (∑ c, stress c • atomMatrix (atoms c)) = 0 := by
  obtain ⟨coefficient, hnonzeroCoefficient, hrelation⟩ :=
    exists_dependency_of_symmetric_family
      (Fin.cons form (fun c => atomMatrix (atoms c)) : Fin 7 → Matrix (Fin 3) (Fin 3) ℝ)
      (by
        intro index
        refine Fin.cases ?_ ?_ index
        · rw [Fin.cons_zero]; exact hsymmetric
        · intro c
          rw [Fin.cons_succ]
          exact transpose_eq_of_isHermitian (posSemidef_atomMatrix (atoms c)).1)
      (by norm_num)
  have hexpand : (∑ index : Fin 7, coefficient index
        • (Fin.cons form (fun c => atomMatrix (atoms c)) :
            Fin 7 → Matrix (Fin 3) (Fin 3) ℝ) index)
      = coefficient 0 • form + ∑ c : Fin 6, coefficient c.succ • atomMatrix (atoms c) := by
    conv_lhs => rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  have hsplit : coefficient 0 • form
      + ∑ c : Fin 6, coefficient c.succ • atomMatrix (atoms c) = 0 := by
    rw [← hexpand]; exact hrelation
  have hnormNonzero : Matrix.trace (formᵀ * form) ≠ 0 := fun hzero =>
    hnonzero (eq_zero_of_trace_transpose_mul_self hzero)
  have hpaired : coefficient 0 * Matrix.trace (formᵀ * form) = 0 := by
    have hzero : Matrix.trace (formᵀ * (coefficient 0 • form
        + ∑ c : Fin 6, coefficient c.succ • atomMatrix (atoms c))) = 0 := by
      rw [hsplit, Matrix.mul_zero, Matrix.trace_zero]
    rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Matrix.mul_sum, Matrix.trace_sum] at hzero
    have htail : ∑ c : Fin 6, Matrix.trace (formᵀ * (coefficient c.succ
        • atomMatrix (atoms c))) = 0 := by
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
        trace_transpose_mul_atomMatrix, hsymmetric, hquadric c, mul_zero]
    rw [htail, add_zero] at hzero
    exact hzero
  have hhead : coefficient 0 = 0 := (mul_eq_zero.mp hpaired).resolve_right hnormNonzero
  refine ⟨fun c => coefficient c.succ, ?_, ?_⟩
  · intro hzero
    refine hnonzeroCoefficient (funext fun index => ?_)
    refine Fin.cases ?_ ?_ index
    · rw [Pi.zero_apply]; exact hhead
    · intro c
      rw [Pi.zero_apply]
      exact congrFun hzero c
  · rw [← hsplit, hhead, zero_smul, zero_add]

/-- **SIX DIRECTIONS ON A CONIC ARE DOMINATED.**  A `(6,3)` design whose six
directions all lie on one quadric HAS a dominating triple: the quadric
manufactures a stress and the stress-conditional walk closes it below size six. -/
theorem exists_dominating_of_commonQuadric (design : WeightedDesign 6 3)
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form) (hnonzero : form ≠ 0)
    (hquadric : ∀ atomIndex, design.atom atomIndex ⬝ᵥ (form *ᵥ design.atom atomIndex) = 0) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected := by
  obtain ⟨stress, hnonzeroStress, hstress⟩ :=
    exists_stress_of_commonQuadric design.atom hsymmetric hnonzero hquadric
  exact exists_dominating_sixThree_of_stress design hnonzeroStress hstress

/-! ## The degenerate case, spelled out with no conic vocabulary -/

/-- The symmetrised outer product of two normals: the quadratic form of a LINE PAIR. -/
noncomputable def linePairForm (firstNormal secondNormal : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.vecMulVec firstNormal secondNormal + Matrix.vecMulVec secondNormal firstNormal

theorem transpose_linePairForm (firstNormal secondNormal : Fin 3 → ℝ) :
    (linePairForm firstNormal secondNormal)ᵀ = linePairForm firstNormal secondNormal := by
  rw [linePairForm, Matrix.transpose_add]
  ext rowIndex colIndex
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply]
  ring

theorem quadForm_linePairForm (firstNormal secondNormal testVector : Fin 3 → ℝ) :
    testVector ⬝ᵥ (linePairForm firstNormal secondNormal *ᵥ testVector)
      = 2 * ((firstNormal ⬝ᵥ testVector) * (secondNormal ⬝ᵥ testVector)) := by
  simp only [linePairForm, dotProduct, Matrix.mulVec, Matrix.add_apply,
    Matrix.vecMulVec_apply, Fin.sum_univ_three]
  ring

/-- A line-pair form built from two nonzero normals is nonzero: pairing it across
the two normals returns `|n1|^2 |n2|^2 + <n1, n2>^2`, which Cauchy-Schwarz keeps
strictly positive. -/
theorem linePairForm_ne_zero {firstNormal secondNormal : Fin 3 → ℝ}
    (hfirst : firstNormal ≠ 0) (hsecond : secondNormal ≠ 0) :
    linePairForm firstNormal secondNormal ≠ 0 := by
  intro hzero
  have hpair : firstNormal ⬝ᵥ (linePairForm firstNormal secondNormal *ᵥ secondNormal)
      = (firstNormal ⬝ᵥ firstNormal) * (secondNormal ⬝ᵥ secondNormal)
        + (firstNormal ⬝ᵥ secondNormal) * (firstNormal ⬝ᵥ secondNormal) := by
    simp only [linePairForm, dotProduct, Matrix.mulVec, Matrix.add_apply,
      Matrix.vecMulVec_apply, Fin.sum_univ_three]
    ring
  rw [hzero, Matrix.zero_mulVec, dotProduct_zero] at hpair
  have hfirstPos : 0 < firstNormal ⬝ᵥ firstNormal := by
    obtain ⟨witness, hwitness⟩ := Function.ne_iff.mp hfirst
    refine lt_of_lt_of_le (?_ : (0:ℝ) < firstNormal witness ^ 2) ?_
    · exact lt_of_le_of_ne (sq_nonneg _) fun heq =>
        hwitness (pow_eq_zero_iff two_ne_zero |>.mp heq.symm)
    · rw [dotProduct]
      exact Finset.single_le_sum (f := fun index => firstNormal index * firstNormal index)
        (fun index _ => mul_self_nonneg _) (Finset.mem_univ witness) |>.trans_eq' (sq _).symm
  have hsecondPos : 0 < secondNormal ⬝ᵥ secondNormal := by
    obtain ⟨witness, hwitness⟩ := Function.ne_iff.mp hsecond
    refine lt_of_lt_of_le (?_ : (0:ℝ) < secondNormal witness ^ 2) ?_
    · exact lt_of_le_of_ne (sq_nonneg _) fun heq =>
        hwitness (pow_eq_zero_iff two_ne_zero |>.mp heq.symm)
    · rw [dotProduct]
      exact Finset.single_le_sum (f := fun index => secondNormal index * secondNormal index)
        (fun index _ => mul_self_nonneg _) (Finset.mem_univ witness) |>.trans_eq' (sq _).symm
  nlinarith [hpair, hfirstPos, hsecondPos, sq_nonneg (firstNormal ⬝ᵥ secondNormal)]

/-- **THE LINE-PAIR EXCLUSION.**  If every atom of a `(6,3)` design is orthogonal to
one of two fixed nonzero normals -- in particular if the six atoms split into two
COPLANAR TRIPLES -- then the design has a dominating triple.  No parallelism is
involved, so the shipped field `Gtz.HasParallelPair` does not see this. -/
theorem exists_dominating_of_twoPlanes (design : WeightedDesign 6 3)
    {firstNormal secondNormal : Fin 3 → ℝ} (hfirst : firstNormal ≠ 0)
    (hsecond : secondNormal ≠ 0)
    (hsplit : ∀ atomIndex, firstNormal ⬝ᵥ design.atom atomIndex = 0
      ∨ secondNormal ⬝ᵥ design.atom atomIndex = 0) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected := by
  refine exists_dominating_of_commonQuadric design
    (transpose_linePairForm firstNormal secondNormal)
    (linePairForm_ne_zero hfirst hsecond) fun atomIndex => ?_
  rw [quadForm_linePairForm]
  rcases hsplit atomIndex with hleft | hright
  · rw [hleft, zero_mul, mul_zero]
  · rw [hright, mul_zero, mul_zero]

end Gtz
