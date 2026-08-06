/-
# The corank-2 Naimark dual with its bracket dictionary, uniformly in the rank

Every weighted design at the corank-2 cell `(rank + 2, rank)` has an EXPLICIT
rank-two Naimark dual carrying

* **the pair dictionary** — a vanishing dual pair bracket certifies a
  nontrivial primal atom dependence supported off the pair;
* **the triple dictionary** (the general form of the five-coplanar endgame
  input) — three pairwise-vanishing dual brackets certify ONE dependence
  supported off all three labels at once, because three pairwise dependent
  rows of a rank-two completion span at most a line and therefore share a
  common orthogonal mix;
* **the strict-domination transfer** — a strictly dominating dual pair
  complements to a strictly dominating primal rank-subset.

This is the `(5,3)` package
`EndpointSpike.exists_naimarkDual_with_bracketDictionary`
(`Gtz/Ties/SpikeMatroidObstruction.lean`) re-founded at every rank: the
construction below replays that one line by line — whitener of the
co-Parseval operator (`Gtz.coParseval_posDef`), slack-scaled co-design rows,
orthonormal completion (`Gtz.exists_orthonormal_completion`, already
size-generic), weight-rescaled dual atoms — and none of its steps consumes
the value `rank = 3`.  The key structural fact: the dual of a corank-2 cell
has rank EXACTLY 2 at every primal rank, so the rank-two hinge
(`Gtz.rankTwoFourDirectionHinge_holds`) that downstream files feed with this
dual never recurses in the rank.

Cross-check at the end of the file: the `rank = 3` instance reproves the
exact statement of `EndpointSpike.exists_naimarkDual_with_bracketDictionary`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.Completion
import Gtz.Reduction.Naimark
import Gtz.Reduction.Crystallization
import Gtz.Reduction.SplitTransfer
import Gtz.Design.RankTwoTieCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace CorankTwo

open Matrix Finset Gtz

/-! ## The width-two orthonormal completion

`Gtz.exists_orthonormal_completion` types the completion at width
`sizeTotal - rank`, which at the corank-2 cell is propositionally but not
definitionally `2`.  This wrapper reindexes it to an honest `Fin 2`. -/

/-- **Orthonormal completion at corank 2.**  A matrix with orthonormal columns
whose height exceeds its width by exactly two completes by a width-TWO block. -/
theorem exists_orthonormal_completion_width_two {sizeTotal rank : ℕ}
    (hsize : sizeTotal = rank + 2) (coDesign : Matrix (Fin sizeTotal) (Fin rank) ℝ)
    (hortho : coDesignᵀ * coDesign = 1) :
    ∃ completion : Matrix (Fin sizeTotal) (Fin 2) ℝ,
      completionᵀ * completion = 1 ∧ coDesignᵀ * completion = 0
        ∧ coDesign * coDesignᵀ + completion * completionᵀ = 1 := by
  classical
  obtain ⟨wideCompletion, hwideOrtho, hwidePerp, hwideComplete⟩ :=
    exists_orthonormal_completion coDesign hortho
  have hwidth : sizeTotal - rank = 2 := by omega
  set widthEquiv : Fin 2 ≃ Fin (sizeTotal - rank) := finCongr hwidth.symm with hwidthEquiv
  refine ⟨wideCompletion.submatrix id widthEquiv, ?_, ?_, ?_⟩
  · ext colFst colSnd
    have hentry := congrFun (congrFun hwideOrtho (widthEquiv colFst)) (widthEquiv colSnd)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq] at hentry
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      id_eq, Matrix.one_apply] using hentry
  · ext coordIdx colIdx
    have hentry := congrFun (congrFun hwidePerp coordIdx) (widthEquiv colIdx)
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      id_eq, Matrix.zero_apply] using hentry
  · ext labelFst labelSnd
    have hentry := congrFun (congrFun hwideComplete labelFst) labelSnd
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.one_apply] at hentry
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.submatrix_apply, id_eq, Matrix.one_apply]
    rw [Equiv.sum_comp widthEquiv (fun wideCol =>
      wideCompletion labelFst wideCol * wideCompletion labelSnd wideCol)]
    exact hentry

/-! ## Common orthogonals of dependent rows in the plane

The completion has TWO columns, so its rows are plane vectors; a vanishing
`2 × 2` determinant of two rows yields a mix annihilating both, and three
pairwise-vanishing determinants yield ONE mix annihilating all three — the
rows span at most a line.  This last upgrade is what makes the triple
dictionary (and with it the general triangle endgame) possible. -/

/-- Two plane rows with vanishing determinant share a nonzero orthogonal mix. -/
theorem exists_commonOrthogonal_of_rowPair_det_eq_zero
    (rowFst rowSnd : Fin 2 → ℝ)
    (hdet : rowFst 0 * rowSnd 1 - rowFst 1 * rowSnd 0 = 0) :
    ∃ mixCoeff : Fin 2 → ℝ, mixCoeff ≠ 0
      ∧ rowFst 0 * mixCoeff 0 + rowFst 1 * mixCoeff 1 = 0
      ∧ rowSnd 0 * mixCoeff 0 + rowSnd 1 * mixCoeff 1 = 0 := by
  by_cases hfstLive : rowFst 0 ≠ 0 ∨ rowFst 1 ≠ 0
  · refine ⟨![rowFst 1, -(rowFst 0)], ?_, ?_, ?_⟩
    · intro hzero
      rcases hfstLive with hlive | hlive
      · exact hlive (by simpa [neg_eq_zero] using congrFun hzero (1 : Fin 2))
      · exact hlive (by simpa using congrFun hzero (0 : Fin 2))
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith [hdet]
  · push Not at hfstLive
    obtain ⟨hfstZeroA, hfstZeroB⟩ := hfstLive
    by_cases hsndLive : rowSnd 0 ≠ 0 ∨ rowSnd 1 ≠ 0
    · refine ⟨![rowSnd 1, -(rowSnd 0)], ?_, ?_, ?_⟩
      · intro hzero
        rcases hsndLive with hlive | hlive
        · exact hlive (by simpa [neg_eq_zero] using congrFun hzero (1 : Fin 2))
        · exact hlive (by simpa using congrFun hzero (0 : Fin 2))
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hfstZeroA, hfstZeroB]
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
    · push Not at hsndLive
      obtain ⟨hsndZeroA, hsndZeroB⟩ := hsndLive
      refine ⟨![1, 0], ?_, ?_, ?_⟩
      · intro hzero
        have hentry := congrFun hzero (0 : Fin 2)
        simp only [Matrix.cons_val_zero, Pi.zero_apply] at hentry
        exact one_ne_zero hentry
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hfstZeroA, hfstZeroB]
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hsndZeroA, hsndZeroB]
        ring

/-- **Three pairwise dependent plane rows share ONE orthogonal mix.**  Pairwise
vanishing determinants confine the three rows to a line, whose normal is the
mix.  This is the plane-geometry core of the triple dictionary. -/
theorem exists_commonOrthogonal_of_rowTriple_det_eq_zero
    (rowFst rowSnd rowThd : Fin 2 → ℝ)
    (hFstSnd : rowFst 0 * rowSnd 1 - rowFst 1 * rowSnd 0 = 0)
    (hFstThd : rowFst 0 * rowThd 1 - rowFst 1 * rowThd 0 = 0)
    (hSndThd : rowSnd 0 * rowThd 1 - rowSnd 1 * rowThd 0 = 0) :
    ∃ mixCoeff : Fin 2 → ℝ, mixCoeff ≠ 0
      ∧ rowFst 0 * mixCoeff 0 + rowFst 1 * mixCoeff 1 = 0
      ∧ rowSnd 0 * mixCoeff 0 + rowSnd 1 * mixCoeff 1 = 0
      ∧ rowThd 0 * mixCoeff 0 + rowThd 1 * mixCoeff 1 = 0 := by
  by_cases hfstLive : rowFst 0 ≠ 0 ∨ rowFst 1 ≠ 0
  · refine ⟨![rowFst 1, -(rowFst 0)], ?_, ?_, ?_, ?_⟩
    · intro hzero
      rcases hfstLive with hlive | hlive
      · exact hlive (by simpa [neg_eq_zero] using congrFun hzero (1 : Fin 2))
      · exact hlive (by simpa using congrFun hzero (0 : Fin 2))
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith [hFstSnd]
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith [hFstThd]
  · push Not at hfstLive
    obtain ⟨hfstZeroA, hfstZeroB⟩ := hfstLive
    obtain ⟨mixCoeff, hmixNe, hkillSnd, hkillThd⟩ :=
      exists_commonOrthogonal_of_rowPair_det_eq_zero rowSnd rowThd hSndThd
    refine ⟨mixCoeff, hmixNe, ?_, hkillSnd, hkillThd⟩
    rw [hfstZeroA, hfstZeroB]
    ring

/-! ## The mix-parametric dictionary

The classical Gale dictionary, with the vanishing locus parameterized by the
mix: any nonzero mix of the two completion columns produces a nontrivial
primal atom dependence, vanishing at every label whose completion row the mix
annihilates.  The `(5,3)` pair dictionary of
`Gtz/Ties/SpikeMatroidObstruction.lean` is the two-label instance; the triple
dictionary is the three-label instance through the row-triple common
orthogonal above. -/

/-- **The dictionary engine.**  A nonzero column mix of the completion yields a
nontrivial primal dependence vanishing wherever the mix annihilates the row. -/
theorem dependence_of_completion_mix {rank : ℕ}
    (design : WeightedDesign (rank + 2) rank)
    (whitener : Matrix (Fin rank) (Fin rank) ℝ) (hwhitenerUnit : IsUnit whitener.det)
    (coDesign : Matrix (Fin (rank + 2)) (Fin rank) ℝ)
    (hcoDesignShape : ∀ (label : Fin (rank + 2)) (coordIdx : Fin rank),
      coDesign label coordIdx
        = Real.sqrt (1 - design.weight label) * (whitenerᵀ *ᵥ design.atom label) coordIdx)
    (completion : Matrix (Fin (rank + 2)) (Fin 2) ℝ)
    (hcompletionOrtho : completionᵀ * completion = 1)
    (hcoDesignPerp : coDesignᵀ * completion = 0)
    (mixCoeff : Fin 2 → ℝ) (hmixNe : mixCoeff ≠ 0) :
    ∃ dependence : Fin (rank + 2) → ℝ,
      (∃ witnessLabel, dependence witnessLabel ≠ 0)
        ∧ (∀ label : Fin (rank + 2),
            completion label 0 * mixCoeff 0 + completion label 1 * mixCoeff 1 = 0 →
            dependence label = 0)
        ∧ (∑ label, dependence label • design.atom label) = 0 := by
  classical
  have hslackPos : ∀ label : Fin (rank + 2), 0 < 1 - design.weight label := fun label => by
    linarith [weight_lt_one design (by omega) label]
  -- the kernel vector of the co-design transpose
  set kernelVec : Fin (rank + 2) → ℝ := completion *ᵥ mixCoeff with hkernelVecDef
  have hkernelRow : ∀ label : Fin (rank + 2), kernelVec label
      = completion label 0 * mixCoeff 0 + completion label 1 * mixCoeff 1 := by
    intro label
    show ∑ colIdx, completion label colIdx * mixCoeff colIdx = _
    rw [Fin.sum_univ_two]
  have hkernelNe : kernelVec ≠ 0 := by
    intro hzero
    refine hmixNe ?_
    have hpull := congrArg (fun vec => completionᵀ *ᵥ vec) hzero
    simp only [Matrix.mulVec_zero] at hpull
    rwa [hkernelVecDef, Matrix.mulVec_mulVec, hcompletionOrtho, Matrix.one_mulVec] at hpull
  have hcoKernel : coDesignᵀ *ᵥ kernelVec = 0 := by
    rw [hkernelVecDef, Matrix.mulVec_mulVec, hcoDesignPerp, Matrix.zero_mulVec]
  -- the dependence, with the slack roots folded in
  refine ⟨fun label => kernelVec label * Real.sqrt (1 - design.weight label), ?_, ?_, ?_⟩
  · obtain ⟨witnessLabel, hwitness⟩ := Function.ne_iff.mp hkernelNe
    simp only [Pi.zero_apply] at hwitness
    exact ⟨witnessLabel,
      mul_ne_zero hwitness (Real.sqrt_pos.mpr (hslackPos witnessLabel)).ne'⟩
  · intro label hrowZero
    show kernelVec label * Real.sqrt (1 - design.weight label) = 0
    rw [hkernelRow label, hrowZero, zero_mul]
  · -- the whitener transports the co-design kernel to the atom dependence
    have hcoordZero : ∀ coordIdx : Fin rank,
        ∑ label, (kernelVec label * Real.sqrt (1 - design.weight label))
          * (whitenerᵀ *ᵥ design.atom label) coordIdx = 0 := by
      intro coordIdx
      have hentry := congrFun hcoKernel coordIdx
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hentry
      rw [← hentry]
      refine Finset.sum_congr rfl fun label _ => ?_
      rw [hcoDesignShape label coordIdx]
      ring
    have hwhitenedSum : whitenerᵀ *ᵥ (∑ label,
        (kernelVec label * Real.sqrt (1 - design.weight label)) • design.atom label) = 0 := by
      rw [← Matrix.mulVecLin_apply, map_sum]
      funext coordIdx
      simp only [Finset.sum_apply, LinearMap.map_smul, Matrix.mulVecLin_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hcoordZero coordIdx
    by_contra hsumNe
    have hdetZero : (whitenerᵀ).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hsumNe, hwhitenedSum⟩
    rw [Matrix.det_transpose] at hdetZero
    exact (isUnit_iff_ne_zero.mp hwhitenerUnit) hdetZero

/-- A vanishing dual pair bracket forces the determinant of the two completion
rows to vanish — the bracket is a positive multiple of that determinant. -/
theorem completionRowDet_eq_zero_of_pairBracket_eq_zero {rank : ℕ}
    (design : WeightedDesign (rank + 2) rank)
    (completion : Matrix (Fin (rank + 2)) (Fin 2) ℝ)
    (dualDesign : WeightedDesign (rank + 2) 2)
    (hdualAtom : ∀ label : Fin (rank + 2), dualDesign.atom label
        = (Real.sqrt (design.weight label))⁻¹ • (fun colIdx => completion label colIdx))
    (pairFst pairSnd : Fin (rank + 2))
    (hbracket : pairBracket dualDesign pairFst pairSnd = 0) :
    completion pairFst 0 * completion pairSnd 1
      - completion pairFst 1 * completion pairSnd 0 = 0 := by
  have hrootPos : ∀ label : Fin (rank + 2), 0 < Real.sqrt (design.weight label) :=
    fun label => Real.sqrt_pos.mpr (design.weight_pos label)
  have hexpand : pairBracket dualDesign pairFst pairSnd
      = (Real.sqrt (design.weight pairFst))⁻¹ * (Real.sqrt (design.weight pairSnd))⁻¹
        * (completion pairFst 0 * completion pairSnd 1
            - completion pairFst 1 * completion pairSnd 0) := by
    rw [pairBracket, hdualAtom pairFst, hdualAtom pairSnd]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexpand] at hbracket
  rcases mul_eq_zero.mp hbracket with hscale | hdet
  · exfalso
    rcases mul_eq_zero.mp hscale with hfst | hsnd
    · exact (inv_ne_zero (hrootPos pairFst).ne') hfst
    · exact (inv_ne_zero (hrootPos pairSnd).ne') hsnd
  · exact hdet

/-! ## The strict-domination transfer, uniformly in the rank

The four-congruence chain of `Gtz.weighted_naimark_duality`, walked once in
the definite verdict in the dual-to-primal direction — the port of
`EndpointSpike.posDef_primalGap_of_posDef_dualPairGap` with `5 → rank + 2`,
`3 → rank`; no step consumes the rank's value. -/

/-- **The transfer half**: a strictly dominating dual pair complements to a
strictly dominating primal rank-subset, at every rank. -/
theorem posDef_primalGap_of_posDef_dualPairGap {rank : ℕ}
    (design : WeightedDesign (rank + 2) rank)
    (whitener : Matrix (Fin rank) (Fin rank) ℝ) (hwhitenerUnit : IsUnit whitener.det)
    (hwhitened : whitenerᵀ
        * (∑ label, (1 - design.weight label) • atomMatrix (design.atom label))
        * whitener = 1)
    (coDesign : Matrix (Fin (rank + 2)) (Fin rank) ℝ)
    (hcoDesignShape : ∀ (label : Fin (rank + 2)) (coordIdx : Fin rank),
      coDesign label coordIdx
        = Real.sqrt (1 - design.weight label) * (whitenerᵀ *ᵥ design.atom label) coordIdx)
    (completion : Matrix (Fin (rank + 2)) (Fin 2) ℝ)
    (hcomplete : coDesign * coDesignᵀ + completion * completionᵀ = 1)
    (dualDesign : WeightedDesign (rank + 2) 2)
    (hdualAtom : ∀ label : Fin (rank + 2), dualDesign.atom label
        = (Real.sqrt (design.weight label))⁻¹ • (fun colIdx => completion label colIdx))
    (dualPair : Finset (Fin (rank + 2))) (hpairCard : dualPair.card = 2)
    (hdom : (Gtz.subsetSum dualDesign dualPair - 1).PosDef) :
    (Gtz.subsetSum design dualPairᶜ - 1).PosDef := by
  classical
  have hslackPos : ∀ label : Fin (rank + 2), 0 < 1 - design.weight label := fun label => by
    linarith [weight_lt_one design (by omega) label]
  have hrootPos : ∀ label : Fin (rank + 2), 0 < Real.sqrt (design.weight label) :=
    fun label => Real.sqrt_pos.mpr (design.weight_pos label)
  -- the pair enumeration and the two stacked row matrices
  set enumPair : Fin 2 → Fin (rank + 2) :=
    fun slotIdx => ((dualPair.orderIsoOfFin hpairCard) slotIdx).val with henumPairDef
  have henumMem : ∀ slotIdx, enumPair slotIdx ∈ dualPair := fun slotIdx =>
    ((dualPair.orderIsoOfFin hpairCard) slotIdx).2
  have henumInj : Function.Injective enumPair := fun slotIdx slotIdx' heq =>
    (dualPair.orderIsoOfFin hpairCard).toEquiv.injective (Subtype.val_injective heq)
  set whitenedRows : Matrix (Fin 2) (Fin rank) ℝ :=
    Matrix.of (fun slotIdx coordIdx =>
      (whitenerᵀ *ᵥ design.atom (enumPair slotIdx)) coordIdx) with hwhitenedRowsDef
  set dualRows : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.of (fun slotIdx colIdx =>
      (Real.sqrt (design.weight (enumPair slotIdx)))⁻¹ * completion (enumPair slotIdx) colIdx)
    with hdualRowsDef
  -- STEP 0: the complement dictionary
  have hgapSplit : Gtz.subsetSum design dualPairᶜ - 1
      = (∑ label, (1 - design.weight label) • atomMatrix (design.atom label))
        - Gtz.subsetSum design dualPair := by
    have hweightless : (∑ label, (1 - design.weight label) • atomMatrix (design.atom label))
        = (∑ label, atomMatrix (design.atom label)) - 1 := by
      rw [← design.isParseval, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun label _ => by rw [sub_smul, one_smul]
    have htotalSplit : (∑ label, atomMatrix (design.atom label))
        = Gtz.subsetSum design dualPair + Gtz.subsetSum design dualPairᶜ :=
      (Finset.sum_add_sum_compl dualPair _).symm
    rw [hweightless, htotalSplit]
    abel
  -- STEP 1: congruence by the whitener
  have hcoParsevalSymm : ((∑ label, (1 - design.weight label) • atomMatrix (design.atom label))
      - Gtz.subsetSum design dualPair)ᵀ
      = (∑ label, (1 - design.weight label) • atomMatrix (design.atom label))
        - Gtz.subsetSum design dualPair := by
    rw [Matrix.transpose_sub, Matrix.transpose_sum, Gtz.subsetSum, Matrix.transpose_sum]
    congr 1
    · exact Finset.sum_congr rfl fun label _ => by
        rw [Matrix.transpose_smul,
          transpose_eq_of_isHermitian (posSemidef_atomMatrix (design.atom label)).1]
    · exact Finset.sum_congr rfl fun label _ =>
        transpose_eq_of_isHermitian (posSemidef_atomMatrix (design.atom label)).1
  have hwhitenerConj : whitenerᵀ
      * ((∑ label, (1 - design.weight label) • atomMatrix (design.atom label))
          - Gtz.subsetSum design dualPair) * whitener
      = 1 - whitenedRowsᵀ * whitenedRows := by
    have hrowsGram : whitenedRowsᵀ * whitenedRows
        = ∑ label ∈ dualPair, atomMatrix (whitenerᵀ *ᵥ design.atom label) := by
      rw [transpose_mul_self_eq_sum_rows,
        ← sum_orderIsoOfFin dualPair hpairCard
          (fun label => atomMatrix (whitenerᵀ *ᵥ design.atom label))]
      exact Finset.sum_congr rfl fun slotIdx _ =>
        congrArg atomMatrix (funext fun coordIdx => by
          simp [hwhitenedRowsDef, henumPairDef])
    have hconjSum : whitenerᵀ * Gtz.subsetSum design dualPair * whitener
        = ∑ label ∈ dualPair, atomMatrix (whitenerᵀ *ᵥ design.atom label) := by
      rw [Gtz.subsetSum, Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl fun label _ => transpose_mul_atomMatrix_mul whitener _
    rw [Matrix.mul_sub, Matrix.sub_mul, hwhitened, hconjSum, hrowsGram]
  -- STEP 2 entries: the co-design and completion Gram formulas
  have hcoGramEntry : ∀ label label' : Fin (rank + 2), (coDesign * coDesignᵀ) label label'
      = Real.sqrt (1 - design.weight label) * Real.sqrt (1 - design.weight label')
        * ((whitenerᵀ *ᵥ design.atom label) ⬝ᵥ (whitenerᵀ *ᵥ design.atom label')) := by
    intro label label'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun coordIdx _ => ?_
    rw [hcoDesignShape label coordIdx, hcoDesignShape label' coordIdx]
    ring
  have hwhitenedGramEntry : ∀ slotIdx slotIdx' : Fin 2,
      (whitenedRows * whitenedRowsᵀ) slotIdx slotIdx'
        = (whitenerᵀ *ᵥ design.atom (enumPair slotIdx))
            ⬝ᵥ (whitenerᵀ *ᵥ design.atom (enumPair slotIdx')) := by
    intro slotIdx slotIdx'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hwhitenedRowsDef,
      Matrix.of_apply, dotProduct]
  have hdualGramEntry : ∀ slotIdx slotIdx' : Fin 2,
      (dualRows * dualRowsᵀ) slotIdx slotIdx'
        = (Real.sqrt (design.weight (enumPair slotIdx)))⁻¹
          * (Real.sqrt (design.weight (enumPair slotIdx')))⁻¹
          * ∑ colIdx, completion (enumPair slotIdx) colIdx
              * completion (enumPair slotIdx') colIdx := by
    intro slotIdx slotIdx'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hdualRowsDef,
      Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun colIdx _ => by ring
  -- STEP 2: diagonal congruence by the slack roots
  have hdiagSlack : (Matrix.diagonal
        (fun slotIdx => Real.sqrt (1 - design.weight (enumPair slotIdx))))ᵀ
        * (1 - whitenedRows * whitenedRowsᵀ)
        * Matrix.diagonal (fun slotIdx => Real.sqrt (1 - design.weight (enumPair slotIdx)))
      = Matrix.diagonal (fun slotIdx => 1 - design.weight (enumPair slotIdx))
        - Matrix.of (fun slotIdx slotIdx' =>
            (coDesign * coDesignᵀ) (enumPair slotIdx) (enumPair slotIdx')) := by
    rw [Matrix.diagonal_transpose]
    ext slotIdx slotIdx'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.of_apply]
    rw [hwhitenedGramEntry slotIdx slotIdx', hcoGramEntry (enumPair slotIdx) (enumPair slotIdx')]
    rcases eq_or_ne slotIdx slotIdx' with rfl | hne
    · rw [if_pos rfl, if_pos rfl]
      have hss := Real.mul_self_sqrt (hslackPos (enumPair slotIdx)).le
      linear_combination hss
    · rw [if_neg hne, if_neg hne]
      ring
  -- STEP 3: completeness swaps the co-design block for the completion block
  have hcompleteEntry : ∀ slotIdx slotIdx' : Fin 2,
      (coDesign * coDesignᵀ) (enumPair slotIdx) (enumPair slotIdx')
        + (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx')
      = if slotIdx = slotIdx' then 1 else 0 := by
    intro slotIdx slotIdx'
    have hentry := congrFun (congrFun hcomplete (enumPair slotIdx)) (enumPair slotIdx')
    rw [Matrix.add_apply, Matrix.one_apply] at hentry
    rwa [if_congr ⟨fun heq => henumInj heq, fun heq => heq ▸ rfl⟩ rfl rfl] at hentry
  have hblockSwap : Matrix.diagonal (fun slotIdx => 1 - design.weight (enumPair slotIdx))
        - Matrix.of (fun slotIdx slotIdx' =>
            (coDesign * coDesignᵀ) (enumPair slotIdx) (enumPair slotIdx'))
      = Matrix.of (fun slotIdx slotIdx' =>
            (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx'))
        - Matrix.diagonal (fun slotIdx => design.weight (enumPair slotIdx)) := by
    ext slotIdx slotIdx'
    simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply]
    have hentry := hcompleteEntry slotIdx slotIdx'
    rcases eq_or_ne slotIdx slotIdx' with rfl | hne
    · rw [if_pos rfl] at hentry
      rw [if_pos rfl, if_pos rfl]
      linarith
    · rw [if_neg hne] at hentry
      rw [if_neg hne, if_neg hne]
      linarith
  -- STEP 4: diagonal congruence by the inverse weight roots
  have hdiagWeight : (Matrix.diagonal
        (fun slotIdx => (Real.sqrt (design.weight (enumPair slotIdx)))⁻¹))ᵀ
        * (Matrix.of (fun slotIdx slotIdx' =>
              (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx'))
            - Matrix.diagonal (fun slotIdx => design.weight (enumPair slotIdx)))
        * Matrix.diagonal (fun slotIdx => (Real.sqrt (design.weight (enumPair slotIdx)))⁻¹)
      = dualRows * dualRowsᵀ - 1 := by
    rw [Matrix.diagonal_transpose]
    ext slotIdx slotIdx'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.of_apply]
    rw [hdualGramEntry slotIdx slotIdx',
      show (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx')
          = ∑ colIdx, completion (enumPair slotIdx) colIdx
              * completion (enumPair slotIdx') colIdx from by
        simp [Matrix.mul_apply, Matrix.transpose_apply]]
    rcases eq_or_ne slotIdx slotIdx' with rfl | hne
    · rw [if_pos rfl, if_pos rfl]
      have hroot := Real.mul_self_sqrt (design.weight_pos (enumPair slotIdx)).le
      have hcancel : (Real.sqrt (design.weight (enumPair slotIdx)))⁻¹
          * design.weight (enumPair slotIdx)
          * (Real.sqrt (design.weight (enumPair slotIdx)))⁻¹ = 1 := by
        rw [show (Real.sqrt (design.weight (enumPair slotIdx)))⁻¹
              * design.weight (enumPair slotIdx)
              * (Real.sqrt (design.weight (enumPair slotIdx)))⁻¹
            = design.weight (enumPair slotIdx) * (Real.sqrt (design.weight (enumPair slotIdx))
                * Real.sqrt (design.weight (enumPair slotIdx)))⁻¹ from by
          rw [mul_inv]; ring,
          hroot, mul_inv_cancel₀ (design.weight_pos (enumPair slotIdx)).ne']
      linear_combination (-1 : ℝ) * hcancel
    · rw [if_neg hne, if_neg hne]
      ring
  -- STEP 5: the dual rows realize the dual subset sum
  have hdualRowsGram : dualRowsᵀ * dualRows = Gtz.subsetSum dualDesign dualPair := by
    rw [transpose_mul_self_eq_sum_rows, Gtz.subsetSum,
      ← sum_orderIsoOfFin dualPair hpairCard
        (fun label => atomMatrix (dualDesign.atom label))]
    refine Finset.sum_congr rfl fun slotIdx _ =>
      congrArg atomMatrix (funext fun colIdx => ?_)
    rw [hdualAtom (enumPair slotIdx)]
    simp [hdualRowsDef, henumPairDef, Pi.smul_apply, smul_eq_mul]
  -- symmetry and determinant side conditions
  have hgapSymmOne : (1 - whitenedRows * whitenedRowsᵀ)ᵀ
      = 1 - whitenedRows * whitenedRowsᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hcompletionGramSymm : (completion * completionᵀ)ᵀ = completion * completionᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hgapSymmTwo : (Matrix.of (fun slotIdx slotIdx' =>
          (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx'))
        - Matrix.diagonal (fun slotIdx => design.weight (enumPair slotIdx)))ᵀ
      = Matrix.of (fun slotIdx slotIdx' =>
            (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx'))
        - Matrix.diagonal (fun slotIdx => design.weight (enumPair slotIdx)) := by
    rw [Matrix.transpose_sub, Matrix.diagonal_transpose]
    congr 1
    ext slotIdx slotIdx'
    rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
    have hsym := congrFun (congrFun hcompletionGramSymm (enumPair slotIdx)) (enumPair slotIdx')
    rw [Matrix.transpose_apply] at hsym
    exact hsym
  have hdetSlack : IsUnit (Matrix.diagonal
      (fun slotIdx => Real.sqrt (1 - design.weight (enumPair slotIdx)))).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun slotIdx _ =>
      (Real.sqrt_pos.mpr (hslackPos (enumPair slotIdx))).ne'
  have hdetWeight : IsUnit (Matrix.diagonal
      (fun slotIdx => (Real.sqrt (design.weight (enumPair slotIdx)))⁻¹)).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun slotIdx _ =>
      inv_ne_zero (hrootPos (enumPair slotIdx)).ne'
  -- the chain, dual to primal, in the definite verdict
  have hstepSix : (dualRowsᵀ * dualRows - 1).PosDef := by
    rw [hdualRowsGram]
    exact hdom
  have hstepFive : (dualRows * dualRowsᵀ - 1).PosDef :=
    (posDef_transpose_mul_sub_one_comm dualRows).mp hstepSix
  have hstepFour : (Matrix.of (fun slotIdx slotIdx' =>
        (completion * completionᵀ) (enumPair slotIdx) (enumPair slotIdx'))
      - Matrix.diagonal (fun slotIdx => design.weight (enumPair slotIdx))).PosDef :=
    (posDef_congr_right hgapSymmTwo hdetWeight).mpr (by rw [hdiagWeight]; exact hstepFive)
  have hstepThree : (1 - whitenedRows * whitenedRowsᵀ).PosDef :=
    (posDef_congr_right hgapSymmOne hdetSlack).mpr
      (by rw [hdiagSlack, hblockSwap]; exact hstepFour)
  have hstepTwo : (1 - whitenedRowsᵀ * whitenedRows).PosDef :=
    (posDef_one_sub_transpose_comm whitenedRows).mpr hstepThree
  have hstepOne : ((∑ label, (1 - design.weight label) • atomMatrix (design.atom label))
      - Gtz.subsetSum design dualPair).PosDef :=
    (posDef_congr_right hcoParsevalSymm hwhitenerUnit).mpr
      (by rw [hwhitenerConj]; exact hstepTwo)
  rw [hgapSplit]
  exact hstepOne

/-! ## The packaged corank-2 dual, all ranks -/

/-- **THE CORANK-2 NAIMARK DESCENT PACKAGE, UNIFORMLY IN THE RANK.**  Every
weighted design at the corank-2 cell has an explicit rank-two Naimark dual
carrying the pair dictionary, the triple dictionary, and the
strict-domination transfer.  The `rank = 3` instance is
`EndpointSpike.exists_naimarkDual_with_bracketDictionary` extended by the
triple clause; the cross-check below rederives that statement verbatim. -/
theorem exists_naimarkDualCorankTwo (rank : ℕ)
    (design : WeightedDesign (rank + 2) rank) :
    ∃ dualDesign : WeightedDesign (rank + 2) 2,
      (∀ pairFst pairSnd : Fin (rank + 2),
        pairBracket dualDesign pairFst pairSnd = 0 →
        ∃ dependence : Fin (rank + 2) → ℝ,
          (∃ witnessLabel, dependence witnessLabel ≠ 0)
            ∧ dependence pairFst = 0 ∧ dependence pairSnd = 0
            ∧ (∑ label, dependence label • design.atom label) = 0)
      ∧ (∀ triFst triSnd triThd : Fin (rank + 2),
          pairBracket dualDesign triFst triSnd = 0 →
          pairBracket dualDesign triFst triThd = 0 →
          pairBracket dualDesign triSnd triThd = 0 →
          ∃ dependence : Fin (rank + 2) → ℝ,
            (∃ witnessLabel, dependence witnessLabel ≠ 0)
              ∧ dependence triFst = 0 ∧ dependence triSnd = 0 ∧ dependence triThd = 0
              ∧ (∑ label, dependence label • design.atom label) = 0)
      ∧ ∀ dualPair : Finset (Fin (rank + 2)), dualPair.card = 2 →
          (Gtz.subsetSum dualDesign dualPair - 1).PosDef →
          (Gtz.subsetSum design dualPairᶜ - 1).PosDef := by
  classical
  have hslackPos : ∀ label : Fin (rank + 2), 0 < 1 - design.weight label := fun label => by
    linarith [weight_lt_one design (by omega) label]
  obtain ⟨whitener, hwhitenerUnit, hwhitened⟩ :=
    exists_congruence_to_one (coParseval_posDef design (by omega))
  set coDesign : Matrix (Fin (rank + 2)) (Fin rank) ℝ :=
    Matrix.of (fun label coordIdx =>
      Real.sqrt (1 - design.weight label) * (whitenerᵀ *ᵥ design.atom label) coordIdx)
    with hcoDesignDef
  have hcoDesignShape : ∀ (label : Fin (rank + 2)) (coordIdx : Fin rank),
      coDesign label coordIdx
        = Real.sqrt (1 - design.weight label) * (whitenerᵀ *ᵥ design.atom label) coordIdx :=
    fun label coordIdx => rfl
  have hconjSum : whitenerᵀ
      * (∑ label, (1 - design.weight label) • atomMatrix (design.atom label)) * whitener
      = ∑ label, (1 - design.weight label) • atomMatrix (whitenerᵀ *ᵥ design.atom label) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, transpose_mul_atomMatrix_mul]
  have hcoDesignOrtho : coDesignᵀ * coDesign = 1 := by
    rw [← hwhitened, hconjSum]
    ext coordIdx coordIdx'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hcoDesignDef, Matrix.of_apply,
      Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [show Real.sqrt (1 - design.weight label) * (whitenerᵀ *ᵥ design.atom label) coordIdx
          * (Real.sqrt (1 - design.weight label) * (whitenerᵀ *ᵥ design.atom label) coordIdx')
        = (Real.sqrt (1 - design.weight label) * Real.sqrt (1 - design.weight label))
          * ((whitenerᵀ *ᵥ design.atom label) coordIdx
              * (whitenerᵀ *ᵥ design.atom label) coordIdx') from by ring,
      Real.mul_self_sqrt (hslackPos label).le]
  obtain ⟨completion, hcompletionOrtho, hcoDesignPerp, hcomplete⟩ :=
    exists_orthonormal_completion_width_two rfl coDesign hcoDesignOrtho
  refine ⟨{ atom := fun label => (Real.sqrt (design.weight label))⁻¹
              • (fun colIdx => completion label colIdx)
            weight := design.weight
            weight_pos := design.weight_pos
            weight_sum_one := design.weight_sum_one
            isParseval := ?_ }, ?_, ?_, ?_⟩
  · calc ∑ label, design.weight label
        • atomMatrix ((Real.sqrt (design.weight label))⁻¹
            • (fun colIdx => completion label colIdx))
        = ∑ label, atomMatrix (fun colIdx => completion label colIdx) := by
          refine Finset.sum_congr rfl fun label _ => ?_
          rw [atomMatrix_smul, smul_smul, inv_pow,
            Real.sq_sqrt (design.weight_pos label).le,
            mul_inv_cancel₀ (design.weight_pos label).ne', one_smul]
      _ = 1 := by rw [← transpose_mul_self_eq_sum_rows, hcompletionOrtho]
  · -- the pair dictionary
    intro pairFst pairSnd hbracket
    have hdet := completionRowDet_eq_zero_of_pairBracket_eq_zero design completion _
      (fun label => rfl) pairFst pairSnd hbracket
    obtain ⟨mixCoeff, hmixNe, hrowFst, hrowSnd⟩ :=
      exists_commonOrthogonal_of_rowPair_det_eq_zero
        (fun colIdx => completion pairFst colIdx) (fun colIdx => completion pairSnd colIdx)
        hdet
    obtain ⟨dependence, hwitness, hsupport, hsum⟩ :=
      dependence_of_completion_mix design whitener hwhitenerUnit coDesign hcoDesignShape
        completion hcompletionOrtho hcoDesignPerp mixCoeff hmixNe
    exact ⟨dependence, hwitness, hsupport pairFst hrowFst, hsupport pairSnd hrowSnd, hsum⟩
  · -- the triple dictionary
    intro triFst triSnd triThd hbracketFstSnd hbracketFstThd hbracketSndThd
    have hdetFstSnd := completionRowDet_eq_zero_of_pairBracket_eq_zero design completion _
      (fun label => rfl) triFst triSnd hbracketFstSnd
    have hdetFstThd := completionRowDet_eq_zero_of_pairBracket_eq_zero design completion _
      (fun label => rfl) triFst triThd hbracketFstThd
    have hdetSndThd := completionRowDet_eq_zero_of_pairBracket_eq_zero design completion _
      (fun label => rfl) triSnd triThd hbracketSndThd
    obtain ⟨mixCoeff, hmixNe, hrowFst, hrowSnd, hrowThd⟩ :=
      exists_commonOrthogonal_of_rowTriple_det_eq_zero
        (fun colIdx => completion triFst colIdx) (fun colIdx => completion triSnd colIdx)
        (fun colIdx => completion triThd colIdx) hdetFstSnd hdetFstThd hdetSndThd
    obtain ⟨dependence, hwitness, hsupport, hsum⟩ :=
      dependence_of_completion_mix design whitener hwhitenerUnit coDesign hcoDesignShape
        completion hcompletionOrtho hcoDesignPerp mixCoeff hmixNe
    exact ⟨dependence, hwitness, hsupport triFst hrowFst, hsupport triSnd hrowSnd,
      hsupport triThd hrowThd, hsum⟩
  · -- the strict-domination transfer
    intro dualPair hpairCard hdom
    exact posDef_primalGap_of_posDef_dualPairGap design whitener hwhitenerUnit hwhitened
      coDesign hcoDesignShape completion hcomplete _
      (fun label => rfl) dualPair hpairCard hdom

/-! ## Cross-check: the `rank = 3` instance reproves the `(5,3)` package

The statement below is byte-for-byte the conclusion of
`EndpointSpike.exists_naimarkDual_with_bracketDictionary`, rederived from the
uniform-in-rank theorem at `rank = 3`. -/

theorem naimarkDual_landed_fiveThree_rederived (D : WeightedDesign 5 3) :
    ∃ dualDesign : WeightedDesign 5 2,
      (∀ pairFst pairSnd : Fin 5, pairBracket dualDesign pairFst pairSnd = 0 →
        ∃ dependence : Fin 5 → ℝ,
          (∃ witnessLabel, dependence witnessLabel ≠ 0)
            ∧ dependence pairFst = 0 ∧ dependence pairSnd = 0
            ∧ (∑ label, dependence label • D.atom label) = 0)
        ∧ ∀ dualPair : Finset (Fin 5), dualPair.card = 2 →
            (Gtz.subsetSum dualDesign dualPair - 1).PosDef →
            (Gtz.subsetSum D dualPairᶜ - 1).PosDef := by
  obtain ⟨dualDesign, hpairDictionary, _htripleDictionary, htransfer⟩ :=
    exists_naimarkDualCorankTwo 3 D
  exact ⟨dualDesign, hpairDictionary, htransfer⟩

end CorankTwo
