/-
# Antecedent mining: what a tie hands the producer for free, and two witnesses

The tightness antecedent is KERNEL MEMBERSHIP: a positive semidefinite gap with
a vanishing Rayleigh value annihilates the tight direction outright, so the
direction is reconstructed by its own projections onto the dominator's atoms.
From there every dominator atom under-reads the tight direction, at least one
strictly, and weighted Parseval forces an atom OUTSIDE the dominator to
strictly over-read it.  Normalizing the tight direction turns that atom into a
surplus witness at every card-3 subset containing it -- so the surplus half of
the residual, and the choice of unit normal, are both discharged by the
antecedents, and `PatternPlaneCoverAtTightDirection` is what actually remains.

Two exact witnesses fix the shape of the problem.  `r4WitnessDesign` has the
FREE TRIPLE as its singular weak dominator with the tight direction INSIDE the
line plane; `r4LlfDesign` has a two-line-plus-one-free triple as its singular
weak dominator with the tight direction OFF the plane.  So the dominator's
anatomy is free on this stratum and the tight direction is neither forced into
nor out of the line plane.  Both kill the complement selector ("take the
dominator's complement"), and the first also kills the free-triple selector.
The refined selector -- any card-3 subset containing an over-reading atom --
survives at both.
-/
import Gtz.Design.PairDifferenceCover

set_option maxHeartbeats 4000000

namespace Gtz
open Matrix


/-- **The tight direction is a genuine null vector.**  PSD plus a vanishing
Rayleigh value forces the whole matrix-vector product to vanish. -/
theorem tightDirection_mem_kernel {size rank : ℕ} (design : WeightedDesign size rank)
    (dominator : Finset (Fin size)) (tightDir : Fin rank → ℝ)
    (hdominates : Dominates design dominator)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    (subsetSum design dominator - 1) *ᵥ tightDir = 0 :=
  (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hdominates tightDir).mp
    (by rw [star_trivial]; exact htight)

/-- **The kernel condition as a vector reconstruction identity.**  The tight
direction is reproduced by its own projections onto the dominator's atoms. -/
theorem tightDirection_reconstruction {size rank : ℕ} (design : WeightedDesign size rank)
    (dominator : Finset (Fin size)) (tightDir : Fin rank → ℝ)
    (hdominates : Dominates design dominator)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    ∑ selectedLabel ∈ dominator,
        (design.atom selectedLabel ⬝ᵥ tightDir) • design.atom selectedLabel = tightDir := by
  have hkernel := tightDirection_mem_kernel design dominator tightDir hdominates htight
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hkernel
  have hexpand : subsetSum design dominator *ᵥ tightDir
      = ∑ selectedLabel ∈ dominator,
          (design.atom selectedLabel ⬝ᵥ tightDir) • design.atom selectedLabel := by
    rw [subsetSum, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun selectedLabel _ =>
      atomMatrix_mulVec_eq_dot_smul (design.atom selectedLabel) tightDir
  rw [← hexpand]
  exact hkernel

/-! ## Step 2: every dominator atom UNDER-covers the tight direction -/

/-- **Some dominator atom STRICTLY under-covers.**  Three nonnegative readings
summing to `|v|² > 0` cannot all reach `|v|²`. -/
theorem exists_dominatorAtom_reading_lt_normSq {size rank : ℕ}
    (design : WeightedDesign size rank)
    (dominator : Finset (Fin size)) (tightDir : Fin rank → ℝ)
    (hcardTwo : 2 ≤ dominator.card) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    ∃ selectedLabel ∈ dominator,
      (design.atom selectedLabel ⬝ᵥ tightDir) ^ 2 < tightDir ⬝ᵥ tightDir := by
  have hsum := tightDirection_rayleigh_identity design dominator htight
  have hnormPos : 0 < tightDir ⬝ᵥ tightDir := dotProduct_self_pos htightNe
  have hconst : ∑ _otherLabel ∈ dominator, tightDir ⬝ᵥ tightDir
      = (dominator.card : ℝ) * (tightDir ⬝ᵥ tightDir) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcardReal : (2 : ℝ) ≤ (dominator.card : ℝ) := by exact_mod_cast hcardTwo
  refine Finset.exists_lt_of_sum_lt (f := fun otherLabel =>
    (design.atom otherLabel ⬝ᵥ tightDir) ^ 2) (g := fun _ => tightDir ⬝ᵥ tightDir) ?_
  rw [hsum, hconst]
  nlinarith [hnormPos, hcardReal]

/-! ## Step 3: THE SURPLUS — some atom OUTSIDE the dominator strictly over-covers -/

/-- **The dominator's complement strictly over-covers the tight direction.**
The tight-direction analogue of `Gtz.complement_strictly_overcovers_normal`,
with the DOMINATOR (not a line) as the excluded set. -/
theorem dominatorComplement_strictly_overcovers_tightDirection {size rank : ℕ}
    (design : WeightedDesign size rank)
    (dominator : Finset (Fin size)) (tightDir : Fin rank → ℝ)
    (hcardTwo : 2 ≤ dominator.card) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    tightDir ⬝ᵥ tightDir
      < ∑ outsideLabel ∈ dominatorᶜ, (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 := by
  classical
  obtain ⟨overLabel, hnotMem, hover⟩ :=
    exists_outsideAtom_strictly_overcovers_tightDirection design dominator tightDir
      hcardTwo htightNe htight
  have hsingle : (design.atom overLabel ⬝ᵥ tightDir) ^ 2
      ≤ ∑ outsideLabel ∈ dominatorᶜ, (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2 :=
    Finset.single_le_sum (f := fun outsideLabel => (design.atom outsideLabel ⬝ᵥ tightDir) ^ 2)
      (fun outsideLabel _ => sq_nonneg _) (Finset.mem_compl.mpr hnotMem)
  linarith [hover, hsingle]

/-! ## Step 5: the canonical unit normal read off the tight direction -/

/-- The tight direction rescaled to unit length — the CANONICAL unit normal the
antecedents hand the producer. -/
noncomputable def normalizedDirection {rank : ℕ} (rawDir : Fin rank → ℝ) : Fin rank → ℝ :=
  (Real.sqrt (rawDir ⬝ᵥ rawDir))⁻¹ • rawDir

theorem normalizedDirection_isUnit {rank : ℕ} (rawDir : Fin rank → ℝ) (hne : rawDir ≠ 0) :
    normalizedDirection rawDir ⬝ᵥ normalizedDirection rawDir = 1 := by
  have hnormPos : 0 < rawDir ⬝ᵥ rawDir := dotProduct_self_pos hne
  have hrootPos : 0 < Real.sqrt (rawDir ⬝ᵥ rawDir) := Real.sqrt_pos.mpr hnormPos
  have hrootSq : Real.sqrt (rawDir ⬝ᵥ rawDir) * Real.sqrt (rawDir ⬝ᵥ rawDir)
      = rawDir ⬝ᵥ rawDir := Real.mul_self_sqrt hnormPos.le
  rw [normalizedDirection, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp
  linarith [hrootSq]

theorem dotProduct_normalizedDirection_sq {rank : ℕ}
    (atomVec rawDir : Fin rank → ℝ) (hne : rawDir ≠ 0) :
    (atomVec ⬝ᵥ normalizedDirection rawDir) ^ 2
      = (atomVec ⬝ᵥ rawDir) ^ 2 / (rawDir ⬝ᵥ rawDir) := by
  have hnormPos : 0 < rawDir ⬝ᵥ rawDir := dotProduct_self_pos hne
  have hrootSq : Real.sqrt (rawDir ⬝ᵥ rawDir) ^ 2 = rawDir ⬝ᵥ rawDir :=
    Real.sq_sqrt hnormPos.le
  rw [normalizedDirection, dotProduct_smul, smul_eq_mul, mul_pow, inv_pow, hrootSq]
  ring

/-! ## Step 6: THE SURPLUS HALF OF THE TARGET IS FREE

At `unitNormal := normalizedDirection tightDir`, EVERY card-3 subset containing
the over-covering atom already satisfies the producer's strict-surplus
hypothesis.  Nothing but the plane cover is left. -/

theorem surplus_of_mem_of_overcovers {size rank : ℕ} (design : WeightedDesign size rank)
    (tightDir : Fin rank → ℝ) (htightNe : tightDir ≠ 0)
    (overLabel : Fin size)
    (hover : tightDir ⬝ᵥ tightDir < (design.atom overLabel ⬝ᵥ tightDir) ^ 2)
    (selected : Finset (Fin size)) (hmem : overLabel ∈ selected) :
    1 < ∑ selectedLabel ∈ selected,
      (design.atom selectedLabel ⬝ᵥ normalizedDirection tightDir) ^ 2 := by
  have hnormPos : 0 < tightDir ⬝ᵥ tightDir := dotProduct_self_pos htightNe
  have hsingle : (design.atom overLabel ⬝ᵥ normalizedDirection tightDir) ^ 2
      ≤ ∑ selectedLabel ∈ selected,
          (design.atom selectedLabel ⬝ᵥ normalizedDirection tightDir) ^ 2 :=
    Finset.single_le_sum
      (f := fun selectedLabel =>
        (design.atom selectedLabel ⬝ᵥ normalizedDirection tightDir) ^ 2)
      (fun selectedLabel _ => sq_nonneg _) hmem
  have hvalue := dotProduct_normalizedDirection_sq (design.atom overLabel) tightDir htightNe
  rw [hvalue] at hsingle
  have hratio : 1 < (design.atom overLabel ⬝ᵥ tightDir) ^ 2 / (tightDir ⬝ᵥ tightDir) :=
    (one_lt_div hnormPos).mpr hover
  linarith [hsingle, hratio]

/-- **The antecedents determine the unit normal and one member of the witness
triple.**  The surplus half of `Gtz.PatternTightDominatedCoverProperty` is
discharged outright: the normal is the normalised tight direction, and any
card-3 subset containing the over-covering atom works. -/
theorem antecedents_determine_surplus_witness {size rank : ℕ}
    (design : WeightedDesign size rank)
    (dominator : Finset (Fin size)) (tightDir : Fin rank → ℝ)
    (hcardTwo : 2 ≤ dominator.card) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    ∃ overLabel : Fin size, overLabel ∉ dominator ∧
      normalizedDirection tightDir ⬝ᵥ normalizedDirection tightDir = 1 ∧
      ∀ selected : Finset (Fin size), overLabel ∈ selected →
        1 < ∑ selectedLabel ∈ selected,
          (design.atom selectedLabel ⬝ᵥ normalizedDirection tightDir) ^ 2 := by
  obtain ⟨overLabel, hnotMem, hover⟩ :=
    exists_outsideAtom_strictly_overcovers_tightDirection design dominator tightDir
      hcardTwo htightNe htight
  exact ⟨overLabel, hnotMem, normalizedDirection_isUnit tightDir htightNe,
    fun selected hmem =>
      surplus_of_mem_of_overcovers design tightDir htightNe overLabel hover selected hmem⟩

/-! ## Step 7: heaviness is NOT spent at the over-covering atom

The over-covering atom is heavy as a CONSEQUENCE (Cauchy-Schwarz against the
unit normal), so the heaviness antecedent contributes nothing to the surplus
half of the target. -/

/-- **The residual after antecedent mining.**  Only the plane cover survives:
the unit normal is pinned to the normalised tight direction and one member of
the witness triple is pinned to an atom outside the dominator that strictly
over-covers the tight direction. -/
def PatternPlaneCoverAtTightDirection {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∀ design : WeightedDesign size 3, HasLinePattern design pattern →
    (∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) →
    ∀ (dominator : Finset (Fin size)) (tightDir : Fin 3 → ℝ),
      dominator.card = 3 → Dominates design dominator → tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0 →
      ∀ overLabel : Fin size, overLabel ∉ dominator →
        tightDir ⬝ᵥ tightDir < (design.atom overLabel ⬝ᵥ tightDir) ^ 2 →
        ∃ selected : Finset (Fin size), selected.card = 3 ∧ overLabel ∈ selected ∧
          ∀ probe : Fin 3 → ℝ,
            probe ⬝ᵥ normalizedDirection tightDir = 0 → probe ≠ 0 →
            (∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe)
                * (design.atom selectedLabel ⬝ᵥ normalizedDirection tightDir)) ^ 2
              < ((∑ selectedLabel ∈ selected,
                    (design.atom selectedLabel ⬝ᵥ normalizedDirection tightDir) ^ 2) - 1)
                * ((∑ selectedLabel ∈ selected,
                      (design.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)

/-- **The reduction.**  The plane cover at the tight direction implies the
sharpened cover property, hence (through the landed chain) the class statement. -/
theorem patternTightDominatedCoverProperty_of_planeCoverAtTightDirection {size : ℕ}
    (pattern : LinePattern size)
    (hplaneCover : PatternPlaneCoverAtTightDirection pattern) :
    PatternTightDominatedCoverProperty pattern := by
  intro design hpattern hheavy dominator tightDir hcard hdominates htightNe htight
  have hcardTwo : 2 ≤ dominator.card := by rw [hcard]; norm_num
  obtain ⟨overLabel, hnotMem, hover⟩ :=
    exists_outsideAtom_strictly_overcovers_tightDirection design dominator tightDir
      hcardTwo htightNe htight
  obtain ⟨selected, hcardSelected, hmemSelected, hcover⟩ :=
    hplaneCover design hpattern hheavy dominator tightDir hcard hdominates htightNe
      htight overLabel hnotMem hover
  exact ⟨selected, normalizedDirection tightDir, hcardSelected,
    normalizedDirection_isUnit tightDir htightNe,
    surplus_of_mem_of_overcovers design tightDir htightNe overLabel hover selected
      hmemSelected,
    hcover⟩

/-! ## Step 9: one-line anatomy of the dominator -/

/-- On the one-line stratum a weak dominator always contains a FREE atom: the
line triple is the only card-3 subset of `{0,1,2}`, and it never dominates. -/
theorem oneLine_dominator_meets_freeTriple (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (dominator : Finset (Fin 6)) (hcard : dominator.card = 3)
    (hdominates : Dominates design dominator) :
    ∃ freeLabel ∈ dominator, freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)) := by
  classical
  by_contra hnone
  push Not at hnone
  have hsubset : dominator ⊆ ({0, 1, 2} : Finset (Fin 6)) := by
    intro label hmem
    have hnotFree := hnone label hmem
    fin_cases label <;> first | decide | exact absurd (by decide) hnotFree
  have hlineCard : ({0, 1, 2} : Finset (Fin 6)).card = 3 := by decide
  have heq : dominator = ({0, 1, 2} : Finset (Fin 6)) :=
    Finset.eq_of_subset_of_card_le hsubset (by rw [hcard, hlineCard])
  exact oneLine_lineTriple_not_dominates design hpattern (heq ▸ hdominates)

/-- **The normal component of the tight direction is carried entirely by the
dominator's free atoms.**  Line atoms are invisible along the line normal, so
the reconstruction identity collapses to the free part. -/
theorem oneLine_tightDirection_normalComponent (design : WeightedDesign 6 3)
    (dominator : Finset (Fin 6)) (tightDir normalVec : Fin 3 → ℝ)
    (hdominates : Dominates design dominator)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0) :
    tightDir ⬝ᵥ normalVec
      = ∑ freeLabel ∈ dominator \ ({0, 1, 2} : Finset (Fin 6)),
          (design.atom freeLabel ⬝ᵥ tightDir) * (design.atom freeLabel ⬝ᵥ normalVec) := by
  classical
  have hreconstruct :=
    tightDirection_reconstruction design dominator tightDir hdominates htight
  have hdotted := congrArg (fun leftVec : Fin 3 → ℝ => leftVec ⬝ᵥ normalVec) hreconstruct
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul] at hdotted
  rw [← hdotted]
  refine (Finset.sum_subset Finset.sdiff_subset fun selectedLabel hmemDominator hnotFree => ?_).symm
  have hmemLine : selectedLabel ∈ ({0, 1, 2} : Finset (Fin 6)) := by
    by_contra hnotLine
    exact hnotFree (Finset.mem_sdiff.mpr ⟨hmemDominator, hnotLine⟩)
  rw [horthogonal selectedLabel hmemLine, mul_zero]

noncomputable def r4WitnessAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![9 / 2, 2, 0]
  | 1 => ![-(9 / 2), 2, 0]
  | 2 => ![0, 1, 0]
  | 3 => ![0, 1 / 3, 4]
  | 4 => ![3 / 2, -(2 / 3), 1]
  | 5 => ![-(3 / 2), -(2 / 3), 1]

noncomputable def r4WitnessWeight : Fin 6 → ℝ
  | 0 => 1 / 54
  | 1 => 1 / 54
  | 2 => 43 / 54
  | 3 => 1 / 18
  | 4 => 1 / 18
  | 5 => 1 / 18

noncomputable def r4WitnessDesign : WeightedDesign 6 3 where
  atom := r4WitnessAtom
  weight := r4WitnessWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [r4WitnessWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [r4WitnessWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [r4WitnessAtom, r4WitnessWeight, atomMatrix] <;> norm_num

theorem r4WitnessDesign_hasLinePattern :
    HasLinePattern r4WitnessDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, r4WitnessDesign,
            r4WitnessAtom, Matrix.cons_val_two])
          (by decide)
      | exact iff_of_true
          (by norm_num [atomBracket, tripleBracket_eq, r4WitnessDesign,
            r4WitnessAtom, Matrix.cons_val_two])
          (by decide)

theorem r4WitnessDesign_isHeavy (label : Fin 6) :
    1 ≤ leverageOf (r4WitnessDesign.atom label) := by
  fin_cases label <;>
    simp [leverageOf, Fin.sum_univ_three, r4WitnessDesign, r4WitnessAtom] <;> norm_num

/-- The free-triple gap as an explicit sum of squares: `7/2·x² + 17·z²`. -/
theorem r4Witness_freeTripleGap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum r4WitnessDesign {3, 4, 5} - 1) *ᵥ vecArg)
      = 7 / 2 * vecArg 0 ^ 2 + 17 * vecArg 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [r4WitnessDesign, r4WitnessAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

theorem r4Witness_freeTripleGap_posSemidef :
    (subsetSum r4WitnessDesign {3, 4, 5} - 1).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg => ?_⟩
  · exact ((Matrix.posSemidef_sum ({3, 4, 5} : Finset (Fin 6)) fun freeLabel _ =>
      posSemidef_atomMatrix (r4WitnessDesign.atom freeLabel)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, r4Witness_freeTripleGap_form]
    positivity

/-- The free triple weakly dominates. -/
theorem r4WitnessDesign_dominates_freeTriple :
    Dominates r4WitnessDesign ({3, 4, 5} : Finset (Fin 6)) :=
  r4Witness_freeTripleGap_posSemidef

/-- `(0,1,0)` is a genuine tight direction of the free-triple gap. -/
theorem r4Witness_tightDirection_rayleigh :
    (![0, 1, 0] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum r4WitnessDesign {3, 4, 5} - 1) *ᵥ ![0, 1, 0]) = 0 := by
  rw [r4Witness_freeTripleGap_form]
  norm_num [show (![0, 1, 0] : Fin 3 → ℝ) 2 = 0 from rfl]

theorem r4Witness_tightDirection_ne_zero : (![0, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hentry := congrFun hzero 1
  norm_num at hentry

/-- The tight direction lies INSIDE the line plane: it is orthogonal to the
line normal `(0,0,1)`, exactly like the line atoms themselves. -/
theorem r4Witness_tightDirection_in_linePlane :
    (![0, 1, 0] : Fin 3 → ℝ) ⬝ᵥ ![0, 0, 1] = 0 := by
  simp [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, show (![0, 1, 0] : Fin 3 → ℝ) 2 = 0 from rfl]

theorem r4Witness_lineAtoms_orthogonal_to_normal
    (lineLabel : Fin 6) (hmem : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6))) :
    r4WitnessDesign.atom lineLabel ⬝ᵥ ![0, 0, 1] = 0 := by
  fin_cases hmem <;>
    simp [r4WitnessDesign, r4WitnessAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]

/-! ## The refutation of the complement selector -/

/-- The dominator's complement here is the LINE TRIPLE, which the pattern
forbids from dominating at all — so it can never be a producer witness. -/
theorem r4Witness_freeTripleComplement_eq :
    ({3, 4, 5} : Finset (Fin 6))ᶜ = ({0, 1, 2} : Finset (Fin 6)) := by decide

theorem r4Witness_complement_not_dominates :
    ¬ Dominates r4WitnessDesign (({3, 4, 5} : Finset (Fin 6))ᶜ) := by
  rw [r4Witness_freeTripleComplement_eq]
  exact oneLine_lineTriple_not_dominates r4WitnessDesign r4WitnessDesign_hasLinePattern

theorem r4Witness_complement_not_posDef :
    ¬ (subsetSum r4WitnessDesign (({3, 4, 5} : Finset (Fin 6))ᶜ) - 1).PosDef :=
  fun hposDef => r4Witness_complement_not_dominates hposDef.posSemidef

/-! ## The over-covering atoms are the LINE atoms -/

theorem r4Witness_lineAtomZero_overcovers :
    (![0, 1, 0] : Fin 3 → ℝ) ⬝ᵥ ![0, 1, 0]
      < (r4WitnessDesign.atom 0 ⬝ᵥ ![0, 1, 0]) ^ 2 := by
  norm_num [r4WitnessDesign, r4WitnessAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem r4Witness_freeAtoms_undercover (freeLabel : Fin 6)
    (hmem : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    (r4WitnessDesign.atom freeLabel ⬝ᵥ ![0, 1, 0]) ^ 2
      < (![0, 1, 0] : Fin 3 → ℝ) ⬝ᵥ ![0, 1, 0] := by
  fin_cases hmem <;>
    norm_num [r4WitnessDesign, r4WitnessAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two]

/-! ## A strict dominator DOES exist, and it contains the over-coverer

`{0,1,3}` has gap form `79/2·x² + 64/9·y² + 8/3·yz + 15·z²`, i.e. the completed
square `79/2·x² + (8y/3 + z/2)² + 59/4·z²` — positive definite.  So the refined
selector
"pick a card-3 set containing an over-covering atom" SURVIVES at this witness,
while the complement selector dies. -/

theorem r4Witness_llfGap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum r4WitnessDesign {0, 1, 3} - 1) *ᵥ vecArg)
      = 79 / 2 * vecArg 0 ^ 2 + (8 / 3 * vecArg 1 + 1 / 2 * vecArg 2) ^ 2
        + 59 / 4 * vecArg 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [r4WitnessDesign, r4WitnessAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

theorem r4Witness_llfGap_posDef :
    (subsetSum r4WitnessDesign {0, 1, 3} - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 3} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (r4WitnessDesign.atom label)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, r4Witness_llfGap_form]
    rcases Function.ne_iff.mp hne with ⟨coordIndex, hcoord⟩
    fin_cases coordIndex
    · have hcoordNe : vecArg 0 ≠ 0 := by simpa using hcoord
      have hsq : 0 < vecArg 0 ^ 2 := by positivity
      nlinarith [sq_nonneg (8 / 3 * vecArg 1 + 1 / 2 * vecArg 2), sq_nonneg (vecArg 2)]
    · have hcoordNe : vecArg 1 ≠ 0 := by simpa using hcoord
      have hsq : 0 < vecArg 1 ^ 2 := by positivity
      nlinarith [sq_nonneg (vecArg 0), sq_nonneg (vecArg 2),
        sq_nonneg (8 / 3 * vecArg 1 + 1 / 2 * vecArg 2),
        sq_nonneg (8 / 3 * vecArg 1 - 1 / 2 * vecArg 2)]
    · have hcoordNe : vecArg 2 ≠ 0 := by simpa using hcoord
      have hsq : 0 < vecArg 2 ^ 2 := by positivity
      nlinarith [sq_nonneg (8 / 3 * vecArg 1 + 1 / 2 * vecArg 2), sq_nonneg (vecArg 0)]

/-! ## Two candidate selector rules, both KILLED by this witness -/

/-- Candidate rule A: "always take the dominator's complement". -/
def ComplementSelectorRule {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∀ design : WeightedDesign size 3, HasLinePattern design pattern →
    (∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) →
    ∀ (dominator : Finset (Fin size)) (tightDir : Fin 3 → ℝ),
      dominator.card = 3 → Dominates design dominator → tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0 →
      (subsetSum design dominatorᶜ - 1).PosDef

/-- Candidate rule B: "the FREE TRIPLE always strictly dominates on the
one-line stratum" — the shape the tree's own prose gestures at, since the
surplus half is automatic there against the line normal. -/
def FreeTripleSelectorRule : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef

theorem r4Witness_freeTripleGap_not_posDef :
    ¬ (subsetSum r4WitnessDesign ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hpos := hposDef.dotProduct_mulVec_pos r4Witness_tightDirection_ne_zero
  rw [star_trivial, r4Witness_tightDirection_rayleigh] at hpos
  exact lt_irrefl 0 hpos

/-- **Rule B is false.**  The witness's free triple weakly dominates with a
one-dimensional kernel, so it is not a strict dominator. -/
theorem not_freeTripleSelectorRule : ¬ FreeTripleSelectorRule := fun hrule =>
  r4Witness_freeTripleGap_not_posDef
    (hrule r4WitnessDesign r4WitnessDesign_hasLinePattern r4WitnessDesign_isHeavy)

/-- **Rule A is false.**  At the witness the dominator is the free triple, so
its complement is the line triple, which the pattern forbids from dominating. -/
theorem not_complementSelectorRule :
    ¬ ComplementSelectorRule (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  intro hrule
  exact r4Witness_complement_not_posDef
    (hrule r4WitnessDesign r4WitnessDesign_hasLinePattern r4WitnessDesign_isHeavy
      ({3, 4, 5} : Finset (Fin 6)) ![0, 1, 0] (by decide)
      r4WitnessDesign_dominates_freeTriple r4Witness_tightDirection_ne_zero
      r4Witness_tightDirection_rayleigh)

/-! ## The refined selector SURVIVES at the witness

`{0,1,3}` contains the over-covering atom `0`, and against the (already unit)
tight direction `(0,1,0)` it satisfies BOTH producer hypotheses. -/

theorem r4Witness_tightDirection_isUnit :
    (![0, 1, 0] : Fin 3 → ℝ) ⬝ᵥ ![0, 1, 0] = 1 := by
  simp [dotProduct, Fin.sum_univ_three, show (![0, 1, 0] : Fin 3 → ℝ) 2 = 0 from rfl]

theorem r4Witness_refinedSelector_survives :
    ∃ (selected : Finset (Fin 6)) (unitNormal : Fin 3 → ℝ),
      selected.card = 3 ∧ (0 : Fin 6) ∈ selected ∧ unitNormal ⬝ᵥ unitNormal = 1 ∧
      (1 < ∑ selectedLabel ∈ selected,
        (r4WitnessDesign.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) ∧
      ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
        (∑ selectedLabel ∈ selected, (r4WitnessDesign.atom selectedLabel ⬝ᵥ probe)
            * (r4WitnessDesign.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2
          < ((∑ selectedLabel ∈ selected,
                (r4WitnessDesign.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
            * ((∑ selectedLabel ∈ selected,
                  (r4WitnessDesign.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe) := by
  obtain ⟨hsurplus, hcover⟩ :=
    normalSurplus_planeCover_of_posDef r4WitnessDesign ({0, 1, 3} : Finset (Fin 6))
      ![0, 1, 0] r4Witness_tightDirection_isUnit r4Witness_llfGap_posDef
  exact ⟨{0, 1, 3}, ![0, 1, 0], by decide, by decide,
    r4Witness_tightDirection_isUnit, hsurplus, hcover⟩

noncomputable def r4LlfAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![3 / 2, 3 / 4, 0]
  | 1 => ![-(3 / 2), 3 / 4, 0]
  | 2 => ![0, 1, 0]
  | 3 => ![0, 1, 3]
  | 4 => ![1, -(4 / 3), 1]
  | 5 => ![-1, -(4 / 3), 1]

noncomputable def r4LlfWeight : Fin 6 → ℝ
  | 0 => 8 / 45
  | 1 => 8 / 45
  | 2 => 16 / 45
  | 3 => 4 / 45
  | 4 => 1 / 10
  | 5 => 1 / 10

noncomputable def r4LlfDesign : WeightedDesign 6 3 where
  atom := r4LlfAtom
  weight := r4LlfWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [r4LlfWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [r4LlfWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [r4LlfAtom, r4LlfWeight, atomMatrix] <;> norm_num

theorem r4LlfDesign_hasLinePattern :
    HasLinePattern r4LlfDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, r4LlfDesign,
            r4LlfAtom, Matrix.cons_val_two])
          (by decide)
      | exact iff_of_true
          (by norm_num [atomBracket, tripleBracket_eq, r4LlfDesign,
            r4LlfAtom, Matrix.cons_val_two])
          (by decide)

theorem r4LlfDesign_isHeavy (label : Fin 6) :
    1 ≤ leverageOf (r4LlfDesign.atom label) := by
  fin_cases label <;>
    simp [leverageOf, Fin.sum_univ_three, r4LlfDesign, r4LlfAtom] <;> norm_num

/-- The LLF gap as an explicit sum of squares: `7/2·x² + 9/8·(y + 8z/3)²`. -/
theorem r4Llf_gap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum r4LlfDesign {0, 1, 3} - 1) *ᵥ vecArg)
      = 7 / 2 * vecArg 0 ^ 2 + 9 / 8 * (vecArg 1 + 8 / 3 * vecArg 2) ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [r4LlfDesign, r4LlfAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  ring

theorem r4Llf_gap_posSemidef :
    (subsetSum r4LlfDesign {0, 1, 3} - 1).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 3} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (r4LlfDesign.atom label)).1).sub Matrix.isHermitian_one
  · rw [star_trivial, r4Llf_gap_form]
    positivity

theorem r4LlfDesign_dominates_llfTriple :
    Dominates r4LlfDesign ({0, 1, 3} : Finset (Fin 6)) :=
  r4Llf_gap_posSemidef

theorem r4Llf_tightDirection_ne_zero : (![0, 8, -3] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hentry := congrFun hzero 1
  norm_num at hentry

theorem r4Llf_tightDirection_rayleigh :
    (![0, 8, -3] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum r4LlfDesign {0, 1, 3} - 1) *ᵥ ![0, 8, -3]) = 0 := by
  rw [r4Llf_gap_form]
  norm_num [show (![0, 8, -3] : Fin 3 → ℝ) 2 = -3 from rfl]

/-- **The tight direction sits OFF the line plane.**  Its component along the
line normal `(0,0,1)` is `-3`, not zero — the opposite of the free-triple
witness, where the tight direction lay inside the plane. -/
theorem r4Llf_tightDirection_off_linePlane :
    (![0, 8, -3] : Fin 3 → ℝ) ⬝ᵥ ![0, 0, 1] = -3 := by
  simp [dotProduct, Fin.sum_univ_three, show (![0, 8, -3] : Fin 3 → ℝ) 2 = -3 from rfl,
    show (![0, 0, 1] : Fin 3 → ℝ) 2 = 1 from rfl]

theorem r4Llf_lineAtoms_orthogonal_to_normal
    (lineLabel : Fin 6) (hmem : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6))) :
    r4LlfDesign.atom lineLabel ⬝ᵥ ![0, 0, 1] = 0 := by
  fin_cases hmem <;>
    simp [r4LlfDesign, r4LlfAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

/-! ## Here the over-coverers are the FREE atoms -/

theorem r4Llf_normSq : (![0, 8, -3] : Fin 3 → ℝ) ⬝ᵥ ![0, 8, -3] = 73 := by
  simp [dotProduct, Fin.sum_univ_three, show (![0, 8, -3] : Fin 3 → ℝ) 2 = -3 from rfl]
  norm_num

theorem r4Llf_freeAtomFour_overcovers :
    (![0, 8, -3] : Fin 3 → ℝ) ⬝ᵥ ![0, 8, -3]
      < (r4LlfDesign.atom 4 ⬝ᵥ ![0, 8, -3]) ^ 2 := by
  rw [r4Llf_normSq]
  norm_num [r4LlfDesign, r4LlfAtom, dotProduct, Fin.sum_univ_three,
    show (![0, 8, -3] : Fin 3 → ℝ) 2 = -3 from rfl,
    show (![1, -(4 / 3), 1] : Fin 3 → ℝ) 2 = 1 from rfl]

theorem r4Llf_lineAtomTwo_undercovers :
    (r4LlfDesign.atom 2 ⬝ᵥ ![0, 8, -3]) ^ 2
      < (![0, 8, -3] : Fin 3 → ℝ) ⬝ᵥ ![0, 8, -3] := by
  rw [r4Llf_normSq]
  norm_num [r4LlfDesign, r4LlfAtom, dotProduct, Fin.sum_univ_three,
    show (![0, 8, -3] : Fin 3 → ℝ) 2 = -3 from rfl,
    show (![0, 1, 0] : Fin 3 → ℝ) 2 = 0 from rfl]

/-! ## The complement selector dies here too -/

theorem r4Llf_complement_eq :
    ({0, 1, 3} : Finset (Fin 6))ᶜ = ({2, 4, 5} : Finset (Fin 6)) := by decide

theorem r4Llf_complementGap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum r4LlfDesign {2, 4, 5} - 1) *ᵥ vecArg)
      = vecArg 0 ^ 2 + 32 / 9 * vecArg 1 ^ 2 - 16 / 3 * vecArg 1 * vecArg 2
        + vecArg 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [r4LlfDesign, r4LlfAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  ring

theorem r4Llf_complement_not_dominates :
    ¬ Dominates r4LlfDesign (({0, 1, 3} : Finset (Fin 6))ᶜ) := by
  rw [r4Llf_complement_eq]
  intro hpsd
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, 1, 2]
  rw [star_trivial, r4Llf_complementGap_form] at hform
  norm_num [show (![0, 1, 2] : Fin 3 → ℝ) 2 = 2 from rfl] at hform

/-! ## A strict dominator containing an over-coverer: the free triple -/

theorem r4Llf_freeTripleGap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum r4LlfDesign {3, 4, 5} - 1) *ᵥ vecArg)
      = vecArg 0 ^ 2 + 32 / 9 * (vecArg 1 + 3 / 32 * vecArg 2) ^ 2
        + 319 / 32 * vecArg 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [r4LlfDesign, r4LlfAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
  ring

theorem r4Llf_freeTripleGap_posDef :
    (subsetSum r4LlfDesign {3, 4, 5} - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact ((Matrix.posSemidef_sum ({3, 4, 5} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (r4LlfDesign.atom label)).1).sub Matrix.isHermitian_one
  · rw [star_trivial, r4Llf_freeTripleGap_form]
    rcases Function.ne_iff.mp hne with ⟨coordIndex, hcoord⟩
    fin_cases coordIndex
    · have hcoordNe : vecArg 0 ≠ 0 := by simpa using hcoord
      have hsq : 0 < vecArg 0 ^ 2 := by positivity
      nlinarith [sq_nonneg (vecArg 1 + 3 / 32 * vecArg 2), sq_nonneg (vecArg 2)]
    · have hcoordNe : vecArg 1 ≠ 0 := by simpa using hcoord
      have hsq : 0 < vecArg 1 ^ 2 := by positivity
      nlinarith [sq_nonneg (vecArg 0), sq_nonneg (vecArg 2),
        sq_nonneg (vecArg 1 + 3 / 32 * vecArg 2), sq_nonneg (vecArg 1 - 3 / 32 * vecArg 2)]
    · have hcoordNe : vecArg 2 ≠ 0 := by simpa using hcoord
      have hsq : 0 < vecArg 2 ^ 2 := by positivity
      nlinarith [sq_nonneg (vecArg 0), sq_nonneg (vecArg 1 + 3 / 32 * vecArg 2)]

/-- A concrete unit vector, so the backward direction has a normal to hand. -/
theorem firstAxis_isUnit : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ ![1, 0, 0] = 1 := by
  simp [dotProduct, Fin.sum_univ_three]

/-- **Every unit normal works as soon as one does.**  The normal that the
existential produces is irrelevant: any unit vector serves. -/
theorem producerNormal_transfers {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (sourceNormal targetNormal : Fin 3 → ℝ)
    (hsourceUnit : sourceNormal ⬝ᵥ sourceNormal = 1)
    (htargetUnit : targetNormal ⬝ᵥ targetNormal = 1)
    (hsurplus : 1 < ∑ selectedLabel ∈ selected,
      (design.atom selectedLabel ⬝ᵥ sourceNormal) ^ 2)
    (hcover : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ sourceNormal = 0 → probe ≠ 0 →
      (∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe)
          * (design.atom selectedLabel ⬝ᵥ sourceNormal)) ^ 2
        < ((∑ selectedLabel ∈ selected,
              (design.atom selectedLabel ⬝ᵥ sourceNormal) ^ 2) - 1)
          * ((∑ selectedLabel ∈ selected,
                (design.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)) :
    (1 < ∑ selectedLabel ∈ selected,
        (design.atom selectedLabel ⬝ᵥ targetNormal) ^ 2)
      ∧ ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ targetNormal = 0 → probe ≠ 0 →
          (∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe)
              * (design.atom selectedLabel ⬝ᵥ targetNormal)) ^ 2
            < ((∑ selectedLabel ∈ selected,
                  (design.atom selectedLabel ⬝ᵥ targetNormal) ^ 2) - 1)
              * ((∑ selectedLabel ∈ selected,
                    (design.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe) :=
  normalSurplus_planeCover_of_posDef design selected targetNormal htargetUnit
    (posDef_of_normalSurplus_planeCover design selected sourceNormal hsourceUnit
      hsurplus hcover)

/-- **The target Prop is exactly a strict-domination selector.**  The whole
`(selected, unitNormal)` existential of
`Gtz.PatternTightDominatedCoverProperty` collapses to "some card-3 subset has a
POSITIVE DEFINITE gap"; nothing about the normal survives. -/
theorem patternTightDominatedCoverProperty_iff_strictSelector {size : ℕ}
    (pattern : LinePattern size) :
    PatternTightDominatedCoverProperty pattern ↔
      ∀ design : WeightedDesign size 3, HasLinePattern design pattern →
        (∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) →
        ∀ (dominator : Finset (Fin size)) (tightDir : Fin 3 → ℝ),
          dominator.card = 3 → Dominates design dominator →
          tightDir ≠ 0 →
          tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0 →
          ∃ selected : Finset (Fin size),
            selected.card = 3 ∧ (subsetSum design selected - 1).PosDef := by
  constructor
  · intro hproperty design hpattern hheavy dominator tightDir hcard hdominates
      htightNe htight
    obtain ⟨selected, unitNormal, hcardSelected, hunit, hsurplus, hcover⟩ :=
      hproperty design hpattern hheavy dominator tightDir hcard hdominates htightNe htight
    exact ⟨selected, hcardSelected,
      posDef_of_normalSurplus_planeCover design selected unitNormal hunit hsurplus hcover⟩
  · intro hselector design hpattern hheavy dominator tightDir hcard hdominates
      htightNe htight
    obtain ⟨selected, hcardSelected, hposDef⟩ :=
      hselector design hpattern hheavy dominator tightDir hcard hdominates htightNe htight
    obtain ⟨hsurplus, hcover⟩ :=
      normalSurplus_planeCover_of_posDef design selected ![1, 0, 0] firstAxis_isUnit hposDef
    exact ⟨selected, ![1, 0, 0], hcardSelected, firstAxis_isUnit, hsurplus, hcover⟩

#print axioms firstAxis_isUnit
#print axioms existsProducerNormal_iff_posDef
#print axioms producerNormal_transfers
#print axioms patternTightDominatedCoverProperty_iff_strictSelector


/-- **The leverage floor poisons a subset, three-element form.**  A card-3 subset
containing an atom of leverage at most one NEVER strictly dominates.  No
hypothesis on the other two atoms, on the pattern, or on any unit normal. -/
theorem notPosDef_of_mem_leverage_le_one {size : ℕ}
    (design : WeightedDesign size 3) (lightLabel otherFirst otherSecond : Fin size)
    (hlight : leverageOf (design.atom lightLabel) ≤ 1) :
    ¬ (subsetSum design {lightLabel, otherFirst, otherSecond} - 1).PosDef := by
  obtain ⟨probe, hprobeNe, hfirstOrth, hsecondOrth⟩ :=
    exists_commonOrthogonal_of_pair (design.atom otherFirst) (design.atom otherSecond)
  refine notPosDef_of_leverage_le_one_of_annihilated design
    {lightLabel, otherFirst, otherSecond} (by simp) probe hprobeNe ?_ hlight
  intro otherLabel hmem hne
  have hcases : otherLabel = lightLabel ∨ otherLabel = otherFirst
      ∨ otherLabel = otherSecond := by simpa using hmem
  rcases hcases with heq | heq | heq
  · exact absurd heq hne
  · rw [heq]; exact hfirstOrth
  · rw [heq]; exact hsecondOrth

/-- **Every strict dominator is strictly heavy.**  Contrapositive form: if a
card-3 subset strictly dominates then each of its three atoms has leverage
STRICTLY above one.  Heaviness `1 <= leverage` is therefore never enough on its
own — the census's selection rule has to avoid floor atoms. -/
theorem one_lt_leverage_of_posDef {size : ℕ} (design : WeightedDesign size 3)
    (lightLabel otherFirst otherSecond : Fin size)
    (hposDef : (subsetSum design {lightLabel, otherFirst, otherSecond} - 1).PosDef) :
    1 < leverageOf (design.atom lightLabel) := by
  by_contra hnot
  exact notPosDef_of_mem_leverage_le_one design lightLabel otherFirst otherSecond
    (not_lt.mp hnot) hposDef

#print axioms exists_commonOrthogonal_of_pair
#print axioms notPosDef_of_leverage_le_one_of_annihilated
#print axioms notPosDef_of_mem_leverage_le_one
#print axioms one_lt_leverage_of_posDef

/-- **The margin-versus-tilt producer.**  ANATOMY-FREE, and the sharpest
sufficient condition the Schur decomposition admits: a card-three subset
strictly dominates as soon as three scalars line up --

* a normal SURPLUS `sigma = (sum of squared heights) - 1 > 0`;
* a strict multiplicative COVER MARGIN of the subset's in-plane readings over
  the plane's own norm;
* a TILT BOUND on the subset's height-weighted in-plane reading, the single
  quantity the Schur complement subtracts;

subject to the one inequality `tiltBound < margin * sigma`.

No flatness is assumed of any slot, so this covers every anatomy at once: the
two-line-plus-one-free route is the instance where two heights vanish and the
tilt collapses onto the free atom's shadow alone.  Read against
`Gtz.margin_cap_and_its_floor`, which caps `sigma` from above by the
complement's height budget and floors that cap by the line weight, this is the
exact trade the chartless residual has to win. -/
theorem posDef_of_coverMargin_of_tiltBound {size : ℕ} (design : WeightedDesign size 3)
    (firstLabel secondLabel thirdLabel : Fin size) (unitNormal : Fin 3 → ℝ)
    (margin tiltBound : ℝ)
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hsurplus : 1 < (design.atom firstLabel ⬝ᵥ unitNormal) ^ 2
      + (design.atom secondLabel ⬝ᵥ unitNormal) ^ 2
      + (design.atom thirdLabel ⬝ᵥ unitNormal) ^ 2)
    (hcover : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ (design.atom firstLabel ⬝ᵥ probe) ^ 2
          + (design.atom secondLabel ⬝ᵥ probe) ^ 2
          + (design.atom thirdLabel ⬝ᵥ probe) ^ 2)
    (htilt : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 →
      ((design.atom firstLabel ⬝ᵥ unitNormal) * (design.atom firstLabel ⬝ᵥ probe)
          + (design.atom secondLabel ⬝ᵥ unitNormal) * (design.atom secondLabel ⬝ᵥ probe)
          + (design.atom thirdLabel ⬝ᵥ unitNormal) * (design.atom thirdLabel ⬝ᵥ probe)) ^ 2
        ≤ tiltBound * (probe ⬝ᵥ probe))
    (hbeat : tiltBound < margin * ((design.atom firstLabel ⬝ᵥ unitNormal) ^ 2
      + (design.atom secondLabel ⬝ᵥ unitNormal) ^ 2
      + (design.atom thirdLabel ⬝ᵥ unitNormal) ^ 2 - 1)) :
    (subsetSum design ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)) - 1).PosDef := by
  have hsumThree : ∀ valueOf : Fin size → ℝ,
      ∑ selectedLabel ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
          valueOf selectedLabel
        = valueOf firstLabel + valueOf secondLabel + valueOf thirdLabel := by
    intro valueOf
    rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
      Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, add_assoc]
  refine posDef_of_normalSurplus_planeCover design _ unitNormal hunit ?_ ?_
  · rw [hsumThree (fun selectedLabel => (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2)]
    exact hsurplus
  · intro probe hprobeFlat hprobeNe
    have hnormPos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
    have hcoverAt := hcover probe hprobeFlat
    have htiltAt := htilt probe hprobeFlat
    rw [hsumThree (fun selectedLabel =>
        (design.atom selectedLabel ⬝ᵥ probe) * (design.atom selectedLabel ⬝ᵥ unitNormal)),
      hsumThree (fun selectedLabel => (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2),
      hsumThree (fun selectedLabel => (design.atom selectedLabel ⬝ᵥ probe) ^ 2)]
    nlinarith [hcoverAt, htiltAt, hnormPos, hbeat, hsurplus]

/-- **The tilt bound is always available**, with the height-weighted total
leverage as the constant: Cauchy-Schwarz on the three height-scaled shadows. -/
theorem tiltBound_of_leverages {size : ℕ} (design : WeightedDesign size 3)
    (firstLabel secondLabel thirdLabel : Fin size) (unitNormal probe : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) (hprobeFlat : probe ⬝ᵥ unitNormal = 0) :
    ((design.atom firstLabel ⬝ᵥ unitNormal) * (design.atom firstLabel ⬝ᵥ probe)
        + (design.atom secondLabel ⬝ᵥ unitNormal) * (design.atom secondLabel ⬝ᵥ probe)
        + (design.atom thirdLabel ⬝ᵥ unitNormal) * (design.atom thirdLabel ⬝ᵥ probe)) ^ 2
      ≤ 3 * ((design.atom firstLabel ⬝ᵥ unitNormal) ^ 2
              * (leverageOf (design.atom firstLabel)
                  - (design.atom firstLabel ⬝ᵥ unitNormal) ^ 2)
            + (design.atom secondLabel ⬝ᵥ unitNormal) ^ 2
              * (leverageOf (design.atom secondLabel)
                  - (design.atom secondLabel ⬝ᵥ unitNormal) ^ 2)
            + (design.atom thirdLabel ⬝ᵥ unitNormal) ^ 2
              * (leverageOf (design.atom thirdLabel)
                  - (design.atom thirdLabel ⬝ᵥ unitNormal) ^ 2))
        * (probe ⬝ᵥ probe) := by
  have hfirst := atomShadow_reading_sq_le (design.atom firstLabel) unitNormal probe hunit
    hprobeFlat
  have hsecond := atomShadow_reading_sq_le (design.atom secondLabel) unitNormal probe hunit
    hprobeFlat
  have hthird := atomShadow_reading_sq_le (design.atom thirdLabel) unitNormal probe hunit
    hprobeFlat
  have hnormNonneg : 0 ≤ probe ⬝ᵥ probe := dotProduct_self_nonneg probe
  nlinarith [hfirst, hsecond, hthird, hnormNonneg,
    sq_nonneg ((design.atom firstLabel ⬝ᵥ unitNormal) * (design.atom firstLabel ⬝ᵥ probe)
      - (design.atom secondLabel ⬝ᵥ unitNormal) * (design.atom secondLabel ⬝ᵥ probe)),
    sq_nonneg ((design.atom firstLabel ⬝ᵥ unitNormal) * (design.atom firstLabel ⬝ᵥ probe)
      - (design.atom thirdLabel ⬝ᵥ unitNormal) * (design.atom thirdLabel ⬝ᵥ probe)),
    sq_nonneg ((design.atom secondLabel ⬝ᵥ unitNormal) * (design.atom secondLabel ⬝ᵥ probe)
      - (design.atom thirdLabel ⬝ᵥ unitNormal) * (design.atom thirdLabel ⬝ᵥ probe)),
    sq_nonneg (design.atom firstLabel ⬝ᵥ unitNormal),
    sq_nonneg (design.atom secondLabel ⬝ᵥ unitNormal),
    sq_nonneg (design.atom thirdLabel ⬝ᵥ unitNormal)]

/-- **The free-triple producer on a line stratum, in explicit constants.**
Everything the Schur decomposition needs is now supplied by weights and one
in-plane mass ceiling:

* the SURPLUS is free -- `Gtz.complement_surplus_ge_lineWeight` makes it
  strictly positive with the line weight as floor, on every design of the
  stratum;
* the COVER MARGIN follows from a ceiling on the line atoms' weighted in-plane
  reading, through `Gtz.complementShadow_coverMargin_of_lineMassCeiling`;
* the TILT is bounded by `Gtz.tiltBound_of_leverages`.

What remains is ONE division-free inequality between the four constants:
`tiltBound * complementWeight < margin * lineWeight`.  This is the exact trade
the chartless residual has to win at the free triple, with both sides now
kernel quantities: the left side is capped by
`Gtz.margin_cap_and_its_floor`, the right side is bought by line thinness. -/
theorem oneLine_freeTriple_posDef_of_constants (design : WeightedDesign 6 3)
    (unitNormal : Fin 3 → ℝ)
    (maxFreeWeight lineMassCeiling margin tiltBound : ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (horth : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hmaxFreeWeightPos : 0 < maxFreeWeight)
    (hmaxFreeWeight : ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      design.weight freeLabel ≤ maxFreeWeight)
    (hlineMass : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 →
      ∑ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
          design.weight lineLabel * (design.atom lineLabel ⬝ᵥ probe) ^ 2
        ≤ lineMassCeiling * (probe ⬝ᵥ probe))
    (hmarginPos : 0 < margin)
    (hmarginFits : (1 + margin) * maxFreeWeight ≤ 1 - lineMassCeiling)
    (htilt : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 →
      ((design.atom 3 ⬝ᵥ unitNormal) * (design.atom 3 ⬝ᵥ probe)
          + (design.atom 4 ⬝ᵥ unitNormal) * (design.atom 4 ⬝ᵥ probe)
          + (design.atom 5 ⬝ᵥ unitNormal) * (design.atom 5 ⬝ᵥ probe)) ^ 2
        ≤ tiltBound * (probe ⬝ᵥ probe))
    (hbeat : tiltBound * (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)), design.weight freeLabel)
      < margin * ∑ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight lineLabel) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  have hcompl : (({0, 1, 2} : Finset (Fin 6)))ᶜ = ({3, 4, 5} : Finset (Fin 6)) := by decide
  have hsumThree : ∀ valueOf : Fin 6 → ℝ,
      ∑ selectedLabel ∈ ({3, 4, 5} : Finset (Fin 6)), valueOf selectedLabel
        = valueOf 3 + valueOf 4 + valueOf 5 := by
    intro valueOf
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      add_assoc]
  have hlineWeightPos : 0 < ∑ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight lineLabel :=
    Finset.sum_pos (fun label _ => design.weight_pos label) ⟨0, by decide⟩
  have hfreeWeightPos : 0 < ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)), design.weight freeLabel :=
    Finset.sum_pos (fun label _ => design.weight_pos label) ⟨3, by decide⟩
  have hsurplusProduct := complement_surplus_ge_lineWeight design ({0, 1, 2} : Finset (Fin 6))
    unitNormal hunit horth
  rw [hcompl] at hsurplusProduct
  have hheightSum : (design.atom 3 ⬝ᵥ unitNormal) ^ 2 + (design.atom 4 ⬝ᵥ unitNormal) ^ 2
      + (design.atom 5 ⬝ᵥ unitNormal) ^ 2
      = ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
          (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 :=
    (hsumThree (fun freeLabel => (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2)).symm
  have hsurplus : 1 < (design.atom 3 ⬝ᵥ unitNormal) ^ 2 + (design.atom 4 ⬝ᵥ unitNormal) ^ 2
      + (design.atom 5 ⬝ᵥ unitNormal) ^ 2 := by
    rw [hheightSum]
    nlinarith [hsurplusProduct, hlineWeightPos, hfreeWeightPos]
  refine posDef_of_coverMargin_of_tiltBound design 3 4 5 unitNormal margin tiltBound
    (by decide) (by decide) (by decide) hunit hsurplus ?_ htilt ?_
  · intro probe hprobeFlat
    have hcover := complementShadow_coverMargin_of_lineMassCeiling design
      ({0, 1, 2} : Finset (Fin 6)) probe maxFreeWeight lineMassCeiling margin
      hmaxFreeWeightPos (by rw [hcompl]; exact hmaxFreeWeight)
      (hlineMass probe hprobeFlat) hmarginFits
    rw [hcompl, hsumThree (fun freeLabel => (design.atom freeLabel ⬝ᵥ probe) ^ 2)] at hcover
    exact hcover
  · rw [hheightSum]
    nlinarith [hsurplusProduct, hbeat, hmarginPos, hfreeWeightPos, hlineWeightPos]

/-- **Equal complement weights kill the tilt outright.**  The cross identity
`Gtz.oneLine_crossIdentity` says the complement's WEIGHTED height-times-shadow
readings cancel exactly against any in-plane probe.  When the complement
weights are all equal that common weight factors out, so the UNWEIGHTED tilt --
the single quantity the Schur complement subtracts -- vanishes identically.
The third input of `Gtz.posDef_of_coverMargin_of_tiltBound` is then not merely
bounded but discharged. -/
theorem complement_tilt_vanishes_of_equalWeights {size : ℕ} (design : WeightedDesign size 3)
    (lineTriple : Finset (Fin size)) (unitNormal probe : Fin 3 → ℝ) (commonWeight : ℝ)
    (hprobeFlat : probe ⬝ᵥ unitNormal = 0)
    (horth : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hequal : ∀ freeLabel ∈ lineTripleᶜ, design.weight freeLabel = commonWeight)
    (hcommonPos : 0 < commonWeight) :
    ∑ freeLabel ∈ lineTripleᶜ,
        (design.atom freeLabel ⬝ᵥ unitNormal) * (design.atom freeLabel ⬝ᵥ probe) = 0 := by
  have hcross := oneLine_crossIdentity design lineTriple unitNormal probe hprobeFlat horth
  have hfactor : ∑ freeLabel ∈ lineTripleᶜ, design.weight freeLabel
        * ((design.atom freeLabel ⬝ᵥ unitNormal) * (design.atom freeLabel ⬝ᵥ probe))
      = commonWeight * ∑ freeLabel ∈ lineTripleᶜ,
          (design.atom freeLabel ⬝ᵥ unitNormal) * (design.atom freeLabel ⬝ᵥ probe) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun freeLabel hmem => by rw [hequal freeLabel hmem]
  rw [hfactor] at hcross
  rcases mul_eq_zero.mp hcross with hzero | hzero
  · exact absurd hzero (ne_of_gt hcommonPos)
  · exact hzero

/-- **The free triple strictly dominates whenever its weights are equal and the
line is thin.**  With the tilt discharged, the only surviving requirement is
the in-plane cover -- and `Gtz.complementShadow_coverMargin_of_lineMassCeiling`
buys that from a ceiling on the line atoms' weighted in-plane reading.  The
surplus comes free from `Gtz.complement_surplus_ge_lineWeight`.

So on the one-line stratum the chartless residual is DISCHARGED at every
design whose three free atoms share a weight and whose line mass stays below
`1 - (1 + margin) * commonWeight` of the probe norm.  That is a genuine
uniform region of the stratum, and the first one on which the residual is
proved rather than assumed. -/
theorem oneLine_freeTriple_posDef_of_equalWeights (design : WeightedDesign 6 3)
    (unitNormal : Fin 3 → ℝ) (commonWeight lineMassCeiling margin : ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (horth : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hcommonPos : 0 < commonWeight)
    (hequal : ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      design.weight freeLabel = commonWeight)
    (hlineMass : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 →
      ∑ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
          design.weight lineLabel * (design.atom lineLabel ⬝ᵥ probe) ^ 2
        ≤ lineMassCeiling * (probe ⬝ᵥ probe))
    (hmarginPos : 0 < margin)
    (hmarginFits : (1 + margin) * commonWeight ≤ 1 - lineMassCeiling) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  have hcompl : (({0, 1, 2} : Finset (Fin 6)))ᶜ = ({3, 4, 5} : Finset (Fin 6)) := by decide
  have hsumThree : ∀ valueOf : Fin 6 → ℝ,
      ∑ selectedLabel ∈ ({3, 4, 5} : Finset (Fin 6)), valueOf selectedLabel
        = valueOf 3 + valueOf 4 + valueOf 5 := by
    intro valueOf
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      add_assoc]
  have hlineWeightPos : 0 < ∑ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)), design.weight lineLabel :=
    Finset.sum_pos (fun label _ => design.weight_pos label) ⟨0, by decide⟩
  have hfreeWeightPos : 0 < ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)), design.weight freeLabel :=
    Finset.sum_pos (fun label _ => design.weight_pos label) ⟨3, by decide⟩
  have hsurplusProduct := complement_surplus_ge_lineWeight design ({0, 1, 2} : Finset (Fin 6))
    unitNormal hunit horth
  rw [hcompl] at hsurplusProduct
  have hheightSum : (design.atom 3 ⬝ᵥ unitNormal) ^ 2 + (design.atom 4 ⬝ᵥ unitNormal) ^ 2
      + (design.atom 5 ⬝ᵥ unitNormal) ^ 2
      = ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
          (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 :=
    (hsumThree (fun freeLabel => (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2)).symm
  have hsurplus : 1 < (design.atom 3 ⬝ᵥ unitNormal) ^ 2 + (design.atom 4 ⬝ᵥ unitNormal) ^ 2
      + (design.atom 5 ⬝ᵥ unitNormal) ^ 2 := by
    rw [hheightSum]
    nlinarith [hsurplusProduct, hlineWeightPos, hfreeWeightPos]
  refine posDef_of_coverMargin_of_tiltBound design 3 4 5 unitNormal margin 0
    (by decide) (by decide) (by decide) hunit hsurplus ?_ ?_ ?_
  · intro probe hprobeFlat
    have hcover := complementShadow_coverMargin_of_lineMassCeiling design
      ({0, 1, 2} : Finset (Fin 6)) probe commonWeight lineMassCeiling margin hcommonPos
      (by rw [hcompl]; exact fun freeLabel hmem => le_of_eq (hequal freeLabel hmem))
      (hlineMass probe hprobeFlat) hmarginFits
    rw [hcompl, hsumThree (fun freeLabel => (design.atom freeLabel ⬝ᵥ probe) ^ 2)] at hcover
    exact hcover
  · intro probe hprobeFlat
    have hvanish := complement_tilt_vanishes_of_equalWeights design
      ({0, 1, 2} : Finset (Fin 6)) unitNormal probe commonWeight hprobeFlat horth
      (by rw [hcompl]; exact hequal) hcommonPos
    rw [hcompl, hsumThree (fun freeLabel =>
      (design.atom freeLabel ⬝ᵥ unitNormal) * (design.atom freeLabel ⬝ᵥ probe))] at hvanish
    rw [hvanish]
    simp
  · rw [hheightSum]
    nlinarith [hsurplusProduct, hmarginPos, hlineWeightPos, hfreeWeightPos]

end Gtz
