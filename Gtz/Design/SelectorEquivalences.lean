/-
# Selector equivalences, the leverage floor, and the in-scope LLF refutation

The chartless residual is restated twice, each an EQUIVALENCE, each spending
something the tie already hands over.  `PatternStrictDominatorSelector` drops
the unit normal outright -- the producer pair IS positive definiteness.
`PatternStrictDominatorSelectorGivenOvercoverer` additionally receives the
strictly-over-covering outside atom and its strict heaviness, both free by
weighted Parseval and one Cauchy-Schwarz, so nothing is assumed.

The LEVERAGE FLOOR: two vectors in three-space always share a nonzero
orthogonal, so an atom at leverage exactly one can be isolated inside any
card-3 subset and kills it.  Heaviness permits leverage exactly one, hence
heaviness alone never selects.

The FLAT-PAIR obstructions: at two atoms flat against a unit direction the
third atom's in-plane shadow is worth nothing -- tilting the probe off the
plane annihilates it and only ADDS to the norm being covered -- so the flat
pair alone must dominate in-plane, and a short third atom kills the subset at
the normal itself.  Together with `Gtz.oneLine_planeCover_of_inPlaneExcess`
this makes the two-line-plus-one-free route an exact equivalence.

The IN-SCOPE REFUTATION: `tightLlfDesign` satisfies EVERY antecedent of the
chartless residual at the one-line pattern -- the pattern, heaviness, the weak
dominator `{0,1,3}`, and its nonzero tight direction `(0,8,-3)` -- and none of
its nine two-line-plus-one-free subsets dominates strictly.  So that anatomy
cannot be the selector even inside the antecedent's own region, and
`oneLine_planeCover_of_inPlaneExcess` is a DEAD ROUTE retained only as the
exact statement of what fails.
-/
import Gtz.Design.InPlaneRestriction

set_option maxHeartbeats 4000000

namespace Gtz
open Matrix


theorem firstAxisUnit : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ ![1, 0, 0] = 1 := by
  simp [dotProduct, Fin.sum_univ_three]

theorem producerPair_iff_posDef {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) :
    (∃ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1 ∧
        (1 < ∑ selectedLabel ∈ selected,
          (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) ∧
        ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
          (∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe)
              * (design.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2
            < ((∑ selectedLabel ∈ selected,
                  (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
              * ((∑ selectedLabel ∈ selected,
                    (design.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe))
      ↔ (subsetSum design selected - 1).PosDef := by
  constructor
  · rintro ⟨unitNormal, hunit, hsurplus, hcover⟩
    exact posDef_of_normalSurplus_planeCover design selected unitNormal hunit
      hsurplus hcover
  · intro hposDef
    exact ⟨![1, 0, 0], firstAxisUnit,
      (normalSurplus_planeCover_of_posDef design selected _ firstAxisUnit hposDef).1,
      (normalSurplus_planeCover_of_posDef design selected _ firstAxisUnit hposDef).2⟩

/-! ### Step 2: the global collapse -/

/-- **The strict-dominator selector at a pattern.** -/
def PatternStrictDominatorSelector {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∀ design : WeightedDesign size 3, HasLinePattern design pattern →
    (∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) →
    ∀ (dominator : Finset (Fin size)) (tightDir : Fin 3 → ℝ),
      dominator.card = 3 → Dominates design dominator →
      tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0 →
      ∃ selected : Finset (Fin size),
        selected.card = 3 ∧ (subsetSum design selected - 1).PosDef

theorem patternTightDominatedCoverProperty_iff_strictDominatorSelector
    {size : ℕ} (pattern : LinePattern size) :
    PatternTightDominatedCoverProperty pattern
      ↔ PatternStrictDominatorSelector pattern := by
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
    exact ⟨selected, ![1, 0, 0], hcardSelected, firstAxisUnit,
      (normalSurplus_planeCover_of_posDef design selected _ firstAxisUnit hposDef).1,
      (normalSurplus_planeCover_of_posDef design selected _ firstAxisUnit hposDef).2⟩

/-! ### The tight-direction mining -/

/-- **Every atom of a tight subset under-covers its tight direction.** -/
theorem tightSubsetAtom_reading_le_normSq {size rank : ℕ}
    (design : WeightedDesign size rank) (dominator : Finset (Fin size))
    {tightDir : Fin rank → ℝ}
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0)
    {selectedLabel : Fin size} (hmem : selectedLabel ∈ dominator) :
    (design.atom selectedLabel ⬝ᵥ tightDir) ^ 2 ≤ tightDir ⬝ᵥ tightDir := by
  have hrayleigh : ∑ otherLabel ∈ dominator,
      (design.atom otherLabel ⬝ᵥ tightDir) ^ 2 = tightDir ⬝ᵥ tightDir :=
    tightDirection_rayleigh_identity design dominator htight
  have hsingle : (design.atom selectedLabel ⬝ᵥ tightDir) ^ 2
      ≤ ∑ otherLabel ∈ dominator, (design.atom otherLabel ⬝ᵥ tightDir) ^ 2 :=
    Finset.single_le_sum (f := fun otherLabel =>
      (design.atom otherLabel ⬝ᵥ tightDir) ^ 2)
      (fun otherLabel _ => sq_nonneg _) hmem
  rw [hrayleigh] at hsingle
  exact hsingle

/-- **Some atom of a tight subset strictly under-covers**, whenever the subset
has at least two members and the tight direction is nonzero. -/
theorem exists_tightSubsetAtom_reading_lt_normSq {size rank : ℕ}
    (design : WeightedDesign size rank) (dominator : Finset (Fin size))
    {tightDir : Fin rank → ℝ} (htightNe : tightDir ≠ 0)
    (hcardTwo : 2 ≤ dominator.card)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    ∃ selectedLabel ∈ dominator,
      (design.atom selectedLabel ⬝ᵥ tightDir) ^ 2 < tightDir ⬝ᵥ tightDir := by
  by_contra hcontra
  push Not at hcontra
  have hrayleigh : ∑ otherLabel ∈ dominator,
      (design.atom otherLabel ⬝ᵥ tightDir) ^ 2 = tightDir ⬝ᵥ tightDir :=
    tightDirection_rayleigh_identity design dominator htight
  have hnormPos : 0 < tightDir ⬝ᵥ tightDir := dotProduct_self_pos htightNe
  have heach : ∀ otherLabel ∈ dominator,
      tightDir ⬝ᵥ tightDir ≤ (design.atom otherLabel ⬝ᵥ tightDir) ^ 2 :=
    fun otherLabel hmem => hcontra otherLabel hmem
  have hlower : (dominator.card : ℝ) * (tightDir ⬝ᵥ tightDir)
      ≤ ∑ otherLabel ∈ dominator, (design.atom otherLabel ⬝ᵥ tightDir) ^ 2 := by
    calc (dominator.card : ℝ) * (tightDir ⬝ᵥ tightDir)
        = ∑ _otherLabel ∈ dominator, tightDir ⬝ᵥ tightDir := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum heach
  rw [hrayleigh] at hlower
  have hcardReal : (2 : ℝ) ≤ (dominator.card : ℝ) := by exact_mod_cast hcardTwo
  nlinarith [hnormPos, hlower, hcardReal]

theorem exists_commonOrthogonal_of_pair (firstVec secondVec : Fin 3 → ℝ) :
    ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
      firstVec ⬝ᵥ probe = 0 ∧ secondVec ⬝ᵥ probe = 0 := by
  set flatMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
    !![firstVec 0, firstVec 1, firstVec 2;
       secondVec 0, secondVec 1, secondVec 2;
       0, 0, 0] with hflatMatrix
  have hdet : flatMatrix.det = 0 := by
    rw [hflatMatrix, Matrix.det_fin_three]
    simp
  obtain ⟨probe, hprobeNe, hprobeNull⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨probe, hprobeNe, ?_, ?_⟩
  · have hrow := congrFun hprobeNull 0
    simpa [hflatMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hrow
  · have hrow := congrFun hprobeNull 1
    simpa [hflatMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hrow

/-! ### The leverage floor -/

/-- **The leverage floor, in annihilated form.**  If a probe kills every atom of
`selected` except one, and that one has leverage at most one, the gap cannot be
positive definite. -/
theorem notPosDef_of_leverage_le_one_of_annihilated {size : ℕ}
    (design : WeightedDesign size 3) (selected : Finset (Fin size))
    {lightLabel : Fin size} (hmem : lightLabel ∈ selected)
    (probe : Fin 3 → ℝ) (hprobeNe : probe ≠ 0)
    (hannihilated : ∀ otherLabel ∈ selected, otherLabel ≠ lightLabel →
      design.atom otherLabel ⬝ᵥ probe = 0)
    (hlight : leverageOf (design.atom lightLabel) ≤ 1) :
    ¬ (subsetSum design selected - 1).PosDef := by
  intro hposDef
  have hvalue := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form] at hvalue
  have hcollapse : ∑ selectedLabel ∈ selected,
      (design.atom selectedLabel ⬝ᵥ probe) ^ 2
      = (design.atom lightLabel ⬝ᵥ probe) ^ 2 := by
    refine Finset.sum_eq_single_of_mem lightLabel hmem ?_
    intro otherLabel hotherMem hotherNe
    rw [hannihilated otherLabel hotherMem hotherNe]
    ring
  rw [hcollapse] at hvalue
  have hcauchy : (design.atom lightLabel ⬝ᵥ probe) ^ 2
      ≤ leverageOf (design.atom lightLabel) * (probe ⬝ᵥ probe) :=
    atomOverlap_sq_le_leverage_mul_normSq (design.atom lightLabel) probe
  have hnormPos : 0 < probe ⬝ᵥ probe :=
    lt_of_le_of_ne (dotProduct_self_nonneg probe)
      (fun hzero => hprobeNe (dotProduct_self_eq_zero.mp hzero.symm))
  nlinarith [hvalue, hcauchy, hnormPos]

/-- **Every atom of a strictly dominating card-3 subset is STRICTLY heavy.**  The
heaviness antecedent `1 <= leverageOf` is therefore exactly not enough for
membership: an atom sitting at the heaviness floor is excluded from every strict
dominator, so it poisons all ten card-3 subsets that contain it. -/
theorem one_lt_leverage_of_mem_of_posDef {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hcard : selected.card = 3)
    {selectedLabel : Fin size} (hmem : selectedLabel ∈ selected)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    1 < leverageOf (design.atom selectedLabel) := by
  by_contra hcontra
  push Not at hcontra
  have hcardErase : (selected.erase selectedLabel).card = 2 := by
    rw [Finset.card_erase_of_mem hmem, hcard]
  obtain ⟨otherFirst, otherSecond, _hne, hpair⟩ := Finset.card_eq_two.mp hcardErase
  obtain ⟨probe, hprobeNe, hfirstOrth, hsecondOrth⟩ :=
    exists_commonOrthogonal_of_pair (design.atom otherFirst) (design.atom otherSecond)
  refine notPosDef_of_leverage_le_one_of_annihilated design selected hmem probe
    hprobeNe ?_ hcontra hposDef
  intro otherLabel hotherMem hotherNe
  have hinErase : otherLabel ∈ selected.erase selectedLabel :=
    Finset.mem_erase.mpr ⟨hotherNe, hotherMem⟩
  rw [hpair] at hinErase
  rcases Finset.mem_insert.mp hinErase with hleft | hright
  · rw [hleft]; exact hfirstOrth
  · rw [Finset.mem_singleton.mp hright]; exact hsecondOrth

/-! ### The flat-pair obstruction -/

/-- **A card-3 subset with two flat atoms dies at any in-plane probe where the
FLAT PAIR ALONE fails to over-cover.**  The third atom's in-plane shadow is no
help whatsoever: tilting the probe off the plane by the third atom's own height
annihilates it, and the tilt only ADDS to the norm being covered.  This is the
exact converse of `Gtz.oneLine_planeCover_of_inPlaneExcess`, and it makes the
in-plane domination of the flat pair a NECESSARY condition. -/
theorem notPosDef_of_flatPair_inPlane_deficit {size : ℕ} (design : WeightedDesign size 3)
    (flatFirst flatSecond thirdLabel : Fin size)
    (hfirstSecond : flatFirst ≠ flatSecond) (hfirstThird : flatFirst ≠ thirdLabel)
    (hsecondThird : flatSecond ≠ thirdLabel)
    (unitNormal probe : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hfirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hsecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hprobeFlat : probe ⬝ᵥ unitNormal = 0) (hprobeNe : probe ≠ 0)
    (hdeficit : (design.atom flatFirst ⬝ᵥ probe) ^ 2
        + (design.atom flatSecond ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe) :
    ¬ (subsetSum design {flatFirst, flatSecond, thirdLabel} - 1).PosDef := by
  intro hposDef
  have hsplit : ∀ vec : Fin 3 → ℝ,
      ∑ selectedLabel ∈ ({flatFirst, flatSecond, thirdLabel} : Finset (Fin size)),
          (design.atom selectedLabel ⬝ᵥ vec) ^ 2
        = (design.atom flatFirst ⬝ᵥ vec) ^ 2
          + (design.atom flatSecond ⬝ᵥ vec) ^ 2
          + (design.atom thirdLabel ⬝ᵥ vec) ^ 2 := by
    intro vec
    rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
      Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton]
    ring
  have hnormalAgainstProbe : unitNormal ⬝ᵥ probe = 0 := by
    rw [dotProduct_comm]; exact hprobeFlat
  by_cases hthirdHeight : design.atom thirdLabel ⬝ᵥ unitNormal = 0
  · have hnormalNe : unitNormal ≠ 0 := by
      intro hzero
      rw [hzero] at hunit
      simp at hunit
    have hvalue := hposDef.dotProduct_mulVec_pos hnormalNe
    rw [star_trivial, dominationGap_form, hsplit, hfirstFlat, hsecondFlat,
      hthirdHeight, hunit] at hvalue
    norm_num at hvalue
  · set tilt : ℝ := (design.atom thirdLabel ⬝ᵥ probe)
      / (design.atom thirdLabel ⬝ᵥ unitNormal) with htilt
    set tiltedProbe : Fin 3 → ℝ := probe - tilt • unitNormal with htiltedProbe
    have hreading : ∀ atomLabel : Fin size,
        design.atom atomLabel ⬝ᵥ tiltedProbe
          = (design.atom atomLabel ⬝ᵥ probe)
            - tilt * (design.atom atomLabel ⬝ᵥ unitNormal) := by
      intro atomLabel
      rw [htiltedProbe, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have hfirstReading : design.atom flatFirst ⬝ᵥ tiltedProbe
        = design.atom flatFirst ⬝ᵥ probe := by
      rw [hreading, hfirstFlat]; ring
    have hsecondReading : design.atom flatSecond ⬝ᵥ tiltedProbe
        = design.atom flatSecond ⬝ᵥ probe := by
      rw [hreading, hsecondFlat]; ring
    have hthirdReading : design.atom thirdLabel ⬝ᵥ tiltedProbe = 0 := by
      rw [hreading, htilt, div_mul_cancel₀ _ hthirdHeight]
      ring
    have hnorm : tiltedProbe ⬝ᵥ tiltedProbe = probe ⬝ᵥ probe + tilt ^ 2 := by
      have hexpand : tiltedProbe ⬝ᵥ tiltedProbe
          = probe ⬝ᵥ probe - tilt * (probe ⬝ᵥ unitNormal)
            - tilt * (unitNormal ⬝ᵥ probe)
            + tilt * tilt * (unitNormal ⬝ᵥ unitNormal) := by
        simp only [htiltedProbe, sub_dotProduct, dotProduct_sub, smul_dotProduct,
          dotProduct_smul, smul_eq_mul]
        ring
      rw [hexpand, hunit, hprobeFlat, hnormalAgainstProbe]
      ring
    have hnonZero : tiltedProbe ≠ 0 := by
      intro hzero
      have hpair : tiltedProbe ⬝ᵥ probe = probe ⬝ᵥ probe := by
        rw [htiltedProbe, sub_dotProduct, smul_dotProduct, smul_eq_mul,
          hnormalAgainstProbe]
        ring
      rw [hzero, zero_dotProduct] at hpair
      exact hprobeNe (dotProduct_self_eq_zero.mp hpair.symm)
    have hvalue := hposDef.dotProduct_mulVec_pos hnonZero
    rw [star_trivial, dominationGap_form, hsplit, hfirstReading, hsecondReading,
      hthirdReading, hnorm] at hvalue
    nlinarith [hvalue, hdeficit, sq_nonneg tilt]

/-- **The landed LLF reduction is EXACT**: the in-plane pair domination it needs
is not merely sufficient but necessary.  Read against
`Gtz.oneLine_planeCover_of_inPlaneExcess`, the two together say the two-line-atom
plus one-free-atom anatomy is available exactly when the line PAIR already
dominates the identity inside the line plane. -/
theorem flatPair_inPlane_domination_of_posDef {size : ℕ} (design : WeightedDesign size 3)
    (flatFirst flatSecond thirdLabel : Fin size)
    (hfirstSecond : flatFirst ≠ flatSecond) (hfirstThird : flatFirst ≠ thirdLabel)
    (hsecondThird : flatSecond ≠ thirdLabel)
    (unitNormal probe : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hfirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hsecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hprobeFlat : probe ⬝ᵥ unitNormal = 0) (hprobeNe : probe ≠ 0)
    (hposDef : (subsetSum design {flatFirst, flatSecond, thirdLabel} - 1).PosDef) :
    probe ⬝ᵥ probe < (design.atom flatFirst ⬝ᵥ probe) ^ 2
      + (design.atom flatSecond ⬝ᵥ probe) ^ 2 := by
  by_contra hcontra
  push Not at hcontra
  exact notPosDef_of_flatPair_inPlane_deficit design flatFirst flatSecond thirdLabel
    hfirstSecond hfirstThird hsecondThird unitNormal probe hunit hfirstFlat
    hsecondFlat hprobeFlat hprobeNe hcontra hposDef

/-! ### A heavy one-line design whose line atoms sit in a narrow cone -/

/-- Two of the three line atoms are STRICTLY heavy; the middle one sits exactly
on the heaviness floor. -/
theorem narrowCone_lineLeverages :
    leverageOf (narrowConeDesign.atom 0) = 5/4
      ∧ leverageOf (narrowConeDesign.atom 1) = 1
      ∧ leverageOf (narrowConeDesign.atom 2) = 5/4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [leverageOf, Fin.sum_univ_three, narrowConeDesign, narrowConeAtom,
      Matrix.cons_val_two, Matrix.tail_cons]

/-! ### The free triple dominates strictly -/

theorem narrowCone_freeTripleGap_eq :
    subsetSum narrowConeDesign {3, 4, 5} - 1
      = Matrix.of ![![2, 0, -2], ![0, 119/9, 0], ![-2, 0, 11]] := by
  rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [narrowConeDesign, narrowConeAtom, atomMatrix, Matrix.sub_apply] <;> norm_num

theorem narrowCone_freeTripleGap_posSemidef :
    (subsetSum narrowConeDesign {3, 4, 5} - 1).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg => ?_⟩
  · exact ((Matrix.posSemidef_sum ({3, 4, 5} : Finset (Fin 6)) fun freeLabel _ =>
      posSemidef_atomMatrix (narrowConeDesign.atom freeLabel)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, narrowCone_freeTripleGap_form]
    positivity

theorem narrowConeDesign_hasStrictDominator :
    ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧
      (subsetSum narrowConeDesign dominator - 1).PosDef :=
  ⟨{3, 4, 5}, by decide, narrowCone_freeTripleGap_posDef⟩

/-! ### The antecedents supply the over-coverer for free -/

/-- **An atom that strictly over-covers a direction is strictly heavy.** -/
theorem overcoveringAtom_is_strictly_heavy {rank : ℕ} (atomVec tightDir : Fin rank → ℝ)
    (htightNe : tightDir ≠ 0)
    (hover : tightDir ⬝ᵥ tightDir < (atomVec ⬝ᵥ tightDir) ^ 2) :
    1 < leverageOf atomVec := by
  have hcauchy := atomOverlap_sq_le_leverage_mul_normSq atomVec tightDir
  have hnormPos := dotProduct_self_pos htightNe
  nlinarith [hcauchy, hnormPos, hover]

/-- **The strict-dominator selector with the over-coverer handed over.**  Same
Prop as `Gtz.PatternStrictDominatorSelector`, but the antecedents now include the
strictly-over-covering outside atom and its strict heaviness -- both of which the
tie supplies for free, so nothing is being assumed. -/
def PatternStrictDominatorSelectorGivenOvercoverer {size : ℕ}
    (pattern : LinePattern size) : Prop :=
  ∀ design : WeightedDesign size 3, HasLinePattern design pattern →
    (∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) →
    ∀ (dominator : Finset (Fin size)) (tightDir : Fin 3 → ℝ),
      dominator.card = 3 → Dominates design dominator →
      tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0 →
      ∀ overLabel : Fin size, overLabel ∉ dominator →
        tightDir ⬝ᵥ tightDir < (design.atom overLabel ⬝ᵥ tightDir) ^ 2 →
        1 < leverageOf (design.atom overLabel) →
        ∃ selected : Finset (Fin size),
          selected.card = 3 ∧ (subsetSum design selected - 1).PosDef

theorem patternStrictDominatorSelector_iff_givenOvercoverer {size : ℕ}
    (pattern : LinePattern size) :
    PatternStrictDominatorSelector pattern
      ↔ PatternStrictDominatorSelectorGivenOvercoverer pattern := by
  constructor
  · intro hselector design hpattern hheavy dominator tightDir hcard hdominates
      htightNe htight _overLabel _hnotMem _hover _hheavyOver
    exact hselector design hpattern hheavy dominator tightDir hcard hdominates
      htightNe htight
  · intro hselector design hpattern hheavy dominator tightDir hcard hdominates
      htightNe htight
    have hcardTwo : 2 ≤ dominator.card := by rw [hcard]; omega
    obtain ⟨overLabel, hnotMem, hover⟩ :=
      exists_outsideAtom_strictly_overcovers_tightDirection design dominator tightDir
        hcardTwo htightNe htight
    exact hselector design hpattern hheavy dominator tightDir hcard hdominates
      htightNe htight overLabel hnotMem hover
      (overcoveringAtom_is_strictly_heavy (design.atom overLabel) tightDir htightNe hover)

/-- **The full collapse.**  The registry-axiom Prop is the same statement as
"given a tie's weak dominator, a tight direction, and the over-covering outside
atom the tie hands over for free, produce a card-3 subset with a positive
definite gap".  Both quantified inequalities and the unit-normal existential of
`Gtz.PatternTightDominatedCoverProperty` are gone. -/
theorem patternTightDominatedCoverProperty_iff_givenOvercoverer {size : ℕ}
    (pattern : LinePattern size) :
    PatternTightDominatedCoverProperty pattern
      ↔ PatternStrictDominatorSelectorGivenOvercoverer pattern :=
  (patternTightDominatedCoverProperty_iff_strictDominatorSelector pattern).trans
    (patternStrictDominatorSelector_iff_givenOvercoverer pattern)

/-! ### The LLF anatomy is not a uniform selector

`Gtz.narrowConeDesign` is a heavy one-line design in which EVERY card-3 subset
built from two line atoms and one free atom fails to dominate strictly, while
the free triple does dominate strictly.  Two of its three line atoms carry
leverage `5/4`, STRICTLY above the heaviness floor, and their pair `{0,2}` fails
the in-plane domination that `Gtz.flatPair_inPlane_domination_of_posDef` shows is
necessary -- so at least one of the nine failures is not a floor artefact.  The
six subsets built on a pair containing atom `1` die through the floor instead
(that atom's leverage is exactly one). -/

theorem narrowCone_unitAtom_leverage : leverageOf (narrowConeDesign.atom 1) = 1 := by
  norm_num [leverageOf, Fin.sum_univ_three, narrowConeDesign, narrowConeAtom,
    Matrix.cons_val_two, Matrix.tail_cons]

theorem narrowCone_notPosDef_of_unitAtomFirst (otherFirst otherSecond : Fin 6) :
    ¬ (subsetSum narrowConeDesign {1, otherFirst, otherSecond} - 1).PosDef := by
  obtain ⟨probe, hprobeNe, hfirstOrth, hsecondOrth⟩ :=
    exists_commonOrthogonal_of_pair (narrowConeDesign.atom otherFirst)
      (narrowConeDesign.atom otherSecond)
  refine notPosDef_of_leverage_le_one_of_annihilated narrowConeDesign
    {1, otherFirst, otherSecond} (Finset.mem_insert_self _ _) probe hprobeNe ?_
    (le_of_eq narrowCone_unitAtom_leverage)
  intro otherLabel hmem hotherNe
  rcases Finset.mem_insert.mp hmem with hhead | htail
  · exact absurd hhead hotherNe
  · rcases Finset.mem_insert.mp htail with hsecond | hthird
    · rw [hsecond]; exact hfirstOrth
    · rw [Finset.mem_singleton.mp hthird]; exact hsecondOrth

theorem narrowCone_notPosDef_of_unitAtomSecond (otherFirst otherSecond : Fin 6) :
    ¬ (subsetSum narrowConeDesign {otherFirst, 1, otherSecond} - 1).PosDef := by
  rw [Finset.insert_comm]
  exact narrowCone_notPosDef_of_unitAtomFirst otherFirst otherSecond

theorem narrowCone_pairZeroTwo_notPosDef (freeLabel : Fin 6)
    (hfirstFree : (0 : Fin 6) ≠ freeLabel) (hsecondFree : (2 : Fin 6) ≠ freeLabel) :
    ¬ (subsetSum narrowConeDesign {0, 2, freeLabel} - 1).PosDef := by
  have hprobeNe : (![0, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hentry := congrFun hzero 1
    norm_num at hentry
  refine notPosDef_of_flatPair_inPlane_deficit narrowConeDesign 0 2 freeLabel
    (by decide) hfirstFree hsecondFree ![0, 0, 1] ![0, 1, 0] ?_ ?_ ?_ ?_ hprobeNe ?_
  · simp [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]
  · simp [dotProduct, Fin.sum_univ_three, narrowConeDesign, narrowConeAtom,
      Matrix.cons_val_two, Matrix.tail_cons]
  · simp [dotProduct, Fin.sum_univ_three, narrowConeDesign, narrowConeAtom,
      Matrix.cons_val_two, Matrix.tail_cons]
  · simp [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]
  · norm_num [dotProduct, Fin.sum_univ_three, narrowConeDesign, narrowConeAtom,
      Matrix.cons_val_two, Matrix.tail_cons]

theorem narrowCone_pairTwoZero_notPosDef (freeLabel : Fin 6)
    (hfirstFree : (2 : Fin 6) ≠ freeLabel) (hsecondFree : (0 : Fin 6) ≠ freeLabel) :
    ¬ (subsetSum narrowConeDesign {2, 0, freeLabel} - 1).PosDef := by
  rw [Finset.insert_comm]
  exact narrowCone_pairZeroTwo_notPosDef freeLabel hsecondFree hfirstFree

/-- **All nine two-line-plus-one-free subsets of the narrow-cone design fail.** -/
theorem narrowCone_llf_notPosDef (lineFirst lineSecond freeLabel : Fin 6)
    (hfirst : lineFirst = 0 ∨ lineFirst = 1 ∨ lineFirst = 2)
    (hsecond : lineSecond = 0 ∨ lineSecond = 1 ∨ lineSecond = 2)
    (hne : lineFirst ≠ lineSecond)
    (hfree : freeLabel = 3 ∨ freeLabel = 4 ∨ freeLabel = 5) :
    ¬ (subsetSum narrowConeDesign {lineFirst, lineSecond, freeLabel} - 1).PosDef := by
  have hzeroFree : (0 : Fin 6) ≠ freeLabel := by
    rcases hfree with rfl | rfl | rfl <;> decide
  have htwoFree : (2 : Fin 6) ≠ freeLabel := by
    rcases hfree with rfl | rfl | rfl <;> decide
  rcases hfirst with rfl | rfl | rfl <;> rcases hsecond with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact narrowCone_notPosDef_of_unitAtomSecond 0 freeLabel
  · exact narrowCone_pairZeroTwo_notPosDef freeLabel hzeroFree htwoFree
  · exact narrowCone_notPosDef_of_unitAtomFirst 0 freeLabel
  · exact absurd rfl hne
  · exact narrowCone_notPosDef_of_unitAtomFirst 2 freeLabel
  · exact narrowCone_pairTwoZero_notPosDef freeLabel htwoFree hzeroFree
  · exact narrowCone_notPosDef_of_unitAtomSecond 2 freeLabel
  · exact absurd rfl hne

/-- The STRICTLY heavy line pair `{0,2}` (leverages `5/4` each) still fails the
in-plane domination a two-line-plus-one-free subset needs: against the in-plane
probe `(0,1,0)` the pair reads only `1/2` against the probe's own norm `1`. -/
theorem narrowCone_strictlyHeavyPair_inPlane_deficit :
    (narrowConeDesign.atom 0 ⬝ᵥ ![0, 1, 0]) ^ 2
        + (narrowConeDesign.atom 2 ⬝ᵥ ![0, 1, 0]) ^ 2 = 1/2
      ∧ (![0, 1, 0] : Fin 3 → ℝ) ⬝ᵥ ![0, 1, 0] = 1 := by
  constructor <;>
    norm_num [dotProduct, Fin.sum_univ_three, narrowConeDesign, narrowConeAtom,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- The uniform two-line-plus-one-free selector at the one-line pattern. -/
def OneLineLlfSelector : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
    ∃ lineFirst lineSecond freeLabel : Fin 6,
      (lineFirst = 0 ∨ lineFirst = 1 ∨ lineFirst = 2) ∧
      (lineSecond = 0 ∨ lineSecond = 1 ∨ lineSecond = 2) ∧
      lineFirst ≠ lineSecond ∧
      (freeLabel = 3 ∨ freeLabel = 4 ∨ freeLabel = 5) ∧
      (subsetSum design {lineFirst, lineSecond, freeLabel} - 1).PosDef

/-- **REFUTATION: the LLF anatomy is not a uniform selector on the heavy one-line
stratum.**  The narrow-cone design realises the pattern, is heavy, HAS a strictly
dominating triple (the free triple), and yet no two-line-plus-one-free subset of
it dominates strictly.

SCOPE.  This refutes the UNCONDITIONED LLF rule -- the shape an anatomy-first
strategy or `Gtz.oneLine_planeCover_of_inPlaneExcess` would be used at.  It does
NOT refute an LLF route conditioned on the tightness antecedent of
`Gtz.PatternTightDominatedCoverProperty`, which asks for a card-3 subset whose
gap is positive SEMIdefinite and SINGULAR.  The free triple supplies no such
subset here: its gap is positive DEFINITE
(`Gtz.narrowCone_freeTripleGap_posDef`), hence has no tight direction.  Whether
any of the other nineteen card-3 subsets is positive semidefinite is NOT settled
in kernel -- an exhaustive exact-rational check outside the kernel says none is,
but that check is not a theorem here. -/
theorem not_oneLineLlfSelector : ¬ OneLineLlfSelector := by
  intro hselector
  obtain ⟨lineFirst, lineSecond, freeLabel, hfirst, hsecond, hne, hfree, hposDef⟩ :=
    hselector narrowConeDesign narrowConeDesign_hasLinePattern narrowConeDesign_heavy
  exact narrowCone_llf_notPosDef lineFirst lineSecond freeLabel hfirst hsecond hne
    hfree hposDef


/-! ### The short-third obstruction -/

/-- **A card-3 subset with two flat atoms and a SHORT third dies at the normal.**
If the third atom's height against the unit normal has square at most one, the
gap's value at the normal itself is nonpositive. -/
theorem notPosDef_of_flatPair_shortThird {size : ℕ} (design : WeightedDesign size 3)
    (flatFirst flatSecond thirdLabel : Fin size)
    (hfirstSecond : flatFirst ≠ flatSecond) (hfirstThird : flatFirst ≠ thirdLabel)
    (hsecondThird : flatSecond ≠ thirdLabel)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hfirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hsecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hshort : (design.atom thirdLabel ⬝ᵥ unitNormal) ^ 2 ≤ 1) :
    ¬ (subsetSum design {flatFirst, flatSecond, thirdLabel} - 1).PosDef := by
  intro hposDef
  have hnormalNe : unitNormal ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp at hunit
  have hsplit : ∑ selectedLabel ∈
        ({flatFirst, flatSecond, thirdLabel} : Finset (Fin size)),
        (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2
      = (design.atom flatFirst ⬝ᵥ unitNormal) ^ 2
        + (design.atom flatSecond ⬝ᵥ unitNormal) ^ 2
        + (design.atom thirdLabel ⬝ᵥ unitNormal) ^ 2 := by
    rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
      Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton]
    ring
  have hvalue := hposDef.dotProduct_mulVec_pos hnormalNe
  rw [star_trivial, dominationGap_form, hsplit, hfirstFlat, hsecondFlat,
    hunit] at hvalue
  nlinarith [hvalue, hshort]

/-! ### An IN-SCOPE one-line design: the tightness antecedent holds and no
two-line-plus-one-free subset dominates strictly -/

noncomputable def tightLlfAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![3/2, 3/4, 0]
  | 1 => ![-3/2, 3/4, 0]
  | 2 => ![0, 1, 0]
  | 3 => ![0, 1, 3]
  | 4 => ![1, -4/3, 1]
  | 5 => ![-1, -4/3, 1]

noncomputable def tightLlfWeight : Fin 6 → ℝ
  | 0 => 8/45
  | 1 => 8/45
  | 2 => 16/45
  | 3 => 4/45
  | 4 => 1/10
  | 5 => 1/10

noncomputable def tightLlfDesign : WeightedDesign 6 3 where
  atom := tightLlfAtom
  weight := tightLlfWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [tightLlfWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [tightLlfWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [tightLlfAtom, tightLlfWeight, atomMatrix] <;> norm_num

theorem tightLlfDesign_hasLinePattern :
    HasLinePattern tightLlfDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, tightLlfDesign,
            tightLlfAtom, Matrix.cons_val_two])
          (by decide)
      | exact iff_of_true
          (by norm_num [atomBracket, tripleBracket_eq, tightLlfDesign,
            tightLlfAtom, Matrix.cons_val_two])
          (by decide)

theorem tightLlfDesign_isHeavy :
    ∀ label : Fin 6, 1 ≤ leverageOf (tightLlfDesign.atom label) := by
  intro label
  fin_cases label <;>
    norm_num [leverageOf, Fin.sum_univ_three, tightLlfDesign, tightLlfAtom,
      Matrix.cons_val_two, Matrix.tail_cons]

theorem tightLlf_unitAtom_leverage : leverageOf (tightLlfDesign.atom 2) = 1 := by
  norm_num [leverageOf, Fin.sum_univ_three, tightLlfDesign, tightLlfAtom,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The weak dominator `{0,1,3}` is itself a two-line-plus-one-free subset, and
its gap is the exact square sum `7/2 x^2 + 9/8 (y + 8z/3)^2` -- positive
semidefinite and SINGULAR. -/
theorem tightLlf_dominatorGap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum tightLlfDesign {0, 1, 3} - 1) *ᵥ vecArg)
      = 7/2 * vecArg 0 ^ 2 + 9/8 * (vecArg 1 + 8/3 * vecArg 2) ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [tightLlfDesign, tightLlfAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

theorem tightLlf_dominatorGap_posSemidef :
    (subsetSum tightLlfDesign {0, 1, 3} - 1).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 3} : Finset (Fin 6)) fun someLabel _ =>
      posSemidef_atomMatrix (tightLlfDesign.atom someLabel)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, tightLlf_dominatorGap_form]
    positivity

theorem tightLlfDesign_dominates : Dominates tightLlfDesign {0, 1, 3} :=
  tightLlf_dominatorGap_posSemidef

theorem tightLlf_tightDirection_ne_zero : (![0, 8, -3] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hentry := congrFun hzero 1
  norm_num at hentry

theorem tightLlf_tightDirection_rayleigh :
    (![0, 8, -3] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum tightLlfDesign {0, 1, 3} - 1) *ᵥ ![0, 8, -3]) = 0 := by
  rw [tightLlf_dominatorGap_form]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

theorem tightLlf_notPosDef_of_unitAtomFirst (otherFirst otherSecond : Fin 6) :
    ¬ (subsetSum tightLlfDesign {2, otherFirst, otherSecond} - 1).PosDef := by
  obtain ⟨probe, hprobeNe, hfirstOrth, hsecondOrth⟩ :=
    exists_commonOrthogonal_of_pair (tightLlfDesign.atom otherFirst)
      (tightLlfDesign.atom otherSecond)
  refine notPosDef_of_leverage_le_one_of_annihilated tightLlfDesign
    {2, otherFirst, otherSecond} (Finset.mem_insert_self _ _) probe hprobeNe ?_
    (le_of_eq tightLlf_unitAtom_leverage)
  intro otherLabel hmem hotherNe
  rcases Finset.mem_insert.mp hmem with hhead | htail
  · exact absurd hhead hotherNe
  · rcases Finset.mem_insert.mp htail with hsecond | hthird
    · rw [hsecond]; exact hfirstOrth
    · rw [Finset.mem_singleton.mp hthird]; exact hsecondOrth

theorem tightLlf_notPosDef_of_unitAtomSecond (otherFirst otherSecond : Fin 6) :
    ¬ (subsetSum tightLlfDesign {otherFirst, 2, otherSecond} - 1).PosDef := by
  rw [Finset.insert_comm]
  exact tightLlf_notPosDef_of_unitAtomFirst otherFirst otherSecond

theorem tightLlf_pairZeroOne_notPosDef (freeLabel : Fin 6)
    (hfree : freeLabel = 3 ∨ freeLabel = 4 ∨ freeLabel = 5) :
    ¬ (subsetSum tightLlfDesign {0, 1, freeLabel} - 1).PosDef := by
  rcases hfree with rfl | rfl | rfl
  · intro hposDef
    have hvalue := hposDef.dotProduct_mulVec_pos tightLlf_tightDirection_ne_zero
    rw [star_trivial, tightLlf_tightDirection_rayleigh] at hvalue
    exact lt_irrefl 0 hvalue
  · refine notPosDef_of_flatPair_shortThird tightLlfDesign 0 1 4
      (by decide) (by decide) (by decide) ![0, 0, 1] ?_ ?_ ?_ ?_ <;>
      norm_num [dotProduct, Fin.sum_univ_three, tightLlfDesign, tightLlfAtom,
        Matrix.cons_val_two, Matrix.tail_cons]
  · refine notPosDef_of_flatPair_shortThird tightLlfDesign 0 1 5
      (by decide) (by decide) (by decide) ![0, 0, 1] ?_ ?_ ?_ ?_ <;>
      norm_num [dotProduct, Fin.sum_univ_three, tightLlfDesign, tightLlfAtom,
        Matrix.cons_val_two, Matrix.tail_cons]

theorem tightLlf_pairOneZero_notPosDef (freeLabel : Fin 6)
    (hfree : freeLabel = 3 ∨ freeLabel = 4 ∨ freeLabel = 5) :
    ¬ (subsetSum tightLlfDesign {1, 0, freeLabel} - 1).PosDef := by
  rw [Finset.insert_comm]
  exact tightLlf_pairZeroOne_notPosDef freeLabel hfree

/-- **All nine two-line-plus-one-free subsets of the tight design fail.** -/
theorem tightLlf_llf_notPosDef (lineFirst lineSecond freeLabel : Fin 6)
    (hfirst : lineFirst = 0 ∨ lineFirst = 1 ∨ lineFirst = 2)
    (hsecond : lineSecond = 0 ∨ lineSecond = 1 ∨ lineSecond = 2)
    (hne : lineFirst ≠ lineSecond)
    (hfree : freeLabel = 3 ∨ freeLabel = 4 ∨ freeLabel = 5) :
    ¬ (subsetSum tightLlfDesign {lineFirst, lineSecond, freeLabel} - 1).PosDef := by
  rcases hfirst with rfl | rfl | rfl <;> rcases hsecond with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact tightLlf_pairZeroOne_notPosDef freeLabel hfree
  · exact tightLlf_notPosDef_of_unitAtomSecond 0 freeLabel
  · exact tightLlf_pairOneZero_notPosDef freeLabel hfree
  · exact absurd rfl hne
  · exact tightLlf_notPosDef_of_unitAtomSecond 1 freeLabel
  · exact tightLlf_notPosDef_of_unitAtomFirst 0 freeLabel
  · exact tightLlf_notPosDef_of_unitAtomFirst 1 freeLabel
  · exact absurd rfl hne

/-- The two-line-plus-one-free selector RESTRICTED to the tightness antecedent of
`Gtz.PatternTightDominatedCoverProperty` -- the only region where that Prop asks
for anything. -/
def OneLineLlfSelectorAtTightAntecedent : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
    ∀ (dominator : Finset (Fin 6)) (tightDir : Fin 3 → ℝ),
      dominator.card = 3 → Dominates design dominator → tightDir ≠ 0 →
      tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0 →
      ∃ lineFirst lineSecond freeLabel : Fin 6,
        (lineFirst = 0 ∨ lineFirst = 1 ∨ lineFirst = 2) ∧
        (lineSecond = 0 ∨ lineSecond = 1 ∨ lineSecond = 2) ∧
        lineFirst ≠ lineSecond ∧
        (freeLabel = 3 ∨ freeLabel = 4 ∨ freeLabel = 5) ∧
        (subsetSum design {lineFirst, lineSecond, freeLabel} - 1).PosDef

/-- **IN-SCOPE REFUTATION: no proof of the one-line class obligation can route
through the two-line-plus-one-free anatomy.**  `Gtz.tightLlfDesign` satisfies
EVERY antecedent of `Gtz.PatternTightDominatedCoverProperty` at the one-line
pattern -- it realises the pattern, it is heavy, `{0,1,3}` weakly dominates, and
`(0,8,-3)` is a nonzero tight direction of that dominator -- and yet none of its
nine two-line-plus-one-free subsets dominates strictly.  So the anatomy the
landed reduction `Gtz.oneLine_planeCover_of_inPlaneExcess` is written for cannot
be the selector, even inside the antecedent's region. -/
theorem not_oneLineLlfSelectorAtTightAntecedent :
    ¬ OneLineLlfSelectorAtTightAntecedent := by
  intro hselector
  obtain ⟨lineFirst, lineSecond, freeLabel, hfirst, hsecond, hne, hfree, hposDef⟩ :=
    hselector tightLlfDesign tightLlfDesign_hasLinePattern tightLlfDesign_isHeavy
      {0, 1, 3} ![0, 8, -3] (by decide) tightLlfDesign_dominates
      tightLlf_tightDirection_ne_zero tightLlf_tightDirection_rayleigh
  exact tightLlf_llf_notPosDef lineFirst lineSecond freeLabel hfirst hsecond hne
    hfree hposDef


end Gtz
