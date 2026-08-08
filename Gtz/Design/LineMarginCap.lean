/-
# The margin cap on a line stratum, two-sided, and two twin witnesses

Along a unit normal that every line atom is blind to, only the complement's
atoms are visible, so EVERY card-3 subset's gap has Rayleigh value at that
normal bounded above by the complement's total squared height minus one.  The
Rayleigh value at a unit vector bounds the least eigenvalue, so this caps the
margin of every strictly dominating subset simultaneously -- no selector, no
anatomy and no choice of normal can beat it.

The cap has its own FLOOR: Parseval puts the whole unit mass on the complement,
and a weighted sum is at most weight-total times value-total, so the cap is at
least `lineWeight / complementWeight`.  The two together say the margin can be
driven to zero ONLY by starving the line weight -- no in-plane angle and no
single free weight can do it.  That pins the one channel the earlier
no-uniform-floor prose could only gesture at.

Two witnesses on the two-meeting-lines twin.  `sharedAtomUnitDesign` puts the
shared atom -- the class's rigidity kernel, and the natural thing for a
selector to reach for -- at leverage exactly one, and all TEN card-3 subsets
containing it fail.  `mixedSurvivorDesign` kills the line complement `{3,4,5}`:
on the twin neither line complement is a valid selector either, and the
surviving dominators are MIXED triples taking one atom from each line.
-/
import Gtz.Design.SelectorEquivalences

set_option maxHeartbeats 4000000

namespace Gtz
open Matrix


/-- No producer pair can live at a subset whose gap is not positive definite. -/
theorem no_producerPair_of_not_posDef {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hnot : ¬ (subsetSum design selected - 1).PosDef) :
    ¬ ∃ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1 ∧
        (1 < ∑ s ∈ selected, (design.atom s ⬝ᵥ unitNormal) ^ 2) ∧
        ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
          (∑ s ∈ selected, (design.atom s ⬝ᵥ probe) * (design.atom s ⬝ᵥ unitNormal)) ^ 2
            < ((∑ s ∈ selected, (design.atom s ⬝ᵥ unitNormal) ^ 2) - 1)
              * ((∑ s ∈ selected, (design.atom s ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe) :=
  fun hexists => hnot ((producerPair_iff_posDef design selected).mp hexists)

/-! ## Part 1 -- C4 dies universally: the tie's own dominator is never a producer -/

/-- **C4 refuted, no witness needed.**  The tight direction handed over by the
sharpened property's own antecedent is a null vector of the dominator's gap, so that
gap is never positive definite; by `producerPair_iff_posDef` NO unit normal makes the
dominator a producer subset.  A selector that returns the tie's own weak dominator
can never discharge `PatternTightDominatedCoverProperty`. -/
theorem tieDominator_admits_no_producerPair {size : ℕ} (design : WeightedDesign size 3)
    (dominator : Finset (Fin size)) (tightDir : Fin 3 → ℝ) (htightNe : tightDir ≠ 0)
    (htight : tightDir ⬝ᵥ ((subsetSum design dominator - 1) *ᵥ tightDir) = 0) :
    ¬ ∃ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1 ∧
        (1 < ∑ s ∈ dominator, (design.atom s ⬝ᵥ unitNormal) ^ 2) ∧
        ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
          (∑ s ∈ dominator, (design.atom s ⬝ᵥ probe) * (design.atom s ⬝ᵥ unitNormal)) ^ 2
            < ((∑ s ∈ dominator, (design.atom s ⬝ᵥ unitNormal) ^ 2) - 1)
              * ((∑ s ∈ dominator, (design.atom s ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe) := by
  refine no_producerPair_of_not_posDef design dominator (fun hposDef => ?_)
  have hpos := hposDef.dotProduct_mulVec_pos htightNe
  rw [star_trivial, htight] at hpos
  exact lt_irrefl 0 hpos

/-! ## Part 2 -- why two flat atoms are so often useless: the plane-domination
necessary condition, and its Cauchy-Schwarz reading -/

/-- **Flat-pair plane domination.**  If two of a card-3 subset's atoms are flat
against a unit direction, positive definiteness of the gap forces the FLAT PAIR ALONE
to strictly dominate the identity on the whole orthogonal plane -- the third atom's
in-plane shadow is no help at all. -/
theorem flatPair_planeDomination_of_posDef {size : ℕ} (design : WeightedDesign size 3)
    (flatFirst flatSecond thirdLabel : Fin size) (unitNormal : Fin 3 → ℝ)
    (hdistinctFirstSecond : flatFirst ≠ flatSecond)
    (hdistinctFirstThird : flatFirst ≠ thirdLabel)
    (hdistinctSecondThird : flatSecond ≠ thirdLabel)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hfirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hsecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hposDef : (subsetSum design
      ({flatFirst, flatSecond, thirdLabel} : Finset (Fin size)) - 1).PosDef)
    (probe : Fin 3 → ℝ) (hprobeFlat : probe ⬝ᵥ unitNormal = 0) (hprobeNe : probe ≠ 0) :
    probe ⬝ᵥ probe
      < (design.atom flatFirst ⬝ᵥ probe) ^ 2 + (design.atom flatSecond ⬝ᵥ probe) ^ 2 := by
  have hsumThree : ∀ valueOf : Fin size → ℝ,
      ∑ s ∈ ({flatFirst, flatSecond, thirdLabel} : Finset (Fin size)), valueOf s
        = valueOf flatFirst + valueOf flatSecond + valueOf thirdLabel := by
    intro valueOf
    rw [Finset.sum_insert (by simp [hdistinctFirstSecond, hdistinctFirstThird]),
      Finset.sum_insert (by simp [hdistinctSecondThird]), Finset.sum_singleton, add_assoc]
  have hnormalNe : unitNormal ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp at hunit
  have hheightNe : design.atom thirdLabel ⬝ᵥ unitNormal ≠ 0 := by
    intro hzero
    have hpos := hposDef.dotProduct_mulVec_pos hnormalNe
    rw [star_trivial, dominationGap_form, hsumThree, hfirstFlat, hsecondFlat, hzero,
      hunit] at hpos
    norm_num at hpos
  set heightVal : ℝ := design.atom thirdLabel ⬝ᵥ unitNormal with hheightVal
  set shiftVal : ℝ := -(design.atom thirdLabel ⬝ᵥ probe) / heightVal with hshiftVal
  set lifted : Fin 3 → ℝ := probe + shiftVal • unitNormal with hlifted
  have hnormalAgainstProbe : unitNormal ⬝ᵥ probe = 0 := by
    rw [dotProduct_comm]; exact hprobeFlat
  have hliftedNe : lifted ≠ 0 := by
    intro hzero
    have hagainst : lifted ⬝ᵥ unitNormal = 0 := by rw [hzero]; simp
    rw [hlifted, add_dotProduct, smul_dotProduct, hprobeFlat, hunit] at hagainst
    simp only [smul_eq_mul, mul_one, zero_add] at hagainst
    rw [hlifted, hagainst, zero_smul, add_zero] at hzero
    exact hprobeNe hzero
  have hatomLift : ∀ label : Fin size, design.atom label ⬝ᵥ lifted
      = design.atom label ⬝ᵥ probe + shiftVal * (design.atom label ⬝ᵥ unitNormal) := by
    intro label
    rw [hlifted, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hliftedNorm : lifted ⬝ᵥ lifted = probe ⬝ᵥ probe + shiftVal ^ 2 := by
    have hexpand : lifted ⬝ᵥ lifted
        = probe ⬝ᵥ probe + 2 * shiftVal * (probe ⬝ᵥ unitNormal)
          + shiftVal ^ 2 * (unitNormal ⬝ᵥ unitNormal) := by
      rw [hlifted]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      rw [dotProduct_comm unitNormal probe]
      ring
    rw [hexpand, hprobeFlat, hunit]
    ring
  have hthirdKilled : design.atom thirdLabel ⬝ᵥ lifted = 0 := by
    rw [hatomLift, hshiftVal, ← hheightVal, div_mul_cancel₀ _ hheightNe]
    ring
  have hpos := hposDef.dotProduct_mulVec_pos hliftedNe
  rw [star_trivial, dominationGap_form, hsumThree, hatomLift flatFirst, hatomLift flatSecond,
    hfirstFlat, hsecondFlat, hthirdKilled, hliftedNorm] at hpos
  nlinarith [hpos, sq_nonneg shiftVal]

/-- The pure algebra behind the flat-pair kill. -/
theorem flatPair_cauchySchwarz_contradiction (levFirst levSecond crossVal : ℝ)
    (hfirstLeverage : levFirst ≤ 1) (hsecondPos : 0 < levSecond)
    (hnormPos : 0 < levSecond * (levFirst * levSecond - crossVal ^ 2))
    (hkey : levSecond * (levFirst * levSecond - crossVal ^ 2)
      < (levFirst * levSecond - crossVal ^ 2) ^ 2) : False := by
  have hdiscriminantPos : 0 < levFirst * levSecond - crossVal ^ 2 := by
    by_contra hle
    push Not at hle
    nlinarith [hnormPos, hsecondPos, hle]
  nlinarith [hkey, hdiscriminantPos, hsecondPos,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - levFirst) hsecondPos.le, sq_nonneg crossVal]

/-- **The Cauchy-Schwarz obstruction on a flat pair.**  Testing plane domination
against the in-plane probe orthogonal to the second flat atom turns it into
`l_i * l_j - (a_i . a_j)^2 > l_j`.  With `l_i <= 1` the left side is at most `l_j`,
so NO card-3 subset built on a unit-leverage flat pair can be strictly dominating,
whatever the third atom is. -/
theorem flatPair_unitLeverage_not_posDef {size : ℕ} (design : WeightedDesign size 3)
    (flatFirst flatSecond thirdLabel : Fin size) (unitNormal : Fin 3 → ℝ)
    (hdistinctFirstSecond : flatFirst ≠ flatSecond)
    (hdistinctFirstThird : flatFirst ≠ thirdLabel)
    (hdistinctSecondThird : flatSecond ≠ thirdLabel)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hfirstFlat : design.atom flatFirst ⬝ᵥ unitNormal = 0)
    (hsecondFlat : design.atom flatSecond ⬝ᵥ unitNormal = 0)
    (hfirstLeverage : design.atom flatFirst ⬝ᵥ design.atom flatFirst ≤ 1)
    (hsecondPos : 0 < design.atom flatSecond ⬝ᵥ design.atom flatSecond)
    (hnotParallel : (design.atom flatSecond ⬝ᵥ design.atom flatSecond)
        • design.atom flatFirst
        - (design.atom flatFirst ⬝ᵥ design.atom flatSecond) • design.atom flatSecond ≠ 0) :
    ¬ (subsetSum design ({flatFirst, flatSecond, thirdLabel} : Finset (Fin size))
        - 1).PosDef := by
  intro hposDef
  have hprobeFlat : ((design.atom flatSecond ⬝ᵥ design.atom flatSecond)
        • design.atom flatFirst
      - (design.atom flatFirst ⬝ᵥ design.atom flatSecond)
        • design.atom flatSecond) ⬝ᵥ unitNormal = 0 := by
    rw [sub_dotProduct, smul_dotProduct, smul_dotProduct, hfirstFlat, hsecondFlat]
    simp
  have hfirstAgainst : design.atom flatFirst ⬝ᵥ
      ((design.atom flatSecond ⬝ᵥ design.atom flatSecond) • design.atom flatFirst
        - (design.atom flatFirst ⬝ᵥ design.atom flatSecond) • design.atom flatSecond)
      = (design.atom flatFirst ⬝ᵥ design.atom flatFirst)
          * (design.atom flatSecond ⬝ᵥ design.atom flatSecond)
        - (design.atom flatFirst ⬝ᵥ design.atom flatSecond) ^ 2 := by
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    ring
  have hsecondAgainst : design.atom flatSecond ⬝ᵥ
      ((design.atom flatSecond ⬝ᵥ design.atom flatSecond) • design.atom flatFirst
        - (design.atom flatFirst ⬝ᵥ design.atom flatSecond) • design.atom flatSecond)
      = 0 := by
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (design.atom flatSecond) (design.atom flatFirst)]
    ring
  have hprobeNorm : ((design.atom flatSecond ⬝ᵥ design.atom flatSecond)
        • design.atom flatFirst
      - (design.atom flatFirst ⬝ᵥ design.atom flatSecond) • design.atom flatSecond)
      ⬝ᵥ ((design.atom flatSecond ⬝ᵥ design.atom flatSecond) • design.atom flatFirst
        - (design.atom flatFirst ⬝ᵥ design.atom flatSecond) • design.atom flatSecond)
      = (design.atom flatSecond ⬝ᵥ design.atom flatSecond)
        * ((design.atom flatFirst ⬝ᵥ design.atom flatFirst)
            * (design.atom flatSecond ⬝ᵥ design.atom flatSecond)
          - (design.atom flatFirst ⬝ᵥ design.atom flatSecond) ^ 2) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (design.atom flatSecond) (design.atom flatFirst)]
    ring
  have hkey := flatPair_planeDomination_of_posDef design flatFirst flatSecond thirdLabel
    unitNormal hdistinctFirstSecond hdistinctFirstThird hdistinctSecondThird hunit
    hfirstFlat hsecondFlat hposDef _ hprobeFlat hnotParallel
  rw [hprobeNorm, hfirstAgainst, hsecondAgainst] at hkey
  have hnormPos := dotProduct_self_pos hnotParallel
  rw [hprobeNorm] at hnormPos
  exact flatPair_cauchySchwarz_contradiction _ _ _ hfirstLeverage hsecondPos hnormPos
    (by nlinarith [hkey])

/-! ## Part 3 -- C6: the margin has NO floor on this stratum, and the collapsing
channel is the normal-direction height budget -/

/-- **The normal-height cap.**  On the one-line stratum only the three free atoms are
visible along the line normal, so EVERY card-3 subset's gap has Rayleigh value at the
unit line normal bounded by the free atoms' total squared height minus one.  Since the
Rayleigh value at a unit vector bounds the least eigenvalue from above, this caps the
margin of every strictly dominating subset simultaneously -- no selector, no anatomy,
no normal choice can beat it. -/
theorem oneLine_gapForm_at_lineNormal_le (design : WeightedDesign 6 3)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (horth : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (selected : Finset (Fin 6)) :
    unitNormal ⬝ᵥ ((subsetSum design selected - 1) *ᵥ unitNormal)
      ≤ (∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
          (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2) - 1 := by
  have hsplit : ∑ label : Fin 6, (design.atom label ⬝ᵥ unitNormal) ^ 2
      = ∑ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
          (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 := by
    rw [Fin.sum_univ_six, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, horth 0 (by decide), horth 1 (by decide), horth 2 (by decide)]
    ring
  have hle : ∑ s ∈ selected, (design.atom s ⬝ᵥ unitNormal) ^ 2
      ≤ ∑ label : Fin 6, (design.atom label ⬝ᵥ unitNormal) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
      (fun label _ _ => sq_nonneg _)
  rw [dominationGap_form, hunit]
  linarith [hle, hsplit.le, hsplit.ge]

/-! ## Part 6 -- the general normal-height cap, valid at EITHER line of the
two-meeting-lines twin.  On the twin the cap applies at BOTH line normals at once,
so the twin's margin is squeezed twice as hard as the one-line stratum's. -/

theorem gapForm_at_flatNormal_le {size : ℕ} (design : WeightedDesign size 3)
    (lineTriple : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (horth : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (selected : Finset (Fin size)) :
    unitNormal ⬝ᵥ ((subsetSum design selected - 1) *ᵥ unitNormal)
      ≤ (∑ freeLabel ∈ lineTripleᶜ, (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2) - 1 := by
  have hlineZero : ∑ lineLabel ∈ lineTriple,
      (design.atom lineLabel ⬝ᵥ unitNormal) ^ 2 = 0 :=
    Finset.sum_eq_zero fun lineLabel hmem => by rw [horth lineLabel hmem]; ring
  have hsplit := Finset.sum_add_sum_compl lineTriple
    (fun label => (design.atom label ⬝ᵥ unitNormal) ^ 2)
  rw [hlineZero, zero_add] at hsplit
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
    (fun label _ _ => sq_nonneg (design.atom label ⬝ᵥ unitNormal))
  rw [dominationGap_form, hunit]
  linarith [hle, hsplit.le, hsplit.ge]

/-! ## Part 7 -- WITNESS W-D on the TWO-MEETING-LINES twin.  The shared atom `0`
is the class's rigidity kernel (it is pinned projectively by the two line planes),
so it is the natural thing for a selector to reach for.  At unit shared leverage it
is exactly the atom a selector must NOT use: every card-3 subset containing it
pairs it with a partner on one of the two lines, and that pair is flat against
that line's normal, so `flatPair_unitLeverage_not_posDef` kills all ten. -/

noncomputable def sharedAtomUnitAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 0, 0]
  | 1 => ![-1, 2, 0]
  | 2 => ![-1, -1, 0]
  | 3 => ![-1, (-1/2), 1]
  | 4 => ![-1, 1, -2]
  | 5 => ![1, 1, 2]

noncomputable def sharedAtomUnitWeight : Fin 6 → ℝ
  | 0 => 1/4
  | 1 => 1/6
  | 2 => 1/12
  | 3 => 1/3
  | 4 => 1/24
  | 5 => 1/8

noncomputable def sharedAtomUnitDesign : WeightedDesign 6 3 where
  atom := sharedAtomUnitAtom
  weight := sharedAtomUnitWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [sharedAtomUnitWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [sharedAtomUnitWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [sharedAtomUnitAtom, sharedAtomUnitWeight, atomMatrix] <;> norm_num

theorem sharedAtomUnitDesign_hasLinePattern :
    HasLinePattern sharedAtomUnitDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, sharedAtomUnitDesign,
            sharedAtomUnitAtom, Matrix.cons_val_two])
          (by decide)
      | exact iff_of_true
          (by norm_num [atomBracket, tripleBracket_eq, sharedAtomUnitDesign,
            sharedAtomUnitAtom, Matrix.cons_val_two])
          (by decide)

theorem sharedAtomUnitDesign_heavy (label : Fin 6) :
    1 ≤ leverageOf (sharedAtomUnitDesign.atom label) := by
  fin_cases label <;>
    simp [leverageOf, Fin.sum_univ_three, sharedAtomUnitDesign, sharedAtomUnitAtom] <;> norm_num


/-- No card-3 subset containing the shared atom dominates strictly: `{0,1,2}` fails. -/
theorem sharedAtomUnit_not_posDef_012 :
    ¬ (subsetSum sharedAtomUnitDesign ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hprobeNe : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 2
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcoord
  have hpos := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hpos
  norm_num [sharedAtomUnitDesign, sharedAtomUnitAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hpos


/-- No card-3 subset containing the shared atom dominates strictly: `{0,1,3}` fails. -/
theorem sharedAtomUnit_not_posDef_013 :
    ¬ (subsetSum sharedAtomUnitDesign ({0, 1, 3} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hprobeNe : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 2
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcoord
  have hpos := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hpos
  norm_num [sharedAtomUnitDesign, sharedAtomUnitAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hpos


/-- No card-3 subset containing the shared atom dominates strictly: `{0,1,4}` fails. -/
theorem sharedAtomUnit_not_posDef_014 :
    ¬ (subsetSum sharedAtomUnitDesign ({0, 1, 4} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hprobeNe : (![1, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 0
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcoord
  have hpos := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hpos
  norm_num [sharedAtomUnitDesign, sharedAtomUnitAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hpos


/-- No card-3 subset containing the shared atom dominates strictly: `{0,1,5}` fails. -/
theorem sharedAtomUnit_not_posDef_015 :
    ¬ (subsetSum sharedAtomUnitDesign ({0, 1, 5} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hprobeNe : (![1, 1, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 0
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcoord
  have hpos := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hpos
  norm_num [sharedAtomUnitDesign, sharedAtomUnitAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hpos


/-- No card-3 subset containing the shared atom dominates strictly: `{0,2,3}` fails. -/
theorem sharedAtomUnit_not_posDef_023 :
    ¬ (subsetSum sharedAtomUnitDesign ({0, 2, 3} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hprobeNe : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 2
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcoord
  have hpos := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hpos
  norm_num [sharedAtomUnitDesign, sharedAtomUnitAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hpos


/-- No card-3 subset containing the shared atom dominates strictly: `{0,2,4}` fails. -/
theorem sharedAtomUnit_not_posDef_024 :
    ¬ (subsetSum sharedAtomUnitDesign ({0, 2, 4} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hprobeNe : (![0, 1, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 1
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcoord
  have hpos := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hpos
  norm_num [sharedAtomUnitDesign, sharedAtomUnitAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hpos


/-- No card-3 subset containing the shared atom dominates strictly: `{0,2,5}` fails. -/
theorem sharedAtomUnit_not_posDef_025 :
    ¬ (subsetSum sharedAtomUnitDesign ({0, 2, 5} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hprobeNe : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 0
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcoord
  have hpos := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hpos
  norm_num [sharedAtomUnitDesign, sharedAtomUnitAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hpos


/-- No card-3 subset containing the shared atom dominates strictly: `{0,3,4}` fails. -/
theorem sharedAtomUnit_not_posDef_034 :
    ¬ (subsetSum sharedAtomUnitDesign ({0, 3, 4} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hprobeNe : (![0, 1, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 1
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcoord
  have hpos := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hpos
  norm_num [sharedAtomUnitDesign, sharedAtomUnitAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hpos


/-- No card-3 subset containing the shared atom dominates strictly: `{0,3,5}` fails. -/
theorem sharedAtomUnit_not_posDef_035 :
    ¬ (subsetSum sharedAtomUnitDesign ({0, 3, 5} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hprobeNe : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 0
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcoord
  have hpos := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hpos
  norm_num [sharedAtomUnitDesign, sharedAtomUnitAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hpos


/-- No card-3 subset containing the shared atom dominates strictly: `{0,4,5}` fails. -/
theorem sharedAtomUnit_not_posDef_045 :
    ¬ (subsetSum sharedAtomUnitDesign ({0, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hprobeNe : (![2, 0, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 0
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcoord
  have hpos := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hpos
  norm_num [sharedAtomUnitDesign, sharedAtomUnitAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hpos


/-- **The shared atom is unusable at unit leverage.**  All ten card-3 subsets of
W-D that contain the two-meeting-lines shared atom fail to dominate strictly. -/
theorem sharedAtomUnit_every_subset_with_shared_atom_fails :
    (¬ (subsetSum sharedAtomUnitDesign ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef)
    ∧ (¬ (subsetSum sharedAtomUnitDesign ({0, 1, 3} : Finset (Fin 6)) - 1).PosDef)
    ∧ (¬ (subsetSum sharedAtomUnitDesign ({0, 1, 4} : Finset (Fin 6)) - 1).PosDef)
    ∧ (¬ (subsetSum sharedAtomUnitDesign ({0, 1, 5} : Finset (Fin 6)) - 1).PosDef)
    ∧ (¬ (subsetSum sharedAtomUnitDesign ({0, 2, 3} : Finset (Fin 6)) - 1).PosDef)
    ∧ (¬ (subsetSum sharedAtomUnitDesign ({0, 2, 4} : Finset (Fin 6)) - 1).PosDef)
    ∧ (¬ (subsetSum sharedAtomUnitDesign ({0, 2, 5} : Finset (Fin 6)) - 1).PosDef)
    ∧ (¬ (subsetSum sharedAtomUnitDesign ({0, 3, 4} : Finset (Fin 6)) - 1).PosDef)
    ∧ (¬ (subsetSum sharedAtomUnitDesign ({0, 3, 5} : Finset (Fin 6)) - 1).PosDef)
    ∧ (¬ (subsetSum sharedAtomUnitDesign ({0, 4, 5} : Finset (Fin 6)) - 1).PosDef) :=
  ⟨sharedAtomUnit_not_posDef_012, sharedAtomUnit_not_posDef_013,
   sharedAtomUnit_not_posDef_014, sharedAtomUnit_not_posDef_015,
   sharedAtomUnit_not_posDef_023, sharedAtomUnit_not_posDef_024,
   sharedAtomUnit_not_posDef_025, sharedAtomUnit_not_posDef_034,
   sharedAtomUnit_not_posDef_035, sharedAtomUnit_not_posDef_045⟩


noncomputable def mixedSurvivorAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 0, 0]
  | 1 => ![-1, 2, 0]
  | 2 => ![-1, -1, 0]
  | 3 => ![-1, (-1/2), 1]
  | 4 => ![(-7/13), 7/13, (-14/13)]
  | 5 => ![7/3, 7/3, 14/3]

noncomputable def mixedSurvivorWeight : Fin 6 → ℝ
  | 0 => 1/4
  | 1 => 1/6
  | 2 => 1/12
  | 3 => 1/3
  | 4 => 169/1176
  | 5 => 9/392

noncomputable def mixedSurvivorDesign : WeightedDesign 6 3 where
  atom := mixedSurvivorAtom
  weight := mixedSurvivorWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [mixedSurvivorWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [mixedSurvivorWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [mixedSurvivorAtom, mixedSurvivorWeight, atomMatrix] <;> norm_num

theorem mixedSurvivorDesign_hasLinePattern :
    HasLinePattern mixedSurvivorDesign
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, mixedSurvivorDesign,
            mixedSurvivorAtom, Matrix.cons_val_two])
          (by decide)
      | exact iff_of_true
          (by norm_num [atomBracket, tripleBracket_eq, mixedSurvivorDesign,
            mixedSurvivorAtom, Matrix.cons_val_two])
          (by decide)

theorem mixedSurvivorDesign_heavy (label : Fin 6) :
    1 ≤ leverageOf (mixedSurvivorDesign.atom label) := by
  fin_cases label <;>
    simp [leverageOf, Fin.sum_univ_three, mixedSurvivorDesign, mixedSurvivorAtom] <;>
    norm_num

/-- **The line complement fails on the twin.**  The in-plane probe `(1,-1,0)` reads `-399/676` on the gap of `{3,4,5}`. -/
theorem mixedSurvivor_lineComplement_not_posDef :
    ¬ (subsetSum mixedSurvivorDesign ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  have hprobeNe : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero 0
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcoord
  have hpos := hposDef.dotProduct_mulVec_pos hprobeNe
  rw [star_trivial, dominationGap_form, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hpos
  norm_num [mixedSurvivorDesign, mixedSurvivorAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hpos

theorem mixedSurvivor_lineComplement_no_producerPair :
    ¬ ∃ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1 ∧
        (1 < ∑ s ∈ ({3, 4, 5} : Finset (Fin 6)),
          (mixedSurvivorDesign.atom s ⬝ᵥ unitNormal) ^ 2) ∧
        ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
          (∑ s ∈ ({3, 4, 5} : Finset (Fin 6)),
              (mixedSurvivorDesign.atom s ⬝ᵥ probe)
                * (mixedSurvivorDesign.atom s ⬝ᵥ unitNormal)) ^ 2
            < ((∑ s ∈ ({3, 4, 5} : Finset (Fin 6)),
                  (mixedSurvivorDesign.atom s ⬝ᵥ unitNormal) ^ 2) - 1)
              * ((∑ s ∈ ({3, 4, 5} : Finset (Fin 6)),
                    (mixedSurvivorDesign.atom s ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe) := by
  rintro ⟨unitNormal, hunit, hsurplus, hcover⟩
  exact mixedSurvivor_lineComplement_not_posDef
    (posDef_of_normalSurplus_planeCover mixedSurvivorDesign _ unitNormal hunit hsurplus hcover)

/-- **The normal-height cap has its OWN floor, and the floor is the LINE WEIGHT.**
Parseval along a unit normal flat on the line puts all of the unit mass on the
complement, and a weighted sum is at most the weight total times the value total,
so the complement's squared heights sum to at least the reciprocal of the
complement's weight.  Subtracting one: the cap is at least
`(1 - complementWeight)/complementWeight = lineWeight / complementWeight`. -/
theorem complement_normalHeights_ge_inv_weight {size : ℕ} (design : WeightedDesign size 3)
    (lineTriple : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (horth : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ unitNormal = 0) :
    1 ≤ (∑ freeLabel ∈ lineTripleᶜ, design.weight freeLabel)
      * ∑ freeLabel ∈ lineTripleᶜ, (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 := by
  have hcarried : ∑ freeLabel ∈ lineTripleᶜ,
      design.weight freeLabel * (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2
        = unitNormal ⬝ᵥ unitNormal := by
    have hparseval := dotProduct_self_eq_sum_weight_mul_sq design unitNormal
    have hlineVanishes : ∑ lineLabel ∈ lineTriple,
        design.weight lineLabel * (design.atom lineLabel ⬝ᵥ unitNormal) ^ 2 = 0 :=
      Finset.sum_eq_zero fun lineLabel hmem => by rw [horth lineLabel hmem]; ring
    rw [← Finset.sum_add_sum_compl lineTriple
        (fun label => design.weight label * (design.atom label ⬝ᵥ unitNormal) ^ 2),
      hlineVanishes, zero_add] at hparseval
    exact hparseval.symm
  have hbound : ∑ freeLabel ∈ lineTripleᶜ,
      design.weight freeLabel * (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2
        ≤ (∑ freeLabel ∈ lineTripleᶜ, design.weight freeLabel)
          * ∑ freeLabel ∈ lineTripleᶜ, (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun freeLabel hmem => ?_
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun label => (design.atom label ⬝ᵥ unitNormal) ^ 2)
        (fun label _ => sq_nonneg _) hmem) (design.weight_pos freeLabel).le
  rw [hcarried, hunit] at hbound
  exact hbound

/-- **The C6 verdict, in one inequality pair.**  For every card-3 subset and the
unit line normal, the gap's Rayleigh value at the normal (hence the least
eigenvalue, hence the margin) is at most `capValue`, and `capValue` is itself at
least `lineWeight / complementWeight`.  So the margin can only be driven to zero
by starving the LINE WEIGHT -- no in-plane angle and no single free weight can do
it, because both leave `capValue` bounded below. -/
theorem margin_cap_and_its_floor {size : ℕ} (design : WeightedDesign size 3)
    (lineTriple : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (horth : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (selected : Finset (Fin size)) :
    unitNormal ⬝ᵥ ((subsetSum design selected - 1) *ᵥ unitNormal)
        ≤ (∑ freeLabel ∈ lineTripleᶜ,
            (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2) - 1
      ∧ 1 ≤ (∑ freeLabel ∈ lineTripleᶜ, design.weight freeLabel)
          * ∑ freeLabel ∈ lineTripleᶜ, (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 := by
  refine ⟨?_, complement_normalHeights_ge_inv_weight design lineTriple unitNormal
    hunit horth⟩
  have hlineZero : ∑ lineLabel ∈ lineTriple,
      (design.atom lineLabel ⬝ᵥ unitNormal) ^ 2 = 0 :=
    Finset.sum_eq_zero fun lineLabel hmem => by rw [horth lineLabel hmem]; ring
  have hsplit := Finset.sum_add_sum_compl lineTriple
    (fun label => (design.atom label ⬝ᵥ unitNormal) ^ 2)
  rw [hlineZero, zero_add] at hsplit
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
    (fun label _ _ => sq_nonneg (design.atom label ⬝ᵥ unitNormal))
  rw [dominationGap_form, hunit]
  linarith [hle, hsplit.le, hsplit.ge]

/-- **The complement's surplus is at least the line weight, times nothing.**
Division-free form: along a unit normal every line atom is blind to, the
complement's total squared height exceeds one by at least the LINE WEIGHT
divided by the complement weight -- stated as a product so no division
appears.  Combined with strict positivity of the line weights this says the
complement ALWAYS carries a strict normal surplus on a line stratum, with an
explicit floor. -/
theorem complement_surplus_ge_lineWeight {size : ℕ} (design : WeightedDesign size 3)
    (lineTriple : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (horth : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ unitNormal = 0) :
    (∑ lineLabel ∈ lineTriple, design.weight lineLabel)
      ≤ (∑ freeLabel ∈ lineTripleᶜ, design.weight freeLabel)
        * ((∑ freeLabel ∈ lineTripleᶜ, (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2) - 1) := by
  have hproduct := complement_normalHeights_ge_inv_weight design lineTriple unitNormal
    hunit horth
  have hweights := Finset.sum_add_sum_compl lineTriple design.weight
  rw [design.weight_sum_one] at hweights
  nlinarith [hproduct, hweights]

/-- **The complement's unweighted cover, from the line's mass deficit.**  What
the line atoms fail to carry of a probe's own norm is carried by the
complement, weighted; bounding every complement weight by one constant turns
that into an UNWEIGHTED cover bound.  No orthogonality and no in-plane
restriction are needed -- this is just the weighted Parseval identity split
over a set and its complement. -/
theorem complementShadow_cover_of_lineMassDeficit {size : ℕ} (design : WeightedDesign size 3)
    (lineTriple : Finset (Fin size)) (probe : Fin 3 → ℝ) (maxComplementWeight : ℝ)
    (hmax : ∀ freeLabel ∈ lineTripleᶜ, design.weight freeLabel ≤ maxComplementWeight) :
    (probe ⬝ᵥ probe)
        - ∑ lineLabel ∈ lineTriple,
            design.weight lineLabel * (design.atom lineLabel ⬝ᵥ probe) ^ 2
      ≤ maxComplementWeight
        * ∑ freeLabel ∈ lineTripleᶜ, (design.atom freeLabel ⬝ᵥ probe) ^ 2 := by
  have hparseval := parseval_weighted_sum_sq design probe
  have hsplit := Finset.sum_add_sum_compl lineTriple
    (fun label => design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
  rw [hparseval] at hsplit
  have hbound : ∑ freeLabel ∈ lineTripleᶜ,
        design.weight freeLabel * (design.atom freeLabel ⬝ᵥ probe) ^ 2
      ≤ ∑ freeLabel ∈ lineTripleᶜ,
        maxComplementWeight * (design.atom freeLabel ⬝ᵥ probe) ^ 2 :=
    Finset.sum_le_sum fun freeLabel hmem =>
      mul_le_mul_of_nonneg_right (hmax freeLabel hmem) (sq_nonneg _)
  rw [← Finset.mul_sum] at hbound
  linarith [hsplit, hbound]

/-- **The complement cover margin, from a line-mass ceiling.**  If the line
atoms' weighted reading never reaches a fixed fraction of the probe's own norm,
the complement's unweighted readings cover the probe with an explicit
multiplicative MARGIN.  The two constants trade directly: a thinner line mass
or a smaller largest complement weight both widen the margin. -/
theorem complementShadow_coverMargin_of_lineMassCeiling {size : ℕ}
    (design : WeightedDesign size 3) (lineTriple : Finset (Fin size)) (probe : Fin 3 → ℝ)
    (maxComplementWeight lineMassCeiling margin : ℝ)
    (hmaxPos : 0 < maxComplementWeight)
    (hmax : ∀ freeLabel ∈ lineTripleᶜ, design.weight freeLabel ≤ maxComplementWeight)
    (hlineMass : ∑ lineLabel ∈ lineTriple,
        design.weight lineLabel * (design.atom lineLabel ⬝ᵥ probe) ^ 2
      ≤ lineMassCeiling * (probe ⬝ᵥ probe))
    (hmarginFits : (1 + margin) * maxComplementWeight ≤ 1 - lineMassCeiling) :
    (1 + margin) * (probe ⬝ᵥ probe)
      ≤ ∑ freeLabel ∈ lineTripleᶜ, (design.atom freeLabel ⬝ᵥ probe) ^ 2 := by
  have hdeficit := complementShadow_cover_of_lineMassDeficit design lineTriple probe
    maxComplementWeight hmax
  have hnormNonneg : 0 ≤ probe ⬝ᵥ probe := dotProduct_self_nonneg probe
  nlinarith [hdeficit, hlineMass, hmarginFits, hnormNonneg, hmaxPos]

end Gtz
