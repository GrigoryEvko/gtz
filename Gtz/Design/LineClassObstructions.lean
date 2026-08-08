/-
# Line-class obstructions: the census ladder, a rational one-line sample, the open-atom lift

Three arcs of design-level ammunition for the two chartless rank-3 classes —
one three-point line `[[0,1,2]]` and two meeting lines `[[0,1,2],[0,3,4]]`
(`Skeleton.obligationTieFreeOneLine` / `...TwoMeetingLines`).

ARC 1, THE CENSUS LADDER.  What an exact tie on either stratum would require,
proved as finite obstruction lemmas over the live vocabulary.  The relabel
bridge `stressFreeStratumIsTieFree_of_stratumIsTieFree` is the endgame shape of
any direct route: identity-labelled tie-freeness closes the class obligation
outright, because both strata are uniformly stress-free
(`Gtz.stratumIsStressFree_oneThreePointLine` / `_twoMeetingLines`).  The kernel
one-steps say a tie's weak dominator avoids every declared line (leaving 19
resp. 18 basis triples) and each line has a nonzero normal.  The Parseval seeds
say the normal direction is carried entirely by the complement
(`normalParseval_on_complement`) and STRICTLY over-covered by it
(`complement_strictly_overcovers_normal`) — the strict-domination seed present
on every design of either stratum — while weak domination forces the
dominator's free atoms alone to cover the normal to level one.  The class
anatomy pins the two-meeting-lines rigidity kernel: the two normals are
non-parallel and the shared atom spans the plane intersection.

ARC 2, THE ONE-LINE RATIONAL SAMPLE.  A fully rational inhabitant of the
one-line stratum — atoms `(1,0,0), (0,1,0), (1,1,0), (-2,-2,1), (-1,1,2),
(2,-1,2)` with weights `1/7, 3/7, 1/7, 1/21, 1/7, 2/21` — with exact Parseval,
the exact line pattern, and TWO strictly dominating triples `{3,4,5}` and
`{2,4,5}` (both containing the free pair `{4,5}`, as the normal-coverage
obstruction predicts).  Unlike `Gtz.tetrahedronChartPoint` no scale gauge is
needed: the mass solve lands at total one, so weights equal masses and the
atoms are the raw integer vectors.  The sample is the class's non-vacuity
anchor and the concrete testbed for any candidate selector.

ARC 3, THE OPEN-ATOM LIFT IDENTITY.  Splitting one atom off a chart face and
re-opening it with weight `eps` and mass `openedMass` perturbs every chart gap
over a triple avoiding the opened atom by a scaled PSD gain minus one rank-one
mass term — direction-generic, so it serves the two-meeting-lines boundary leg
(where the diamond tie family sits at the weight-zero face) verbatim.  The
companion PSD lemma makes "the eps term only helps" formal: the whole off-face
cost is the rank-one subtraction.
-/
import Gtz.Design.RigidityBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## Bracket helpers: zero atoms, common orthogonals, and the Grassmann identity

Three small facts the ladder consumes repeatedly: a zero atom kills every
bracket through its slot; a common orthogonal direction kills a bracket
outright (the converse of `Gtz.hasCommonOrthogonal_of_atomBracket_eq_zero`);
and the cross product satisfies the Grassmann (BAC-CAB) identity, which turns
"orthogonal to two independent normals" into "parallel to their cross". -/

/-- A vanishing left atom kills the bracket. -/
theorem atomBracket_eq_zero_of_left_atom_eq_zero {size : ℕ} (design : WeightedDesign size 3)
    (leftLabel midLabel rightLabel : Fin size) (hzero : design.atom leftLabel = 0) :
    atomBracket design leftLabel midLabel rightLabel = 0 := by
  rw [atomBracket, hzero]
  simp [tripleBracket_eq]

/-- A vanishing middle atom kills the bracket. -/
theorem atomBracket_eq_zero_of_mid_atom_eq_zero {size : ℕ} (design : WeightedDesign size 3)
    (leftLabel midLabel rightLabel : Fin size) (hzero : design.atom midLabel = 0) :
    atomBracket design leftLabel midLabel rightLabel = 0 := by
  rw [atomBracket, hzero]
  simp [tripleBracket_eq]

/-- A vanishing right atom kills the bracket. -/
theorem atomBracket_eq_zero_of_right_atom_eq_zero {size : ℕ} (design : WeightedDesign size 3)
    (leftLabel midLabel rightLabel : Fin size) (hzero : design.atom rightLabel = 0) :
    atomBracket design leftLabel midLabel rightLabel = 0 := by
  rw [atomBracket, hzero]
  simp [tripleBracket_eq]

/-- **A common orthogonal kills the bracket** — the converse of
`Gtz.hasCommonOrthogonal_of_atomBracket_eq_zero`: three vectors annihilating
one nonzero direction are coplanar. -/
theorem tripleBracket_eq_zero_of_commonOrthogonal
    {leftVec midVec rightVec normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hleftOrth : leftVec ⬝ᵥ normalVec = 0) (hmidOrth : midVec ⬝ᵥ normalVec = 0)
    (hrightOrth : rightVec ⬝ᵥ normalVec = 0) :
    tripleBracket leftVec midVec rightVec = 0 := by
  rw [tripleBracket]
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨normalVec, hnormalNe, ?_⟩
  funext rowIndex
  fin_cases rowIndex
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hleftOrth
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hmidOrth
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hrightOrth

/-- **The Grassmann (BAC-CAB) identity** for `Gtz.bracketNormal`:
`(a × b) × v = (a ⬝ᵥ v) • b − (b ⬝ᵥ v) • a`. -/
theorem bracketNormal_bracketNormal (firstVec secondVec probeVec : Fin 3 → ℝ) :
    bracketNormal (bracketNormal firstVec secondVec) probeVec
      = (firstVec ⬝ᵥ probeVec) • secondVec - (secondVec ⬝ᵥ probeVec) • firstVec := by
  funext coordIndex
  fin_cases coordIndex
  · show bracketNormal (bracketNormal firstVec secondVec) probeVec 0
      = ((firstVec ⬝ᵥ probeVec) • secondVec - (secondVec ⬝ᵥ probeVec) • firstVec) 0
    simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  · show bracketNormal (bracketNormal firstVec secondVec) probeVec 1
      = ((firstVec ⬝ᵥ probeVec) • secondVec - (secondVec ⬝ᵥ probeVec) • firstVec) 1
    simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  · show bracketNormal (bracketNormal firstVec secondVec) probeVec 2
      = ((firstVec ⬝ᵥ probeVec) • secondVec - (secondVec ⬝ᵥ probeVec) • firstVec) 2
    simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring

/-- Two vectors both parallel to a common carrier, the first of them nonzero,
are parallel to each other — with the ratio exhibited. -/
theorem exists_smul_of_both_smul_of_ne_zero {baseVec firstVec secondVec : Fin 3 → ℝ}
    {firstScale secondScale : ℝ} (hfirstNe : firstVec ≠ 0)
    (hfirstEq : firstVec = firstScale • baseVec)
    (hsecondEq : secondVec = secondScale • baseVec) :
    ∃ scale : ℝ, secondVec = scale • firstVec := by
  have hfirstScaleNe : firstScale ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hfirstEq
    exact hfirstNe hfirstEq
  refine ⟨secondScale / firstScale, ?_⟩
  rw [hsecondEq, hfirstEq, smul_smul, div_mul_cancel₀ _ hfirstScaleNe]

/-! ## The relabel bridge

`Gtz.StressFreeStratumIsTieFree` quantifies a relabelling and a stress-freeness
hypothesis; on the four nonempty-family classes the latter is redundant
(`Gtz.stratumIsStressFree_*`), and `Gtz.stratumIsTieFree_comp_relabel`
transports the identity-labelled statement across the former.  So a direct
chartless route may end at plain `Gtz.StratumIsTieFree`. -/

/-- **The bridge**: identity-labelled tie-freeness closes the class obligation. -/
theorem stressFreeStratumIsTieFree_of_stratumIsTieFree (pattern : LinePattern 6)
    (hfree : StratumIsTieFree pattern) : StressFreeStratumIsTieFree pattern :=
  fun design relabel _hstressFree hpattern =>
    stratumIsTieFree_comp_relabel pattern relabel hfree design hpattern

/-! ## Kernel one-steps: dominators avoid lines, lines have normals, atoms are nonzero -/

/-- The line triple of the one-line stratum never dominates. -/
theorem oneLine_lineTriple_not_dominates (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    ¬ Dominates design ({0, 1, 2} : Finset (Fin 6)) :=
  not_dominates_of_atomBracket_eq_zero design 0 1 2
    ((hpattern 0 1 2 (by decide) (by decide) (by decide)).mpr (by decide))

/-- A tie's weak dominator on the one-line stratum avoids the line, hence is
one of the nineteen basis triples and contains at least one free atom. -/
theorem oneLine_tieDominator_avoids_line (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (htie : IsTie design) :
    ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator ∧
      dominator ≠ ({0, 1, 2} : Finset (Fin 6)) := by
  obtain ⟨⟨dominator, hcard, hdominates⟩, _⟩ := htie
  exact ⟨dominator, hcard, hdominates, fun heq =>
    oneLine_lineTriple_not_dominates design hpattern (heq ▸ hdominates)⟩

/-- Neither line triple of the two-meeting-lines stratum dominates. -/
theorem twoMeetingLines_lineTriples_not_dominate (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])) :
    ¬ Dominates design ({0, 1, 2} : Finset (Fin 6)) ∧
      ¬ Dominates design ({0, 3, 4} : Finset (Fin 6)) :=
  ⟨not_dominates_of_atomBracket_eq_zero design 0 1 2
      ((hpattern 0 1 2 (by decide) (by decide) (by decide)).mpr (by decide)),
    not_dominates_of_atomBracket_eq_zero design 0 3 4
      ((hpattern 0 3 4 (by decide) (by decide) (by decide)).mpr (by decide))⟩

/-- A tie's weak dominator on the two-meeting-lines stratum avoids both lines,
hence is one of the eighteen basis triples. -/
theorem twoMeetingLines_tieDominator_avoids_both_lines (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (htie : IsTie design) :
    ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator ∧
      dominator ≠ ({0, 1, 2} : Finset (Fin 6)) ∧
      dominator ≠ ({0, 3, 4} : Finset (Fin 6)) := by
  obtain ⟨⟨dominator, hcard, hdominates⟩, _⟩ := htie
  obtain ⟨hfirstLine, hsecondLine⟩ := twoMeetingLines_lineTriples_not_dominate design hpattern
  exact ⟨dominator, hcard, hdominates,
    fun heq => hfirstLine (heq ▸ hdominates), fun heq => hsecondLine (heq ▸ hdominates)⟩

/-- The one-line stratum's line has a nonzero normal. -/
theorem oneLine_has_lineNormal (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    ∃ normalVec : Fin 3 → ℝ, normalVec ≠ 0 ∧
      ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ normalVec = 0 := by
  obtain ⟨normalVec, hnormalNe, horthogonal⟩ :=
    hasCommonOrthogonal_of_atomBracket_eq_zero design 0 1 2
      ((hpattern 0 1 2 (by decide) (by decide) (by decide)).mpr (by decide))
  exact ⟨normalVec, hnormalNe, horthogonal⟩

/-- Both lines of the two-meeting-lines stratum have nonzero normals. -/
theorem twoMeetingLines_have_two_normals (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])) :
    ∃ normalFirst normalSecond : Fin 3 → ℝ,
      normalFirst ≠ 0 ∧ normalSecond ≠ 0 ∧
      (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ normalFirst = 0) ∧
      (∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ normalSecond = 0) := by
  obtain ⟨normalFirst, hfirstNe, horthFirst⟩ :=
    hasCommonOrthogonal_of_atomBracket_eq_zero design 0 1 2
      ((hpattern 0 1 2 (by decide) (by decide) (by decide)).mpr (by decide))
  obtain ⟨normalSecond, hsecondNe, horthSecond⟩ :=
    hasCommonOrthogonal_of_atomBracket_eq_zero design 0 3 4
      ((hpattern 0 3 4 (by decide) (by decide) (by decide)).mpr (by decide))
  exact ⟨normalFirst, normalSecond, hfirstNe, hsecondNe, horthFirst, horthSecond⟩

/-- Every atom on the one-line stratum is nonzero: a vanishing atom would kill
the bracket of a triple the pattern declares independent. -/
theorem oneLine_atoms_ne_zero (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (label : Fin 6) : design.atom label ≠ 0 := by
  fin_cases label <;> intro hzero
  · exact absurd ((hpattern 0 3 4 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_left_atom_eq_zero design 0 3 4 hzero)) (by decide)
  · exact absurd ((hpattern 1 3 4 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_left_atom_eq_zero design 1 3 4 hzero)) (by decide)
  · exact absurd ((hpattern 2 3 4 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_left_atom_eq_zero design 2 3 4 hzero)) (by decide)
  · exact absurd ((hpattern 0 1 3 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_right_atom_eq_zero design 0 1 3 hzero)) (by decide)
  · exact absurd ((hpattern 0 1 4 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_right_atom_eq_zero design 0 1 4 hzero)) (by decide)
  · exact absurd ((hpattern 0 1 5 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_right_atom_eq_zero design 0 1 5 hzero)) (by decide)

/-- Every atom on the two-meeting-lines stratum is nonzero. -/
theorem twoMeetingLines_atoms_ne_zero (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (label : Fin 6) : design.atom label ≠ 0 := by
  fin_cases label <;> intro hzero
  · exact absurd ((hpattern 0 1 3 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_left_atom_eq_zero design 0 1 3 hzero)) (by decide)
  · exact absurd ((hpattern 1 3 4 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_left_atom_eq_zero design 1 3 4 hzero)) (by decide)
  · exact absurd ((hpattern 2 3 4 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_left_atom_eq_zero design 2 3 4 hzero)) (by decide)
  · exact absurd ((hpattern 1 2 3 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_right_atom_eq_zero design 1 2 3 hzero)) (by decide)
  · exact absurd ((hpattern 1 2 4 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_right_atom_eq_zero design 1 2 4 hzero)) (by decide)
  · exact absurd ((hpattern 0 1 5 (by decide) (by decide) (by decide)).mp
      (atomBracket_eq_zero_of_right_atom_eq_zero design 0 1 5 hzero)) (by decide)

/-! ## Parseval seeds: the normal direction is carried, and strictly over-covered,
by the complement -/

/-- **Parseval transfers the normal direction to the complement.**  If every
atom of `lineTriple` is orthogonal to `normalVec`, the weighted Parseval
identity evaluated at `normalVec` is carried entirely by the complementary
atoms. -/
theorem normalParseval_on_complement (design : WeightedDesign 6 3)
    (lineTriple : Finset (Fin 6)) (normalVec : Fin 3 → ℝ)
    (horthogonal : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ normalVec = 0) :
    ∑ freeLabel ∈ lineTripleᶜ,
        design.weight freeLabel * (design.atom freeLabel ⬝ᵥ normalVec) ^ 2
      = normalVec ⬝ᵥ normalVec := by
  have hparseval := dotProduct_self_eq_sum_weight_mul_sq design normalVec
  have hlineVanishes : ∑ lineLabel ∈ lineTriple,
      design.weight lineLabel * (design.atom lineLabel ⬝ᵥ normalVec) ^ 2 = 0 :=
    Finset.sum_eq_zero fun lineLabel hmem => by rw [horthogonal lineLabel hmem]; ring
  rw [← Finset.sum_add_sum_compl lineTriple
      (fun atomLabel => design.weight atomLabel * (design.atom atomLabel ⬝ᵥ normalVec) ^ 2),
    hlineVanishes, zero_add] at hparseval
  exact hparseval.symm

/-- **The complement strictly over-covers the line normal.**  The unweighted
atom sum of the complement exceeds the identity STRICTLY in the normal
direction, because each positive weight is strictly below one.  This is the
strict-inequality seed a strict-domination certificate can grow from. -/
theorem complement_strictly_overcovers_normal (design : WeightedDesign 6 3)
    (lineTriple : Finset (Fin 6)) (normalVec : Fin 3 → ℝ)
    (_hlineNonempty : lineTriple.Nonempty) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ normalVec = 0) :
    normalVec ⬝ᵥ normalVec
      < normalVec ⬝ᵥ ((subsetSum design lineTripleᶜ) *ᵥ normalVec) := by
  have hcarried := normalParseval_on_complement design lineTriple normalVec horthogonal
  have hnormPos : 0 < normalVec ⬝ᵥ normalVec := dotProduct_self_pos hnormalNe
  rw [dotProduct_subsetSum_mulVec_of_finset, ← hcarried]
  have hsumPos : (0 : ℝ) < ∑ freeLabel ∈ lineTripleᶜ,
      design.weight freeLabel * (design.atom freeLabel ⬝ᵥ normalVec) ^ 2 := by
    rw [hcarried]; exact hnormPos
  obtain ⟨witnessLabel, hwitnessMem, hwitnessPos⟩ :=
    Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) (by simpa using hsumPos)
  have hwitnessSqPos : 0 < (design.atom witnessLabel ⬝ᵥ normalVec) ^ 2 := by
    nlinarith [design.weight_pos witnessLabel, hwitnessPos]
  exact Finset.sum_lt_sum
    (fun freeLabel _ => mul_le_of_le_one_left (sq_nonneg _)
      (weight_lt_one design (by norm_num) freeLabel).le)
    ⟨witnessLabel, hwitnessMem,
      mul_lt_of_lt_one_left hwitnessSqPos (weight_lt_one design (by norm_num) witnessLabel)⟩

/-- **The free triple `{3,4,5}` strictly over-covers the one-line normal** —
the stratum-wide strict seed, present on every design of the class. -/
theorem oneLine_freeTriple_strictly_overcovers_normal (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0) :
    normalVec ⬝ᵥ normalVec
      < normalVec ⬝ᵥ ((subsetSum design ({3, 4, 5} : Finset (Fin 6))) *ᵥ normalVec) := by
  have hstrict := complement_strictly_overcovers_normal design {0, 1, 2} normalVec
    ⟨0, by decide⟩ hnormalNe horthogonal
  rwa [show ({0, 1, 2} : Finset (Fin 6))ᶜ = {3, 4, 5} by decide] at hstrict

/-- **What weak domination forces on the free atoms**: only the dominator's
free atoms see the normal direction, so they alone must cover it to Loewner
level one. -/
theorem oneLine_dominator_freeAtoms_cover_normal (design : WeightedDesign 6 3)
    (dominator : Finset (Fin 6)) (normalVec : Fin 3 → ℝ)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0)
    (hdominates : Dominates design dominator) :
    normalVec ⬝ᵥ normalVec
      ≤ ∑ freeLabel ∈ dominator \ ({0, 1, 2} : Finset (Fin 6)),
          (design.atom freeLabel ⬝ᵥ normalVec) ^ 2 := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 normalVec
  rw [star_trivial, dominationGap_form] at hform
  have hsplit : ∑ selectedLabel ∈ dominator, (design.atom selectedLabel ⬝ᵥ normalVec) ^ 2
      = ∑ freeLabel ∈ dominator \ ({0, 1, 2} : Finset (Fin 6)),
          (design.atom freeLabel ⬝ᵥ normalVec) ^ 2 := by
    refine (Finset.sum_subset Finset.sdiff_subset
      fun selectedLabel hmemDominator hnotFree => ?_).symm
    have hmemLine : selectedLabel ∈ ({0, 1, 2} : Finset (Fin 6)) := by
      by_contra hnotLine
      exact hnotFree (Finset.mem_sdiff.mpr ⟨hmemDominator, hnotLine⟩)
    rw [horthogonal selectedLabel hmemLine]
    ring
  linarith [hform, hsplit.le, hsplit.ge]

/-- **Each complement strictly over-covers its line's normal** on the
two-meeting-lines stratum: `{3,4,5}` over the `{0,1,2}` normal and `{1,2,5}`
over the `{0,3,4}` normal.  Atom `5` is the only atom in both complements —
a tie must keep both over-covered complements non-strict while atom `5`
carries normal mass for both planes at once. -/
theorem twoMeetingLines_complements_strictly_overcover_normals
    (design : WeightedDesign 6 3) (normalFirst normalSecond : Fin 3 → ℝ)
    (hfirstNe : normalFirst ≠ 0) (hsecondNe : normalSecond ≠ 0)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    normalFirst ⬝ᵥ normalFirst
        < normalFirst ⬝ᵥ ((subsetSum design ({3, 4, 5} : Finset (Fin 6))) *ᵥ normalFirst)
      ∧ normalSecond ⬝ᵥ normalSecond
        < normalSecond ⬝ᵥ ((subsetSum design ({1, 2, 5} : Finset (Fin 6))) *ᵥ normalSecond) := by
  constructor
  · have hstrict := complement_strictly_overcovers_normal design {0, 1, 2} normalFirst
      ⟨0, by decide⟩ hfirstNe horthFirst
    rwa [show ({0, 1, 2} : Finset (Fin 6))ᶜ = {3, 4, 5} by decide] at hstrict
  · have hstrict := complement_strictly_overcovers_normal design {0, 3, 4} normalSecond
      ⟨0, by decide⟩ hsecondNe horthSecond
    rwa [show ({0, 3, 4} : Finset (Fin 6))ᶜ = {1, 2, 5} by decide] at hstrict

/-! ## Class anatomy: independent normals, the pinned shared atom, and the
tie's null vector -/

/-- **The two normals are non-parallel**: coincident line planes would kill the
bracket of `{1,2,3}`, which the pattern declares independent. -/
theorem twoMeetingLines_normals_not_parallel (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (hfirstNe : normalFirst ≠ 0) (hsecondNe : normalSecond ≠ 0)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    ∀ ratio : ℝ, normalSecond ≠ ratio • normalFirst := by
  intro ratio hparallel
  have hratioNe : ratio ≠ 0 := fun hzero =>
    hsecondNe (by rw [hparallel, hzero, zero_smul])
  have hthirdOrth : design.atom 3 ⬝ᵥ normalFirst = 0 := by
    have hthirdSecond := horthSecond 3 (by decide)
    rw [hparallel, dotProduct_smul, smul_eq_mul] at hthirdSecond
    exact (mul_eq_zero.mp hthirdSecond).resolve_left hratioNe
  have hbracket : atomBracket design 1 2 3 = 0 := by
    rw [atomBracket]
    exact tripleBracket_eq_zero_of_commonOrthogonal hfirstNe
      (horthFirst 1 (by decide)) (horthFirst 2 (by decide)) hthirdOrth
  exact absurd ((hpattern 1 2 3 (by decide) (by decide) (by decide)).mp hbracket) (by decide)

/-- **The shared atom spans the plane intersection**: any vector orthogonal to
both normals is a multiple of atom `0`.  This pins atom `0` projectively by
the two line planes — the rigidity kernel of the class. -/
theorem twoMeetingLines_sharedAtom_spans_intersection (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (hfirstNe : normalFirst ≠ 0) (hsecondNe : normalSecond ≠ 0)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (commonVec : Fin 3 → ℝ)
    (hcommonFirst : normalFirst ⬝ᵥ commonVec = 0)
    (hcommonSecond : normalSecond ⬝ᵥ commonVec = 0) :
    ∃ scale : ℝ, commonVec = scale • design.atom 0 := by
  have hcrossNe : bracketNormal normalFirst normalSecond ≠ 0 :=
    bracketNormal_ne_zero_of_not_parallel normalFirst normalSecond hfirstNe
      (twoMeetingLines_normals_not_parallel design normalFirst normalSecond hpattern
        hfirstNe hsecondNe horthFirst horthSecond)
  have hcommonCross : bracketNormal (bracketNormal normalFirst normalSecond) commonVec = 0 := by
    rw [bracketNormal_bracketNormal, hcommonFirst, hcommonSecond, zero_smul, zero_smul,
      sub_zero]
  have hatomCross :
      bracketNormal (bracketNormal normalFirst normalSecond) (design.atom 0) = 0 := by
    rw [bracketNormal_bracketNormal, dotProduct_comm normalFirst (design.atom 0),
      dotProduct_comm normalSecond (design.atom 0), horthFirst 0 (by decide),
      horthSecond 0 (by decide), zero_smul, zero_smul, sub_zero]
  exact exists_smul_of_both_smul_of_ne_zero
    (twoMeetingLines_atoms_ne_zero design hpattern 0)
    (eq_smul_of_bracketNormal_eq_zero (bracketNormal normalFirst normalSecond)
      (design.atom 0) hcrossNe hatomCross)
    (eq_smul_of_bracketNormal_eq_zero (bracketNormal normalFirst normalSecond)
      commonVec hcrossNe hcommonCross)

/-- **A tie's dominator gap has a genuine null vector** — the Rayleigh-zero
direction of `Gtz.isTie_yields_tightDirection` upgraded to kernel membership
through PSD.  This feeds the KKT chain of `Gtz.Reduction.RayleighCertificate`. -/
theorem oneLine_tie_has_nullVector_on_dominator (design : WeightedDesign 6 3)
    (_hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (htie : IsTie design) :
    ∃ (dominator : Finset (Fin 6)) (tightDir : Fin 3 → ℝ),
      dominator.card = 3 ∧ Dominates design dominator ∧ tightDir ≠ 0 ∧
        (subsetSum design dominator - 1) *ᵥ tightDir = 0 := by
  obtain ⟨dominator, tightDir, hcard, hdominates, htightNe, hrayleighZero⟩ :=
    isTie_yields_tightDirection htie
  exact ⟨dominator, tightDir, hcard, hdominates, htightNe,
    (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hdominates tightDir).mp
      (by rw [star_trivial]; exact hrayleighZero)⟩

/-! ## The one-line rational sample

A fully rational inhabitant of the one-line stratum, with two strictly
dominating triples certified by explicit sum-of-squares forms and exact
determinants.  Mirrors `Gtz.tetrahedronChartPoint` for the K4 class, one
better: no scale gauge is needed. -/

/-- The sample's six atom directions: line atoms `0,1,2` span the plane
`z = 0`, free atoms `3,4,5` resolve the rest of the identity. -/
def oneLineSampleAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![1, 1, 0]
  | 3 => ![-2, -2, 1]
  | 4 => ![-1, 1, 2]
  | 5 => ![2, -1, 2]

/-- The sample's weights: exact sevenths and twenty-firsts, no gauge. -/
noncomputable def oneLineSampleWeight : Fin 6 → ℝ
  | 0 => 1 / 7
  | 1 => 3 / 7
  | 2 => 1 / 7
  | 3 => 1 / 21
  | 4 => 1 / 7
  | 5 => 2 / 21

/-- The one-line sample design: Parseval holds on the nose. -/
noncomputable def oneLineSampleDesign : WeightedDesign 6 3 where
  atom := oneLineSampleAtom
  weight := oneLineSampleWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [oneLineSampleWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [oneLineSampleWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [oneLineSampleAtom, oneLineSampleWeight, atomMatrix] <;> norm_num

/-- The sample realizes the one-line pattern exactly: `{0,1,2}` is its only
dependent triple. -/
theorem oneLineSampleDesign_hasLinePattern :
    HasLinePattern oneLineSampleDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, oneLineSampleDesign,
            oneLineSampleAtom, Matrix.cons_val_two])
          (by decide)
      | exact iff_of_true
          (by norm_num [atomBracket, tripleBracket_eq, oneLineSampleDesign,
            oneLineSampleAtom, Matrix.cons_val_two])
          (by decide)

/-- The free-triple gap `S_{345} − I` of the sample, entry by entry. -/
theorem oneLineSample_freeTripleGap_eq :
    subsetSum oneLineSampleDesign {3, 4, 5} - 1
      = Matrix.of ![![8, 1, 0], ![1, 5, -2], ![0, -2, 8]] := by
  rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [oneLineSampleDesign, oneLineSampleAtom, atomMatrix, Matrix.sub_apply] <;> norm_num

/-- The free-triple gap as an explicit sum of squares:
`7·x₀² + 7·x₂² + (x₀+x₁)² + (2x₁−x₂)²`. -/
theorem oneLineSample_freeTripleGap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum oneLineSampleDesign {3, 4, 5} - 1) *ᵥ vecArg)
      = 7 * vecArg 0 ^ 2 + 7 * vecArg 2 ^ 2 + (vecArg 0 + vecArg 1) ^ 2
        + (2 * vecArg 1 - vecArg 2) ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [oneLineSampleDesign, oneLineSampleAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

/-- The free-triple gap is positive semidefinite. -/
theorem oneLineSample_freeTripleGap_posSemidef :
    (subsetSum oneLineSampleDesign {3, 4, 5} - 1).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg => ?_⟩
  · exact ((Matrix.posSemidef_sum ({3, 4, 5} : Finset (Fin 6)) fun freeLabel _ =>
      posSemidef_atomMatrix (oneLineSampleDesign.atom freeLabel)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, oneLineSample_freeTripleGap_form]
    positivity

/-- **The free triple `{3,4,5}` dominates STRICTLY** — PSD plus exact
determinant `280 ≠ 0`. -/
theorem oneLineSample_freeTripleGap_posDef :
    (subsetSum oneLineSampleDesign {3, 4, 5} - 1).PosDef := by
  refine oneLineSample_freeTripleGap_posSemidef.posDef_iff_det_ne_zero.mpr ?_
  rw [oneLineSample_freeTripleGap_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

/-- The mixed-triple gap `S_{245} − I` of the sample, entry by entry:
one line atom plus the free pair `{4,5}`. -/
theorem oneLineSample_mixedTripleGap_eq :
    subsetSum oneLineSampleDesign {2, 4, 5} - 1
      = Matrix.of ![![5, -2, 2], ![-2, 2, 0], ![2, 0, 7]] := by
  rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [oneLineSampleDesign, oneLineSampleAtom, atomMatrix, Matrix.sub_apply] <;> norm_num

/-- The mixed-triple gap as an explicit sum of squares:
`(2x₀−x₁)² + (x₀+2x₂)² + x₁² + 3·x₂²`. -/
theorem oneLineSample_mixedTripleGap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum oneLineSampleDesign {2, 4, 5} - 1) *ᵥ vecArg)
      = (2 * vecArg 0 - vecArg 1) ^ 2 + (vecArg 0 + 2 * vecArg 2) ^ 2
        + vecArg 1 ^ 2 + 3 * vecArg 2 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [oneLineSampleDesign, oneLineSampleAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

/-- The mixed-triple gap is positive semidefinite. -/
theorem oneLineSample_mixedTripleGap_posSemidef :
    (subsetSum oneLineSampleDesign {2, 4, 5} - 1).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg => ?_⟩
  · exact ((Matrix.posSemidef_sum ({2, 4, 5} : Finset (Fin 6)) fun freeLabel _ =>
      posSemidef_atomMatrix (oneLineSampleDesign.atom freeLabel)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, oneLineSample_mixedTripleGap_form]
    positivity

/-- **The mixed triple `{2,4,5}` also dominates STRICTLY** — determinant
`34 ≠ 0`.  Both strict dominators contain the free pair `{4,5}`, as the
normal-coverage obstruction predicts. -/
theorem oneLineSample_mixedTripleGap_posDef :
    (subsetSum oneLineSampleDesign {2, 4, 5} - 1).PosDef := by
  refine oneLineSample_mixedTripleGap_posSemidef.posDef_iff_det_ne_zero.mpr ?_
  rw [oneLineSample_mixedTripleGap_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

/-- The sample's free triple dominates (the weak half, read off the strict). -/
theorem oneLineSampleDesign_dominates_freeTriple :
    Dominates oneLineSampleDesign {3, 4, 5} :=
  oneLineSample_freeTripleGap_posSemidef

/-- The sample has a strictly dominating triple. -/
theorem oneLineSampleDesign_hasStrictDominator :
    ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧
      (subsetSum oneLineSampleDesign dominator - 1).PosDef :=
  ⟨{3, 4, 5}, by decide, oneLineSample_freeTripleGap_posDef⟩

/-- **The one-line stratum's known inhabitant is not a tie** — the class
obligation's conclusion, verified at the sample by rational arithmetic. -/
theorem oneLineSampleDesign_not_isTie : ¬ IsTie oneLineSampleDesign :=
  fun htie => htie.2 {3, 4, 5} (by decide) oneLineSample_freeTripleGap_posDef

/-! ## The open-atom lift identity

Direction-generic: nothing below constrains `direction`, which is exactly why
it transfers to the two-meeting-lines class, whose sixth atom is generic.  The
identity is the skeleton of the boundary leg at the diamond face: base face
point, sixth direction, and the `(eps, openedMass)` re-opening. -/

/-- **The open-atom lift identity.**  For a face design (`faceMass opened = 0`)
and any triple `selected` avoiding `opened`, re-opening the atom with weight
`eps` (remaining weights scaled by `1 − eps`) and mass `openedMass` perturbs
the chart gap by the scaled selected atom sum minus the rank-one mass term.
Weight-hypothesis-free: only `1 − eps ≠ 0` is needed. -/
theorem directionChartGap_openAtom {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ))
    (faceMass faceWeight : Fin size → ℝ) (opened : Fin size)
    (eps openedMass : ℝ)
    (hfaceMassOpened : faceMass opened = 0)
    (hepsNe : (1 : ℝ) - eps ≠ 0)
    (selected : Finset (Fin size))
    (hopenedNotSelected : opened ∉ selected) :
    directionChartGap direction (Function.update faceMass opened openedMass)
        (Function.update (fun label => (1 - eps) * faceWeight label) opened eps)
        selected
      = directionChartGap direction faceMass faceWeight selected
          + (eps / (1 - eps)) • (∑ label ∈ selected,
              (faceMass label / faceWeight label) • atomMatrix (direction label))
          - openedMass • atomMatrix (direction opened) := by
  have hselected :
      (∑ label ∈ selected,
          (Function.update faceMass opened openedMass label
              / Function.update (fun label => (1 - eps) * faceWeight label)
                  opened eps label)
            • atomMatrix (direction label))
        = ((1 : ℝ) / (1 - eps)) • ∑ label ∈ selected,
            (faceMass label / faceWeight label) • atomMatrix (direction label) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun label hmem => ?_
    have hlabelNe : label ≠ opened := fun heq => hopenedNotSelected (heq ▸ hmem)
    rw [Function.update_of_ne hlabelNe, Function.update_of_ne hlabelNe, smul_smul]
    congr 1
    rw [one_div_mul_eq_div, div_div, mul_comm (faceWeight label) ((1 : ℝ) - eps)]
  have hfull :
      (∑ label, Function.update faceMass opened openedMass label
          • atomMatrix (direction label))
        = openedMass • atomMatrix (direction opened)
          + ∑ label, faceMass label • atomMatrix (direction label) := by
    rw [← Finset.add_sum_erase Finset.univ
          (fun label => Function.update faceMass opened openedMass label
            • atomMatrix (direction label)) (Finset.mem_univ opened),
        ← Finset.add_sum_erase Finset.univ
          (fun label => faceMass label • atomMatrix (direction label))
          (Finset.mem_univ opened),
        hfaceMassOpened, zero_smul, zero_add]
    congr 1
    · rw [Function.update_self]
    · refine Finset.sum_congr rfl fun label hmem => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hmem)]
  have hcoeff : ((1 : ℝ) / (1 - eps)) = 1 + eps / (1 - eps) := by
    field_simp
    ring
  unfold directionChartGap
  rw [hselected, hfull, hcoeff, add_smul, one_smul]
  abel

/-- **The eps term only helps.**  The selected atom sum of a face design with
nonnegative masses and weights is positive semidefinite, so by the lift
identity the opened weight direction can never destroy domination — the whole
off-face cost is the rank-one `openedMass` subtraction. -/
theorem posSemidef_selectedFaceAtomSum {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ))
    (faceMass faceWeight : Fin size → ℝ)
    (hmassNonneg : ∀ label, 0 ≤ faceMass label)
    (hweightNonneg : ∀ label, 0 ≤ faceWeight label)
    (selected : Finset (Fin size)) :
    (∑ label ∈ selected,
        (faceMass label / faceWeight label) • atomMatrix (direction label)).PosSemidef := by
  refine Finset.sum_induction _ Matrix.PosSemidef
    (fun leftMat rightMat hleft hright => hleft.add hright)
    Matrix.PosSemidef.zero (fun label _ => ?_)
  exact (posSemidef_atomMatrix (direction label)).smul
    (div_nonneg (hmassNonneg label) (hweightNonneg label))


/-! ## Strict-domination producers: the pointwise seed and the Schur completion

The ladder above says what a tie must LOOK like; this section builds the tools
that will refuse it.  Three design-level facts:

* every free atom of the one-line stratum sits strictly off the line plane
  (`oneLine_freeAtom_normal_dot_ne_zero`) — a vanishing normal component would
  merge the atom into the line plane and kill a bracket the pattern declares
  independent;
* SOME SINGLE complement atom strictly over-covers the normal
  (`exists_complementAtom_overcovers_normal`) — the pointwise strengthening of
  `complement_strictly_overcovers_normal`: not just the complement's sum but
  one atom alone beats `|n|²`, because the complement's weights sum to
  strictly less than one;
* the uniform Schur producer (`posDef_of_normalSurplus_planeCover`): for ANY
  selected subset, a strict normal surplus plus a plane cover beating the
  cross-coupling square yields a POSITIVE DEFINITE gap.  The engine is one
  completed square,
  `alpha * gapForm = (alpha * planeSurplus - cross²) + (cross + alpha*t)²`,
  so the statement is triple-type-agnostic: two line atoms plus one free
  (where the cross collapses to the free atom's own term), one line plus two
  free, or the free triple — one lemma serves all nineteen candidates, and it
  is direction-generic, so the two-meeting-lines class consumes it verbatim.

The tie-side reading (`isTie_yields_planeCover_failure`) turns the producer
around: a tie must exhibit, for EVERY normal-surplus triple, an in-plane probe
where the cross square meets the scaled plane surplus.  That quantified
failure family is the exact residual obstruction a direct closure of the class
obligation still has to refute. -/

/-- **Free atoms sit strictly off the line plane.**  A free atom orthogonal to
the line normal would be coplanar with two line atoms, so the bracket of
`{0, 1, f}` — independent in the pattern — would vanish. -/
theorem oneLine_freeAtom_normal_dot_ne_zero (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0)
    (freeLabel : Fin 6) (hfreeMem : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    design.atom freeLabel ⬝ᵥ normalVec ≠ 0 := by
  fin_cases hfreeMem <;> intro hzero
  · exact absurd ((hpattern 0 1 3 (by decide) (by decide) (by decide)).mp
      (by rw [atomBracket]
          exact tripleBracket_eq_zero_of_commonOrthogonal hnormalNe
            (horthogonal 0 (by decide)) (horthogonal 1 (by decide)) hzero)) (by decide)
  · exact absurd ((hpattern 0 1 4 (by decide) (by decide) (by decide)).mp
      (by rw [atomBracket]
          exact tripleBracket_eq_zero_of_commonOrthogonal hnormalNe
            (horthogonal 0 (by decide)) (horthogonal 1 (by decide)) hzero)) (by decide)
  · exact absurd ((hpattern 0 1 5 (by decide) (by decide) (by decide)).mp
      (by rw [atomBracket]
          exact tripleBracket_eq_zero_of_commonOrthogonal hnormalNe
            (horthogonal 0 (by decide)) (horthogonal 1 (by decide)) hzero)) (by decide)

/-- **Some single complement atom strictly over-covers the normal** — the
pointwise strengthening of `Gtz.complement_strictly_overcovers_normal`.  If
every complement atom stayed at or below `|n|²` in the normal direction, the
complement's weighted Parseval share — whose weights sum strictly below one —
could not carry the full `|n|²`. -/
theorem exists_complementAtom_overcovers_normal (design : WeightedDesign 6 3)
    (lineTriple : Finset (Fin 6)) (normalVec : Fin 3 → ℝ)
    (hlineNonempty : lineTriple.Nonempty) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ normalVec = 0) :
    ∃ freeLabel ∈ lineTripleᶜ,
      normalVec ⬝ᵥ normalVec < (design.atom freeLabel ⬝ᵥ normalVec) ^ 2 := by
  by_contra hnone
  push Not at hnone
  have hcarried := normalParseval_on_complement design lineTriple normalVec horthogonal
  have hnormPos : 0 < normalVec ⬝ᵥ normalVec := dotProduct_self_pos hnormalNe
  have hbound : ∑ freeLabel ∈ lineTripleᶜ,
        design.weight freeLabel * (design.atom freeLabel ⬝ᵥ normalVec) ^ 2
      ≤ (∑ freeLabel ∈ lineTripleᶜ, design.weight freeLabel)
        * (normalVec ⬝ᵥ normalVec) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun freeLabel hmem =>
      mul_le_mul_of_nonneg_left (hnone freeLabel hmem) (design.weight_pos freeLabel).le
  have hcomplLtOne : ∑ freeLabel ∈ lineTripleᶜ, design.weight freeLabel < 1 := by
    have hsplit := Finset.sum_add_sum_compl lineTriple design.weight
    rw [design.weight_sum_one] at hsplit
    have hlinePos : 0 < ∑ lineLabel ∈ lineTriple, design.weight lineLabel :=
      Finset.sum_pos (fun lineLabel _ => design.weight_pos lineLabel) hlineNonempty
    linarith
  have hshrunk : (∑ freeLabel ∈ lineTripleᶜ, design.weight freeLabel)
      * (normalVec ⬝ᵥ normalVec) < normalVec ⬝ᵥ normalVec :=
    mul_lt_of_lt_one_left hnormPos hcomplLtOne
  linarith [hcarried.le, hbound, hshrunk]

/-- The one-line reading: some single free atom of `{3, 4, 5}` strictly
over-covers the line normal — the seed atom every completion argument grows
from. -/
theorem oneLine_exists_freeAtom_overcovers_normal (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0) :
    ∃ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      normalVec ⬝ᵥ normalVec < (design.atom freeLabel ⬝ᵥ normalVec) ^ 2 := by
  have hexists := exists_complementAtom_overcovers_normal design {0, 1, 2} normalVec
    ⟨0, by decide⟩ hnormalNe horthogonal
  rwa [show ({0, 1, 2} : Finset (Fin 6))ᶜ = {3, 4, 5} by decide] at hexists

/-- **The uniform Schur producer.**  A selected subset whose atoms carry a
STRICT surplus along a unit normal, and whose in-plane coverage beats the
identity by more than the cross-coupling square demands, has a POSITIVE
DEFINITE gap.  The engine is the completed square
`alpha * gapForm = (alpha * planeSurplus - cross²) + (cross + alpha * t)²`
with `alpha = normal surplus`, so no eigenvalue machinery is needed, and the
statement is uniform over the selected subset's anatomy — line pairs plus a
free atom, mixed triples, and the free triple all instantiate it. -/
theorem posDef_of_normalSurplus_planeCover {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hsurplus : 1 < ∑ selectedLabel ∈ selected,
      (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2)
    (hplaneCover : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
      (∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe)
          * (design.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2
        < ((∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
          * ((∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe) ^ 2)
              - probe ⬝ᵥ probe)) :
    (subsetSum design selected - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec hprobeNe => ?_⟩
  · exact ((Matrix.posSemidef_sum selected fun selectedLabel _ =>
      posSemidef_atomMatrix (design.atom selectedLabel)).1).sub Matrix.isHermitian_one
  · rw [star_trivial, dominationGap_form]
    set normalCoord : ℝ := probeVec ⬝ᵥ unitNormal with hnormalCoord
    set planePart : Fin 3 → ℝ := probeVec - normalCoord • unitNormal with hplanePart
    have hdecompose : probeVec = planePart + normalCoord • unitNormal := by
      rw [hplanePart, sub_add_cancel]
    have horthPlane : planePart ⬝ᵥ unitNormal = 0 := by
      rw [hplanePart, sub_dotProduct, smul_dotProduct, hunit, smul_eq_mul, mul_one,
        ← hnormalCoord, sub_self]
    have hatomSplit : ∀ selectedLabel : Fin size,
        design.atom selectedLabel ⬝ᵥ probeVec
          = design.atom selectedLabel ⬝ᵥ planePart
            + normalCoord * (design.atom selectedLabel ⬝ᵥ unitNormal) := by
      intro selectedLabel
      rw [hdecompose, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hnormSplit : probeVec ⬝ᵥ probeVec
        = planePart ⬝ᵥ planePart + normalCoord ^ 2 := by
      rw [hdecompose, dotProduct_add, add_dotProduct, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul,
        horthPlane, dotProduct_comm unitNormal planePart, horthPlane, hunit]
      simp only [smul_eq_mul, mul_zero, mul_one]
      ring
    set coverSum : ℝ := ∑ selectedLabel ∈ selected,
      (design.atom selectedLabel ⬝ᵥ planePart) ^ 2 with hcoverSum
    set crossSum : ℝ := ∑ selectedLabel ∈ selected,
      (design.atom selectedLabel ⬝ᵥ planePart)
        * (design.atom selectedLabel ⬝ᵥ unitNormal) with hcrossSum
    set surplusBase : ℝ := ∑ selectedLabel ∈ selected,
      (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2 with hsurplusBase
    have hsumExpand : ∑ selectedLabel ∈ selected,
        (design.atom selectedLabel ⬝ᵥ probeVec) ^ 2
          = coverSum + 2 * normalCoord * crossSum + normalCoord ^ 2 * surplusBase := by
      rw [hcoverSum, hcrossSum, hsurplusBase, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun selectedLabel _ => ?_
      rw [hatomSplit selectedLabel]
      ring
    rw [hsumExpand, hnormSplit]
    by_cases hplaneZero : planePart = 0
    · have hcoverZero : coverSum = 0 := by
        rw [hcoverSum]
        exact Finset.sum_eq_zero fun selectedLabel _ => by simp [hplaneZero]
      have hcrossZero : crossSum = 0 := by
        rw [hcrossSum]
        exact Finset.sum_eq_zero fun selectedLabel _ => by simp [hplaneZero]
      have hplaneNormZero : planePart ⬝ᵥ planePart = 0 := by simp [hplaneZero]
      have hcoordNe : normalCoord ≠ 0 := by
        intro hzero
        exact hprobeNe (by rw [hdecompose, hplaneZero, hzero, zero_smul, add_zero])
      have hcoordSqPos : 0 < normalCoord ^ 2 := by positivity
      rw [hcoverZero, hcrossZero, hplaneNormZero]
      nlinarith [mul_pos hcoordSqPos (sub_pos.mpr hsurplus)]
    · have hcover := hplaneCover planePart horthPlane hplaneZero
      have halphaPos : 0 < surplusBase - 1 := by linarith [hsurplus]
      have hbracketPos :
          0 < (surplusBase - 1) * (coverSum - planePart ⬝ᵥ planePart) - crossSum ^ 2 := by
        linarith [hcover]
      have hproductPos : 0 < (surplusBase - 1)
          * (coverSum + 2 * normalCoord * crossSum + normalCoord ^ 2 * surplusBase
              - (planePart ⬝ᵥ planePart + normalCoord ^ 2)) := by
        nlinarith [hbracketPos, sq_nonneg (crossSum + (surplusBase - 1) * normalCoord)]
      nlinarith [hproductPos, halphaPos]

/-- **What a tie must refuse, quantified.**  At a tie, EVERY normal-surplus
subset comes with an in-plane probe where the cross-coupling square reaches
the scaled plane surplus — the producer's hypothesis fails everywhere.  This
family of failing probes is the exact residual obstruction of the direct
route. -/
theorem isTie_yields_planeCover_failure {size : ℕ} (design : WeightedDesign size 3)
    (htie : IsTie design) (selected : Finset (Fin size)) (hcard : selected.card = 3)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hsurplus : 1 < ∑ selectedLabel ∈ selected,
      (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) :
    ∃ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 ∧ probe ≠ 0 ∧
      ((∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
          * ((∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe) ^ 2)
              - probe ⬝ᵥ probe)
        ≤ (∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe)
            * (design.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2 := by
  by_contra hnone
  push Not at hnone
  exact htie.2 selected hcard (posDef_of_normalSurplus_planeCover design selected
    unitNormal hunit hsurplus fun probe horth hne => hnone probe horth hne)


/-! ## The corner Half-Plane Lemma: leg B of the one-line corner dichotomy

The fiber corner of the one-line stratum (line weights to zero, free weights
to their normal masses) reduces the direct route's margin question to a
two-dimensional corner datum: a plane matrix (the line part of the corner
Parseval split), three shadow points with positive masses summing to one and
barycenter zero, and per line a unit normal whose normal deficit is the plane
matrix's quadratic form there.  The corner dichotomy splits on the least
normal deficit against `1/2`; this section proves the CLOSED `<= 1/2` leg in
kernel:

* the strict range bound (`halfPlane_minMaxPair_product_lt_neg_secondMoment`):
  positive masses summing to one, zero-mean values, pairwise-distinct entries
  — the extreme pair product lies STRICTLY below minus the second moment.
  The non-strict bound is the mass average of the pointwise inequality
  `0 <= (value - min) * (max - value)`; equality would force every value onto
  the two-point support `{min, max}`, and three pairwise-distinct values do
  not fit in two slots;
* the corner feeds: the barycenter identity dotted with the normal gives the
  zero mean (`cornerBarycenter_zeroMean`), and the matrix Parseval split
  evaluated at the unit normal gives the second moment as one minus the
  normal deficit (`cornerSplit_secondMoment_eq_one_sub_normalDeficit`);
* the covering statements: on any corner datum the extreme shadow pair's
  reading product lies strictly below minus the normal complement
  (`cornerHalfPlane_pair_product_lt_neg_normalComplement`, the sharp form),
  hence strictly below `-(1/2)` whenever the normal deficit is at most `1/2`
  (`cornerHalfPlane_pair_product_lt_neg_half`) — the CLOSED region, including
  the knife face where the deficit is exactly `1/2` and the fine adversary's
  value reaches zero;
* the seam hooks (`tripleBracket_planeAtom_expand`,
  `shadowReadings_separated_of_bracket_ne_zero`): the design bracket of a
  plane atom against two off-plane atoms factors through the difference of
  their shadow normal readings, so the one-line pattern's declared
  independence of `{line, free, free}` is exactly the pairwise-distinctness
  the range bound consumes.

The OPEN `> 1/2` leg (the vertex dual certificate) and the corner-to-interior
seam are NOT stated here; they remain the named residuals of the corner
endgame. -/

/-- **The strict range bound with the two-point-support kill.**  Positive
masses summing to one, zero-mean values, pairwise-distinct entries: the
extreme pair product lies strictly below minus the second moment.  The mass
average of `0 <= (value - min) * (max - value)` gives the non-strict bound;
equality forces every value onto `{min, max}`, and three pairwise-distinct
values do not fit in two slots. -/
theorem halfPlane_minMaxPair_product_lt_neg_secondMoment
    (shadowMass shadowValue : Fin 3 → ℝ)
    (hmassPos : ∀ shadowIdx, 0 < shadowMass shadowIdx)
    (hmassSum : ∑ shadowIdx, shadowMass shadowIdx = 1)
    (hzeroMean : ∑ shadowIdx, shadowMass shadowIdx * shadowValue shadowIdx = 0)
    (hseparated : ∀ firstIdx secondIdx : Fin 3, firstIdx ≠ secondIdx →
      shadowValue firstIdx ≠ shadowValue secondIdx) :
    ∃ minIdx maxIdx : Fin 3, minIdx ≠ maxIdx ∧
      shadowValue minIdx * shadowValue maxIdx
        < -(∑ shadowIdx, shadowMass shadowIdx * shadowValue shadowIdx ^ 2) := by
  obtain ⟨minIdx, -, hminLe⟩ :=
    Finset.exists_min_image Finset.univ shadowValue Finset.univ_nonempty
  obtain ⟨maxIdx, -, hmaxLe⟩ :=
    Finset.exists_max_image Finset.univ shadowValue Finset.univ_nonempty
  have htermNonneg : ∀ shadowIdx : Fin 3,
      0 ≤ shadowMass shadowIdx * ((shadowValue shadowIdx - shadowValue minIdx)
        * (shadowValue maxIdx - shadowValue shadowIdx)) := fun shadowIdx =>
    mul_nonneg (hmassPos shadowIdx).le (mul_nonneg
      (sub_nonneg.mpr (hminLe shadowIdx (Finset.mem_univ shadowIdx)))
      (sub_nonneg.mpr (hmaxLe shadowIdx (Finset.mem_univ shadowIdx))))
  have hkeyIdentity : ∑ shadowIdx, shadowMass shadowIdx
        * ((shadowValue shadowIdx - shadowValue minIdx)
          * (shadowValue maxIdx - shadowValue shadowIdx))
      = -(∑ shadowIdx, shadowMass shadowIdx * shadowValue shadowIdx ^ 2)
        - shadowValue minIdx * shadowValue maxIdx := by
    simp only [Fin.sum_univ_three] at hzeroMean hmassSum ⊢
    linear_combination (shadowValue minIdx + shadowValue maxIdx) * hzeroMean
      - shadowValue minIdx * shadowValue maxIdx * hmassSum
  have hsumNonneg : 0 ≤ ∑ shadowIdx, shadowMass shadowIdx
      * ((shadowValue shadowIdx - shadowValue minIdx)
        * (shadowValue maxIdx - shadowValue shadowIdx)) :=
    Finset.sum_nonneg fun shadowIdx _ => htermNonneg shadowIdx
  have hsumPos : 0 < ∑ shadowIdx, shadowMass shadowIdx
      * ((shadowValue shadowIdx - shadowValue minIdx)
        * (shadowValue maxIdx - shadowValue shadowIdx)) := by
    rcases hsumNonneg.lt_or_eq with hpos | hzeroSum
    · exact hpos
    · exfalso
      have hallZero := (Finset.sum_eq_zero_iff_of_nonneg
        fun shadowIdx _ => htermNonneg shadowIdx).mp hzeroSum.symm
      have hvalueSplit : ∀ shadowIdx : Fin 3,
          shadowValue shadowIdx = shadowValue minIdx
            ∨ shadowValue shadowIdx = shadowValue maxIdx := by
        intro shadowIdx
        have hterm := hallZero shadowIdx (Finset.mem_univ shadowIdx)
        rcases mul_eq_zero.mp hterm with hmassZero | hfactorZero
        · exact absurd hmassZero (hmassPos shadowIdx).ne'
        · rcases mul_eq_zero.mp hfactorZero with hleftFactor | hrightFactor
          · exact Or.inl (sub_eq_zero.mp hleftFactor)
          · exact Or.inr (sub_eq_zero.mp hrightFactor).symm
      rcases hvalueSplit 0 with hzero | hzero <;>
        rcases hvalueSplit 1 with hone | hone <;>
          rcases hvalueSplit 2 with htwo | htwo
      · exact hseparated 0 1 (by decide) (hzero.trans hone.symm)
      · exact hseparated 0 1 (by decide) (hzero.trans hone.symm)
      · exact hseparated 0 2 (by decide) (hzero.trans htwo.symm)
      · exact hseparated 1 2 (by decide) (hone.trans htwo.symm)
      · exact hseparated 1 2 (by decide) (hone.trans htwo.symm)
      · exact hseparated 0 2 (by decide) (hzero.trans htwo.symm)
      · exact hseparated 0 1 (by decide) (hzero.trans hone.symm)
      · exact hseparated 0 1 (by decide) (hzero.trans hone.symm)
  have hproductLt : shadowValue minIdx * shadowValue maxIdx
      < -(∑ shadowIdx, shadowMass shadowIdx * shadowValue shadowIdx ^ 2) := by
    linarith [hkeyIdentity, hsumPos]
  have hsecondNonneg : 0 ≤ ∑ shadowIdx, shadowMass shadowIdx
      * shadowValue shadowIdx ^ 2 :=
    Finset.sum_nonneg fun shadowIdx _ =>
      mul_nonneg (hmassPos shadowIdx).le (sq_nonneg _)
  have hneIdx : minIdx ≠ maxIdx := by
    intro heqIdx
    have hproductNeg : shadowValue minIdx * shadowValue maxIdx < 0 :=
      hproductLt.trans_le (neg_nonpos.mpr hsecondNonneg)
    rw [heqIdx] at hproductNeg
    exact absurd hproductNeg (not_lt.mpr (mul_self_nonneg (shadowValue maxIdx)))
  exact ⟨minIdx, maxIdx, hneIdx, hproductLt⟩

/-- **The pair bound under a second-moment floor.**  Any lower bound on the
second moment transfers to the extreme pair: the reading product drops
strictly below minus the bound.  At bound `1/2` this is the corner covering
conclusion of the closed leg. -/
theorem halfPlane_exists_pair_product_lt_neg_bound
    (shadowMass shadowValue : Fin 3 → ℝ) (boundVal : ℝ)
    (hmassPos : ∀ shadowIdx, 0 < shadowMass shadowIdx)
    (hmassSum : ∑ shadowIdx, shadowMass shadowIdx = 1)
    (hzeroMean : ∑ shadowIdx, shadowMass shadowIdx * shadowValue shadowIdx = 0)
    (hseparated : ∀ firstIdx secondIdx : Fin 3, firstIdx ≠ secondIdx →
      shadowValue firstIdx ≠ shadowValue secondIdx)
    (hsecondBound : boundVal
      ≤ ∑ shadowIdx, shadowMass shadowIdx * shadowValue shadowIdx ^ 2) :
    ∃ minIdx maxIdx : Fin 3, minIdx ≠ maxIdx ∧
      shadowValue minIdx * shadowValue maxIdx < -boundVal := by
  obtain ⟨minIdx, maxIdx, hneIdx, hproductLt⟩ :=
    halfPlane_minMaxPair_product_lt_neg_secondMoment shadowMass shadowValue
      hmassPos hmassSum hzeroMean hseparated
  exact ⟨minIdx, maxIdx, hneIdx, hproductLt.trans_le (by linarith)⟩

/-- **The corner barycenter dotted with any direction is a zero mean.** -/
theorem cornerBarycenter_zeroMean
    (shadowMass : Fin 3 → ℝ) (shadowPoint : Fin 3 → (Fin 2 → ℝ))
    (normalVec : Fin 2 → ℝ)
    (hbarycenter : ∑ shadowIdx, shadowMass shadowIdx • shadowPoint shadowIdx = 0) :
    ∑ shadowIdx, shadowMass shadowIdx * (shadowPoint shadowIdx ⬝ᵥ normalVec) = 0 := by
  have happlied := congrArg
    (fun leftVec : Fin 2 → ℝ => leftVec ⬝ᵥ normalVec) hbarycenter
  simp only [Fin.sum_univ_three] at happlied ⊢
  simpa only [add_dotProduct, smul_dotProduct, zero_dotProduct, smul_eq_mul]
    using happlied

/-- The quadratic form of a scaled outer square: the scale times the squared
reading. -/
theorem dotProduct_smul_vecMulVec_self
    (scaleVal : ℝ) (shadowVec probeVec : Fin 2 → ℝ) :
    probeVec ⬝ᵥ ((scaleVal • Matrix.vecMulVec shadowVec shadowVec) *ᵥ probeVec)
      = scaleVal * (shadowVec ⬝ᵥ probeVec) ^ 2 := by
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
    Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  ring

/-- **The corner Parseval split evaluated at the unit normal.**  If the plane
matrix and the shadow outer squares split the identity, the shadows' weighted
second moment along a unit direction is one minus the plane matrix's normal
deficit there. -/
theorem cornerSplit_secondMoment_eq_one_sub_normalDeficit
    (planeMatrix : Matrix (Fin 2) (Fin 2) ℝ)
    (shadowMass : Fin 3 → ℝ) (shadowPoint : Fin 3 → (Fin 2 → ℝ))
    (normalVec : Fin 2 → ℝ)
    (hsplit : planeMatrix + ∑ shadowIdx, shadowMass shadowIdx •
        Matrix.vecMulVec (shadowPoint shadowIdx) (shadowPoint shadowIdx) = 1)
    (hunit : normalVec ⬝ᵥ normalVec = 1) :
    ∑ shadowIdx, shadowMass shadowIdx * (shadowPoint shadowIdx ⬝ᵥ normalVec) ^ 2
      = 1 - normalVec ⬝ᵥ (planeMatrix *ᵥ normalVec) := by
  have happlied := congrArg
    (fun mat : Matrix (Fin 2) (Fin 2) ℝ => normalVec ⬝ᵥ (mat *ᵥ normalVec)) hsplit
  simp only [Fin.sum_univ_three] at happlied
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec,
    dotProduct_smul_vecMulVec_self, hunit] at happlied
  simp only [Fin.sum_univ_three]
  linarith [happlied]

/-- **The corner Half-Plane Lemma, sharp form.**  On a corner datum — positive
shadow masses summing to one, barycenter zero, the Parseval split, pairwise
distinct normal readings — the extreme shadow pair's reading product lies
strictly below minus the normal complement. -/
theorem cornerHalfPlane_pair_product_lt_neg_normalComplement
    (planeMatrix : Matrix (Fin 2) (Fin 2) ℝ)
    (shadowMass : Fin 3 → ℝ) (shadowPoint : Fin 3 → (Fin 2 → ℝ))
    (normalVec : Fin 2 → ℝ)
    (hmassPos : ∀ shadowIdx, 0 < shadowMass shadowIdx)
    (hmassSum : ∑ shadowIdx, shadowMass shadowIdx = 1)
    (hbarycenter : ∑ shadowIdx, shadowMass shadowIdx • shadowPoint shadowIdx = 0)
    (hsplit : planeMatrix + ∑ shadowIdx, shadowMass shadowIdx •
        Matrix.vecMulVec (shadowPoint shadowIdx) (shadowPoint shadowIdx) = 1)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hseparated : ∀ firstIdx secondIdx : Fin 3, firstIdx ≠ secondIdx →
      shadowPoint firstIdx ⬝ᵥ normalVec ≠ shadowPoint secondIdx ⬝ᵥ normalVec) :
    ∃ minIdx maxIdx : Fin 3, minIdx ≠ maxIdx ∧
      (shadowPoint minIdx ⬝ᵥ normalVec) * (shadowPoint maxIdx ⬝ᵥ normalVec)
        < -(1 - normalVec ⬝ᵥ (planeMatrix *ᵥ normalVec)) := by
  have hsecond := cornerSplit_secondMoment_eq_one_sub_normalDeficit
    planeMatrix shadowMass shadowPoint normalVec hsplit hunit
  obtain ⟨minIdx, maxIdx, hneIdx, hproductLt⟩ :=
    halfPlane_minMaxPair_product_lt_neg_secondMoment shadowMass
      (fun shadowIdx => shadowPoint shadowIdx ⬝ᵥ normalVec) hmassPos hmassSum
      (cornerBarycenter_zeroMean shadowMass shadowPoint normalVec hbarycenter)
      hseparated
  refine ⟨minIdx, maxIdx, hneIdx, ?_⟩
  have hbounded := hproductLt
  simp only [hsecond] at hbounded
  exact hbounded

/-- **The corner covering statement on the closed leg-B region.**  If a
line's normal deficit is at most `1/2` — the CLOSED region, including the
knife face where the deficit equals `1/2` exactly — the extreme shadow pair
for that line wins strictly: its normal-reading product drops strictly below
`-(1/2)`. -/
theorem cornerHalfPlane_pair_product_lt_neg_half
    (planeMatrix : Matrix (Fin 2) (Fin 2) ℝ)
    (shadowMass : Fin 3 → ℝ) (shadowPoint : Fin 3 → (Fin 2 → ℝ))
    (normalVec : Fin 2 → ℝ)
    (hmassPos : ∀ shadowIdx, 0 < shadowMass shadowIdx)
    (hmassSum : ∑ shadowIdx, shadowMass shadowIdx = 1)
    (hbarycenter : ∑ shadowIdx, shadowMass shadowIdx • shadowPoint shadowIdx = 0)
    (hsplit : planeMatrix + ∑ shadowIdx, shadowMass shadowIdx •
        Matrix.vecMulVec (shadowPoint shadowIdx) (shadowPoint shadowIdx) = 1)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hseparated : ∀ firstIdx secondIdx : Fin 3, firstIdx ≠ secondIdx →
      shadowPoint firstIdx ⬝ᵥ normalVec ≠ shadowPoint secondIdx ⬝ᵥ normalVec)
    (hdeficit : normalVec ⬝ᵥ (planeMatrix *ᵥ normalVec) ≤ 1 / 2) :
    ∃ minIdx maxIdx : Fin 3, minIdx ≠ maxIdx ∧
      (shadowPoint minIdx ⬝ᵥ normalVec) * (shadowPoint maxIdx ⬝ᵥ normalVec)
        < -(1 / 2) := by
  obtain ⟨minIdx, maxIdx, hneIdx, hproductLt⟩ :=
    cornerHalfPlane_pair_product_lt_neg_normalComplement planeMatrix shadowMass
      shadowPoint normalVec hmassPos hmassSum hbarycenter hsplit hunit hseparated
  exact ⟨minIdx, maxIdx, hneIdx, hproductLt.trans_le (by linarith)⟩

/-- **The bracket of a plane atom against two off-plane atoms, expanded.**
The bracket depends on the two free atoms only through their heights and the
difference of their shadow normal readings. -/
theorem tripleBracket_planeAtom_expand
    (planeX planeY : ℝ) (freeFirst freeSecond : Fin 3 → ℝ) :
    tripleBracket ![planeX, planeY, 0] freeFirst freeSecond
      = freeFirst 2 * (planeY * freeSecond 0 - planeX * freeSecond 1)
        - freeSecond 2 * (planeY * freeFirst 0 - planeX * freeFirst 1) := by
  rw [tripleBracket_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **Bracket independence separates the shadow normal readings** — the seam
hook feeding the pairwise-distinctness hypothesis of the range bound: when
the one-line pattern declares a line atom with two free atoms independent,
the two free shadows read differently against the line's rotated (normal)
direction. -/
theorem shadowReadings_separated_of_bracket_ne_zero
    (planeX planeY : ℝ) (freeFirst freeSecond : Fin 3 → ℝ)
    (hfirstHeight : freeFirst 2 ≠ 0) (hsecondHeight : freeSecond 2 ≠ 0)
    (hbracket : tripleBracket ![planeX, planeY, 0] freeFirst freeSecond ≠ 0) :
    (![-planeY, planeX] : Fin 2 → ℝ)
        ⬝ᵥ ![freeFirst 0 / freeFirst 2, freeFirst 1 / freeFirst 2]
      ≠ (![-planeY, planeX] : Fin 2 → ℝ)
        ⬝ᵥ ![freeSecond 0 / freeSecond 2, freeSecond 1 / freeSecond 2] := by
  have hreadingEq : ∀ freeVec : Fin 3 → ℝ,
      (![-planeY, planeX] : Fin 2 → ℝ)
          ⬝ᵥ ![freeVec 0 / freeVec 2, freeVec 1 / freeVec 2]
        = (planeX * freeVec 1 - planeY * freeVec 0) / freeVec 2 := by
    intro freeVec
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  intro hcontra
  rw [hreadingEq, hreadingEq,
    div_eq_div_iff hfirstHeight hsecondHeight] at hcontra
  apply hbracket
  rw [tripleBracket_planeAtom_expand]
  linear_combination hcontra
end Gtz
