/-
# The eight six-point ledger entries, sorted by stress structure

`Gtz.hingeHoldsAtSize_sixThree_of_balancedStressResidual` reduces
`Gtz.HingeHoldsAtSize 6 3` — equivalently, by
`Gtz.gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three`, rank-three GTZ at
every `n` — to eight tie-freeness obligations, one per non-near-pencil entry of
`Gtz.lineFamiliesSix`.  A second route through the same hinge,
`Gtz.sixThree_stress_trichotomy`, sorts designs not by line pattern but by
STRESS structure: stress-free (i), balanced full support (ii), coplanar support
(iii).  This file builds the dictionary between the two, routes every entry into
the branch machinery, and then shows the dictionary makes the enumeration
unnecessary.

## The dictionary

Write a design's six atoms as points of the projective plane.  A stress is a
linear dependence of the six rank-one atoms; `Sym(3)` has dimension six, so a
stress exists exactly when the six Veronese images are dependent — exactly when
the six points lie on a CONIC.  A conic meeting a line three times contains it
(`Gtz.quadForm_eq_zero_of_span_of_three_collinear`), so a conic through a
configuration with a three-point line is a LINE PAIR.  That single observation
sorts all eight entries:

| entry                               | lines     | branch      | disposition          |
| ----------------------------------- | --------- | ----------- | -------------------- |
| `[]`                                | none      | (i) or (ii) | open on its (i) part |
| `[[0,1,2]]`                         | `{3}`     | (i) only    | open                 |
| `[[0,1,2],[3,4,5]]`                 | `{3,3}`   | (ii) only   | DISCHARGED, branch (ii) capstone |
| `[[0,1,2],[0,3,4]]`                 | `{3,3}`   | (i) only    | open                 |
| `[[0,1,2],[0,3,4],[1,3,5]]`         | `{3,3,3}` | (i) only    | open                 |
| `[[0,1,2],[0,3,4],[1,3,5],[2,4,5]]` | `{3^4}`   | (i) only    | open                 |
| `[[0,1,2,3]]`                       | `{4}`     | (iii)       | DISCHARGED, branch (iii) capstone |
| `[[0,1,2,3],[0,4,5]]`               | `{4,3}`   | (iii)       | DISCHARGED, branch (iii) capstone |

Branch (iii) is reached exactly by the two entries with a four-point line, and
those two entries FALL: a four-point line puts four atoms on one plane, so at
most two atoms are off it, and
`Gtz.sixThree_hasParallelPair_of_isTie_of_offPlaneCard_le_two` turns a tie into a
parallel pair — which the pattern forbids.  That route needs no stress at all;
`exists_coplanarStress_of_fourPointLine` separately proves the branch LABEL, by
showing the forced stress cannot reach either off-line atom without making them
parallel.  Both conclusions are conditional on `Gtz.TwoPoleStratumSelection 6`
and on nothing else, and the dependency rides in the hypotheses.

The two-disjoint-lines entry is the whole of branch (ii): its two lines are a
line-pair conic through all six points, so every design carries a stress
(`Gtz.patternForcesStress_twoDisjointLines`), and no design carries a coplanar
one, so every stress has FULL support.  That is exactly the input of the
balanced-stratum capstone, quoted here as `BalancedStratumCapstone`.

The stress-side half of the dictionary is unconditional.  Four entries —
`[[0,1,2]]`, `[[0,1,2],[0,3,4]]`, `[[0,1,2],[0,3,4],[1,3,5]]`, and `M(K4)` —
are STRESS-FREE outright: their designs' atoms are a basis of `Sym(3)`.  The
mechanism is the line-pair law in its stress form, two lines of linear algebra
rather than any projective geometry.  Let `n` be the normal of the line
`{0,1,2}`.  Multiplying a stress `Sum z_c A_c = 0` by `n` kills the three
on-line terms — `A_c n = (g_c . n) g_c` — and leaves
`Sum_{c in {3,4,5}} z_c (g_c . n) g_c = 0`.  On a full-support stress every
coefficient there is nonzero, so `{3,4,5}` is a dependent triple, and none of
those four patterns has one.  Full support itself comes from
`Gtz.stress_fullSupport_or_orthogonalProbe` plus
`Gtz.sixThree_offPlaneCard_le_two_of_coplanarStress`: a stress with coplanar
support would put four atoms on a plane, hence four labels pairwise dependent,
which no pattern with all lines of size three admits.

## What this costs the stress-based narrowings

`Gtz.HasOnlyBalancedStress` is VACUOUS on a stress-free design.  So
`Gtz.stratumIsTieFreeAmongHeavy_of_balancedStress_sixThree` gives exactly
nothing on those four entries, `M(K4)` — the sharpest of the nine — among them.
Dually, `Gtz.PatternForcesStress` cannot be extended past the three entries that
already have it: four of the remaining five provably carry NO stress at all, so
no argument of that shape reaches them.  Only the line-free entry `[]` is
undecided between the branches — it meets both, its balanced part being the
codimension-one sublocus where the six points fall on a smooth conic.

## The residual, in its sharpest form

With both branch capstones the enumeration is not needed at all.  The
trichotomy alone gives `hingeHoldsAtSize_sixThree_of_stressFreeHinge`: the hinge
at six points is `Gtz.TwoPoleStratumSelection 6`, the balanced capstone, and the
hinge restricted to designs whose atoms are a BASIS of `Sym(3)`.  The
line-pattern route agrees and localizes it — the five surviving ledger entries
are exactly the strata that are stress-free or meet the stress-free branch.

Branch (i) has no capstone, and it cannot get one of certificate shape: every
certificate of this kind concludes STRICT domination, a tie admits none, so at a
tie every certificate fails and any residual reading "the certificate fails but
domination still holds" contains the whole tie locus.  The stress-free arm has
to be settled as tie-emptiness, not relaxed.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.TwoPoleStratum
import Gtz.Design.LinePatternSixCasesTwo
import Gtz.Quantitative.HingeStressNarrowing
import Gtz.Reduction.ConverseBridge
import Gtz.Reduction.ParallelFreeReach
import Gtz.Design.BalancedStratum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## Two decidable conditions on a pattern -/

/-- Every pair of labels has a witness making it independent.  A pattern with
this property leaves no room for a parallel pair, because two parallel atoms
make EVERY triple through them dependent. -/
def PatternForbidsParallelPair {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∀ keptLabel dropLabel : Fin size, keptLabel ≠ dropLabel →
    ∃ witnessLabel : Fin size, keptLabel ≠ witnessLabel ∧ dropLabel ≠ witnessLabel ∧
      ¬ pattern keptLabel dropLabel witnessLabel

instance decidablePatternForbidsParallelPair {size : ℕ} (pattern : LinePattern size)
    [∀ leftLabel midLabel rightLabel : Fin size,
      Decidable (pattern leftLabel midLabel rightLabel)] :
    Decidable (PatternForbidsParallelPair pattern) := by
  unfold PatternForbidsParallelPair
  infer_instance

/-- No four labels are pairwise dependent: every label set of size at least four
contains an INDEPENDENT distinct triple.  Equivalently the pattern has no line of
four or more points. -/
def PatternHasNoCoplanarQuadruple (pattern : LinePattern 6) : Prop :=
  ∀ labelSet : Finset (Fin 6), 4 ≤ labelSet.card →
    ∃ leftLabel ∈ labelSet, ∃ midLabel ∈ labelSet, ∃ rightLabel ∈ labelSet,
      leftLabel ≠ midLabel ∧ leftLabel ≠ rightLabel ∧ midLabel ≠ rightLabel ∧
        ¬ pattern leftLabel midLabel rightLabel

instance decidablePatternHasNoCoplanarQuadruple (pattern : LinePattern 6)
    [∀ leftLabel midLabel rightLabel : Fin 6,
      Decidable (pattern leftLabel midLabel rightLabel)] :
    Decidable (PatternHasNoCoplanarQuadruple pattern) := by
  unfold PatternHasNoCoplanarQuadruple
  infer_instance

/-- **A PATTERN CAN FORBID PARALLEL ATOMS ALL BY ITSELF.**  Two parallel atoms
have vanishing bracket against every third label, so the pattern would have to
carry every triple through them; a single independent witness triple rules that
out.  Every entry of `Gtz.lineFamiliesSix` supplies one. -/
theorem isPrimitiveDesign_of_hasLinePattern {size : ℕ} {pattern : LinePattern size}
    (hforbids : PatternForbidsParallelPair pattern) (design : WeightedDesign size 3)
    (hpattern : HasLinePattern design pattern) : IsPrimitiveDesign design := by
  intro keptLabel dropLabel ratio hdistinct hparallel
  obtain ⟨witnessLabel, hkeptWitness, hdropWitness, hwitnessFree⟩ :=
    hforbids keptLabel dropLabel hdistinct
  refine hwitnessFree ((hpattern keptLabel dropLabel witnessLabel hdistinct hkeptWitness
    hdropWitness).mp ?_)
  exact tripleBracket_eq_zero_of_parallel (design.atom keptLabel) (design.atom witnessLabel)
    ratio hparallel

/-! ## Branch (iii): the entries with a four-point line

A four-point line pins four atoms to one plane, so at most two atoms are off it,
and the two-pole capstone applies with no stress construction at all. -/

/-- The two-pole capstone with the probe left UNNORMALIZED.  The off-plane
filter is scale invariant, so rescaling the probe to unit length changes
nothing. -/
theorem sixThree_hasParallelPair_of_isTie_of_offPlaneCard_le_two_of_probeNe
    (hselection : TwoPoleStratumSelection 6)
    (design : WeightedDesign 6 3) (htie : IsTie design)
    {probe : Fin 3 → ℝ} (hprobeNe : probe ≠ 0)
    (hoffPlaneSmall :
      (Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0).card ≤ 2) :
    HasParallelPair design := by
  classical
  have hprobeNormPos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
  have hsqrtPos : 0 < Real.sqrt (probe ⬝ᵥ probe) := Real.sqrt_pos.mpr hprobeNormPos
  set scale := (Real.sqrt (probe ⬝ᵥ probe))⁻¹ with hscaleDef
  have hscaleNe : scale ≠ 0 := inv_ne_zero hsqrtPos.ne'
  set unitProbe := scale • probe with hunitProbeDef
  have hunit : unitProbe ⬝ᵥ unitProbe = 1 := by
    rw [hunitProbeDef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      hscaleDef, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hprobeNormPos.le]
    exact inv_mul_cancel₀ hprobeNormPos.ne'
  have hunitProbeNe : unitProbe ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    exact one_ne_zero hunit.symm
  have hfilterEq : (Finset.univ.filter fun c => design.atom c ⬝ᵥ unitProbe ≠ 0)
      = Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0 := by
    refine Finset.filter_congr fun c _ => ?_
    rw [hunitProbeDef, dotProduct_smul, smul_eq_mul]
    constructor
    · intro hne hzero
      exact hne (by rw [hzero, mul_zero])
    · intro hne hzero
      exact hne ((mul_eq_zero.mp hzero).resolve_left hscaleNe)
  exact sixThree_hasParallelPair_of_isTie_of_offPlaneCard_le_two hselection design htie
    unitProbe hunitProbeNe hunit (by rw [hfilterEq]; exact hoffPlaneSmall)

/-- **A FOUR-POINT LINE DISCHARGES ITS ENTRY**, modulo the named two-pole
residual.  The line's normal leaves at most two atoms off its plane, the
capstone turns the tie into a parallel pair, and the pattern forbids one. -/
theorem stratumIsTieFree_of_lineCardFour_of_selection
    (hselection : TwoPoleStratumSelection 6) {pattern : LinePattern 6}
    (hforbids : PatternForbidsParallelPair pattern)
    (lineSet : Finset (Fin 6)) (hlineCard : 4 ≤ lineSet.card)
    (firstLabel secondLabel witnessLabel : Fin 6)
    (hdistinct : firstLabel ≠ secondLabel)
    (hfirstWitness : firstLabel ≠ witnessLabel) (hsecondWitness : secondLabel ≠ witnessLabel)
    (hwitnessFree : ¬ pattern firstLabel secondLabel witnessLabel)
    (hlineDependent : ∀ label ∈ lineSet, label ≠ firstLabel → label ≠ secondLabel →
      pattern firstLabel secondLabel label) :
    StratumIsTieFree pattern := by
  classical
  intro design hpattern htie
  obtain ⟨normalVec, hnormalNe, hcoplanar⟩ :=
    exists_lineNormal_of_hasLinePattern design hpattern lineSet firstLabel secondLabel
      witnessLabel hdistinct hfirstWitness hsecondWitness hwitnessFree hlineDependent
  have hsubset : (Finset.univ.filter fun c => design.atom c ⬝ᵥ normalVec ≠ 0) ⊆ lineSetᶜ := by
    intro label hlabel
    rw [Finset.mem_compl]
    intro hmem
    exact (Finset.mem_filter.mp hlabel).2 (hcoplanar label hmem)
  have hcardLe : (Finset.univ.filter fun c => design.atom c ⬝ᵥ normalVec ≠ 0).card ≤ 2 := by
    have hstep := Finset.card_le_card hsubset
    rw [Finset.card_compl, Fintype.card_fin] at hstep
    omega
  exact (isPrimitiveDesign_iff_not_hasParallelPair design).mp
    (isPrimitiveDesign_of_hasLinePattern hforbids design hpattern)
    (sixThree_hasParallelPair_of_isTie_of_offPlaneCard_le_two_of_probeNe hselection design htie
      hnormalNe hcardLe)

/-- **ENTRY `[[0,1,2,3]]`, one four-point line: TIE-FREE**, modulo the two-pole
residual. -/
theorem stratumIsTieFree_fourPointLine_of_selection (hselection : TwoPoleStratumSelection 6) :
    StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2, 3]]) := by
  refine stratumIsTieFree_of_lineCardFour_of_selection hselection (by decide)
    ({0, 1, 2, 3} : Finset (Fin 6)) (by decide) 0 1 4 (by decide) (by decide) (by decide)
    (by decide) ?_
  intro label hlabel hfirst hsecond
  revert hlabel hfirst hsecond
  fin_cases label <;> decide

/-- **ENTRY `[[0,1,2,3],[0,4,5]]`, a four-point line and a three-point line:
TIE-FREE**, modulo the two-pole residual. -/
theorem stratumIsTieFree_fourPointLineWithThreePointLine_of_selection
    (hselection : TwoPoleStratumSelection 6) :
    StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2, 3], [0, 4, 5]]) := by
  refine stratumIsTieFree_of_lineCardFour_of_selection hselection (by decide)
    ({0, 1, 2, 3} : Finset (Fin 6)) (by decide) 1 2 4 (by decide) (by decide) (by decide)
    (by decide) ?_
  intro label hlabel hfirst hsecond
  revert hlabel hfirst hsecond
  fin_cases label <;> decide

/-- **A FOUR-POINT-LINE STRATUM SITS IN BRANCH (iii).**  The label of the branch,
proved rather than asserted: the pattern's forced stress cannot reach the two
off-line labels, because multiplying it by the line's normal leaves a dependence
between those two atoms alone, and primitivity forbids one.  So the stress is
supported inside the line and its support is coplanar — the branch-(iii)
disjunct of `Gtz.sixThree_stress_trichotomy` verbatim.  The tie-freeness of
these two entries does not go through this theorem; the off-plane count reaches
the capstone directly. -/
theorem exists_coplanarStress_of_fourPointLine {pattern : LinePattern 6}
    (hforbids : PatternForbidsParallelPair pattern) (hforces : PatternForcesStress pattern)
    (hline : ∀ label ∈ ({0, 1, 2, 3} : Finset (Fin 6)),
      label ≠ 0 → label ≠ 1 → pattern 0 1 label)
    (hoffFourth : ¬ pattern 0 1 4) (hoffFifth : ¬ pattern 0 1 5)
    (design : WeightedDesign 6 3) (hpattern : HasLinePattern design pattern) :
    ∃ (stress : Fin 6 → ℝ) (probe : Fin 3 → ℝ), stress ≠ 0 ∧ probe ≠ 0
      ∧ (∑ c, stress c • atomMatrix (design.atom c)) = 0
      ∧ ∀ c, stress c ≠ 0 → design.atom c ⬝ᵥ probe = 0 := by
  classical
  have hprimitive := isPrimitiveDesign_of_hasLinePattern hforbids design hpattern
  obtain ⟨stress, hstressNe, hstress⟩ := hforces design hpattern
  obtain ⟨normalVec, hnormalNe, hcoplanar⟩ :=
    exists_lineNormal_of_hasLinePattern design hpattern ({0, 1, 2, 3} : Finset (Fin 6))
      0 1 4 (by decide) (by decide) (by decide) hoffFourth hline
  have hoffPlane : ∀ offLabel : Fin 6, ¬ pattern 0 1 offLabel → (0 : Fin 6) ≠ offLabel →
      (1 : Fin 6) ≠ offLabel → design.atom offLabel ⬝ᵥ normalVec ≠ 0 := by
    intro offLabel hoffFree hzeroth hfirst hpairing
    exact hoffFree ((hpattern 0 1 offLabel (by decide) hzeroth hfirst).mp
      (tripleBracket_eq_zero_of_forall_dotProduct_eq_zero (design.atom 0) (design.atom 1)
        (design.atom offLabel) normalVec hnormalNe (hcoplanar 0 (by decide))
        (hcoplanar 1 (by decide)) hpairing))
  have hmultiplied : ∑ c, (stress c * (design.atom c ⬝ᵥ normalVec)) • design.atom c = 0 := by
    have hstep := congrArg (fun gramSum => gramSum *ᵥ normalVec) hstress
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq,
      smul_smul, Matrix.zero_mulVec] at hstep
    exact hstep
  rw [Fin.sum_univ_six, hcoplanar 0 (by decide), hcoplanar 1 (by decide),
    hcoplanar 2 (by decide), hcoplanar 3 (by decide)] at hmultiplied
  simp only [mul_zero, zero_smul, zero_add] at hmultiplied
  have hfourthZero : stress 4 * (design.atom 4 ⬝ᵥ normalVec) = 0 := by
    by_contra hne
    have hsolve : (stress 4 * (design.atom 4 ⬝ᵥ normalVec)) • design.atom 4
        = (-(stress 5 * (design.atom 5 ⬝ᵥ normalVec))) • design.atom 5 := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact hmultiplied
    refine hprimitive 5 4 ((stress 4 * (design.atom 4 ⬝ᵥ normalVec))⁻¹
      * (-(stress 5 * (design.atom 5 ⬝ᵥ normalVec)))) (by decide) ?_
    rw [mul_smul, ← hsolve, inv_smul_smul₀ hne]
  have hfifthZero : stress 5 * (design.atom 5 ⬝ᵥ normalVec) = 0 := by
    rw [hfourthZero, zero_smul, zero_add] at hmultiplied
    by_contra hne
    refine hprimitive 4 5 0 (by decide) ?_
    rw [zero_smul]
    exact (smul_eq_zero.mp hmultiplied).resolve_left hne
  refine ⟨stress, normalVec, hstressNe, hnormalNe, hstress, fun c hlive => ?_⟩
  have hnotFourth : c ≠ 4 := by
    rintro rfl
    exact hlive ((mul_eq_zero.mp hfourthZero).resolve_right
      (hoffPlane 4 hoffFourth (by decide) (by decide)))
  have hnotFifth : c ≠ 5 := by
    rintro rfl
    exact hlive ((mul_eq_zero.mp hfifthZero).resolve_right
      (hoffPlane 5 hoffFifth (by decide) (by decide)))
  refine hcoplanar c ?_
  revert hnotFourth hnotFifth
  fin_cases c <;> decide

/-- Entry `[[0,1,2,3]]` meets branch (iii) at every design. -/
theorem exists_coplanarStress_fourPointLine (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2, 3]])) :
    ∃ (stress : Fin 6 → ℝ) (probe : Fin 3 → ℝ), stress ≠ 0 ∧ probe ≠ 0
      ∧ (∑ c, stress c • atomMatrix (design.atom c)) = 0
      ∧ ∀ c, stress c ≠ 0 → design.atom c ⬝ᵥ probe = 0 :=
  exists_coplanarStress_of_fourPointLine (by decide) patternForcesStress_fourPointLine
    (by intro label hlabel hfirst hsecond
        revert hlabel hfirst hsecond
        fin_cases label <;> decide)
    (by decide) (by decide) design hpattern

/-- Entry `[[0,1,2,3],[0,4,5]]` meets branch (iii) at every design. -/
theorem exists_coplanarStress_fourPointLineWithThreePointLine (design : WeightedDesign 6 3)
    (hpattern :
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2, 3], [0, 4, 5]])) :
    ∃ (stress : Fin 6 → ℝ) (probe : Fin 3 → ℝ), stress ≠ 0 ∧ probe ≠ 0
      ∧ (∑ c, stress c • atomMatrix (design.atom c)) = 0
      ∧ ∀ c, stress c ≠ 0 → design.atom c ⬝ᵥ probe = 0 :=
  exists_coplanarStress_of_fourPointLine (by decide)
    patternForcesStress_fourPointLineWithThreePointLine
    (by intro label hlabel hfirst hsecond
        revert hlabel hfirst hsecond
        fin_cases label <;> decide)
    (by decide) (by decide) design hpattern

/-! ## Branch (iii) is empty when every line is short

A stress with coplanar support forces four atoms onto a plane, hence four
labels pairwise dependent.  A pattern whose lines all carry three points admits
no such quadruple, so every one of its stresses has FULL SUPPORT. -/

/-- Every nonzero stress of every design on the stratum has full support —
equivalently, the stratum never meets branch (iii) of the trichotomy. -/
def StratumStressHasFullSupport (pattern : LinePattern 6) : Prop :=
  ∀ design : WeightedDesign 6 3, HasLinePattern design pattern →
    ∀ stress : Fin 6 → ℝ, stress ≠ 0 →
      (∑ c, stress c • atomMatrix (design.atom c)) = 0 → ∀ c, stress c ≠ 0

/-- **NO SHORT-LINE PATTERN MEETS BRANCH (iii).**  A coplanar-support stress
leaves at most two atoms off the plane (`Gtz.sixThree_offPlaneCard_le_two_of_coplanarStress`),
so at least four labels pair to zero against the probe; any distinct triple of
those has vanishing bracket and is therefore in the pattern, contradicting the
quadruple-free condition. -/
theorem stratumStressHasFullSupport_of_noCoplanarQuadruple {pattern : LinePattern 6}
    (hforbids : PatternForbidsParallelPair pattern)
    (hnoQuadruple : PatternHasNoCoplanarQuadruple pattern) :
    StratumStressHasFullSupport pattern := by
  classical
  intro design hpattern stress hstressNe hstress
  have hprimitive := isPrimitiveDesign_of_hasLinePattern hforbids design hpattern
  rcases stress_fullSupport_or_orthogonalProbe (by norm_num) design.atom hstress with
    hfull | ⟨probe, hprobeNe, hprobeOrth⟩
  · exact hfull
  · exfalso
    have hcardLe := sixThree_offPlaneCard_le_two_of_coplanarStress design hstressNe hprobeNe
      hstress hprobeOrth hprimitive
    set offPlaneSet := Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0
      with hoffPlaneDef
    have hplaneCard : 4 ≤ offPlaneSetᶜ.card := by
      have hcompl : offPlaneSetᶜ.card = 6 - offPlaneSet.card := by
        rw [Finset.card_compl, Fintype.card_fin]
      omega
    have hplaneMem : ∀ label ∈ offPlaneSetᶜ, design.atom label ⬝ᵥ probe = 0 := by
      intro label hlabel
      by_contra hne
      exact (Finset.mem_compl.mp hlabel) (Finset.mem_filter.mpr ⟨Finset.mem_univ label, hne⟩)
    obtain ⟨leftLabel, hleftMem, midLabel, hmidMem, rightLabel, hrightMem,
      hleftMid, hleftRight, hmidRight, hfree⟩ := hnoQuadruple offPlaneSetᶜ hplaneCard
    exact hfree ((hpattern leftLabel midLabel rightLabel hleftMid hleftRight hmidRight).mp
      (tripleBracket_eq_zero_of_forall_dotProduct_eq_zero (design.atom leftLabel)
        (design.atom midLabel) (design.atom rightLabel) probe hprobeNe
        (hplaneMem leftLabel hleftMem) (hplaneMem midLabel hmidMem)
        (hplaneMem rightLabel hrightMem)))

/-! ## Branch (i): the stress-free entries

Multiplying a stress by the normal of a three-point line annihilates the three
on-line terms and exhibits the other three labels as a dependent triple.  A
pattern whose three-point line has an INDEPENDENT complementary triple therefore
carries no stress at all. -/

/-- A nontrivial linear dependence kills the bracket.  The scaled bracket is the
cofactor combination of the dependence's three coordinates. -/
theorem tripleBracket_eq_zero_of_dependency {leftVec midVec rightVec : Fin 3 → ℝ}
    {leftScale midScale rightScale : ℝ} (hleftScaleNe : leftScale ≠ 0)
    (hdependency : leftScale • leftVec + midScale • midVec + rightScale • rightVec = 0) :
    tripleBracket leftVec midVec rightVec = 0 := by
  have hcoordinate : ∀ index : Fin 3,
      leftScale * leftVec index + midScale * midVec index + rightScale * rightVec index = 0 := by
    intro index
    have hentry := congrFun hdependency index
    simpa using hentry
  have hzeroth := hcoordinate 0
  have hfirst := hcoordinate 1
  have hsecond := hcoordinate 2
  rw [tripleBracket_eq]
  have hscaled : leftScale * (leftVec 0 * (midVec 1 * rightVec 2 - midVec 2 * rightVec 1)
      - leftVec 1 * (midVec 0 * rightVec 2 - midVec 2 * rightVec 0)
      + leftVec 2 * (midVec 0 * rightVec 1 - midVec 1 * rightVec 0)) = 0 := by
    linear_combination (midVec 1 * rightVec 2 - midVec 2 * rightVec 1) * hzeroth
      - (midVec 0 * rightVec 2 - midVec 2 * rightVec 0) * hfirst
      + (midVec 0 * rightVec 1 - midVec 1 * rightVec 0) * hsecond
  exact (mul_eq_zero.mp hscaled).resolve_left hleftScaleNe

/-- Every stress of every design on the stratum is zero — the six atoms are a
basis of the symmetric three-by-three matrices, so the stratum lies entirely
inside branch (i) of the trichotomy. -/
def StratumIsStressFree (pattern : LinePattern 6) : Prop :=
  ∀ design : WeightedDesign 6 3, HasLinePattern design pattern →
    ∀ stress : Fin 6 → ℝ, (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0

/-- **THE LINE-PAIR LAW IN STRESS FORM.**  If `{0,1,2}` is a line, the other
three labels are off its plane, and `{3,4,5}` is NOT a line, the stratum carries
no stress.  This is a conic through six points with three collinear being forced
to split into that line and a second one carrying the other three. -/
theorem stratumIsStressFree_of_shortLine_of_independentComplement {pattern : LinePattern 6}
    (hforbids : PatternForbidsParallelPair pattern)
    (hnoQuadruple : PatternHasNoCoplanarQuadruple pattern)
    (hline : pattern 0 1 2) (hoffThird : ¬ pattern 0 1 3) (hcomplementFree : ¬ pattern 3 4 5) :
    StratumIsStressFree pattern := by
  classical
  intro design hpattern stress hstress
  by_contra hstressNe
  have hfull := stratumStressHasFullSupport_of_noCoplanarQuadruple hforbids hnoQuadruple
    design hpattern stress hstressNe hstress
  have hlineClosure : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      label ≠ 0 → label ≠ 1 → pattern 0 1 label := by
    intro label hlabel hfirst hsecond
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with rfl | rfl | rfl
    · exact absurd rfl hfirst
    · exact absurd rfl hsecond
    · exact hline
  obtain ⟨normalVec, hnormalNe, hcoplanar⟩ :=
    exists_lineNormal_of_hasLinePattern design hpattern ({0, 1, 2} : Finset (Fin 6))
      0 1 3 (by decide) (by decide) (by decide) hoffThird hlineClosure
  -- the three off-line atoms pair nontrivially with the normal
  have hoffPlane : ∀ offLabel : Fin 6, ¬ pattern 0 1 offLabel → (0 : Fin 6) ≠ offLabel →
      (1 : Fin 6) ≠ offLabel → design.atom offLabel ⬝ᵥ normalVec ≠ 0 := by
    intro offLabel hoffFree hzeroth hfirst hpairing
    exact hoffFree ((hpattern 0 1 offLabel (by decide) hzeroth hfirst).mp
      (tripleBracket_eq_zero_of_forall_dotProduct_eq_zero (design.atom 0) (design.atom 1)
        (design.atom offLabel) normalVec hnormalNe (hcoplanar 0 (by decide))
        (hcoplanar 1 (by decide)) hpairing))
  -- multiply the stress by the normal
  have hmultiplied : ∑ c, (stress c * (design.atom c ⬝ᵥ normalVec)) • design.atom c = 0 := by
    have hstep := congrArg (fun gramSum => gramSum *ᵥ normalVec) hstress
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq,
      smul_smul, Matrix.zero_mulVec] at hstep
    exact hstep
  rw [Fin.sum_univ_six] at hmultiplied
  rw [hcoplanar 0 (by decide), hcoplanar 1 (by decide), hcoplanar 2 (by decide)] at hmultiplied
  simp only [mul_zero, zero_smul, zero_add] at hmultiplied
  have hdependency : (stress 3 * (design.atom 3 ⬝ᵥ normalVec)) • design.atom 3
      + (stress 4 * (design.atom 4 ⬝ᵥ normalVec)) • design.atom 4
      + (stress 5 * (design.atom 5 ⬝ᵥ normalVec)) • design.atom 5 = 0 := hmultiplied
  have hthirdNe : stress 3 * (design.atom 3 ⬝ᵥ normalVec) ≠ 0 :=
    mul_ne_zero (hfull 3) (hoffPlane 3 hoffThird (by decide) (by decide))
  exact hcomplementFree ((hpattern 3 4 5 (by decide) (by decide) (by decide)).mp
    (tripleBracket_eq_zero_of_dependency hthirdNe hdependency))

/-! ## The four stress-free entries -/

/-- **ENTRY `[[0,1,2]]`, one three-point line: STRESS-FREE.** -/
theorem stratumIsStressFree_oneThreePointLine :
    StratumIsStressFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  stratumIsStressFree_of_shortLine_of_independentComplement (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **ENTRY `[[0,1,2],[0,3,4]]`, two three-point lines meeting: STRESS-FREE.** -/
theorem stratumIsStressFree_twoMeetingLines :
    StratumIsStressFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  stratumIsStressFree_of_shortLine_of_independentComplement (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **ENTRY `[[0,1,2],[0,3,4],[1,3,5]]`, three three-point lines: STRESS-FREE.** -/
theorem stratumIsStressFree_threeLines :
    StratumIsStressFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]]) :=
  stratumIsStressFree_of_shortLine_of_independentComplement (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- **ENTRY `M(K4)`, the four triangles of the complete graph on four vertices:
STRESS-FREE.**  The sharpest of the nine six-point classes lies entirely in the
stress-free branch, so every stress-based narrowing is vacuous on it. -/
theorem stratumIsStressFree_graphicKFour :
    StratumIsStressFree
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]) :=
  stratumIsStressFree_of_shortLine_of_independentComplement (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- The four stress-free entries make `Gtz.HasOnlyBalancedStress` vacuously
true, so the balanced-stress narrowing carries no information there. -/
theorem hasOnlyBalancedStress_of_stratumIsStressFree {pattern : LinePattern 6}
    (hstressFree : StratumIsStressFree pattern) (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design pattern) : HasOnlyBalancedStress design :=
  fun stress hstressNe hstress => absurd (hstressFree design hpattern stress hstress) hstressNe

/-! ## The two entries that never meet branch (iii) but may carry a stress -/

/-- **ENTRY `[]`, the line-free stratum `U(3,6)`: never branch (iii).**  With no
dependent triple at all there is certainly no coplanar quadruple, so every
stress has full support.  Both remaining branches occur: the six points lie on a
smooth conic exactly on a codimension-one sublocus. -/
theorem stratumStressHasFullSupport_lineFree :
    StratumStressHasFullSupport (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  stratumStressHasFullSupport_of_noCoplanarQuadruple (by decide) (by decide)

/-- **ENTRY `[[0,1,2],[3,4,5]]`, two disjoint three-point lines: never branch
(iii).** -/
theorem stratumStressHasFullSupport_twoDisjointLines :
    StratumStressHasFullSupport (lineFamilyPattern [[(0 : Fin 6), 1, 2], [3, 4, 5]]) :=
  stratumStressHasFullSupport_of_noCoplanarQuadruple (by decide) (by decide)

/-- **ENTRY `[[0,1,2],[3,4,5]]` LIES ENTIRELY IN BRANCH (ii).**  Its two lines
are a line-pair conic through all six points, so
`Gtz.patternForcesStress_twoDisjointLines` supplies a stress, and the coplanar
exclusion makes it full support. -/
theorem exists_fullSupport_stress_twoDisjointLines (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2], [3, 4, 5]])) :
    ∃ stress : Fin 6 → ℝ, (∀ c, stress c ≠ 0)
      ∧ (∑ c, stress c • atomMatrix (design.atom c)) = 0 := by
  obtain ⟨stress, hstressNe, hstress⟩ := patternForcesStress_twoDisjointLines design hpattern
  exact ⟨stress, stratumStressHasFullSupport_twoDisjointLines design hpattern stress hstressNe
    hstress, hstress⟩

/-- The branch-(ii) data of the trichotomy, exhibited on the two-disjoint-lines
entry: a full-support stress splitting three against three by sign, with a
positive definite middle matrix presenting the two sides as one form. -/
theorem twoDisjointLines_meets_balancedStratum (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2], [3, 4, 5]])) :
    ∃ stress : Fin 6 → ℝ,
      (∑ c, stress c • atomMatrix (design.atom c)) = 0
      ∧ (∀ c, stress c ≠ 0)
      ∧ (Finset.univ.filter fun c => 0 < stress c).card = 3
      ∧ (Finset.univ.filter fun c => stress c < 0).card = 3
      ∧ (∑ c ∈ Finset.univ.filter (fun c => 0 < stress c),
          stress c • atomMatrix (design.atom c)).PosDef
      ∧ ∑ c ∈ Finset.univ.filter (fun c => 0 < stress c),
          stress c • atomMatrix (design.atom c)
        = ∑ c ∈ Finset.univ.filter (fun c => stress c < 0),
            (-stress c) • atomMatrix (design.atom c) := by
  classical
  obtain ⟨stress, hfull, hstress⟩ := exists_fullSupport_stress_twoDisjointLines design hpattern
  have hspan : ∀ probe : Fin 3 → ℝ, (∀ c, design.atom c ⬝ᵥ probe = 0) → probe = 0 :=
    fun probe hprobe => weightedDesign_atoms_span design hprobe
  obtain ⟨hpositiveCard, hnegativeCard⟩ :=
    sixThree_fullSupport_stress_splits_three_three design.atom hspan hstress hfull
  exact ⟨stress, hstress, hfull, hpositiveCard, hnegativeCard,
    posDef_posSide_sum design.atom hspan hstress hfull,
    posSide_sum_eq_negSide_sum design.atom hstress hfull⟩

/-! ## Branch (ii)'s capstone, quoted

The balanced-stratum lane's `Gtz.sixThree_hasParallelPair_of_isTie_of_balancedStress`
is the branch-(ii) sibling of `Gtz.sixThree_hasParallelPair_of_isTie_of_coplanarStress`,
and its own residual is the positively phrased `BalancedStratumSelection 6`.
Quoting its conclusion as a hypothesis keeps this file importable against the
tree alone; the hypothesis is discharged by one application of that theorem and
is NOT proposed here as a residual of its own.  Read as a residual it would be
worthless, since a tie satisfies every negative clause and the obligation would
collapse onto the hinge itself. -/

/-- The branch-(ii) capstone's conclusion, as a hypothesis: a `(6,3)` tie
carrying a FULL-SUPPORT stress has a parallel pair. -/
def BalancedStratumCapstone : Prop :=
  ∀ design : WeightedDesign 6 3, IsTie design →
    ∀ stress : Fin 6 → ℝ, (∑ c, stress c • atomMatrix (design.atom c)) = 0 →
      (∀ c, stress c ≠ 0) → HasParallelPair design

/-- **A PATTERN THAT FORCES A STRESS AND FORBIDS A COPLANAR QUADRUPLE IS
TIE-FREE**, modulo the branch-(ii) capstone.  The forced stress cannot have
coplanar support, so it has full support, so the capstone fires; the pattern
then forbids the parallel pair it produces. -/
theorem stratumIsTieFree_of_forcedStress_of_balancedCapstone
    (hbalanced : BalancedStratumCapstone) {pattern : LinePattern 6}
    (hforbids : PatternForbidsParallelPair pattern)
    (hnoQuadruple : PatternHasNoCoplanarQuadruple pattern)
    (hforces : PatternForcesStress pattern) :
    StratumIsTieFree pattern := by
  intro design hpattern htie
  obtain ⟨stress, hstressNe, hstress⟩ := hforces design hpattern
  have hfull := stratumStressHasFullSupport_of_noCoplanarQuadruple hforbids hnoQuadruple
    design hpattern stress hstressNe hstress
  exact (isPrimitiveDesign_iff_not_hasParallelPair design).mp
    (isPrimitiveDesign_of_hasLinePattern hforbids design hpattern)
    (hbalanced design htie stress hstress hfull)

/-- **ENTRY `[[0,1,2],[3,4,5]]`, two disjoint three-point lines: TIE-FREE**,
modulo the branch-(ii) capstone.  Its two lines are a line-pair conic through
all six points, so every design of the stratum carries a stress, and no design
of it carries a coplanar one. -/
theorem stratumIsTieFree_twoDisjointLines_of_balancedCapstone
    (hbalanced : BalancedStratumCapstone) :
    StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [3, 4, 5]]) :=
  stratumIsTieFree_of_forcedStress_of_balancedCapstone hbalanced (by decide) (by decide)
    patternForcesStress_twoDisjointLines

/-! ## The whole residual is the stress-free stratum

With both branch capstones in hand the line-pattern enumeration is no longer
needed at all: the trichotomy alone reduces the hinge to its branch-(i) arm. -/

/-- The hinge asked only of designs whose six atoms are a BASIS of the symmetric
three-by-three matrices.  This is branch (i) of `Gtz.sixThree_stress_trichotomy`
and the only arm of it with no capstone.  It is a restriction of the hinge, not
a certificate residual: every certificate of strict domination fails at a tie,
so no relaxation can close it and it has to be attacked as tie-emptiness on the
stress-free stratum. -/
def StressFreeHingeHoldsSixThree : Prop :=
  ∀ design : WeightedDesign 6 3,
    (∀ stress : Fin 6 → ℝ,
      (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0) →
      IsTie design → HasParallelPair design

/-- **A STRESS-FREE DESIGN HAS NO PARALLEL PAIR.**  A parallel pair manufactures
a stress on the nose: put `1` at the duplicate and `-ratio ^ 2` at the original.
So branch (i) of the trichotomy consists entirely of primitive designs. -/
theorem isPrimitiveDesign_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : ∀ stress : Fin 6 → ℝ,
      (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0) :
    IsPrimitiveDesign design := by
  classical
  intro keptLabel dropLabel ratio hdistinct hparallel
  set stress : Fin 6 → ℝ := fun c =>
    (if c = dropLabel then (1 : ℝ) else 0) - (if c = keptLabel then ratio ^ 2 else 0)
    with hstressDef
  have hstressParseval : (∑ c, stress c • atomMatrix (design.atom c)) = 0 := by
    have hdrop : atomMatrix (design.atom dropLabel)
        = ratio ^ 2 • atomMatrix (design.atom keptLabel) := by
      rw [hparallel, atomMatrix_smul]
    have hpointwise : ∀ c, stress c • atomMatrix (design.atom c)
        = (if c = dropLabel then (1 : ℝ) else 0) • atomMatrix (design.atom c)
          - (if c = keptLabel then ratio ^ 2 else 0) • atomMatrix (design.atom c) := by
      intro c
      rw [hstressDef, sub_smul]
    rw [Finset.sum_congr rfl fun c _ => hpointwise c, Finset.sum_sub_distrib]
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_pos]
    rw [hdrop, one_smul, sub_self]
  have hzero := hstressFree stress hstressParseval
  have hentry : stress dropLabel = 0 := congrFun hzero dropLabel
  rw [hstressDef] at hentry
  simp only [if_neg (Ne.symm hdistinct)] at hentry
  norm_num at hentry

/-- **THE STRESS-FREE RESIDUAL IS A TIE-EMPTINESS STATEMENT.**  On branch (i) a
parallel pair is impossible, so the hinge's conclusion there is unreachable and
the obligation is exactly "no design whose atoms are a basis of `Sym(3)` is a
tie".  That is the shape the arm has to be attacked in; there is no weaker
certificate reading of it, because every strict-domination certificate fails at
a tie by definition. -/
theorem stressFreeHingeHoldsSixThree_iff_no_stressFree_tie :
    StressFreeHingeHoldsSixThree ↔
      ∀ design : WeightedDesign 6 3,
        (∀ stress : Fin 6 → ℝ,
          (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0) →
          ¬ IsTie design := by
  constructor
  · intro hhinge design hstressFree htie
    exact (isPrimitiveDesign_iff_not_hasParallelPair design).mp
      (isPrimitiveDesign_of_stressFree design hstressFree)
      (hhinge design hstressFree htie)
  · intro hempty design hstressFree htie
    exact absurd htie (hempty design hstressFree)

/-- **THE HINGE AT SIX POINTS REDUCES TO THE STRESS-FREE STRATUM.**  Branch
(iii) goes to `Gtz.sixThree_hasParallelPair_of_isTie_of_coplanarStress`, branch
(ii) to the balanced capstone, and branch (i) is what is left.  No line pattern,
no enumeration, no ledger. -/
theorem hingeHoldsAtSize_sixThree_of_stressFreeHinge
    (hselection : TwoPoleStratumSelection 6) (hbalanced : BalancedStratumCapstone)
    (hstressFreeHinge : StressFreeHingeHoldsSixThree) : HingeHoldsAtSize 6 3 := by
  intro design htie
  rcases sixThree_stress_trichotomy design with
    hindependent | ⟨stress, hstress, hfull, _, _, _, _⟩
      | ⟨stress, probe, hstressNe, hprobeNe, hstress, hcoplanarSupport⟩
  · exact hstressFreeHinge design hindependent htie
  · exact hbalanced design htie stress hstress hfull
  · exact sixThree_hasParallelPair_of_isTie_of_coplanarStress hselection design htie
      hstressNe hprobeNe hstress hcoplanarSupport

/-! ## No parallel-pair design sits on any ledger stratum

The tree's certified `(6,3)` ties all carry a repeated direction, and a repeated
direction makes every triple through it dependent — which no entry of
`Gtz.lineFamiliesSix` allows.  So the known ties are outside the ledger, and the
eight obligations are not refuted by any of them. -/

/-- A design with a parallel pair realizes no pattern that forbids one. -/
theorem not_hasLinePattern_of_hasParallelPair {size : ℕ} {pattern : LinePattern size}
    (hforbids : PatternForbidsParallelPair pattern) (design : WeightedDesign size 3)
    (hpair : HasParallelPair design) : ¬ HasLinePattern design pattern :=
  fun hpattern => (isPrimitiveDesign_iff_not_hasParallelPair design).mp
    (isPrimitiveDesign_of_hasLinePattern hforbids design hpattern) hpair

/-- Every entry of the six-point catalogue forbids a parallel pair. -/
theorem forall_patternForbidsParallelPair_lineFamiliesSix :
    ∀ lines ∈ lineFamiliesSix, PatternForbidsParallelPair (lineFamilyPattern lines) := by
  decide

/-- **THE SPLIT-TETRAHEDRON TIE IS ON NO LEDGER STRATUM.**  It is the tree's
two-parameter family of certified `(6,3)` ties, and its directions `2` and `3`
coincide, so it realizes none of the nine catalogued patterns.  The eight open
obligations are therefore not refuted by the only ties currently known at this
size. -/
theorem not_hasLinePattern_splitTetraDesign (splitA splitB : ℝ) (hAPos : 0 < splitA)
    (hALt : splitA < 1 / 4) (hBPos : 0 < splitB) (hBLt : splitB < 1 / 4)
    (lines : List (List (Fin 6))) (hlines : lines ∈ lineFamiliesSix) :
    ¬ HasLinePattern (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt)
      (lineFamilyPattern lines) :=
  not_hasLinePattern_of_hasParallelPair
    (forall_patternForbidsParallelPair_lineFamiliesSix lines hlines) _
    (splitTetraDesign_hasParallelPair splitA splitB hAPos hALt hBPos hBLt)

/-! ## The residual along the ledger route

`Gtz.hingeHoldsAtSize_sixThree_of_balancedStressResidual` asks for eight
obligations.  Five remain. -/

/-- **THE HINGE AT SIX POINTS FROM FIVE ENTRIES.**  The two entries with a
four-point line are discharged from `Gtz.TwoPoleStratumSelection 6` and the
two-disjoint-lines entry from the branch-(ii) capstone; the five named
hypotheses are the rest of the ledger, each still allowed to assume heaviness
and balanced stress.  All five are STRESS-FREE strata, so that second narrowing
is vacuous on every one of them. -/
theorem hingeHoldsAtSize_sixThree_of_fiveStressFreeEntries
    (hselection : TwoPoleStratumSelection 6) (hbalanced : BalancedStratumCapstone)
    (hlineFree : StratumIsTieFreeAmongHeavyAtBalancedStress
      (lineFamilyPattern ([] : List (List (Fin 6)))))
    (honeThreePointLine : StratumIsTieFreeAmongHeavyAtBalancedStress
      (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (htwoMeetingLines : StratumIsTieFreeAmongHeavyAtBalancedStress
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (hthreeLines : StratumIsTieFreeAmongHeavyAtBalancedStress
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]]))
    (hgraphicKFour : StratumIsTieFreeAmongHeavyAtBalancedStress
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]])) :
    HingeHoldsAtSize 6 3 := by
  refine hingeHoldsAtSize_sixThree_of_balancedStressResidual ?_
  intro lines hlines hnotNearPencil
  simp only [lineFamiliesSix, List.mem_cons, List.not_mem_nil, or_false] at hlines
  rcases hlines with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hlineFree
  · exact honeThreePointLine
  · exact fun design hpattern _ _ =>
      stratumIsTieFree_twoDisjointLines_of_balancedCapstone hbalanced design hpattern
  · exact htwoMeetingLines
  · exact hthreeLines
  · exact hgraphicKFour
  · exact fun design hpattern _ _ =>
      stratumIsTieFree_fourPointLine_of_selection hselection design hpattern
  · exact fun design hpattern _ _ =>
      stratumIsTieFree_fourPointLineWithThreePointLine_of_selection hselection design hpattern
  · exact absurd (by decide) hnotNearPencil

/-- **THE 1997 CONJECTURE AT RANK THREE, FROM SIX ENTRIES AND ONE SELECTION
RULE.**  Composing the hinge with `Gtz.gtzWeighted_six_three_of_hinge` and
`Gtz.gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three`: every real
`n`-by-three matrix with orthonormal columns has a three-row submatrix of
smallest singular value at least `1/sqrt n`, as soon as the six short-line
ledger entries and the two-pole selection rule hold.  Nothing else is
assumed. -/
theorem forall_gtzOriginal_rank_three_of_stressFreeHinge
    (hselection : TwoPoleStratumSelection 6) (hbalanced : BalancedStratumCapstone)
    (hstressFreeHinge : StressFreeHingeHoldsSixThree) :
    ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three.mp
    (gtzWeighted_six_three_of_hinge
      (hingeHoldsAtSize_sixThree_of_stressFreeHinge hselection hbalanced hstressFreeHinge))


/-! ## Composition against the balanced-stratum lane -/

theorem balancedStratumCapstone_of_balancedStratumSelection
    (hselection : BalancedStratumSelection 6) : BalancedStratumCapstone :=
  fun design htie _ hstress hfull =>
    sixThree_hasParallelPair_of_isTie_of_balancedStress hselection design htie hstress hfull

theorem stratumIsTieFree_twoDisjointLines_of_balancedSelection
    (hselection : BalancedStratumSelection 6) :
    StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [3, 4, 5]]) :=
  stratumIsTieFree_twoDisjointLines_of_balancedCapstone
    (balancedStratumCapstone_of_balancedStratumSelection hselection)

theorem forall_gtzOriginal_rank_three_of_twoSelections_and_stressFreeHinge
    (hTwoPole : TwoPoleStratumSelection 6) (hBalanced : BalancedStratumSelection 6)
    (hstressFreeHinge : StressFreeHingeHoldsSixThree) :
    ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  forall_gtzOriginal_rank_three_of_stressFreeHinge hTwoPole
    (balancedStratumCapstone_of_balancedStratumSelection hBalanced) hstressFreeHinge


end Gtz
