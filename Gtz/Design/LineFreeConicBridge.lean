import Gtz.Core.Basic
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.LinePatternEnumeration
import Gtz.Certificates.ResidueDissolution
import Gtz.Reduction.StressConditionalWalk
import Gtz.Design.StressFreeStratum
import Gtz.Design.StressFreeMatroidStratification
import Gtz.Design.RigidityBridge
import Gtz.LinAlg.ProjectionForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The `U(3,6)` conic bridge: formulation, sample point, clearance functionals

The line-free class `Gtz.StressFreeStratumIsTieFree (Gtz.lineFamilyPattern [])`
is the single MIXED class of the `(6,3)` stratification: uniquely among the
five residual classes its stress-freeness hypothesis carves out a genuine
sublocus — the codimension-one conic locus.  This file lands the three
unconditional layers of the two-family attack on that class.

## Layer 1: the conic formulation

`Gtz.HasNoCommonQuadric` names the off-conic condition; the two bridges
`Gtz.hasNoCommonQuadric_of_stressFree` / `Gtz.not_stressFree_of_commonQuadric`
pin STRESS-FREE = OFF-CONIC on every `(6,3)` design (both directions from the
shipped `Gtz.exists_stress_of_commonQuadric`, sharpened to an `Iff` and to the
Veronese determinant by the shipped `Gtz.stressFree_iff_no_conic_sixThree` and
`Gtz.stressFree_iff_veroneseGrid_det_ne_zero`).  The attack Prop
`Gtz.LineFreeOffConicWeakToStrict` KEEPS the weak-domination antecedent — on
this class the antecedent is load-bearing: the per-direction-tuple margin
infimum over masses and weights is zero at EVERY tuple (mass-collapse cascade),
so no antecedent-free strict-triple form can hold.
`Gtz.stressFreeStratumIsTieFree_lineFree_of_weakToStrict` closes the class
obligation from the attack Prop verbatim, and
`Gtz.lineFreeOffConicWeakToStrict_of_twoFamilies` assembles the attack Prop
from an interior margin floor plus a boundary collar exclusion over any
clearance functional.

## Layer 2: the rational sample point

`Gtz.icosaApproximantDirection` is the denominator-bounded rational icosahedron
approximant (short entry `662/727`, long entry `249/169` — the
`limit_denominator 1000` convergents of the icosahedral coordinates
`sqrt((3 - 3*sqrt 5/5)/2)` and `sqrt((3 + 3*sqrt 5/5)/2)`).  It is EXACTLY
line-free (`Gtz.tripleBracket_icosaApproximantDirection_ne_zero`), exactly
stress-free hence off-conic
(`Gtz.hasNoCommonQuadric_icosaApproximantDirection`), and at the uniform chart
point `Gtz.icosaApproximantChartPoint` (mass `1`, weight `1/6`) the triple
`{0, 4, 5}` is strictly dominating (`Gtz.icosaApproximant_gap_posDef`) by an
all-integer sum-of-squares certificate with the identity floor `3` — the
interior family's non-vacuity seed, fully rational, no square root anywhere.

## Layer 3: the clearance functionals

The scan behind this file adjudicated 767 exact-rational chart points: ties 0,
weak-not-strict triples 0, and the structural finding that clearance MUST read
the masses — direction-only clearance admits no positive floor.  Accordingly
`Gtz.wallClearanceOf` reads the design masses `m_c = w_c * |g_c|^2`
(`Gtz.designMassOf`), the six-by-six Veronese conic discriminant
(`Gtz.conicClearanceOf` through the shipped `Gtz.veroneseGrid`), and the
minimal squared triple bracket (`Gtz.bracketClearanceOf`) — all polynomial in
the design data, selector-free.  Trace normalization is Parseval itself:
`Gtz.sum_designMassOf_eq_three`.  Each functional is strictly positive exactly
on the open stratum the two-family split works over
(`Gtz.wallClearanceOf_pos`).
-/

namespace Gtz

open Matrix

/-! ## Layer 1: the conic formulation of the line-free obligation -/

/-- The six atoms, read as points of the projective plane, lie on NO conic: the
only symmetric `3x3` form annihilating every atom's quadratic form is zero.
This names the hypothesis triple of `Gtz.exists_stress_of_commonQuadric` and
the conclusion shape of `Gtz.stressFree_iff_no_conic_sixThree`. -/
def HasNoCommonQuadric (atoms : Fin 6 → (Fin 3 → ℝ)) : Prop :=
  ∀ form : Matrix (Fin 3) (Fin 3) ℝ, formᵀ = form →
    (∀ atomIndex, atoms atomIndex ⬝ᵥ (form *ᵥ atoms atomIndex) = 0) → form = 0

/-- A design is stress-free: the only linear dependency among its six atom
matrices is trivial.  This is verbatim the antecedent shape of
`Gtz.StressFreeStratumIsTieFree`. -/
def IsStressFreeDesign (design : WeightedDesign 6 3) : Prop :=
  ∀ stress : Fin 6 → ℝ, (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0

/-- **STRESS-FREE FORCES OFF-CONIC.**  A common conic would manufacture a
nonzero stress by `Gtz.exists_stress_of_commonQuadric`; stress-freeness forbids
it. -/
theorem hasNoCommonQuadric_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) :
    HasNoCommonQuadric design.atom := by
  intro form hsymmetric hquadric
  by_contra hnonzero
  obtain ⟨stress, hstressNe, hstress⟩ :=
    exists_stress_of_commonQuadric design.atom hsymmetric hnonzero hquadric
  exact hstressNe (hstressFree stress hstress)

/-- **ON-CONIC KILLS STRESS-FREENESS.**  The converse direction: six directions
on a common conic carry a nonzero stress, so the design is not stress-free.
Together with `Gtz.hasNoCommonQuadric_of_stressFree` this pins, on EVERY
stratum, stress-free `<=>` off-conic — the mixed-class geometry of `U(3,6)`. -/
theorem not_stressFree_of_commonQuadric (design : WeightedDesign 6 3)
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form) (hnonzero : form ≠ 0)
    (hquadric : ∀ atomIndex, design.atom atomIndex ⬝ᵥ (form *ᵥ design.atom atomIndex) = 0) :
    ¬ IsStressFreeDesign design := by
  intro hstressFree
  obtain ⟨stress, hstressNe, hstress⟩ :=
    exists_stress_of_commonQuadric design.atom hsymmetric hnonzero hquadric
  exact hstressNe (hstressFree stress hstress)

/-- The two bridges as one `Iff`, through the shipped left-right kernel duality
of the Veronese grid. -/
theorem isStressFreeDesign_iff_hasNoCommonQuadric (design : WeightedDesign 6 3) :
    IsStressFreeDesign design ↔ HasNoCommonQuadric design.atom :=
  stressFree_iff_no_conic_sixThree design.atom

/-- **OFF-CONIC IS ONE DETERMINANT.**  The named predicate is the nonvanishing
of the six-by-six Veronese determinant — the exact-rational membership test of
the open stratum, and the well-definedness fact behind
`Gtz.conicClearanceOf`. -/
theorem hasNoCommonQuadric_iff_veroneseGrid_det_ne_zero (atoms : Fin 6 → (Fin 3 → ℝ)) :
    HasNoCommonQuadric atoms ↔ (veroneseGrid atoms).det ≠ 0 :=
  (stressFree_iff_no_conic_sixThree atoms).symm.trans
    (stressFree_iff_veroneseGrid_det_ne_zero atoms)

/-- **THE `U(3,6)` ATTACK STATEMENT.**  On the line-free stratum, off every
conic, a weakly dominating triple forces a strictly dominating one.  This is
the design-level analogue of `Gtz.DirectionChartIsTieFree` with the directions
left free.  The `PosSemidef` antecedent is KEPT and is load-bearing at this
class: the fiber margin infimum over masses and weights is zero at every
direction tuple, so the antecedent-free strict-triple sibling is out of
reach. -/
def LineFreeOffConicWeakToStrict : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    (∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected) →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - 1).PosDef

/-- Relabelling the EMPTY line family is invisible: both patterns are the
everywhere-false predicate, so `Gtz.HasLinePattern` transports across it. -/
theorem hasLinePattern_lineFree_of_relabel (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6))
    (hpattern : HasLinePattern design (fun leftLabel midLabel rightLabel =>
      lineFamilyPattern ([] : List (List (Fin 6)))
        (relabel leftLabel) (relabel midLabel) (relabel rightLabel))) :
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  have hrelabelled := hpattern leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  simpa [lineFamilyPattern] using hrelabelled

/-- **THE REDUCTION.**  The attack Prop closes the `U(3,6)` obligation
verbatim: `Gtz.StressFreeStratumIsTieFree (Gtz.lineFamilyPattern [])` — the
exact statement of `Skeleton.obligationTieFreeUThreeSix`.  Stress-freeness is
converted to off-conic by the bridge; the tie's weak half feeds the attack
Prop's antecedent; the strict conclusion contradicts the tie's second half. -/
theorem stressFreeStratumIsTieFree_lineFree_of_weakToStrict
    (hattack : LineFreeOffConicWeakToStrict) :
    StressFreeStratumIsTieFree (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro design relabel hstressFree hpattern htie
  obtain ⟨⟨weakTriple, hweakCard, hweakDominates⟩, hnoStrict⟩ := htie
  obtain ⟨strictTriple, hstrictCard, hstrictGap⟩ :=
    hattack design
      (hasLinePattern_lineFree_of_relabel design relabel hpattern)
      (hasNoCommonQuadric_of_stressFree design hstressFree)
      ⟨weakTriple, hweakCard, hweakDominates⟩
  exact hnoStrict strictTriple hstrictCard hstrictGap

/-- Interior-family shape: away from the walls (all measured by one clearance
functional, no selector), some triple of the twenty is strictly dominating with
margin bounded below by an explicit positive function of the clearance. -/
def InteriorFamilyMarginFloor
    (wallClearance : WeightedDesign 6 3 → ℝ) (floorOf : ℝ → ℝ) : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    (∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected) →
    0 < wallClearance design →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - (1 + floorOf (wallClearance design) • 1)).PosSemidef

/-- Boundary-collar shape: inside the collar a hypothetical tie compactifies
onto an excluded boundary object, so the collar contains no tie at all. -/
def BoundaryCollarExcludesTies (wallClearance : WeightedDesign 6 3 → ℝ)
    (collarWidth : ℝ) : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    wallClearance design ≤ collarWidth →
    ¬ IsTie design

/-- **THE TWO-FAMILY ASSEMBLY.**  The two families assemble to the attack
Prop's conclusion shape, hence (through the reduction above) to the
obligation: a tie is excluded in the collar, and outside the collar the
interior floor upgrades the tie's own weak triple to a strict one. -/
theorem lineFreeOffConicWeakToStrict_of_twoFamilies
    (wallClearance : WeightedDesign 6 3 → ℝ) (floorOf : ℝ → ℝ) (collarWidth : ℝ)
    (hinterior : InteriorFamilyMarginFloor wallClearance floorOf)
    (hfloorPos : ∀ clearance : ℝ, collarWidth < clearance → 0 < floorOf clearance)
    (hcollar : BoundaryCollarExcludesTies wallClearance collarWidth)
    (hcollarNonneg : 0 ≤ collarWidth) :
    ∀ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      ¬ IsTie design := by
  intro design hlineFree hoffConic htie
  rcases le_or_gt (wallClearance design) collarWidth with hinCollar | houtside
  · exact hcollar design hlineFree hoffConic hinCollar htie
  · obtain ⟨⟨weakTriple, hweakCard, hweakDominates⟩, hnoStrict⟩ := htie
    have hclearancePos : 0 < wallClearance design := lt_of_le_of_lt hcollarNonneg houtside
    obtain ⟨strictTriple, hstrictCard, hstrictFloor⟩ :=
      hinterior design hlineFree hoffConic ⟨weakTriple, hweakCard, hweakDominates⟩
        hclearancePos
    refine hnoStrict strictTriple hstrictCard ?_
    have hfloorPosHere : 0 < floorOf (wallClearance design) := hfloorPos _ houtside
    obtain ⟨hshiftedHerm, hshiftedForm⟩ :=
      Matrix.posSemidef_iff_dotProduct_mulVec.mp hstrictFloor
    have hsplit : subsetSum design strictTriple - 1
        = (subsetSum design strictTriple
            - (1 + floorOf (wallClearance design) • 1))
          + floorOf (wallClearance design) • 1 := by
      abel
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec hprobeNe => ?_⟩
    · refine isHermitian_of_transpose_eq ?_
      have hshiftedTranspose : (subsetSum design strictTriple
          - (1 + floorOf (wallClearance design) • 1))ᵀ
            = subsetSum design strictTriple
              - (1 + floorOf (wallClearance design) • 1) := hshiftedHerm.eq
      rw [hsplit, Matrix.transpose_add, hshiftedTranspose, Matrix.transpose_smul,
        Matrix.transpose_one]
    · have hexpand : probeVec ⬝ᵥ ((subsetSum design strictTriple - 1) *ᵥ probeVec)
          = probeVec ⬝ᵥ ((subsetSum design strictTriple
              - (1 + floorOf (wallClearance design) • 1)) *ᵥ probeVec)
            + floorOf (wallClearance design) * (probeVec ⬝ᵥ probeVec) := by
        rw [hsplit, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
          Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      have hnormPos : 0 < probeVec ⬝ᵥ probeVec := by
        obtain ⟨witnessIndex, hwitnessRaw⟩ := Function.ne_iff.mp hprobeNe
        have hwitness : probeVec witnessIndex ≠ 0 := by simpa using hwitnessRaw
        exact Finset.sum_pos' (fun index _ => mul_self_nonneg (probeVec index))
          ⟨witnessIndex, Finset.mem_univ _,
            lt_of_le_of_ne (mul_self_nonneg _)
              (Ne.symm (mul_ne_zero hwitness hwitness))⟩
      have hpsdPart := hshiftedForm probeVec
      rw [star_trivial] at hpsdPart
      have hfloorTerm : 0 < floorOf (wallClearance design) * (probeVec ⬝ᵥ probeVec) :=
        mul_pos hfloorPosHere hnormPos
      rw [star_trivial, hexpand]
      linarith

/-! ## Layer 2: the rational icosahedron approximant

The interior family's seed witness.  The six directions are the
`limit_denominator 1000` rational convergents of the icosahedral chart
directions of `Gtz.icosaDesign`: short entry `662/727`, long entry `249/169`.
Every statement below is decided by rational arithmetic — no square root
appears anywhere on this chart. -/

/-- The rational icosahedron approximant: the six icosahedral directions with
the irrational entries replaced by their denominator-`1000` convergents. -/
noncomputable def icosaApproximantDirection : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![662 / 727, 249 / 169, 0]
  | 1 => ![-(662 / 727), 249 / 169, 0]
  | 2 => ![0, 662 / 727, 249 / 169]
  | 3 => ![0, -(662 / 727), 249 / 169]
  | 4 => ![249 / 169, 0, 662 / 727]
  | 5 => ![249 / 169, 0, -(662 / 727)]

set_option maxHeartbeats 1600000 in
/-- **THE APPROXIMANT IS EXACTLY LINE-FREE**: every bracket of three distinct
labels is nonzero, so the tuple realizes the empty line family — the `U(3,6)`
stratum. -/
theorem tripleBracket_icosaApproximantDirection_ne_zero
    (leftLabel midLabel rightLabel : Fin 6) (hleftMid : leftLabel ≠ midLabel)
    (hleftRight : leftLabel ≠ rightLabel) (hmidRight : midLabel ≠ rightLabel) :
    tripleBracket (icosaApproximantDirection leftLabel)
      (icosaApproximantDirection midLabel)
      (icosaApproximantDirection rightLabel) ≠ 0 := by
  rcases fin_six_cases leftLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_six_cases midLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin_six_cases rightLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hleftMid
          | exact absurd rfl hleftRight
          | exact absurd rfl hmidRight
          | (simp [icosaApproximantDirection, tripleBracket_eq]; norm_num)

/-- **THE APPROXIMANT IS EXACTLY STRESS-FREE.**  The six-by-six stress system
decouples into three difference equations and a cyclic three-by-three block of
determinant `S^6 + L^6 > 0`; the certificate below is the exact inverse of that
system, one `linear_combination` per coordinate. -/
theorem icosaApproximantDirection_isStressFree :
    ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex
          • atomMatrix (icosaApproximantDirection atomIndex)) = 0 →
        stressCoeff = 0 := by
  intro stressCoeff hstress
  have hentry : ∀ rowIndex colIndex : Fin 3,
      ∑ atomIndex, stressCoeff atomIndex
          * (icosaApproximantDirection atomIndex rowIndex
            * icosaApproximantDirection atomIndex colIndex) = 0 := by
    intro rowIndex colIndex
    rw [← sum_smul_atomMatrix_apply icosaApproximantDirection stressCoeff rowIndex colIndex,
      hstress, Matrix.zero_apply]
  have haxisFirst := hentry 0 0
  have haxisSecond := hentry 1 1
  have haxisThird := hentry 2 2
  have hcrossTop := hentry 0 1
  have hcrossSide := hentry 0 2
  have hcrossBottom := hentry 1 2
  simp [icosaApproximantDirection, Fin.sum_univ_six] at haxisFirst haxisSecond haxisThird
  simp [icosaApproximantDirection, Fin.sum_univ_six] at hcrossTop hcrossSide hcrossBottom
  have hzeroth : stressCoeff 0 = 0 := by
    linear_combination
      (1182472396737778827026152573832 / 37149602734297142792294438788993 : ℝ) * haxisFirst +
      (16209785305436794250274884205729 / 74299205468594285584588877577986 : ℝ) * haxisSecond +
      (-3095773221727059444191701785042 / 37149602734297142792294438788993 : ℝ) * haxisThird +
      (122863 / 329676 : ℝ) * hcrossTop
  have hfirst : stressCoeff 1 = 0 := by
    linear_combination
      (1182472396737778827026152573832 / 37149602734297142792294438788993 : ℝ) * haxisFirst +
      (16209785305436794250274884205729 / 74299205468594285584588877577986 : ℝ) * haxisSecond +
      (-3095773221727059444191701785042 / 37149602734297142792294438788993 : ℝ) * haxisThird +
      (-(122863 / 329676) : ℝ) * hcrossTop
  have hsecond : stressCoeff 2 = 0 := by
    linear_combination
      (-3095773221727059444191701785042 / 37149602734297142792294438788993 : ℝ) * haxisFirst +
      (1182472396737778827026152573832 / 37149602734297142792294438788993 : ℝ) * haxisSecond +
      (16209785305436794250274884205729 / 74299205468594285584588877577986 : ℝ) * haxisThird +
      (122863 / 329676 : ℝ) * hcrossBottom
  have hthird : stressCoeff 3 = 0 := by
    linear_combination
      (-3095773221727059444191701785042 / 37149602734297142792294438788993 : ℝ) * haxisFirst +
      (1182472396737778827026152573832 / 37149602734297142792294438788993 : ℝ) * haxisSecond +
      (16209785305436794250274884205729 / 74299205468594285584588877577986 : ℝ) * haxisThird +
      (-(122863 / 329676) : ℝ) * hcrossBottom
  have hfourth : stressCoeff 4 = 0 := by
    linear_combination
      (16209785305436794250274884205729 / 74299205468594285584588877577986 : ℝ) * haxisFirst +
      (-3095773221727059444191701785042 / 37149602734297142792294438788993 : ℝ) * haxisSecond +
      (1182472396737778827026152573832 / 37149602734297142792294438788993 : ℝ) * haxisThird +
      (122863 / 329676 : ℝ) * hcrossSide
  have hfifth : stressCoeff 5 = 0 := by
    linear_combination
      (16209785305436794250274884205729 / 74299205468594285584588877577986 : ℝ) * haxisFirst +
      (-3095773221727059444191701785042 / 37149602734297142792294438788993 : ℝ) * haxisSecond +
      (1182472396737778827026152573832 / 37149602734297142792294438788993 : ℝ) * haxisThird +
      (-(122863 / 329676) : ℝ) * hcrossSide
  funext label
  rcases fin_six_cases label with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hzeroth
  · exact hfirst
  · exact hsecond
  · exact hthird
  · exact hfourth
  · exact hfifth

/-- **THE APPROXIMANT IS EXACTLY OFF-CONIC** — stress-freeness read through the
Veronese kernel duality. -/
theorem hasNoCommonQuadric_icosaApproximantDirection :
    HasNoCommonQuadric icosaApproximantDirection := by
  have hconic := (stressFree_iff_no_conic_sixThree icosaApproximantDirection).mp
    icosaApproximantDirection_isStressFree
  intro form hsymmetric hquadric
  exact hconic form hsymmetric hquadric

/-- The uniform chart point over the approximant: every mass `1`, every weight
`1/6`.  Fully rational — the icosahedral `sqrt 5` gauge never enters. -/
noncomputable def icosaApproximantChartPoint : DirectionChartPoint 6 where
  mass := fun _ => 1
  weight := fun _ => 1 / 6
  mass_pos := fun _ => by norm_num
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num

/-- The `{0, 4, 5}` chart gap at the uniform point, entry by entry.  With net
coefficient `5` on the selected labels and `-1` off them the gap block-splits:
a `2x2` block `[[4*S^2 + 10*L^2, 6*S*L], [6*S*L, 4*L^2 - 2*S^2]]` against the
decoupled entry `10*S^2 - 2*L^2`, at `S = 662/727`, `L = 249/169`. -/
theorem icosaApproximant_gap_eq :
    directionChartGap icosaApproximantDirection icosaApproximantChartPoint.mass
        icosaApproximantChartPoint.weight {0, 4, 5}
      = Matrix.of ![![377760012826 / 15095316769, 989028 / 122863, 0],
          ![989028 / 122863, 106043932348 / 15095316769, 0],
          ![0, 0, 59628215782 / 15095316769]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [icosaApproximantChartPoint, icosaApproximantDirection, atomMatrix,
      Matrix.sub_apply] <;>
    norm_num

/-- **THE STRICT TRIPLE AT THE APPROXIMANT.**  The `{0, 4, 5}` gap is positive
definite with identity floor `3`: scaled by the positive integer
`15095316769 * 332474062519` its quadratic form is `3` times the norm plus an
explicit all-integer sum of squares.  Exact minimum eigenvalue `~ 3.95`. -/
theorem icosaApproximant_gap_posDef :
    (directionChartGap icosaApproximantDirection icosaApproximantChartPoint.mass
      icosaApproximantChartPoint.weight {0, 4, 5}).PosDef := by
  rw [icosaApproximant_gap_eq]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.transpose_apply]
  · have hnormPos : (0 : ℝ) < vecArg ⬝ᵥ vecArg := by
      obtain ⟨badIndex, hbadRaw⟩ := Function.ne_iff.mp hne
      have hbad : vecArg badIndex ≠ 0 := by simpa using hbadRaw
      exact Finset.sum_pos' (fun index _ => mul_self_nonneg (vecArg index))
        ⟨badIndex, Finset.mem_univ _,
          lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm (mul_ne_zero hbad hbad))⟩
    rw [star_trivial]
    have hkey : (5018801291200615081111 : ℝ)
          * (vecArg ⬝ᵥ ((Matrix.of ![![377760012826 / 15095316769, 989028 / 122863, 0],
              ![989028 / 122863, 106043932348 / 15095316769, 0],
              ![0, 0, 59628215782 / 15095316769]] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vecArg))
        = 15056403873601845243333 * (vecArg ⬝ᵥ vecArg)
          + (332474062519 * vecArg 0 + 121514947164 * vecArg 1) ^ 2
          + 5434570735358001578383 * vecArg 1 ^ 2
          + 4768431268199245231525 * vecArg 2 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    linarith [hkey, sq_nonneg (332474062519 * vecArg 0 + 121514947164 * vecArg 1),
      sq_nonneg (vecArg 1), sq_nonneg (vecArg 2), hnormPos]

/-- The interior seed: at the approximant's uniform chart point SOME triple is
strictly dominating.  One point, one triple, rational arithmetic alone — the
non-vacuity anchor of `Gtz.InteriorFamilyMarginFloor`. -/
theorem icosaApproximantChartPoint_hasStrictTriple :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap icosaApproximantDirection icosaApproximantChartPoint.mass
        icosaApproximantChartPoint.weight selected).PosDef :=
  ⟨{0, 4, 5}, by decide, icosaApproximant_gap_posDef⟩

/-! ## Layer 3: the clearance functionals

The scan's structural finding is BINDING here: the fiber margin infimum over
masses and weights is zero at every direction tuple, approached along the
mass-collapse cascade, so any clearance functional powering the two-family
split MUST read the masses.  All three functionals below are polynomial in the
design data and selector-free; `Gtz.wallClearanceOf` is their minimum.  Trace
normalization is automatic on a `Gtz.WeightedDesign`: the masses sum to the
rank (`Gtz.sum_designMassOf_eq_three`). -/

/-- The design-level mass of a label: `m_c = w_c * |g_c|^2`.  This is the
chart mass of the rigidity bridge read off the design data. -/
def designMassOf (design : WeightedDesign 6 3) (label : Fin 6) : ℝ :=
  design.weight label * leverageOf (design.atom label)

/-- **TRACE NORMALIZATION IS PARSEVAL**: the six masses sum to the rank, so no
further normalization enters the clearance functionals. -/
theorem sum_designMassOf_eq_three (design : WeightedDesign 6 3) :
    ∑ label, designMassOf design label = 3 := by
  simpa [designMassOf] using sum_weight_mul_leverage design

/-- On the line-free stratum no atom vanishes: a zero atom would kill every
bracket through it, and the empty line family forbids every vanishing
bracket. -/
theorem atom_ne_zero_of_hasLinePattern_lineFree (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (label : Fin 6) :
    design.atom label ≠ 0 := by
  obtain ⟨otherFirst, otherSecond, hlabelFirst, hlabelSecond, hfirstSecond⟩ :
      ∃ otherFirst otherSecond : Fin 6,
        label ≠ otherFirst ∧ label ≠ otherSecond ∧ otherFirst ≠ otherSecond := by
    revert label
    decide
  intro hzero
  have hvanishes : atomBracket design label otherFirst otherSecond = 0 := by
    simp [atomBracket, tripleBracket_eq, hzero]
  have hfalse := (hpattern label otherFirst otherSecond hlabelFirst hlabelSecond
    hfirstSecond).mp hvanishes
  simp [lineFamilyPattern] at hfalse

/-- On the line-free stratum every design mass is positive. -/
theorem designMassOf_pos (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (label : Fin 6) :
    0 < designMassOf design label := by
  have hatomNe := atom_ne_zero_of_hasLinePattern_lineFree design hpattern label
  have hleveragePos : 0 < leverageOf (design.atom label) := by
    obtain ⟨coord, hcoordRaw⟩ := Function.ne_iff.mp hatomNe
    have hcoordNe : design.atom label coord ≠ 0 := by simpa using hcoordRaw
    exact Finset.sum_pos' (fun index _ => sq_nonneg (design.atom label index))
      ⟨coord, Finset.mem_univ _, sq_pos_of_ne_zero hcoordNe⟩
  exact mul_pos (design.weight_pos label) hleveragePos

/-- The mass-collapse clearance: the smallest design mass.  This is the
coordinate the scan's collapse cascade drives to zero, so it MUST appear in any
wall clearance with a positive interior floor. -/
noncomputable def massClearanceOf (design : WeightedDesign 6 3) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (designMassOf design)

/-- On the line-free stratum the mass clearance is positive. -/
theorem massClearanceOf_pos (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    0 < massClearanceOf design := by
  simp only [massClearanceOf, Finset.lt_inf'_iff]
  exact fun label _ => designMassOf_pos design hpattern label

/-- The conic clearance: the absolute six-by-six Veronese determinant of the
atoms — the polynomial distance functional to the on-conic wall. -/
noncomputable def conicClearanceOf (design : WeightedDesign 6 3) : ℝ :=
  |(veroneseGrid design.atom).det|

/-- Off the conic the conic clearance is positive. -/
theorem conicClearanceOf_pos (design : WeightedDesign 6 3)
    (hoffConic : HasNoCommonQuadric design.atom) :
    0 < conicClearanceOf design :=
  abs_pos.mpr ((hasNoCommonQuadric_iff_veroneseGrid_det_ne_zero design.atom).mp hoffConic)

/-- The ordered distinct label triples of `Fin 6` — the index set of the
bracket clearance.  Ordered triples keep the functional selector-free; the
square below makes the slot order irrelevant. -/
def distinctLabelTriples : Finset (Fin 6 × Fin 6 × Fin 6) :=
  Finset.univ.filter fun labels =>
    labels.1 ≠ labels.2.1 ∧ labels.1 ≠ labels.2.2 ∧ labels.2.1 ≠ labels.2.2

/-- The distinct triples are nonempty — `(0, 1, 2)` qualifies. -/
theorem distinctLabelTriples_nonempty : distinctLabelTriples.Nonempty :=
  ⟨(0, 1, 2), by decide⟩

/-- The line clearance: the smallest squared bracket over distinct label
triples — the polynomial distance functional to the line walls. -/
noncomputable def bracketClearanceOf (design : WeightedDesign 6 3) : ℝ :=
  distinctLabelTriples.inf' distinctLabelTriples_nonempty fun labels =>
    atomBracket design labels.1 labels.2.1 labels.2.2 ^ 2

/-- On the line-free stratum the bracket clearance is positive. -/
theorem bracketClearanceOf_pos (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    0 < bracketClearanceOf design := by
  simp only [bracketClearanceOf, Finset.lt_inf'_iff]
  intro labels hmem
  simp only [distinctLabelTriples, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨hfirstMid, hfirstLast, hmidLast⟩ := hmem
  refine sq_pos_of_ne_zero fun hvanishes => ?_
  have hfalse := (hpattern labels.1 labels.2.1 labels.2.2 hfirstMid hfirstLast
    hmidLast).mp hvanishes
  simp [lineFamilyPattern] at hfalse

/-- **THE WALL CLEARANCE** of the two-family split: the minimum of the mass,
conic, and bracket clearances.  Polynomial in the design data, selector-free,
and mass-reading — the shape the scan's structural finding mandates for
`Gtz.InteriorFamilyMarginFloor` and `Gtz.BoundaryCollarExcludesTies`. -/
noncomputable def wallClearanceOf (design : WeightedDesign 6 3) : ℝ :=
  min (massClearanceOf design) (min (conicClearanceOf design) (bracketClearanceOf design))

/-- **THE WALL CLEARANCE IS POSITIVE EXACTLY ON THE OPEN STRATUM** the
two-family split works over: line-free and off-conic. -/
theorem wallClearanceOf_pos (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hoffConic : HasNoCommonQuadric design.atom) :
    0 < wallClearanceOf design := by
  simp only [wallClearanceOf, lt_min_iff]
  exact ⟨massClearanceOf_pos design hpattern,
    conicClearanceOf_pos design hoffConic, bracketClearanceOf_pos design hpattern⟩


/-! ## Layer 4: the interior family -- clearance-bounded formulation, orbit
normalization, and the quantitative seed -/

/-- **FLOOR WEAKENING.**  A gap positive-semidefinite above a stronger identity
floor is positive-semidefinite above any weaker one: the difference of the two
shifted gaps is a nonnegative multiple of the identity. -/
theorem posSemidef_identityFloor_of_le {matrixSize : ℕ}
    {gapMatrix : Matrix (Fin matrixSize) (Fin matrixSize) ℝ} {strongFloor weakFloor : ℝ}
    (hstrong : (gapMatrix - (1 + strongFloor • 1)).PosSemidef)
    (hfloorLe : weakFloor ≤ strongFloor) :
    (gapMatrix - (1 + weakFloor • 1)).PosSemidef := by
  obtain ⟨hstrongHerm, hstrongForm⟩ := Matrix.posSemidef_iff_dotProduct_mulVec.mp hstrong
  have hsplit : gapMatrix
        - (1 + weakFloor • (1 : Matrix (Fin matrixSize) (Fin matrixSize) ℝ))
      = (gapMatrix - (1 + strongFloor • 1)) + (strongFloor - weakFloor) • 1 := by
    rw [sub_smul]
    abel
  rw [hsplit]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    have hstrongTranspose : (gapMatrix - (1 + strongFloor • 1))ᵀ
        = gapMatrix - (1 + strongFloor • 1) := hstrongHerm.eq
    rw [Matrix.transpose_add, hstrongTranspose, Matrix.transpose_smul, Matrix.transpose_one]
  · have hexpand : probeVec ⬝ᵥ (((gapMatrix - (1 + strongFloor • 1))
          + (strongFloor - weakFloor) • 1) *ᵥ probeVec)
        = probeVec ⬝ᵥ ((gapMatrix - (1 + strongFloor • 1)) *ᵥ probeVec)
          + (strongFloor - weakFloor) * (probeVec ⬝ᵥ probeVec) := by
      rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul, smul_eq_mul]
    have hnormNonneg : 0 ≤ probeVec ⬝ᵥ probeVec :=
      Finset.sum_nonneg fun index _ => mul_self_nonneg (probeVec index)
    have hstrongHere := hstrongForm probeVec
    rw [star_trivial] at hstrongHere
    have hshiftTerm : 0 ≤ (strongFloor - weakFloor) * (probeVec ⬝ᵥ probeVec) :=
      mul_nonneg (by linarith) hnormNonneg
    rw [star_trivial, hexpand]
    linarith

/-- A weakly dominating triple already carries every nonpositive identity
floor: inside the collar the ramp reduction below costs nothing. -/
theorem posSemidef_identityFloor_of_dominates {design : WeightedDesign 6 3}
    {selected : Finset (Fin 6)} (hdominates : Dominates design selected)
    {weakFloor : ℝ} (hfloorNonpos : weakFloor ≤ 0) :
    (subsetSum design selected - (1 + weakFloor • 1)).PosSemidef := by
  have hzeroFloor : (subsetSum design selected - (1 + (0 : ℝ) • 1)).PosSemidef := by
    have hdominatesRaw : (subsetSum design selected - 1).PosSemidef := hdominates
    simpa using hdominatesRaw
  exact posSemidef_identityFloor_of_le hzeroFloor hfloorNonpos

/-- **FAMILY I, CLEARANCE-BOUNDED CORE.**  On the clearance-bounded interior of
the line-free off-conic stratum -- wall clearance at least `clearanceFloor` --
every weakly dominated design has a triple dominating strictly above the
CONSTANT identity floor `marginFloor`.  This is the exact obligation the
per-orbit cell certificates must discharge; the ramp reduction feeds it
verbatim into `Gtz.lineFreeOffConicWeakToStrict_of_twoFamilies`.  NO instance
over `Gtz.wallClearanceOf` exists: every constant pair with
`clearanceFloor <= 3/8` and `1/16 <= marginFloor` is REFUTED in kernel
(`Gtz.clearanceBoundedInteriorFloor_rectangle_refuted` below, subsuming the
single-pair refutation at `(1/16, 1/4)`), and every `Monotone`
clearance-graded `floorOf` reaching `1/16` by clearance `3/8` is refuted
through `Gtz.InteriorFamilyMarginFloor`
(`Gtz.interiorFamilyMarginFloor_monotoneGraded_refuted` below).  The escape is
the dust-weight channel: raw weights below roughly `1/128` mask a jointly
degenerating frame from every weight-compensated clearance leg, so the
in-region margin infimum is zero in every `wallClearanceOf` band (exact
witness with best margin near `7.62e-5` at exact wall clearance at least
`1/4`), while a raw-weight floor restores the margin linearly (measured law:
stall about `2.2 * weightFloor`).  The interior family must be re-founded on
a weight-aware clearance functional; the two-family assembly is already
parametric in the functional. -/
def ClearanceBoundedInteriorFloor (clearanceFloor marginFloor : ℝ) : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    (∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected) →
    clearanceFloor ≤ wallClearanceOf design →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - (1 + marginFloor • 1)).PosSemidef

/-- The ramp floor of the two-family split: nonpositive at and below the collar
edge `clearanceFloor` (where the interior obligation is discharged by the weak
triple itself), rising linearly, capped at the interior constant
`marginFloor`. -/
noncomputable def clearanceRampFloor (clearanceFloor marginFloor clearance : ℝ) : ℝ :=
  min marginFloor (clearance - clearanceFloor)

/-- Strictly outside the collar the ramp floor is positive -- the positivity
input of the two-family assembly. -/
theorem clearanceRampFloor_pos {clearanceFloor marginFloor clearance : ℝ}
    (hmarginPos : 0 < marginFloor) (habove : clearanceFloor < clearance) :
    0 < clearanceRampFloor clearanceFloor marginFloor clearance :=
  lt_min hmarginPos (by linarith)

/-- **THE RAMP REDUCTION.**  A clearance-bounded constant floor upgrades to the
full `Gtz.InteriorFamilyMarginFloor` shape: inside the collar the ramp is
nonpositive and the weak triple discharges the obligation for free; outside it
the ramp is capped by `marginFloor` and the bounded core delivers the
triple. -/
theorem interiorFamilyMarginFloor_of_clearanceBounded
    {clearanceFloor marginFloor : ℝ}
    (hbounded : ClearanceBoundedInteriorFloor clearanceFloor marginFloor) :
    InteriorFamilyMarginFloor wallClearanceOf
      (clearanceRampFloor clearanceFloor marginFloor) := by
  intro design hlineFree hoffConic hweak _hclearancePos
  rcases le_or_gt (wallClearanceOf design) clearanceFloor with hinCollar | houtside
  · obtain ⟨weakTriple, hweakCard, hweakDominates⟩ := hweak
    have hrampNonpos :
        clearanceRampFloor clearanceFloor marginFloor (wallClearanceOf design) ≤ 0 := by
      have hdiff : wallClearanceOf design - clearanceFloor ≤ 0 := by linarith
      exact le_trans (min_le_right _ _) hdiff
    exact ⟨weakTriple, hweakCard,
      posSemidef_identityFloor_of_dominates hweakDominates hrampNonpos⟩
  · obtain ⟨strictTriple, hstrictCard, hstrictFloor⟩ :=
      hbounded design hlineFree hoffConic hweak houtside.le
    have hrampLe :
        clearanceRampFloor clearanceFloor marginFloor (wallClearanceOf design)
          ≤ marginFloor := min_le_left _ _
    exact ⟨strictTriple, hstrictCard, posSemidef_identityFloor_of_le hstrictFloor hrampLe⟩

/-- **FAMILY I'S INTERFACE TO THE ASSEMBLY.**  A clearance-bounded constant
interior floor plus a collar exclusion at the same clearance threshold close
tie-freeness of the whole open stratum through
`Gtz.lineFreeOffConicWeakToStrict_of_twoFamilies`. -/
theorem lineFreeOffConic_noTie_of_clearanceBoundedAndCollar
    {clearanceFloor marginFloor : ℝ} (hclearanceNonneg : 0 ≤ clearanceFloor)
    (hmarginPos : 0 < marginFloor)
    (hbounded : ClearanceBoundedInteriorFloor clearanceFloor marginFloor)
    (hcollar : BoundaryCollarExcludesTies wallClearanceOf clearanceFloor) :
    ∀ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      ¬ IsTie design :=
  lineFreeOffConicWeakToStrict_of_twoFamilies wallClearanceOf
    (clearanceRampFloor clearanceFloor marginFloor) clearanceFloor
    (interiorFamilyMarginFloor_of_clearanceBounded hbounded)
    (fun _clearance habove => clearanceRampFloor_pos hmarginPos habove)
    hcollar hclearanceNonneg

/-! ### Orbit normalization: the clearance functionals are relabelling-invariant
and every weak triple can be pinned at the base triple `{0, 1, 2}` -/

/-- Relabelling permutes the design masses. -/
theorem designMassOf_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6)) (label : Fin 6) :
    designMassOf (relabelDesign design relabel) label
      = designMassOf design (relabel label) := rfl

/-- The mass clearance is relabelling-invariant: the minimum of a permuted
family is the minimum of the family. -/
theorem massClearanceOf_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6)) :
    massClearanceOf (relabelDesign design relabel) = massClearanceOf design := by
  unfold massClearanceOf
  refine le_antisymm (Finset.le_inf' _ _ fun label _ => ?_)
    (Finset.le_inf' _ _ fun label _ => ?_)
  · refine le_trans (Finset.inf'_le _ (Finset.mem_univ (relabel.symm label))) (le_of_eq ?_)
    rw [designMassOf_relabelDesign, Equiv.apply_symm_apply]
  · exact le_trans (Finset.inf'_le _ (Finset.mem_univ (relabel label)))
      (le_of_eq (designMassOf_relabelDesign design relabel label).symm)

/-- Relabelling permutes the Veronese rows, so the conic clearance -- the
absolute Veronese determinant -- is relabelling-invariant. -/
theorem conicClearanceOf_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6)) :
    conicClearanceOf (relabelDesign design relabel) = conicClearanceOf design := by
  unfold conicClearanceOf
  have hgrid : veroneseGrid (relabelDesign design relabel).atom
      = (veroneseGrid design.atom).submatrix relabel id := rfl
  rw [hgrid, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign relabel) with hsign | hsign <;>
    rw [hsign] <;> simp

/-- Relabelling permutes the bracket triples, so the bracket clearance is
relabelling-invariant. -/
theorem bracketClearanceOf_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6)) :
    bracketClearanceOf (relabelDesign design relabel) = bracketClearanceOf design := by
  unfold bracketClearanceOf
  refine le_antisymm (Finset.le_inf' _ _ fun labels hmem => ?_)
    (Finset.le_inf' _ _ fun labels hmem => ?_)
  · have hmemPre : (relabel.symm labels.1, relabel.symm labels.2.1, relabel.symm labels.2.2)
        ∈ distinctLabelTriples := by
      simp only [distinctLabelTriples, Finset.mem_filter, Finset.mem_univ, true_and]
        at hmem ⊢
      exact ⟨fun h => hmem.1 (relabel.symm.injective h),
        fun h => hmem.2.1 (relabel.symm.injective h),
        fun h => hmem.2.2 (relabel.symm.injective h)⟩
    refine le_trans (Finset.inf'_le _ hmemPre) (le_of_eq ?_)
    simp only [atomBracket_relabelDesign, Equiv.apply_symm_apply]
  · have hmemPost : (relabel labels.1, relabel labels.2.1, relabel labels.2.2)
        ∈ distinctLabelTriples := by
      simp only [distinctLabelTriples, Finset.mem_filter, Finset.mem_univ, true_and]
        at hmem ⊢
      exact ⟨fun h => hmem.1 (relabel.injective h),
        fun h => hmem.2.1 (relabel.injective h),
        fun h => hmem.2.2 (relabel.injective h)⟩
    refine le_trans (Finset.inf'_le _ hmemPost) (le_of_eq ?_)
    simp only [atomBracket_relabelDesign]

/-- **THE WALL CLEARANCE IS RELABELLING-INVARIANT** -- the orbit split of the
interior family moves freely along `Gtz.relabelDesign`. -/
theorem wallClearanceOf_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6)) :
    wallClearanceOf (relabelDesign design relabel) = wallClearanceOf design := by
  unfold wallClearanceOf
  rw [massClearanceOf_relabelDesign, conicClearanceOf_relabelDesign,
    bracketClearanceOf_relabelDesign]

/-- Off-conic is relabelling-invariant: the six atoms are the same six
points. -/
theorem hasNoCommonQuadric_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6)) (hoffConic : HasNoCommonQuadric design.atom) :
    HasNoCommonQuadric (relabelDesign design relabel).atom := by
  intro form hsymmetric hquadric
  refine hoffConic form hsymmetric fun atomIndex => ?_
  have hatomEq : (relabelDesign design relabel).atom (relabel.symm atomIndex)
      = design.atom atomIndex := by
    show design.atom (relabel (relabel.symm atomIndex)) = design.atom atomIndex
    rw [Equiv.apply_symm_apply]
  have hquadricHere := hquadric (relabel.symm atomIndex)
  rw [hatomEq] at hquadricHere
  exact hquadricHere

/-- Line-freeness is relabelling-invariant: the empty line family is the
everywhere-false pattern, and relabelling only permutes which bracket is
inspected. -/
theorem hasLinePattern_lineFree_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6))
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    HasLinePattern (relabelDesign design relabel)
      (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  rw [atomBracket_relabelDesign]
  have hrelabelled := hpattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)
    (fun h => hleftMid (relabel.injective h))
    (fun h => hleftRight (relabel.injective h))
    (fun h => hmidRight (relabel.injective h))
  simpa [lineFamilyPattern] using hrelabelled

/-- **ORBIT NORMALIZATION.**  Every card-three label set is the image of the
base triple `{0, 1, 2}` under some relabelling: any bijection between the two
three-element subtypes extends to a permutation of the six labels. -/
theorem exists_relabel_map_baseTriple (selected : Finset (Fin 6))
    (hcard : selected.card = 3) :
    ∃ relabel : Equiv.Perm (Fin 6),
      ({0, 1, 2} : Finset (Fin 6)).map relabel.toEmbedding = selected := by
  have hbaseCard : ({0, 1, 2} : Finset (Fin 6)).card = 3 := by decide
  have hcardsMatch : ({0, 1, 2} : Finset (Fin 6)).card = selected.card :=
    hbaseCard.trans hcard.symm
  refine ⟨(Finset.equivOfCardEq hcardsMatch).extendSubtype, ?_⟩
  refine Finset.eq_of_subset_of_card_le (fun label hmem => ?_) ?_
  · obtain ⟨sourceLabel, hsourceMem, rfl⟩ := Finset.mem_map.mp hmem
    exact (Finset.equivOfCardEq hcardsMatch).extendSubtype_mem sourceLabel hsourceMem
  · refine le_of_eq ?_
    rw [Finset.card_map, hbaseCard, hcard]

/-- **FAMILY I, ORBIT-NORMALIZED CORE.**  The clearance-bounded interior
obligation with the weakly dominating triple pinned at the base triple
`{0, 1, 2}`.  Every hypothesis is relabelling-invariant, so this single
representative implies the full clearance-bounded core -- the shape the
per-cell certificates are built against.  Every instance with
`clearanceFloor <= 3/8` and `1/16 <= marginFloor` is REFUTED in kernel
(`Gtz.baseTripleClearanceBoundedFloor_rectangle_refuted` below, subsuming the
single-pair refutation at `(1/16, 1/4)`), and the Monotone clearance-graded
route through `Gtz.InteriorFamilyMarginFloor` is refuted with it
(`Gtz.interiorFamilyMarginFloor_monotoneGraded_refuted` below): the
dust-weight channel drives the in-region margin infimum to zero in every
`Gtz.wallClearanceOf` band, so no instance over that functional exists -- the
interior family must be re-founded on a weight-aware clearance functional. -/
def BaseTripleClearanceBoundedFloor (clearanceFloor marginFloor : ℝ) : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    Dominates design {0, 1, 2} →
    clearanceFloor ≤ wallClearanceOf design →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - (1 + marginFloor • 1)).PosSemidef

/-- **THE ORBIT SPLIT.**  The base-triple core suffices: relabel the weak
triple onto `{0, 1, 2}`, run the representative obligation on the relabelled
design (all hypotheses transport by the invariance suite above), and carry the
floored triple back through the inverse relabelling. -/
theorem clearanceBoundedInteriorFloor_of_baseTriple
    {clearanceFloor marginFloor : ℝ}
    (hbase : BaseTripleClearanceBoundedFloor clearanceFloor marginFloor) :
    ClearanceBoundedInteriorFloor clearanceFloor marginFloor := by
  intro design hlineFree hoffConic hweak hclearance
  obtain ⟨weakTriple, hweakCard, hweakDominates⟩ := hweak
  obtain ⟨relabel, hmap⟩ := exists_relabel_map_baseTriple weakTriple hweakCard
  obtain ⟨strictTriple, hstrictCard, hstrictFloor⟩ :=
    hbase (relabelDesign design relabel)
      (hasLinePattern_lineFree_relabelDesign design relabel hlineFree)
      (hasNoCommonQuadric_relabelDesign design relabel hoffConic)
      (by rw [dominates_relabelDesign_iff, hmap]; exact hweakDominates)
      (by rw [wallClearanceOf_relabelDesign]; exact hclearance)
  refine ⟨strictTriple.map relabel.toEmbedding, ?_, ?_⟩
  · rw [Finset.card_map]
    exact hstrictCard
  · rw [← subsetSum_relabelDesign]
    exact hstrictFloor

/-! ### The quantitative seed at the icosa approximant -/

/-- The atom moment matrix of the approximant's uniform chart point is an exact
multiple of the identity: `T = tau • 1` with
`tau = 2 * (S^2 + L^2) = 90572026826 / 15095316769` (just above `6`).  Through
the whitening congruence this converts the raw identity floor of
`Gtz.icosaApproximant_gap_floorThree` into the design-level identity floor
`3 / tau` (just below `1/2`) at the seed, and pins the seed design's mass
clearance at exactly `1/2` on every label. -/
theorem icosaApproximant_atomMomentMatrix_eq :
    ∑ atomIndex, icosaApproximantChartPoint.mass atomIndex
        • atomMatrix (icosaApproximantDirection atomIndex)
      = (90572026826 / 15095316769 : ℝ) • 1 := by
  rw [Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [icosaApproximantChartPoint, icosaApproximantDirection, atomMatrix,
      Matrix.smul_apply, Matrix.add_apply] <;>
    norm_num

/-- **THE INTERIOR SEED CARRIES AN EXPLICIT MARGIN FLOOR.**  At the icosa
approximant's uniform chart point the `{0, 4, 5}` gap dominates `3 • 1`
outright: scaled by the positive integer `15095316769 * 332474062519` the
shifted quadratic form is an explicit all-integer sum of squares (the identity
part of the landed certificate cancels EXACTLY against the floor).  Combined
with `Gtz.icosaApproximant_atomMomentMatrix_eq` this is the design-level floor
`3 / tau` at the seed -- the quantitative anchor of
`Gtz.BaseTripleClearanceBoundedFloor`. -/
theorem icosaApproximant_gap_floorThree :
    (directionChartGap icosaApproximantDirection icosaApproximantChartPoint.mass
        icosaApproximantChartPoint.weight {0, 4, 5} - (3 : ℝ) • 1).PosSemidef := by
  rw [icosaApproximant_gap_eq]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply]
  · have hkey : (5018801291200615081111 : ℝ)
          * (probeVec ⬝ᵥ (((Matrix.of ![![377760012826 / 15095316769, 989028 / 122863, 0],
              ![989028 / 122863, 106043932348 / 15095316769, 0],
              ![0, 0, 59628215782 / 15095316769]] : Matrix (Fin 3) (Fin 3) ℝ)
                - (3 : ℝ) • 1) *ᵥ probeVec))
        = (332474062519 * probeVec 0 + 121514947164 * probeVec 1) ^ 2
          + 5434570735358001578383 * probeVec 1 ^ 2
          + 4768431268199245231525 * probeVec 2 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, Fin.sum_univ_three]
      ring
    rw [star_trivial]
    linarith [hkey, sq_nonneg (332474062519 * probeVec 0 + 121514947164 * probeVec 1),
      sq_nonneg (probeVec 1), sq_nonneg (probeVec 2)]


/-! # Layer 4: the boundary collar — per-wall split, the quantified stress walk,
the dust-monotonicity engine, and the two corner dust-ray witnesses

The `U(3,6)` collar (`Gtz.BoundaryCollarExcludesTies`) must exclude ties
outright where `Gtz.wallClearanceOf` is small.  This layer lands its
unconditional pieces: the split of the collar claim along the three walls; the
proof that the ATTAINED mass wall (a vanished atom) lies inside the stressed
locus — i.e. ON the conic wall — and is weakly dominated there; the stress
walk quantified with its off-wall residual explicit (the conic leg's engine);
the dust-monotonicity engine (one certificate dominates a whole dust-mass
ray); and explicit dust-ray collar witnesses at BOTH named surviving boundary
ties — the `(4,3)` tetrahedron and the `(5,3)` diamond — with margins that do
NOT degenerate as the dust mass collapses at fixed offset off the tie locus.
The exact-rational cartography behind this layer shows the margin dies only
along the FULL cascade (tie-locus offset, dust weight, and dust conductance
ratio collapsing simultaneously); that joint corner is the walled residual
`wallUThreeSixJointCornerCollar` of the campaign ledger. -/

/-! ## Layer 4a: the collar splits along the three walls -/

/-- **THE COLLAR SPLITS ALONG THE THREE WALLS.**  `Gtz.wallClearanceOf` is the
minimum of the mass, conic, and bracket clearances, so the collar claim for the
combined clearance follows from the three per-wall collar legs — each leg may
be attacked with its own wall's tools (the five-label exclusions on the mass
wall, the stress walk on the conic wall, the chart classes on the bracket
wall). -/
theorem boundaryCollarExcludesTies_wallClearance_of_perWall (collarWidth : ℝ)
    (hmassLeg : BoundaryCollarExcludesTies massClearanceOf collarWidth)
    (hconicLeg : BoundaryCollarExcludesTies conicClearanceOf collarWidth)
    (hbracketLeg : BoundaryCollarExcludesTies bracketClearanceOf collarWidth) :
    BoundaryCollarExcludesTies wallClearanceOf collarWidth := by
  intro design hpattern hoffConic hclearance
  simp only [wallClearanceOf] at hclearance
  rcases min_le_iff.mp hclearance with hmassSmall | hinnerSmall
  · exact hmassLeg design hpattern hoffConic hmassSmall
  · rcases min_le_iff.mp hinnerSmall with hconicSmall | hbracketSmall
    · exact hconicLeg design hpattern hoffConic hconicSmall
    · exact hbracketLeg design hpattern hoffConic hbracketSmall

/-! ## Layer 4b: the attained mass wall lies ON the conic wall -/

/-- **A VANISHED ATOM IS A STRESS**: the coordinate vector at the vanished
label annihilates the atom-matrix sum, so the design is not stress-free.  The
attained mass wall (`Gtz.designMassOf` at zero forces a zero atom, weights
being positive) therefore lies inside the stressed locus. -/
theorem not_stressFree_of_atom_eq_zero (design : WeightedDesign 6 3)
    (vanishedLabel : Fin 6) (hvanished : design.atom vanishedLabel = 0) :
    ¬ IsStressFreeDesign design := by
  intro hstressFree
  have hcollapse : (∑ label, (if label = vanishedLabel then (1 : ℝ) else 0)
      • atomMatrix (design.atom label)) = 0 := by
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' Finset.univ vanishedLabel
      (fun label => atomMatrix (design.atom label)), if_pos (Finset.mem_univ vanishedLabel),
      hvanished]
    ext rowIndex colIndex
    simp [atomMatrix, Matrix.vecMulVec_apply]
  have hzeroed := hstressFree (fun label => if label = vanishedLabel then 1 else 0) hcollapse
  have hentry := congrFun hzeroed vanishedLabel
  simp at hentry

/-- **THE MASS WALL MEETS THE CONIC WALL.**  Through the shipped equivalence,
a design with a vanished atom carries a common quadric: the two walls of the
`U(3,6)` collar are one stressed locus at their attained boundary. -/
theorem not_hasNoCommonQuadric_of_atom_eq_zero (design : WeightedDesign 6 3)
    (vanishedLabel : Fin 6) (hvanished : design.atom vanishedLabel = 0) :
    ¬ HasNoCommonQuadric design.atom := fun hoffConic =>
  not_stressFree_of_atom_eq_zero design vanishedLabel hvanished
    ((isStressFreeDesign_iff_hasNoCommonQuadric design).mpr hoffConic)

/-- **THE ATTAINED MASS WALL IS WEAKLY DOMINATED**: the vanished-atom stress
feeds the stress-conditional walk, which closes below size six. -/
theorem exists_dominating_of_atom_eq_zero (design : WeightedDesign 6 3)
    (vanishedLabel : Fin 6) (hvanished : design.atom vanishedLabel = 0) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected := by
  refine exists_dominating_sixThree_of_stress design
    (stress := fun label => if label = vanishedLabel then 1 else 0) ?_ ?_
  · intro hzero
    have hentry := congrFun hzero vanishedLabel
    simp at hentry
  · simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' Finset.univ vanishedLabel
      (fun label => atomMatrix (design.atom label)), if_pos (Finset.mem_univ vanishedLabel),
      hvanished]
    ext rowIndex colIndex
    simp [atomMatrix, Matrix.vecMulVec_apply]

/-! ## Layer 4c: the quantified stress walk -/

/-- **THE QUANTIFIED STRESS WALK.**  The weight walk of
`Gtz.exists_rescaledReducedDesign_of_stress` run against an ARBITRARY stress
vector with a positive entry: the walked weights stay nonnegative, the argmin
weight vanishes exactly, the walk length is characterized as the exact minimum
of `weight / stress` over the positive-stress labels, and the walked Parseval
identity carries the explicit residual `walkLength • (Σ stress • atom)` — the
off-wall cost of walking a design that is only NEAR the conic wall.  On the
wall the residual is zero and the shipped walk is recovered
(`Gtz.exists_walkedWeights_parseval_of_commonQuadric`). -/
theorem exists_walkedWeights_of_positiveStressEntry {size rank : ℕ}
    (design : WeightedDesign size rank) {stress : Fin size → ℝ}
    (hposEntry : ∃ label, 0 < stress label) :
    ∃ (stopLabel : Fin size) (walkLength : ℝ),
      0 < stress stopLabel ∧
      walkLength = design.weight stopLabel / stress stopLabel ∧
      0 < walkLength ∧
      (∀ label, 0 < stress label → walkLength ≤ design.weight label / stress label) ∧
      (∀ label, 0 ≤ design.weight label - walkLength * stress label) ∧
      design.weight stopLabel - walkLength * stress stopLabel = 0 ∧
      (∑ label, (design.weight label - walkLength * stress label)
          • atomMatrix (design.atom label))
        = 1 - walkLength • (∑ label, stress label • atomMatrix (design.atom label)) := by
  obtain ⟨raiseLabel, hraiseLabel⟩ := hposEntry
  set raisers : Finset (Fin size) := Finset.univ.filter (fun label => 0 < stress label)
    with hraisers
  have hraisersNonempty : raisers.Nonempty :=
    ⟨raiseLabel, Finset.mem_filter.mpr ⟨Finset.mem_univ raiseLabel, hraiseLabel⟩⟩
  obtain ⟨stopLabel, hstopMem, hstopMin⟩ :=
    Finset.exists_min_image raisers (fun label => design.weight label / stress label)
      hraisersNonempty
  have hstressStop : 0 < stress stopLabel := (Finset.mem_filter.mp hstopMem).2
  refine ⟨stopLabel, design.weight stopLabel / stress stopLabel, hstressStop, rfl,
    div_pos (design.weight_pos stopLabel) hstressStop, ?_, ?_, ?_, ?_⟩
  · intro label hlabelPos
    exact hstopMin label (Finset.mem_filter.mpr ⟨Finset.mem_univ label, hlabelPos⟩)
  · intro label
    rcases le_or_gt (stress label) 0 with hnonpos | hpos
    · have hweight := design.weight_pos label
      have hwalkPos : 0 < design.weight stopLabel / stress stopLabel :=
        div_pos (design.weight_pos stopLabel) hstressStop
      nlinarith
    · have hmem : label ∈ raisers := Finset.mem_filter.mpr ⟨Finset.mem_univ label, hpos⟩
      have hbound := (le_div_iff₀ hpos).mp (hstopMin label hmem)
      linarith
  · rw [div_mul_cancel₀ _ (ne_of_gt hstressStop), sub_self]
  · simp only [sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, design.isParseval]

/-- **ON THE CONIC WALL THE RESIDUAL VANISHES**: a common quadric manufactures
a stress, the quantified walk consumes it, and the walked weights form an EXACT
sub-Parseval system with one weight vanished — the reduced object the collar's
conic leg compactifies onto, now with the walk data explicit rather than only
the domination conclusion of `Gtz.exists_dominating_of_commonQuadric`. -/
theorem exists_walkedWeights_parseval_of_commonQuadric (design : WeightedDesign 6 3)
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form) (hnonzero : form ≠ 0)
    (hquadric : ∀ atomIndex, design.atom atomIndex ⬝ᵥ (form *ᵥ design.atom atomIndex) = 0) :
    ∃ walked : Fin 6 → ℝ, (∀ label, 0 ≤ walked label) ∧ (∃ stopLabel, walked stopLabel = 0)
      ∧ (∑ label, walked label • atomMatrix (design.atom label)) = 1 := by
  obtain ⟨stress, hstressNe, hstressSum⟩ :=
    exists_stress_of_commonQuadric design.atom hsymmetric hnonzero hquadric
  obtain ⟨witnessLabel, hwitnessRaw⟩ := Function.ne_iff.mp hstressNe
  have hwitness : stress witnessLabel ≠ 0 := by simpa using hwitnessRaw
  rcases lt_or_gt_of_ne hwitness with hnegative | hpositive
  · obtain ⟨stopLabel, walkLength, _, _, _, _, hnonneg, hstopZero, hparseval⟩ :=
      exists_walkedWeights_of_positiveStressEntry design
        (stress := -stress) ⟨witnessLabel, by simpa using hnegative⟩
    refine ⟨fun label => design.weight label - walkLength * (-stress) label,
      hnonneg, ⟨stopLabel, hstopZero⟩, ?_⟩
    rw [hparseval]
    have hnegSum : (∑ label, (-stress) label • atomMatrix (design.atom label)) = 0 := by
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hstressSum, neg_zero]
    rw [hnegSum, smul_zero, sub_zero]
  · obtain ⟨stopLabel, walkLength, _, _, _, _, hnonneg, hstopZero, hparseval⟩ :=
      exists_walkedWeights_of_positiveStressEntry design
        (stress := stress) ⟨witnessLabel, hpositive⟩
    refine ⟨fun label => design.weight label - walkLength * stress label,
      hnonneg, ⟨stopLabel, hstopZero⟩, ?_⟩
    rw [hparseval, hstressSum, smul_zero, sub_zero]

/-! ## Layer 4d: the dust-monotonicity engine -/

/-- **THE DUST-MONOTONICITY ENGINE.**  A positive-definite certificate at the
ceiling scale propagates down the whole ray: subtracting LESS of a positive-
semidefinite perturbation keeps the matrix positive definite.  One rational
certificate therefore strictly dominates an entire dust-mass interval. -/
theorem posDef_sub_smul_of_scale_le {matrixSize : ℕ}
    {base perturb : Matrix (Fin matrixSize) (Fin matrixSize) ℝ} {ceilingScale : ℝ}
    (hceiling : (base - ceilingScale • perturb).PosDef) (hperturb : perturb.PosSemidef)
    {scale : ℝ} (hscale : scale ≤ ceilingScale) :
    (base - scale • perturb).PosDef := by
  obtain ⟨hceilingHerm, hceilingForm⟩ := Matrix.posDef_iff_dotProduct_mulVec.mp hceiling
  have hperturbTranspose : perturbᵀ = perturb := transpose_eq_of_isHermitian hperturb.1
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    have hbaseTranspose : baseᵀ = base := by
      have hshift : (base - ceilingScale • perturb)ᵀ
          = base - ceilingScale • perturb := transpose_eq_of_isHermitian hceilingHerm
      have hexpand : baseᵀ - ceilingScale • perturbᵀ
          = base - ceilingScale • perturb := by
        rw [← Matrix.transpose_smul, ← Matrix.transpose_sub, hshift]
      rw [hperturbTranspose] at hexpand
      have hshifted := congrArg (fun matrixArg => matrixArg + ceilingScale • perturb) hexpand
      simpa using hshifted
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hbaseTranspose, hperturbTranspose]
  · have hsplit : base - scale • perturb
        = (base - ceilingScale • perturb) + (ceilingScale - scale) • perturb := by
      rw [sub_smul]
      abel
    have hceilingValue := hceilingForm hne
    rw [star_trivial] at hceilingValue
    have hperturbValue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hperturb).2 probeVec
    rw [star_trivial] at hperturbValue
    rw [star_trivial, hsplit, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hscale) hperturbValue]

/-! ## Layer 4e: the tetra-corner dust-ray witness -/

/-- The tetra-corner directions: the four integer tetrahedral atoms (the exact
`(4,3)` tie tuple — at uniform masses and weights `1/4` every triple's gap is
PSD-singular) plus two generic dust atoms.  Exactly line-free and off-conic. -/
def tetraCornerDirection : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 1, 1]
  | 1 => ![1, -1, -1]
  | 2 => ![-1, 1, -1]
  | 3 => ![-1, -1, 1]
  | 4 => ![2, 1, 0]
  | 5 => ![0, 2, 1]

/-- The tetra-corner masses along the dust ray: three heavy units, the fourth
heavy displaced to `1/4` (the fixed offset off the tie locus), and two dust
masses equal to the ray parameter. -/
noncomputable def tetraCornerMass (dustScale : ℝ) : Fin 6 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1 / 4
  | 4 => dustScale
  | 5 => dustScale

/-- The tetra-corner weights along the dust ray: the heavies share the residual
`1 - 2 * dustScale` equally, the dust labels carry `dustScale` each — so the
dust conductance ratio `mass / weight` stays one along the whole ray. -/
noncomputable def tetraCornerWeight (dustScale : ℝ) : Fin 6 → ℝ
  | 0 => (1 - 2 * dustScale) / 4
  | 1 => (1 - 2 * dustScale) / 4
  | 2 => (1 - 2 * dustScale) / 4
  | 3 => (1 - 2 * dustScale) / 4
  | 4 => dustScale
  | 5 => dustScale

set_option maxHeartbeats 1600000 in
/-- **THE TETRA-CORNER TUPLE IS EXACTLY LINE-FREE**: every bracket of three
distinct labels is nonzero, so the tuple realizes the empty line family. -/
theorem tripleBracket_tetraCornerDirection_ne_zero
    (leftLabel midLabel rightLabel : Fin 6) (hleftMid : leftLabel ≠ midLabel)
    (hleftRight : leftLabel ≠ rightLabel) (hmidRight : midLabel ≠ rightLabel) :
    tripleBracket (tetraCornerDirection leftLabel) (tetraCornerDirection midLabel)
      (tetraCornerDirection rightLabel) ≠ 0 := by
  rcases fin_six_cases leftLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_six_cases midLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin_six_cases rightLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hleftMid
          | exact absurd rfl hleftRight
          | exact absurd rfl hmidRight
          | (simp [tetraCornerDirection, tripleBracket_eq] <;> norm_num)

/-- **THE TETRA-CORNER TUPLE IS EXACTLY STRESS-FREE**: the six-by-six stress
system has determinant `208`; the certificate below is its exact inverse, one
`linear_combination` per coordinate. -/
theorem tetraCornerDirection_isStressFree :
    ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex
          • atomMatrix (tetraCornerDirection atomIndex)) = 0 →
        stressCoeff = 0 := by
  intro stressCoeff hstress
  have hentry : ∀ rowIndex colIndex : Fin 3,
      ∑ atomIndex, stressCoeff atomIndex
          * (tetraCornerDirection atomIndex rowIndex
            * tetraCornerDirection atomIndex colIndex) = 0 := by
    intro rowIndex colIndex
    rw [← sum_smul_atomMatrix_apply tetraCornerDirection stressCoeff rowIndex colIndex,
      hstress, Matrix.zero_apply]
  have haxisFirst := hentry 0 0
  have haxisSecond := hentry 1 1
  have haxisThird := hentry 2 2
  have hcrossTop := hentry 0 1
  have hcrossSide := hentry 0 2
  have hcrossBottom := hentry 1 2
  simp [tetraCornerDirection, Fin.sum_univ_six] at haxisFirst haxisSecond haxisThird
  simp [tetraCornerDirection, Fin.sum_univ_six] at hcrossTop hcrossSide hcrossBottom
  have hzeroth : stressCoeff 0 = 0 := by
    linear_combination (-(3 / 52) : ℝ) * haxisFirst + (-(7 / 26) : ℝ) * haxisSecond +
      (15 / 26 : ℝ) * haxisThird + (1 / 4 : ℝ) * hcrossTop + (1 / 4 : ℝ) * hcrossSide +
      (1 / 4 : ℝ) * hcrossBottom
  have hfirst : stressCoeff 1 = 0 := by
    linear_combination (9 / 52 : ℝ) * haxisFirst + (-(5 / 26) : ℝ) * haxisSecond +
      (7 / 26 : ℝ) * haxisThird + (-(1 / 4) : ℝ) * hcrossTop + (-(1 / 4) : ℝ) * hcrossSide +
      (1 / 4 : ℝ) * hcrossBottom
  have hsecond : stressCoeff 2 = 0 := by
    linear_combination (5 / 52 : ℝ) * haxisFirst + (3 / 26 : ℝ) * haxisSecond +
      (1 / 26 : ℝ) * haxisThird + (-(1 / 4) : ℝ) * hcrossTop + (1 / 4 : ℝ) * hcrossSide +
      (-(1 / 4) : ℝ) * hcrossBottom
  have hthird : stressCoeff 3 = 0 := by
    linear_combination (-(7 / 52) : ℝ) * haxisFirst + (1 / 26 : ℝ) * haxisSecond +
      (9 / 26 : ℝ) * haxisThird + (1 / 4 : ℝ) * hcrossTop + (-(1 / 4) : ℝ) * hcrossSide +
      (-(1 / 4) : ℝ) * hcrossBottom
  have hfourth : stressCoeff 4 = 0 := by
    linear_combination (3 / 13 : ℝ) * haxisFirst + (1 / 13 : ℝ) * haxisSecond +
      (-(4 / 13) : ℝ) * haxisThird
  have hfifth : stressCoeff 5 = 0 := by
    linear_combination (-(1 / 13) : ℝ) * haxisFirst + (4 / 13 : ℝ) * haxisSecond +
      (-(3 / 13) : ℝ) * haxisThird
  funext label
  rcases fin_six_cases label with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hzeroth
  · exact hfirst
  · exact hsecond
  · exact hthird
  · exact hfourth
  · exact hfifth

/-- **THE TETRA-CORNER TUPLE IS EXACTLY OFF-CONIC** — stress-freeness read
through the Veronese kernel duality. -/
theorem hasNoCommonQuadric_tetraCornerDirection :
    HasNoCommonQuadric tetraCornerDirection := by
  have hconic := (stressFree_iff_no_conic_sixThree tetraCornerDirection).mp
    tetraCornerDirection_isStressFree
  intro form hsymmetric hquadric
  exact hconic form hsymmetric hquadric

/-- The tetra-corner chart point at ray parameter `dustScale`. -/
noncomputable def tetraCornerChartPoint (dustScale : ℝ) (hdustPos : 0 < dustScale)
    (hdustSmall : dustScale < 1 / 2) : DirectionChartPoint 6 where
  mass := tetraCornerMass dustScale
  weight := tetraCornerWeight dustScale
  mass_pos := by
    intro label
    fin_cases label
    · norm_num [tetraCornerMass]
    · norm_num [tetraCornerMass]
    · norm_num [tetraCornerMass]
    · norm_num [tetraCornerMass]
    · simpa [tetraCornerMass] using hdustPos
    · simpa [tetraCornerMass] using hdustPos
  weight_pos := by
    intro label
    fin_cases label
    · simp only [tetraCornerWeight]
      linarith
    · simp only [tetraCornerWeight]
      linarith
    · simp only [tetraCornerWeight]
      linarith
    · simp only [tetraCornerWeight]
      linarith
    · simpa [tetraCornerWeight] using hdustPos
    · simpa [tetraCornerWeight] using hdustPos
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    simp only [tetraCornerWeight]
    ring

/-- **THE CLEARED QUADRATIC FORM OF THE HEAVY-TRIPLE GAP** along the dust ray:
multiplying by the positive heavy-weight numerator `1 - 2 * dustScale` clears
every division and leaves a polynomial identity in the ray parameter and the
probe coordinates. -/
theorem tetraCorner_gap_form (dustScale : ℝ)
    (hhalfNe : 1 - 2 * dustScale ≠ 0) (probeVec : Fin 3 → ℝ) :
    (1 - 2 * dustScale)
        * (probeVec ⬝ᵥ (directionChartGap tetraCornerDirection (tetraCornerMass dustScale)
            (tetraCornerWeight dustScale) ({0, 1, 2} : Finset (Fin 6)) *ᵥ probeVec))
      = 4 * ((probeVec 0 + probeVec 1 + probeVec 2) ^ 2
            + (probeVec 0 - probeVec 1 - probeVec 2) ^ 2
            + (-probeVec 0 + probeVec 1 - probeVec 2) ^ 2)
        - (1 - 2 * dustScale)
            * (((probeVec 0 + probeVec 1 + probeVec 2) ^ 2
                + (probeVec 0 - probeVec 1 - probeVec 2) ^ 2
                + (-probeVec 0 + probeVec 1 - probeVec 2) ^ 2)
              + (1 / 4) * (-probeVec 0 - probeVec 1 + probeVec 2) ^ 2)
        - dustScale * (1 - 2 * dustScale)
            * ((2 * probeVec 0 + probeVec 1) ^ 2 + (2 * probeVec 1 + probeVec 2) ^ 2) := by
  rw [directionChartGap, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  simp only [tetraCornerDirection, tetraCornerMass, tetraCornerWeight, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  field_simp
  ring

/-- **THE DUST-RAY WITNESS.**  Along the whole ray `0 < dustScale ≤ 1/4` the
heavy triple `{0, 1, 2}` is strictly dominating — ONE rational certificate (the
corner value, identity floor `1`) covers the entire ray down to the mass wall.
This is the kernel form of the scan's finding that the margin does NOT
degenerate under dust-mass collapse alone at a fixed offset off the tie locus:
the joint corner needs the tie offset and the dust conductance ratio to
collapse SIMULTANEOUSLY. -/
theorem tetraCorner_gap_posDef_on_dustRay (dustScale : ℝ) (hdustPos : 0 < dustScale)
    (hdustLe : dustScale ≤ 1 / 4) :
    (directionChartGap tetraCornerDirection (tetraCornerMass dustScale)
      (tetraCornerWeight dustScale) ({0, 1, 2} : Finset (Fin 6))).PosDef := by
  have hhalfPos : 0 < 1 - 2 * dustScale := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (directionChartGap_transpose _ _ _ _),
      fun probeVec hne => ?_⟩
  rw [star_trivial]
  have hnormPos : 0 < probeVec ⬝ᵥ probeVec := by
    obtain ⟨witnessIndex, hwitnessRaw⟩ := Function.ne_iff.mp hne
    have hwitness : probeVec witnessIndex ≠ 0 := by simpa using hwitnessRaw
    exact Finset.sum_pos' (fun index _ => mul_self_nonneg (probeVec index))
      ⟨witnessIndex, Finset.mem_univ _,
        lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm (mul_ne_zero hwitness hwitness))⟩
  have hform := tetraCorner_gap_form dustScale (ne_of_gt hhalfPos) probeVec
  have hcertKey : (5724 : ℝ)
        * (3 * ((probeVec 0 + probeVec 1 + probeVec 2) ^ 2
              + (probeVec 0 - probeVec 1 - probeVec 2) ^ 2
              + (-probeVec 0 + probeVec 1 - probeVec 2) ^ 2)
          - (1 / 4) * (-probeVec 0 - probeVec 1 + probeVec 2) ^ 2
          - (1 / 4) * ((2 * probeVec 0 + probeVec 1) ^ 2
              + (2 * probeVec 1 + probeVec 2) ^ 2))
      = 5724 * (probeVec ⬝ᵥ probeVec)
        + 53 * (27 * probeVec 0 - 15 * probeVec 1 + 13 * probeVec 2) ^ 2
        + (159 * probeVec 1 + 164 * probeVec 2) ^ 2
        + 7077 * probeVec 2 ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_three]
    ring
  have hcertPos : 0
      < 3 * ((probeVec 0 + probeVec 1 + probeVec 2) ^ 2
            + (probeVec 0 - probeVec 1 - probeVec 2) ^ 2
            + (-probeVec 0 + probeVec 1 - probeVec 2) ^ 2)
        - (1 / 4) * (-probeVec 0 - probeVec 1 + probeVec 2) ^ 2
        - (1 / 4) * ((2 * probeVec 0 + probeVec 1) ^ 2
            + (2 * probeVec 1 + probeVec 2) ^ 2) := by
    nlinarith [hcertKey, hnormPos,
      sq_nonneg (27 * probeVec 0 - 15 * probeVec 1 + 13 * probeVec 2),
      sq_nonneg (159 * probeVec 1 + 164 * probeVec 2), sq_nonneg (probeVec 2)]
  have hdustTail : (0 : ℝ) ≤ 1 / 4 - dustScale + 2 * dustScale ^ 2 := by
    nlinarith [sq_nonneg (dustScale - 1 / 4)]
  have hrhsPos : 0
      < 4 * ((probeVec 0 + probeVec 1 + probeVec 2) ^ 2
            + (probeVec 0 - probeVec 1 - probeVec 2) ^ 2
            + (-probeVec 0 + probeVec 1 - probeVec 2) ^ 2)
        - (1 - 2 * dustScale)
            * (((probeVec 0 + probeVec 1 + probeVec 2) ^ 2
                + (probeVec 0 - probeVec 1 - probeVec 2) ^ 2
                + (-probeVec 0 + probeVec 1 - probeVec 2) ^ 2)
              + (1 / 4) * (-probeVec 0 - probeVec 1 + probeVec 2) ^ 2)
        - dustScale * (1 - 2 * dustScale)
            * ((2 * probeVec 0 + probeVec 1) ^ 2 + (2 * probeVec 1 + probeVec 2) ^ 2) := by
    nlinarith [hcertPos,
      mul_nonneg hdustPos.le (by positivity :
        (0 : ℝ) ≤ (probeVec 0 + probeVec 1 + probeVec 2) ^ 2
          + (probeVec 0 - probeVec 1 - probeVec 2) ^ 2
          + (-probeVec 0 + probeVec 1 - probeVec 2) ^ 2),
      mul_nonneg hdustPos.le (sq_nonneg (-probeVec 0 - probeVec 1 + probeVec 2)),
      mul_nonneg hdustTail (by positivity :
        (0 : ℝ) ≤ (2 * probeVec 0 + probeVec 1) ^ 2 + (2 * probeVec 1 + probeVec 2) ^ 2)]
  rcases le_or_gt (probeVec ⬝ᵥ (directionChartGap tetraCornerDirection
      (tetraCornerMass dustScale) (tetraCornerWeight dustScale)
      ({0, 1, 2} : Finset (Fin 6)) *ᵥ probeVec)) 0 with hnonpos | hpositive
  · exfalso
    nlinarith [hrhsPos, hform, mul_nonneg hhalfPos.le (neg_nonneg.mpr hnonpos)]
  · exact hpositive

/-- The corner witness packaged for the record: at every ray parameter in
`(0, 1/4]` the tetra-corner chart point has a strictly dominating triple. -/
theorem tetraCornerChartPoint_hasStrictTriple (dustScale : ℝ) (hdustPos : 0 < dustScale)
    (hdustLe : dustScale ≤ 1 / 4) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap tetraCornerDirection
        (tetraCornerChartPoint dustScale hdustPos (by linarith)).mass
        (tetraCornerChartPoint dustScale hdustPos (by linarith)).weight selected).PosDef :=
  ⟨{0, 1, 2}, by decide, tetraCorner_gap_posDef_on_dustRay dustScale hdustPos hdustLe⟩

/-! ## Layer 4f: the diamond-corner dust-ray witness -/

/-- The diamond-corner directions: the five reduced incidence rows of
`M(K4 - e)` with three rows bent by the slide `1/4` off the two triangle
planes (the `(5,3)` diamond tie lives at slide `0`, masses = the tie
conductances `(2,3,3,3,3)`, uniform weights), plus one generic dust atom.
Exactly line-free and off-conic. -/
noncomputable def diamondCornerDirection : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, -1, 0]
  | 1 => ![1, 0, -1]
  | 2 => ![1, 1 / 4, 0]
  | 3 => ![0, 1, -(3 / 4)]
  | 4 => ![0, 1, 1 / 4]
  | 5 => ![2, 3, 5]

/-- The diamond-corner masses along the dust ray: the five tie conductances
and the dust mass equal to the ray parameter. -/
noncomputable def diamondCornerMass (dustScale : ℝ) : Fin 6 → ℝ
  | 0 => 2
  | 1 => 3
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => dustScale

/-- The diamond-corner weights along the dust ray: the five heavies share
`1 - dustScale` equally, the dust label carries `dustScale` — dust conductance
ratio one along the whole ray. -/
noncomputable def diamondCornerWeight (dustScale : ℝ) : Fin 6 → ℝ
  | 0 => (1 - dustScale) / 5
  | 1 => (1 - dustScale) / 5
  | 2 => (1 - dustScale) / 5
  | 3 => (1 - dustScale) / 5
  | 4 => (1 - dustScale) / 5
  | 5 => dustScale

set_option maxHeartbeats 1600000 in
/-- **THE DIAMOND-CORNER TUPLE IS EXACTLY LINE-FREE**: the slide breaks both
diamond triangles and every bracket of three distinct labels is nonzero. -/
theorem tripleBracket_diamondCornerDirection_ne_zero
    (leftLabel midLabel rightLabel : Fin 6) (hleftMid : leftLabel ≠ midLabel)
    (hleftRight : leftLabel ≠ rightLabel) (hmidRight : midLabel ≠ rightLabel) :
    tripleBracket (diamondCornerDirection leftLabel) (diamondCornerDirection midLabel)
      (diamondCornerDirection rightLabel) ≠ 0 := by
  rcases fin_six_cases leftLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_six_cases midLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin_six_cases rightLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hleftMid
          | exact absurd rfl hleftRight
          | exact absurd rfl hmidRight
          | (simp [diamondCornerDirection, tripleBracket_eq]; norm_num)

/-- **THE DIAMOND-CORNER TUPLE IS EXACTLY STRESS-FREE**: the six-by-six stress
system has determinant `-1625/32`; the certificate below is its exact inverse,
one `linear_combination` per coordinate. -/
theorem diamondCornerDirection_isStressFree :
    ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex
          • atomMatrix (diamondCornerDirection atomIndex)) = 0 →
        stressCoeff = 0 := by
  intro stressCoeff hstress
  have hentry : ∀ rowIndex colIndex : Fin 3,
      ∑ atomIndex, stressCoeff atomIndex
          * (diamondCornerDirection atomIndex rowIndex
            * diamondCornerDirection atomIndex colIndex) = 0 := by
    intro rowIndex colIndex
    rw [← sum_smul_atomMatrix_apply diamondCornerDirection stressCoeff rowIndex colIndex,
      hstress, Matrix.zero_apply]
  have haxisFirst := hentry 0 0
  have haxisSecond := hentry 1 1
  have haxisThird := hentry 2 2
  have hcrossTop := hentry 0 1
  have hcrossSide := hentry 0 2
  have hcrossBottom := hentry 1 2
  simp [diamondCornerDirection, Fin.sum_univ_six] at haxisFirst haxisSecond haxisThird
  simp [diamondCornerDirection, Fin.sum_univ_six] at hcrossTop hcrossSide hcrossBottom
  have hzeroth : stressCoeff 0 = 0 := by
    linear_combination (263 / 1300 : ℝ) * haxisFirst + (-(3 / 325) : ℝ) * haxisSecond +
      (16 / 325 : ℝ) * haxisThird + (-(1049 / 1300) : ℝ) * hcrossTop +
      (327 / 1300 : ℝ) * hcrossSide + (8 / 325 : ℝ) * hcrossBottom
  have hfirst : stressCoeff 1 = 0 := by
    linear_combination (3 / 260 : ℝ) * haxisFirst + (-(3 / 65) : ℝ) * haxisSecond +
      (16 / 65 : ℝ) * haxisThird + (-(9 / 260) : ℝ) * hcrossTop +
      (-(193 / 260) : ℝ) * hcrossSide + (8 / 65 : ℝ) * hcrossBottom
  have hsecond : stressCoeff 2 = 0 := by
    linear_combination (254 / 325 : ℝ) * haxisFirst + (24 / 325 : ℝ) * haxisSecond +
      (-(128 / 325) : ℝ) * haxisThird + (278 / 325 : ℝ) * hcrossTop +
      (126 / 325 : ℝ) * hcrossSide + (-(64 / 325) : ℝ) * hcrossBottom
  have hthird : stressCoeff 3 = 0 := by
    linear_combination (-(5 / 104) : ℝ) * haxisFirst + (5 / 26 : ℝ) * haxisSecond +
      (4 / 13 : ℝ) * haxisThird + (15 / 104 : ℝ) * hcrossTop +
      (27 / 104 : ℝ) * hcrossSide + (-(11 / 13) : ℝ) * hcrossBottom
  have hfourth : stressCoeff 4 = 0 := by
    linear_combination (-(111 / 520) : ℝ) * haxisFirst + (111 / 130 : ℝ) * haxisSecond +
      (-(36 / 65) : ℝ) * haxisThird + (333 / 520 : ℝ) * hcrossTop +
      (-(399 / 520) : ℝ) * hcrossSide + (47 / 65 : ℝ) * hcrossBottom
  have hfifth : stressCoeff 5 = 0 := by
    linear_combination (3 / 2600 : ℝ) * haxisFirst + (-(3 / 650) : ℝ) * haxisSecond +
      (8 / 325 : ℝ) * haxisThird + (-(9 / 2600) : ℝ) * hcrossTop +
      (67 / 2600 : ℝ) * hcrossSide + (4 / 325 : ℝ) * hcrossBottom
  funext label
  rcases fin_six_cases label with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hzeroth
  · exact hfirst
  · exact hsecond
  · exact hthird
  · exact hfourth
  · exact hfifth

/-- **THE DIAMOND-CORNER TUPLE IS EXACTLY OFF-CONIC** — stress-freeness read
through the Veronese kernel duality. -/
theorem hasNoCommonQuadric_diamondCornerDirection :
    HasNoCommonQuadric diamondCornerDirection := by
  have hconic := (stressFree_iff_no_conic_sixThree diamondCornerDirection).mp
    diamondCornerDirection_isStressFree
  intro form hsymmetric hquadric
  exact hconic form hsymmetric hquadric

/-- The diamond-corner chart point at ray parameter `dustScale`. -/
noncomputable def diamondCornerChartPoint (dustScale : ℝ) (hdustPos : 0 < dustScale)
    (hdustSmall : dustScale < 1) : DirectionChartPoint 6 where
  mass := diamondCornerMass dustScale
  weight := diamondCornerWeight dustScale
  mass_pos := by
    intro label
    fin_cases label
    · norm_num [diamondCornerMass]
    · norm_num [diamondCornerMass]
    · norm_num [diamondCornerMass]
    · norm_num [diamondCornerMass]
    · norm_num [diamondCornerMass]
    · simpa [diamondCornerMass] using hdustPos
  weight_pos := by
    intro label
    fin_cases label
    · simp only [diamondCornerWeight]
      linarith
    · simp only [diamondCornerWeight]
      linarith
    · simp only [diamondCornerWeight]
      linarith
    · simp only [diamondCornerWeight]
      linarith
    · simp only [diamondCornerWeight]
      linarith
    · simpa [diamondCornerWeight] using hdustPos
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    simp only [diamondCornerWeight]
    ring

/-- **THE CLEARED QUADRATIC FORM OF THE NODE-STAR GAP** along the diamond dust
ray: multiplying by the positive heavy-weight numerator `1 - dustScale` clears
every division. -/
theorem diamondCorner_gap_form (dustScale : ℝ)
    (honeNe : 1 - dustScale ≠ 0) (probeVec : Fin 3 → ℝ) :
    (1 - dustScale)
        * (probeVec ⬝ᵥ (directionChartGap diamondCornerDirection
            (diamondCornerMass dustScale) (diamondCornerWeight dustScale)
            ({0, 1, 2} : Finset (Fin 6)) *ᵥ probeVec))
      = 5 * (2 * (probeVec 0 - probeVec 1) ^ 2 + 3 * (probeVec 0 - probeVec 2) ^ 2
            + 3 * (probeVec 0 + (1 / 4) * probeVec 1) ^ 2)
        - (1 - dustScale)
            * (2 * (probeVec 0 - probeVec 1) ^ 2 + 3 * (probeVec 0 - probeVec 2) ^ 2
              + 3 * (probeVec 0 + (1 / 4) * probeVec 1) ^ 2
              + 3 * (probeVec 1 - (3 / 4) * probeVec 2) ^ 2
              + 3 * (probeVec 1 + (1 / 4) * probeVec 2) ^ 2)
        - dustScale * (1 - dustScale)
            * (2 * probeVec 0 + 3 * probeVec 1 + 5 * probeVec 2) ^ 2 := by
  rw [directionChartGap, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  simp only [diamondCornerDirection, diamondCornerMass, diamondCornerWeight, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  field_simp
  ring

/-- **THE DIAMOND DUST-RAY WITNESS.**  Along the whole ray
`0 < dustScale ≤ 1/16` the node star `{0, 1, 2}` of the slid diamond is
strictly dominating — one rational certificate (identity floor `1/4`) covers
the entire ray down to the mass wall, at the fixed slide `1/4` off the
`(5,3)` diamond tie locus.  The second named surviving boundary tie thus also
carries a kernel dust-ray collar witness. -/
theorem diamondCorner_gap_posDef_on_dustRay (dustScale : ℝ) (hdustPos : 0 < dustScale)
    (hdustLe : dustScale ≤ 1 / 16) :
    (directionChartGap diamondCornerDirection (diamondCornerMass dustScale)
      (diamondCornerWeight dustScale) ({0, 1, 2} : Finset (Fin 6))).PosDef := by
  have honePos : 0 < 1 - dustScale := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (directionChartGap_transpose _ _ _ _),
      fun probeVec hne => ?_⟩
  rw [star_trivial]
  have hnormPos : 0 < probeVec ⬝ᵥ probeVec := by
    obtain ⟨witnessIndex, hwitnessRaw⟩ := Function.ne_iff.mp hne
    have hwitness : probeVec witnessIndex ≠ 0 := by simpa using hwitnessRaw
    exact Finset.sum_pos' (fun index _ => mul_self_nonneg (probeVec index))
      ⟨witnessIndex, Finset.mem_univ _,
        lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm (mul_ne_zero hwitness hwitness))⟩
  have hform := diamondCorner_gap_form dustScale (ne_of_gt honePos) probeVec
  have hcertKey : (4146912 : ℝ)
        * (4 * (2 * (probeVec 0 - probeVec 1) ^ 2 + 3 * (probeVec 0 - probeVec 2) ^ 2
              + 3 * (probeVec 0 + (1 / 4) * probeVec 1) ^ 2)
          - 3 * (probeVec 1 - (3 / 4) * probeVec 2) ^ 2
          - 3 * (probeVec 1 + (1 / 4) * probeVec 2) ^ 2
          - (1 / 16) * (2 * probeVec 0 + 3 * probeVec 1 + 5 * probeVec 2) ^ 2)
      = 1036728 * (probeVec ⬝ᵥ probeVec)
        + 2057 * (252 * probeVec 0 - 43 * probeVec 1 - 101 * probeVec 2) ^ 2
        + (2057 * probeVec 1 - 3209 * probeVec 2) ^ 2
        + 3190068 * probeVec 2 ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_three]
    ring
  have hcertPos : 0
      < 4 * (2 * (probeVec 0 - probeVec 1) ^ 2 + 3 * (probeVec 0 - probeVec 2) ^ 2
            + 3 * (probeVec 0 + (1 / 4) * probeVec 1) ^ 2)
        - 3 * (probeVec 1 - (3 / 4) * probeVec 2) ^ 2
        - 3 * (probeVec 1 + (1 / 4) * probeVec 2) ^ 2
        - (1 / 16) * (2 * probeVec 0 + 3 * probeVec 1 + 5 * probeVec 2) ^ 2 := by
    nlinarith [hcertKey, hnormPos,
      sq_nonneg (252 * probeVec 0 - 43 * probeVec 1 - 101 * probeVec 2),
      sq_nonneg (2057 * probeVec 1 - 3209 * probeVec 2), sq_nonneg (probeVec 2)]
  have hdustTail : (0 : ℝ) ≤ 1 / 16 - dustScale + dustScale ^ 2 := by
    nlinarith [sq_nonneg dustScale]
  have hrhsPos : 0
      < 5 * (2 * (probeVec 0 - probeVec 1) ^ 2 + 3 * (probeVec 0 - probeVec 2) ^ 2
            + 3 * (probeVec 0 + (1 / 4) * probeVec 1) ^ 2)
        - (1 - dustScale)
            * (2 * (probeVec 0 - probeVec 1) ^ 2 + 3 * (probeVec 0 - probeVec 2) ^ 2
              + 3 * (probeVec 0 + (1 / 4) * probeVec 1) ^ 2
              + 3 * (probeVec 1 - (3 / 4) * probeVec 2) ^ 2
              + 3 * (probeVec 1 + (1 / 4) * probeVec 2) ^ 2)
        - dustScale * (1 - dustScale)
            * (2 * probeVec 0 + 3 * probeVec 1 + 5 * probeVec 2) ^ 2 := by
    nlinarith [hcertPos,
      mul_nonneg hdustPos.le (by positivity :
        (0 : ℝ) ≤ 2 * (probeVec 0 - probeVec 1) ^ 2 + 3 * (probeVec 0 - probeVec 2) ^ 2
          + 3 * (probeVec 0 + (1 / 4) * probeVec 1) ^ 2
          + 3 * (probeVec 1 - (3 / 4) * probeVec 2) ^ 2
          + 3 * (probeVec 1 + (1 / 4) * probeVec 2) ^ 2),
      mul_nonneg hdustTail
        (sq_nonneg (2 * probeVec 0 + 3 * probeVec 1 + 5 * probeVec 2))]
  rcases le_or_gt (probeVec ⬝ᵥ (directionChartGap diamondCornerDirection
      (diamondCornerMass dustScale) (diamondCornerWeight dustScale)
      ({0, 1, 2} : Finset (Fin 6)) *ᵥ probeVec)) 0 with hnonpos | hpositive
  · exfalso
    nlinarith [hrhsPos, hform, mul_nonneg honePos.le (neg_nonneg.mpr hnonpos)]
  · exact hpositive

/-- The diamond corner witness packaged for the record: at every ray parameter
in `(0, 1/16]` the diamond-corner chart point has a strictly dominating
triple. -/
theorem diamondCornerChartPoint_hasStrictTriple (dustScale : ℝ) (hdustPos : 0 < dustScale)
    (hdustLe : dustScale ≤ 1 / 16) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap diamondCornerDirection
        (diamondCornerChartPoint dustScale hdustPos (by linarith)).mass
        (diamondCornerChartPoint dustScale hdustPos (by linarith)).weight selected).PosDef :=
  ⟨{0, 1, 2}, by decide, diamondCorner_gap_posDef_on_dustRay dustScale hdustPos hdustLe⟩



/-! ## The clearance-bounded interior floor is FALSE at the scan constants

An explicit rational design refutes `Gtz.BaseTripleClearanceBoundedFloor
(1/16) (1/4)`: it is line-free (every squared atom bracket is at least
`1/16`), off-conic (stress-free by the exact inverse of its Veronese grid),
weakly dominated AT the base triple `{0, 1, 2}`, and has wall clearance
above `1/16` -- yet NO triple of the twenty reaches the identity floor
`1/4` (each is refuted by an explicit rational probe vector).  The design
is an exact rational Parseval frame: the six atoms are the rows of a
rational Stiefel matrix (a Cayley transform of a rational skew matrix)
divided by rational sphere coordinates whose squares are the weights, so
`isParseval` holds by construction and every hypothesis is decided by
rational arithmetic.  Consequence: the interior family's constant pair
must move below the true in-region margin floor; the clearance-bounded
FORMULATION (and every landed reduction consuming it) is untouched --
only the instance `(1/16, 1/4)` dies. -/

/-- The floor-refuting atoms: rows of an exact rational Stiefel frame
scaled by the inverse sphere coordinates of the weights.  Numerically the
whitened image of the direction tuple `(-4,6,-7), (1,3,1), (1,1,-4),
(7,-8,4), (-3,2,-1), (4,-2,3)` at unit masses under the weight tilt
`13/32` on the fourth label -- a deep pocket of the clearance-bounded
region found by the exact cartography. -/
noncomputable def floorRefuterAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![-(174621712615 / 1757819585819), 1760824766148 / 1757819585819, -(3361373256444 / 1757819585819)]
  | 1 => ![170994768427 / 140742852576, 3377843407001 / 1688914230912, 42420072177 / 46914284192]
  | 2 => ![164735898971 / 140742852576, 5554055297 / 46914284192, -(3108696243541 / 1688914230912)]
  | 3 => ![56635636267 / 67439283526, -(130247073243 / 134878567052), -(2277522219 / 67439283526)]
  | 4 => ![-(308584667447 / 281485705152), 12782492079 / 93828568384, 3020254685 / 23457142096]
  | 5 => ![136209686963 / 93828568384, 43165409119 / 93828568384, 53101921411 / 70371426288]

/-- The floor-refuting weights: exact rational squares summing to one
(sphere coordinates `1199/3409, 1152/3409 (x4), 2208/3409`). -/
noncomputable def floorRefuterWeight : Fin 6 → ℝ
  | 0 => 1437601 / 11621281
  | 1 => 1327104 / 11621281
  | 2 => 1327104 / 11621281
  | 3 => 4875264 / 11621281
  | 4 => 1327104 / 11621281
  | 5 => 1327104 / 11621281

/-- The floor-refuting design.  Parseval is exact: the weighted atom sum
is the Gram of the underlying Stiefel frame. -/
noncomputable def floorRefuterDesign : WeightedDesign 6 3 where
  atom := floorRefuterAtom
  weight := floorRefuterWeight
  weight_pos := by
    intro label
    fin_cases label <;> norm_num [floorRefuterWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num [floorRefuterWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, floorRefuterWeight, atomMatrix,
        Matrix.add_apply] <;>
      norm_num

/-- The design's atoms, read back. -/
theorem floorRefuterDesign_atom_eq : floorRefuterDesign.atom = floorRefuterAtom :=
  rfl

/-- The design's weights, read back. -/
theorem floorRefuterDesign_weight_eq :
    floorRefuterDesign.weight = floorRefuterWeight := rfl

set_option maxHeartbeats 1600000 in
/-- **EVERY SQUARED BRACKET CLEARS `1/16`** -- one bound serving both the
line-freeness of the refuter (a vanishing bracket would violate it) and its
bracket-clearance leg. -/
theorem floorRefuterAtom_bracketSq_ge (leftLabel midLabel rightLabel : Fin 6)
    (hleftMid : leftLabel ≠ midLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hmidRight : midLabel ≠ rightLabel) :
    (1 / 16 : ℝ) ≤ tripleBracket (floorRefuterAtom leftLabel)
      (floorRefuterAtom midLabel) (floorRefuterAtom rightLabel) ^ 2 := by
  rcases fin_six_cases leftLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_six_cases midLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin_six_cases rightLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hleftMid
          | exact absurd rfl hleftRight
          | exact absurd rfl hmidRight
          | (simp [floorRefuterAtom, tripleBracket_eq]; norm_num)

/-- The refuter realizes the empty line family: no bracket vanishes. -/
theorem floorRefuterDesign_hasLinePattern_lineFree :
    HasLinePattern floorRefuterDesign
      (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  constructor
  · intro hvanishes
    exfalso
    have hlower := floorRefuterAtom_bracketSq_ge leftLabel midLabel rightLabel
      hleftMid hleftRight hmidRight
    have hbracket : tripleBracket (floorRefuterAtom leftLabel)
        (floorRefuterAtom midLabel) (floorRefuterAtom rightLabel) = 0 := hvanishes
    rw [hbracket] at hlower
    norm_num at hlower
  · intro hpattern
    simp [lineFamilyPattern] at hpattern

/-- **THE REFUTER IS EXACTLY STRESS-FREE**: the certificate is the exact
inverse of its six-by-six Veronese grid, one `linear_combination` per
coordinate. -/
theorem floorRefuterAtom_isStressFree :
    ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex
          • atomMatrix (floorRefuterAtom atomIndex)) = 0 →
        stressCoeff = 0 := by
  intro stressCoeff hstress
  have hentry : ∀ rowIndex colIndex : Fin 3,
      ∑ atomIndex, stressCoeff atomIndex
          * (floorRefuterAtom atomIndex rowIndex
            * floorRefuterAtom atomIndex colIndex) = 0 := by
    intro rowIndex colIndex
    rw [← sum_smul_atomMatrix_apply floorRefuterAtom stressCoeff rowIndex colIndex,
      hstress, Matrix.zero_apply]
  have haxisFirst := hentry 0 0
  have haxisSecond := hentry 1 1
  have haxisThird := hentry 2 2
  have hcrossTop := hentry 0 1
  have hcrossSide := hentry 0 2
  have hcrossBottom := hentry 1 2
  simp [floorRefuterAtom, Fin.sum_univ_six] at haxisFirst haxisSecond haxisThird
  simp [floorRefuterAtom, Fin.sum_univ_six] at hcrossTop hcrossSide hcrossBottom
  have hzeroth : stressCoeff 0 = 0 := by
    linear_combination
      (4377041194391856057300086799 / 154770218213782097954379612295 : ℝ) * haxisFirst +
      (108576259525333501412627586536 / 773851091068910489771898061475 : ℝ) * haxisSecond +
      (-(34732853275304793541319047056 / 773851091068910489771898061475) : ℝ) * haxisThird +
      (379864792143802624846035847163 / 2321553273206731469315694184425 : ℝ) * hcrossTop +
      (10511324993642237170603377367 / 773851091068910489771898061475 : ℝ) * hcrossSide +
      (-(418842617200497311027908760531 / 773851091068910489771898061475) : ℝ) * hcrossBottom
  have hfirst : stressCoeff 1 = 0 := by
    linear_combination
      (2475605632977455032941576192 / 154770218213782097954379612295 : ℝ) * haxisFirst +
      (2696370005722748618912248774656 / 13155468548171478326122267045075 : ℝ) * haxisSecond +
      (-(1404494377541880908521070002176 / 13155468548171478326122267045075) : ℝ) * haxisThird +
      (3275864928562777914955966857216 / 13155468548171478326122267045075 : ℝ) * hcrossTop +
      (-(1684292020239075806545465171968 / 13155468548171478326122267045075) : ℝ) * hcrossSide +
      (-(1604805455289318080670065074176 / 13155468548171478326122267045075) : ℝ) * hcrossBottom
  have hsecond : stressCoeff 2 = 0 := by
    linear_combination
      (-(6326005036997326675280265216 / 154770218213782097954379612295) : ℝ) * haxisFirst +
      (-(103308535411466751226458537984 / 773851091068910489771898061475) : ℝ) * haxisSecond +
      (223309272771979936849401790464 / 773851091068910489771898061475 : ℝ) * haxisThird +
      (-(128444301201045737596222439424 / 773851091068910489771898061475) : ℝ) * hcrossTop +
      (-(74622442684146498317980827648 / 773851091068910489771898061475) : ℝ) * hcrossSide +
      (371284266283838755760789028864 / 773851091068910489771898061475 : ℝ) * hcrossBottom
  have hthird : stressCoeff 3 = 0 := by
    linear_combination
      (-(11079101141549591275603985888 / 92862130928269258772627767377) : ℝ) * haxisFirst +
      (19793219880685589950140004256 / 154770218213782097954379612295 : ℝ) * haxisSecond +
      (27257089164654423157764678016 / 66330093520192327694734119555 : ℝ) * haxisThird +
      (-(540908565646210099950224666752 / 464310654641346293863138836885) : ℝ) * hcrossTop +
      (557255810250946655357385254888 / 1392931963924038881589416510655 : ℝ) * hcrossSide +
      (1324719460894253671088145009976 / 1392931963924038881589416510655 : ℝ) * hcrossBottom
  have hfourth : stressCoeff 4 = 0 := by
    linear_combination
      (28074740405758813211404176384 / 30954043642756419590875922459 : ℝ) * haxisFirst +
      (1463535246154919734122446149632 / 2631093709634295665224453409015 : ℝ) * haxisSecond +
      (-(3549427759247628579453558592512 / 2631093709634295665224453409015) : ℝ) * haxisThird +
      (3602617007789646974023464794112 / 2631093709634295665224453409015 : ℝ) * hcrossTop +
      (-(3165752345266754370732490360576 / 2631093709634295665224453409015) : ℝ) * hcrossSide +
      (-(6497923909074704086810317435392 / 2631093709634295665224453409015) : ℝ) * hcrossBottom
  have hfifth : stressCoeff 5 = 0 := by
    linear_combination
      (275206772393477372891667456 / 22110031173397442564911373185 : ℝ) * haxisFirst +
      (-(323043077683477106731396380672 / 773851091068910489771898061475) : ℝ) * haxisSecond +
      (401781552825231950926729946112 / 773851091068910489771898061475 : ℝ) * haxisThird +
      (-(354627972901022096304753518592 / 773851091068910489771898061475) : ℝ) * hcrossTop +
      (545243847612534467973177705216 / 773851091068910489771898061475 : ℝ) * hcrossSide +
      (670312835085653901131981056512 / 773851091068910489771898061475 : ℝ) * hcrossBottom
  funext label
  rcases fin_six_cases label with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hzeroth
  · exact hfirst
  · exact hsecond
  · exact hthird
  · exact hfourth
  · exact hfifth

/-- **THE REFUTER IS EXACTLY OFF-CONIC** -- stress-freeness read through
the Veronese kernel duality. -/
theorem hasNoCommonQuadric_floorRefuterAtom :
    HasNoCommonQuadric floorRefuterAtom := by
  have hconic := (stressFree_iff_no_conic_sixThree floorRefuterAtom).mp
    floorRefuterAtom_isStressFree
  intro form hsymmetric hquadric
  exact hconic form hsymmetric hquadric

/-- The base-triple subset sum, entry by entry. -/
theorem floorRefuter_subsetSum_baseTriple_eq :
    subsetSum floorRefuterDesign {0, 1, 2}
      = !![
        40664417805607618036860993385 / 14238396040499162292790706688, 843696541530889988069882077919 / 341721504971979895026976960512, -(295900650251359749683460947147 / 341721504971979895026976960512);
        843696541530889988069882077919 / 341721504971979895026976960512, 20574941443031652472825286606881 / 4100658059663758740323723526144, -(9255047472394720147692067667 / 28476792080998324585581413376);
        -(295900650251359749683460947147 / 341721504971979895026976960512), -(9255047472394720147692067667 / 28476792080998324585581413376), 32240321980734618910826167199209 / 4100658059663758740323723526144] := by
  simp only [subsetSum, floorRefuterDesign_atom_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [floorRefuterAtom, atomMatrix, Matrix.add_apply] <;>
    norm_num

/-- **THE BASE TRIPLE WEAKLY DOMINATES**: the gap above the identity is an
explicit rational sum of squares. -/
theorem floorRefuterDesign_dominates_baseTriple :
    Dominates floorRefuterDesign {0, 1, 2} := by
  have hgap : subsetSum floorRefuterDesign {0, 1, 2} - 1
      = !![
        26426021765108455744070286697 / 14238396040499162292790706688, 843696541530889988069882077919 / 341721504971979895026976960512, -(295900650251359749683460947147 / 341721504971979895026976960512);
        843696541530889988069882077919 / 341721504971979895026976960512, 16474283383367893732501563080737 / 4100658059663758740323723526144, -(9255047472394720147692067667 / 28476792080998324585581413376);
        -(295900650251359749683460947147 / 341721504971979895026976960512), -(9255047472394720147692067667 / 28476792080998324585581413376), 28139663921070860170502443673065 / 4100658059663758740323723526144] := by
    rw [floorRefuter_subsetSum_baseTriple_eq]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.sub_apply] <;> norm_num
  show (subsetSum floorRefuterDesign {0, 1, 2} - 1).PosSemidef
  rw [hgap]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp [Matrix.transpose_apply]
  · rw [star_trivial]
    have hkey : (11143565940738243821368968025312260979111195357662216964625461222121099263382431345440436027392 : ℝ)
          * (probeVec ⬝ᵥ ((!![
            26426021765108455744070286697 / 14238396040499162292790706688, 843696541530889988069882077919 / 341721504971979895026976960512, -(295900650251359749683460947147 / 341721504971979895026976960512);
            843696541530889988069882077919 / 341721504971979895026976960512, 16474283383367893732501563080737 / 4100658059663758740323723526144, -(9255047472394720147692067667 / 28476792080998324585581413376);
            -(295900650251359749683460947147 / 341721504971979895026976960512), -(9255047472394720147692067667 / 28476792080998324585581413376), 28139663921070860170502443673065 / 4100658059663758740323723526144]
              : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ probeVec))
        = 51417250206863875808409985804647097 * (634224522362602937857686880728 * probeVec 0 + 843696541530889988069882077919 * probeVec 1 - 295900650251359749683460947147 * probeVec 2) ^ 2
          + 3089929696288880705900761 * (51417250206863875808409985804647097 * probeVec 1 + 57999060210846234336824569396820221 * probeVec 2) ^ 2
          + 61573589695430783375688231189947834815934898144898519324526373606954535495148051625810669060096 * probeVec 2 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    linarith [hkey, sq_nonneg (634224522362602937857686880728 * probeVec 0 + 843696541530889988069882077919 * probeVec 1 - 295900650251359749683460947147 * probeVec 2), sq_nonneg (51417250206863875808409985804647097 * probeVec 1 + 57999060210846234336824569396820221 * probeVec 2),
      sq_nonneg (probeVec 2)]

/-- The mass clearance clears the collar threshold: every design mass is
far above `1/16` (the smallest is `~0.141`). -/
theorem floorRefuter_massClearance_ge :
    (1 / 16 : ℝ) ≤ massClearanceOf floorRefuterDesign := by
  simp only [massClearanceOf]
  refine Finset.le_inf' _ _ fun label _ => ?_
  fin_cases label <;>
    simp [designMassOf, leverageOf, floorRefuterDesign_atom_eq,
      floorRefuterDesign_weight_eq, floorRefuterAtom, floorRefuterWeight,
      Fin.sum_univ_three] <;>
    norm_num

/-- The bracket clearance clears the collar threshold, from the uniform
squared-bracket bound. -/
theorem floorRefuter_bracketClearance_ge :
    (1 / 16 : ℝ) ≤ bracketClearanceOf floorRefuterDesign := by
  simp only [bracketClearanceOf]
  refine Finset.le_inf' _ _ fun labels hmem => ?_
  simp only [distinctLabelTriples, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem
  obtain ⟨hfirstMid, hfirstLast, hmidLast⟩ := hmem
  have hlower := floorRefuterAtom_bracketSq_ge labels.1 labels.2.1 labels.2.2
    hfirstMid hfirstLast hmidLast
  simpa [atomBracket, floorRefuterDesign_atom_eq] using hlower

/-- The refuter's Veronese grid, entry by entry. -/
noncomputable def floorRefuterVeroneseGrid : Matrix (Fin 6) (Fin 6) ℝ :=
  !![
    30492742516595650138225 / 3089929696288880705900761, 3100503857080158886757904 / 3089929696288880705900761, 11298830169136940987525136 / 3089929696288880705900761, -(307478236279670636557020 / 3089929696288880705900761), 586968754778510864841060 / 3089929696288880705900761, -(5918789278214147534057712 / 3089929696288880705900761);
    29239210829403356054329 / 19808550551229669835776, 11409826082220123335814001 / 2852431279377072456351744, 1799462523501889519329 / 2200950061247741092864, 577593551162804705557427 / 237702606614756038029312, 2417870139520913585193 / 2200950061247741092864, 15920929014176223012353 / 8803800244990964371456;
    27137916409783518858841 / 19808550551229669835776, 30847530242133758209 / 2200950061247741092864, 9663992334605924384218681 / 2852431279377072456351744, 914952292285939399387 / 6602850183743223278592, -(512113870307497387296311 / 237702606614756038029312), -(17265870838202893086677 / 79234202204918679343104);
    3207595295367925695289 / 4548056962500214992676, 16964300088367406537049 / 18192227850000859970704, 5187107458038683961 / 4548056962500214992676, -(7376625865031856103881 / 9096113925000429985352), -(128988919985294716473 / 4548056962500214992676), 296640603270652886217 / 9096113925000429985352;
    95224496983375581497809 / 79234202204918679343104, 163392103749697742241 / 8803800244990964371456, 9121938362264449225 / 550237515311935273216, -(1314827022447375550771 / 8803800244990964371456), -(932004287575968739195 / 6602850183743223278592), 38606381587575140115 / 2200950061247741092864;
    18553078822558452163369 / 8803800244990964371456, 1863252544410648356161 / 8803800244990964371456, 2819814057540020230921 / 4952137637807417458944, 5879546863728815615597 / 8803800244990964371456, 7232996092526137264793 / 6602850183743223278592, 2292166162710800746909 / 6602850183743223278592]

/-- Unit upper-triangular column-elimination certificate for the Veronese
determinant. -/
noncomputable def floorRefuterVeroneseElimination : Matrix (Fin 6) (Fin 6) ℝ :=
  !![
    1, -(266795360776506384 / 2623871027350225), 614583693415540661319234000 / 64174994106169211791810019, -(1306686059846267259946465990518492 / 2720045052229304606287475566716223), 39675898404879265458602902548300 / 33916543305524975931869456929831, 6270987652195122429172110 / 436401585342222591882800167;
    0, 1, -(239910264949545447174037296 / 64174994106169211791810019), -(6282377143724609477268297818890764 / 13600225261146523031437377833581115), -(26688209394383321213637623545704 / 33916543305524975931869456929831), -(210314503700180408028252852 / 436401585342222591882800167);
    0, 0, 1, 2111681447791955846135777867372496 / 13600225261146523031437377833581115, 5526269099338433760331160977356 / 33916543305524975931869456929831, 261576531787260384717923142 / 436401585342222591882800167;
    0, 0, 0, 1, 2638424140035859323028799283918 / 33916543305524975931869456929831, -(230877586524102927281740572 / 436401585342222591882800167);
    0, 0, 0, 0, 1, 709952926578820921840075137 / 872803170684445183765600334;
    0, 0, 0, 0, 0, 1]

/-- The lower-triangular column-reduced form of the Veronese grid. -/
noncomputable def floorRefuterVeroneseReduced : Matrix (Fin 6) (Fin 6) ℝ :=
  !![
    30492742516595650138225 / 3089929696288880705900761, 0, 0, 0, 0, 0;
    29239210829403356054329 / 19808550551229669835776, -(745795639681136243781137729414339 / 5105080072131246228263218790400), 0, 0, 0, 0;
    27137916409783518858841 / 19808550551229669835776, -(548672825259102591700449619011 / 3939104993928430731684582400), 2054676512500067642176972822193825858208095 / 124860742058422549103498564774170875641856, 0, 0, 0;
    3207595295367925695289 / 4548056962500214992676, -(2304508555651083315250674150459 / 32559164715439685266580376400), 650849083029146246305238483585846357043 / 199084118649044923308951644379148561724, -(90958541608194137959036572530530000041 / 57556153305172085469042982991715278680), 0, 0;
    95224496983375581497809 / 79234202204918679343104, -(1925144670335870334482748063139 / 15756419975713722926738329600), 16231779086966623354398744082247076777 / 1416811252478469375266641303265373952, -(122446179506653922063207541369314210627 / 167119568008968475010302498819044741120), 86216272685826648381911776728416759 / 69461080689715150708468647792293888, 0;
    18553078822558452163369 / 8803800244990964371456, -(3372950654175225882747294581891 / 15756419975713722926738329600), 4326786317429457118575636542264163668105 / 216772121629205814415796119399602214656, -(3942733783856233059329906009529216301 / 11141304533931231667353499921269649408), 737443356093511583834678638827048605 / 208383242069145452125405943376881664, 773851091068910489771898061475 / 670312835085653901131981056512]

/-- The abstract Veronese grid of the refuter is the explicit one. -/
theorem floorRefuterVeroneseGrid_eq :
    veroneseGrid floorRefuterAtom = floorRefuterVeroneseGrid := by
  ext atomIndex coordIndex
  fin_cases atomIndex <;> fin_cases coordIndex <;>
    simp [veroneseGrid, veroneseCoords, floorRefuterAtom,
      floorRefuterVeroneseGrid] <;>
    norm_num

set_option maxHeartbeats 800000 in
/-- The column elimination, verified entrywise. -/
theorem floorRefuterVeronese_columnReduction :
    floorRefuterVeroneseGrid * floorRefuterVeroneseElimination
      = floorRefuterVeroneseReduced := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [floorRefuterVeroneseGrid, floorRefuterVeroneseElimination,
      floorRefuterVeroneseReduced, Matrix.mul_apply, Fin.sum_univ_six] <;>
    norm_num

/-- The elimination matrix is unit upper triangular, so its determinant is
one. -/
theorem floorRefuterVeroneseElimination_det :
    floorRefuterVeroneseElimination.det = 1 := by
  have htri : floorRefuterVeroneseElimination.BlockTriangular id := by
    intro rowIndex colIndex hlt
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp_all [floorRefuterVeroneseElimination]
  rw [Matrix.det_of_upperTriangular htri, Fin.prod_univ_six]
  simp [floorRefuterVeroneseElimination]

/-- The reduced form is lower triangular; its determinant is the diagonal
product. -/
theorem floorRefuterVeroneseReduced_det :
    floorRefuterVeroneseReduced.det = 164031558612224485491243275397886285393828313361765046989947401475 / 3053271314662738061920843255706665722660499978837226478744109056 := by
  have htri : floorRefuterVeroneseReducedᵀ.BlockTriangular id := by
    intro rowIndex colIndex hlt
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp_all [floorRefuterVeroneseReduced, Matrix.transpose_apply]
  rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular htri,
    Fin.prod_univ_six]
  simp [floorRefuterVeroneseReduced, Matrix.transpose_apply]
  norm_num

/-- **THE EXACT VERONESE DETERMINANT** of the refuter, via the triangular
factorization. -/
theorem floorRefuterVeronese_det :
    (veroneseGrid floorRefuterAtom).det = 164031558612224485491243275397886285393828313361765046989947401475 / 3053271314662738061920843255706665722660499978837226478744109056 := by
  have hproduct := congrArg Matrix.det floorRefuterVeronese_columnReduction
  rw [Matrix.det_mul, floorRefuterVeroneseElimination_det, mul_one,
    floorRefuterVeroneseReduced_det] at hproduct
  rw [floorRefuterVeroneseGrid_eq]
  exact hproduct

/-- The conic clearance clears the collar threshold (the determinant is
`~53.7`). -/
theorem floorRefuter_conicClearance_ge :
    (1 / 16 : ℝ) ≤ conicClearanceOf floorRefuterDesign := by
  simp only [conicClearanceOf, floorRefuterDesign_atom_eq]
  rw [floorRefuterVeronese_det, abs_of_pos (by norm_num)]
  norm_num

/-- **THE REFUTER SITS IN THE CLEARANCE-BOUNDED REGION**: its wall
clearance is at least `1/16`. -/
theorem floorRefuter_wallClearance_ge :
    (1 / 16 : ℝ) ≤ wallClearanceOf floorRefuterDesign := by
  simp only [wallClearanceOf, le_min_iff]
  exact ⟨floorRefuter_massClearance_ge,
    floorRefuter_conicClearance_ge, floorRefuter_bracketClearance_ge⟩

/-! ### No triple reaches the identity floor `1/4`

Each of the twenty floor-shifted gaps has an explicit rational probe with
strictly negative Rayleigh value. -/

/-- The `{0, 1, 2}` gap fails the `1/4` floor at the probe
`![3, -2, 0]`. -/
theorem floorRefuter_gap_zeroOneTwo_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {0, 1, 2}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {0, 1, 2}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        22866422754983665170872610025 / 14238396040499162292790706688, 843696541530889988069882077919 / 341721504971979895026976960512, -(295900650251359749683460947147 / 341721504971979895026976960512);
        843696541530889988069882077919 / 341721504971979895026976960512, 15449118868451954047420632199201 / 4100658059663758740323723526144, -(9255047472394720147692067667 / 28476792080998324585581413376);
        -(295900650251359749683460947147 / 341721504971979895026976960512), -(9255047472394720147692067667 / 28476792080998324585581413376), 27114499406154920485421512791529 / 4100658059663758740323723526144] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![3, -2, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 1, 3}` gap fails the `1/4` floor at the probe
`![3, -1, -1]`. -/
theorem floorRefuter_gap_zeroOneThree_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {0, 1, 3}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {0, 1, 3}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        14178838051686288005512373984617 / 15064223010848113705772567675904, 274667596782812291805196822294979 / 180770676130177364469270812110848, 2109255677502015813330834926169 / 1673802556760901522863618630656;
        274667596782812291805196822294979 / 180770676130177364469270812110848, 10165010215382035909321369082730529 / 2169248113562128373631249745330176, -(498672986985956585802429938767 / 6695210227043606091454474522624);
        2109255677502015813330834926169 / 1673802556760901522863618630656, -(498672986985956585802429938767 / 6695210227043606091454474522624), 5398661827210722446154627944593 / 1673802556760901522863618630656] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![3, -1, -1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 1, 4}` gap fails the `1/4` floor at the probe
`![2, -1, -1]`. -/
theorem floorRefuter_gap_zeroOneFour_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {0, 1, 4}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {0, 1, 4}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        163772231053182254723857874645 / 113907168323993298342325653504, 372654562148264447459261133385 / 170860752485989947513488480256, 42543419180438671149677309 / 37079156355466568470809132;
        372654562148264447459261133385 / 170860752485989947513488480256, 15467751100957165110094513518421 / 4100658059663758740323723526144, -(1133415120749677484700846739 / 12656352035999255371369517056);
        42543419180438671149677309 / 37079156355466568470809132, -(1133415120749677484700846739 / 12656352035999255371369517056), 10254256036041419080430891813 / 3164088008999813842842379264] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![2, -1, -1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 1, 5}` gap fails the `1/4` floor at the probe
`![2, -1, -1]`. -/
theorem floorRefuter_gap_zeroOneFive_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {0, 1, 5}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {0, 1, 5}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        266924720980884215883629098357 / 113907168323993298342325653504, 512280189905664958518245476153 / 170860752485989947513488480256, 5657282005406866876939135973 / 2373066006749860382131784448;
        512280189905664958518245476153 / 170860752485989947513488480256, 16259516727428063047475643436501 / 4100658059663758740323723526144, 9114629235147651696072391639 / 37969056107997766114108551168;
        5657282005406866876939135973 / 2373066006749860382131784448, 9114629235147651696072391639 / 37969056107997766114108551168, 108031280882492063778915936301 / 28476792080998324585581413376] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![2, -1, -1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 2, 3}` gap fails the `1/4` floor at the probe
`![1, 1, 0]`. -/
theorem floorRefuter_gap_zeroTwoThree_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {0, 2, 3}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {0, 2, 3}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        12580822706407082189886950256265 / 15064223010848113705772567675904, -(3876049845843177772793097777941 / 5021407670282704568590855891968), -(360245317143123368122185861780743 / 180770676130177364469270812110848);
        -(3876049845843177772793097777941 / 5021407670282704568590855891968), 1171561873710535349788673547761 / 1673802556760901522863618630656, -(126588093905417906201576141715269 / 60256892043392454823090270703616);
        -(360245317143123368122185861780743 / 180770676130177364469270812110848), -(126588093905417906201576141715269 / 60256892043392454823090270703616), 12572500732105001937297017901070441 / 2169248113562128373631249745330176] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, 1, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 2, 4}` gap fails the `1/4` floor at the probe
`![0, -1, 0]`. -/
theorem floorRefuter_gap_zeroTwoFour_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {0, 2, 4}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {0, 2, 4}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        151688939217422664435574897493 / 113907168323993298342325653504, -(4187537172926466333511880525 / 37969056107997766114108551168), -(719535974189109486385738445411 / 341721504971979895026976960512);
        -(4187537172926466333511880525 / 37969056107997766114108551168), -(2708497833361582258368051259 / 12656352035999255371369517056), -(241013660514997186075642728905 / 113907168323993298342325653504);
        -(719535974189109486385738445411 / 341721504971979895026976960512), -(241013660514997186075642728905 / 113907168323993298342325653504), 23829846643200994151075146725145 / 4100658059663758740323723526144] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, -1, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 2, 5}` gap fails the `1/4` floor at the probe
`![0, 1, 0]`. -/
theorem floorRefuter_gap_zeroTwoFive_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {0, 2, 5}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {0, 2, 5}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        254841429145124625595346121205 / 113907168323993298342325653504, 26840380106495869457373528979 / 37969056107997766114108551168, -(296967516577443449421928945043 / 341721504971979895026976960512);
        26840380106495869457373528979 / 37969056107997766114108551168, -(264776764006958994846045339 / 12656352035999255371369517056), -(203469036722807133625117933337 / 113907168323993298342325653504);
        -(296967516577443449421928945043 / 341721504971979895026976960512), -(203469036722807133625117933337 / 113907168323993298342325653504), 26096835267570172207000605762841 / 4100658059663758740323723526144] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, 1, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 3, 4}` gap fails the `1/4` floor at the probe
`![-1, -2, -1]`. -/
theorem floorRefuter_gap_zeroThreeFour_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {0, 3, 4}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {0, 3, 4}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        40188099953670870505335731086465 / 60256892043392454823090270703616, -(7095731043234496966578550374211 / 6695210227043606091454474522624), 102681300198558253450704873461 / 5021407670282704568590855891968;
        -(7095731043234496966578550374211 / 6695210227043606091454474522624), 4716668639889229831730259678289 / 6695210227043606091454474522624, -(3122238967881108135381123829341 / 1673802556760901522863618630656);
        102681300198558253450704873461 / 5021407670282704568590855891968, -(3122238967881108135381123829341 / 1673802556760901522863618630656), 1014483876632420767620981899513 / 418450639190225380715904657664] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![-1, -2, -1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 3, 5}` gap fails the `1/4` floor at the probe
`![-1, 3, 2]`. -/
theorem floorRefuter_gap_zeroThreeFive_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {0, 3, 5}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {0, 3, 5}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        10528418569491689773206078714457 / 6695210227043606091454474522624, -(1624474962963025088785756498339 / 6695210227043606091454474522624), 6312090024547761963280016698313 / 5021407670282704568590855891968;
        -(1624474962963025088785756498339 / 6695210227043606091454474522624), 6009397085577825538133400809969 / 6695210227043606091454474522624, -(7711624738137612927282736750067 / 5021407670282704568590855891968);
        6312090024547761963280016698313 / 5021407670282704568590855891968, -(7711624738137612927282736750067 / 5021407670282704568590855891968), 11212363539503063282867600691001 / 3766055752712028426443141918976] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![-1, 3, 2]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 4, 5}` gap fails the `1/4` floor at the probe
`![0, -1, 0]`. -/
theorem floorRefuter_gap_zeroFourFive_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {0, 4, 5}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {0, 4, 5}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        117841139079218779476111557825 / 56953584161996649171162826752, 2651407476372254295648184253 / 6328176017999627685684758528, 5430740067233876299679973359 / 4746132013499720764263568896;
        2651407476372254295648184253 / 6328176017999627685684758528, -(103634936779388351321353967 / 6328176017999627685684758528), -(7360399288332306266527386805 / 4746132013499720764263568896);
        5430740067233876299679973359 / 4746132013499720764263568896, -(7360399288332306266527386805 / 4746132013499720764263568896), 10652649031358446918244382605 / 3559599010124790573197676672] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, -1, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 2, 3}` gap fails the `1/4` floor at the probe
`![4, -3, 3]`. -/
theorem floorRefuter_gap_oneTwoThree_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {1, 2, 3}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {1, 2, 3}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        12057697909028469226052953 / 5239361620800247671562752, 220996864061216740381753967 / 125744678899205944117506048, -(136336766241310711251547547 / 125744678899205944117506048);
        220996864061216740381753967 / 125744678899205944117506048, 5577863293709425281179967121 / 1508936146790471329410072576, 17008204315738708954662109 / 10478723241600495343125504;
        -(136336766241310711251547547 / 125744678899205944117506048), 17008204315738708954662109 / 10478723241600495343125504, 4461485433994962504118589401 / 1508936146790471329410072576] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![4, -3, 3]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 2, 4}` gap fails the `1/4` floor at the probe
`![-1, 1, -1]`. -/
theorem floorRefuter_gap_oneTwoFour_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {1, 2, 4}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {1, 2, 4}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        73896751061324910657203 / 26411400734972893114368, 287515752039509692032271 / 118851303307378019014656, -(284536049591973594706487 / 237702606614756038029312);
        287515752039509692032271 / 118851303307378019014656, 7937204423807490184499269 / 2852431279377072456351744, 3981635000829244345895 / 2476068818903708729472;
        -(284536049591973594706487 / 237702606614756038029312), 3981635000829244345895 / 2476068818903708729472, 8477844794313011535611785 / 2852431279377072456351744] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![-1, 1, -1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 2, 5}` gap fails the `1/4` floor at the probe
`![-1, 1, -1]`. -/
theorem floorRefuter_gap_oneTwoFive_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {1, 2, 5}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {1, 2, 5}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        293443465603625219944121 / 79234202204918679343104, 384639799502888272778239 / 118851303307378019014656, 9403964091702221437081 / 237702606614756038029312;
        384639799502888272778239 / 118851303307378019014656, 8487959206581638183409349 / 2852431279377072456351744, 9595530265119545186713 / 4952137637807417458944;
        9403964091702221437081 / 237702606614756038029312, 9595530265119545186713 / 4952137637807417458944, 10054769562986084283839881 / 2852431279377072456351744] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![-1, 1, -1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 3, 4}` gap fails the `1/4` floor at the probe
`![0, 0, 1]`. -/
theorem floorRefuter_gap_oneThreeFour_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {1, 3, 4}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {1, 3, 4}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        89411511053331510515457029 / 41914892966401981372502016, 92396419122653722734082873 / 62872339449602972058753024, 6338019829576750106281 / 6822085443750322489014;
        92396419122653722734082873 / 62872339449602972058753024, 5584719473550185444921146501 / 1508936146790471329410072576, 8655742540813105247761181 / 4657210329600220152500224;
        6338019829576750106281 / 6822085443750322489014, 8655742540813105247761181 / 4657210329600220152500224, -(482832631983759764277163 / 1164302582400055038125056)] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, 0, 1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 3, 5}` gap fails the `1/4` floor at the probe
`![-1, 0, 2]`. -/
theorem floorRefuter_gap_oneThreeFive_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {1, 3, 5}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {1, 3, 5}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        127368960423326618652915877 / 41914892966401981372502016, 143775040230780991948699945 / 62872339449602972058753024, 1891087838454327532631381 / 873226936800041278593792;
        143775040230780991948699945 / 62872339449602972058753024, 5876068753637709736344578821 / 1508936146790471329410072576, 30572377912417443134292967 / 13971630988800660457500672;
        1891087838454327532631381 / 873226936800041278593792, 30572377912417443134292967 / 13971630988800660457500672, 1447514663729880759093469 / 10478723241600495343125504] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![-1, 0, 2]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 4, 5}` gap fails the `1/4` floor at the probe
`![0, -1, 2]`. -/
theorem floorRefuter_gap_oneFourFive_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {1, 4, 5}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {1, 4, 5}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        140058148473933363003283 / 39617101102459339671552, 700840986877403587307729 / 237702606614756038029312, 13554602223512909281177 / 6602850183743223278592;
        700840986877403587307729 / 237702606614756038029312, 8500919849002734901256569 / 2852431279377072456351744, 57394728272422773706075 / 26411400734972893114368;
        13554602223512909281177 / 6602850183743223278592, 57394728272422773706075 / 26411400734972893114368, 3042120533681519475025 / 19808550551229669835776] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, -1, 2]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{2, 3, 4}` gap fails the `1/4` floor at the probe
`![1, 1, 1]`. -/
theorem floorRefuter_gap_twoThreeFour_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {2, 3, 4}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {2, 3, 4}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        84965172061415935009804421 / 41914892966401981372502016, -(11481088762835868205531901 / 13971630988800660457500672), -(292223612705016294870023603 / 125744678899205944117506048);
        -(11481088762835868205531901 / 13971630988800660457500672), -(1326944292502273979125003 / 4657210329600220152500224), -(7031505842584380974814137 / 41914892966401981372502016);
        -(292223612705016294870023603 / 125744678899205944117506048), -(7031505842584380974814137 / 41914892966401981372502016), 3252818139243061920528825865 / 1508936146790471329410072576] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, 1, 1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{2, 3, 5}` gap fails the `1/4` floor at the probe
`![0, -1, 0]`. -/
theorem floorRefuter_gap_twoThreeFive_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {2, 3, 5}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {2, 3, 5}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        122922621431411043147263269 / 41914892966401981372502016, -(63617405474252824505885 / 13971630988800660457500672), -(136729345466351788130076131 / 125744678899205944117506048);
        -(63617405474252824505885 / 13971630988800660457500672), -(427718119392631104361323 / 4657210329600220152500224), 6783945027350001198214135 / 41914892966401981372502016;
        -(136729345466351788130076131 / 125744678899205944117506048), 6783945027350001198214135 / 41914892966401981372502016, 4087011341871117404341488649 / 1508936146790471329410072576] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, -1, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{2, 4, 5}` gap fails the `1/4` floor at the probe
`![0, 1, 0]`. -/
theorem floorRefuter_gap_twoFourFive_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {2, 4, 5}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {2, 4, 5}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        135855559634693688612307 / 39617101102459339671552, 8676984346494038896013 / 13205700367486446557184, -(285278165329291320374783 / 237702606614756038029312);
        8676984346494038896013 / 13205700367486446557184, -(4427357768554912166541 / 4401900122495482185728), 11629952851479420920371 / 79234202204918679343104;
        -(285278165329291320374783 / 237702606614756038029312), 11629952851479420920371 / 79234202204918679343104, 7769954260997614371571897 / 2852431279377072456351744] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, 1, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{3, 4, 5}` gap fails the `1/4` floor at the probe
`![0, 0, -1]`. -/
theorem floorRefuter_gap_threeFourFive_not_posSemidef :
    ¬ (subsetSum floorRefuterDesign {3, 4, 5}
      - (1 + (1 / 4 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum floorRefuterDesign {3, 4, 5}
      - (1 + (1 / 4 : ℝ) • 1)
      = !![
        57936274606257399927148337 / 20957446483200990686251008, -(681047823429214265447059 / 2328605164800110076250112), 1617080587134966403895039 / 1746453873600082557187584;
        -(681047823429214265447059 / 2328605164800110076250112), -(203278535250698015543039 / 2328605164800110076250112), 693867109654713025392347 / 1746453873600082557187584;
        1617080587134966403895039 / 1746453873600082557187584, 693867109654713025392347 / 1746453873600082557187584, -(868251027061456383923875 / 1309840405200061917890688)] := by
    simp only [subsetSum, floorRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [floorRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, 0, -1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The twenty card-three subsets of the six labels, enumerated. -/
theorem cardThreeFinsetsOfSix_enumeration :
    ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      selected = {0, 1, 2} ∨
      selected = {0, 1, 3} ∨
      selected = {0, 1, 4} ∨
      selected = {0, 1, 5} ∨
      selected = {0, 2, 3} ∨
      selected = {0, 2, 4} ∨
      selected = {0, 2, 5} ∨
      selected = {0, 3, 4} ∨
      selected = {0, 3, 5} ∨
      selected = {0, 4, 5} ∨
      selected = {1, 2, 3} ∨
      selected = {1, 2, 4} ∨
      selected = {1, 2, 5} ∨
      selected = {1, 3, 4} ∨
      selected = {1, 3, 5} ∨
      selected = {1, 4, 5} ∨
      selected = {2, 3, 4} ∨
      selected = {2, 3, 5} ∨
      selected = {2, 4, 5} ∨
      selected = {3, 4, 5} := by
  decide

/-- **THE SCAN CONSTANTS ARE REFUTED IN KERNEL.**  The rational refuter
design satisfies every hypothesis of the base-triple clearance-bounded
floor at `(1/16, 1/4)` and defeats every candidate triple, so that
instance of the interior Prop is FALSE.  (The refuter's own best floor is
`~0.221`; any repaired constant pair must sit below it.) -/
theorem baseTripleClearanceBoundedFloor_sixteenth_quarter_refuted :
    ¬ BaseTripleClearanceBoundedFloor (1 / 16) (1 / 4) := by
  intro hbase
  obtain ⟨selected, hcard, hfloor⟩ :=
    hbase floorRefuterDesign floorRefuterDesign_hasLinePattern_lineFree
      hasNoCommonQuadric_floorRefuterAtom floorRefuterDesign_dominates_baseTriple
      floorRefuter_wallClearance_ge
  have hpow : selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  rcases cardThreeFinsetsOfSix_enumeration selected hpow with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact floorRefuter_gap_zeroOneTwo_not_posSemidef hfloor
  · exact floorRefuter_gap_zeroOneThree_not_posSemidef hfloor
  · exact floorRefuter_gap_zeroOneFour_not_posSemidef hfloor
  · exact floorRefuter_gap_zeroOneFive_not_posSemidef hfloor
  · exact floorRefuter_gap_zeroTwoThree_not_posSemidef hfloor
  · exact floorRefuter_gap_zeroTwoFour_not_posSemidef hfloor
  · exact floorRefuter_gap_zeroTwoFive_not_posSemidef hfloor
  · exact floorRefuter_gap_zeroThreeFour_not_posSemidef hfloor
  · exact floorRefuter_gap_zeroThreeFive_not_posSemidef hfloor
  · exact floorRefuter_gap_zeroFourFive_not_posSemidef hfloor
  · exact floorRefuter_gap_oneTwoThree_not_posSemidef hfloor
  · exact floorRefuter_gap_oneTwoFour_not_posSemidef hfloor
  · exact floorRefuter_gap_oneTwoFive_not_posSemidef hfloor
  · exact floorRefuter_gap_oneThreeFour_not_posSemidef hfloor
  · exact floorRefuter_gap_oneThreeFive_not_posSemidef hfloor
  · exact floorRefuter_gap_oneFourFive_not_posSemidef hfloor
  · exact floorRefuter_gap_twoThreeFour_not_posSemidef hfloor
  · exact floorRefuter_gap_twoThreeFive_not_posSemidef hfloor
  · exact floorRefuter_gap_twoFourFive_not_posSemidef hfloor
  · exact floorRefuter_gap_threeFourFive_not_posSemidef hfloor

/-- The unpinned clearance-bounded interior floor falls with its
base-triple form: pinning the weak triple only specializes the
antecedent. -/
theorem clearanceBoundedInteriorFloor_sixteenth_quarter_refuted :
    ¬ ClearanceBoundedInteriorFloor (1 / 16) (1 / 4) := by
  intro hbounded
  refine baseTripleClearanceBoundedFloor_sixteenth_quarter_refuted ?_
  intro design hlineFree hoffConic hdominates hclearance
  exact hbounded design hlineFree hoffConic
    ⟨{0, 1, 2}, by decide, hdominates⟩ hclearance


/-! ## The minimax rectangle: no constant pair survives up to clearance `3/8`,
and no monotone graded floor reaches `1/16` by clearance `3/8`

A second exact rational Parseval design (Cayley Stiefel rows over square
weights, three dust weights near `1/128`, wall clearance above `3/8`)
defeats every triple at the identity floor `1/16` while its base triple
weakly dominates.  Consequences, all parametric: EVERY constant pair
`(clearanceFloor, marginFloor)` with `clearanceFloor <= 3/8` and
`marginFloor >= 1/16` is refuted, for BOTH interior Props; and every
MONOTONE graded floor `floorOf` with `1/16 <= floorOf (3/8)` refutes
`Gtz.InteriorFamilyMarginFloor wallClearanceOf floorOf`.  The escape
mechanism is the dust-weight channel: sub-`1/128` weights mask a
degenerating frame from every weight-compensated clearance functional,
and the adversarial floored minimax measures the residual margin floor as
LINEAR in the smallest raw weight (about twice it) -- so a repaired
region functional must read the raw weights themselves. -/

/-- The minimax-refuting atoms: rows of an exact rational Stiefel frame
(Cayley transform at denominator `512`) scaled by the inverse sphere
coordinates of the weights.  Three labels carry dust weights near `1/128`;
the frame beneath them is close to degenerate, which no weight-compensated
clearance functional can detect. -/
noncomputable def minimaxRefuterAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![-(4927036628422430505757 / 732692265994768663779), 37865450200479466992640 / 7571153415279276192383, -(16085987678537603064832 / 7571153415279276192383)]
  | 1 => ![-(381608764994125298282 / 132567289730364427791), -(386942708420217938409865 / 67874452341946587028992), -(536616776784415142198 / 132567289730364427791)]
  | 2 => ![-(182175176047769658575 / 394526604766413895881), -(364863091076974489445 / 394526604766413895881), 248327198638924044666487 / 403995243280807829382144]
  | 3 => ![196931171295388468112 / 44189096576788142597, 194718507215518381356 / 44189096576788142597, 189724779645054734682 / 44189096576788142597]
  | 4 => ![-(892385434552804744342 / 931146292537230382029), 308478787228998458342 / 931146292537230382029, 747298550272225278974 / 931146292537230382029]
  | 5 => ![2735282614417632724 / 39426199939769061359, -(23566406085175406926 / 39426199939769061359), 287215624121476987472 / 275983399578383429513]

/-- The minimax-refuting weights: exact rational squares summing to one. -/
noncomputable def minimaxRefuterWeight : Fin 6 → ℝ
  | 0 => 7368333921 / 926862531169
  | 1 => 7310934016 / 926862531169
  | 2 => 259007709184 / 926862531169
  | 3 => 7310934016 / 926862531169
  | 4 => 360691531776 / 926862531169
  | 5 => 285173088256 / 926862531169

/-- The minimax-refuting design; Parseval is exact by construction. -/
noncomputable def minimaxRefuterDesign : WeightedDesign 6 3 where
  atom := minimaxRefuterAtom
  weight := minimaxRefuterWeight
  weight_pos := by
    intro label
    fin_cases label <;> norm_num [minimaxRefuterWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num [minimaxRefuterWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, minimaxRefuterWeight, atomMatrix,
        Matrix.add_apply] <;>
      norm_num

/-- The design's atoms, read back. -/
theorem minimaxRefuterDesign_atom_eq :
    minimaxRefuterDesign.atom = minimaxRefuterAtom := rfl

/-- The design's weights, read back. -/
theorem minimaxRefuterDesign_weight_eq :
    minimaxRefuterDesign.weight = minimaxRefuterWeight := rfl

set_option maxHeartbeats 3200000 in
/-- **EVERY SQUARED BRACKET CLEARS `3/8`** -- serving both line-freeness
and the bracket-clearance leg at the strongest rectangle corner. -/
theorem minimaxRefuterAtom_bracketSq_ge (leftLabel midLabel rightLabel : Fin 6)
    (hleftMid : leftLabel ≠ midLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hmidRight : midLabel ≠ rightLabel) :
    (3 / 8 : ℝ) ≤ tripleBracket (minimaxRefuterAtom leftLabel)
      (minimaxRefuterAtom midLabel) (minimaxRefuterAtom rightLabel) ^ 2 := by
  rcases fin_six_cases leftLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_six_cases midLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin_six_cases rightLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hleftMid
          | exact absurd rfl hleftRight
          | exact absurd rfl hmidRight
          | (simp [minimaxRefuterAtom, tripleBracket_eq]; norm_num)

/-- The minimax refuter realizes the empty line family. -/
theorem minimaxRefuterDesign_hasLinePattern_lineFree :
    HasLinePattern minimaxRefuterDesign
      (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  constructor
  · intro hvanishes
    exfalso
    have hlower := minimaxRefuterAtom_bracketSq_ge leftLabel midLabel rightLabel
      hleftMid hleftRight hmidRight
    have hbracket : tripleBracket (minimaxRefuterAtom leftLabel)
        (minimaxRefuterAtom midLabel) (minimaxRefuterAtom rightLabel) = 0 :=
      hvanishes
    rw [hbracket] at hlower
    norm_num at hlower
  · intro hpattern
    simp [lineFamilyPattern] at hpattern

/-- The minimax refuter's Veronese grid, entry by entry. -/
noncomputable def minimaxRefuterVeroneseGrid : Matrix (Fin 6) (Fin 6) ℝ :=
  !![
    24275689937816271533477055266986114810143049 / 536837956648548836820082633306657146560841, 1433792318884990507064937261653031245814169600 / 57322364037695048020455490067521946427218689, 258758999594063584237374191335508759595188224 / 57322364037695048020455490067521946427218689, -(186564460089467798313559324703514702996628480 / 5547325552035004647140853877502123847795357), 79256250496506671686397832663315495020237824 / 5547325552035004647140853877502123847795357, -(609103165367191917814635986981049045986836480 / 57322364037695048020455490067521946427218689);
    145625249520341549665335795580275472151524 / 17574086306454385882010454580474853139681, 149724659599573798253563869790277094484729318225 / 4606941280719178532653748605543999901448536064, 287957565126494825919051742605508560271204 / 17574086306454385882010454580474853139681, 73830364541860647756755409539007073948175965 / 4498966094452322785794676372601562403758336, 204777665463828870160995139318504195103836 / 17574086306454385882010454580474853139681, 103819974496344561487396414495582329990491635 / 4498966094452322785794676372601562403758336;
    33187794768035867919003008680372071030625 / 155651241868514159788071296047492308766161, 133125075230244581300024221015318416408025 / 155651241868514159788071296047492308766161, 61666397583855639901935057279835075071060921169 / 163212156593519103613936647324295295156786036736, 66468997850281242449519217724772591240875 / 155651241868514159788071296047492308766161, -(45239051129495453781616736845788133734676025 / 159386871673358499622985007152632124176548864), -(90605429293883679181774788173654212126729715 / 159386871673358499622985007152632124176548864);
    38781886227773634937638985397554040844544 / 1952676256272709542445606064497205904409, 37915297052239883943842083686310248398736 / 1952676256272709542445606064497205904409, 35995492011364575376987781291665413641124 / 1952676256272709542445606064497205904409, 38346143698841585771909041178726661319872 / 1952676256272709542445606064497205904409, 37362723079260105282260049796108577460384 / 1952676256272709542445606064497205904409, 36942925874278225282786132402688675388792 / 1952676256272709542445606064497205904409;
    796351763801998159699382514223023981012964 / 867033418105829420640710056311025286156841, 95159162170273702360860676231012709388964 / 867033418105829420640710056311025286156841, 558455123238969612575337977912472126492676 / 867033418105829420640710056311025286156841, -(275281976591671983741913297800461447200964 / 867033418105829420640710056311025286156841), -(666878341525360757753368794562651698065108 / 867033418105829420640710056311025286156841), 230525750485964789782187297844766867501108 / 867033418105829420640710056311025286156841;
    7481770980735360054163738164155660176 / 1554425241690645937532177569575906926881, 555375495771392448921505857009688769476 / 1554425241690645937532177569575906926881, 82492814739489553531577983541272444950784 / 76166836842841650939076700909219439417169, -(64460780849086196073304965776313846424 / 1554425241690645937532177569575906926881), 785615903248585671310469952989245233728 / 10880976691834521562725242987031348488167, -(6768640032053827666473929296072204031072 / 10880976691834521562725242987031348488167)]

/-- Unit upper-triangular column-elimination certificate for the Veronese
determinant. -/
noncomputable def minimaxRefuterVeroneseElimination : Matrix (Fin 6) (Fin 6) ℝ :=
  !![
    1, -(13922378385163174339703520598425600 / 25169792979783041774603914862176681), 110050026448919361500799540568213812176297779003392 / 527953989494865297909290441470078796551296215985595, 7326989958503036493557542595659490059764926394561549448489478415360 / 6369254458114887748637337053303981477397891576159709349361887647229, 370870627653254696585629095007565107657593809088529659311616 / 126269584849127430196064589917643755260676567087673720076729, 7674625404155939758961952561786474619607409960383316480 / 3205325813498932742866085098791981463744413044889646999;
    0, 1, -(7355911647391850259340058031632478267634300163719168 / 13198849737371632447732261036751969913782405399639875), -(22291115482468470885678412018674752812908634156327144048291697783808 / 31846272290574438743186685266519907386989457880798546746809438236145), 1562329471480914615969799043320630694627655527307775691709952 / 631347924245637150980322949588218776303382835438368600383645, 2059956874116003390014597339303972439991376435717257472 / 3205325813498932742866085098791981463744413044889646999;
    0, 0, 1, -(1241689125999561480113815436707797049382805537456067791042919792640 / 6369254458114887748637337053303981477397891576159709349361887647229), -(1483580015734117501998432835898414202726958048423206127959040 / 126269584849127430196064589917643755260676567087673720076729), -(15459206617707356935838028356231540180613366710055811840 / 3205325813498932742866085098791981463744413044889646999);
    0, 0, 0, 1, 5855638981867089781169970697382635548030029066360339520905173 / 1262695848491274301960645899176437552606765670876737200767290, 26383979398068181084292680097104325659742442782210345855 / 12821303253995730971464340395167925854977652179558587996;
    0, 0, 0, 0, 1, -(20407897745029701840283320411099173085888335478008195575 / 12821303253995730971464340395167925854977652179558587996);
    0, 0, 0, 0, 0, 1]

/-- The lower-triangular column-reduced form of the Veronese grid. -/
noncomputable def minimaxRefuterVeroneseReduced : Matrix (Fin 6) (Fin 6) ℝ :=
  !![
    24275689937816271533477055266986114810143049 / 536837956648548836820082633306657146560841, 0, 0, 0, 0, 0;
    145625249520341549665335795580275472151524 / 17574086306454385882010454580474853139681, 12233519276099562143722654558543366968735294967407507543562763875 / 438221487588114364594548965304933801079118386928439624249114624, 0, 0, 0, 0;
    33187794768035867919003008680372071030625 / 155651241868514159788071296047492308766161, 10916927201331551203578301878120579470606465889026923985275 / 14805858073778098927399065910405064346671837564127585082851, -(5903423308707802350904310051845120146526501950023211144144913299690465088980701 / 108549711372538296362147122580023670235507688434980124808452754930967086277591040), 0, 0, 0;
    38781886227773634937638985397554040844544 / 1952676256272709542445606064497205904409, 1566045636253872077891173770757155255565168096302607801776 / 185742478937833304763178916636544885033127842766842153019, 1144709219880821219681035118737140346314102964468752061047695676425351075172 / 97401956039787389683621847249725095760378307516386435394384547989191647625, 22470633028400844083050135248706423344640712137406765362621327456140710592 / 888160687911830522108733465397973697115748990837590670221768422967847905, 0, 0;
    796351763801998159699382514223023981012964 / 867033418105829420640710056311025286156841, -(32848820163123628814670058693998963713475993584559261473876 / 82473956388615094506990714342545129049758651659544810170731), 11163726857114641839485736349160223769157997560230400519477618421801242960876 / 14416240378486351963139172218200760294504811676580093047340543231763828877875, 23517259092114821520975570030213848342843272964087569315186199915135771452 / 43818209586497796925474112672077469651073017792469263626790763542820753705, -(5941792793441909660665902924544178727374152558537281275552089623662 / 868689918059375279511204775703968272660337241381879069957268281205), 0;
    7481770980735360054163738164155660176 / 1554425241690645937532177569575906926881, 52434772109764027549216571346157634587187730714563355916 / 147860044279064763851243684902575674732707204893207452371, 3362137120533019690463902608434338588254250122314825772971940490661756782848 / 3799297948148971712142362325962429477494057924392895670599370222865436002625, -(17223598663355642027643563806723217351412244698020339964182279287534958552 / 34643935465029112612336892380498414731029094766168818279969900575752102105), -(8205311664428427160084342799421228253399608391391209719884363134556 / 686811208042692129056793340386594207582858714148793843558747829605), -(20240554066622818934964406575445684017826492062174951487110938 / 3486910480889000485394127808635758243352895986470157598215151)]

/-- The abstract Veronese grid of the minimax refuter is the explicit one. -/
theorem minimaxRefuterVeroneseGrid_eq :
    veroneseGrid minimaxRefuterAtom = minimaxRefuterVeroneseGrid := by
  ext atomIndex coordIndex
  fin_cases atomIndex <;> fin_cases coordIndex <;>
    simp [veroneseGrid, veroneseCoords, minimaxRefuterAtom,
      minimaxRefuterVeroneseGrid] <;>
    norm_num

set_option maxHeartbeats 1600000 in
/-- The column elimination, verified entrywise. -/
theorem minimaxRefuterVeronese_columnReduction :
    minimaxRefuterVeroneseGrid * minimaxRefuterVeroneseElimination
      = minimaxRefuterVeroneseReduced := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [minimaxRefuterVeroneseGrid, minimaxRefuterVeroneseElimination,
      minimaxRefuterVeroneseReduced, Matrix.mul_apply, Fin.sum_univ_six] <;>
    norm_num

/-- The elimination matrix is unit upper triangular: determinant one. -/
theorem minimaxRefuterVeroneseElimination_det :
    minimaxRefuterVeroneseElimination.det = 1 := by
  have htri : minimaxRefuterVeroneseElimination.BlockTriangular id := by
    intro rowIndex colIndex hlt
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp_all [minimaxRefuterVeroneseElimination]
  rw [Matrix.det_of_upperTriangular htri, Fin.prod_univ_six]
  simp [minimaxRefuterVeroneseElimination]

/-- The reduced form is lower triangular: determinant = diagonal product. -/
theorem minimaxRefuterVeroneseReduced_det :
    minimaxRefuterVeroneseReduced.det = -(6922596698375161564691789295437069142260313728720911871345023183923987923596760726946070848002171508729233336787076467181 / 100380553943374846977220009595490423051204470114476003425740803214051400419577716956032483519321318045517535325978624) := by
  have htri : minimaxRefuterVeroneseReducedᵀ.BlockTriangular id := by
    intro rowIndex colIndex hlt
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp_all [minimaxRefuterVeroneseReduced, Matrix.transpose_apply]
  rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular htri,
    Fin.prod_univ_six]
  simp [minimaxRefuterVeroneseReduced, Matrix.transpose_apply]
  norm_num

/-- The exact Veronese determinant of the minimax refuter. -/
theorem minimaxRefuterVeronese_det :
    (veroneseGrid minimaxRefuterAtom).det = -(6922596698375161564691789295437069142260313728720911871345023183923987923596760726946070848002171508729233336787076467181 / 100380553943374846977220009595490423051204470114476003425740803214051400419577716956032483519321318045517535325978624) := by
  have hproduct := congrArg Matrix.det minimaxRefuterVeronese_columnReduction
  rw [Matrix.det_mul, minimaxRefuterVeroneseElimination_det, mul_one,
    minimaxRefuterVeroneseReduced_det] at hproduct
  rw [minimaxRefuterVeroneseGrid_eq]
  exact hproduct

/-- **THE MINIMAX REFUTER IS OFF-CONIC** -- read off the nonvanishing exact
Veronese determinant through the landed kernel duality. -/
theorem hasNoCommonQuadric_minimaxRefuterAtom :
    HasNoCommonQuadric minimaxRefuterAtom := by
  rw [hasNoCommonQuadric_iff_veroneseGrid_det_ne_zero,
    minimaxRefuterVeronese_det]
  norm_num

/-- The base-triple subset sum, entry by entry. -/
theorem minimaxRefuter_subsetSum_baseTriple_eq :
    subsetSum minimaxRefuterDesign {0, 1, 2}
      = !![
        13136563159614857244127840290998671404838185996706 / 244540604958532515664562981151392898953776479267, -(97774282890926687316031575260104151646591702752076325 / 5822022722852742132941915455252362138291510418388736), 597472497142184546546265513684322730786138532673526897 / 23288090891410968531767661821009448553166041673554944;
        -(97774282890926687316031575260104151646591702752076325 / 5822022722852742132941915455252362138291510418388736), 10787215816774432698385657684836957595238792153680812774425 / 184814289314237446268108164211530983717925706721332035584, 8577996176277841267352151807201783173570052355898154545 / 721930817633740024484797516451292905148147291880203264;
        597472497142184546546265513684322730786138532673526897 / 23288090891410968531767661821009448553166041673554944, 8577996176277841267352151807201783173570052355898154545 / 721930817633740024484797516451292905148147291880203264, 15729383214065201417122409859085893955213794817970597420969 / 739257157256949785072432656846123934871702826885328142336] := by
  simp only [subsetSum, minimaxRefuterDesign_atom_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [minimaxRefuterAtom, atomMatrix, Matrix.add_apply] <;>
    norm_num

set_option maxHeartbeats 800000 in
/-- **THE BASE TRIPLE WEAKLY DOMINATES**: the gap above the identity is an
explicit rational sum of squares. -/
theorem minimaxRefuterDesign_dominates_baseTriple :
    Dominates minimaxRefuterDesign {0, 1, 2} := by
  have hgap : subsetSum minimaxRefuterDesign {0, 1, 2} - 1
      = !![
        12892022554656324728463277309847278505884409517439 / 244540604958532515664562981151392898953776479267, -(97774282890926687316031575260104151646591702752076325 / 5822022722852742132941915455252362138291510418388736), 597472497142184546546265513684322730786138532673526897 / 23288090891410968531767661821009448553166041673554944;
        -(97774282890926687316031575260104151646591702752076325 / 5822022722852742132941915455252362138291510418388736), 10602401527460195252117549520625426611520866446959480738841 / 184814289314237446268108164211530983717925706721332035584, 8577996176277841267352151807201783173570052355898154545 / 721930817633740024484797516451292905148147291880203264;
        597472497142184546546265513684322730786138532673526897 / 23288090891410968531767661821009448553166041673554944, 8577996176277841267352151807201783173570052355898154545 / 721930817633740024484797516451292905148147291880203264, 14990126056808251632049977202239770020342091991085269278633 / 739257157256949785072432656846123934871702826885328142336] := by
    rw [minimaxRefuter_subsetSum_baseTriple_eq]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.sub_apply] <;> norm_num
  show (subsetSum minimaxRefuterDesign {0, 1, 2} - 1).PosSemidef
  rw [hgap]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp [Matrix.transpose_apply]
  · rw [star_trivial]
    have hkey : (657442107114488822539219885177340876493476066002524823267299536116798289437133743211749099811877789480725248421921901619615930037406085977218391909646594036919738450313216 : ℝ)
          * (probeVec ⬝ᵥ ((!![
            12892022554656324728463277309847278505884409517439 / 244540604958532515664562981151392898953776479267, -(97774282890926687316031575260104151646591702752076325 / 5822022722852742132941915455252362138291510418388736), 597472497142184546546265513684322730786138532673526897 / 23288090891410968531767661821009448553166041673554944;
            -(97774282890926687316031575260104151646591702752076325 / 5822022722852742132941915455252362138291510418388736), 10602401527460195252117549520625426611520866446959480738841 / 184814289314237446268108164211530983717925706721332035584, 8577996176277841267352151807201783173570052355898154545 / 721930817633740024484797516451292905148147291880203264;
            597472497142184546546265513684322730786138532673526897 / 23288090891410968531767661821009448553166041673554944, 8577996176277841267352151807201783173570052355898154545 / 721930817633740024484797516451292905148147291880203264, 14990126056808251632049977202239770020342091991085269278633 / 739257157256949785072432656846123934871702826885328142336]
              : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ probeVec))
        = 22994272117549803687365294117039811123648649483768706795339663393 * (1227733091925031116541014824771376026672384087164750848 * probeVec 0 - 391097131563706749264126301040416606586366811008305300 * probeVec 1 + 597472497142184546546265513684322730786138532673526897 * probeVec 2) ^ 2
          + 64680448312777230883968255280405448377643716 * (22994272117549803687365294117039811123648649483768706795339663393 * probeVec 1 + 8865047648333495689068634267276268422184878052652625659609907685 * probeVec 2) ^ 2
          + 39619772760849429673801946200886662775836780553344795097265500295277516746496452221800769883654417098203107888247972218354850354586874236525840361705378386124307442958336 * probeVec 2 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    linarith [hkey, sq_nonneg (1227733091925031116541014824771376026672384087164750848 * probeVec 0 - 391097131563706749264126301040416606586366811008305300 * probeVec 1 + 597472497142184546546265513684322730786138532673526897 * probeVec 2), sq_nonneg (22994272117549803687365294117039811123648649483768706795339663393 * probeVec 1 + 8865047648333495689068634267276268422184878052652625659609907685 * probeVec 2),
      sq_nonneg (probeVec 2)]

/-- The mass clearance clears `3/8`: every design mass does. -/
theorem minimaxRefuter_massClearance_ge :
    (3 / 8 : ℝ) ≤ massClearanceOf minimaxRefuterDesign := by
  simp only [massClearanceOf]
  refine Finset.le_inf' _ _ fun label _ => ?_
  fin_cases label <;>
    simp [designMassOf, leverageOf, minimaxRefuterDesign_atom_eq,
      minimaxRefuterDesign_weight_eq, minimaxRefuterAtom,
      minimaxRefuterWeight, Fin.sum_univ_three] <;>
    norm_num

/-- The bracket clearance clears `3/8`, from the uniform squared-bracket
bound. -/
theorem minimaxRefuter_bracketClearance_ge :
    (3 / 8 : ℝ) ≤ bracketClearanceOf minimaxRefuterDesign := by
  simp only [bracketClearanceOf]
  refine Finset.le_inf' _ _ fun labels hmem => ?_
  simp only [distinctLabelTriples, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem
  obtain ⟨hfirstMid, hfirstLast, hmidLast⟩ := hmem
  have hlower := minimaxRefuterAtom_bracketSq_ge labels.1 labels.2.1 labels.2.2
    hfirstMid hfirstLast hmidLast
  simpa [atomBracket, minimaxRefuterDesign_atom_eq] using hlower

/-- The conic clearance clears `3/8` (the determinant magnitude is huge). -/
theorem minimaxRefuter_conicClearance_ge :
    (3 / 8 : ℝ) ≤ conicClearanceOf minimaxRefuterDesign := by
  simp only [conicClearanceOf, minimaxRefuterDesign_atom_eq]
  rw [minimaxRefuterVeronese_det, abs_of_neg (by norm_num)]
  norm_num

/-- **THE MINIMAX REFUTER SITS ABOVE WALL CLEARANCE `3/8`** -- deep inside
every clearance-bounded region the interior family can quantify over. -/
theorem minimaxRefuter_wallClearance_ge :
    (3 / 8 : ℝ) ≤ wallClearanceOf minimaxRefuterDesign := by
  simp only [wallClearanceOf, le_min_iff]
  exact ⟨minimaxRefuter_massClearance_ge,
    minimaxRefuter_conicClearance_ge, minimaxRefuter_bracketClearance_ge⟩

/-! ### No triple reaches the identity floor `1/16`

Each of the twenty floor-shifted gaps has an explicit rational probe with
strictly negative Rayleigh value. -/

/-- The `{0, 1, 2}` gap fails the `1/16` floor at the probe
`![3, 2, -5]`. -/
theorem minimaxRefuter_gap_zeroOneTwo_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {0, 1, 2}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {0, 1, 2}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        206027820269542663139747873976405063195196775799757 / 3912649679336520250633007698422286383260423668272, -(97774282890926687316031575260104151646591702752076325 / 5822022722852742132941915455252362138291510418388736), 597472497142184546546265513684322730786138532673526897 / 23288090891410968531767661821009448553166041673554944;
        -(97774282890926687316031575260104151646591702752076325 / 5822022722852742132941915455252362138291510418388736), 10590850634378055411725792760362205925038496090289397486617 / 184814289314237446268108164211530983717925706721332035584, 8577996176277841267352151807201783173570052355898154545 / 721930817633740024484797516451292905148147291880203264;
        597472497142184546546265513684322730786138532673526897 / 23288090891410968531767661821009448553166041673554944, 8577996176277841267352151807201783173570052355898154545 / 721930817633740024484797516451292905148147291880203264, 14943922484479692270482950161186887274412610564404936269737 / 739257157256949785072432656846123934871702826885328142336] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![3, 2, -5]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 1, 3}` gap fails the `1/16` floor at the probe
`![2, 1, -3]`. -/
theorem minimaxRefuter_gap_zeroOneThree_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {0, 1, 3}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {0, 1, 3}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        17320547135357754376705872835285634569368902578823 / 239549980367542056161204552964629778566964714384, 287160120043606770531843890240712770734073699101387 / 118816790262300859855957458270456370169214498334464, 20919947754423469974344762362427276911349378034916 / 464128086962112733812333821368970195973494134119;
        287160120043606770531843890240712770734073699101387 / 118816790262300859855957458270456370169214498334464, 286149782580021572160107289879250764163445793181466017897 / 3771720190086478495267513555337367014651545035129225216, 115544315841667355498320696471761351573798551192692027 / 3683320498131326655534681206384147475245649448368384;
        20919947754423469974344762362427276911349378034916 / 464128086962112733812333821368970195973494134119, 115544315841667355498320696471761351573798551192692027 / 3683320498131326655534681206384147475245649448368384, 8810244759429461752386694342865900459319413489676151 / 230207531133207915970917575399009217202853090523024] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![2, 1, -3]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 1, 4}` gap fails the `1/16` floor at the probe
`![3, 2, -5]`. -/
theorem minimaxRefuter_gap_zeroOneFour_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {0, 1, 4}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {0, 1, 4}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        17588353387126333297232079365695018950810525489363920335 / 329603764937131773791830019356070086593865192497662736, -(2867239265187343071881362367748097516079162779086724515149 / 163483467408817359800747689600610762950557135478840717056), 16073995814855174012445118006090498028684971066886771800 / 638607294565692811721670662502385792775613810464221551;
        -(2867239265187343071881362367748097516079162779086724515149 / 163483467408817359800747689600610762950557135478840717056), 293524038345003970826351675329348513295753872495029172218182113 / 5189619189425498269514934658681788059102485708640319722225664, 64446357036605809831790732871728355879116084705023086808483 / 5067987489673338153823178377618933651467271199844062228736;
        16073995814855174012445118006090498028684971066886771800 / 638607294565692811721670662502385792775613810464221551, 64446357036605809831790732871728355879116084705023086808483 / 5067987489673338153823178377618933651467271199844062228736, 6487356994006756522586697026436979223311088194023204942079 / 316749218104583634613948648601183353216704449990253889296] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![3, 2, -5]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 1, 5}` gap fails the `1/16` floor at the probe
`![3, 2, -5]`. -/
theorem minimaxRefuter_gap_zeroOneFive_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {0, 1, 5}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {0, 1, 5}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        278933909868706867428370057119607300733550473988134543 / 5318249114139801188834902280367745713965183624039184, -(45535584236580644800858215465311068725547985832098613581 / 2637851560613341389662111531062401874126731077523435264), 1876194543702298798277557016059348355394602048797028476 / 72128753610521053623573362177487551245652802901031433;
        -(45535584236580644800858215465311068725547985832098613581 / 2637851560613341389662111531062401874126731077523435264), 4756820122814362261290522320298411786684205201429678760153569 / 83735959940109909073434068442044885092278951324903929020416, 6770750805276699773703386443015184994338203262355482110837 / 572413788653095081556678202240541206685500643822585452288;
        1876194543702298798277557016059348355394602048797028476 / 72128753610521053623573362177487551245652802901031433, 6770750805276699773703386443015184994338203262355482110837 / 572413788653095081556678202240541206685500643822585452288, 5239018910288177069529389900571170041179931273254648736399 / 250431032535729098181046713480236777924906531672381135376] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![3, 2, -5]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 2, 3}` gap fails the `1/16` floor at the probe
`![8, 5, -13]`. -/
theorem minimaxRefuter_gap_zeroTwoThree_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {0, 2, 3}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {0, 2, 3}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        753944662244820434778096194032726796417832149652263 / 11737949038009560751899023095266859149781271004816, -(308536477997585471409639854251674853634319762523667 / 22742276261143523956804357247079539602701212571831), 771710718119092597768165659914784599122117804438129777 / 23288090891410968531767661821009448553166041673554944;
        -(308536477997585471409639854251674853634319762523667 / 22742276261143523956804357247079539602701212571831), 498839106440676258961916314321572483071571101093082967 / 11280169025527187882574961194551451642939801435628176, 5576725778681249716725330885324492127039055728424344837 / 721930817633740024484797516451292905148147291880203264;
        771710718119092597768165659914784599122117804438129777 / 23288090891410968531767661821009448553166041673554944, 5576725778681249716725330885324492127039055728424344837 / 721930817633740024484797516451292905148147291880203264, 16458347440368259101316915809995372019893107492578075959209 / 739257157256949785072432656846123934871702826885328142336] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![8, 5, -13]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 2, 4}` gap fails the `1/16` floor at the probe
`![1, 2, 2]`. -/
theorem minimaxRefuter_gap_zeroTwoFour_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {0, 2, 4}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {0, 2, 4}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        26226947157523272476626010138893721910991612024641631 / 579102315677129223557663270409388441432084134690576, -(37611914998469897603826339612453547363795294276612679 / 1122010736624437870642972586418190105274663010962991), 15205413716359264236712101723552072350495211572000049721 / 1148938994303424379538403928492226667801254923226102784;
        -(37611914998469897603826339612453547363795294276612679 / 1122010736624437870642972586418190105274663010962991), 13865808177611827985861293010234669560339461477560534287 / 556517325365721183838914402863422292216232853437643536, -(389241894202919233283403222857171198784725145049523684243 / 35617108823406155765690521783259026701838902620009186304);
        15205413716359264236712101723552072350495211572000049721 / 1148938994303424379538403928492226667801254923226102784, -(389241894202919233283403222857171198784725145049523684243 / 35617108823406155765690521783259026701838902620009186304), 163158241768420485081648503528986465623201326630334144595249 / 36471919435167903504067094306057243342683036282889406775296] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, 2, 2]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 2, 5}` gap fails the `1/16` floor at the probe
`![1, 2, 2]`. -/
theorem minimaxRefuter_gap_zeroTwoFive_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {0, 2, 5}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {0, 2, 5}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        414641871326046012246890865380210228497360015718687 / 9343978148834675257374241160960218723665029136144, -(601881562583480257386746131068773540786023262069651 / 18103957663367183311162592249360423777100993951279), 260940945736505129035415242794237567413191835028181561 / 18538452647287995710630494463345073947751417806109696;
        -(601881562583480257386746131068773540786023262069651 / 18103957663367183311162592249360423777100993951279), 225951448970633897721520543045238272849123066149519631 / 8979563001030122922336645755682770193442092999834384, -(6790819398899851031634579725157668924628238835848289171 / 574692032065927867029545328363697292380293951989400576);
        260940945736505129035415242794237567413191835028181561 / 18538452647287995710630494463345073947751417806109696, -(6790819398899851031634579725157668924628238835848289171 / 574692032065927867029545328363697292380293951989400576), 2890922522995691728173406837892757543038952460480800152881 / 588484640835510135838254416244426027397421006837146189824] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, 2, 2]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 3, 4}` gap fails the `1/16` floor at the probe
`![3, 2, -5]`. -/
theorem minimaxRefuter_gap_zeroThreeFour_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {0, 3, 4}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {0, 3, 4}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        21403360877552840137031276522466705107485620555705492367 / 329603764937131773791830019356070086593865192497662736, -(9139227546623352062617386925134249985380021211002956636 / 638607294565692811721670662502385792775613810464221551), 20851965783575999068441966027111168628925237796394868820 / 638607294565692811721670662502385792775613810464221551;
        -(9139227546623352062617386925134249985380021211002956636 / 638607294565692811721670662502385792775613810464221551), 13771349156764682518514767363226983627338888965218143699391 / 316749218104583634613948648601183353216704449990253889296, 169442582156410596926191257944855280611136896993405482636 / 19796826131536477163371790537573959576044028124390868081;
        20851965783575999068441966027111168628925237796394868820 / 638607294565692811721670662502385792775613810464221551, 169442582156410596926191257944855280611136896993405482636 / 19796826131536477163371790537573959576044028124390868081, 7136242048343864860917817582454612655929594382827470153471 / 316749218104583634613948648601183353216704449990253889296] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![3, 2, -5]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 3, 5}` gap fails the `1/16` floor at the probe
`![3, 2, -5]`. -/
theorem minimaxRefuter_gap_zeroThreeFive_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {0, 3, 5}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {0, 3, 5}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        340490124829623367008204464329200386106664773903209551 / 5318249114139801188834902280367745713965183624039184, -(48206586687532773786532250290616418308433391082262328 / 3434702552881954934455874389404169106935847757191973), 805283911512575029354117086940843236160508895936711712 / 24042917870173684541191120725829183748550934300343811;
        -(48206586687532773786532250290616418308433391082262328 / 3434702552881954934455874389404169106935847757191973), 24829964952023066417738632195514258634608903357586993543 / 567870822076483215830037899048155959013393495855739536, 1905844160012178581476760433994100962881867485419882344 / 248443484658461406925641580833568232068359654436886047;
        805283911512575029354117086940843236160508895936711712 / 24042917870173684541191120725829183748550934300343811, 1905844160012178581476760433994100962881867485419882344 / 248443484658461406925641580833568232068359654436886047, 639116230859253005371132690248327246183913316898580820439 / 27825670281747677575671857053359641991656281296931237264] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![3, 2, -5]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{0, 4, 5}` gap fails the `1/16` floor at the probe
`![1, 2, 1]`. -/
theorem minimaxRefuter_gap_zeroFourFive_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {0, 4, 5}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {0, 4, 5}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        11828266408418570978263770410757959516447227699268673223 / 262380622660162161065381270742016995678238772944193424, -(17279439338122165595112265290526612771523256375622407332 / 508362456404064187064176212062657929126587622579374759), 48361736173920911450455653198800262227141237678844732364 / 3558537194828449309449233484438605503886113358055623313;
        -(17279439338122165595112265290526612771523256375622407332 / 508362456404064187064176212062657929126587622579374759), 6156775624544226760303277034589429906240100228595440526007 / 252147778376415836783831401183078332846787460799369880464, -(1211487488161823482338650709284295621232325180661353550644 / 110314653039681928592926238017596770620469514099724322703);
        48361736173920911450455653198800262227141237678844732364 / 3558537194828449309449233484438605503886113358055623313, -(1211487488161823482338650709284295621232325180661353550644 / 110314653039681928592926238017596770620469514099724322703), 63984766632208747294318627889736567120966370481452760743111 / 12355241140444376002407738657970838309492585579169124142736] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, 2, 1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 2, 3}` gap fails the `1/16` floor at the probe
`![-2, -1, 3]`. -/
theorem minimaxRefuter_gap_oneTwoThree_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {1, 2, 3}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {1, 2, 3}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        1895989260110889758840068837395515206444006908287 / 69455319751535862437272326007496207986871426064, 40534450879590458638727843901577981438179333836477 / 1111285116024573798996357216119939327789942817024, 135588029125072709738087833805904044081107642357847 / 4445140464098295195985428864479757311159771268096;
        40534450879590458638727843901577981438179333836477 / 1111285116024573798996357216119939327789942817024, 58843325900875662892680808988782834183863613901076017 / 1137955958809163570172269789306817871656901444632576, 184149144897701876037099320205273320880601922804873 / 4445140464098295195985428864479757311159771268096;
        135588029125072709738087833805904044081107642357847 / 4445140464098295195985428864479757311159771268096, 184149144897701876037099320205273320880601922804873 / 4445140464098295195985428864479757311159771268096, 155374719964223717273097865286156970123783332506276673 / 4551823835236654280689079157227271486627605778530304] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![-2, -1, 3]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 2, 4}` gap fails the `1/16` floor at the probe
`![1, -1, 1]`. -/
theorem minimaxRefuter_gap_oneTwoFour_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {1, 2, 4}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {1, 2, 4}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        798504027375193417812546297879728056139684714545215751 / 95565588650410987667453674251168249959168014392813456, 25259984204723504472291210641722538427191805628568594581 / 1529049418406575802679258788018691999346688230285015296, 64827229225375279974363741907838478642260294823152523487 / 6116197673626303210717035152074767997386752921140061184;
        25259984204723504472291210641722538427191805628568594581 / 1529049418406575802679258788018691999346688230285015296, 50733835404302455237169096577600161497623456570778275743593 / 1565746604448333621943560998931140607331008747811855663104, 139289208341081276615936243248433521906511032480016399617 / 6116197673626303210717035152074767997386752921140061184;
        64827229225375279974363741907838478642260294823152523487 / 6116197673626303210717035152074767997386752921140061184, 139289208341081276615936243248433521906511032480016399617 / 6116197673626303210717035152074767997386752921140061184, 102367128795269239601378161628594332691724427916209124993017 / 6262986417793334487774243995724562429324034991247422652416] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, -1, 1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 2, 5}` gap fails the `1/16` floor at the probe
`![-2, 1, 0]`. -/
theorem minimaxRefuter_gap_oneTwoFive_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {1, 2, 5}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {1, 2, 5}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        11475234504046353258168283885456386088148497512587207 / 1541977553803847681969882909692423313516532530046864, 414387024256129215842453285067310029798665764760816789 / 24671640860861562911518126555078773016264520480749824, 1129035488868655201527021132610113062388203829786530015 / 98686563443446251646072506220315092065058081922999296;
        414387024256129215842453285067310029798665764760816789 / 24671640860861562911518126555078773016264520480749824, 824858294639768139309644173420137476808997193409161256809 / 25263760241522240421394561592400663568654868972287819776, 2159842609498183604083364184973300443924587387842348289 / 98686563443446251646072506220315092065058081922999296;
        1129035488868655201527021132610113062388203829786530015 / 98686563443446251646072506220315092065058081922999296, 2159842609498183604083364184973300443924587387842348289 / 98686563443446251646072506220315092065058081922999296, 1696080976022087022378410917300440836296212674069393326073 / 101055040966088961685578246369602654274619475889151279104] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![-2, 1, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 3, 4}` gap fails the `1/16` floor at the probe
`![-1, -2, 3]`. -/
theorem minimaxRefuter_gap_oneThreeFour_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {1, 3, 4}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {1, 3, 4}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        10834201076359944535577018051756674399947170461783 / 386891119960855627395980204167330947290050218384, 221182600795596946815992098497722722976257091134261 / 6190257919373690038335683266677295156640803494144, 725837046230689303926997271239001275346086437256 / 24180694997553476712248762760458184205628138649;
        221182600795596946815992098497722722976257091134261 / 6190257919373690038335683266677295156640803494144, 323052742041178267373682756374616766286618282937093001 / 6338824109438658599255739665077550240400182778003456, 261609034047879999378197476531278388647942228130459 / 6190257919373690038335683266677295156640803494144;
        725837046230689303926997271239001275346086437256 / 24180694997553476712248762760458184205628138649, 261609034047879999378197476531278388647942228130459 / 6190257919373690038335683266677295156640803494144, 13309393649174201493684400382531328169200555678871 / 386891119960855627395980204167330947290050218384] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![-1, -2, 3]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 3, 5}` gap fails the `1/16` floor at the probe
`![-5, -1, 6]`. -/
theorem minimaxRefuter_gap_oneThreeFive_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {1, 3, 5}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {1, 3, 5}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        169109225098625073419309791198329119779834017559 / 6242596641433501135464225634257955432864926096, 3596413499096040094210614012401832028216839309109 / 99881546262936018167427610148127286925838817536, 84278931384275728111596058912715646267885869572 / 2731136030627156746765598714987855501878405167;
        3596413499096040094210614012401832028216839309109 / 99881546262936018167427610148127286925838817536, 5237863993844311056428584350716700282997388889547657 / 102278703373246482603445872791682341812058949156864, 28927123414098395295381543247354536021167919318589 / 699170823840552127171993271036891008480871722752;
        84278931384275728111596058912715646267885869572 / 2731136030627156746765598714987855501878405167, 28927123414098395295381543247354536021167919318589 / 699170823840552127171993271036891008480871722752, 10657059902905086186186432194543887816305408272551 / 305887235430241555637747056078639816210381378704] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![-5, -1, 6]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{1, 4, 5}` gap fails the `1/16` floor at the probe
`![-6, 5, -3]`. -/
theorem minimaxRefuter_gap_oneFourFive_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {1, 4, 5}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {1, 4, 5}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        69978921908855879728118359917376320415134252024449503 / 8589369754250955783818156512718914360786404898343184, 2205963197466299779375272678400675151458269447937369933 / 137429916068015292541090504203502629772582478373490944, 41168375020321598188679695311938585565726881571224536 / 3757849267484793155420443474314525032844052143025143;
        2205963197466299779375272678400675151458269447937369933 / 137429916068015292541090504203502629772582478373490944, 4489841004656144387629933985195733357378732757133467671553 / 140728234053647659562076676304386692887124457854454726656, 21857069663294567966779235517337641839124577544757775381 / 962009412476107047787633529424518408408077348614436608;
        41168375020321598188679695311938585565726881571224536 / 3757849267484793155420443474314525032844052143025143, 21857069663294567966779235517337641839124577544757775381 / 962009412476107047787633529424518408408077348614436608, 7175990447434090471046912990387168795621162911759893679 / 420879117958296833407089669123226803678533840018816016] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![-6, 5, -3]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{2, 3, 4}` gap fails the `1/16` floor at the probe
`![1, -1, 0]`. -/
theorem minimaxRefuter_gap_twoThreeFour_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {2, 3, 4}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {2, 3, 4}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        1904630459510689483789828313748441793873883875792180423 / 95565588650410987667453674251168249959168014392813456, 117947508244866418164135500410649937138625169844331039 / 5972849290650686729215854640698015622448000899550841, 110587760080602635960181234998644580577296680282171091167 / 6116197673626303210717035152074767997386752921140061184;
        117947508244866418164135500410649937138625169844331039 / 5972849290650686729215854640698015622448000899550841, 1846291224734498495729917644509614373284798835848551751 / 95565588650410987667453674251168249959168014392813456, 113862446419668789526782248800972487158668562797650203669 / 6116197673626303210717035152074767997386752921140061184;
        110587760080602635960181234998644580577296680282171091167 / 6116197673626303210717035152074767997386752921140061184, 113862446419668789526782248800972487158668562797650203669 / 6116197673626303210717035152074767997386752921140061184, 115197336573968695117898474672818541986555592801679387846649 / 6262986417793334487774243995724562429324034991247422652416] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, -1, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{2, 3, 5}` gap fails the `1/16` floor at the probe
`![-1, 1, 0]`. -/
theorem minimaxRefuter_gap_twoThreeFive_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {2, 3, 5}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {2, 3, 5}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        29322894463128651952913171182912369421181637724650375 / 1541977553803847681969882909692423313516532530046864, 1929718053186646436212990667448614477867388720822091 / 96373597112740480123117681855776457094783283127929, 1867394477971219745366953399543207916163175353444851935 / 98686563443446251646072506220315092065058081922999296;
        1929718053186646436212990667448614477867388720822091 / 96373597112740480123117681855776457094783283127929, 30172118382446703107809531453762959970761962988206407 / 1541977553803847681969882909692423313516532530046864, 1749574680399168592504781401466242716064464758391110677 / 98686563443446251646072506220315092065058081922999296;
        1867394477971219745366953399543207916163175353444851935 / 98686563443446251646072506220315092065058081922999296, 1749574680399168592504781401466242716064464758391110677 / 98686563443446251646072506220315092065058081922999296, 1903099974019008819885598766306328255308782866006859071481 / 101055040966088961685578246369602654274619475889151279104] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![-1, 1, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{2, 4, 5}` gap fails the `1/16` floor at the probe
`![1, 0, 1]`. -/
theorem minimaxRefuter_gap_twoFourFive_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {2, 4, 5}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {2, 4, 5}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        5630368701658433380176734250031483474262679886036927 / 76074855090816247882862025244726821232152070261925904, 323651529701671367708628979648221725041584970231423 / 4754678443176015492678876577795426327009504391370369, -(4775214465424402730137633549827504891903499546995244649 / 4868790725812239864503169615662516558857732496763257856);
        323651529701671367708628979648221725041584970231423 / 4754678443176015492678876577795426327009504391370369, 19765560377079019480035876964182563884376104481625727 / 76074855090816247882862025244726821232152070261925904, -(4501904854185803562736298288215779102598250731118643203 / 4868790725812239864503169615662516558857732496763257856);
        -(4775214465424402730137633549827504891903499546995244649 / 4868790725812239864503169615662516558857732496763257856), -(4501904854185803562736298288215779102598250731118643203 / 4868790725812239864503169615662516558857732496763257856), 5197444938691971518873946048793690568505925981059197475841 / 4985641703231733621251245686438416956270318076685576044544] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, 0, 1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- The `{3, 4, 5}` gap fails the `1/16` floor at the probe
`![1, -1, 0]`. -/
theorem minimaxRefuter_gap_threeFourFive_not_posSemidef :
    ¬ (subsetSum minimaxRefuterDesign {3, 4, 5}
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef := by
  have hgap : subsetSum minimaxRefuterDesign {3, 4, 5}
      - (1 + (1 / 16 : ℝ) • 1)
      = !![
        169396809191668037021017153217625759469731273099972511 / 8589369754250955783818156512718914360786404898343184, 10349530019864253316172096338470035852606402604012100 / 536835609640684736488634782044932147549150306146449, 69284074762261976435303312568653010237097501682065396 / 3757849267484793155420443474314525032844052143025143;
        10349530019864253316172096338470035852606402604012100 / 536835609640684736488634782044932147549150306146449, 161665961851262164799107310602903218823395619358043103 / 8589369754250955783818156512718914360786404898343184, 69756737149830736551478980177087254985455902278472180 / 3757849267484793155420443474314525032844052143025143;
        69284074762261976435303312568653010237097501682065396 / 3757849267484793155420443474314525032844052143025143, 69756737149830736551478980177087254985455902278472180 / 3757849267484793155420443474314525032844052143025143, 8038193583908925691629818558693190008088073319967054511 / 420879117958296833407089669123226803678533840018816016] := by
    simp only [subsetSum, minimaxRefuterDesign_atom_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [minimaxRefuterAtom, atomMatrix, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply] <;>
      norm_num
  intro hpsd
  rw [hgap] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, -1, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  norm_num at hvalue

/-- **THE RECTANGLE REFUTATION.**  No constant pair with clearance floor at
most `3/8` and margin floor at least `1/16` survives: the minimax refuter
sits inside every such region and defeats every triple.  With the landed
`(1/16, 1/4)` refuter this shows the constant-pair landscape is empty on
the whole observed rectangle; the float-side records (margins near `10^-4`
at wall clearance up to `0.41`) say the true envelope is far lower still. -/
theorem baseTripleClearanceBoundedFloor_rectangle_refuted
    {clearanceFloor marginFloor : ℝ} (hclearance : clearanceFloor ≤ 3 / 8)
    (hmargin : (1 / 16 : ℝ) ≤ marginFloor) :
    ¬ BaseTripleClearanceBoundedFloor clearanceFloor marginFloor := by
  intro hbase
  obtain ⟨selected, hcard, hfloor⟩ :=
    hbase minimaxRefuterDesign minimaxRefuterDesign_hasLinePattern_lineFree
      hasNoCommonQuadric_minimaxRefuterAtom
      minimaxRefuterDesign_dominates_baseTriple
      (le_trans hclearance minimaxRefuter_wallClearance_ge)
  have hfloorSixteenth : (subsetSum minimaxRefuterDesign selected
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef :=
    posSemidef_identityFloor_of_le hfloor hmargin
  have hpow : selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  rcases cardThreeFinsetsOfSix_enumeration selected hpow with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact minimaxRefuter_gap_zeroOneTwo_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroOneThree_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroOneFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroOneFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroTwoThree_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroTwoFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroTwoFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroThreeFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroThreeFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroFourFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneTwoThree_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneTwoFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneTwoFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneThreeFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneThreeFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneFourFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_twoThreeFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_twoThreeFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_twoFourFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_threeFourFive_not_posSemidef hfloorSixteenth

/-- The unpinned clearance-bounded Prop falls on the same rectangle. -/
theorem clearanceBoundedInteriorFloor_rectangle_refuted
    {clearanceFloor marginFloor : ℝ} (hclearance : clearanceFloor ≤ 3 / 8)
    (hmargin : (1 / 16 : ℝ) ≤ marginFloor) :
    ¬ ClearanceBoundedInteriorFloor clearanceFloor marginFloor := by
  intro hbounded
  refine baseTripleClearanceBoundedFloor_rectangle_refuted
    hclearance hmargin ?_
  intro design hlineFree hoffConic hdominates hclearanceLe
  exact hbounded design hlineFree hoffConic
    ⟨{0, 1, 2}, by decide, hdominates⟩ hclearanceLe

/-- **THE GRADED ROUTE IS OBSTRUCTED.**  No monotone clearance-graded floor
through `Gtz.InteriorFamilyMarginFloor wallClearanceOf` can reach `1/16` by
clearance `3/8`: the minimax refuter's wall clearance is at least `3/8`,
so a monotone floor would demand a triple at floor `1/16` there, and no
triple reaches it. -/
theorem interiorFamilyMarginFloor_monotoneGraded_refuted
    (floorOf : ℝ → ℝ) (hmonotone : Monotone floorOf)
    (hreaches : (1 / 16 : ℝ) ≤ floorOf (3 / 8)) :
    ¬ InteriorFamilyMarginFloor wallClearanceOf floorOf := by
  intro hinterior
  obtain ⟨selected, hcard, hfloor⟩ :=
    hinterior minimaxRefuterDesign
      minimaxRefuterDesign_hasLinePattern_lineFree
      hasNoCommonQuadric_minimaxRefuterAtom
      ⟨{0, 1, 2}, by decide, minimaxRefuterDesign_dominates_baseTriple⟩
      (lt_of_lt_of_le (by norm_num) minimaxRefuter_wallClearance_ge)
  have hreachesWall : (1 / 16 : ℝ)
      ≤ floorOf (wallClearanceOf minimaxRefuterDesign) :=
    le_trans hreaches (hmonotone minimaxRefuter_wallClearance_ge)
  have hfloorSixteenth : (subsetSum minimaxRefuterDesign selected
      - (1 + (1 / 16 : ℝ) • 1)).PosSemidef :=
    posSemidef_identityFloor_of_le hfloor hreachesWall
  have hpow : selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  rcases cardThreeFinsetsOfSix_enumeration selected hpow with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact minimaxRefuter_gap_zeroOneTwo_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroOneThree_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroOneFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroOneFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroTwoThree_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroTwoFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroTwoFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroThreeFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroThreeFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_zeroFourFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneTwoThree_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneTwoFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneTwoFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneThreeFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneThreeFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_oneFourFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_twoThreeFour_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_twoThreeFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_twoFourFive_not_posSemidef hfloorSixteenth
  · exact minimaxRefuter_gap_threeFourFive_not_posSemidef hfloorSixteenth

end Gtz
