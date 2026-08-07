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
verbatim into `Gtz.lineFreeOffConicWeakToStrict_of_twoFamilies`.  Scan-verified
constants (exact rationals, 1371 adjudicated points, zero failures):
`clearanceFloor = 1/16`, `marginFloor = 1/4`. -/
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
per-cell certificates are built against. -/
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

end Gtz
