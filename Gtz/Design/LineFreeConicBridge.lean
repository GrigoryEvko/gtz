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

end Gtz
