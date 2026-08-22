/-
# Coplanar atoms, the shadow-class pigeonhole, and the pair-normal Gram
# trichotomy of `(6,3)`

Two things live here.  The first is the COPLANAR BRIDGE, which the campaign's
sharp duality needs: a `(6,3)` tie with four coplanar atoms has a parallel pair.
The second is what the same mechanism gives when the plane is chosen to be the
plane of a PAIR rather than of four atoms, and that second reading is a statement
about the Gram matrix of a `(6,3)` design alone.

## What the tree already owns, and this module therefore does not repeat

* `Gtz.oneLine_normalIdentity` and `Gtz.oneLine_crossIdentity`
  (`Gtz/Design/InPlaneRestriction.lean`) are the two Parseval readings at a
  normal that the coplanar atoms kill — identities (A) and (B) of the two-plane
  structure, in general form.  Part 1 only specialises them.
* `Gtz.inPlaneRestriction_eq_planarCompressionDesign`
  (`Gtz/Design/SphereDichotomy.lean`) proves by `rfl` that the tree's two shadow
  constructions are ONE object.  There is nothing to choose between them.
* `Gtz.posDef_tripleGap_iff_flatPairFires`
  (`Gtz/Design/OneLineLiftCertificate.lean`) is the strict-domination criterion
  at a pair flat against the normal, in basis-free shadow-Gram vocabulary.
  Part 2 lands the FRAME form of the same law, because the frame form is the one
  Parseval sums: `Gtz.sum_weight_mul_frameAlpha` averages the plane adjugate and
  there is no basis-free sibling of that averaging law.
* `Gtz.sixThree_planeShadow_trichotomy`
  (`Gtz/Wave/RankTwoTieClassification.lean`) splits every plane of a `(6,3)`
  design into light shadow, strict shadow pair, or three rigid classes.  Parts 3
  and 5 turn the third alternative into geometry the rank-three lane can spend.
* `Gtz.crossNormSq_le_of_isTie` (`Gtz/Wave/PlaneShadowPairBridge.lean`) is the
  area ceiling.  Summing the domination gate over the WHOLE complement of a pair
  reproduces it exactly.  Part 4 sums over the two OFF-PLANE atoms only, which is
  strictly stronger and is available only under coplanarity.

## Part 1 — the two-plane structure

Call an atom FLAT at a frame when it reads zero against the axis.  With four flat
atoms and two off-plane atoms `1`, `2` of heights `alpha_i` and shadows `q_i`,
the two Parseval readings say

    (A)   t_1 alpha_1^2 + t_2 alpha_2^2 = 1
    (B)   t_1 alpha_1 q_1 + t_2 alpha_2 q_2 = 0

and nothing else, because the four flat atoms contribute to neither.  Three
consequences follow.

* If one off-plane shadow vanishes, either the two off-plane atoms are PARALLEL
  or the other one is flat as well.  The disjunction is not removable: its second
  branch is the five-coplanar configuration.
* If both heights are nonzero the two shadows are PARALLEL, so the two off-plane
  atoms and the axis are COPLANAR.  The six atoms then occupy TWO PLANES meeting
  in the axis.
* If one height vanishes — five coplanar atoms — the sixth atom is a pure SPIKE
  along the axis with `alpha^2 = 1/t`, and every triple through the spike is
  BLOCK DIAGONAL: its gap determinant is the planar pair minor times `1/t - 1`.

## Part 2 — the coplanar determinant law

For a flat pair the frame readings of its gap satisfy `dd = ee = 0` and
`ff = -1`, so the rank-one insertion of a third atom collapses to a bare
polynomial identity,

    det(gap of the triple) = frameBlockDet * (alpha^2 - 1) - frameAlpha(q),

with `frameBlockDet` the pair minor and `frameAlpha` the plane adjugate form.
This is Sherman-Morrison with the inverse cleared: `frameAlpha / frameBlockDet`
is `q^T A^{-1} q`.  Strict domination is the strict inequality, and at a tie the
reverse inequality holds at every atom.

## Part 3 — the shadow-class pigeonhole

The plane shadow of a rank-three design is a rank-two design, and a rank-two
design that is heavy with no strictly dominating pair has exactly THREE parallel
classes (`Gtz.card_image_tieClass_eq_three`, which consumes heaviness and
no-strict-pair, not `Gtz.IsTie`).  A FLAT atom IS its own shadow.  So four flat
atoms distributed among three classes must repeat, and the repeat is a parallel
pair of the design itself.

## Part 4 — the coplanar wall, and the two residues

What the pigeonhole misses is exactly the first two alternatives of the landed
plane trichotomy, and under coplanarity only the two OFF-PLANE shadows can be
light.  Against the second residue Part 4 lands the COPLANAR WALL

    frameBlockDet * (1 - t_1 - t_2) <= t_1 frameAlpha(q_1) + t_2 frameAlpha(q_2),

the pair minor times the total coplanar weight against the weighted
plane-adjugate energy of the two off-plane shadows.  Divided by the pair minor it
reads `1 - t_1 - t_2 <= t_1 s_1 + t_2 s_2` with `s_i = q_i^T A^{-1} q_i`.  It
strengthens the landed area ceiling by `(t_c + t_d) pairGapMinor`, where `c`, `d`
are the coplanar atoms outside the pair.  It is a wall and not a kill.

## Part 5 — the pair-normal Gram trichotomy

Now put the axis along the normal of a PAIR instead of a plane of four.  Every
quantity the shadow trichotomy mentions then becomes a polynomial in the Gram
matrix of the six atoms, because the normal itself is `g_a x g_b` and

    (g_p x g_q) . (g_a x g_b) = (g_p.g_a)(g_q.g_b) - (g_p.g_b)(g_q.g_a)

is Binet-Cauchy.  Writing `X = crossNormSq(g_a, g_b)`, `[abc]` for the triple
bracket and `gramWedge` for the four-atom minor above:

* the shadow is LIGHT at `c` exactly when `X (l_c - 1) < [abc]^2`;
* the shadow pair `{p,q}` dominates STRICTLY exactly when
  `gramWedge(p,q,a,b)^2 + [abp]^2 + [abq]^2 > X (l_p + l_q - 1)`;
* otherwise at least THREE of the fifteen pairs `{c,d}` satisfy
  `gramWedge(c,d,a,b) = 0`.

`Gtz.pairNormal_gram_trichotomy` is that statement, and it holds at EVERY
rank-three design of six atoms with no tie hypothesis at all.  The `(6,3)`
capstone `Gtz.hingeHoldsAtSize_six_three_of_pairNormalGramResidue` reduces the
hinge — and through `Gtz.gtzWeightedAll_three_of_hinge` the whole of weighted GTZ
at rank three — to refuting one named residue in which all three Gram
alternatives are simultaneously pinned at every one of the fifteen pairs.
-/
import Gtz.Wave.PlaneShadowPairBridge
import Gtz.Wave.RankTwoTieClassification
import Gtz.Wave.UnitAtomFunnelClosure
import Gtz.Design.SphereDichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {size : ℕ}

/-! ## Part 0 — the shadow of a frame, flatness, and the flat readback -/

/-- The plane shadow of a rank-three design at an axis frame: the tree's
`Gtz.inPlaneRestriction` along the frame's plane.  By
`Gtz.inPlaneRestriction_eq_planarCompressionDesign` this is also the tree's
`Gtz.planarCompressionDesign`, so both vocabularies apply to it. -/
noncomputable def frameShadow (design : WeightedDesign size 3) (frame : AxisFrame) :
    WeightedDesign size 2 :=
  inPlaneRestriction design frame.pOne frame.pTwo frame.oneOne frame.twoTwo frame.oneTwo

theorem frameShadow_atom (design : WeightedDesign size 3) (frame : AxisFrame)
    (label : Fin size) :
    (frameShadow design frame).atom label
      = ![design.atom label ⬝ᵥ frame.pOne, design.atom label ⬝ᵥ frame.pTwo] := rfl

theorem frameShadow_weight (design : WeightedDesign size 3) (frame : AxisFrame)
    (label : Fin size) :
    (frameShadow design frame).weight label = design.weight label := rfl

/-- **The shadow leverage.**  Compression spends exactly the atom's axis mass. -/
theorem leverageOf_frameShadow_atom (design : WeightedDesign size 3) (frame : AxisFrame)
    (label : Fin size) :
    leverageOf ((frameShadow design frame).atom label)
      = leverageOf (design.atom label) - (design.atom label ⬝ᵥ frame.axis) ^ 2 := by
  have hsplit := frame.dotProduct_self_split (design.atom label)
  have hlev : leverageOf (design.atom label) = design.atom label ⬝ᵥ design.atom label :=
    leverageOf_eq_dotProduct _
  rw [frameShadow, leverageOf_inPlaneRestriction_atom, hlev, hsplit]
  ring

/-- A flat atom keeps its whole leverage in the shadow. -/
theorem leverageOf_frameShadow_atom_of_flat (design : WeightedDesign size 3)
    (frame : AxisFrame) {label : Fin size} (hflat : design.atom label ⬝ᵥ frame.axis = 0) :
    leverageOf ((frameShadow design frame).atom label) = leverageOf (design.atom label) := by
  rw [leverageOf_frameShadow_atom, hflat]
  ring

/-- The shadow wedge of two atoms, in raw frame readings. -/
theorem planeWedge_frameShadow (design : WeightedDesign size 3) (frame : AxisFrame)
    (labelFirst labelSecond : Fin size) :
    planeWedge ((frameShadow design frame).atom labelFirst)
        ((frameShadow design frame).atom labelSecond)
      = (design.atom labelFirst ⬝ᵥ frame.pOne) * (design.atom labelSecond ⬝ᵥ frame.pTwo)
        - (design.atom labelFirst ⬝ᵥ frame.pTwo)
          * (design.atom labelSecond ⬝ᵥ frame.pOne) := by
  rw [frameShadow, planeWedge_inPlaneRestriction]

/-- The shadow wedge is the triple bracket against the axis, up to the frame's
sign.  The dictionary is the tree's `Gtz.SphereDichotomy` bridge. -/
theorem sq_planeWedge_frameShadow (design : WeightedDesign size 3) (frame : AxisFrame)
    (labelFirst labelSecond : Fin size) :
    planeWedge ((frameShadow design frame).atom labelFirst)
          ((frameShadow design frame).atom labelSecond) ^ 2
      = tripleBracket (design.atom labelFirst) (design.atom labelSecond) frame.axis ^ 2 := by
  have hbridge := pairBracket_inPlaneRestriction_eq_frameOrientation_mul_tripleBracket
    design frame.pOne frame.pTwo frame.axis frame.oneOne frame.twoTwo frame.oneTwo
    frame.axisAxis frame.oneAxis frame.twoAxis labelFirst labelSecond
  have hsign := frameOrientation_sq_eq_one frame.pOne frame.pTwo frame.axis frame.oneOne
    frame.twoTwo frame.oneTwo frame.axisAxis frame.oneAxis frame.twoAxis
  have hwedge : planeWedge ((frameShadow design frame).atom labelFirst)
      ((frameShadow design frame).atom labelSecond)
      = pairBracket (frameShadow design frame) labelFirst labelSecond := rfl
  rw [hwedge, frameShadow, hbridge, mul_pow, hsign, one_mul]

/-- **A FLAT ATOM IS ITS OWN SHADOW.**  Frame completeness rebuilds a flat atom
from its two plane readings, so two flat atoms with parallel shadows are parallel
in `ℝ³`.  Nonvanishing of the first atom is what fixes the direction of the
scalar, and heaviness supplies it. -/
theorem exists_smul_of_flat_of_planeWedge_eq_zero (design : WeightedDesign size 3)
    (frame : AxisFrame) {labelFirst labelSecond : Fin size}
    (hheavy : 1 ≤ leverageOf (design.atom labelFirst))
    (hfirstFlat : design.atom labelFirst ⬝ᵥ frame.axis = 0)
    (hsecondFlat : design.atom labelSecond ⬝ᵥ frame.axis = 0)
    (hwedge : planeWedge ((frameShadow design frame).atom labelFirst)
      ((frameShadow design frame).atom labelSecond) = 0) :
    ∃ ratio : ℝ, design.atom labelSecond = ratio • design.atom labelFirst := by
  classical
  have hresolveFirst := orthonormalFrame_resolution frame.oneOne frame.twoTwo frame.axisAxis
    frame.oneTwo frame.oneAxis frame.twoAxis (design.atom labelFirst)
  have hresolveSecond := orthonormalFrame_resolution frame.oneOne frame.twoTwo frame.axisAxis
    frame.oneTwo frame.oneAxis frame.twoAxis (design.atom labelSecond)
  rw [hfirstFlat, zero_smul, add_zero] at hresolveFirst
  rw [hsecondFlat, zero_smul, add_zero] at hresolveSecond
  have hshadowHeavy : 1 ≤ leverageOf ((frameShadow design frame).atom labelFirst) := by
    rw [leverageOf_frameShadow_atom_of_flat design frame hfirstFlat]
    exact hheavy
  have hshadowNe : (frameShadow design frame).atom labelFirst ≠ 0 := by
    intro hzero
    rw [hzero] at hshadowHeavy
    simp only [leverageOf, Pi.zero_apply] at hshadowHeavy
    norm_num at hshadowHeavy
  obtain ⟨ratio, hratio⟩ := exists_smul_of_planeWedge_eq_zero hshadowNe hwedge
  refine ⟨ratio, ?_⟩
  have hsecondOne : design.atom labelSecond ⬝ᵥ frame.pOne
      = ratio * (design.atom labelFirst ⬝ᵥ frame.pOne) := by
    have hentry := congrFun hratio 0
    simpa [frameShadow_atom] using hentry
  have hsecondTwo : design.atom labelSecond ⬝ᵥ frame.pTwo
      = ratio * (design.atom labelFirst ⬝ᵥ frame.pTwo) := by
    have hentry := congrFun hratio 1
    simpa [frameShadow_atom] using hentry
  rw [hresolveSecond, hsecondOne, hsecondTwo]
  conv_rhs => rw [hresolveFirst]
  module

/-! ## Part 1 — the two-plane structure

Two Parseval readings and three consequences.  The readings are the tree's
`Gtz.oneLine_normalIdentity` and `Gtz.oneLine_crossIdentity` specialised to a
complement of exactly two labels. -/

/-- **(A) THE AXIS MASS SITS ON THE TWO OFF-PLANE ATOMS.**  At a frame whose axis
every atom outside a named pair kills, the pair's weighted squared heights total
one. -/
theorem twoOffPlane_axisMass_eq_one (design : WeightedDesign size 3) (frame : AxisFrame)
    (flatSet : Finset (Fin size)) {offFirst offSecond : Fin size}
    (hne : offFirst ≠ offSecond) (hcompl : flatSetᶜ = {offFirst, offSecond})
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ frame.axis = 0) :
    design.weight offFirst * (design.atom offFirst ⬝ᵥ frame.axis) ^ 2
        + design.weight offSecond * (design.atom offSecond ⬝ᵥ frame.axis) ^ 2 = 1 := by
  have hidentity := oneLine_normalIdentity design flatSet frame.axis frame.axisAxis hflat
  rw [hcompl, Finset.sum_pair hne] at hidentity
  exact hidentity

/-- **(B) THE TWO OFF-PLANE HEIGHT-SHADOW READINGS CANCEL.**  Against every probe
of the plane the pair's weighted height-times-reading total vanishes. -/
theorem twoOffPlane_crossReading_eq_zero (design : WeightedDesign size 3)
    (frame : AxisFrame) (flatSet : Finset (Fin size)) {offFirst offSecond : Fin size}
    (hne : offFirst ≠ offSecond) (hcompl : flatSetᶜ = {offFirst, offSecond})
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ frame.axis = 0)
    {probe : Fin 3 → ℝ} (hprobeFlat : probe ⬝ᵥ frame.axis = 0) :
    design.weight offFirst * ((design.atom offFirst ⬝ᵥ frame.axis)
          * (design.atom offFirst ⬝ᵥ probe))
        + design.weight offSecond * ((design.atom offSecond ⬝ᵥ frame.axis)
          * (design.atom offSecond ⬝ᵥ probe)) = 0 := by
  have hidentity := oneLine_crossIdentity design flatSet frame.axis probe hprobeFlat hflat
  rw [hcompl, Finset.sum_pair hne] at hidentity
  exact hidentity

/-- **(b) THE TWO-PLANE STRUCTURE.**  If both off-plane atoms have nonzero height
then their SHADOWS are parallel: the cross identity read at the two plane
directions is a two by two homogeneous system whose coefficients are the weighted
heights. -/
theorem planeWedge_frameShadow_offPlane_eq_zero (design : WeightedDesign size 3)
    (frame : AxisFrame) (flatSet : Finset (Fin size)) {offFirst offSecond : Fin size}
    (hne : offFirst ≠ offSecond) (hcompl : flatSetᶜ = {offFirst, offSecond})
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ frame.axis = 0)
    (hheightSecond : design.atom offSecond ⬝ᵥ frame.axis ≠ 0) :
    planeWedge ((frameShadow design frame).atom offFirst)
      ((frameShadow design frame).atom offSecond) = 0 := by
  have hcrossOne := twoOffPlane_crossReading_eq_zero design frame flatSet hne hcompl hflat
    frame.oneAxis
  have hcrossTwo := twoOffPlane_crossReading_eq_zero design frame flatSet hne hcompl hflat
    frame.twoAxis
  have hcoeff : design.weight offSecond * (design.atom offSecond ⬝ᵥ frame.axis) ≠ 0 :=
    mul_ne_zero (design.weight_pos offSecond).ne' hheightSecond
  rw [planeWedge_frameShadow]
  refine mul_left_cancel₀ hcoeff ?_
  rw [mul_zero]
  linear_combination (design.atom offFirst ⬝ᵥ frame.pOne) * hcrossTwo
    - (design.atom offFirst ⬝ᵥ frame.pTwo) * hcrossOne

/-- **(b) FRAME FREE.**  The two off-plane atoms and the axis are COPLANAR: the
six atoms occupy two planes meeting in the axis. -/
theorem tripleBracket_offPlane_axis_eq_zero (design : WeightedDesign size 3)
    (frame : AxisFrame) (flatSet : Finset (Fin size)) {offFirst offSecond : Fin size}
    (hne : offFirst ≠ offSecond) (hcompl : flatSetᶜ = {offFirst, offSecond})
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ frame.axis = 0)
    (hheightSecond : design.atom offSecond ⬝ᵥ frame.axis ≠ 0) :
    tripleBracket (design.atom offFirst) (design.atom offSecond) frame.axis = 0 := by
  have hwedge := planeWedge_frameShadow_offPlane_eq_zero design frame flatSet hne hcompl
    hflat hheightSecond
  have hsq := sq_planeWedge_frameShadow design frame offFirst offSecond
  rw [hwedge] at hsq
  have hzero : tripleBracket (design.atom offFirst) (design.atom offSecond) frame.axis ^ 2
      = 0 := by linarith [hsq]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero

/-- **(a) A VANISHING OFF-PLANE SHADOW.**  If the first off-plane atom has no
shadow then either the two off-plane atoms are PARALLEL, or the second one is
flat as well and the configuration has FIVE coplanar atoms.  The disjunction is
not removable. -/
theorem parallel_or_flat_of_offPlane_shadow_eq_zero (design : WeightedDesign size 3)
    (frame : AxisFrame) (flatSet : Finset (Fin size)) {offFirst offSecond : Fin size}
    (hne : offFirst ≠ offSecond) (hcompl : flatSetᶜ = {offFirst, offSecond})
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ frame.axis = 0)
    (hheavyFirst : 1 ≤ leverageOf (design.atom offFirst))
    (hshadowOne : design.atom offFirst ⬝ᵥ frame.pOne = 0)
    (hshadowTwo : design.atom offFirst ⬝ᵥ frame.pTwo = 0) :
    (∃ ratio : ℝ, design.atom offSecond = ratio • design.atom offFirst)
      ∨ design.atom offSecond ⬝ᵥ frame.axis = 0 := by
  classical
  by_cases hheight : design.atom offSecond ⬝ᵥ frame.axis = 0
  · exact Or.inr hheight
  refine Or.inl ?_
  have hcrossOne := twoOffPlane_crossReading_eq_zero design frame flatSet hne hcompl hflat
    frame.oneAxis
  have hcrossTwo := twoOffPlane_crossReading_eq_zero design frame flatSet hne hcompl hflat
    frame.twoAxis
  rw [hshadowOne, mul_zero, mul_zero, zero_add] at hcrossOne
  rw [hshadowTwo, mul_zero, mul_zero, zero_add] at hcrossTwo
  have hcoeff : design.weight offSecond * (design.atom offSecond ⬝ᵥ frame.axis) ≠ 0 :=
    mul_ne_zero (design.weight_pos offSecond).ne' hheight
  have hsecondOne : design.atom offSecond ⬝ᵥ frame.pOne = 0 := by
    refine mul_left_cancel₀ hcoeff ?_
    rw [mul_zero]
    linear_combination hcrossOne
  have hsecondTwo : design.atom offSecond ⬝ᵥ frame.pTwo = 0 := by
    refine mul_left_cancel₀ hcoeff ?_
    rw [mul_zero]
    linear_combination hcrossTwo
  -- both atoms are multiples of the axis, so the pair is parallel
  have hresolveFirst := orthonormalFrame_resolution frame.oneOne frame.twoTwo frame.axisAxis
    frame.oneTwo frame.oneAxis frame.twoAxis (design.atom offFirst)
  have hresolveSecond := orthonormalFrame_resolution frame.oneOne frame.twoTwo frame.axisAxis
    frame.oneTwo frame.oneAxis frame.twoAxis (design.atom offSecond)
  rw [hshadowOne, hshadowTwo, zero_smul, zero_smul, zero_add, zero_add] at hresolveFirst
  rw [hsecondOne, hsecondTwo, zero_smul, zero_smul, zero_add, zero_add] at hresolveSecond
  have hfirstHeight : design.atom offFirst ⬝ᵥ frame.axis ≠ 0 := by
    intro hzero
    have hsplit := frame.dotProduct_self_split (design.atom offFirst)
    rw [hshadowOne, hshadowTwo, hzero] at hsplit
    have hlev : leverageOf (design.atom offFirst)
        = design.atom offFirst ⬝ᵥ design.atom offFirst := leverageOf_eq_dotProduct _
    rw [← hlev] at hsplit
    norm_num at hsplit
    rw [hsplit] at hheavyFirst
    norm_num at hheavyFirst
  have hquotient : ((design.atom offSecond ⬝ᵥ frame.axis)
        / (design.atom offFirst ⬝ᵥ frame.axis)) * (design.atom offFirst ⬝ᵥ frame.axis)
      = design.atom offSecond ⬝ᵥ frame.axis := div_mul_cancel₀ _ hfirstHeight
  refine ⟨(design.atom offSecond ⬝ᵥ frame.axis) / (design.atom offFirst ⬝ᵥ frame.axis), ?_⟩
  calc design.atom offSecond
      = (design.atom offSecond ⬝ᵥ frame.axis) • frame.axis := hresolveSecond
    _ = (((design.atom offSecond ⬝ᵥ frame.axis) / (design.atom offFirst ⬝ᵥ frame.axis))
          * (design.atom offFirst ⬝ᵥ frame.axis)) • frame.axis := by rw [hquotient]
    _ = ((design.atom offSecond ⬝ᵥ frame.axis) / (design.atom offFirst ⬝ᵥ frame.axis))
          • ((design.atom offFirst ⬝ᵥ frame.axis) • frame.axis) := by rw [smul_smul]
    _ = ((design.atom offSecond ⬝ᵥ frame.axis) / (design.atom offFirst ⬝ᵥ frame.axis))
          • design.atom offFirst := by rw [← hresolveFirst]

/-- **(c) THE SPIKE.**  If the first off-plane atom is flat too — five coplanar
atoms — then the sixth atom is a pure multiple of the axis and its squared height
is the reciprocal of its weight. -/
theorem spike_of_fiveFlat (design : WeightedDesign size 3) (frame : AxisFrame)
    (flatSet : Finset (Fin size)) {offFirst offSecond : Fin size}
    (hne : offFirst ≠ offSecond) (hcompl : flatSetᶜ = {offFirst, offSecond})
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ frame.axis = 0)
    (hfirstFlat : design.atom offFirst ⬝ᵥ frame.axis = 0) :
    design.weight offSecond * (design.atom offSecond ⬝ᵥ frame.axis) ^ 2 = 1
      ∧ design.atom offSecond ⬝ᵥ frame.pOne = 0
      ∧ design.atom offSecond ⬝ᵥ frame.pTwo = 0
      ∧ design.atom offSecond
          = (design.atom offSecond ⬝ᵥ frame.axis) • frame.axis := by
  have hmass := twoOffPlane_axisMass_eq_one design frame flatSet hne hcompl hflat
  rw [hfirstFlat] at hmass
  have hspikeMass : design.weight offSecond
      * (design.atom offSecond ⬝ᵥ frame.axis) ^ 2 = 1 := by
    simpa using hmass
  have hheight : design.atom offSecond ⬝ᵥ frame.axis ≠ 0 := by
    intro hzero
    rw [hzero] at hspikeMass
    norm_num at hspikeMass
  have hcrossOne := twoOffPlane_crossReading_eq_zero design frame flatSet hne hcompl hflat
    frame.oneAxis
  have hcrossTwo := twoOffPlane_crossReading_eq_zero design frame flatSet hne hcompl hflat
    frame.twoAxis
  rw [hfirstFlat, zero_mul, mul_zero, zero_add] at hcrossOne
  rw [hfirstFlat, zero_mul, mul_zero, zero_add] at hcrossTwo
  have hcoeff : design.weight offSecond * (design.atom offSecond ⬝ᵥ frame.axis) ≠ 0 :=
    mul_ne_zero (design.weight_pos offSecond).ne' hheight
  have hspikeOne : design.atom offSecond ⬝ᵥ frame.pOne = 0 := by
    refine mul_left_cancel₀ hcoeff ?_
    rw [mul_zero]
    linear_combination hcrossOne
  have hspikeTwo : design.atom offSecond ⬝ᵥ frame.pTwo = 0 := by
    refine mul_left_cancel₀ hcoeff ?_
    rw [mul_zero]
    linear_combination hcrossTwo
  refine ⟨hspikeMass, hspikeOne, hspikeTwo, ?_⟩
  have hresolve := orthonormalFrame_resolution frame.oneOne frame.twoTwo frame.axisAxis
    frame.oneTwo frame.oneAxis frame.twoAxis (design.atom offSecond)
  rwa [hspikeOne, hspikeTwo, zero_smul, zero_smul, zero_add, zero_add] at hresolve

/-! ## Part 2 — the coplanar determinant law

The frame readings of a FLAT pair's gap are `dd = ee = 0` and `ff = -1`, so the
rank-one insertion of a third atom collapses to a bare polynomial identity in six
scalars.  The basis-free sibling of the resulting criterion is the tree's
`Gtz.posDef_tripleGap_iff_flatPairFires`; the frame form is landed here because
`Gtz.sum_weight_mul_frameAlpha` averages `Gtz.frameAlpha` over the design and
there is no basis-free averaging law for it. -/

/-- **THE COPLANAR RANK-ONE COLLAPSE.**  A bare polynomial identity in six
scalars: at `dd = ee = 0` and `ff = -1` the rank-one insertion of `(x, y, z)`
into `Gtz.frameDet` leaves the plane block determinant against `z^2 - 1`, less
the plane adjugate form of `(x, y)`. -/
theorem frameDet_flatPair_insert (aa bb cc x y z : ℝ) :
    frameDet (aa + x ^ 2) (bb + x * y) (cc + y ^ 2) (0 + x * z) (0 + y * z) (-1 + z ^ 2)
      = frameBlockDet aa bb cc * (z ^ 2 - 1) - frameAlpha aa bb cc x y := by
  simp only [frameDet, frameBlockDet, frameAlpha]
  ring

/-- The six frame readings of a FLAT pair's gap: the two axis readings vanish and
the axis diagonal is minus one. -/
theorem gapReading_flatPair_axis (design : WeightedDesign size 3) (frame : AxisFrame)
    {pairFirst pairSecond : Fin size} (hne : pairFirst ≠ pairSecond)
    (hfirstFlat : design.atom pairFirst ⬝ᵥ frame.axis = 0)
    (hsecondFlat : design.atom pairSecond ⬝ᵥ frame.axis = 0) :
    gapReading design {pairFirst, pairSecond} frame.pOne frame.axis = 0
      ∧ gapReading design {pairFirst, pairSecond} frame.pTwo frame.axis = 0
      ∧ gapReading design {pairFirst, pairSecond} frame.axis frame.axis = -1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gapReading_eq_sum, Finset.sum_pair hne, hfirstFlat, hsecondFlat, frame.oneAxis]
    ring
  · rw [gapReading_eq_sum, Finset.sum_pair hne, hfirstFlat, hsecondFlat, frame.twoAxis]
    ring
  · rw [gapReading_eq_sum, Finset.sum_pair hne, hfirstFlat, hsecondFlat, frame.axisAxis]
    ring

/-- **THE COPLANAR DETERMINANT LAW.**  For a pair FLAT against the axis and any
third atom, the triple's gap determinant is the pair's plane block determinant
against the third atom's squared height, less the plane adjugate form of the
third atom's shadow.  Sherman-Morrison with the inverse cleared:
`frameAlpha / frameBlockDet` is `q^T A^{-1} q`. -/
theorem det_gap_flatPair_triple (design : WeightedDesign size 3) (frame : AxisFrame)
    {pairFirst pairSecond thirdLabel : Fin size} (hne : pairFirst ≠ pairSecond)
    (hneFirstThird : pairFirst ≠ thirdLabel) (hneSecondThird : pairSecond ≠ thirdLabel)
    (hfirstFlat : design.atom pairFirst ⬝ᵥ frame.axis = 0)
    (hsecondFlat : design.atom pairSecond ⬝ᵥ frame.axis = 0) :
    (subsetSum design {pairFirst, pairSecond, thirdLabel} - 1).det
      = frameBlockDet (gapReading design {pairFirst, pairSecond} frame.pOne frame.pOne)
            (gapReading design {pairFirst, pairSecond} frame.pOne frame.pTwo)
            (gapReading design {pairFirst, pairSecond} frame.pTwo frame.pTwo)
          * ((design.atom thirdLabel ⬝ᵥ frame.axis) ^ 2 - 1)
        - frameAlpha (gapReading design {pairFirst, pairSecond} frame.pOne frame.pOne)
            (gapReading design {pairFirst, pairSecond} frame.pOne frame.pTwo)
            (gapReading design {pairFirst, pairSecond} frame.pTwo frame.pTwo)
            (design.atom thirdLabel ⬝ᵥ frame.pOne)
            (design.atom thirdLabel ⬝ᵥ frame.pTwo) := by
  classical
  set pairSet : Finset (Fin size) := {pairFirst, pairSecond} with hpairDef
  have hthirdNotMem : thirdLabel ∉ pairSet := by
    simp only [hpairDef, Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨Ne.symm hneFirstThird, Ne.symm hneSecondThird⟩
  obtain ⟨hdd, hee, hff⟩ := gapReading_flatPair_axis design frame hne hfirstFlat hsecondFlat
  rw [← hpairDef] at hdd hee hff
  have hentry : ∀ probeLeft probeRight : Fin 3 → ℝ,
      gapReading design (insert thirdLabel pairSet) probeLeft probeRight
        = gapReading design pairSet probeLeft probeRight
          + (design.atom thirdLabel ⬝ᵥ probeLeft) * (design.atom thirdLabel ⬝ᵥ probeRight) :=
    fun probeLeft probeRight => gapReading_insert design hthirdNotMem probeLeft probeRight
  have htriple : ({pairFirst, pairSecond, thirdLabel} : Finset (Fin size))
      = insert thirdLabel pairSet := tripleSet_eq_insert
  rw [htriple, det_gap_eq_frameDet design (insert thirdLabel pairSet) frame, hentry, hentry,
    hentry, hentry, hentry, hentry, hdd, hee, hff]
  have hsq : ∀ probe : Fin 3 → ℝ,
      (design.atom thirdLabel ⬝ᵥ probe) * (design.atom thirdLabel ⬝ᵥ probe)
        = (design.atom thirdLabel ⬝ᵥ probe) ^ 2 := fun probe => (sq _).symm
  rw [hsq frame.pOne, hsq frame.pTwo, hsq frame.axis]
  exact frameDet_flatPair_insert _ _ _ _ _ _

/-- **THE COPLANAR GATE AT A TIE.**  At a tie, through a flat pair that is strict
on the plane, every atom obeys the Sherman-Morrison inequality with no
division. -/
theorem flatPair_gate_of_isTie (design : WeightedDesign size 3) (htie : IsTie design)
    (frame : AxisFrame) {pairFirst pairSecond thirdLabel : Fin size}
    (hne : pairFirst ≠ pairSecond) (hneFirstThird : pairFirst ≠ thirdLabel)
    (hneSecondThird : pairSecond ≠ thirdLabel)
    (hfirstFlat : design.atom pairFirst ⬝ᵥ frame.axis = 0)
    (hsecondFlat : design.atom pairSecond ⬝ᵥ frame.axis = 0)
    (hstrict : PlaneStrictPair design frame.axis pairFirst pairSecond) :
    frameBlockDet (gapReading design {pairFirst, pairSecond} frame.pOne frame.pOne)
          (gapReading design {pairFirst, pairSecond} frame.pOne frame.pTwo)
          (gapReading design {pairFirst, pairSecond} frame.pTwo frame.pTwo)
        * ((design.atom thirdLabel ⬝ᵥ frame.axis) ^ 2 - 1)
      ≤ frameAlpha (gapReading design {pairFirst, pairSecond} frame.pOne frame.pOne)
          (gapReading design {pairFirst, pairSecond} frame.pOne frame.pTwo)
          (gapReading design {pairFirst, pairSecond} frame.pTwo frame.pTwo)
          (design.atom thirdLabel ⬝ᵥ frame.pOne)
          (design.atom thirdLabel ⬝ᵥ frame.pTwo) := by
  have hgate := det_gap_nonpos_of_isTie_of_pairPlaneStrict design htie frame.oneOne
    frame.twoTwo frame.axisAxis frame.oneTwo frame.oneAxis frame.twoAxis hne hneFirstThird
    hneSecondThird hstrict
  rw [det_gap_flatPair_triple design frame hne hneFirstThird hneSecondThird hfirstFlat
    hsecondFlat] at hgate
  linarith

/-- **THE SPIKE DECOUPLES.**  With five atoms coplanar the sixth is a spike, and
every triple through the spike has gap determinant the planar pair minor against
`1/t - 1`.  The gap is block diagonal in the plane and the axis. -/
theorem det_gap_spike_triple (design : WeightedDesign size 3) (frame : AxisFrame)
    (flatSet : Finset (Fin size)) {offFirst offSecond : Fin size}
    (hne : offFirst ≠ offSecond) (hcompl : flatSetᶜ = {offFirst, offSecond})
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ frame.axis = 0)
    (hfirstFlat : design.atom offFirst ⬝ᵥ frame.axis = 0)
    {planeFirst planeSecond : Fin size} (hplaneNe : planeFirst ≠ planeSecond)
    (hplaneFirstFlat : design.atom planeFirst ⬝ᵥ frame.axis = 0)
    (hplaneSecondFlat : design.atom planeSecond ⬝ᵥ frame.axis = 0)
    (hneFirstSpike : planeFirst ≠ offSecond) (hneSecondSpike : planeSecond ≠ offSecond) :
    (subsetSum design {planeFirst, planeSecond, offSecond} - 1).det
      = frameBlockDet (gapReading design {planeFirst, planeSecond} frame.pOne frame.pOne)
          (gapReading design {planeFirst, planeSecond} frame.pOne frame.pTwo)
          (gapReading design {planeFirst, planeSecond} frame.pTwo frame.pTwo)
        * (1 / design.weight offSecond - 1) := by
  obtain ⟨hmass, hspikeOne, hspikeTwo, -⟩ := spike_of_fiveFlat design frame flatSet hne hcompl
    hflat hfirstFlat
  have hweight := design.weight_pos offSecond
  have hheightSq : (design.atom offSecond ⬝ᵥ frame.axis) ^ 2 = 1 / design.weight offSecond := by
    field_simp
    linarith [hmass]
  rw [det_gap_flatPair_triple design frame hplaneNe hneFirstSpike hneSecondSpike
    hplaneFirstFlat hplaneSecondFlat, hspikeOne, hspikeTwo, hheightSq]
  simp only [frameAlpha]
  ring

/-! ## Part 3 — the shadow-class pigeonhole

A rank-two design that is heavy and carries no strictly dominating pair has
exactly THREE parallel classes (`Gtz.card_image_tieClass_eq_three`, whose
hypotheses are heaviness and no-strict-pair, NOT `Gtz.IsTie`).  A FLAT atom is
its own shadow.  Four flat atoms therefore repeat a class, and the repeat is a
parallel pair of the design itself. -/

/-- **THE PIGEONHOLE CLOSURE.**  Four atoms flat against the axis of a frame
whose shadow is heavy and carries no strictly dominating pair force a PARALLEL
PAIR of the design.  Three classes cannot separate four flat atoms, and a flat
atom is rebuilt from its shadow by frame completeness. -/
theorem hasParallelPair_of_fourFlat_of_shadowClasses (design : WeightedDesign size 3)
    (frame : AxisFrame) {flatOne flatTwo flatThree flatFour : Fin size}
    (hneOneTwo : flatOne ≠ flatTwo) (hneOneThree : flatOne ≠ flatThree)
    (hneOneFour : flatOne ≠ flatFour) (hneTwoThree : flatTwo ≠ flatThree)
    (hneTwoFour : flatTwo ≠ flatFour) (hneThreeFour : flatThree ≠ flatFour)
    (hflat : ∀ label ∈ ({flatOne, flatTwo, flatThree, flatFour} : Finset (Fin size)),
      design.atom label ⬝ᵥ frame.axis = 0)
    (hheavy : ∀ label : Fin size, 1 ≤ leverageOf ((frameShadow design frame).atom label))
    (hnostrict : NoStrictPair (frameShadow design frame)) :
    HasParallelPair design := by
  classical
  set shadow := frameShadow design frame with hshadowDef
  set flatFour' : Finset (Fin size) := {flatOne, flatTwo, flatThree, flatFour}
    with hflatFourDef
  have hcard : flatFour'.card = 4 := by
    rw [hflatFourDef,
      Finset.card_insert_of_notMem (by simp [hneOneTwo, hneOneThree, hneOneFour]),
      Finset.card_insert_of_notMem (by simp [hneTwoThree, hneTwoFour]),
      Finset.card_insert_of_notMem (by simp [hneThreeFour]), Finset.card_singleton]
  have hclassCount : (Finset.univ.image (tieClass shadow)).card = 3 :=
    card_image_tieClass_eq_three shadow hheavy hnostrict
  have hlt : (Finset.univ.image (tieClass shadow)).card < flatFour'.card := by
    rw [hclassCount, hcard]
    norm_num
  obtain ⟨firstLabel, hfirstMem, secondLabel, hsecondMem, hlabelNe, hclassEq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
      (f := tieClass shadow)
      (fun label _ => Finset.mem_image_of_mem _ (Finset.mem_univ label))
  have hsecondInFirst : secondLabel ∈ tieClass shadow firstLabel := by
    rw [hclassEq]
    exact self_mem_tieClass shadow hheavy secondLabel
  have hwedge : planeWedge (shadow.atom firstLabel) (shadow.atom secondLabel) = 0 :=
    (mem_tieClass_iff_planeWedge_eq_zero shadow hheavy hnostrict firstLabel secondLabel).mp
      hsecondInFirst
  have hfirstFlat : design.atom firstLabel ⬝ᵥ frame.axis = 0 := hflat firstLabel hfirstMem
  have hsecondFlat : design.atom secondLabel ⬝ᵥ frame.axis = 0 := hflat secondLabel hsecondMem
  have hfirstHeavy : 1 ≤ leverageOf (design.atom firstLabel) := by
    have hshadowHeavy := hheavy firstLabel
    rwa [hshadowDef, leverageOf_frameShadow_atom_of_flat design frame hfirstFlat] at hshadowHeavy
  obtain ⟨ratio, hratio⟩ := exists_smul_of_flat_of_planeWedge_eq_zero design frame
    hfirstHeavy hfirstFlat hsecondFlat (by rw [← hshadowDef]; exact hwedge)
  exact ⟨firstLabel, secondLabel, ratio, hlabelNe, hratio⟩

/-- Every atom of a `(6,3)` tie is heavy, so a FLAT atom of a `(6,3)` tie is
heavy in the shadow too and needs no hypothesis. -/
theorem shadow_heavy_of_isTie_sixThree_of_flat (design : WeightedDesign 6 3)
    (htie : IsTie design) (frame : AxisFrame) {label : Fin 6}
    (hflat : design.atom label ⬝ᵥ frame.axis = 0) :
    1 ≤ leverageOf ((frameShadow design frame).atom label) := by
  rw [leverageOf_frameShadow_atom_of_flat design frame hflat]
  exact leverage_one_le_of_isTie_sixThree design htie label

/-- **THE COPLANAR BRIDGE, MODULO THE TWO RESIDUES.**  A `(6,3)` tie with four
coplanar atoms has a PARALLEL PAIR, provided the two off-plane shadows stay heavy
and the plane carries no strictly dominating shadow pair.  The four coplanar
atoms need no heaviness hypothesis: a tie supplies it. -/
theorem hasParallelPair_of_isTie_sixThree_of_fourCoplanar (design : WeightedDesign 6 3)
    (htie : IsTie design) (frame : AxisFrame)
    {flatOne flatTwo flatThree flatFour : Fin 6}
    (hneOneTwo : flatOne ≠ flatTwo) (hneOneThree : flatOne ≠ flatThree)
    (hneOneFour : flatOne ≠ flatFour) (hneTwoThree : flatTwo ≠ flatThree)
    (hneTwoFour : flatTwo ≠ flatFour) (hneThreeFour : flatThree ≠ flatFour)
    (hflat : ∀ label ∈ ({flatOne, flatTwo, flatThree, flatFour} : Finset (Fin 6)),
      design.atom label ⬝ᵥ frame.axis = 0)
    (hoffHeavy : ∀ label : Fin 6, design.atom label ⬝ᵥ frame.axis ≠ 0 →
      1 ≤ leverageOf ((frameShadow design frame).atom label))
    (hnostrict : NoStrictPair (frameShadow design frame)) :
    HasParallelPair design := by
  refine hasParallelPair_of_fourFlat_of_shadowClasses design frame hneOneTwo hneOneThree
    hneOneFour hneTwoThree hneTwoFour hneThreeFour hflat (fun label => ?_) hnostrict
  by_cases hlabelFlat : design.atom label ⬝ᵥ frame.axis = 0
  · exact shadow_heavy_of_isTie_sixThree_of_flat design htie frame hlabelFlat
  · exact hoffHeavy label hlabelFlat

/-- **THE FOUR-COPLANAR TRICHOTOMY AT `(6,3)`.**  Every tie with four coplanar
atoms is light in the shadow at some atom, or carries a strictly dominating
shadow pair on that plane, or has a parallel pair.  The first alternative can
only occur at one of the two OFF-PLANE atoms. -/
theorem fourCoplanar_trichotomy_sixThree (design : WeightedDesign 6 3) (htie : IsTie design)
    (frame : AxisFrame) {flatOne flatTwo flatThree flatFour : Fin 6}
    (hneOneTwo : flatOne ≠ flatTwo) (hneOneThree : flatOne ≠ flatThree)
    (hneOneFour : flatOne ≠ flatFour) (hneTwoThree : flatTwo ≠ flatThree)
    (hneTwoFour : flatTwo ≠ flatFour) (hneThreeFour : flatThree ≠ flatFour)
    (hflat : ∀ label ∈ ({flatOne, flatTwo, flatThree, flatFour} : Finset (Fin 6)),
      design.atom label ⬝ᵥ frame.axis = 0) :
    (∃ label : Fin 6, design.atom label ⬝ᵥ frame.axis ≠ 0
        ∧ leverageOf ((frameShadow design frame).atom label) < 1)
      ∨ (∃ pairFirst pairSecond : Fin 6, pairFirst ≠ pairSecond
          ∧ (subsetSum (frameShadow design frame) {pairFirst, pairSecond} - 1).PosDef)
      ∨ HasParallelPair design := by
  classical
  by_cases hoffHeavy : ∀ label : Fin 6, design.atom label ⬝ᵥ frame.axis ≠ 0 →
      1 ≤ leverageOf ((frameShadow design frame).atom label)
  · by_cases hstrict : ∃ pairFirst pairSecond : Fin 6, pairFirst ≠ pairSecond
        ∧ (subsetSum (frameShadow design frame) {pairFirst, pairSecond} - 1).PosDef
    · exact Or.inr (Or.inl hstrict)
    · push_neg at hstrict
      exact Or.inr (Or.inr (hasParallelPair_of_isTie_sixThree_of_fourCoplanar design htie
        frame hneOneTwo hneOneThree hneOneFour hneTwoThree hneTwoFour hneThreeFour hflat
        hoffHeavy (fun pairFirst pairSecond hne => hstrict pairFirst pairSecond hne)))
  · push_neg at hoffHeavy
    obtain ⟨label, hnotFlat, hlight⟩ := hoffHeavy
    exact Or.inl ⟨label, hnotFlat, hlight⟩

/-! ## Part 4 — the coplanar wall

Summing the coplanar gate over the WHOLE complement of a flat pair reproduces the
landed area ceiling `Gtz.crossNormSq_le_of_isTie` exactly.  Summing it over the
TWO OFF-PLANE atoms only is strictly stronger, because the coplanar atoms outside
the pair have vanishing height and so contribute a nonpositive term to the left
and a nonnegative term to the right of the general law.  That improvement is
available only under coplanarity. -/

/-- **THE COPLANAR WALL.**  At a tie whose plane carries a strict flat pair, the
pair minor times the TOTAL COPLANAR WEIGHT is at most the weighted plane-adjugate
energy of the two off-plane shadows.  Divided by the pair minor it reads
`1 - t_1 - t_2 <= t_1 s_1 + t_2 s_2` with `s_i = q_i^T A^{-1} q_i`. -/
theorem coplanar_wall_of_isTie (design : WeightedDesign size 3) (htie : IsTie design)
    (frame : AxisFrame) (flatSet : Finset (Fin size)) {offFirst offSecond : Fin size}
    (hne : offFirst ≠ offSecond) (hcompl : flatSetᶜ = {offFirst, offSecond})
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ frame.axis = 0)
    {pairFirst pairSecond : Fin size} (hpairNe : pairFirst ≠ pairSecond)
    (hpairFirstMem : pairFirst ∈ flatSet) (hpairSecondMem : pairSecond ∈ flatSet)
    (hstrict : PlaneStrictPair design frame.axis pairFirst pairSecond)
    {aa bb cc : ℝ}
    (haa : aa = gapReading design {pairFirst, pairSecond} frame.pOne frame.pOne)
    (hbb : bb = gapReading design {pairFirst, pairSecond} frame.pOne frame.pTwo)
    (hcc : cc = gapReading design {pairFirst, pairSecond} frame.pTwo frame.pTwo) :
    frameBlockDet aa bb cc * (1 - design.weight offFirst - design.weight offSecond)
      ≤ design.weight offFirst
          * frameAlpha aa bb cc (design.atom offFirst ⬝ᵥ frame.pOne)
              (design.atom offFirst ⬝ᵥ frame.pTwo)
        + design.weight offSecond
          * frameAlpha aa bb cc (design.atom offSecond ⬝ᵥ frame.pOne)
              (design.atom offSecond ⬝ᵥ frame.pTwo) := by
  classical
  have hoffFirstNotFlat : offFirst ∉ flatSet := by
    have hmem : offFirst ∈ flatSetᶜ := by rw [hcompl]; simp
    exact Finset.mem_compl.mp hmem
  have hoffSecondNotFlat : offSecond ∉ flatSet := by
    have hmem : offSecond ∈ flatSetᶜ := by rw [hcompl]; simp
    exact Finset.mem_compl.mp hmem
  have hpairFirstOffFirst : pairFirst ≠ offFirst := fun heq =>
    hoffFirstNotFlat (heq ▸ hpairFirstMem)
  have hpairSecondOffFirst : pairSecond ≠ offFirst := fun heq =>
    hoffFirstNotFlat (heq ▸ hpairSecondMem)
  have hpairFirstOffSecond : pairFirst ≠ offSecond := fun heq =>
    hoffSecondNotFlat (heq ▸ hpairFirstMem)
  have hpairSecondOffSecond : pairSecond ≠ offSecond := fun heq =>
    hoffSecondNotFlat (heq ▸ hpairSecondMem)
  have hpairFirstFlat : design.atom pairFirst ⬝ᵥ frame.axis = 0 := hflat pairFirst hpairFirstMem
  have hpairSecondFlat : design.atom pairSecond ⬝ᵥ frame.axis = 0 :=
    hflat pairSecond hpairSecondMem
  have hgateFirst := flatPair_gate_of_isTie design htie frame hpairNe hpairFirstOffFirst
    hpairSecondOffFirst hpairFirstFlat hpairSecondFlat hstrict
  have hgateSecond := flatPair_gate_of_isTie design htie frame hpairNe hpairFirstOffSecond
    hpairSecondOffSecond hpairFirstFlat hpairSecondFlat hstrict
  rw [← haa, ← hbb, ← hcc] at hgateFirst hgateSecond
  have hmass := twoOffPlane_axisMass_eq_one design frame flatSet hne hcompl hflat
  have hweightFirst := design.weight_pos offFirst
  have hweightSecond := design.weight_pos offSecond
  have hstepFirst := mul_le_mul_of_nonneg_left hgateFirst hweightFirst.le
  have hstepSecond := mul_le_mul_of_nonneg_left hgateSecond hweightSecond.le
  have hexpand : design.weight offFirst
        * (frameBlockDet aa bb cc * ((design.atom offFirst ⬝ᵥ frame.axis) ^ 2 - 1))
      + design.weight offSecond
        * (frameBlockDet aa bb cc * ((design.atom offSecond ⬝ᵥ frame.axis) ^ 2 - 1))
      = frameBlockDet aa bb cc
        * (1 - design.weight offFirst - design.weight offSecond) := by
    linear_combination frameBlockDet aa bb cc * hmass
  linarith [hstepFirst, hstepSecond, hexpand]

/-! ## Part 5 — the five-coplanar stratum is EMPTY

Everything above is conditional.  This part is not.

If all but ONE atom of a rank-three design lie in a plane, the exceptional atom
is a SPIKE along the normal and its shadow VANISHES.  The remaining atoms then
carry the whole in-plane Parseval identity on a total weight of `1 - t` with
`t` the spike's weight, so rescaling them by `sqrt (1 - t)` gives a genuine
rank-two design one label shorter.  Rank-two GTZ is a THEOREM
(`Gtz.gtz_rank_two`), so that design has a weakly dominating pair — and the
rescaling turns weak domination downstairs into STRICT domination of the plane
upstairs, by exactly the weight deficit `t / (1 - t)`.

The gap of the pair together with the spike is BLOCK DIAGONAL, its plane block
strictly positive and its axis entry `1/t - 1 > 0`.  So the triple dominates
STRICTLY, and no such design is a tie.

Nothing here is special to six atoms: at every size and every rank-three design,
`m - 1` coplanar atoms forbid a tie. -/

/-- The planar companion of a design whose atoms all lie in a plane except the
one at `spikeLabel`: the shadows of the surviving atoms, rescaled by the square
root of their total weight, with the weights renormalised.  Parseval holds
because the spike's shadow vanishes. -/
noncomputable def spikeComplementDesign {atoms : ℕ} (design : WeightedDesign (atoms + 1) 3)
    (frame : AxisFrame) (spikeLabel : Fin (atoms + 1))
    (hspikeOne : design.atom spikeLabel ⬝ᵥ frame.pOne = 0)
    (hspikeTwo : design.atom spikeLabel ⬝ᵥ frame.pTwo = 0)
    (hslack : 0 < 1 - design.weight spikeLabel) : WeightedDesign atoms 2 where
  atom label := Real.sqrt (1 - design.weight spikeLabel)
    • ![design.atom (spikeLabel.succAbove label) ⬝ᵥ frame.pOne,
        design.atom (spikeLabel.succAbove label) ⬝ᵥ frame.pTwo]
  weight label := design.weight (spikeLabel.succAbove label) / (1 - design.weight spikeLabel)
  weight_pos label := div_pos (design.weight_pos _) hslack
  weight_sum_one := by
    have hsplit := Fin.sum_univ_succAbove design.weight spikeLabel
    rw [design.weight_sum_one] at hsplit
    rw [← Finset.sum_div]
    rw [show ∑ label : Fin atoms, design.weight (spikeLabel.succAbove label)
        = 1 - design.weight spikeLabel by linarith [hsplit]]
    exact div_self hslack.ne'
  isParseval := by
    have hnonzero : (1 : ℝ) - design.weight spikeLabel ≠ 0 := ne_of_gt hslack
    have hroot : Real.sqrt (1 - design.weight spikeLabel)
        * Real.sqrt (1 - design.weight spikeLabel) = 1 - design.weight spikeLabel :=
      Real.mul_self_sqrt hslack.le
    have hterm : ∀ (label : Fin atoms) (probeLeft probeRight : Fin 3 → ℝ),
        design.weight (spikeLabel.succAbove label) / (1 - design.weight spikeLabel)
            * (Real.sqrt (1 - design.weight spikeLabel)
                  * (design.atom (spikeLabel.succAbove label) ⬝ᵥ probeLeft)
                * (Real.sqrt (1 - design.weight spikeLabel)
                  * (design.atom (spikeLabel.succAbove label) ⬝ᵥ probeRight)))
          = design.weight (spikeLabel.succAbove label)
            * ((design.atom (spikeLabel.succAbove label) ⬝ᵥ probeLeft)
              * (design.atom (spikeLabel.succAbove label) ⬝ᵥ probeRight)) := by
      intro label probeLeft probeRight
      rw [show Real.sqrt (1 - design.weight spikeLabel)
              * (design.atom (spikeLabel.succAbove label) ⬝ᵥ probeLeft)
            * (Real.sqrt (1 - design.weight spikeLabel)
              * (design.atom (spikeLabel.succAbove label) ⬝ᵥ probeRight))
          = Real.sqrt (1 - design.weight spikeLabel)
              * Real.sqrt (1 - design.weight spikeLabel)
            * ((design.atom (spikeLabel.succAbove label) ⬝ᵥ probeLeft)
              * (design.atom (spikeLabel.succAbove label) ⬝ᵥ probeRight)) from by ring,
        hroot]
      field_simp
    have hentry : ∀ probeLeft probeRight : Fin 3 → ℝ,
        design.atom spikeLabel ⬝ᵥ probeLeft = 0 →
        ∑ label : Fin atoms, design.weight (spikeLabel.succAbove label)
            * ((design.atom (spikeLabel.succAbove label) ⬝ᵥ probeLeft)
              * (design.atom (spikeLabel.succAbove label) ⬝ᵥ probeRight))
          = probeLeft ⬝ᵥ probeRight := by
      intro probeLeft probeRight hspikeFlat
      have hfull := sum_weighted_atomPairing design probeLeft probeRight
      have hsplit := Fin.sum_univ_succAbove
        (fun label => design.weight label
          * ((design.atom label ⬝ᵥ probeLeft) * (design.atom label ⬝ᵥ probeRight)))
        spikeLabel
      rw [hfull, hspikeFlat] at hsplit
      simp only [zero_mul, mul_zero, zero_add] at hsplit
      exact hsplit.symm
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
        smul_eq_mul, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, Fin.zero_eta,
        Fin.mk_one, Fin.reduceEq, not_false_eq_true]
    · rw [Finset.sum_congr rfl (fun label (_ : label ∈ Finset.univ) =>
        hterm label frame.pOne frame.pOne), hentry frame.pOne frame.pOne hspikeOne,
        frame.oneOne]
    · rw [Finset.sum_congr rfl (fun label (_ : label ∈ Finset.univ) =>
        hterm label frame.pOne frame.pTwo), hentry frame.pOne frame.pTwo hspikeOne,
        frame.oneTwo]
    · rw [Finset.sum_congr rfl (fun label (_ : label ∈ Finset.univ) =>
        hterm label frame.pTwo frame.pOne), hentry frame.pTwo frame.pOne hspikeTwo,
        dotProduct_comm, frame.oneTwo]
    · rw [Finset.sum_congr rfl (fun label (_ : label ∈ Finset.univ) =>
        hterm label frame.pTwo frame.pTwo), hentry frame.pTwo frame.pTwo hspikeTwo,
        frame.twoTwo]

/-- **THE WEIGHT DEFICIT BUYS STRICTNESS.**  A weakly dominating pair of the
planar companion reads on the plane of the original design with a strict margin:
the total weight of the surviving atoms is `1 - t`, so the companion's atoms are
longer than the shadows by exactly the factor that turns `>=` into `>`. -/
theorem planeStrict_of_dominates_spikeComplementDesign {atoms : ℕ}
    (design : WeightedDesign (atoms + 1) 3) (frame : AxisFrame)
    (spikeLabel : Fin (atoms + 1))
    (hspikeOne : design.atom spikeLabel ⬝ᵥ frame.pOne = 0)
    (hspikeTwo : design.atom spikeLabel ⬝ᵥ frame.pTwo = 0)
    (hslack : 0 < 1 - design.weight spikeLabel)
    {pairFirst pairSecond : Fin atoms} (hne : pairFirst ≠ pairSecond)
    (hdominates : Dominates
      (spikeComplementDesign design frame spikeLabel hspikeOne hspikeTwo hslack)
      {pairFirst, pairSecond})
    (xcoord ycoord : ℝ) :
    (xcoord ^ 2 + ycoord ^ 2)
      ≤ (1 - design.weight spikeLabel)
        * ((design.atom (spikeLabel.succAbove pairFirst) ⬝ᵥ frame.pOne * xcoord
              + design.atom (spikeLabel.succAbove pairFirst) ⬝ᵥ frame.pTwo * ycoord) ^ 2
          + (design.atom (spikeLabel.succAbove pairSecond) ⬝ᵥ frame.pOne * xcoord
              + design.atom (spikeLabel.succAbove pairSecond) ⬝ᵥ frame.pTwo * ycoord) ^ 2) := by
  classical
  set companion := spikeComplementDesign design frame spikeLabel hspikeOne hspikeTwo hslack
    with hcompanionDef
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 ![xcoord, ycoord]
  rw [star_trivial, dominationGap_form, Finset.sum_pair hne] at hform
  have hroot : Real.sqrt (1 - design.weight spikeLabel)
      * Real.sqrt (1 - design.weight spikeLabel) = 1 - design.weight spikeLabel :=
    Real.mul_self_sqrt hslack.le
  have hreading : ∀ label : Fin atoms,
      companion.atom label ⬝ᵥ ![xcoord, ycoord]
        = Real.sqrt (1 - design.weight spikeLabel)
          * (design.atom (spikeLabel.succAbove label) ⬝ᵥ frame.pOne * xcoord
            + design.atom (spikeLabel.succAbove label) ⬝ᵥ frame.pTwo * ycoord) := by
    intro label
    simp only [hcompanionDef, spikeComplementDesign, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hnorm : (![xcoord, ycoord] : Fin 2 → ℝ) ⬝ᵥ ![xcoord, ycoord]
      = xcoord ^ 2 + ycoord ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring
  rw [hreading pairFirst, hreading pairSecond, hnorm] at hform
  nlinarith [hform, hroot]

/-- **THE FIVE-COPLANAR KILL.**  A rank-three design whose atoms all lie in one
plane except a single one is NEVER a tie: it carries a STRICTLY dominating
triple, namely the exceptional atom together with the pair that rank-two GTZ
returns for the planar companion.

The exceptional atom is a spike of squared height `1/t`, the pair beats the plane
with margin `t / (1 - t)`, and the gap is block diagonal, so the two margins do
not interfere. -/
theorem exists_posDef_triple_of_spike {atoms : ℕ} (design : WeightedDesign (atoms + 1) 3)
    (frame : AxisFrame) (flatSet : Finset (Fin (atoms + 1)))
    {offFirst spikeLabel : Fin (atoms + 1)} (hne : offFirst ≠ spikeLabel)
    (hcompl : flatSetᶜ = {offFirst, spikeLabel})
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ frame.axis = 0)
    (hfirstFlat : design.atom offFirst ⬝ᵥ frame.axis = 0) (hsize : 2 ≤ atoms + 1) :
    ∃ selected : Finset (Fin (atoms + 1)), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  obtain ⟨hmass, hspikeOne, hspikeTwo, hspikeAxis⟩ :=
    spike_of_fiveFlat design frame flatSet hne hcompl hflat hfirstFlat
  have hweightPos := design.weight_pos spikeLabel
  have hslack : 0 < 1 - design.weight spikeLabel := by
    linarith [weight_lt_one design hsize spikeLabel]
  set companion := spikeComplementDesign design frame spikeLabel hspikeOne hspikeTwo hslack
    with hcompanionDef
  obtain ⟨pairSet, hpairCard, hpairDominates⟩ := gtz_rank_two atoms companion
  obtain ⟨pairFirst, pairSecond, hpairNe, hpairEq⟩ := Finset.card_eq_two.mp hpairCard
  rw [hpairEq] at hpairDominates
  set firstLabel : Fin (atoms + 1) := spikeLabel.succAbove pairFirst with hfirstDef
  set secondLabel : Fin (atoms + 1) := spikeLabel.succAbove pairSecond with hsecondDef
  have hfirstNeSpike : firstLabel ≠ spikeLabel := Fin.succAbove_ne spikeLabel pairFirst
  have hsecondNeSpike : secondLabel ≠ spikeLabel := Fin.succAbove_ne spikeLabel pairSecond
  have hfirstNeSecond : firstLabel ≠ secondLabel := fun heq =>
    hpairNe (Fin.succAbove_right_injective heq)
  -- the spike's squared height
  have hheightSq : (design.atom spikeLabel ⬝ᵥ frame.axis) ^ 2
      = 1 / design.weight spikeLabel := by
    field_simp
    linarith [hmass]
  -- the two pair members are flat, because the spike is the only off-plane atom
  have hflatAll : ∀ label : Fin (atoms + 1), label ≠ spikeLabel →
      design.atom label ⬝ᵥ frame.axis = 0 := by
    intro label hlabelNe
    by_cases hmem : label ∈ flatSet
    · exact hflat label hmem
    · have hcomplMem : label ∈ flatSetᶜ := Finset.mem_compl.mpr hmem
      rw [hcompl] at hcomplMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcomplMem
      rcases hcomplMem with heq | heq
      · rw [heq]; exact hfirstFlat
      · exact absurd heq hlabelNe
  have hfirstFlatAtom : design.atom firstLabel ⬝ᵥ frame.axis = 0 := hflatAll _ hfirstNeSpike
  have hsecondFlatAtom : design.atom secondLabel ⬝ᵥ frame.axis = 0 := hflatAll _ hsecondNeSpike
  refine ⟨{firstLabel, secondLabel, spikeLabel}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨hfirstNeSecond, hfirstNeSpike⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact hsecondNeSpike), Finset.card_singleton]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_subsetSum_sub_one design _, fun probe hprobeNe => ?_⟩
  rw [star_trivial, dominationGap_form,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hfirstNeSecond, hfirstNeSpike⟩),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hsecondNeSpike),
    Finset.sum_singleton]
  set xcoord := probe ⬝ᵥ frame.pOne with hxDef
  set ycoord := probe ⬝ᵥ frame.pTwo with hyDef
  set zcoord := probe ⬝ᵥ frame.axis with hzDef
  have hsplitProbe : probe ⬝ᵥ probe = xcoord ^ 2 + ycoord ^ 2 + zcoord ^ 2 :=
    frame.dotProduct_self_split probe
  have hflatReading : ∀ label : Fin (atoms + 1), design.atom label ⬝ᵥ frame.axis = 0 →
      design.atom label ⬝ᵥ probe
        = (design.atom label ⬝ᵥ frame.pOne) * xcoord
          + (design.atom label ⬝ᵥ frame.pTwo) * ycoord := by
    intro label hlabelFlat
    have hresolve := orthonormalFrame_resolution frame.oneOne frame.twoTwo frame.axisAxis
      frame.oneTwo frame.oneAxis frame.twoAxis probe
    conv_lhs => rw [hresolve]
    rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_smul,
      hlabelFlat, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_zero, add_zero, hxDef, hyDef]
    ring
  have hspikeReading : design.atom spikeLabel ⬝ᵥ probe
      = (design.atom spikeLabel ⬝ᵥ frame.axis) * zcoord := by
    conv_lhs => rw [hspikeAxis]
    rw [smul_dotProduct, smul_eq_mul, dotProduct_comm frame.axis probe, ← hzDef]
  rw [hflatReading firstLabel hfirstFlatAtom, hflatReading secondLabel hsecondFlatAtom,
    hspikeReading, hsplitProbe]
  have hplane := planeStrict_of_dominates_spikeComplementDesign design frame spikeLabel
    hspikeOne hspikeTwo hslack hpairNe hpairDominates xcoord ycoord
  rw [← hfirstDef, ← hsecondDef] at hplane
  have hcoordsNe : ¬ (xcoord = 0 ∧ ycoord = 0 ∧ zcoord = 0) := by
    rintro ⟨hx, hy, hz⟩
    refine hprobeNe (dotProduct_self_eq_zero.mp ?_)
    rw [hsplitProbe, hx, hy, hz]
    ring
  have hspikeMargin : (design.atom spikeLabel ⬝ᵥ frame.axis) ^ 2 * zcoord ^ 2 - zcoord ^ 2
      = (1 / design.weight spikeLabel - 1) * zcoord ^ 2 := by
    rw [hheightSq]; ring
  have hspikeGain : 0 < 1 / design.weight spikeLabel - 1 := by
    have hlt := weight_lt_one design hsize spikeLabel
    have hone : (1 : ℝ) < 1 / design.weight spikeLabel := by
      rw [lt_div_iff₀ hweightPos]
      linarith
    linarith
  have hplaneGain : 0 < 1 / (1 - design.weight spikeLabel) - 1 := by
    have hone : (1 : ℝ) < 1 / (1 - design.weight spikeLabel) := by
      rw [lt_div_iff₀ hslack]
      linarith
    linarith
  have hplaneStrict : (xcoord ^ 2 + ycoord ^ 2)
      ≤ (1 - design.weight spikeLabel)
        * (((design.atom firstLabel ⬝ᵥ frame.pOne) * xcoord
              + (design.atom firstLabel ⬝ᵥ frame.pTwo) * ycoord) ^ 2
          + ((design.atom secondLabel ⬝ᵥ frame.pOne) * xcoord
              + (design.atom secondLabel ⬝ᵥ frame.pTwo) * ycoord) ^ 2) := hplane
  rcases eq_or_ne (xcoord ^ 2 + ycoord ^ 2) 0 with hplaneZero | hplaneNe
  · have hx : xcoord = 0 := by nlinarith [sq_nonneg xcoord, sq_nonneg ycoord]
    have hy : ycoord = 0 := by nlinarith [sq_nonneg xcoord, sq_nonneg ycoord]
    have hz : zcoord ≠ 0 := by
      intro hzero
      exact hcoordsNe ⟨hx, hy, hzero⟩
    have hzsq : 0 < zcoord ^ 2 := by positivity
    have hplaneNonneg : 0 ≤ ((design.atom firstLabel ⬝ᵥ frame.pOne) * xcoord
          + (design.atom firstLabel ⬝ᵥ frame.pTwo) * ycoord) ^ 2
        + ((design.atom secondLabel ⬝ᵥ frame.pOne) * xcoord
          + (design.atom secondLabel ⬝ᵥ frame.pTwo) * ycoord) ^ 2 := by positivity
    nlinarith [hspikeMargin, hspikeGain, hzsq, hplaneNonneg, hx, hy]
  · have hplanePos : 0 < xcoord ^ 2 + ycoord ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hplaneNe)
    have hsumBig : (1 / (1 - design.weight spikeLabel)) * (xcoord ^ 2 + ycoord ^ 2)
        ≤ ((design.atom firstLabel ⬝ᵥ frame.pOne) * xcoord
              + (design.atom firstLabel ⬝ᵥ frame.pTwo) * ycoord) ^ 2
          + ((design.atom secondLabel ⬝ᵥ frame.pOne) * xcoord
              + (design.atom secondLabel ⬝ᵥ frame.pTwo) * ycoord) ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hslack]
      nlinarith [hplaneStrict]
    nlinarith [hsumBig, hplanePos, hplaneGain, hspikeMargin, hspikeGain, sq_nonneg zcoord]

/-- **NO TIE HAS ALL BUT ONE ATOM COPLANAR.**  The strictly dominating triple of
`Gtz.exists_posDef_triple_of_spike` refutes the second clause of `Gtz.IsTie`. -/
theorem not_isTie_of_spike {atoms : ℕ} (design : WeightedDesign (atoms + 1) 3)
    (frame : AxisFrame) (flatSet : Finset (Fin (atoms + 1)))
    {offFirst spikeLabel : Fin (atoms + 1)} (hne : offFirst ≠ spikeLabel)
    (hcompl : flatSetᶜ = {offFirst, spikeLabel})
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ frame.axis = 0)
    (hfirstFlat : design.atom offFirst ⬝ᵥ frame.axis = 0) (hsize : 2 ≤ atoms + 1) :
    ¬ IsTie design := by
  intro htie
  obtain ⟨selected, hcard, hposDef⟩ := exists_posDef_triple_of_spike design frame flatSet
    hne hcompl hflat hfirstFlat hsize
  exact htie.2 selected hcard hposDef

/-- **THE FIVE-COPLANAR STRATUM OF `(6,3)` IS EMPTY.**  No `(6,3)` tie has five
coplanar atoms.  Unconditional: no heaviness, no genericity, no residue. -/
theorem not_isTie_sixThree_of_fiveCoplanar (design : WeightedDesign 6 3)
    (frame : AxisFrame) (flatSet : Finset (Fin 6))
    {offFirst spikeLabel : Fin 6} (hne : offFirst ≠ spikeLabel)
    (hcompl : flatSetᶜ = {offFirst, spikeLabel})
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ frame.axis = 0)
    (hfirstFlat : design.atom offFirst ⬝ᵥ frame.axis = 0) :
    ¬ IsTie design :=
  not_isTie_of_spike (atoms := 5) design frame flatSet hne hcompl hflat hfirstFlat
    (by norm_num)

/-! ### The frame-free readings of the kill

The hypothesis "all but one atom lie in a plane" has two shorter names.  One is a
unit normal that every atom but one kills.  The other mentions no direction at
all: an atom ORTHOGONAL TO EVERY OTHER ATOM.  The second is the memorable form,
and it is the one a Gram-matrix consumer can test by inspection. -/

/-- A design whose atoms are all killed by one unit normal except at a single
label is not a tie.  The frame is built on the normal and the two-element
complement is any partner of the exceptional label. -/
theorem not_isTie_of_unitNormal_kills_all_but_one {atoms : ℕ}
    (design : WeightedDesign (atoms + 1) 3) (hsize : 2 ≤ atoms + 1)
    {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    {spikeLabel : Fin (atoms + 1)}
    (hflat : ∀ label : Fin (atoms + 1), label ≠ spikeLabel →
      design.atom label ⬝ᵥ normalVec = 0) :
    ¬ IsTie design := by
  classical
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  set frame : AxisFrame :=
    { pOne := pOne, pTwo := pTwo, axis := normalVec, oneOne := hOneOne, twoTwo := hTwoTwo,
      axisAxis := hunit, oneTwo := hOneTwo, oneAxis := hOneAxis, twoAxis := hTwoAxis }
    with hframeDef
  obtain ⟨partnerLabel, hpartnerNe⟩ := Fintype.exists_ne_of_one_lt_card
    (by simp only [Fintype.card_fin]; omega) spikeLabel
  refine not_isTie_of_spike design frame ({partnerLabel, spikeLabel} : Finset (Fin (atoms + 1)))ᶜ
    hpartnerNe (by rw [compl_compl]) (fun label hmem => ?_) (hflat partnerLabel hpartnerNe) hsize
  have hnotMem : label ∉ ({partnerLabel, spikeLabel} : Finset (Fin (atoms + 1))) :=
    Finset.mem_compl.mp hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnotMem
  push_neg at hnotMem
  exact hflat label hnotMem.2

/-- **NO ATOM OF A RANK-THREE TIE IS ORTHOGONAL TO EVERY OTHER ATOM.**  The
orthogonal atom would be a spike of the plane the others span, and
`Gtz.exists_posDef_triple_of_spike` then produces a strictly dominating triple.

This is the kill in its shortest form: it names no plane, no frame and no normal,
and it is a condition on the GRAM MATRIX alone — a row whose off-diagonal entries
all vanish. -/
theorem not_isTie_of_atom_orthogonal_to_all {atoms : ℕ}
    (design : WeightedDesign (atoms + 1) 3) (hsize : 2 ≤ atoms + 1)
    {spikeLabel : Fin (atoms + 1)} (hnonzero : design.atom spikeLabel ≠ 0)
    (horth : ∀ label : Fin (atoms + 1), label ≠ spikeLabel →
      design.atom label ⬝ᵥ design.atom spikeLabel = 0) :
    ¬ IsTie design := by
  have hpos : 0 < design.atom spikeLabel ⬝ᵥ design.atom spikeLabel :=
    dotProduct_self_pos hnonzero
  have hsqrtPos : 0 < Real.sqrt (design.atom spikeLabel ⬝ᵥ design.atom spikeLabel) :=
    Real.sqrt_pos.mpr hpos
  set normalVec : Fin 3 → ℝ :=
    (Real.sqrt (design.atom spikeLabel ⬝ᵥ design.atom spikeLabel))⁻¹ • design.atom spikeLabel
    with hnormalDef
  have hunit : normalVec ⬝ᵥ normalVec = 1 := by
    rw [hnormalDef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← mul_inv, Real.mul_self_sqrt hpos.le]
    exact inv_mul_cancel₀ hpos.ne'
  refine not_isTie_of_unitNormal_kills_all_but_one design hsize hunit
    (spikeLabel := spikeLabel) (fun label hlabelNe => ?_)
  rw [hnormalDef, dotProduct_smul, smul_eq_mul, horth label hlabelNe, mul_zero]

/-- **THE `(6,3)` READING.**  No atom of a `(6,3)` tie is orthogonal to the other
five, and no plane holds five of its atoms. -/
theorem sixThree_isTie_no_orthogonal_atom (design : WeightedDesign 6 3) (htie : IsTie design)
    (spikeLabel : Fin 6) (hnonzero : design.atom spikeLabel ≠ 0) :
    ∃ otherLabel : Fin 6, otherLabel ≠ spikeLabel
      ∧ design.atom otherLabel ⬝ᵥ design.atom spikeLabel ≠ 0 := by
  classical
  by_contra hcontra
  push_neg at hcontra
  exact not_isTie_of_atom_orthogonal_to_all (atoms := 5) design (by norm_num)
    (spikeLabel := spikeLabel) hnonzero (fun label hlabelNe => hcontra label hlabelNe) htie

/-- **NO PLANE HOLDS FIVE ATOMS OF A `(6,3)` TIE.** -/
theorem sixThree_isTie_no_unitNormal_kills_five (design : WeightedDesign 6 3)
    (htie : IsTie design) {normalVec : Fin 3 → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1)
    (spikeLabel : Fin 6) :
    ∃ otherLabel : Fin 6, otherLabel ≠ spikeLabel
      ∧ design.atom otherLabel ⬝ᵥ normalVec ≠ 0 := by
  classical
  by_contra hcontra
  push_neg at hcontra
  exact not_isTie_of_unitNormal_kills_all_but_one (atoms := 5) design (by norm_num) hunit
    (spikeLabel := spikeLabel) (fun label hlabelNe => hcontra label hlabelNe) htie

/-- **NO PLANE HOLDS ALL THE ATOMS.**  Parseval along the normal totals one, and a
plane that killed every atom would total zero.  The rank-three cell has no flat
design at all. -/
theorem exists_not_flat {rank : ℕ} (design : WeightedDesign size rank)
    {normalVec : Fin rank → ℝ} (hunit : normalVec ⬝ᵥ normalVec = 1) :
    ∃ label : Fin size, design.atom label ⬝ᵥ normalVec ≠ 0 := by
  classical
  by_contra hcontra
  push_neg at hcontra
  have hidentity := oneLine_normalIdentity design Finset.univ normalVec hunit
    (fun label _ => hcontra label)
  rw [Finset.compl_univ, Finset.sum_empty] at hidentity
  norm_num at hidentity

/-! ## Part 6 — a light off-plane pair hands the plane a strict COPLANAR pair

The four-coplanar configuration has two residues: a light off-plane shadow, and a
strictly dominating shadow pair.  This part shows that the FIRST implies the
SECOND, and that the strict pair can be taken among the four COPLANAR atoms —
which is exactly the shape the coplanar wall of Part 4 consumes.

The mechanism is the weight deficit again.  By Part 1 the two off-plane shadows
are PARALLEL, so their two rank-one contributions to the in-plane Parseval
identity add up to a SINGLE rank-one term along one unit direction, carrying their
total shadow mass.  Replacing the two of them by that one fictitious unit atom
leaves a plane Parseval family of FIVE members whose total weight is

    (coplanar weight) + t_1 lambda_1 + t_2 lambda_2 ,

and that is below one exactly when the two off-plane shadows are light on
weighted average.  A plane family of total weight below one carries a pair that
beats the plane STRICTLY, by the same rescaling that emptied the five-coplanar
stratum.  The fictitious atom is a UNIT vector, so Cauchy-Schwarz forbids it from
sitting in that pair: both members are coplanar atoms of the design. -/

/-- The rescaling of a plane Parseval family of five members to a genuine rank-two
design.  The atoms are stretched by the square root of the total weight and the
weights are renormalised, so Parseval is preserved and the weights total one. -/
noncomputable def scaledPlaneFrame {members : ℕ} (atomOf : Fin (members + 1) → (Fin 2 → ℝ))
    (weightOf : Fin (members + 1) → ℝ) (hpos : ∀ index : Fin (members + 1), 0 < weightOf index)
    (hframe : ∑ index, weightOf index • atomMatrix (atomOf index)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ)) : WeightedDesign (members + 1) 2 where
  atom index := Real.sqrt (∑ other, weightOf other) • atomOf index
  weight index := weightOf index / ∑ other, weightOf other
  weight_pos index :=
    div_pos (hpos index)
      (Finset.sum_pos (fun other _ => hpos other) ⟨0, Finset.mem_univ 0⟩)
  weight_sum_one := by
    have hmass : 0 < ∑ other, weightOf other :=
      Finset.sum_pos (fun other _ => hpos other) ⟨0, Finset.mem_univ 0⟩
    rw [← Finset.sum_div]
    exact div_self hmass.ne'
  isParseval := by
    have hmass : 0 < ∑ other, weightOf other :=
      Finset.sum_pos (fun other _ => hpos other) ⟨0, Finset.mem_univ 0⟩
    have hsq : Real.sqrt (∑ other, weightOf other) ^ 2 = ∑ other, weightOf other :=
      Real.sq_sqrt hmass.le
    rw [← hframe]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [atomMatrix_smul, hsq, smul_smul]
    congr 1
    field_simp

/-- **THE PLANE WEIGHT DEFICIT LAW.**  A plane Parseval family whose weights total
STRICTLY LESS THAN ONE carries a pair that beats every nonzero plane probe.

Unconditional, at every size.  Rescale the family to a rank-two design — the atoms
stretch by the square root of the total weight and the weights renormalise — spend
the landed rank-two GTZ `Gtz.gtz_rank_two`, and read the weak domination back
through the stretch.  The deficit is exactly what turns `<=` into `<`.

A rank-two design is the case of total weight one, where the conclusion is false:
its dominating pairs need not be strict.  Every plane sub-frame of a higher-rank
design that drops the atoms reading the normal is of this shape, and the weight it
drops is the whole content of the law. -/
theorem exists_planeStrict_of_weightSum_lt_one {members : ℕ}
    (atomOf : Fin (members + 1) → (Fin 2 → ℝ)) (weightOf : Fin (members + 1) → ℝ)
    (hpos : ∀ index : Fin (members + 1), 0 < weightOf index)
    (hframe : ∑ index, weightOf index • atomMatrix (atomOf index)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hdeficit : ∑ other, weightOf other < 1) :
    ∃ first second : Fin (members + 1), first ≠ second
      ∧ ∀ probe : Fin 2 → ℝ, probe ≠ 0 →
          probe ⬝ᵥ probe
            < (atomOf first ⬝ᵥ probe) ^ 2 + (atomOf second ⬝ᵥ probe) ^ 2 := by
  classical
  have hmass : 0 < ∑ other, weightOf other :=
    Finset.sum_pos (fun other _ => hpos other) ⟨0, Finset.mem_univ 0⟩
  have hsq : Real.sqrt (∑ other, weightOf other) ^ 2 = ∑ other, weightOf other :=
    Real.sq_sqrt hmass.le
  obtain ⟨pairSet, hcard, hdominates⟩ :=
    gtz_rank_two (members + 1) (scaledPlaneFrame atomOf weightOf hpos hframe)
  obtain ⟨first, second, hne, hpairEq⟩ := Finset.card_eq_two.mp hcard
  refine ⟨first, second, hne, fun probe hprobeNe => ?_⟩
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
  rw [star_trivial, dominationGap_form, hpairEq, Finset.sum_pair hne] at hform
  have hreading : ∀ index : Fin (members + 1),
      (scaledPlaneFrame atomOf weightOf hpos hframe).atom index ⬝ᵥ probe
        = Real.sqrt (∑ other, weightOf other) * (atomOf index ⬝ᵥ probe) := by
    intro index
    show (Real.sqrt (∑ other, weightOf other) • atomOf index) ⬝ᵥ probe = _
    rw [smul_dotProduct, smul_eq_mul]
  rw [hreading first, hreading second] at hform
  have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
  have hexpand : (Real.sqrt (∑ other, weightOf other) * (atomOf first ⬝ᵥ probe)) ^ 2
        + (Real.sqrt (∑ other, weightOf other) * (atomOf second ⬝ᵥ probe)) ^ 2
      = (∑ other, weightOf other)
        * ((atomOf first ⬝ᵥ probe) ^ 2 + (atomOf second ⬝ᵥ probe) ^ 2) := by
    rw [mul_pow, mul_pow, hsq]
    ring
  rw [hexpand] at hform
  nlinarith [hform, hprobePos, hmass, hdeficit]

/-- The five-member reading of the deficit law, the shape Part 6 consumes. -/
theorem exists_planeStrict_of_fiveFrame (atomOf : Fin 5 → (Fin 2 → ℝ))
    (weightOf : Fin 5 → ℝ) (hpos : ∀ index : Fin 5, 0 < weightOf index)
    (hframe : ∑ index, weightOf index • atomMatrix (atomOf index)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hdeficit : ∑ other, weightOf other < 1) :
    ∃ first second : Fin 5, first ≠ second
      ∧ ∀ probe : Fin 2 → ℝ, probe ≠ 0 →
          probe ⬝ᵥ probe
            < (atomOf first ⬝ᵥ probe) ^ 2 + (atomOf second ⬝ᵥ probe) ^ 2 :=
  exists_planeStrict_of_weightSum_lt_one (members := 4) atomOf weightOf hpos hframe hdeficit

/-- A unit plane vector cannot join a strictly dominating plane pair: the probe
orthogonal to its partner leaves the unit vector alone against the whole probe,
and Cauchy-Schwarz forbids that. -/
theorem not_planeStrict_of_unit (partnerVec unitVec : Fin 2 → ℝ)
    (hunit : unitVec ⬝ᵥ unitVec = 1)
    (hstrict : ∀ probe : Fin 2 → ℝ, probe ≠ 0 →
      probe ⬝ᵥ probe < (partnerVec ⬝ᵥ probe) ^ 2 + (unitVec ⬝ᵥ probe) ^ 2) : False := by
  classical
  set probe : Fin 2 → ℝ := ![-(partnerVec 1), partnerVec 0] with hprobeDef
  by_cases hzero : partnerVec = 0
  · have hvalue := hstrict ![1, 0] (by
      intro hcontra
      have hentry := congrFun hcontra 0
      simp at hentry)
    rw [hzero] at hvalue
    simp only [zero_dotProduct] at hvalue
    have hschwarz : (unitVec ⬝ᵥ (![1, 0] : Fin 2 → ℝ)) ^ 2
        ≤ (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] := by
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] at hunit ⊢
      nlinarith [sq_nonneg (unitVec 0 * 0 - unitVec 1 * 1), hunit]
    nlinarith [hvalue, hschwarz]
  · have hprobeNe : probe ≠ 0 := by
      intro hcontra
      refine hzero (funext fun coord => ?_)
      have hfirst := congrFun hcontra 0
      have hsecond := congrFun hcontra 1
      simp only [hprobeDef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Pi.zero_apply, neg_eq_zero] at hfirst hsecond
      fin_cases coord
      · simpa using hsecond
      · simpa using hfirst
    have hperp : partnerVec ⬝ᵥ probe = 0 := by
      simp only [hprobeDef, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
      ring
    have hvalue := hstrict probe hprobeNe
    rw [hperp] at hvalue
    have hschwarz : (unitVec ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe := by
      simp only [dotProduct, Fin.sum_univ_two] at hunit ⊢
      nlinarith [sq_nonneg (unitVec 0 * probe 1 - unitVec 1 * probe 0), hunit]
    nlinarith [hvalue, hschwarz]

/-- **A LIGHT OFF-PLANE PAIR HANDS THE PLANE A STRICT COPLANAR PAIR.**  At a
rank-three design with four coplanar atoms whose two off-plane shadows are
PARALLEL and light on weighted average, two of the FOUR COPLANAR atoms beat the
plane strictly.

The two parallel off-plane shadows contribute a single rank-one term to the
in-plane Parseval identity, carrying their total shadow mass.  Replacing them by
one fictitious UNIT atom of that mass leaves a five-member plane family of total
weight below one, and `Gtz.exists_planeStrict_of_fiveFrame` returns a strict pair.
`Gtz.not_planeStrict_of_unit` keeps the fictitious atom out of it. -/
theorem exists_coplanar_planeStrictPair_of_lightOffPlane (design : WeightedDesign 6 3)
    (frame : AxisFrame) {flatOne flatTwo flatThree flatFour offFirst offSecond : Fin 6}
    (hneOneTwo : flatOne ≠ flatTwo) (hneOneThree : flatOne ≠ flatThree)
    (hneOneFour : flatOne ≠ flatFour) (hneTwoThree : flatTwo ≠ flatThree)
    (hneTwoFour : flatTwo ≠ flatFour) (hneThreeFour : flatThree ≠ flatFour)
    (hoffNe : offFirst ≠ offSecond)
    (hcompl : ({flatOne, flatTwo, flatThree, flatFour} : Finset (Fin 6))ᶜ
      = {offFirst, offSecond})
    (hflat : ∀ label ∈ ({flatOne, flatTwo, flatThree, flatFour} : Finset (Fin 6)),
      design.atom label ⬝ᵥ frame.axis = 0)
    (hshadowNe : (frameShadow design frame).atom offFirst ≠ 0)
    (hwedge : planeWedge ((frameShadow design frame).atom offFirst)
      ((frameShadow design frame).atom offSecond) = 0)
    (hlight : design.weight offFirst
          * leverageOf ((frameShadow design frame).atom offFirst)
        + design.weight offSecond
          * leverageOf ((frameShadow design frame).atom offSecond)
      < design.weight offFirst + design.weight offSecond) :
    ∃ pairFirst pairSecond : Fin 6,
      pairFirst ∈ ({flatOne, flatTwo, flatThree, flatFour} : Finset (Fin 6))
        ∧ pairSecond ∈ ({flatOne, flatTwo, flatThree, flatFour} : Finset (Fin 6))
        ∧ pairFirst ≠ pairSecond
        ∧ PlaneStrictPair design frame.axis pairFirst pairSecond := by
  classical
  set shadow := frameShadow design frame with hshadowDef
  set flatSet : Finset (Fin 6) := {flatOne, flatTwo, flatThree, flatFour} with hflatSetDef
  -- the shared direction of the two off-plane shadows
  obtain ⟨ratio, hratio⟩ := exists_smul_of_planeWedge_eq_zero hshadowNe hwedge
  set normSq := shadow.atom offFirst ⬝ᵥ shadow.atom offFirst with hnormSqDef
  have hnormPos : 0 < normSq := dotProduct_self_pos hshadowNe
  have hsqrtPos : 0 < Real.sqrt normSq := Real.sqrt_pos.mpr hnormPos
  set unitVec : Fin 2 → ℝ := (Real.sqrt normSq)⁻¹ • shadow.atom offFirst with hunitDef
  have hunit : unitVec ⬝ᵥ unitVec = 1 := by
    rw [hunitDef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← mul_inv, Real.mul_self_sqrt hnormPos.le, ← hnormSqDef]
    exact inv_mul_cancel₀ hnormPos.ne'
  set shadowMass := design.weight offFirst * leverageOf (shadow.atom offFirst)
    + design.weight offSecond * leverageOf (shadow.atom offSecond) with hmassDef
  have hlevFirst : leverageOf (shadow.atom offFirst) = normSq := leverageOf_eq_dotProduct _
  have hlevSecond : leverageOf (shadow.atom offSecond) = ratio ^ 2 * normSq := by
    rw [leverageOf_eq_dotProduct, hratio, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, ← hnormSqDef]
    ring
  have hmassValue : shadowMass
      = (design.weight offFirst + design.weight offSecond * ratio ^ 2) * normSq := by
    rw [hmassDef, hlevFirst, hlevSecond]
    ring
  have hcoeffPos : 0 < design.weight offFirst + design.weight offSecond * ratio ^ 2 := by
    have := design.weight_pos offFirst
    nlinarith [(design.weight_pos offSecond).le, sq_nonneg ratio]
  have hmassPos : 0 < shadowMass := by
    rw [hmassValue]
    exact mul_pos hcoeffPos hnormPos
  -- the five-member plane family
  set atomOf : Fin 5 → (Fin 2 → ℝ) :=
    ![shadow.atom flatOne, shadow.atom flatTwo, shadow.atom flatThree,
      shadow.atom flatFour, unitVec] with hatomDef
  set weightOf : Fin 5 → ℝ :=
    ![design.weight flatOne, design.weight flatTwo, design.weight flatThree,
      design.weight flatFour, shadowMass] with hweightDef
  have hpos : ∀ index : Fin 5, 0 < weightOf index := by
    intro index
    fin_cases index <;>
      simp only [hweightDef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
    · exact design.weight_pos flatOne
    · exact design.weight_pos flatTwo
    · exact design.weight_pos flatThree
    · exact design.weight_pos flatFour
    · exact hmassPos
  -- the two off-plane rank-one terms collapse to the fictitious unit atom
  have hcollapse : shadowMass • atomMatrix unitVec
      = design.weight offFirst • atomMatrix (shadow.atom offFirst)
        + design.weight offSecond • atomMatrix (shadow.atom offSecond) := by
    have hunitMatrix : atomMatrix unitVec = normSq⁻¹ • atomMatrix (shadow.atom offFirst) := by
      rw [hunitDef, atomMatrix_smul, inv_pow, Real.sq_sqrt hnormPos.le]
    have hsecondMatrix : atomMatrix (shadow.atom offSecond)
        = ratio ^ 2 • atomMatrix (shadow.atom offFirst) := by
      rw [hratio, atomMatrix_smul]
    rw [hunitMatrix, hsecondMatrix, smul_smul, hmassValue, smul_smul, ← add_smul]
    congr 1
    field_simp
  -- the flat part of Parseval, unrolled
  have hflatSum : ∑ label ∈ flatSet, design.weight label • atomMatrix (shadow.atom label)
      = design.weight flatOne • atomMatrix (shadow.atom flatOne)
        + design.weight flatTwo • atomMatrix (shadow.atom flatTwo)
        + design.weight flatThree • atomMatrix (shadow.atom flatThree)
        + design.weight flatFour • atomMatrix (shadow.atom flatFour) := by
    rw [hflatSetDef, Finset.sum_insert (by simp [hneOneTwo, hneOneThree, hneOneFour]),
      Finset.sum_insert (by simp [hneTwoThree, hneTwoFour]),
      Finset.sum_insert (by simp [hneThreeFour]), Finset.sum_singleton]
    abel
  have hframe : ∑ index, weightOf index • atomMatrix (atomOf index)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hparseval : ∑ label : Fin 6, shadow.weight label • atomMatrix (shadow.atom label)
        = (1 : Matrix (Fin 2) (Fin 2) ℝ) := shadow.isParseval
    have hweightEq : ∀ label : Fin 6, shadow.weight label = design.weight label :=
      fun label => rfl
    rw [Finset.sum_congr rfl fun label (_ : label ∈ Finset.univ) => by
      rw [hweightEq label]] at hparseval
    have hsplit := Finset.sum_add_sum_compl flatSet
      (fun label => design.weight label • atomMatrix (shadow.atom label))
    rw [hparseval] at hsplit
    rw [hcompl, Finset.sum_pair hoffNe, hflatSum] at hsplit
    rw [Fin.sum_univ_five]
    simp only [hatomDef, hweightDef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]
    rw [hcollapse]
    rw [← hsplit]
  -- the weight deficit
  have hweightSplit : ∑ label ∈ flatSet, design.weight label
      = 1 - design.weight offFirst - design.weight offSecond := by
    have hsplit := Finset.sum_add_sum_compl flatSet design.weight
    rw [design.weight_sum_one, hcompl, Finset.sum_pair hoffNe] at hsplit
    linarith [hsplit]
  have hflatWeightSum : ∑ label ∈ flatSet, design.weight label
      = design.weight flatOne + design.weight flatTwo + design.weight flatThree
        + design.weight flatFour := by
    rw [hflatSetDef, Finset.sum_insert (by simp [hneOneTwo, hneOneThree, hneOneFour]),
      Finset.sum_insert (by simp [hneTwoThree, hneTwoFour]),
      Finset.sum_insert (by simp [hneThreeFour]), Finset.sum_singleton]
    ring
  have hdeficit : ∑ index, weightOf index < 1 := by
    rw [Fin.sum_univ_five]
    simp only [hweightDef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
    have hchain := hflatWeightSum.symm.trans hweightSplit
    linarith [hchain, hlight]
  obtain ⟨firstIndex, secondIndex, hindexNe, hstrict⟩ :=
    exists_planeStrict_of_fiveFrame atomOf weightOf hpos hframe hdeficit
  -- the fictitious unit atom cannot join the pair
  set labelOf : Fin 5 → Fin 6 := ![flatOne, flatTwo, flatThree, flatFour, flatOne]
    with hlabelOfDef
  have hatomAt : ∀ index : Fin 5, index ≠ 4 →
      atomOf index = shadow.atom (labelOf index) := by
    intro index hindex
    fin_cases index
    · simp [hatomDef, hlabelOfDef]
    · simp [hatomDef, hlabelOfDef]
    · simp [hatomDef, hlabelOfDef]
    · simp [hatomDef, hlabelOfDef]
    · exact absurd rfl hindex
  have hmemAt : ∀ index : Fin 5, index ≠ 4 → labelOf index ∈ flatSet := by
    intro index hindex
    fin_cases index
    · simp [hlabelOfDef, hflatSetDef]
    · simp [hlabelOfDef, hflatSetDef]
    · simp [hlabelOfDef, hflatSetDef]
    · simp [hlabelOfDef, hflatSetDef]
    · exact absurd rfl hindex
  have hinjAt : ∀ indexFirst indexSecond : Fin 5, indexFirst ≠ 4 → indexSecond ≠ 4 →
      indexFirst ≠ indexSecond → labelOf indexFirst ≠ labelOf indexSecond := by
    have hswapOneTwo := hneOneTwo.symm
    have hswapOneThree := hneOneThree.symm
    have hswapOneFour := hneOneFour.symm
    have hswapTwoThree := hneTwoThree.symm
    have hswapTwoFour := hneTwoFour.symm
    have hswapThreeFour := hneThreeFour.symm
    intro indexFirst indexSecond hfirst hsecond hdistinct
    fin_cases indexFirst <;> fin_cases indexSecond <;>
      simp only [hlabelOfDef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
        Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      first
        | exact absurd rfl hdistinct
        | exact absurd rfl hfirst
        | exact absurd rfl hsecond
        | assumption
        | (exfalso; exact hdistinct rfl)
        | (exfalso; exact hfirst rfl)
        | (exfalso; exact hsecond rfl)
  have hunitAt : atomOf 4 = unitVec := by
    simp only [hatomDef, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
  have hfirstNe : firstIndex ≠ 4 := by
    intro hcontra
    refine not_planeStrict_of_unit (atomOf secondIndex) unitVec hunit (fun probe hprobe => ?_)
    have hvalue := hstrict probe hprobe
    rw [hcontra, hunitAt] at hvalue
    linarith [hvalue]
  have hsecondNe : secondIndex ≠ 4 := by
    intro hcontra
    refine not_planeStrict_of_unit (atomOf firstIndex) unitVec hunit (fun probe hprobe => ?_)
    have hvalue := hstrict probe hprobe
    rw [hcontra, hunitAt] at hvalue
    linarith [hvalue]
  refine ⟨labelOf firstIndex, labelOf secondIndex, hmemAt firstIndex hfirstNe,
    hmemAt secondIndex hsecondNe, hinjAt firstIndex secondIndex hfirstNe hsecondNe hindexNe,
    fun planar hperp hplanarNe => ?_⟩
  set probe : Fin 2 → ℝ := ![planar ⬝ᵥ frame.pOne, planar ⬝ᵥ frame.pTwo] with hprobeDef
  have hresolve := orthonormalFrame_resolution frame.oneOne frame.twoTwo frame.axisAxis
    frame.oneTwo frame.oneAxis frame.twoAxis planar
  rw [hperp, zero_smul, add_zero] at hresolve
  have hprobeNe : probe ≠ 0 := by
    intro hcontra
    have hfirstCoord : planar ⬝ᵥ frame.pOne = 0 := by
      have hentry := congrFun hcontra 0
      simpa [hprobeDef] using hentry
    have hsecondCoord : planar ⬝ᵥ frame.pTwo = 0 := by
      have hentry := congrFun hcontra 1
      simpa [hprobeDef] using hentry
    rw [hfirstCoord, hsecondCoord, zero_smul, zero_smul, zero_add] at hresolve
    exact hplanarNe hresolve
  have hsplitPlanar := frame.dotProduct_self_split planar
  rw [hperp] at hsplitPlanar
  have hnormProbe : probe ⬝ᵥ probe = planar ⬝ᵥ planar := by
    have hval : probe ⬝ᵥ probe
        = (planar ⬝ᵥ frame.pOne) ^ 2 + (planar ⬝ᵥ frame.pTwo) ^ 2 := by
      rw [hprobeDef, dot_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring
    rw [hval, hsplitPlanar]
    ring
  have hflatReading : ∀ label : Fin 6, label ∈ flatSet →
      shadow.atom label ⬝ᵥ probe = design.atom label ⬝ᵥ planar := by
    intro label hlabel
    have hlabelFlat := hflat label hlabel
    have hleft : shadow.atom label ⬝ᵥ probe
        = (design.atom label ⬝ᵥ frame.pOne) * (planar ⬝ᵥ frame.pOne)
          + (design.atom label ⬝ᵥ frame.pTwo) * (planar ⬝ᵥ frame.pTwo) := by
      rw [hshadowDef, frameShadow_atom, hprobeDef, dot_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hlabelResolve := orthonormalFrame_resolution frame.oneOne frame.twoTwo
      frame.axisAxis frame.oneTwo frame.oneAxis frame.twoAxis (design.atom label)
    rw [hlabelFlat, zero_smul, add_zero] at hlabelResolve
    have hright : design.atom label ⬝ᵥ planar
        = (design.atom label ⬝ᵥ frame.pOne) * (frame.pOne ⬝ᵥ planar)
          + (design.atom label ⬝ᵥ frame.pTwo) * (frame.pTwo ⬝ᵥ planar) := by
      conv_lhs => rw [hlabelResolve]
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    rw [hleft, hright, dotProduct_comm frame.pOne planar, dotProduct_comm frame.pTwo planar]
  have hvalue := hstrict probe hprobeNe
  rw [hatomAt firstIndex hfirstNe, hatomAt secondIndex hsecondNe,
    hflatReading _ (hmemAt firstIndex hfirstNe), hflatReading _ (hmemAt secondIndex hsecondNe),
    hnormProbe] at hvalue
  exact hvalue

end Gtz
