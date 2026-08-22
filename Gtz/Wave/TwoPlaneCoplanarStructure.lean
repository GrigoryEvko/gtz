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

end Gtz
