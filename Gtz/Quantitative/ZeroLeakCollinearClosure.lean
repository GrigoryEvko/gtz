import Mathlib
import Gtz.Design.SphereExistence
import Gtz.LinAlg.ProjectionForm
import Gtz.Quantitative.ChartStationary

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The rank-three rigidity behind the zero-leak branch

Two facts are already in place elsewhere and are consumed, not re-proved:

* an active block whose tight direction has no off-block residual pins every atom
  of its support at the weight floor `-value`, and puts the direction in the chart
  kernel;
* at a floor atom EVERY positively weighted projected tight direction vanishes.

What has been missing is the step that turns "two atoms at the floor" into "the
projected tight directions all lie on one line", which is a statement about rank
three and nothing else.  This file supplies it, from the design side, where the
cross product makes it elementary and no dimension count is needed:

* `Gtz.crossProduct_crossProduct_left` — the triple-product expansion.
* `Gtz.exists_smul_crossProduct_of_dotProduct_eq_zero` — a vector orthogonal to
  two vectors of nonvanishing cross product is a multiple of that cross product.
* `Gtz.exists_unitNormal_of_projectionFixed_vanishing_pair` — **THE MISSING RUNG.**
  For a parallel-free rank-three design and any two distinct atoms there is a
  single unit chart-fixed vector such that EVERY chart-fixed vector vanishing at
  those two atoms is a multiple of it.  Unconditional, and about designs alone.
* `Gtz.exists_unitNormal_projected_tightDir_collinear` — the socket: the same
  statement read at a chart stationarity datum, delivering exactly the
  collinearity hypothesis a closing theorem consumes.

The bridge is `projectionOfDesign D = S Sᵀ` with `Sᵀ S = 1`: a chart-fixed vector
is `S w`, its `c`-th coordinate is `sqrt (t c) * (a c ⬝ w)`, and `S` is an isometry
on the fibre, so an orthogonality statement in three space transports verbatim.
-/

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## Part 1 -- the triple product in three space -/

/-- **The triple-product expansion.**  `(a × b) × w = (w ⬝ a) b - (w ⬝ b) a`,
componentwise. -/
theorem crossProduct_crossProduct_left (leftVec rightVec probe : Fin 3 → ℝ) :
    crossProduct (crossProduct leftVec rightVec) probe
      = (probe ⬝ᵥ leftVec) • rightVec - (probe ⬝ᵥ rightVec) • leftVec := by
  funext coordinate
  fin_cases coordinate <;>
    simp [cross_apply, dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply] <;> ring

/-- **Two orthogonality constraints in three space leave a line.**  A vector
orthogonal to both members of a pair whose cross product does not vanish is a
multiple of that cross product. -/
theorem exists_smul_crossProduct_of_dotProduct_eq_zero {leftVec rightVec probe : Fin 3 → ℝ}
    (hcrossNe : crossProduct leftVec rightVec ≠ 0)
    (hleft : probe ⬝ᵥ leftVec = 0) (hright : probe ⬝ᵥ rightVec = 0) :
    ∃ ratio : ℝ, probe = ratio • crossProduct leftVec rightVec := by
  refine eq_smul_of_crossProduct_eq_zero hcrossNe ?_
  rw [crossProduct_crossProduct_left, hleft, hright, zero_smul, zero_smul, sub_zero]

/-! ## Part 2 -- the design bridge -/

/-- The coordinates of a vector pulled up from the fibre. -/
theorem scaledAtomRows_mulVec_apply {rank : ℕ} (design : WeightedDesign size rank)
    (fibre : Fin rank → ℝ) (atomIndex : Fin size) :
    (scaledAtomRows design *ᵥ fibre) atomIndex
      = Real.sqrt (design.weight atomIndex) * (design.atom atomIndex ⬝ᵥ fibre) := by
  show (fun colIndex => scaledAtomRows design atomIndex colIndex) ⬝ᵥ fibre = _
  have hrow : (fun colIndex => scaledAtomRows design atomIndex colIndex)
      = Real.sqrt (design.weight atomIndex) • design.atom atomIndex := by
    funext colIndex
    rw [scaledAtomRows_row]
  rw [hrow, smul_dotProduct, smul_eq_mul]

/-- Pulling up from the fibre preserves the norm: `Sᵀ S = 1`. -/
theorem dotProduct_scaledAtomRows_mulVec_self {rank : ℕ} (design : WeightedDesign size rank)
    (fibre : Fin rank → ℝ) :
    (scaledAtomRows design *ᵥ fibre) ⬝ᵥ (scaledAtomRows design *ᵥ fibre) = fibre ⬝ᵥ fibre := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
    transpose_mul_scaledAtomRows, Matrix.one_mulVec]

/-- The chart fixes exactly what the fibre pulls up. -/
theorem projectionOfDesign_mulVec_scaledAtomRows_mulVec {rank : ℕ}
    (design : WeightedDesign size rank) (fibre : Fin rank → ℝ) :
    projectionOfDesign design *ᵥ (scaledAtomRows design *ᵥ fibre)
      = scaledAtomRows design *ᵥ fibre := by
  rw [projectionOfDesign, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    transpose_mul_scaledAtomRows, Matrix.mul_one]

/-- A chart-fixed vector is the pull-up of its own fibre image. -/
theorem eq_scaledAtomRows_mulVec_of_projectionOfDesign_mulVec_eq {rank : ℕ}
    (design : WeightedDesign size rank) {ambient : Fin size → ℝ}
    (hfixed : projectionOfDesign design *ᵥ ambient = ambient) :
    ambient = scaledAtomRows design *ᵥ ((scaledAtomRows design)ᵀ *ᵥ ambient) := by
  rw [Matrix.mulVec_mulVec, ← projectionOfDesign, hfixed]

/-- A chart-fixed vector vanishes at an atom exactly when its fibre image is
orthogonal to that atom's direction: the square root of a positive weight is
never zero. -/
theorem dotProduct_atom_eq_zero_of_apply_eq_zero {rank : ℕ}
    (design : WeightedDesign size rank) {ambient : Fin size → ℝ}
    (hfixed : projectionOfDesign design *ᵥ ambient = ambient) {atomIndex : Fin size}
    (hvanish : ambient atomIndex = 0) :
    design.atom atomIndex ⬝ᵥ ((scaledAtomRows design)ᵀ *ᵥ ambient) = 0 := by
  have hpull := eq_scaledAtomRows_mulVec_of_projectionOfDesign_mulVec_eq design hfixed
  have hcoord := scaledAtomRows_mulVec_apply design
    ((scaledAtomRows design)ᵀ *ᵥ ambient) atomIndex
  rw [← congrFun hpull atomIndex, hvanish] at hcoord
  have hsqrt : Real.sqrt (design.weight atomIndex) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (design.weight_pos atomIndex))
  exact (mul_eq_zero.mp hcoord.symm).resolve_left hsqrt

/-! ## Part 3 -- the missing rung -/

/-- The unit normal cut out by a pair of atoms: the cross product of their
directions, normalised in the fibre and pulled up to the chart. -/
noncomputable def pairNormal (design : WeightedDesign size 3) (first second : Fin size) :
    Fin size → ℝ :=
  scaledAtomRows design *ᵥ
    ((Real.sqrt (crossProduct (design.atom first) (design.atom second)
      ⬝ᵥ crossProduct (design.atom first) (design.atom second)))⁻¹
      • crossProduct (design.atom first) (design.atom second))

/-- **THE MISSING RUNG.**  In a parallel-free rank-three design, any two distinct
atoms determine a single unit chart-fixed direction, and EVERY chart-fixed vector
vanishing at both of those atoms is a multiple of it.

Nothing here is about stationarity, about a value, or about a counterexample: it
is a fact about every parallel-free design at rank three, and both quantifiers
are inhabited. -/
theorem exists_unitNormal_of_projectionFixed_vanishing_pair
    (design : WeightedDesign size 3) (hsimple : ¬ HasParallelPair design)
    {first second : Fin size} (hne : first ≠ second) :
    projectionOfDesign design *ᵥ pairNormal design first second = pairNormal design first second
      ∧ pairNormal design first second ⬝ᵥ pairNormal design first second = 1
      ∧ ∀ ambient : Fin size → ℝ, projectionOfDesign design *ᵥ ambient = ambient →
          ambient first = 0 → ambient second = 0 →
          ∃ ratio : ℝ, ambient = ratio • pairNormal design first second := by
  classical
  set axis : Fin 3 → ℝ := crossProduct (design.atom first) (design.atom second) with haxisDef
  have haxisNe : axis ≠ 0 :=
    crossProduct_atom_ne_zero_of_not_hasParallelPair design hsimple hne
  have haxisPos : 0 < axis ⬝ᵥ axis := dotProduct_self_pos haxisNe
  set lengthValue : ℝ := Real.sqrt (axis ⬝ᵥ axis) with hlengthDef
  have hlengthPos : 0 < lengthValue := Real.sqrt_pos.mpr haxisPos
  have hlengthSq : lengthValue * lengthValue = axis ⬝ᵥ axis :=
    Real.mul_self_sqrt haxisPos.le
  have hlengthNe : lengthValue ≠ 0 := ne_of_gt hlengthPos
  have hnormalDef : pairNormal design first second
      = scaledAtomRows design *ᵥ (lengthValue⁻¹ • axis) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hnormalDef]
    exact projectionOfDesign_mulVec_scaledAtomRows_mulVec design _
  · rw [hnormalDef, dotProduct_scaledAtomRows_mulVec_self, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hlengthSq]
    field_simp
  · intro ambient hfixed hfirst hsecond
    have hleft := dotProduct_atom_eq_zero_of_apply_eq_zero design hfixed hfirst
    have hright := dotProduct_atom_eq_zero_of_apply_eq_zero design hfixed hsecond
    obtain ⟨ratio, hratio⟩ := exists_smul_crossProduct_of_dotProduct_eq_zero
      (leftVec := design.atom first) (rightVec := design.atom second)
      (probe := (scaledAtomRows design)ᵀ *ᵥ ambient) haxisNe
      (by rw [dotProduct_comm]; exact hleft) (by rw [dotProduct_comm]; exact hright)
    refine ⟨ratio * lengthValue, ?_⟩
    have hpull := eq_scaledAtomRows_mulVec_of_projectionOfDesign_mulVec_eq design hfixed
    rw [hpull, hratio, hnormalDef, ← Matrix.mulVec_smul, smul_smul]
    congr 1
    rw [← haxisDef]
    congr 1
    field_simp

/-! ## Part 4 -- the socket -/

variable {activeIndex : Type*}

/-- **THE COLLINEARITY PRODUCTION.**  At a chart stationarity datum carried by a
parallel-free rank-three design, if every positively weighted projected tight
direction vanishes at two distinct atoms then they are all multiples of a single
unit chart-fixed vector.

The conclusion is exactly the hypothesis bundle a closing theorem consumes; the
input `hvanish` is what the floor-atom row law supplies at two atoms sitting at
the weight floor. -/
theorem exists_unitNormal_projected_tightDir_collinear
    (design : WeightedDesign size 3) (hsimple : ¬ HasParallelPair design)
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData 3 (projectionOfDesign design) design.weight value
      activeSet activeSubset activeWeight tightDir)
    {first second : Fin size} (hne : first ≠ second)
    (hvanish : ∀ activeLabel ∈ activeSet, 0 < activeWeight activeLabel →
      (projectionOfDesign design *ᵥ tightDir activeLabel) first = 0
        ∧ (projectionOfDesign design *ᵥ tightDir activeLabel) second = 0) :
    ∃ normal : Fin size → ℝ,
      projectionOfDesign design *ᵥ normal = normal ∧ normal ⬝ᵥ normal = 1
        ∧ ∀ activeLabel ∈ activeSet, 0 < activeWeight activeLabel →
            ∃ scale : ℝ, projectionOfDesign design *ᵥ tightDir activeLabel = scale • normal := by
  obtain ⟨hfixed, hunit, hspan⟩ :=
    exists_unitNormal_of_projectionFixed_vanishing_pair design hsimple hne
  refine ⟨pairNormal design first second, hfixed, hunit, ?_⟩
  intro activeLabel hmem hpositive
  obtain ⟨hfirst, hsecond⟩ := hvanish activeLabel hmem hpositive
  exact hspan _ (by rw [Matrix.mulVec_mulVec, hdata.isIdempotent]) hfirst hsecond

end Gtz
