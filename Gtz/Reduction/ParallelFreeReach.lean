import Mathlib
import Gtz.Reduction.ConnectednessRoute
import Gtz.Quantitative.ExcessGapCensus
import Gtz.Reduction.CholeskyWhitening

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Path-connectedness of the parallel-free spanning tuples (step T1 of the reach hypothesis)

`Gtz.ParallelFreeReachesAnchor 6 3 icosaDesign` — the ONE open hypothesis of the landed
connectedness route (`Gtz/Reduction/ConnectednessRoute.lean:416`) — asks for a continuous
path of atom families between any parallel-free design and the icosahedron, staying
parallel-free and design-realizable.  The proof decomposes as

  T1 (THIS FILE): the space of six-tuples in `ℝ³` that are pairwise non-parallel and
      spanning is path-connected — `JoinedIn`-connected inside itself;
  T2 (CholeskyTransfer): a spanning-tuple path whitens to a Parseval path by explicit
      3×3 Cholesky, preserving the parallelism pattern;
  T3 (composition file, later): rows `√w_c • g_c` translate designs to tuples and back.

The construction here is ELEMENTARY on purpose — none of `Matrix.PosSemidef.sqrt`,
Sard, semialgebraic machinery, or Hausdorff dimension is used.  A single coordinate
moves at a time, along two straight segments through a waypoint on the moment curve
`t ↦ (1, t, t²)`; avoiding the five forbidden lines is the statement that a nonzero
quadratic has at most two roots.  Spanning survives because three untouched columns
(a "tripod") always span: first the three non-tripod coordinates walk onto the moment
curve, then the tripod follows, three placed moment vectors being automatically
independent (Vandermonde, again the quadratic).  Any two good tuples therefore reach a
common moment-curve hub.

The rank signature is visible: two vectors of `ℝ³` are parallel on a codimension-2 set,
which is why single-coordinate movers can steer around all five lines at once.  At rank
two the same lines are codimension-1 walls and this construction (correctly) dies.
-/

namespace Gtz

open Function Set

/-! ## The space -/

/-- A six-tuple of rows has a parallel pair — the tuple-level mirror of
`Gtz.HasParallelPair` (same quantifier shape, same orientation). -/
def HasParallelRows (rows : Fin 6 → Fin 3 → ℝ) : Prop :=
  ∃ (keptLabel dropLabel : Fin 6) (ratio : ℝ),
    keptLabel ≠ dropLabel ∧ rows dropLabel = ratio • rows keptLabel

/-- The rows span `ℝ³`, in the dual form the whole file consumes: only the zero probe
is orthogonal to every row. -/
def RowsSpan (rows : Fin 6 → Fin 3 → ℝ) : Prop :=
  ∀ probe : Fin 3 → ℝ, (∀ c, dotProduct (rows c) probe = 0) → probe = 0

/-- The good tuples: pairwise non-parallel and spanning.  These are exactly the row
systems of parallel-free weighted `(6,3)` designs after folding the weights in. -/
def GoodTuple (rows : Fin 6 → Fin 3 → ℝ) : Prop :=
  ¬ HasParallelRows rows ∧ RowsSpan rows

/-- The good tuples as a set, the `F` of every `JoinedIn` below. -/
def goodTuples : Set (Fin 6 → Fin 3 → ℝ) := {rows | GoodTuple rows}

theorem noRatio_of_goodTuple {rows : Fin 6 → Fin 3 → ℝ} (hgood : GoodTuple rows)
    {keptLabel dropLabel : Fin 6} (hne : keptLabel ≠ dropLabel) (ratio : ℝ) :
    rows dropLabel ≠ ratio • rows keptLabel :=
  fun heq => hgood.1 ⟨keptLabel, dropLabel, ratio, hne, heq⟩

theorem row_ne_zero_of_goodTuple {rows : Fin 6 → Fin 3 → ℝ} (hgood : GoodTuple rows)
    (c : Fin 6) : rows c ≠ 0 := by
  intro hzero
  rcases eq_or_ne c 0 with rfl | hc
  · exact noRatio_of_goodTuple hgood (show (1 : Fin 6) ≠ 0 by decide) 0
      (by rw [hzero, zero_smul])
  · exact noRatio_of_goodTuple hgood (Ne.symm hc) 0 (by rw [hzero, zero_smul])

/-- Non-parallelism transfers across the pair: if `mover` is off the line of `u` and
`u` is nonzero, then `u` is off the line of `mover` as well. -/
theorem offLine_symm {u mover : Fin 3 → ℝ} (hu : u ≠ 0)
    (hoff : ∀ ratio : ℝ, mover ≠ ratio • u) (ratio : ℝ) : u ≠ ratio • mover := by
  intro heq
  rcases eq_or_ne ratio 0 with rfl | hr
  · rw [zero_smul] at heq
    exact hu heq
  · exact hoff ratio⁻¹ (by rw [heq, smul_smul, inv_mul_cancel₀ hr, one_smul])

/-! ## Cross-product certificates -/

theorem linearIndependent_pair_of_offLine {u target : Fin 3 → ℝ} (hu : u ≠ 0)
    (hoff : ∀ ratio : ℝ, target ≠ ratio • u) :
    LinearIndependent ℝ ![target, u] := by
  refine linearIndependent_fin2.mpr ⟨?_, ?_⟩
  · simpa using hu
  · intro a ha
    exact hoff a (by simpa using ha.symm)

theorem cross_ne_zero_of_offLine {u target : Fin 3 → ℝ} (hu : u ≠ 0)
    (hoff : ∀ ratio : ℝ, target ≠ ratio • u) :
    crossProduct target u ≠ 0 :=
  crossProduct_ne_zero_iff_linearIndependent.mpr
    (linearIndependent_pair_of_offLine hu hoff)

theorem cross_rows_ne_zero_of_goodTuple {rows : Fin 6 → Fin 3 → ℝ}
    (hgood : GoodTuple rows) {c d : Fin 6} (hne : c ≠ d) :
    crossProduct (rows c) (rows d) ≠ 0 :=
  cross_ne_zero_of_offLine (row_ne_zero_of_goodTuple hgood d)
    (fun ratio => noRatio_of_goodTuple hgood (Ne.symm hne) ratio)

/-- If a probe is orthogonal to two independent vectors and to a third vector that is
off their plane, the probe is zero.  This is the tripod's spanning certificate,
proved by the BAC–CAB identity with no `Submodule` machinery. -/
theorem probe_eq_zero_of_offPlane {baseOne baseTwo offVec probe : Fin 3 → ℝ}
    (hcross : crossProduct baseOne baseTwo ≠ 0)
    (hoffPlane : dotProduct offVec (crossProduct baseOne baseTwo) ≠ 0)
    (hprobeOne : dotProduct baseOne probe = 0)
    (hprobeTwo : dotProduct baseTwo probe = 0)
    (hprobeOff : dotProduct offVec probe = 0) : probe = 0 := by
  set normalVec := crossProduct baseOne baseTwo with hnormal
  have hprobeTwo' : probe ⬝ᵥ baseTwo = 0 := by
    rw [dotProduct_comm]; exact hprobeTwo
  have hprobeOne' : probe ⬝ᵥ baseOne = 0 := by
    rw [dotProduct_comm]; exact hprobeOne
  have hcrossProbe : crossProduct probe normalVec = 0 := by
    rw [hnormal, cross_cross_eq_smul_sub_smul']
    simp [hprobeOne, hprobeTwo']
  have hnotIndep : ¬ LinearIndependent ℝ ![probe, normalVec] := by
    intro hindep
    exact (crossProduct_ne_zero_iff_linearIndependent.mpr hindep) hcrossProbe
  rw [linearIndependent_fin2] at hnotIndep
  push Not at hnotIndep
  obtain ⟨scale, hscale⟩ := hnotIndep
    (by simp only [Matrix.cons_val_one]; exact hcross)
  have hprobeEq : probe = scale • normalVec := by
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hscale
    exact hscale.symm
  have hzeroScale : scale * dotProduct offVec normalVec = 0 := by
    have := hprobeOff
    rw [hprobeEq, dotProduct_smul, smul_eq_mul] at this
    exact this
  have hscaleZero : scale = 0 :=
    (mul_eq_zero.mp hzeroScale).resolve_right hoffPlane
  rw [hprobeEq, hscaleZero, zero_smul]

/-- Every good tuple has a row off the plane of any two of its rows — otherwise the
cross product would be a nonzero probe orthogonal to everything. -/
theorem exists_offPlane_row {rows : Fin 6 → Fin 3 → ℝ} (hgood : GoodTuple rows)
    {c d : Fin 6} (hne : c ≠ d) :
    ∃ e : Fin 6, dotProduct (rows e) (crossProduct (rows c) (rows d)) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  exact cross_rows_ne_zero_of_goodTuple hgood hne (hgood.2 _ hnone)

/-! ## The moment curve and quadratic root counting -/

/-- The moment curve `t ↦ (1, t, t²)` — every waypoint and every hub slot lives on it. -/
def momentVec (param : ℝ) : Fin 3 → ℝ := fun coord => param ^ (coord : ℕ)

theorem momentVec_apply_zero (param : ℝ) : momentVec param 0 = 1 := by
  simp [momentVec]

theorem momentVec_apply_one (param : ℝ) : momentVec param 1 = param := by
  simp [momentVec]

theorem momentVec_ne_zero (param : ℝ) : momentVec param ≠ 0 := by
  intro hzero
  have := congrFun hzero 0
  rw [momentVec_apply_zero] at this
  simp at this

theorem momentVec_dot (param : ℝ) (coeffs : Fin 3 → ℝ) :
    dotProduct (momentVec param) coeffs
      = coeffs 0 + coeffs 1 * param + coeffs 2 * param ^ 2 := by
  simp [momentVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Distinct moment-curve points are never parallel: the zeroth coordinate pins the
ratio to one and the first coordinate then pins the parameters. -/
theorem momentVec_offLine {paramOne paramTwo : ℝ} (hne : paramOne ≠ paramTwo)
    (ratio : ℝ) : momentVec paramTwo ≠ ratio • momentVec paramOne := by
  intro heq
  have hzero := congrFun heq 0
  rw [momentVec_apply_zero, Pi.smul_apply, momentVec_apply_zero, smul_eq_mul,
    mul_one] at hzero
  have hone := congrFun heq 1
  rw [momentVec_apply_one, Pi.smul_apply, momentVec_apply_one, smul_eq_mul,
    ← hzero, one_mul] at hone
  exact hne hone.symm

/-- The Vandermonde core: a quadratic vanishing at three distinct points is zero. -/
theorem coeffs_eq_zero_of_three_roots {coeffs : Fin 3 → ℝ} {t1 t2 t3 : ℝ}
    (h12 : t1 ≠ t2) (h13 : t1 ≠ t3) (h23 : t2 ≠ t3)
    (e1 : coeffs 0 + coeffs 1 * t1 + coeffs 2 * t1 ^ 2 = 0)
    (e2 : coeffs 0 + coeffs 1 * t2 + coeffs 2 * t2 ^ 2 = 0)
    (e3 : coeffs 0 + coeffs 1 * t3 + coeffs 2 * t3 ^ 2 = 0) : coeffs = 0 := by
  have d12 : (t1 - t2) * (coeffs 1 + coeffs 2 * (t1 + t2)) = 0 := by
    linear_combination e1 - e2
  have d13 : (t1 - t3) * (coeffs 1 + coeffs 2 * (t1 + t3)) = 0 := by
    linear_combination e1 - e3
  have k12 : coeffs 1 + coeffs 2 * (t1 + t2) = 0 :=
    (mul_eq_zero.mp d12).resolve_left (sub_ne_zero.mpr h12)
  have k13 : coeffs 1 + coeffs 2 * (t1 + t3) = 0 :=
    (mul_eq_zero.mp d13).resolve_left (sub_ne_zero.mpr h13)
  have hquad : coeffs 2 * (t2 - t3) = 0 := by linear_combination k12 - k13
  have h2 : coeffs 2 = 0 :=
    (mul_eq_zero.mp hquad).resolve_right (sub_ne_zero.mpr h23)
  have h1 : coeffs 1 = 0 := by
    have := k12
    rw [h2, zero_mul, add_zero] at this
    exact this
  have h0 : coeffs 0 = 0 := by
    have := e1
    rw [h1, h2, zero_mul, zero_mul, add_zero, add_zero] at this
    exact this
  funext coord
  fin_cases coord <;> simp [h0, h1, h2]

/-- A nonzero quadratic has finitely many roots. -/
theorem finite_setOf_quadratic_root {coeffs : Fin 3 → ℝ} (hne : coeffs ≠ 0) :
    {t : ℝ | coeffs 0 + coeffs 1 * t + coeffs 2 * t ^ 2 = 0}.Finite := by
  by_contra hinf
  have hinfSet : {t : ℝ | coeffs 0 + coeffs 1 * t + coeffs 2 * t ^ 2 = 0}.Infinite :=
    hinf
  obtain ⟨t1, ht1⟩ := hinfSet.nonempty
  obtain ⟨t2, ht2⟩ := (hinfSet.sdiff (Set.finite_singleton t1)).nonempty
  obtain ⟨t3, ht3⟩ :=
    (hinfSet.sdiff ((Set.finite_singleton t1).insert t2)).nonempty
  rw [Set.mem_sdiff, Set.mem_singleton_iff] at ht2
  rw [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff] at ht3
  push Not at ht3
  exact hne (coeffs_eq_zero_of_three_roots
    (fun h => ht2.2 h.symm) (fun h => ht3.2.2 h.symm) (fun h => ht3.2.1 h.symm)
    ht1 ht2.1 ht3.1)

/-- The moment-curve parameters hitting a fixed normal — finitely many whenever the
normal is nonzero. -/
def paramsAgainst (normal : Fin 3 → ℝ) : Set ℝ :=
  {t : ℝ | dotProduct (momentVec t) normal = 0}

theorem finite_paramsAgainst {normal : Fin 3 → ℝ} (hne : normal ≠ 0) :
    (paramsAgainst normal).Finite := by
  have hrewrite : paramsAgainst normal
      = {t : ℝ | normal 0 + normal 1 * t + normal 2 * t ^ 2 = 0} := by
    ext t
    simp [paramsAgainst, momentVec_dot]
  rw [hrewrite]
  exact finite_setOf_quadratic_root hne

/-- The moment-curve parameters whose point is parallel to a fixed vector form a
subsingleton-bounded set: the zeroth coordinate `1` forces the ratio, the first
coordinate then forces the parameter.  No nonvanishing hypothesis is needed. -/
theorem finite_setOf_momentVec_parallel (u : Fin 3 → ℝ) :
    {t : ℝ | ∃ ratio : ℝ, momentVec t = ratio • u}.Finite := by
  refine Set.Finite.subset (Set.finite_singleton (u 1 / u 0)) ?_
  rintro t ⟨ratio, ht⟩
  have hzero := congrFun ht 0
  rw [momentVec_apply_zero, Pi.smul_apply, smul_eq_mul] at hzero
  have hu0 : u 0 ≠ 0 := by
    intro hcontra
    rw [hcontra, mul_zero] at hzero
    exact one_ne_zero hzero
  have hone := congrFun ht 1
  rw [momentVec_apply_one, Pi.smul_apply, smul_eq_mul] at hone
  have hratio : ratio = 1 / u 0 := by
    field_simp
    linarith [hzero]
  rw [Set.mem_singleton_iff, hone, hratio]
  field_simp

/-- Picking a parameter outside any finite bad set. -/
theorem exists_param_avoiding {bad : Set ℝ} (hbad : bad.Finite) : ∃ t, t ∉ bad := by
  obtain ⟨t, ht⟩ := hbad.infinite_compl.nonempty
  exact ⟨t, ht⟩

/-- Picking injectively many parameters outside any finite bad set. -/
theorem exists_params_avoiding (count : ℕ) {bad : Set ℝ} (hbad : bad.Finite) :
    ∃ params : Fin count → ℝ, Function.Injective params ∧ ∀ c, params c ∉ bad := by
  induction count with
  | zero => exact ⟨Fin.elim0, fun x => x.elim0, fun c => c.elim0⟩
  | succ n ih =>
      obtain ⟨params, hinj, havoid⟩ := ih
      obtain ⟨fresh, hfresh⟩ :=
        exists_param_avoiding (hbad.union (Set.finite_range params))
      rw [Set.mem_union] at hfresh
      push Not at hfresh
      refine ⟨Fin.cons fresh params, ?_, ?_⟩
      · rw [Fin.cons_injective_iff]
        exact ⟨hfresh.2, hinj⟩
      · intro c
        refine Fin.cases ?_ ?_ c
        · rw [Fin.cons_zero]
          exact hfresh.1
        · intro j
          rw [Fin.cons_succ]
          exact havoid j

/-! ## Segments avoiding lines -/

/-- The straight segment, as a globally defined map. -/
def seg (start finish : Fin 3 → ℝ) (s : ℝ) : Fin 3 → ℝ :=
  (1 - s) • start + s • finish

theorem seg_zero (start finish : Fin 3 → ℝ) : seg start finish 0 = start := by
  simp [seg]

theorem seg_one (start finish : Fin 3 → ℝ) : seg start finish 1 = finish := by
  simp [seg]

theorem continuous_seg (start finish : Fin 3 → ℝ) : Continuous (seg start finish) :=
  (((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const))

/-- **The avoidance mechanism.**  A segment from `start` (independent of `u`) toward a
waypoint certified off the plane `span {start, u}` never meets the line of `u` — at any
interior time the certificate forbids it, and at time zero the independence does. -/
theorem seg_avoids_line {start waypoint u : Fin 3 → ℝ}
    (hcross : crossProduct start u ≠ 0)
    (hcert : dotProduct waypoint (crossProduct start u) ≠ 0)
    (s ratio : ℝ) : seg start waypoint s ≠ ratio • u := by
  intro heq
  have hdotSeg : dotProduct (seg start waypoint s) (crossProduct start u)
      = s * dotProduct waypoint (crossProduct start u) := by
    rw [seg, add_dotProduct, smul_dotProduct, smul_dotProduct, dot_self_cross,
      smul_zero, zero_add, smul_eq_mul]
  have hdotLine : dotProduct (ratio • u) (crossProduct start u) = 0 := by
    rw [smul_dotProduct, dot_cross_self, smul_zero]
  rw [heq, hdotLine] at hdotSeg
  have hs : s = 0 := by
    rcases mul_eq_zero.mp hdotSeg.symm with hs | hzero
    · exact hs
    · exact absurd hzero hcert
  rw [hs, seg_zero] at heq
  apply hcross
  rw [heq, map_smul, LinearMap.smul_apply, cross_self, smul_zero]

/-! ## Single-coordinate moves -/

/-- Updating one coordinate to a mover that is off every other row's line preserves
goodness, provided the other rows span on their own. -/
theorem goodTuple_update {rows : Fin 6 → Fin 3 → ℝ} (hgood : GoodTuple rows)
    (movingIdx : Fin 6) {mover : Fin 3 → ℝ}
    (hmoverOff : ∀ j, j ≠ movingIdx → ∀ ratio : ℝ, mover ≠ ratio • rows j)
    (hothersSpan : ∀ probe : Fin 3 → ℝ,
      (∀ j, j ≠ movingIdx → dotProduct (rows j) probe = 0) → probe = 0) :
    GoodTuple (Function.update rows movingIdx mover) := by
  constructor
  · rintro ⟨keptLabel, dropLabel, ratio, hkd, heq⟩
    rcases eq_or_ne dropLabel movingIdx with rfl | hdrop
    · rw [Function.update_self, Function.update_of_ne hkd] at heq
      exact hmoverOff keptLabel hkd ratio heq
    · rcases eq_or_ne keptLabel movingIdx with rfl | hkept
      · rw [Function.update_of_ne hdrop, Function.update_self] at heq
        exact offLine_symm (row_ne_zero_of_goodTuple hgood dropLabel)
          (hmoverOff dropLabel hdrop) ratio heq
      · rw [Function.update_of_ne hdrop, Function.update_of_ne hkept] at heq
        exact noRatio_of_goodTuple hgood hkd ratio heq
  · intro probe hprobe
    refine hothersSpan probe fun j hj => ?_
    have := hprobe j
    rwa [Function.update_of_ne hj] at this

/-- One straight leg of a move, packaged as a `JoinedIn`. -/
theorem joinedIn_update_seg {X : Set (Fin 6 → Fin 3 → ℝ)} {rows : Fin 6 → Fin 3 → ℝ}
    (movingIdx : Fin 6) (target : Fin 3 → ℝ)
    (hmem : ∀ s : ℝ,
      Function.update rows movingIdx (seg (rows movingIdx) target s) ∈ X) :
    JoinedIn X rows (Function.update rows movingIdx target) := by
  refine ⟨⟨⟨fun t => Function.update rows movingIdx
      (seg (rows movingIdx) target (t : ℝ)), ?_⟩, ?_, ?_⟩, fun t => hmem _⟩
  · exact continuous_const.update movingIdx
      ((continuous_seg _ _).comp continuous_subtype_val)
  · show Function.update rows movingIdx
      (seg (rows movingIdx) target ((0 : unitInterval) : ℝ)) = rows
    rw [Set.Icc.coe_zero, seg_zero, Function.update_eq_self]
  · show Function.update rows movingIdx
      (seg (rows movingIdx) target ((1 : unitInterval) : ℝ))
        = Function.update rows movingIdx target
    rw [Set.Icc.coe_one, seg_one]

/-- **The single move.**  If the target is off every other row's line and the other
rows span on their own, the tuple joins its update inside the good tuples.  The path
runs through a waypoint on the moment curve chosen against at most ten quadratics. -/
theorem joinedIn_moveOne {rows : Fin 6 → Fin 3 → ℝ} (hgood : GoodTuple rows)
    (movingIdx : Fin 6) {target : Fin 3 → ℝ}
    (htargetOff : ∀ j, j ≠ movingIdx → ∀ ratio : ℝ, target ≠ ratio • rows j)
    (hothersSpan : ∀ probe : Fin 3 → ℝ,
      (∀ j, j ≠ movingIdx → dotProduct (rows j) probe = 0) → probe = 0) :
    JoinedIn goodTuples rows (Function.update rows movingIdx target) := by
  -- the two normal families and the finite bad set of waypoint parameters
  have hstartCross : ∀ j, j ≠ movingIdx →
      crossProduct (rows movingIdx) (rows j) ≠ 0 := fun j hj =>
    cross_rows_ne_zero_of_goodTuple hgood (Ne.symm hj)
  have htargetCross : ∀ j, j ≠ movingIdx →
      crossProduct target (rows j) ≠ 0 := fun j hj =>
    cross_ne_zero_of_offLine (row_ne_zero_of_goodTuple hgood j) (htargetOff j hj)
  have hbad : (⋃ j ∈ Finset.univ.erase movingIdx,
      (paramsAgainst (crossProduct (rows movingIdx) (rows j))
        ∪ paramsAgainst (crossProduct target (rows j)))).Finite := by
    refine Set.Finite.biUnion (Finset.univ.erase movingIdx).finite_toSet
      fun j hj => ?_
    have hjne : j ≠ movingIdx := Finset.ne_of_mem_erase hj
    exact (finite_paramsAgainst (hstartCross j hjne)).union
      (finite_paramsAgainst (htargetCross j hjne))
  obtain ⟨param, hparam⟩ := exists_param_avoiding hbad
  set waypoint := momentVec param with hwaypoint
  have hcertStart : ∀ j, j ≠ movingIdx →
      dotProduct waypoint (crossProduct (rows movingIdx) (rows j)) ≠ 0 := by
    intro j hj hzero
    exact hparam (Set.mem_biUnion (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      (Set.mem_union_left _ hzero))
  have hcertTarget : ∀ j, j ≠ movingIdx →
      dotProduct waypoint (crossProduct target (rows j)) ≠ 0 := by
    intro j hj hzero
    exact hparam (Set.mem_biUnion (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      (Set.mem_union_right _ hzero))
  -- leg one: from the current position to the waypoint
  have hlegOne : JoinedIn goodTuples rows
      (Function.update rows movingIdx waypoint) := by
    refine joinedIn_update_seg movingIdx waypoint fun s => ?_
    refine goodTuple_update hgood movingIdx (fun j hj ratio => ?_) hothersSpan
    exact seg_avoids_line (hstartCross j hj) (hcertStart j hj) s ratio
  -- leg two: from the target position back to the waypoint
  have hlegTwo : JoinedIn goodTuples (Function.update rows movingIdx target)
      (Function.update rows movingIdx waypoint) := by
    have hupdate : Function.update (Function.update rows movingIdx target)
        movingIdx waypoint = Function.update rows movingIdx waypoint :=
      Function.update_idem ..
    have hbase : (Function.update rows movingIdx target) movingIdx = target :=
      Function.update_self ..
    have := joinedIn_update_seg (X := goodTuples)
      (rows := Function.update rows movingIdx target) movingIdx waypoint ?_
    · rwa [hupdate] at this
    · intro s
      rw [Function.update_idem, hbase]
      refine goodTuple_update hgood movingIdx (fun j hj ratio => ?_) hothersSpan
      exact seg_avoids_line (htargetCross j hj) (hcertTarget j hj) s ratio
  exact hlegOne.trans hlegTwo.symm

/-! ## The mixed tuples along the walk to the hub -/

/-- The tuple obtained by moving the coordinates of `movedSet` onto the moment curve. -/
def mixedRows (rows : Fin 6 → Fin 3 → ℝ) (params : Fin 6 → ℝ)
    (movedSet : Finset (Fin 6)) : Fin 6 → Fin 3 → ℝ :=
  fun c => if c ∈ movedSet then momentVec (params c) else rows c

theorem mixedRows_empty (rows : Fin 6 → Fin 3 → ℝ) (params : Fin 6 → ℝ) :
    mixedRows rows params ∅ = rows := by
  funext c
  simp [mixedRows]

theorem mixedRows_of_mem {rows : Fin 6 → Fin 3 → ℝ} {params : Fin 6 → ℝ}
    {movedSet : Finset (Fin 6)} {c : Fin 6} (hc : c ∈ movedSet) :
    mixedRows rows params movedSet c = momentVec (params c) := by
  simp [mixedRows, hc]

theorem mixedRows_of_not_mem {rows : Fin 6 → Fin 3 → ℝ} {params : Fin 6 → ℝ}
    {movedSet : Finset (Fin 6)} {c : Fin 6} (hc : c ∉ movedSet) :
    mixedRows rows params movedSet c = rows c := by
  simp [mixedRows, hc]

theorem mixedRows_insert {rows : Fin 6 → Fin 3 → ℝ} {params : Fin 6 → ℝ}
    {movedSet : Finset (Fin 6)} {movingIdx : Fin 6} :
    mixedRows rows params (insert movingIdx movedSet)
      = Function.update (mixedRows rows params movedSet) movingIdx
          (momentVec (params movingIdx)) := by
  funext c
  rcases eq_or_ne c movingIdx with rfl | hc
  · rw [Function.update_self, mixedRows_of_mem (Finset.mem_insert_self c movedSet)]
  · rw [Function.update_of_ne hc]
    rcases Finset.decidableMem c movedSet with hmem | hmem
    · rw [mixedRows_of_not_mem hmem, mixedRows_of_not_mem]
      simp [Finset.mem_insert, hc, hmem]
    · rw [mixedRows_of_mem hmem, mixedRows_of_mem (Finset.mem_insert_of_mem hmem)]

/-- The standing genericity package for a walk: injective parameters whose moment
vectors are off every original row's line. -/
structure WalkData (rows : Fin 6 → Fin 3 → ℝ) (params : Fin 6 → ℝ) : Prop where
  isInjective : Function.Injective params
  isOffRows : ∀ c j (ratio : ℝ), momentVec (params c) ≠ ratio • rows j

/-- Every mixed row is off every other mixed row's line — pairwise goodness is uniform
in the moved set; only spanning needs the phase structure. -/
theorem mixedRows_noParallel {rows : Fin 6 → Fin 3 → ℝ} {params : Fin 6 → ℝ}
    (hgood : GoodTuple rows) (hwalk : WalkData rows params)
    (movedSet : Finset (Fin 6)) :
    ¬ HasParallelRows (mixedRows rows params movedSet) := by
  rintro ⟨keptLabel, dropLabel, ratio, hkd, heq⟩
  rcases Finset.decidableMem dropLabel movedSet with hdrop | hdrop <;>
    rcases Finset.decidableMem keptLabel movedSet with hkept | hkept
  · rw [mixedRows_of_not_mem hdrop, mixedRows_of_not_mem hkept] at heq
    exact noRatio_of_goodTuple hgood hkd ratio heq
  · rw [mixedRows_of_not_mem hdrop, mixedRows_of_mem hkept] at heq
    exact offLine_symm (row_ne_zero_of_goodTuple hgood dropLabel)
      (fun r => hwalk.isOffRows keptLabel dropLabel r) ratio heq
  · rw [mixedRows_of_mem hdrop, mixedRows_of_not_mem hkept] at heq
    exact hwalk.isOffRows dropLabel keptLabel ratio heq
  · rw [mixedRows_of_mem hdrop, mixedRows_of_mem hkept] at heq
    exact momentVec_offLine (fun h => hkd (hwalk.isInjective h)) ratio heq

/-- Three placed moment vectors span — the Vandermonde certificate. -/
theorem probe_eq_zero_of_three_moment {params : Fin 6 → ℝ}
    (hinj : Function.Injective params) {probe : Fin 3 → ℝ}
    {c1 c2 c3 : Fin 6} (h12 : c1 ≠ c2) (h13 : c1 ≠ c3) (h23 : c2 ≠ c3)
    (hd1 : dotProduct (momentVec (params c1)) probe = 0)
    (hd2 : dotProduct (momentVec (params c2)) probe = 0)
    (hd3 : dotProduct (momentVec (params c3)) probe = 0) : probe = 0 := by
  rw [momentVec_dot] at hd1 hd2 hd3
  exact coeffs_eq_zero_of_three_roots
    (fun h => h12 (hinj h)) (fun h => h13 (hinj h)) (fun h => h23 (hinj h))
    hd1 hd2 hd3

/-! ## The walk to the hub -/

/-- One step of the walk: move `movingIdx` onto the moment curve, given that the
remaining rows span. -/
theorem joinedIn_mixedStep {rows : Fin 6 → Fin 3 → ℝ} {params : Fin 6 → ℝ}
    (_hgood : GoodTuple rows) (hwalk : WalkData rows params)
    {movedSet : Finset (Fin 6)} {movingIdx : Fin 6} (_hnot : movingIdx ∉ movedSet)
    (hmixedGood : GoodTuple (mixedRows rows params movedSet))
    (hothersSpan : ∀ probe : Fin 3 → ℝ,
      (∀ j, j ≠ movingIdx → dotProduct (mixedRows rows params movedSet j) probe = 0)
        → probe = 0) :
    JoinedIn goodTuples (mixedRows rows params movedSet)
      (mixedRows rows params (insert movingIdx movedSet)) := by
  rw [mixedRows_insert]
  refine joinedIn_moveOne hmixedGood movingIdx (fun j hj ratio => ?_) hothersSpan
  rcases Finset.decidableMem j movedSet with hj' | hj'
  · rw [mixedRows_of_not_mem hj']
    exact hwalk.isOffRows movingIdx j ratio
  · rw [mixedRows_of_mem hj']
    exact momentVec_offLine
      (fun h => hj (hwalk.isInjective h)) ratio

/-- **The walk.**  Every good tuple reaches the moment-curve hub of any walk-generic
parameter system, inside the good tuples. -/
theorem joinedIn_momentHub {rows : Fin 6 → Fin 3 → ℝ} {params : Fin 6 → ℝ}
    (hgood : GoodTuple rows) (hwalk : WalkData rows params) :
    JoinedIn goodTuples rows (fun c => momentVec (params c)) := by
  classical
  -- the tripod: rows 0 and 1 plus a row off their plane
  obtain ⟨offIdx, hoffIdx⟩ :=
    exists_offPlane_row hgood (show (0 : Fin 6) ≠ 1 by decide)
  have hcross01 : crossProduct (rows 0) (rows 1) ≠ 0 :=
    cross_rows_ne_zero_of_goodTuple hgood (by decide)
  have hoff0 : offIdx ≠ 0 := by
    intro h
    rw [h, dot_self_cross] at hoffIdx
    exact hoffIdx rfl
  have hoff1 : offIdx ≠ 1 := by
    intro h
    rw [h, dot_cross_self] at hoffIdx
    exact hoffIdx rfl
  -- the tripod span certificate, resilient to any probe
  have htripodSpan : ∀ probe : Fin 3 → ℝ, dotProduct (rows 0) probe = 0 →
      dotProduct (rows 1) probe = 0 → dotProduct (rows offIdx) probe = 0 →
      probe = 0 := fun probe h0 h1 hoff =>
    probe_eq_zero_of_offPlane hcross01 hoffIdx h0 h1 hoff
  -- the three mover indices: the complement of the tripod
  have hcardTripod : ({0, 1, offIdx} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hoff0]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hoff1])]
    simp
  have hcardMovers : (Finset.univ \ ({0, 1, offIdx} : Finset (Fin 6))).card = 3 := by
    rw [Finset.card_sdiff, Finset.inter_univ, hcardTripod]
    simp
  obtain ⟨m1, m2, m3, hm12, hm13, hm23, hmovers⟩ :=
    Finset.card_eq_three.mp hcardMovers
  have hmoverFacts : ∀ m ∈ ({m1, m2, m3} : Finset (Fin 6)),
      m ≠ 0 ∧ m ≠ 1 ∧ m ≠ offIdx := by
    intro m hm
    have : m ∈ Finset.univ \ ({0, 1, offIdx} : Finset (Fin 6)) := by
      rw [hmovers]; exact hm
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at this
    push Not at this
    exact this.2
  have hm1f := hmoverFacts m1 (by simp)
  have hm2f := hmoverFacts m2 (by simp)
  have hm3f := hmoverFacts m3 (by simp)
  -- coverage: the six indices exhaust `Fin 6`
  have hcover : ∀ c : Fin 6, c = 0 ∨ c = 1 ∨ c = offIdx ∨
      c = m1 ∨ c = m2 ∨ c = m3 := by
    intro c
    by_cases hc : c ∈ ({0, 1, offIdx} : Finset (Fin 6))
    · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hc
      tauto
    · have : c ∈ Finset.univ \ ({0, 1, offIdx} : Finset (Fin 6)) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, hc⟩
      rw [hmovers, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at this
      tauto
  -- the six moved sets
  set S1 : Finset (Fin 6) := {m1} with hS1
  set S2 : Finset (Fin 6) := insert m2 S1 with hS2
  set S3 : Finset (Fin 6) := insert m3 S2 with hS3
  set S4 : Finset (Fin 6) := insert 0 S3 with hS4
  set S5 : Finset (Fin 6) := insert 1 S4 with hS5
  -- membership bookkeeping
  have hm1S1 : m1 ∈ S1 := by simp [hS1]
  have hm2S2 : m2 ∈ S2 := by simp [hS2]
  have hm3S3 : m3 ∈ S3 := by simp [hS3]
  have htripod0 : (0 : Fin 6) ∉ S3 := by
    simp only [hS3, hS2, hS1, Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨Ne.symm hm3f.1, Ne.symm hm2f.1, Ne.symm hm1f.1⟩
  have htripod1 : (1 : Fin 6) ∉ S4 := by
    simp only [hS4, hS3, hS2, hS1, Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨by decide, Ne.symm hm3f.2.1, Ne.symm hm2f.2.1, Ne.symm hm1f.2.1⟩
  have htripodOff : offIdx ∉ S5 := by
    simp only [hS5, hS4, hS3, hS2, hS1, Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨hoff1, hoff0, Ne.symm hm3f.2.2, Ne.symm hm2f.2.2, Ne.symm hm1f.2.2⟩
  -- spanning suppliers
  have hspanTripod : ∀ (S : Finset (Fin 6)), (0 : Fin 6) ∉ S → (1 : Fin 6) ∉ S →
      offIdx ∉ S → RowsSpan (mixedRows rows params S) := by
    intro S h0 h1 hoff probe hprobe
    refine htripodSpan probe ?_ ?_ ?_
    · have := hprobe 0; rwa [mixedRows_of_not_mem h0] at this
    · have := hprobe 1; rwa [mixedRows_of_not_mem h1] at this
    · have := hprobe offIdx; rwa [mixedRows_of_not_mem hoff] at this
  have hspanMoments : ∀ (S : Finset (Fin 6)), m1 ∈ S → m2 ∈ S → m3 ∈ S →
      RowsSpan (mixedRows rows params S) := by
    intro S h1 h2 h3 probe hprobe
    refine probe_eq_zero_of_three_moment hwalk.isInjective hm12 hm13 hm23 ?_ ?_ ?_
    · have := hprobe m1; rwa [mixedRows_of_mem h1] at this
    · have := hprobe m2; rwa [mixedRows_of_mem h2] at this
    · have := hprobe m3; rwa [mixedRows_of_mem h3] at this
  -- spanning-of-others suppliers, per moving index
  have hothersTripod : ∀ (S : Finset (Fin 6)) (movingIdx : Fin 6),
      (0 : Fin 6) ∉ S → (1 : Fin 6) ∉ S → offIdx ∉ S →
      movingIdx ≠ 0 → movingIdx ≠ 1 → movingIdx ≠ offIdx →
      ∀ probe : Fin 3 → ℝ,
        (∀ j, j ≠ movingIdx → dotProduct (mixedRows rows params S j) probe = 0)
          → probe = 0 := by
    intro S movingIdx h0 h1 hoff hne0 hne1 hneOff probe hprobe
    refine htripodSpan probe ?_ ?_ ?_
    · have := hprobe 0 (Ne.symm hne0); rwa [mixedRows_of_not_mem h0] at this
    · have := hprobe 1 (Ne.symm hne1); rwa [mixedRows_of_not_mem h1] at this
    · have := hprobe offIdx (Ne.symm hneOff)
      rwa [mixedRows_of_not_mem hoff] at this
  have hothersMoments : ∀ (S : Finset (Fin 6)) (movingIdx : Fin 6),
      m1 ∈ S → m2 ∈ S → m3 ∈ S →
      movingIdx ≠ m1 → movingIdx ≠ m2 → movingIdx ≠ m3 →
      ∀ probe : Fin 3 → ℝ,
        (∀ j, j ≠ movingIdx → dotProduct (mixedRows rows params S j) probe = 0)
          → probe = 0 := by
    intro S movingIdx h1 h2 h3 hne1 hne2 hne3 probe hprobe
    refine probe_eq_zero_of_three_moment hwalk.isInjective hm12 hm13 hm23 ?_ ?_ ?_
    · have := hprobe m1 (Ne.symm hne1); rwa [mixedRows_of_mem h1] at this
    · have := hprobe m2 (Ne.symm hne2); rwa [mixedRows_of_mem h2] at this
    · have := hprobe m3 (Ne.symm hne3); rwa [mixedRows_of_mem h3] at this
  -- goodness of the six way stations
  have hgoodMixed : ∀ (S : Finset (Fin 6)), RowsSpan (mixedRows rows params S) →
      GoodTuple (mixedRows rows params S) := fun S hspan =>
    ⟨mixedRows_noParallel hgood hwalk S, hspan⟩
  -- the empty station is the start
  have hstart : mixedRows rows params ∅ = rows := mixedRows_empty rows params
  -- tripod membership facts for the empty and early sets
  have h0S1 : (0 : Fin 6) ∉ S1 := by simp [hS1, Ne.symm hm1f.1]
  have h1S1 : (1 : Fin 6) ∉ S1 := by simp [hS1, Ne.symm hm1f.2.1]
  have hoffS1 : offIdx ∉ S1 := by simp [hS1, Ne.symm hm1f.2.2]
  have h0S2 : (0 : Fin 6) ∉ S2 := by
    simp only [hS2, Finset.mem_insert]
    push Not
    exact ⟨Ne.symm hm2f.1, h0S1⟩
  have h1S2 : (1 : Fin 6) ∉ S2 := by
    simp only [hS2, Finset.mem_insert]
    push Not
    exact ⟨Ne.symm hm2f.2.1, h1S1⟩
  have hoffS2 : offIdx ∉ S2 := by
    simp only [hS2, Finset.mem_insert]
    push Not
    exact ⟨Ne.symm hm2f.2.2, hoffS1⟩
  have h1S3 : (1 : Fin 6) ∉ S3 := by
    simp only [hS3, Finset.mem_insert]
    push Not
    exact ⟨Ne.symm hm3f.2.1, h1S2⟩
  have hoffS3 : offIdx ∉ S3 := by
    simp only [hS3, Finset.mem_insert]
    push Not
    exact ⟨Ne.symm hm3f.2.2, hoffS2⟩
  have hoffS4 : offIdx ∉ S4 := by
    simp only [hS4, Finset.mem_insert]
    push Not
    exact ⟨hoff0, hoffS3⟩
  -- moment membership persists up the chain
  have hm1S2 : m1 ∈ S2 := by simp [hS2, hm1S1]
  have hm1S3 : m1 ∈ S3 := by simp [hS3, hm1S2]
  have hm2S3 : m2 ∈ S3 := by simp [hS3, hm2S2]
  have hm1S4 : m1 ∈ S4 := by simp [hS4, hm1S3]
  have hm2S4 : m2 ∈ S4 := by simp [hS4, hm2S3]
  have hm3S4 : m3 ∈ S4 := by simp [hS4, hm3S3]
  have hm1S5 : m1 ∈ S5 := by simp [hS5, hm1S4]
  have hm2S5 : m2 ∈ S5 := by simp [hS5, hm2S4]
  have hm3S5 : m3 ∈ S5 := by simp [hS5, hm3S4]
  -- not-yet-moved facts for each step
  have hm1empty : m1 ∉ (∅ : Finset (Fin 6)) := Finset.notMem_empty m1
  have hm2S1 : m2 ∉ S1 := by simp [hS1, hm12.symm]
  have hm3S2 : m3 ∉ S2 := by
    simp only [hS2, hS1, Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨hm23.symm, hm13.symm⟩
  -- the six steps
  have hstep1 : JoinedIn goodTuples (mixedRows rows params ∅)
      (mixedRows rows params S1) := by
    have : S1 = insert m1 ∅ := by simp [hS1]
    rw [this]
    exact joinedIn_mixedStep hgood hwalk hm1empty
      (hgoodMixed ∅ (hspanTripod ∅ (by simp) (by simp) (by simp)))
      (hothersTripod ∅ m1 (by simp) (by simp) (by simp)
        hm1f.1 hm1f.2.1 hm1f.2.2)
  have hstep2 : JoinedIn goodTuples (mixedRows rows params S1)
      (mixedRows rows params S2) := by
    rw [hS2]
    exact joinedIn_mixedStep hgood hwalk hm2S1
      (hgoodMixed S1 (hspanTripod S1 h0S1 h1S1 hoffS1))
      (hothersTripod S1 m2 h0S1 h1S1 hoffS1 hm2f.1 hm2f.2.1 hm2f.2.2)
  have hstep3 : JoinedIn goodTuples (mixedRows rows params S2)
      (mixedRows rows params S3) := by
    rw [hS3]
    exact joinedIn_mixedStep hgood hwalk hm3S2
      (hgoodMixed S2 (hspanTripod S2 h0S2 h1S2 hoffS2))
      (hothersTripod S2 m3 h0S2 h1S2 hoffS2 hm3f.1 hm3f.2.1 hm3f.2.2)
  have hstep4 : JoinedIn goodTuples (mixedRows rows params S3)
      (mixedRows rows params S4) := by
    rw [hS4]
    exact joinedIn_mixedStep hgood hwalk htripod0
      (hgoodMixed S3 (hspanMoments S3 hm1S3 hm2S3 hm3S3))
      (hothersMoments S3 0 hm1S3 hm2S3 hm3S3
        (Ne.symm hm1f.1) (Ne.symm hm2f.1) (Ne.symm hm3f.1))
  have hstep5 : JoinedIn goodTuples (mixedRows rows params S4)
      (mixedRows rows params S5) := by
    rw [hS5]
    exact joinedIn_mixedStep hgood hwalk htripod1
      (hgoodMixed S4 (hspanMoments S4 hm1S4 hm2S4 hm3S4))
      (hothersMoments S4 1 hm1S4 hm2S4 hm3S4
        (Ne.symm hm1f.2.1) (Ne.symm hm2f.2.1) (Ne.symm hm3f.2.1))
  have hstep6 : JoinedIn goodTuples (mixedRows rows params S5)
      (mixedRows rows params (insert offIdx S5)) :=
    joinedIn_mixedStep hgood hwalk htripodOff
      (hgoodMixed S5 (hspanMoments S5 hm1S5 hm2S5 hm3S5))
      (hothersMoments S5 offIdx hm1S5 hm2S5 hm3S5
        (Ne.symm hm1f.2.2) (Ne.symm hm2f.2.2) (Ne.symm hm3f.2.2))
  -- the final station is the hub
  have hfinal : mixedRows rows params (insert offIdx S5)
      = fun c => momentVec (params c) := by
    funext c
    refine mixedRows_of_mem ?_
    rcases hcover c with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [hS5, hS4]
    · simp [hS5]
    · exact Finset.mem_insert_self c S5
    · simp only [Finset.mem_insert]
      exact Or.inr hm1S5
    · simp only [Finset.mem_insert]
      exact Or.inr hm2S5
    · simp only [Finset.mem_insert]
      exact Or.inr hm3S5
  rw [hstart] at hstep1
  rw [hfinal] at hstep6
  exact ((((hstep1.trans hstep2).trans hstep3).trans hstep4).trans hstep5).trans
    hstep6

/-! ## The main theorem -/

/-- **Path-connectedness of the good tuples.**  Any two pairwise-non-parallel spanning
six-tuples in `ℝ³` are joined inside the good tuples: both walk to a common
moment-curve hub whose parameters avoid the finitely many parallel-parameters of
either tuple. -/
theorem goodTuple_joinedIn {rowsA rowsB : Fin 6 → Fin 3 → ℝ}
    (hgoodA : GoodTuple rowsA) (hgoodB : GoodTuple rowsB) :
    JoinedIn goodTuples rowsA rowsB := by
  have hbad : (⋃ j : Fin 6,
      ({t : ℝ | ∃ ratio : ℝ, momentVec t = ratio • rowsA j}
        ∪ {t : ℝ | ∃ ratio : ℝ, momentVec t = ratio • rowsB j})).Finite :=
    Set.finite_iUnion fun j =>
      (finite_setOf_momentVec_parallel (rowsA j)).union
        (finite_setOf_momentVec_parallel (rowsB j))
  obtain ⟨params, hinj, havoid⟩ := exists_params_avoiding 6 hbad
  have hwalkA : WalkData rowsA params := by
    refine ⟨hinj, fun c j ratio heq => ?_⟩
    exact havoid c (Set.mem_iUnion.mpr ⟨j, Set.mem_union_left _ ⟨ratio, heq⟩⟩)
  have hwalkB : WalkData rowsB params := by
    refine ⟨hinj, fun c j ratio heq => ?_⟩
    exact havoid c (Set.mem_iUnion.mpr ⟨j, Set.mem_union_right _ ⟨ratio, heq⟩⟩)
  exact (joinedIn_momentHub hgoodA hwalkA).trans
    (joinedIn_momentHub hgoodB hwalkB).symm

/-- The globally-defined path version, ready for the whitening layer: a continuous
`ℝ`-parameterized family of good tuples with the prescribed endpoints. -/
theorem exists_goodTuple_path {rowsA rowsB : Fin 6 → Fin 3 → ℝ}
    (hgoodA : GoodTuple rowsA) (hgoodB : GoodTuple rowsB) :
    ∃ tuplePath : ℝ → Fin 6 → Fin 3 → ℝ,
      Continuous tuplePath ∧ tuplePath 0 = rowsA ∧ tuplePath 1 = rowsB ∧
        ∀ t : ℝ, GoodTuple (tuplePath t) := by
  obtain ⟨joinPath, hjoinMem⟩ := goodTuple_joinedIn hgoodA hgoodB
  refine ⟨joinPath.extend, joinPath.continuous_extend, joinPath.extend_zero,
    joinPath.extend_one, fun t => ?_⟩
  by_cases ht : t ≤ 0
  · rw [joinPath.extend_of_le_zero ht]
    exact hgoodA
  · by_cases ht' : 1 ≤ t
    · rw [joinPath.extend_of_one_le ht']
      exact hgoodB
    · have hmem : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_of_lt (not_le.mp ht), le_of_lt (not_le.mp ht')⟩
      have := joinPath.extend_extends' (⟨t, hmem⟩ : Set.Icc (0 : ℝ) 1)
      rw [this]
      exact hjoinMem _

/-! ## The design composition (step T3): from tuple paths to the reach hypothesis

A parallel-free design folds into a good tuple by `rows c = √(weight c) • atom c`;
the good-tuple path from the icosahedron's rows to the design's rows whitens (step
T2, the `WhiteningTransfer` interface below) back onto the Parseval shell; dividing
by an interpolated weight profile recovers a design witness at every time.  Only
the frame moves — the weights ride along freely, exactly as the shipped
`Gtz.reweight` splitting says they can. -/

/-- The Gram matrix of a bare tuple — `1` exactly on the Parseval shell. -/
def gramOf (rows : Fin 6 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ c, Gtz.atomMatrix (rows c)

/-- **The whitening interface (step T2).**  A continuous pointwise-spanning tuple
path with Parseval endpoints deforms onto the Parseval shell, endpoints fixed,
through a pointwise invertible linear mix — so the parallelism pattern survives. -/
def WhiteningTransfer : Prop :=
  ∀ tuplePath : ℝ → Fin 6 → Fin 3 → ℝ, Continuous tuplePath →
    (∀ t, (gramOf (tuplePath t)).PosDef) →
    gramOf (tuplePath 0) = 1 → gramOf (tuplePath 1) = 1 →
    ∃ whitePath : ℝ → Fin 6 → Fin 3 → ℝ,
      Continuous whitePath ∧ whitePath 0 = tuplePath 0 ∧ whitePath 1 = tuplePath 1 ∧
      (∀ t, gramOf (whitePath t) = 1) ∧
      (∀ t, ∃ mix : Matrix (Fin 3) (Fin 3) ℝ, mix.det ≠ 0 ∧
        ∀ c, whitePath t c = mix.mulVec (tuplePath t c))

/-- The Gram quadratic form is the sum of squared row dots. -/
theorem gramOf_form (rows : Fin 6 → Fin 3 → ℝ) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((gramOf rows).mulVec probe)
      = ∑ c, (rows c ⬝ᵥ probe) ^ 2 := by
  rw [gramOf, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Gtz.atomMatrix, Matrix.vecMulVec_mulVec, dotProduct_smul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, dotProduct_comm]
  ring

/-- A good tuple's Gram matrix is positive definite — no eigenvalues involved. -/
theorem posDef_gramOf_of_goodTuple {rows : Fin 6 → Fin 3 → ℝ}
    (hgood : GoodTuple rows) : (gramOf rows).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hne => ?_⟩
  · exact (Matrix.posSemidef_sum Finset.univ
      fun c _ => Gtz.posSemidef_atomMatrix (rows c)).1
  · rw [star_trivial, gramOf_form]
    have hnonneg : (0 : ℝ) ≤ ∑ c, (rows c ⬝ᵥ probe) ^ 2 :=
      Finset.sum_nonneg fun c _ => sq_nonneg _
    rcases hnonneg.lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      have hall : ∀ c ∈ Finset.univ, (rows c ⬝ᵥ probe) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun c _ => sq_nonneg _).mp hzero.symm
      have hdots : ∀ c, rows c ⬝ᵥ probe = 0 := fun c =>
        pow_eq_zero_iff two_ne_zero |>.mp (hall c (Finset.mem_univ c))
      exact hne (hgood.2 probe hdots)

/-- Rows of a parallel-free design form a good tuple. -/
theorem goodTuple_designRows (D : Gtz.WeightedDesign 6 3)
    (hfree : ¬ Gtz.HasParallelPair D) :
    GoodTuple (fun c => Real.sqrt (D.weight c) • D.atom c) := by
  constructor
  · rintro ⟨keptLabel, dropLabel, ratio, hkd, heq⟩
    have hkeptPos : (0 : ℝ) < Real.sqrt (D.weight keptLabel) :=
      Real.sqrt_pos.mpr (D.weight_pos keptLabel)
    have hdropPos : (0 : ℝ) < Real.sqrt (D.weight dropLabel) :=
      Real.sqrt_pos.mpr (D.weight_pos dropLabel)
    refine hfree ⟨keptLabel, dropLabel,
      ratio * Real.sqrt (D.weight keptLabel) / Real.sqrt (D.weight dropLabel),
      hkd, ?_⟩
    have := congrArg (fun v => (Real.sqrt (D.weight dropLabel))⁻¹ • v) heq
    simp only [smul_smul] at this
    rw [inv_mul_cancel₀ (ne_of_gt hdropPos), one_smul] at this
    rw [this]
    congr 1
    rw [div_eq_mul_inv]
    ring
  · intro probe hprobe
    have hatomDot : ∀ c, D.atom c ⬝ᵥ probe = 0 := by
      intro c
      have := hprobe c
      rw [smul_dotProduct, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_left
        (ne_of_gt (Real.sqrt_pos.mpr (D.weight_pos c)))
    by_contra hne
    have hpos := Gtz.selfDotProduct_pos hne
    have hform : probe ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ).mulVec probe)
        = ∑ c, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
      rw [← D.isParseval, Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        Gtz.atomMatrix, Matrix.vecMulVec_mulVec, dotProduct_smul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, dotProduct_comm]
      ring
    rw [Matrix.one_mulVec] at hform
    rw [hform] at hpos
    have : ∑ c, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 = 0 :=
      Finset.sum_eq_zero fun c _ => by rw [hatomDot c]; ring
    rw [this] at hpos
    exact lt_irrefl 0 hpos

/-- The rows of a design sit exactly on the Parseval shell. -/
theorem gramOf_designRows (D : Gtz.WeightedDesign 6 3) :
    gramOf (fun c => Real.sqrt (D.weight c) • D.atom c) = 1 := by
  rw [← D.isParseval, gramOf]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Gtz.atomMatrix_smul, Real.sq_sqrt (le_of_lt (D.weight_pos c))]

/-! ## The interpolated weight profile

The reach hypothesis asks for a globally continuous atom path but only for
design witnesses on `[0, 1]`, so the weights ride a clamped linear
interpolation: positive everywhere, summing to one everywhere, and exactly the
two designs' weights at the endpoints. -/

/-- Clamp to the unit interval. -/
def clampUnit (t : ℝ) : ℝ := max 0 (min 1 t)

theorem continuous_clampUnit : Continuous clampUnit :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clampUnit_zero : clampUnit 0 = 0 := by norm_num [clampUnit]

theorem clampUnit_one : clampUnit 1 = 1 := by norm_num [clampUnit]

theorem clampUnit_nonneg (t : ℝ) : 0 ≤ clampUnit t := le_max_left 0 _

theorem clampUnit_le_one (t : ℝ) : clampUnit t ≤ 1 :=
  max_le zero_le_one (min_le_left 1 t)

/-- The clamped linear interpolation between two weight profiles. -/
def weightPath (weightA weightB : Fin 6 → ℝ) (t : ℝ) (c : Fin 6) : ℝ :=
  (1 - clampUnit t) * weightA c + clampUnit t * weightB c

theorem weightPath_pos {weightA weightB : Fin 6 → ℝ}
    (hposA : ∀ c, 0 < weightA c) (hposB : ∀ c, 0 < weightB c) (t : ℝ)
    (c : Fin 6) : 0 < weightPath weightA weightB t c := by
  rcases lt_or_eq_of_le (clampUnit_le_one t) with hlt | heqOne
  · have hfirst : 0 < (1 - clampUnit t) * weightA c :=
      mul_pos (by linarith) (hposA c)
    have hsecond : 0 ≤ clampUnit t * weightB c :=
      mul_nonneg (clampUnit_nonneg t) (le_of_lt (hposB c))
    rw [weightPath]
    linarith
  · rw [weightPath, heqOne]
    simpa using hposB c

theorem weightPath_sum {weightA weightB : Fin 6 → ℝ}
    (hsumA : ∑ c, weightA c = 1) (hsumB : ∑ c, weightB c = 1) (t : ℝ) :
    ∑ c, weightPath weightA weightB t c = 1 := by
  simp only [weightPath]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsumA, hsumB]
  ring

theorem weightPath_zero (weightA weightB : Fin 6 → ℝ) (c : Fin 6) :
    weightPath weightA weightB 0 c = weightA c := by
  simp [weightPath, clampUnit_zero]

theorem weightPath_one (weightA weightB : Fin 6 → ℝ) (c : Fin 6) :
    weightPath weightA weightB 1 c = weightB c := by
  simp [weightPath, clampUnit_one]

theorem continuous_weightPath_apply (weightA weightB : Fin 6 → ℝ) (c : Fin 6) :
    Continuous fun t => weightPath weightA weightB t c :=
  (((continuous_const.sub continuous_clampUnit).mul continuous_const).add
    (continuous_clampUnit.mul continuous_const))

/-- Invertible matrices cancel on `mulVec` — the parallelism-transport engine. -/
theorem mulVec_cancel {mix : Matrix (Fin 3) (Fin 3) ℝ} (hdet : mix.det ≠ 0)
    {u v : Fin 3 → ℝ} (h : mix.mulVec u = mix.mulVec v) : u = v := by
  have hunit : IsUnit mix.det := isUnit_iff_ne_zero.mpr hdet
  have hleft := congrArg (fun x => mix⁻¹.mulVec x) h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul mix hunit,
    Matrix.one_mulVec] using hleft

/-! ## The capstone: the reach hypothesis modulo whitening -/

/-- **The reach hypothesis, modulo the whitening interface.**  Fold both designs
into their row tuples, walk the good-tuple path (T1, proved above), whiten back
onto the Parseval shell (T2, the interface), and divide by the interpolated
weight profile: every time slice is a parallel-free design, and the endpoints
are the two designs' atom systems on the nose. -/
theorem parallelFreeReachesAnchor_of_whiteningTransfer
    (hwhiten : WhiteningTransfer) :
    Gtz.ParallelFreeReachesAnchor 6 3 Gtz.icosaDesign := by
  intro D hD
  have hgoodA : GoodTuple
      (fun c => Real.sqrt (Gtz.icosaDesign.weight c) • Gtz.icosaDesign.atom c) :=
    goodTuple_designRows Gtz.icosaDesign Gtz.icosaDesign_hasNoParallelPair
  have hgoodB : GoodTuple (fun c => Real.sqrt (D.weight c) • D.atom c) :=
    goodTuple_designRows D hD
  obtain ⟨tuplePath, hcont, h0, h1, hgood⟩ := exists_goodTuple_path hgoodA hgoodB
  obtain ⟨whitePath, hwcont, hw0, hw1, hwgram, hwmix⟩ :=
    hwhiten tuplePath hcont (fun t => posDef_gramOf_of_goodTuple (hgood t))
      (by rw [h0]; exact gramOf_designRows Gtz.icosaDesign)
      (by rw [h1]; exact gramOf_designRows D)
  have hwPos : ∀ t c, 0 < weightPath Gtz.icosaDesign.weight D.weight t c :=
    fun t c => weightPath_pos Gtz.icosaDesign.weight_pos D.weight_pos t c
  have hsqrtPos : ∀ t c,
      0 < Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight t c) :=
    fun t c => Real.sqrt_pos.mpr (hwPos t c)
  refine ⟨fun t c =>
      (Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight t c))⁻¹
        • whitePath t c, ?_, ?_, ?_, ?_⟩
  · -- continuity, coordinate by coordinate
    refine continuous_pi fun c => ?_
    have hsq : Continuous fun t : ℝ =>
        Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight t c) :=
      Real.continuous_sqrt.comp
        (continuous_weightPath_apply Gtz.icosaDesign.weight D.weight c)
    have hinv := hsq.inv₀ fun t => ne_of_gt (hsqrtPos t c)
    have hrow : Continuous fun t : ℝ => whitePath t c :=
      (continuous_apply c).comp hwcont
    exact hinv.smul hrow
  · -- the icosahedral endpoint
    funext c
    show (Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight 0 c))⁻¹
        • whitePath 0 c = Gtz.icosaDesign.atom c
    have hval := congrFun (hw0.trans h0) c
    rw [hval, weightPath_zero, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (Gtz.icosaDesign.weight_pos c))),
      one_smul]
  · -- the design endpoint
    funext c
    show (Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight 1 c))⁻¹
        • whitePath 1 c = D.atom c
    have hval := congrFun (hw1.trans h1) c
    rw [hval, weightPath_one, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (D.weight_pos c))), one_smul]
  · -- a parallel-free design witness at every time
    intro t _ht
    refine ⟨⟨fun c =>
        (Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight t c))⁻¹
          • whitePath t c,
      weightPath Gtz.icosaDesign.weight D.weight t,
      fun c => hwPos t c,
      weightPath_sum Gtz.icosaDesign.weight_sum_one D.weight_sum_one t,
      ?_⟩, rfl, ?_⟩
    · -- Parseval: the weights cancel the inverse square roots exactly
      show ∑ c, weightPath Gtz.icosaDesign.weight D.weight t c •
          Gtz.atomMatrix
            ((Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight t c))⁻¹
              • whitePath t c) = 1
      have hterm : ∀ c, weightPath Gtz.icosaDesign.weight D.weight t c •
          Gtz.atomMatrix
            ((Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight t c))⁻¹
              • whitePath t c) = Gtz.atomMatrix (whitePath t c) := by
        intro c
        rw [Gtz.atomMatrix_smul, inv_pow,
          Real.sq_sqrt (le_of_lt (hwPos t c)), smul_smul,
          mul_inv_cancel₀ (ne_of_gt (hwPos t c)), one_smul]
      rw [Finset.sum_congr rfl fun c _ => hterm c]
      exact hwgram t
    · -- no parallel pair: transport back through the invertible mix
      rintro ⟨keptLabel, dropLabel, ratio, hkd, heq⟩
      have heq' : (Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight t
              dropLabel))⁻¹ • whitePath t dropLabel
          = ratio • (Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight t
              keptLabel))⁻¹ • whitePath t keptLabel := heq
      have hstep : whitePath t dropLabel
          = (Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight t dropLabel)
              * (ratio * (Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight t
                  keptLabel))⁻¹)) • whitePath t keptLabel := by
        have hmul := congrArg
          (fun v => Real.sqrt (weightPath Gtz.icosaDesign.weight D.weight t
            dropLabel) • v) heq'
        simp only [smul_smul] at hmul
        rwa [mul_inv_cancel₀ (ne_of_gt (hsqrtPos t dropLabel)), one_smul] at hmul
      obtain ⟨mix, hdet, hmix⟩ := hwmix t
      rw [hmix dropLabel, hmix keptLabel, ← Matrix.mulVec_smul] at hstep
      exact (hgood t).1 ⟨keptLabel, dropLabel, _, hkd, mulVec_cancel hdet hstep⟩



/-! ## The whitening layer (step T2) lives in `Gtz.Reduction.CholeskyWhitening`;
the staged verbatim copy was deleted at landing and the capstones below consume the
imported `exists_gramOne_path` directly. -/



/-! ## Discharging the whitening interface -/

/-- `gramOf` (over `Gtz.atomMatrix`) and `gramMatrix` (over `Matrix.vecMulVec`)
are definitionally equal, so the Cholesky theorem above IS the interface. -/
theorem whiteningTransfer_holds : WhiteningTransfer :=
  fun tuplePath hcont hpd hstart hend =>
    exists_gramOne_path tuplePath hcont hpd hstart hend

/-- **THE REACH HYPOTHESIS, UNCONDITIONALLY.**  The one open topological
hypothesis of the landed connectedness route
(`Gtz/Reduction/ConnectednessRoute.lean`) is now a theorem: every parallel-free
weighted `(6,3)` design is joined to the icosahedron by a continuous path of
parallel-free designs. -/
theorem parallelFreeReachesAnchor_six_three :
    Gtz.ParallelFreeReachesAnchor 6 3 Gtz.icosaDesign :=
  parallelFreeReachesAnchor_of_whiteningTransfer whiteningTransfer_holds

/-- The connectedness route now consumes ONE input: the hinge. -/
theorem gtzWeighted_six_three_of_hinge (hhinge : Gtz.HingeHoldsAtSize 6 3) :
    Gtz.GtzWeighted 6 3 :=
  Gtz.gtzWeighted_six_three_of_hinge_of_reach hhinge
    parallelFreeReachesAnchor_six_three

/-- And the hinge alone delivers all of rank three. -/
theorem gtzWeightedAll_three_of_hinge (hhinge : Gtz.HingeHoldsAtSize 6 3) :
    Gtz.GtzWeightedAll 3 :=
  Gtz.gtzWeightedAll_three_of_hinge_of_reach hhinge
    parallelFreeReachesAnchor_six_three


end Gtz
