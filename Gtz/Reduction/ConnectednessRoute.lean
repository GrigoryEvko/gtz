/-
# The connectedness route: `HingeHoldsAtSize 6 3` reaches the frontier

An HONEST INTERFACE.  The composition below is complete except for ONE named
hypothesis, `Gtz.ParallelFreeReachesAnchor`, which is purely topological and is
standard mathematics that this pin of Mathlib cannot express.  Everything else
`Gtz.gtzWeighted_six_three_of_hinge_of_reach` consumes is proved here or already
shipped.

## The composition

`Gtz.IsTie` is exactly "the domination objective vanishes": its first clause is
`objective ≥ 0` and its second is `objective ≤ 0`
(`Gtz.isTie_iff_dominating_and_not_strict`).  So on the parallel-free locus the
hinge says the objective NEVER VANISHES — not that it is positive.  What that
buys is recorded exactly in `Gtz.strict_or_not_dominating_of_not_isTie`: strict
domination, or nothing dominating at all.  The two alternatives are read off the
ATOMS alone, because `Gtz.subsetSum` never touches the weights; the strict side
is an OPEN set of atom families (`Gtz.isOpen_atomsStrict`) and the weak side is
CLOSED (`Gtz.isClosed_atomsWeak`).  Along a parallel-free path they are disjoint
and, by the hinge, they cover; `Set.Icc 0 1` is preconnected; so strict
domination propagates from one endpoint to the other
(`Gtz.atomsStrict_transfer`).  Anchoring at the icosahedron and discharging the
parallel branch gives the frontier.

The propagation uses NO eigenvalues, NO real-valued objective and NO continuity
of `λ_min`.  Both topological lemmas are absent from Mathlib at this pin, and
note that `{M | M.PosDef}` is NOT open in the ambient matrix space — `IsHermitian`
is a closed constraint — so the statements are made on the atom space, where the
gap is symmetric for free (`Gtz.isHermitian_gap`).

## THE NAMED HYPOTHESIS, and what it would cost

`Gtz.ParallelFreeReachesAnchor size rank anchor` says every parallel-free design
is joined to the anchor by a continuous path of atom families that stays inside
the design space and stays parallel-free.  Nothing about domination enters it.

It is standard mathematics.  Via `b_c = √(w_c) · a_c` the design space is
`V_rank(ℝ^size) × Δ°_{size-1}`, a connected manifold, and the parallel locus is
the closed real-algebraic set where some ordered pair of atoms has all its
`2 × 2` minors vanish — codimension `rank − 1`, hence codimension TWO at rank
three, with the zero-atom stratum at codimension three.  The complement of a
closed subset of codimension at least two in a connected manifold is connected.

It is NOT mechanized, and the obstruction is the library rather than the
mathematics.  At this pin Mathlib has no Stiefel manifold, no topological
Grassmannian, no semialgebraic dimension theory and no Sard theorem, and its two
codimension-`≥ 2`-complement results, `isConnected_compl_of_one_lt_codim` and
`isPathConnected_compl_of_one_lt_codim`, are stated for a LINEAR submodule and
so do not apply.  The cheapest viable shape is not the general theorem but an
explicit pencil of paths through `ContDiffOn.dense_compl_image_of_dimH_lt_finrank`,
which does exist and whose arithmetic fits: the bad-parameter set is the image of
a smooth map from a source of Hausdorff dimension at most 17 into `ℝ^18`.  Its
largest single unknown is the retraction `v ↦ S^(-1/2) v` back into the Stiefel
manifold, for which `Matrix.PosSemidef.sqrt` does not resolve at this pin.

`Gtz.reweight` reduces the burden by half: any design can be carried to any
positive weight vector summing to one by rescaling its atoms, preserving Parseval
and preserving every parallelism relation in BOTH directions
(`Gtz.hasParallelPair_of_reweight`, `Gtz.hasParallelPair_reweight_of`).  So the
simplex factor is contractible and contributes nothing; only the frame factor has
to be moved.

## Why this is NOT the phase-4 circularity, which stands

The phase-4 residual census found that the hinge's then-existing consumer — the
chart / leaf-one route — itself reads the frontier, so deriving it from the hinge
is circular.  That finding is correct and is not touched here.  This is a
DIFFERENT consumer: `Gtz.ParallelFreeReachesAnchor` mentions no domination
predicate at all — not `Gtz.Dominates`, not `Matrix.PosDef`, not
`Matrix.PosSemidef`, not `Gtz.subsetSum` — because it quantifies over PATHS
rather than over domination.  What changes is only that the hinge now has a
non-circular consumer; what does not change is that the hinge is still open.

## The hypothesis is neither vacuous nor a tautology

`Gtz/Reduction/ConnectednessRouteCalibration.lean` proves it FALSE at rank two,
at every size and for every parallel-free anchor, and pins the small-cell table:
at `(2,2)` the hinge holds, every design dominates strictly, `GtzWeighted 2 2` is
true, and the REACH is the premise that fails; at `(5,3)` the conclusion itself is
false and the HINGE is the premise that fails.  No small cell makes the route
prove anything false, and the hinge is carrying real weight rather than being
slack.

## Realness

Every input here is field-blind; realness is consumed ENTIRELY AND ONLY in the
hinge.  Over `ℂ` the trine is parallel-free (`Gtz.trineDesign_isPrimitive`) with
no dominating triple while the icosahedron is parallel-free and strictly
dominating, so this argument REFUTES the complex hinge — which is the precise
sense in which the route localises the realness consumption at one place.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.MarginTransfer
import Gtz.Quantitative.RealnessEngine
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.StressWalk
import Gtz.Reduction.WeightFloorWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The trichotomy: `IsTie` is exactly "the objective vanishes" -/

/-- Some `k`-subset dominates: the objective is at least zero. -/
def HasDominatingSubset (D : WeightedDesign m k) : Prop :=
  ∃ C : Finset (Fin m), C.card = k ∧ Dominates D C

/-- Some `k`-subset dominates STRICTLY: the objective is positive. -/
def HasStrictlyDominatingSubset (D : WeightedDesign m k) : Prop :=
  ∃ C : Finset (Fin m), C.card = k ∧ (subsetSum D C - 1).PosDef

theorem hasDominatingSubset_of_strict {D : WeightedDesign m k}
    (hstrict : HasStrictlyDominatingSubset D) : HasDominatingSubset D := by
  obtain ⟨C, hcard, hposDef⟩ := hstrict
  exact ⟨C, hcard, hposDef.posSemidef⟩

/-- **`IsTie` is exactly `objective = 0`.**  Its first clause is `objective ≥ 0`
and its second is `objective ≤ 0`. -/
theorem isTie_iff_dominating_and_not_strict {D : WeightedDesign m k} :
    IsTie D ↔ HasDominatingSubset D ∧ ¬ HasStrictlyDominatingSubset D := by
  constructor
  · rintro ⟨hweak, hnostrict⟩
    exact ⟨hweak, fun ⟨C, hcard, hposDef⟩ => hnostrict C hcard hposDef⟩
  · rintro ⟨hweak, hnostrict⟩
    exact ⟨hweak, fun C hcard hposDef => hnostrict ⟨C, hcard, hposDef⟩⟩

/-- **The trichotomy, exhaustive and exclusive.** -/
theorem trichotomy_of_design (D : WeightedDesign m k) :
    (HasStrictlyDominatingSubset D ∧ ¬ IsTie D ∧ HasDominatingSubset D) ∨
    (IsTie D ∧ ¬ HasStrictlyDominatingSubset D) ∨
    (¬ HasDominatingSubset D ∧ ¬ IsTie D ∧ ¬ HasStrictlyDominatingSubset D) := by
  by_cases hstrict : HasStrictlyDominatingSubset D
  · exact Or.inl ⟨hstrict,
      fun htie => (isTie_iff_dominating_and_not_strict.mp htie).2 hstrict,
      hasDominatingSubset_of_strict hstrict⟩
  · by_cases hweak : HasDominatingSubset D
    · exact Or.inr (Or.inl ⟨isTie_iff_dominating_and_not_strict.mpr ⟨hweak, hstrict⟩, hstrict⟩)
    · exact Or.inr (Or.inr ⟨hweak,
        fun htie => hweak (isTie_iff_dominating_and_not_strict.mp htie).1, hstrict⟩)

/-- **What `¬ IsTie` buys, exactly** -- not positivity, only NONVANISHING. -/
theorem strict_or_not_dominating_of_not_isTie {D : WeightedDesign m k}
    (hnotie : ¬ IsTie D) :
    HasStrictlyDominatingSubset D ∨ ¬ HasDominatingSubset D := by
  by_cases hstrict : HasStrictlyDominatingSubset D
  · exact Or.inl hstrict
  · exact Or.inr fun hweak =>
      hnotie (isTie_iff_dominating_and_not_strict.mpr ⟨hweak, hstrict⟩)

/-! ## 2. Domination reads the ATOMS alone

`subsetSum` never touches the weights, so both branches of the trichotomy live
on the finite-dimensional space `Fin m → Fin k → ℝ`. -/

/-- The weight-free atom sum of a bare atom family. -/
def atomFamilySum (atoms : Fin m → Fin k → ℝ) (C : Finset (Fin m)) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ c ∈ C, atomMatrix (atoms c)

theorem atomFamilySum_eq_subsetSum (D : WeightedDesign m k) (C : Finset (Fin m)) :
    atomFamilySum D.atom C = subsetSum D C := rfl

/-- Strict domination, read off the atoms. -/
def AtomsStrict (k : ℕ) (atoms : Fin m → Fin k → ℝ) : Prop :=
  ∃ C : Finset (Fin m), C.card = k ∧ (atomFamilySum atoms C - 1).PosDef

/-- Weak domination, read off the atoms. -/
def AtomsWeak (k : ℕ) (atoms : Fin m → Fin k → ℝ) : Prop :=
  ∃ C : Finset (Fin m), C.card = k ∧ (atomFamilySum atoms C - 1).PosSemidef

theorem atomsStrict_iff (D : WeightedDesign m k) :
    AtomsStrict k D.atom ↔ HasStrictlyDominatingSubset D := Iff.rfl

theorem atomsWeak_iff (D : WeightedDesign m k) :
    AtomsWeak k D.atom ↔ HasDominatingSubset D := Iff.rfl

theorem atomsWeak_of_atomsStrict {atoms : Fin m → Fin k → ℝ}
    (hstrict : AtomsStrict k atoms) : AtomsWeak k atoms := by
  obtain ⟨C, hcard, hposDef⟩ := hstrict
  exact ⟨C, hcard, hposDef.posSemidef⟩

/-! ### The gap form, and why the Hermitian clause is free -/

/-- The gap's quadratic form: `∑_{c ∈ C} ⟪a_c, x⟫² − ⟪x, x⟫`, the atom-family
twin of the shipped `Gtz.dominationGap_form`. -/
theorem gapForm_eq (atoms : Fin m → Fin k → ℝ) (C : Finset (Fin m))
    (vecArg : Fin k → ℝ) :
    vecArg ⬝ᵥ ((atomFamilySum atoms C - 1) *ᵥ vecArg)
      = (∑ c ∈ C, (atoms c ⬝ᵥ vecArg) ^ 2) - vecArg ⬝ᵥ vecArg := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomFamilySum,
    Matrix.sum_mulVec, dotProduct_sum]
  exact congrArg (· - vecArg ⬝ᵥ vecArg)
    (Finset.sum_congr rfl fun c _ => atom_form_eq_sq (atoms c) vecArg)

/-- The gap is symmetric for EVERY atom family -- no design hypothesis.  This is
why the openness statement below can be true at all. -/
theorem isHermitian_gap (atoms : Fin m → Fin k → ℝ) (C : Finset (Fin m)) :
    (atomFamilySum atoms C - 1).IsHermitian :=
  ((Matrix.posSemidef_sum C fun c _ => posSemidef_atomMatrix (atoms c)).1).sub
    Matrix.isHermitian_one

/-- The gap form is homogeneous of degree two. -/
theorem gapForm_smul (atoms : Fin m → Fin k → ℝ) (C : Finset (Fin m))
    (scale : ℝ) (vecArg : Fin k → ℝ) :
    (scale • vecArg) ⬝ᵥ ((atomFamilySum atoms C - 1) *ᵥ (scale • vecArg))
      = scale ^ 2 * (vecArg ⬝ᵥ ((atomFamilySum atoms C - 1) *ᵥ vecArg)) := by
  rw [gapForm_eq, gapForm_eq, mul_sub]
  have hsquares : ∑ c ∈ C, (atoms c ⬝ᵥ (scale • vecArg)) ^ 2
      = scale ^ 2 * ∑ c ∈ C, (atoms c ⬝ᵥ vecArg) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dotProduct_smul, smul_eq_mul]
    ring
  rw [hsquares, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
  ring

/-- A nonzero real vector has positive self-dot-product. -/
theorem selfDotProduct_pos {vecArg : Fin k → ℝ} (hne : vecArg ≠ 0) :
    0 < vecArg ⬝ᵥ vecArg := by
  obtain ⟨badCoord, hbad⟩ := Function.ne_iff.mp hne
  have hbadNe : vecArg badCoord ≠ 0 := by simpa using hbad
  exact Finset.sum_pos' (fun i _ => mul_self_nonneg (vecArg i))
    ⟨badCoord, Finset.mem_univ badCoord, mul_self_pos.mpr hbadNe⟩

/-! ## 3. The two topological facts, neither of which Mathlib has -/

/-- The probe directions of unit length -- the compact set every statement below
is quantified over. -/
def unitLevel (k : ℕ) : Set (Fin k → ℝ) := {vecArg | vecArg ⬝ᵥ vecArg = 1}

theorem continuous_selfDotProduct :
    Continuous fun vecArg : Fin k → ℝ => vecArg ⬝ᵥ vecArg := by
  simp only [dotProduct]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i)

theorem isCompact_unitLevel (k : ℕ) : IsCompact (unitLevel k) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_eq continuous_selfDotProduct continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := 1)).subset ?_
  intro vecArg hmem
  have hsum : vecArg ⬝ᵥ vecArg = 1 := hmem
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun coord => ?_
  have hle : vecArg coord * vecArg coord ≤ ∑ i, vecArg i * vecArg i :=
    Finset.single_le_sum (f := fun i => vecArg i * vecArg i)
      (fun i _ => mul_self_nonneg (vecArg i)) (Finset.mem_univ coord)
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  calc Real.sqrt (vecArg coord ^ 2) ≤ Real.sqrt 1 := by
        refine Real.sqrt_le_sqrt ?_
        rw [pow_two]
        exact hle.trans_eq hsum
    _ = 1 := Real.sqrt_one

/-- Scaling a nonzero vector by the inverse of its length lands on the unit
level set.  Stated over bare reals so that `field_simp` cannot loop on the
square root's own argument. -/
theorem inv_mul_inv_mul_self_eq_one (radius normSquared : ℝ) (hradius : radius ≠ 0)
    (hsquare : radius * radius = normSquared) :
    radius⁻¹ * radius⁻¹ * normSquared = 1 := by
  subst hsquare
  field_simp

/-- Positivity on the unit level set already gives positive definiteness: the
gap form is homogeneous, so every nonzero direction rescales onto the level set. -/
theorem posDef_gap_of_pos_on_unitLevel {atoms : Fin m → Fin k → ℝ} {C : Finset (Fin m)}
    (hpos : ∀ vecArg ∈ unitLevel k,
      0 < vecArg ⬝ᵥ ((atomFamilySum atoms C - 1) *ᵥ vecArg)) :
    (atomFamilySum atoms C - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_gap atoms C, fun vecArg hne => ?_⟩
  rw [star_trivial]
  have hnormPos : 0 < vecArg ⬝ᵥ vecArg := selfDotProduct_pos hne
  have hradiusPos : 0 < Real.sqrt (vecArg ⬝ᵥ vecArg) := Real.sqrt_pos.mpr hnormPos
  have hradiusSq : Real.sqrt (vecArg ⬝ᵥ vecArg) ^ 2 = vecArg ⬝ᵥ vecArg :=
    Real.sq_sqrt hnormPos.le
  have hmem : (Real.sqrt (vecArg ⬝ᵥ vecArg))⁻¹ • vecArg ∈ unitLevel k := by
    show ((Real.sqrt (vecArg ⬝ᵥ vecArg))⁻¹ • vecArg)
      ⬝ᵥ ((Real.sqrt (vecArg ⬝ᵥ vecArg))⁻¹ • vecArg) = 1
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    exact inv_mul_inv_mul_self_eq_one _ _ (ne_of_gt hradiusPos)
      (Real.mul_self_sqrt hnormPos.le)
  have happlied := hpos _ hmem
  rw [gapForm_smul atoms C _ vecArg] at happlied
  nlinarith [happlied, pow_pos hradiusPos 2, sq_nonneg (Real.sqrt (vecArg ⬝ᵥ vecArg))⁻¹]

/-- Positive definiteness gives positivity on the unit level set. -/
theorem pos_on_unitLevel_of_posDef {atoms : Fin m → Fin k → ℝ} {C : Finset (Fin m)}
    (hposDef : (atomFamilySum atoms C - 1).PosDef) :
    ∀ vecArg ∈ unitLevel k, 0 < vecArg ⬝ᵥ ((atomFamilySum atoms C - 1) *ᵥ vecArg) := by
  intro vecArg hmem
  have hone : vecArg ⬝ᵥ vecArg = 1 := hmem
  have hne : vecArg ≠ 0 := by
    intro hcontra
    rw [hcontra] at hone
    simp [dotProduct] at hone
  have := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hne
  rwa [star_trivial] at this

/-- The gap form is JOINTLY continuous in the atoms and the probe direction. -/
theorem continuous_gapForm_pair (C : Finset (Fin m)) :
    Continuous fun pair : (Fin m → Fin k → ℝ) × (Fin k → ℝ) =>
      pair.2 ⬝ᵥ ((atomFamilySum pair.1 C - 1) *ᵥ pair.2) := by
  simp only [gapForm_eq]
  refine Continuous.sub (continuous_finsetSum C fun c _ => ?_) ?_
  · refine Continuous.pow ?_ 2
    simp only [dotProduct]
    refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ ?_
    · exact Continuous.comp' (continuous_apply i) (Continuous.comp' (continuous_apply c)
        continuous_fst)
    · exact Continuous.comp' (continuous_apply i) continuous_snd
  · simp only [dotProduct]
    refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ ?_
    · exact Continuous.comp' (continuous_apply i) continuous_snd
    · exact Continuous.comp' (continuous_apply i) continuous_snd

/-- **`AtomsWeak` is CLOSED.**  Absent from Mathlib at this pin. -/
theorem isClosed_atomsWeak (m k : ℕ) :
    IsClosed {atoms : Fin m → Fin k → ℝ | AtomsWeak k atoms} := by
  have hrewrite : {atoms : Fin m → Fin k → ℝ | AtomsWeak k atoms}
      = ⋃ C ∈ {C : Finset (Fin m) | C.card = k},
          ⋂ vecArg : Fin k → ℝ,
            {atoms : Fin m → Fin k → ℝ |
              0 ≤ vecArg ⬝ᵥ ((atomFamilySum atoms C - 1) *ᵥ vecArg)} := by
    ext atoms
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, AtomsWeak, exists_prop]
    constructor
    · rintro ⟨C, hcard, hpsd⟩
      exact ⟨C, hcard, fun vecArg => by
        simpa using (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 vecArg⟩
    · rintro ⟨C, hcard, hall⟩
      exact ⟨C, hcard, Matrix.posSemidef_iff_dotProduct_mulVec.mpr
        ⟨isHermitian_gap atoms C, fun vecArg => by simpa using hall vecArg⟩⟩
  rw [hrewrite]
  refine Set.Finite.isClosed_biUnion (Set.toFinite _) fun C _ =>
    isClosed_iInter fun vecArg => isClosed_le continuous_const ?_
  have := continuous_gapForm_pair (m := m) (k := k) C
  exact this.comp (Continuous.prodMk continuous_id continuous_const)

/-- **`AtomsStrict` is OPEN.**  Absent from Mathlib at this pin, and note that
`{M | M.PosDef}` is NOT open in the ambient matrix space -- `IsHermitian` is a
closed constraint.  On the atom space the Hermitian clause is free. -/
theorem isOpen_atomsStrict (m k : ℕ) :
    IsOpen {atoms : Fin m → Fin k → ℝ | AtomsStrict k atoms} := by
  rw [isOpen_iff_mem_nhds]
  rintro atoms ⟨C, hcard, hposDef⟩
  have htube : ∀ᶠ other in nhds atoms, ∀ vecArg ∈ unitLevel k,
      0 < vecArg ⬝ᵥ ((atomFamilySum other C - 1) *ᵥ vecArg) := by
    refine (isCompact_unitLevel k).eventually_forall_of_forall_eventually ?_
    intro vecArg hmem
    have hopen : IsOpen {pair : (Fin m → Fin k → ℝ) × (Fin k → ℝ) |
        0 < pair.2 ⬝ᵥ ((atomFamilySum pair.1 C - 1) *ᵥ pair.2)} :=
      isOpen_lt continuous_const (continuous_gapForm_pair C)
    exact hopen.mem_nhds (pos_on_unitLevel_of_posDef hposDef vecArg hmem)
  filter_upwards [htube] with other hother
  exact ⟨C, hcard, posDef_gap_of_pos_on_unitLevel hother⟩

/-! ## 4. The propagation -- no eigenvalues, no objective function -/

/-- **THE MECHANISM.**  Along a continuous family of atom systems on which the
two branches of the trichotomy COVER (which is what the hinge supplies on the
parallel-free locus), strict domination propagates from one endpoint to the
other.  `Set.Icc 0 1` is preconnected; `AtomsStrict` is open, `AtomsWeak` is
closed, and the two branches are disjoint. -/
theorem atomsStrict_transfer {pathAtoms : ℝ → (Fin m → Fin k → ℝ)}
    (hcont : Continuous pathAtoms)
    (hcover : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AtomsStrict k (pathAtoms t) ∨ ¬ AtomsWeak k (pathAtoms t))
    (hstart : AtomsStrict k (pathAtoms 0)) :
    AtomsStrict k (pathAtoms 1) := by
  set strictSide : Set ℝ := pathAtoms ⁻¹' {atoms | AtomsStrict k atoms} with hstrictSide
  set failSide : Set ℝ := pathAtoms ⁻¹' {atoms | AtomsWeak k atoms}ᶜ with hfailSide
  have hstrictOpen : IsOpen strictSide := (isOpen_atomsStrict m k).preimage hcont
  have hfailOpen : IsOpen failSide := ((isClosed_atomsWeak m k).isOpen_compl).preimage hcont
  have hdisjoint : Disjoint strictSide failSide := by
    rw [Set.disjoint_left]
    intro t hstrictMem hfailMem
    exact hfailMem (atomsWeak_of_atomsStrict hstrictMem)
  have hunion : Set.Icc (0 : ℝ) 1 ⊆ strictSide ∪ failSide := by
    intro t hmem
    rcases hcover t hmem with hstrictHere | hfailHere
    · exact Or.inl hstrictHere
    · exact Or.inr hfailHere
  rcases (isPreconnected_Icc (a := (0 : ℝ)) (b := 1)).subset_or_subset
      hstrictOpen hfailOpen hdisjoint hunion with hall | hall
  · exact hall (Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩)
  · exact absurd (hall (Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩))
      (Set.disjoint_left.mp hdisjoint hstart)

/-- The transfer mechanism is NOT vacuous: the constant path satisfies every
hypothesis and returns the start. -/
theorem atomsStrict_transfer_const {atoms : Fin m → Fin k → ℝ}
    (hstart : AtomsStrict k atoms) : AtomsStrict k atoms :=
  atomsStrict_transfer (pathAtoms := fun _ => atoms) continuous_const
    (fun _ _ => Or.inl hstart) hstart

/-! ## 5. THE ONE OPEN HYPOTHESIS -- and it is purely topological

The parallel-free locus of the design space is path-connected to a chosen
anchor.  Nothing about domination enters; this is a statement about the
manifold `V_rank(ℝ^size) × Δ°_{size-1}` minus a real-algebraic set of
codimension `rank - 1`.  Measured at rank three: codimension EXACTLY two on
every stratum, with the zero-atom stratum at codimension three. -/

/-- **THE TOPOLOGICAL INPUT.**  Every parallel-free design is joined to the
anchor by a continuous path of atom systems that stays inside the design space
and stays parallel-free. -/
def ParallelFreeReachesAnchor (size rank : ℕ) (anchor : WeightedDesign size rank) : Prop :=
  ∀ D : WeightedDesign size rank, ¬ HasParallelPair D →
    ∃ pathAtoms : ℝ → (Fin size → Fin rank → ℝ),
      Continuous pathAtoms ∧ pathAtoms 0 = anchor.atom ∧ pathAtoms 1 = D.atom ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ E : WeightedDesign size rank,
        E.atom = pathAtoms t ∧ ¬ HasParallelPair E

/-- The hypothesis is satisfied at the anchor itself by the constant path, so it
is not empty-by-construction. -/
theorem parallelFreeReachesAnchor_at_anchor {size rank : ℕ}
    (anchor : WeightedDesign size rank) (hanchorFree : ¬ HasParallelPair anchor) :
    ∃ pathAtoms : ℝ → (Fin size → Fin rank → ℝ),
      Continuous pathAtoms ∧ pathAtoms 0 = anchor.atom ∧ pathAtoms 1 = anchor.atom ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ E : WeightedDesign size rank,
        E.atom = pathAtoms t ∧ ¬ HasParallelPair E :=
  ⟨fun _ => anchor.atom, continuous_const, rfl, rfl,
    fun _ _ => ⟨anchor, rfl, hanchorFree⟩⟩

/-! ## 6. The assembly, at general size and rank -/

/-- **The route, rank-general.**  Hinge + reach + a strictly dominating anchor
give strict domination at every parallel-free design. -/
theorem strictlyDominating_of_hinge_of_reach {size rank : ℕ}
    {anchor : WeightedDesign size rank}
    (hhinge : HingeHoldsAtSize size rank)
    (hreach : ParallelFreeReachesAnchor size rank anchor)
    (hanchorStrict : HasStrictlyDominatingSubset anchor)
    (D : WeightedDesign size rank) (hparallelFree : ¬ HasParallelPair D) :
    HasStrictlyDominatingSubset D := by
  obtain ⟨pathAtoms, hcont, hstart, hend, hstays⟩ := hreach D hparallelFree
  have hcover : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AtomsStrict rank (pathAtoms t) ∨ ¬ AtomsWeak rank (pathAtoms t) := by
    intro t hmem
    obtain ⟨E, hatoms, hEfree⟩ := hstays t hmem
    have hnotie : ¬ IsTie E := fun htie => hEfree (hhinge E htie)
    rcases strict_or_not_dominating_of_not_isTie hnotie with hstrictHere | hfailHere
    · exact Or.inl (by rw [← hatoms]; exact (atomsStrict_iff E).mpr hstrictHere)
    · exact Or.inr (by rw [← hatoms]; exact fun hcontra => hfailHere ((atomsWeak_iff E).mp hcontra))
  have hstartStrict : AtomsStrict rank (pathAtoms 0) := by
    rw [hstart]; exact (atomsStrict_iff anchor).mpr hanchorStrict
  have hendStrict : AtomsStrict rank (pathAtoms 1) :=
    atomsStrict_transfer hcont hcover hstartStrict
  rw [hend] at hendStrict
  exact (atomsStrict_iff D).mp hendStrict

/-- **The route, rank-general, with the parallel branch supplied.** -/
theorem gtzWeighted_of_hinge_of_reach {size rank : ℕ}
    {anchor : WeightedDesign size rank}
    (hhinge : HingeHoldsAtSize size rank)
    (hreach : ParallelFreeReachesAnchor size rank anchor)
    (hanchorStrict : HasStrictlyDominatingSubset anchor)
    (hparallelBranch : ∀ D : WeightedDesign size rank, HasParallelPair D →
      ∃ C : Finset (Fin size), C.card = rank ∧ Dominates D C) :
    GtzWeighted size rank := by
  intro D
  by_cases hparallel : HasParallelPair D
  · exact hparallelBranch D hparallel
  · exact hasDominatingSubset_of_strict
      (strictlyDominating_of_hinge_of_reach hhinge hreach hanchorStrict D hparallel)

/-! ## 7. The `(6,3)` capstone

Both remaining inputs are SHIPPED kernel theorems:
`Gtz.icosaDesign_strictly_dominates` is the anchor, and
`Gtz.exists_dominating_triple_of_hasParallelPair_sixThree` is the parallel
branch, unconditional at `(6,3)`. -/

theorem icosaDesign_hasStrictlyDominatingSubset :
    HasStrictlyDominatingSubset icosaDesign :=
  ⟨{0, 2, 4}, by decide, icosaDesign_strictly_dominates⟩

/-- **THE CAPSTONE.**  `HingeHoldsAtSize 6 3` plus path-connectedness of the
parallel-free locus to the icosahedron gives the frontier. -/
theorem gtzWeighted_six_three_of_hinge_of_reach
    (hhinge : HingeHoldsAtSize 6 3)
    (hreach : ParallelFreeReachesAnchor 6 3 icosaDesign) :
    GtzWeighted 6 3 :=
  gtzWeighted_of_hinge_of_reach hhinge hreach icosaDesign_hasStrictlyDominatingSubset
    exists_dominating_triple_of_hasParallelPair_sixThree

/-- And the frontier delivers all of rank three. -/
theorem gtzWeightedAll_three_of_hinge_of_reach
    (hhinge : HingeHoldsAtSize 6 3)
    (hreach : ParallelFreeReachesAnchor 6 3 icosaDesign) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three (gtzWeighted_six_three_of_hinge_of_reach hhinge hreach)

/-! ## 8. Non-vacuity, and a reduction of the open hypothesis -/

/-- The open set is NONEMPTY. -/
theorem atomsStrict_icosaDesign : AtomsStrict 3 icosaDesign.atom :=
  icosaDesign_hasStrictlyDominatingSubset

/-- The open set is NOT everything: an all-zero atom family has gap `-1`. -/
theorem not_atomsStrict_zero (m : ℕ) :
    ¬ AtomsStrict 3 (fun _ : Fin m => (0 : Fin 3 → ℝ)) := by
  rintro ⟨C, _, hposDef⟩
  have hprobe : (fun _ : Fin 3 => (1 : ℝ)) ≠ 0 := by
    intro hcontra
    have := congrFun hcontra 0
    norm_num at this
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
  rw [star_trivial, gapForm_eq] at hpos
  simp only [dotProduct, Fin.sum_univ_three] at hpos
  norm_num at hpos

/-- **Reweighting is FREE.**  Any design can be carried to any positive weight
vector summing to one by rescaling its atoms; Parseval survives because the
rescaling is exactly compensating.  Every parallelism relation survives too,
since the rescaling factors are positive.  CONSEQUENCE: the open hypothesis
below concerns only the FRAME factor of the design space -- the simplex factor
is contractible and contributes nothing. -/
noncomputable def reweight (D : WeightedDesign m k) (newWeight : Fin m → ℝ)
    (hpos : ∀ c, 0 < newWeight c) (hsum : ∑ c, newWeight c = 1) :
    WeightedDesign m k where
  atom := fun c => Real.sqrt (D.weight c / newWeight c) • D.atom c
  weight := newWeight
  weight_pos := hpos
  weight_sum_one := hsum
  isParseval := by
    rw [← D.isParseval]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [atomMatrix_smul, smul_smul,
      Real.sq_sqrt (le_of_lt (div_pos (D.weight_pos c) (hpos c)))]
    congr 1
    rw [mul_comm]
    exact div_mul_cancel₀ (D.weight c) (ne_of_gt (hpos c))

@[simp] theorem reweight_atom (D : WeightedDesign m k) (newWeight : Fin m → ℝ)
    (hpos : ∀ c, 0 < newWeight c) (hsum : ∑ c, newWeight c = 1) (c : Fin m) :
    (reweight D newWeight hpos hsum).atom c
      = Real.sqrt (D.weight c / newWeight c) • D.atom c := rfl

/-- Reweighting never creates a parallel pair. -/
theorem hasParallelPair_of_reweight {D : WeightedDesign m k} {newWeight : Fin m → ℝ}
    {hpos : ∀ c, 0 < newWeight c} {hsum : ∑ c, newWeight c = 1}
    (hparallel : HasParallelPair (reweight D newWeight hpos hsum)) :
    HasParallelPair D := by
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, heq⟩ := hparallel
  rw [reweight_atom, reweight_atom] at heq
  have hkeptPos : 0 < Real.sqrt (D.weight keptLabel / newWeight keptLabel) :=
    Real.sqrt_pos.mpr (div_pos (D.weight_pos keptLabel) (hpos keptLabel))
  have hdropPos : 0 < Real.sqrt (D.weight dropLabel / newWeight dropLabel) :=
    Real.sqrt_pos.mpr (div_pos (D.weight_pos dropLabel) (hpos dropLabel))
  refine ⟨keptLabel, dropLabel,
    ratio * Real.sqrt (D.weight keptLabel / newWeight keptLabel)
      / Real.sqrt (D.weight dropLabel / newWeight dropLabel), hdistinct, ?_⟩
  rw [div_eq_inv_mul, ← smul_smul, ← smul_smul, ← heq, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hdropPos), one_smul]

/-- Reweighting never destroys one either, so the frame is the only factor that
the topological hypothesis has to move. -/
theorem hasParallelPair_reweight_of {D : WeightedDesign m k} {newWeight : Fin m → ℝ}
    {hpos : ∀ c, 0 < newWeight c} {hsum : ∑ c, newWeight c = 1}
    (hparallel : HasParallelPair D) :
    HasParallelPair (reweight D newWeight hpos hsum) := by
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, heq⟩ := hparallel
  have hkeptPos : 0 < Real.sqrt (D.weight keptLabel / newWeight keptLabel) :=
    Real.sqrt_pos.mpr (div_pos (D.weight_pos keptLabel) (hpos keptLabel))
  refine ⟨keptLabel, dropLabel,
    ratio * Real.sqrt (D.weight dropLabel / newWeight dropLabel)
      / Real.sqrt (D.weight keptLabel / newWeight keptLabel), hdistinct, ?_⟩
  rw [reweight_atom, reweight_atom, heq]
  simp only [smul_smul]
  congr 1
  field_simp

end Gtz
