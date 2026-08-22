/-
# The two rank-four registry hinges, restated on the DEPENDENCY SPACE

`Skeleton.obligationSubThresholdBandHinge` and
`Skeleton.obligationThresholdCellHingeRankFourAndUp` are the two registry axioms
that live at rank four and up.  Both say the same thing at their own cells: an
exact tie carries a parallel pair.  This module removes the atoms from both.

`Gtz/Wave/ChartQuadraticCore.lean` already removes the vectors once, into a
symmetric matrix `M = P - diag t` and one quadratic equation.  This module
removes them a second time, into the LINEAR DEPENDENCIES of the atoms, where the
hinge becomes a statement about a subspace of `ℝ^size` and a positive weight
vector, and nothing else.

## The three new readings

**1.  A parallel pair is a SPARSE DEPENDENCY.**

    `Gtz.hasParallelPair_iff_hasSparseDependency` :
      `HasParallelPair D  ↔  some nonzero dependency lives on two labels.`

That is the chart form of the hinge's CONCLUSION, and it is the form a
successor needs: the determinant reading
`Gtz.ChartCore.HasParallelPairCore` names one `2 x 2` minor at a time, while
this names the object — the dependency space meets a coordinate `2`-plane.

**2.  THE STRICT DEPENDENCY CRITERION IS IMPORTED, NOT RE-DERIVED.**
`Gtz.posDef_gap_iff_dependencyBound_compl` of `Gtz/Wave/CircuitSwapLaw.lean` says

    `(S_C - 1).PosDef  ↔  for every NONZERO dependency z ,
       Σ_{c ∈ C} z_c² / (1 - t_c)  <  Σ_{c ∉ C} z_c² / t_c` ,

the strict twin of the weak criterion of
`Gtz/Wave/DependencyDominationCriterion.lean`, whose header carries the strict
form as MEASURED only.  This lane derived the same four theorems independently
and deleted them on the collision scan.  Everything below consumes the landed
versions.

**3.  THE PAIR-MASS READING.**  Moving the complementary part of the right sum
across turns `1/t_c` into the campaign's universal pair mass:

    `Gtz.dominates_iff_dependencyBound_pairMass` :
      `Dominates D C  ↔  for every dependency z ,
         Σ_c z_c² / (1 - t_c)  ≤  Σ_{c ∉ C} z_c² / (t_c (1 - t_c))` .

The left side no longer mentions `C` at all.  So a `rank`-subset is decided by
ONE fixed positive form on the dependency space, tested against the sum of the
rank-one forms of the CORANK labels it omits.  At corank one that sum is a single
rank-one form and the criterion collapses to the landed
`Gtz.dominates_erase_of_coMean_le`; at corank two it is a sum of two.

**4.  THE COMPLEMENTARY BUDGET AT THE SELF-DUAL CELL.**  The defect of a
selection and the defect of its COMPLEMENT total one fixed reading of the
dependency that mentions no selection:

    `Gtz.dependencyDefect_add_compl` :
      `defect(C, z) + defect(Cᶜ, z)  =  Σ_c z_c² (1 - 2 t_c) / (t_c (1 - t_c))` .

At `size = 2 * rank` the complement of a `rank`-subset is a `rank`-subset, so the
`C(2 rank, rank)` tests pair up and carry only half as many budgets.  At `(8,4)`,
the first band cell and the band's LOWER ENDPOINT, seventy tests carry thirty-five
budgets.  Two consequences follow with no further work:
`Gtz.dependencyDefect_pos_of_compl_neg` — with no weight past one half two
complementary selections cannot fail at the same dependency — and
`Gtz.not_dominates_and_compl_of_budget_neg`, its weight-aware converse.

## What the tie and the hinge become

`Gtz.isTie_iff_dependency` and `Gtz.hingeHoldsAtSize_iff_dependency` package the
three readings.  At `(8,4)` the right side of the hinge mentions a
four-dimensional subspace of `ℝ^8`, eight positive weights, and the seventy
`4`-subsets — no atom, no Parseval, no projection and no matrix inverse.

## The registry statements at rank four

`Gtz.SubThresholdBandHingeStatement` and
`Gtz.ThresholdCellHingeRankFourAndUpStatement` carry the exact types of the two
registry axioms.  `Gtz.bandCell_rank_four` says the band at rank four is the two
sizes eight and nine and nothing else, and `Gtz.thresholdCell_rank_four` says the
threshold cell is size ten.  Each of the three cells is then restated twice,
once in the chart of `Gtz.ChartCore` and once on the dependency space.

## What is NOT claimed

Nothing here proves either axiom.  Both stay open, and the readings are
EQUIVALENCES: `Gtz.exists_design_of_chartCore` supplies the backward arrow for
the chart, and the criteria above are iffs, so no reading quantifies over a
superset of the designs.

The dependency reading is field-blind in one direction only.  Every step below
is real: `Gtz.posDef_diagonal_sub_block_iff_kernelBound` divides by
`Real.sqrt (scale slot)` and reads `probe index ^ 2`.  Over `ℂ` the same three
lines run with `Complex.normSq`, so the criteria themselves would survive
complexification and the campaign's realness obstruction does NOT enter here.
It enters at the hinge, which is FALSE over `ℂ`
(`Gtz/Complex/ComplexHingeRefutation.lean`), so no successor should expect the
dependency reading alone to close either axiom.

[MEASURED before proving, in double precision over the cells `(5,3)`, `(6,3)`,
`(7,3)`, `(5,4)`, `(6,4)`, `(7,4)`, `(8,4)`, `(9,4)`, `(6,2)` and `(7,5)`: the
weak dependency criterion, the STRICT dependency criterion, the pair-mass
reading, and the co-frame reading agreed with domination and with strict
domination on all 14080 subsets tested, with no mismatch of any kind.  The
complementary budget was measured at `(8,4)` over 60 designs and all seventy
subsets, residual `8.9e-15`, and the weight-average identity at `4.5e-16`.]
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.ProjectionForm
import Gtz.LinAlg.SchurRankOne
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Wave.TieParallelPairWeightRegular
import Gtz.Wave.DependencyDominationCriterion
import Gtz.Wave.CircuitSwapLaw
import Gtz.Wave.ChartQuadraticCore
import Gtz.Wave.BandTieTower

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The engine, and where it lives

The strict block-versus-kernel criterion and its three design-level readings
`Gtz.posDef_diagonal_sub_block_iff_kernelBound`, `Gtz.posDef_gap_iff_kernelBound`,
`Gtz.posDef_gap_iff_dependencyBound` and `Gtz.posDef_gap_iff_dependencyBound_compl`
are landed in `Gtz/Wave/CircuitSwapLaw.lean` and are imported, not re-derived.
They are the strict twins of the weak chain of
`Gtz/Wave/DependencyDominationCriterion.lean`, whose header records the strict
form as measured only.

What follows is new: the pair-mass reading, the subset-indexed dictionary, the
sparse-dependency reading of a parallel pair, the tie and the hinge in dependency
currency, the corank-two specialisation, and the two rank-four registry
statements. -/

/-! ## 2. The pair-mass reading

Moving the COMPLEMENT'S part of the right sum across as well turns `1/t_c` into
`1/(t_c(1 - t_c))` and leaves a left side that does not mention the selection.
So a `rank`-subset is decided by one fixed positive form on the dependency space,
tested against the rank-one forms of the corank labels it omits. -/

/-- **THE PAIR-MASS READING.**  `Dominates D C` exactly when the fixed form
`Σ_c z_c²/(1 - t_c)` on the dependency space is dominated by the sum of the
rank-one forms `z_c²/(t_c(1 - t_c))` over the labels OUTSIDE `C`. -/
theorem dominates_iff_dependencyBound_pairMass (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    Dominates D (Finset.image pick Finset.univ)
      ↔ ∀ dep : Fin m → ℝ, (∑ index, dep index • D.atom index) = 0 →
          ∑ index, dep index ^ 2 / (1 - D.weight index)
            ≤ ∑ index ∈ (Finset.image pick Finset.univ)ᶜ,
                dep index ^ 2 / (D.weight index * (1 - D.weight index)) := by
  classical
  rw [dominates_iff_dependencyBound_compl D hm pick hinj]
  refine forall_congr' fun dep => forall_congr' fun _ => ?_
  set selection : Finset (Fin m) := Finset.image pick Finset.univ with hselection
  have hmassSplit : ∑ index, dep index ^ 2 / (1 - D.weight index)
      = (∑ index ∈ selection, dep index ^ 2 / (1 - D.weight index))
        + ∑ index ∈ selectionᶜ, dep index ^ 2 / (1 - D.weight index) :=
    (Finset.sum_add_sum_compl selection _).symm
  have hmerge : ∀ index : Fin m,
      dep index ^ 2 / D.weight index + dep index ^ 2 / (1 - D.weight index)
        = dep index ^ 2 / (D.weight index * (1 - D.weight index)) := by
    intro index
    have hw : D.weight index ≠ 0 := (D.weight_pos index).ne'
    have hco : (1 : ℝ) - D.weight index ≠ 0 := by
      have := weight_lt_one D hm index; intro hzero; linarith [hzero]
    field_simp
    ring
  have hright : (∑ index ∈ selectionᶜ, dep index ^ 2 / D.weight index)
        + ∑ index ∈ selectionᶜ, dep index ^ 2 / (1 - D.weight index)
      = ∑ index ∈ selectionᶜ, dep index ^ 2 / (D.weight index * (1 - D.weight index)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun index _ => hmerge index
  constructor
  · intro hbound
    rw [hmassSplit]
    linarith [hright]
  · intro hbound
    rw [hmassSplit] at hbound
    linarith [hright]

/-- **THE STRICT PAIR-MASS READING.** -/
theorem posDef_gap_iff_dependencyBound_pairMass (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef
      ↔ ∀ dep : Fin m → ℝ, dep ≠ 0 → (∑ index, dep index • D.atom index) = 0 →
          ∑ index, dep index ^ 2 / (1 - D.weight index)
            < ∑ index ∈ (Finset.image pick Finset.univ)ᶜ,
                dep index ^ 2 / (D.weight index * (1 - D.weight index)) := by
  classical
  rw [posDef_gap_iff_dependencyBound_compl D hm pick hinj]
  refine forall_congr' fun dep => forall_congr' fun _ => forall_congr' fun _ => ?_
  set selection : Finset (Fin m) := Finset.image pick Finset.univ with hselection
  have hmassSplit : ∑ index, dep index ^ 2 / (1 - D.weight index)
      = (∑ index ∈ selection, dep index ^ 2 / (1 - D.weight index))
        + ∑ index ∈ selectionᶜ, dep index ^ 2 / (1 - D.weight index) :=
    (Finset.sum_add_sum_compl selection _).symm
  have hmerge : ∀ index : Fin m,
      dep index ^ 2 / D.weight index + dep index ^ 2 / (1 - D.weight index)
        = dep index ^ 2 / (D.weight index * (1 - D.weight index)) := by
    intro index
    have hw : D.weight index ≠ 0 := (D.weight_pos index).ne'
    have hco : (1 : ℝ) - D.weight index ≠ 0 := by
      have := weight_lt_one D hm index; intro hzero; linarith [hzero]
    field_simp
    ring
  have hright : (∑ index ∈ selectionᶜ, dep index ^ 2 / D.weight index)
        + ∑ index ∈ selectionᶜ, dep index ^ 2 / (1 - D.weight index)
      = ∑ index ∈ selectionᶜ, dep index ^ 2 / (D.weight index * (1 - D.weight index)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun index _ => hmerge index
  constructor
  · intro hbound
    rw [hmassSplit]
    linarith [hright]
  · intro hbound
    rw [hmassSplit] at hbound
    linarith [hright]

/-! ## 3. The subset-indexed dictionary

Both criteria, restated at a `Finset` rather than at an index map, so they can be
fed to `Gtz.IsTie` verbatim. -/

/-- The image of a subset's own order embedding is that subset. -/
theorem image_orderEmb_univ_eq {selected : Finset (Fin m)} (hcard : selected.card = k) :
    Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
  apply Finset.coe_injective
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]

/-- **THE WEAK DEPENDENCY TEST OF A SUBSET.**  No atom occurs on the right beyond
the choice of WHICH vectors are dependencies. -/
def DependencyDominates (D : WeightedDesign m k) (C : Finset (Fin m)) : Prop :=
  ∀ dep : Fin m → ℝ, (∑ index, dep index • D.atom index) = 0 →
    ∑ index ∈ C, dep index ^ 2 / (1 - D.weight index)
      ≤ ∑ index ∈ Cᶜ, dep index ^ 2 / D.weight index

/-- **THE STRICT DEPENDENCY TEST OF A SUBSET.** -/
def DependencyDominatesStrictly (D : WeightedDesign m k) (C : Finset (Fin m)) : Prop :=
  ∀ dep : Fin m → ℝ, dep ≠ 0 → (∑ index, dep index • D.atom index) = 0 →
    ∑ index ∈ C, dep index ^ 2 / (1 - D.weight index)
      < ∑ index ∈ Cᶜ, dep index ^ 2 / D.weight index

theorem dominates_iff_dependencyDominates (D : WeightedDesign m k) (hm : 2 ≤ m)
    {C : Finset (Fin m)} (hcard : C.card = k) :
    Dominates D C ↔ DependencyDominates D C := by
  have hstep := dominates_iff_dependencyBound_compl D hm (C.orderEmbOfFin hcard)
    (C.orderEmbOfFin hcard).injective
  rw [image_orderEmb_univ_eq hcard] at hstep
  exact hstep

theorem posDef_gap_iff_dependencyDominatesStrictly (D : WeightedDesign m k) (hm : 2 ≤ m)
    {C : Finset (Fin m)} (hcard : C.card = k) :
    (subsetSum D C - 1).PosDef ↔ DependencyDominatesStrictly D C := by
  have hstep := posDef_gap_iff_dependencyBound_compl D hm (C.orderEmbOfFin hcard)
    (C.orderEmbOfFin hcard).injective
  rw [image_orderEmb_univ_eq hcard] at hstep
  exact hstep

/-- **A DEPENDENCY INSIDE A SELECTION REFUTES DOMINATION.**  One line from the
criterion: the right side vanishes and the left side does not.  This recovers
`Gtz.not_dominates_of_parallel_within` and `Gtz.not_dominates_of_exists_null`
from the dependency reading alone, with no null probe and no determinant. -/
theorem not_dominates_of_dependency_inside (D : WeightedDesign m k) (hm : 2 ≤ m)
    {C : Finset (Fin m)} (hcard : C.card = k) {dep : Fin m → ℝ} (hdepNe : dep ≠ 0)
    (hinside : ∀ index ∈ Cᶜ, dep index = 0)
    (hdep : (∑ index, dep index • D.atom index) = 0) :
    ¬ Dominates D C := by
  classical
  intro hdom
  have hbound := (dominates_iff_dependencyDominates D hm hcard).mp hdom dep hdep
  have hright : ∑ index ∈ Cᶜ, dep index ^ 2 / D.weight index = 0 :=
    Finset.sum_eq_zero fun index hindex => by
      rw [hinside index hindex]; simp
  obtain ⟨live, hlive⟩ := Function.ne_iff.mp hdepNe
  have hliveNe : dep live ≠ 0 := by simpa using hlive
  have hmem : live ∈ C := by
    by_contra hcontra
    exact hliveNe (hinside live (Finset.mem_compl.mpr hcontra))
  have hleft : 0 < ∑ index ∈ C, dep index ^ 2 / (1 - D.weight index) := by
    refine Finset.sum_pos' (fun index _ => ?_) ⟨live, hmem, ?_⟩
    · have hco : (0 : ℝ) < 1 - D.weight index := by
        linarith [weight_lt_one D hm index]
      positivity
    · have hco : (0 : ℝ) < 1 - D.weight live := by
        linarith [weight_lt_one D hm live]
      have hsq : 0 < dep live ^ 2 := by positivity
      exact div_pos hsq hco
  rw [hright] at hbound
  linarith

/-! ## 4. A parallel pair IS a sparse dependency

The hinge's conclusion, in the same currency as its hypothesis.  The
`Gtz.ChartCore.HasParallelPairCore` reading names one `2 x 2` minor at a time;
this names the object, and it is what a successor has to produce. -/

/-- **A SPARSE DEPENDENCY**: a nonzero linear dependency of the atoms that lives
on two labels. -/
def HasSparseDependency (D : WeightedDesign m k) : Prop :=
  ∃ (dep : Fin m → ℝ) (firstLabel secondLabel : Fin m),
    firstLabel ≠ secondLabel ∧ dep ≠ 0
      ∧ (∀ other : Fin m, other ≠ firstLabel → other ≠ secondLabel → dep other = 0)
      ∧ (∑ index, dep index • D.atom index) = 0

/-- A vector that lives on two labels totals the two terms it is carried by. -/
theorem sum_smul_of_supported {m k : ℕ} (D : WeightedDesign m k) {dep : Fin m → ℝ}
    {firstLabel secondLabel : Fin m} (hne : firstLabel ≠ secondLabel)
    (hsupport : ∀ other : Fin m, other ≠ firstLabel → other ≠ secondLabel → dep other = 0) :
    (∑ index, dep index • D.atom index)
      = dep firstLabel • D.atom firstLabel + dep secondLabel • D.atom secondLabel := by
  classical
  have hsub : ({firstLabel, secondLabel} : Finset (Fin m)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hvanish : ∀ index ∈ (Finset.univ : Finset (Fin m)),
      index ∉ ({firstLabel, secondLabel} : Finset (Fin m)) →
        dep index • D.atom index = 0 := by
    intro index _ hindex
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hindex
    rw [hsupport index hindex.1 hindex.2, zero_smul]
  rw [← Finset.sum_subset hsub hvanish, Finset.sum_pair hne]

/-- The same total, with the two surviving coefficients supplied by name. -/
theorem sum_smul_eq_pair {m k : ℕ} (D : WeightedDesign m k) (dep : Fin m → ℝ)
    {firstLabel secondLabel : Fin m} (hne : firstLabel ≠ secondLabel)
    (hsupport : ∀ other : Fin m, other ≠ firstLabel → other ≠ secondLabel → dep other = 0)
    (firstValue secondValue : ℝ) (hfirstValue : dep firstLabel = firstValue)
    (hsecondValue : dep secondLabel = secondValue) :
    (∑ index, dep index • D.atom index)
      = firstValue • D.atom firstLabel + secondValue • D.atom secondLabel := by
  rw [sum_smul_of_supported D hne hsupport, hfirstValue, hsecondValue]

/-- **A PARALLEL PAIR IS A SPARSE DEPENDENCY**, at every size and every rank.
The `Gtz.HasParallelPair` predicate allows a zero ratio, and so does this: an
atom that vanishes carries the dependency supported at its own label. -/
theorem hasParallelPair_iff_hasSparseDependency (D : WeightedDesign m k) :
    HasParallelPair D ↔ HasSparseDependency D := by
  classical
  constructor
  · rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
    have hsupport : ∀ other : Fin m, other ≠ keptLabel → other ≠ dropLabel →
        (fun index : Fin m =>
          if index = dropLabel then (1 : ℝ)
          else if index = keptLabel then -ratio else 0) other = 0 := by
      intro other hfirst hsecond
      simp [hsecond, hfirst]
    refine ⟨fun index => if index = dropLabel then 1 else if index = keptLabel then -ratio else 0,
      keptLabel, dropLabel, hne, ?_, hsupport, ?_⟩
    · intro hcontra
      have hentry := congrFun hcontra dropLabel
      simp at hentry
    · rw [sum_smul_eq_pair D _ hne hsupport (-ratio) 1 (by simp [hne]) (by simp), hparallel]
      module
  · rintro ⟨dep, firstLabel, secondLabel, hne, hdepNe, hsupport, hdep⟩
    rw [sum_smul_of_supported D hne hsupport] at hdep
    by_cases hsecond : dep secondLabel = 0
    · have hfirst : dep firstLabel ≠ 0 := by
        intro hzero
        refine hdepNe (funext fun index => ?_)
        by_cases hcase : index = firstLabel
        · rw [hcase, hzero]; rfl
        · by_cases hcase' : index = secondLabel
          · rw [hcase', hsecond]; rfl
          · rw [hsupport index hcase hcase']; rfl
      have hvanish : D.atom firstLabel = 0 := by
        rw [hsecond, zero_smul, add_zero] at hdep
        have := smul_eq_zero.mp hdep
        rcases this with hbad | hgood
        · exact absurd hbad hfirst
        · exact hgood
      exact ⟨secondLabel, firstLabel, 0, Ne.symm hne, by rw [hvanish, zero_smul]⟩
    · refine ⟨firstLabel, secondLabel, -(dep firstLabel / dep secondLabel), hne, ?_⟩
      funext coord
      have hcoord := congrFun hdep coord
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hcoord
      simp only [Pi.smul_apply, smul_eq_mul, neg_mul]
      field_simp
      linarith [hcoord]

/-! ## 5. The tie and the hinge, on the dependency space

Both registry hinges quantify over `Gtz.IsTie`.  With the two criteria of parts
2 and 4 and the reading of part 5, the whole statement leaves the atoms. -/

/-- **A TIE IS A DEPENDENCY CONDITION.**  Some `rank`-subset passes the weak
dependency test, and none passes the strict one. -/
theorem isTie_iff_dependency (D : WeightedDesign m k) (hm : 2 ≤ m) :
    IsTie D
      ↔ (∃ C : Finset (Fin m), C.card = k ∧ DependencyDominates D C)
        ∧ ∀ C : Finset (Fin m), C.card = k → ¬ DependencyDominatesStrictly D C := by
  constructor
  · rintro ⟨⟨C, hcard, hdom⟩, hnostrict⟩
    refine ⟨⟨C, hcard, (dominates_iff_dependencyDominates D hm hcard).mp hdom⟩, ?_⟩
    intro other hother hstrict
    exact hnostrict other hother
      ((posDef_gap_iff_dependencyDominatesStrictly D hm hother).mpr hstrict)
  · rintro ⟨⟨C, hcard, hdom⟩, hnostrict⟩
    refine ⟨⟨C, hcard, (dominates_iff_dependencyDominates D hm hcard).mpr hdom⟩, ?_⟩
    intro other hother hposDef
    exact hnostrict other hother
      ((posDef_gap_iff_dependencyDominatesStrictly D hm hother).mp hposDef)

/-- **THE HINGE IS A STATEMENT ABOUT A SUBSPACE OF `ℝ^size`.**  At every size with
two or more atoms and at every rank, `Gtz.HingeHoldsAtSize` holds exactly when:
whenever the dependency space of a design passes the weak test on some
`rank`-subset and the strict test on none, it contains a nonzero vector carried
by two labels.

No atom, no Parseval, no projection, no matrix inverse and no bracket occurs on
the right beyond the choice of WHICH vectors are dependencies. -/
theorem hingeHoldsAtSize_iff_dependency (size rank : ℕ) (hsize : 2 ≤ size) :
    HingeHoldsAtSize size rank
      ↔ ∀ D : WeightedDesign size rank,
          ((∃ C : Finset (Fin size), C.card = rank ∧ DependencyDominates D C)
            ∧ ∀ C : Finset (Fin size), C.card = rank →
                ¬ DependencyDominatesStrictly D C) → HasSparseDependency D := by
  constructor
  · intro hhinge D hdep
    exact (hasParallelPair_iff_hasSparseDependency D).mp
      (hhinge D ((isTie_iff_dependency D hsize).mpr hdep))
  · intro hdep D htie
    exact (hasParallelPair_iff_hasSparseDependency D).mpr
      (hdep D ((isTie_iff_dependency D hsize).mp htie))

/-! ## 6. Corank two

At size `rank + 2` every `rank`-subset omits exactly two labels, so the pair-mass
reading of part 3 tests one fixed form against a sum of exactly TWO rank-one
forms.  That is the smallest case in which the corank-one engine of
`Gtz/Wave/CorankOneRigidity.lean` — where the sum has one term and the
dependency space is a line — is not already the whole story. -/

/-- At corank two the complement of a `rank`-subset is a pair. -/
theorem exists_pair_compl_of_card_eq_corankTwo {C : Finset (Fin (k + 2))}
    (hcard : C.card = k) :
    ∃ firstLabel secondLabel : Fin (k + 2), firstLabel ≠ secondLabel
      ∧ Cᶜ = {firstLabel, secondLabel} := by
  classical
  have hcompl : Cᶜ.card = 2 := by
    rw [Finset.card_compl, hcard, Fintype.card_fin]
    omega
  obtain ⟨firstLabel, secondLabel, hne, hpair⟩ := Finset.card_eq_two.mp hcompl
  exact ⟨firstLabel, secondLabel, hne, hpair⟩

/-- **THE CORANK-TWO CRITERION.**  A `rank`-subset of a design at size
`rank + 2` dominates exactly when the fixed form `Σ_c z_c²/(1 - t_c)` on the
dependency space is dominated by the two pair-mass rank-one forms of the two
omitted labels.

At corank ONE the same reading has a single term on the right, the dependency
space is a line, and the criterion is the landed
`Gtz.dominates_erase_of_coMean_le` together with its converse. -/
theorem corankTwo_dominates_iff (D : WeightedDesign (k + 2) k)
    {C : Finset (Fin (k + 2))} (hcard : C.card = k)
    {firstLabel secondLabel : Fin (k + 2)} (hne : firstLabel ≠ secondLabel)
    (hcompl : Cᶜ = {firstLabel, secondLabel}) :
    Dominates D C
      ↔ ∀ dep : Fin (k + 2) → ℝ, (∑ index, dep index • D.atom index) = 0 →
          ∑ index, dep index ^ 2 / (1 - D.weight index)
            ≤ dep firstLabel ^ 2
                / (D.weight firstLabel * (1 - D.weight firstLabel))
              + dep secondLabel ^ 2
                / (D.weight secondLabel * (1 - D.weight secondLabel)) := by
  classical
  have hm : 2 ≤ k + 2 := by omega
  have hstep := dominates_iff_dependencyBound_pairMass D hm (C.orderEmbOfFin hcard)
    (C.orderEmbOfFin hcard).injective
  rw [image_orderEmb_univ_eq hcard, hcompl] at hstep
  rw [hstep]
  exact forall_congr' fun dep => forall_congr' fun _ => by rw [Finset.sum_pair hne]

/-- **THE STRICT CORANK-TWO CRITERION.** -/
theorem corankTwo_posDef_gap_iff (D : WeightedDesign (k + 2) k)
    {C : Finset (Fin (k + 2))} (hcard : C.card = k)
    {firstLabel secondLabel : Fin (k + 2)} (hne : firstLabel ≠ secondLabel)
    (hcompl : Cᶜ = {firstLabel, secondLabel}) :
    (subsetSum D C - 1).PosDef
      ↔ ∀ dep : Fin (k + 2) → ℝ, dep ≠ 0 → (∑ index, dep index • D.atom index) = 0 →
          ∑ index, dep index ^ 2 / (1 - D.weight index)
            < dep firstLabel ^ 2
                / (D.weight firstLabel * (1 - D.weight firstLabel))
              + dep secondLabel ^ 2
                / (D.weight secondLabel * (1 - D.weight secondLabel)) := by
  classical
  have hm : 2 ≤ k + 2 := by omega
  have hstep := posDef_gap_iff_dependencyBound_pairMass D hm (C.orderEmbOfFin hcard)
    (C.orderEmbOfFin hcard).injective
  rw [image_orderEmb_univ_eq hcard, hcompl] at hstep
  rw [hstep]
  exact forall_congr' fun dep => forall_congr' fun _ => forall_congr' fun _ => by
    rw [Finset.sum_pair hne]

/-- **AT CORANK TWO A SPARSE DEPENDENCY POISONS ONE SUBSET OUTRIGHT.**  If a
nonzero dependency lives on the two labels a `rank`-subset keeps out of its own
complement — that is, on labels inside the subset — the subset dominates
nothing. -/
theorem corankTwo_not_dominates_of_sparse (D : WeightedDesign (k + 2) k)
    {C : Finset (Fin (k + 2))} (hcard : C.card = k) {dep : Fin (k + 2) → ℝ}
    {firstLabel secondLabel : Fin (k + 2)} (hdepNe : dep ≠ 0)
    (hfirst : firstLabel ∈ C) (hsecond : secondLabel ∈ C)
    (hsupport : ∀ other : Fin (k + 2), other ≠ firstLabel → other ≠ secondLabel →
      dep other = 0)
    (hdep : (∑ index, dep index • D.atom index) = 0) :
    ¬ Dominates D C := by
  classical
  have hm : 2 ≤ k + 2 := by omega
  refine not_dominates_of_dependency_inside D hm hcard hdepNe ?_ hdep
  intro index hindex
  have hout : index ∉ C := Finset.mem_compl.mp hindex
  refine hsupport index (fun hcontra => hout (hcontra ▸ hfirst))
    (fun hcontra => hout (hcontra ▸ hsecond))

/-! ## 7. The self-dual cell: complementary selections share one budget

At `size = 2 * rank` — the band's LOWER ENDPOINT, and the first rank-four band
cell `(8,4)` — the complement of a `rank`-subset is again a `rank`-subset, so the
`C(2 rank, rank)` selection tests pair up.  The pairing law below is one line of
arithmetic, and it holds at every size, but it only SAYS anything where the
complement is itself a selection.

The defect of a pair of complementary selections at a given dependency is a fixed
number that does not know which pair it came from.  So the seventy tests of an
`(8,4)` design carry only thirty-five budgets between them. -/

/-- **THE DEPENDENCY DEFECT** of a selection at a dependency: the right side of the
criterion less the left.  `Gtz.DependencyDominates` is its nonnegativity. -/
noncomputable def dependencyDefect (D : WeightedDesign m k) (C : Finset (Fin m))
    (dep : Fin m → ℝ) : ℝ :=
  (∑ index ∈ Cᶜ, dep index ^ 2 / D.weight index)
    - ∑ index ∈ C, dep index ^ 2 / (1 - D.weight index)

theorem dependencyDominates_iff_defect_nonneg (D : WeightedDesign m k)
    (C : Finset (Fin m)) :
    DependencyDominates D C
      ↔ ∀ dep : Fin m → ℝ, (∑ index, dep index • D.atom index) = 0 →
          0 ≤ dependencyDefect D C dep := by
  refine forall_congr' fun dep => forall_congr' fun _ => ?_
  rw [dependencyDefect]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **THE COMPLEMENTARY BUDGET.**  The defects of a selection and of its complement
total a fixed reading of the dependency that mentions no selection at all:

    `Σ_c z_c² (1 - 2 t_c) / (t_c (1 - t_c))` .

The weight enters exactly through the campaign's pair mass `t_c(1 - t_c)`, and the
sign of each term is the sign of `1 - 2 t_c`. -/
theorem dependencyDefect_add_compl (D : WeightedDesign m k) (hm : 2 ≤ m)
    (C : Finset (Fin m)) (dep : Fin m → ℝ) :
    dependencyDefect D C dep + dependencyDefect D Cᶜ dep
      = ∑ index, dep index ^ 2 * (1 - 2 * D.weight index)
          / (D.weight index * (1 - D.weight index)) := by
  classical
  have hweightSplit : (∑ index ∈ Cᶜ, dep index ^ 2 / D.weight index)
      + ∑ index ∈ C, dep index ^ 2 / D.weight index
      = ∑ index, dep index ^ 2 / D.weight index := by
    rw [add_comm]
    exact Finset.sum_add_sum_compl C _
  have hcoSplit : (∑ index ∈ C, dep index ^ 2 / (1 - D.weight index))
      + ∑ index ∈ Cᶜ, dep index ^ 2 / (1 - D.weight index)
      = ∑ index, dep index ^ 2 / (1 - D.weight index) :=
    Finset.sum_add_sum_compl C _
  have hmerge : ∑ index, dep index ^ 2 * (1 - 2 * D.weight index)
        / (D.weight index * (1 - D.weight index))
      = (∑ index, dep index ^ 2 / D.weight index)
        - ∑ index, dep index ^ 2 / (1 - D.weight index) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun index _ => ?_
    have hw : D.weight index ≠ 0 := (D.weight_pos index).ne'
    have hco : (1 : ℝ) - D.weight index ≠ 0 := by
      have := weight_lt_one D hm index; intro hzero; linarith [hzero]
    field_simp
    ring
  rw [dependencyDefect, dependencyDefect, compl_compl, hmerge]
  linarith [hweightSplit, hcoSplit]

/-- **THE BUDGET DOES NOT KNOW WHICH PAIR IT CAME FROM.**  Every complementary pair
of selections shares the same total defect at every dependency. -/
theorem dependencyDefect_add_compl_eq (D : WeightedDesign m k) (hm : 2 ≤ m)
    (firstSelection secondSelection : Finset (Fin m)) (dep : Fin m → ℝ) :
    dependencyDefect D firstSelection dep + dependencyDefect D firstSelectionᶜ dep
      = dependencyDefect D secondSelection dep + dependencyDefect D secondSelectionᶜ dep := by
  rw [dependencyDefect_add_compl D hm firstSelection dep,
    dependencyDefect_add_compl D hm secondSelection dep]

/-- The budget is nonnegative at every dependency once no weight passes one half. -/
theorem dependencyBudget_nonneg_of_weight_le_half (D : WeightedDesign m k) (hm : 2 ≤ m)
    (hhalf : ∀ index : Fin m, D.weight index ≤ 1 / 2) (dep : Fin m → ℝ) :
    0 ≤ ∑ index, dep index ^ 2 * (1 - 2 * D.weight index)
        / (D.weight index * (1 - D.weight index)) := by
  refine Finset.sum_nonneg fun index _ => ?_
  have hpos := D.weight_pos index
  have hco : (0 : ℝ) < 1 - D.weight index := by linarith [weight_lt_one D hm index]
  have hnum : (0 : ℝ) ≤ 1 - 2 * D.weight index := by linarith [hhalf index]
  have hden : (0 : ℝ) < D.weight index * (1 - D.weight index) := mul_pos hpos hco
  exact div_nonneg (mul_nonneg (sq_nonneg _) hnum) hden.le

/-- **TWO COMPLEMENTARY SELECTIONS CANNOT FAIL AT ONE DEPENDENCY.**  If no weight
passes one half, a dependency at which a selection fails is a dependency at which
its complement succeeds STRICTLY.

At `size = 2 * rank` both are `rank`-subsets, so this is a dichotomy between two
genuine selections of the design.  At `(8,4)` it pairs the seventy tests into
thirty-five. -/
theorem dependencyDefect_pos_of_compl_neg (D : WeightedDesign m k) (hm : 2 ≤ m)
    (hhalf : ∀ index : Fin m, D.weight index ≤ 1 / 2) (C : Finset (Fin m))
    (dep : Fin m → ℝ) (hneg : dependencyDefect D C dep < 0) :
    0 < dependencyDefect D Cᶜ dep := by
  have hsum := dependencyDefect_add_compl D hm C dep
  have hbudget := dependencyBudget_nonneg_of_weight_le_half D hm hhalf dep
  linarith

/-- **A NEGATIVE BUDGET FORBIDS A COMPLEMENTARY DOMINATING PAIR.**  If some
dependency reads the budget negatively — which needs a label of weight past one
half — then no selection and its complement can both dominate.  Weight-aware, and
it decides thirty-five of the seventy `(8,4)` tests at once. -/
theorem not_dominates_and_compl_of_budget_neg (D : WeightedDesign m k) (hm : 2 ≤ m)
    {C : Finset (Fin m)} (hcard : C.card = k) (hcompl : Cᶜ.card = k)
    {dep : Fin m → ℝ} (hdep : (∑ index, dep index • D.atom index) = 0)
    (hbudget : ∑ index, dep index ^ 2 * (1 - 2 * D.weight index)
        / (D.weight index * (1 - D.weight index)) < 0) :
    ¬ (Dominates D C ∧ Dominates D Cᶜ) := by
  rintro ⟨hdom, hdomCompl⟩
  have hfirst := (dependencyDominates_iff_defect_nonneg D C).mp
    ((dominates_iff_dependencyDominates D hm hcard).mp hdom) dep hdep
  have hsecond := (dependencyDominates_iff_defect_nonneg D Cᶜ).mp
    ((dominates_iff_dependencyDominates D hm hcompl).mp hdomCompl) dep hdep
  have hsum := dependencyDefect_add_compl D hm C dep
  linarith

/-- At size twice the rank the complement of a `rank`-subset is a `rank`-subset. -/
theorem card_compl_eq_rank_of_two_mul {rank : ℕ} {C : Finset (Fin (2 * rank))}
    (hcard : C.card = rank) : Cᶜ.card = rank := by
  rw [Finset.card_compl, hcard, Fintype.card_fin]
  omega

/-- **THE PAIR-MASS FORM IS THE WEIGHT-AVERAGE OF THE LABELS' OWN FORMS.**  The left
side of `Gtz.dominates_iff_dependencyBound_pairMass` is the `t`-weighted MEAN of
the rank-one forms on its right.

This is the whole engine of the corank-one rigidity, in dependency currency: at
corank one the right side has a single term, no strict dominator caps each term by
the mean, and a family that never passes its own weighted mean is constant.  At
corank two the right side has two terms and the averaging argument stops. -/
theorem sum_weight_mul_pairMass (D : WeightedDesign m k) (hm : 2 ≤ m)
    (dep : Fin m → ℝ) :
    ∑ index, D.weight index
        * (dep index ^ 2 / (D.weight index * (1 - D.weight index)))
      = ∑ index, dep index ^ 2 / (1 - D.weight index) := by
  refine Finset.sum_congr rfl fun index _ => ?_
  have hw : D.weight index ≠ 0 := (D.weight_pos index).ne'
  have hco : (1 : ℝ) - D.weight index ≠ 0 := by
    have := weight_lt_one D hm index; intro hzero; linarith [hzero]
  field_simp
  try ring

/-- **THE `(8,4)` READING OF THE COMPLEMENTARY BUDGET.**  At the first band cell of
rank four the seventy four-subsets carry thirty-five budgets between them, and the
budget of a complementary pair is one fixed reading of the dependency. -/
theorem eightFour_dependencyDefect_add_compl (D : WeightedDesign 8 4)
    (C : Finset (Fin 8)) (dep : Fin 8 → ℝ) :
    dependencyDefect D C dep + dependencyDefect D Cᶜ dep
      = ∑ index, dep index ^ 2 * (1 - 2 * D.weight index)
          / (D.weight index * (1 - D.weight index)) :=
  dependencyDefect_add_compl D (by norm_num) C dep

/-! ## 8. The two rank-four registry statements

The exact types of `Skeleton.obligationSubThresholdBandHinge` and
`Skeleton.obligationThresholdCellHingeRankFourAndUp`, carried inside `Gtz` so the
readings above apply to them.  Nothing here proves either. -/

/-- The band hinge, with the type of `Skeleton.obligationSubThresholdBandHinge`. -/
def SubThresholdBandHingeStatement : Prop :=
  ∀ rank : ℕ, 3 ≤ rank →
    ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
      GtzWeighted (size - 1) rank →
        ∀ design : WeightedDesign size rank, IsTie design → HasParallelPair design

/-- The threshold-cell hinge, with the type of
`Skeleton.obligationThresholdCellHingeRankFourAndUp`. -/
def ThresholdCellHingeRankFourAndUpStatement : Prop :=
  ∀ rank : ℕ, 4 ≤ rank →
    GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
        IsTie design → HasParallelPair design

/-- The band statement is a family of `Gtz.HingeHoldsAtSize` instances. -/
theorem subThresholdBandHingeStatement_iff_hinge :
    SubThresholdBandHingeStatement
      ↔ ∀ rank : ℕ, 3 ≤ rank →
          ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
            GtzWeighted (size - 1) rank → HingeHoldsAtSize size rank :=
  Iff.rfl

/-- The threshold-cell statement is a family of `Gtz.HingeHoldsAtSize` instances. -/
theorem thresholdCellHingeRankFourAndUpStatement_iff_hinge :
    ThresholdCellHingeRankFourAndUpStatement
      ↔ ∀ rank : ℕ, 4 ≤ rank →
          GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
            HingeHoldsAtSize (rank * (rank + 1) / 2) rank :=
  Iff.rfl

/-- **THE BAND STATEMENT IN THE CHART.**  Every cell of the band, at every rank,
carried into `Gtz.ChartCore` by `Gtz.hingeHoldsAtSize_iff_chartCore`. -/
theorem subThresholdBandHingeStatement_iff_chartCore :
    SubThresholdBandHingeStatement
      ↔ ∀ rank : ℕ, 3 ≤ rank →
          ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
            GtzWeighted (size - 1) rank →
              ∀ core : ChartCore size rank, core.IsTieCore → core.HasParallelPairCore := by
  constructor
  · intro hband rank hrank size hlow hhigh hpred
    exact (hingeHoldsAtSize_iff_chartCore size rank).mp (hband rank hrank size hlow hhigh hpred)
  · intro hchart rank hrank size hlow hhigh hpred
    exact (hingeHoldsAtSize_iff_chartCore size rank).mpr
      (hchart rank hrank size hlow hhigh hpred)

/-- **THE THRESHOLD-CELL STATEMENT IN THE CHART.** -/
theorem thresholdCellHingeRankFourAndUpStatement_iff_chartCore :
    ThresholdCellHingeRankFourAndUpStatement
      ↔ ∀ rank : ℕ, 4 ≤ rank →
          GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
            ∀ core : ChartCore (rank * (rank + 1) / 2) rank,
              core.IsTieCore → core.HasParallelPairCore := by
  constructor
  · intro hcell rank hrank hpred
    exact (hingeHoldsAtSize_iff_chartCore (rank * (rank + 1) / 2) rank).mp
      (hcell rank hrank hpred)
  · intro hchart rank hrank hpred
    exact (hingeHoldsAtSize_iff_chartCore (rank * (rank + 1) / 2) rank).mpr
      (hchart rank hrank hpred)

/-- **THE BAND STATEMENT ON THE DEPENDENCY SPACE.**  The size guard supplies the
two atoms the criteria need, since `2 ≤ 2 * rank ≤ size`. -/
theorem subThresholdBandHingeStatement_iff_dependency :
    SubThresholdBandHingeStatement
      ↔ ∀ rank : ℕ, 3 ≤ rank →
          ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
            GtzWeighted (size - 1) rank →
              ∀ D : WeightedDesign size rank,
                ((∃ C : Finset (Fin size), C.card = rank ∧ DependencyDominates D C)
                  ∧ ∀ C : Finset (Fin size), C.card = rank →
                      ¬ DependencyDominatesStrictly D C) → HasSparseDependency D := by
  constructor
  · intro hband rank hrank size hlow hhigh hpred
    have hsize : 2 ≤ size := by omega
    exact (hingeHoldsAtSize_iff_dependency size rank hsize).mp
      (hband rank hrank size hlow hhigh hpred)
  · intro hdep rank hrank size hlow hhigh hpred
    have hsize : 2 ≤ size := by omega
    exact (hingeHoldsAtSize_iff_dependency size rank hsize).mpr
      (hdep rank hrank size hlow hhigh hpred)

/-! ## 9. Rank four, cell by cell

The band at rank four is exactly the two sizes eight and nine, and the threshold
cell is size ten.  Each is restated in both charts. -/

/-- **THE BAND AT RANK FOUR IS THE TWO SIZES EIGHT AND NINE.** -/
theorem bandCell_rank_four (size : ℕ) :
    (2 * 4 ≤ size ∧ size < 4 * (4 + 1) / 2) ↔ (size = 8 ∨ size = 9) := by
  omega

/-- **THE THRESHOLD CELL AT RANK FOUR IS SIZE TEN.** -/
theorem thresholdCell_rank_four : 4 * (4 + 1) / 2 = 10 := by norm_num

/-- **THE RANK-FOUR BAND IS TWO CELLS.**  The band statement, restricted to rank
four, is exactly the two hinges at sizes eight and nine, each granted its own
predecessor cell. -/
theorem subThresholdBandHinge_rank_four_iff :
    (∀ size : ℕ, 2 * 4 ≤ size → size < 4 * (4 + 1) / 2 →
        GtzWeighted (size - 1) 4 → HingeHoldsAtSize size 4)
      ↔ (GtzWeighted 7 4 → HingeHoldsAtSize 8 4)
        ∧ (GtzWeighted 8 4 → HingeHoldsAtSize 9 4) := by
  constructor
  · intro hband
    exact ⟨fun hpred => hband 8 (by norm_num) (by norm_num) hpred,
      fun hpred => hband 9 (by norm_num) (by norm_num) hpred⟩
  · rintro ⟨height, hnine⟩ size hlow hhigh hpred
    rcases (bandCell_rank_four size).mp ⟨hlow, hhigh⟩ with hcase | hcase
    · subst hcase; exact height hpred
    · subst hcase; exact hnine hpred

/-- The first band cell of rank four, in the chart. -/
theorem hingeHoldsAtSize_eight_four_iff_chartCore :
    HingeHoldsAtSize 8 4
      ↔ ∀ core : ChartCore 8 4, core.IsTieCore → core.HasParallelPairCore :=
  hingeHoldsAtSize_iff_chartCore 8 4

/-- The second band cell of rank four, in the chart. -/
theorem hingeHoldsAtSize_nine_four_iff_chartCore :
    HingeHoldsAtSize 9 4
      ↔ ∀ core : ChartCore 9 4, core.IsTieCore → core.HasParallelPairCore :=
  hingeHoldsAtSize_iff_chartCore 9 4

/-- The threshold cell of rank four, in the chart. -/
theorem hingeHoldsAtSize_ten_four_iff_chartCore :
    HingeHoldsAtSize 10 4
      ↔ ∀ core : ChartCore 10 4, core.IsTieCore → core.HasParallelPairCore :=
  hingeHoldsAtSize_iff_chartCore 10 4

/-- **THE FIRST BAND CELL OF RANK FOUR, ON THE DEPENDENCY SPACE.**  A
four-dimensional subspace of `ℝ^8`, eight positive weights, and the seventy
four-subsets.  Nothing else. -/
theorem hingeHoldsAtSize_eight_four_iff_dependency :
    HingeHoldsAtSize 8 4
      ↔ ∀ D : WeightedDesign 8 4,
          ((∃ C : Finset (Fin 8), C.card = 4 ∧ DependencyDominates D C)
            ∧ ∀ C : Finset (Fin 8), C.card = 4 →
                ¬ DependencyDominatesStrictly D C) → HasSparseDependency D :=
  hingeHoldsAtSize_iff_dependency 8 4 (by norm_num)

/-- The second band cell of rank four, on the dependency space. -/
theorem hingeHoldsAtSize_nine_four_iff_dependency :
    HingeHoldsAtSize 9 4
      ↔ ∀ D : WeightedDesign 9 4,
          ((∃ C : Finset (Fin 9), C.card = 4 ∧ DependencyDominates D C)
            ∧ ∀ C : Finset (Fin 9), C.card = 4 →
                ¬ DependencyDominatesStrictly D C) → HasSparseDependency D :=
  hingeHoldsAtSize_iff_dependency 9 4 (by norm_num)

/-- The threshold cell of rank four, on the dependency space. -/
theorem hingeHoldsAtSize_ten_four_iff_dependency :
    HingeHoldsAtSize 10 4
      ↔ ∀ D : WeightedDesign 10 4,
          ((∃ C : Finset (Fin 10), C.card = 4 ∧ DependencyDominates D C)
            ∧ ∀ C : Finset (Fin 10), C.card = 4 →
                ¬ DependencyDominatesStrictly D C) → HasSparseDependency D :=
  hingeHoldsAtSize_iff_dependency 10 4 (by norm_num)

/-- **BOTH RANK-FOUR CELLS QUANTIFY OVER AN INHABITED STRATUM, IN DEPENDENCY
CURRENCY.**  `Gtz.exists_isTie_eightFour` supplies the tie and
`Gtz.isTie_iff_dependency` carries it across, so neither reading above is
vacuous. -/
theorem exists_dependencyTie_eight_four :
    ∃ D : WeightedDesign 8 4,
      (∃ C : Finset (Fin 8), C.card = 4 ∧ DependencyDominates D C)
        ∧ ∀ C : Finset (Fin 8), C.card = 4 → ¬ DependencyDominatesStrictly D C := by
  obtain ⟨D, htie⟩ := exists_isTie_eightFour
  exact ⟨D, (isTie_iff_dependency D (by norm_num)).mp htie⟩

/-- The threshold cell of rank four carries a tie in dependency currency. -/
theorem exists_dependencyTie_ten_four :
    ∃ D : WeightedDesign 10 4,
      (∃ C : Finset (Fin 10), C.card = 4 ∧ DependencyDominates D C)
        ∧ ∀ C : Finset (Fin 10), C.card = 4 → ¬ DependencyDominatesStrictly D C := by
  obtain ⟨D, htie⟩ := exists_isTie_tenFour
  exact ⟨D, (isTie_iff_dependency D (by norm_num)).mp htie⟩

end Gtz
