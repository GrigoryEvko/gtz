import Gtz.Wave.KFourPivotRecurrentTriangleWiring
import Gtz.Wave.KFourPivotTriangleClosure
import Gtz.Wave.KFourTypeANonlocalEndgame
import Gtz.Design.ChartDesignWhitening
import Gtz.Design.StallTypeSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The triangle stall carries one free pivot

`Gtz.KFourTriangleStallClosure` is the shared bottleneck of BOTH terminal `K4`
walls.  `Gtz.kFourWindowAllPivotWallClosure_of_triangleStallClosure` closes the
whole four-pivot window wall from it, and
`Gtz.kFourGaugeStarCorankWallClosure_iff_typeAStallClosure` reduces the canonical
gauge wall to its matching-complement branch once it holds.  Its hypothesis asks
FOUR ladder pivots to reach one.

This module proves that one of the four is FREE.

## The automatic pivot

A four-edge selection of `K4` contains at most one triangle
(`kFourCardFour_triangle_unique`), so a triangle-carrying selection is `T` plus
exactly one further label `g`.  Erasing `g` returns `T` itself, and a triangle is
never strict (`Gtz.kFourTriangle_gap_not_posDef`).  The erasure equivalence
`Gtz.posDef_directionChartGap_erase_iff` then forces the pivot at `g` to reach
one, from positive definiteness alone.  No stall hypothesis is spent.

`kFourTriangleStallClosure_iff_sharp` turns that into an EQUIVALENCE: the
four-pivot hypothesis of the shared bottleneck is interchangeable with a
three-pivot hypothesis carried only on the triangle.  The residual is smaller
than the definition makes it look.

## The complement reading of the type split

`Gtz.kFourCardFour_matchingCompl_or_triangle` splits a four-edge selection by
triangle containment.  `kFourCardFour_containsTriangle_iff_compl_meets` shows the
split is decided by the two OMITTED labels alone: the selection carries a
triangle exactly when its two omitted edges meet at a vertex, and it is type A
exactly when they are disjoint.  Twelve of the fifteen four-edge selections are
triangle type.

## What a stall forbids

`not_posDef_of_subset_of_stall` reads minimality through the complement at every
size and every direction family: inside a stall, no subselection is strict, so a
strict selection must use an omitted label.  At `K4` that is
`kFourTriangleStall_winner_meets_compl`.

## A refuted rule, with its witness

The natural dispatch at a triangle stall nominates the vertex star at the shared
vertex of the two omitted edges.  `kFourTriangleStall_starRule_refuted` refutes
it with an exact rational chart point.  A census over 5208 triangle stalls fires
that rule at 3663 of them.
-/

namespace Gtz

open Matrix

/-! ## 1.  The four-edge combinatorics -/

/-- The four triangles of `K4`, as a predicate on one selection. -/
def IsKFourTriangle (T : Finset (Fin 6)) : Prop :=
  T = {0, 1, 2} ∨ T = {0, 3, 4} ∨ T = {1, 3, 5} ∨ T = {2, 4, 5}

instance : DecidablePred IsKFourTriangle := fun T => by
  unfold IsKFourTriangle; infer_instance

instance : DecidablePred KFourContainsTriangle := fun S => by
  unfold KFourContainsTriangle; infer_instance

theorem isKFourTriangle_card {T : Finset (Fin 6)} (htri : IsKFourTriangle T) :
    T.card = 3 := by
  rcases htri with h | h | h | h <;> subst h <;> decide

theorem containsTriangle_iff_exists {selected : Finset (Fin 6)} :
    KFourContainsTriangle selected
      ↔ ∃ T : Finset (Fin 6), IsKFourTriangle T ∧ T ⊆ selected := by
  constructor
  · rintro (h | h | h | h)
    · exact ⟨{0, 1, 2}, Or.inl rfl, h⟩
    · exact ⟨{0, 3, 4}, Or.inr (Or.inl rfl), h⟩
    · exact ⟨{1, 3, 5}, Or.inr (Or.inr (Or.inl rfl)), h⟩
    · exact ⟨{2, 4, 5}, Or.inr (Or.inr (Or.inr rfl)), h⟩
  · rintro ⟨T, (h | h | h | h), hsub⟩ <;> subst h
    · exact Or.inl hsub
    · exact Or.inr (Or.inl hsub)
    · exact Or.inr (Or.inr (Or.inl hsub))
    · exact Or.inr (Or.inr (Or.inr hsub))

/-- **AT MOST ONE TRIANGLE.**  Two distinct triangles of `K4` share exactly one
edge, so their union has five labels and cannot sit inside a four-edge
selection. -/
theorem kFourCardFour_triangle_unique (selected : Finset (Fin 6))
    (hcard : selected.card = 4) {S T : Finset (Fin 6)}
    (hS : IsKFourTriangle S) (hT : IsKFourTriangle T)
    (hSsub : S ⊆ selected) (hTsub : T ⊆ selected) : S = T := by
  revert hcard hSsub hTsub
  rcases hS with h | h | h | h <;> subst h <;>
    rcases hT with h' | h' | h' | h' <;> subst h' <;>
      revert selected <;> decide

/-- **THE TYPE SPLIT IS READ OFF THE COMPLEMENT.**  A four-edge selection carries
a triangle exactly when its two omitted labels are NOT one of the three perfect
matchings, that is, exactly when the omitted pair meets at a vertex. -/
theorem kFourCardFour_containsTriangle_iff_compl_meets (selected : Finset (Fin 6))
    (hcard : selected.card = 4) :
    KFourContainsTriangle selected
      ↔ ¬ (selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3}) := by
  revert hcard
  revert selected
  decide

/-- Twelve of the fifteen four-edge selections carry a triangle. -/
theorem kFourCardFour_triangle_count :
    ((Finset.univ : Finset (Finset (Fin 6))).filter
      (fun S => S.card = 4 ∧ KFourContainsTriangle S)).card = 12 := by
  decide

/-- The three type-A selections are the complements of the perfect matchings. -/
theorem kFourCardFour_typeA_count :
    ((Finset.univ : Finset (Finset (Fin 6))).filter
      (fun S => S.card = 4 ∧ ¬ KFourContainsTriangle S)).card = 3 := by
  decide

/-! ## 2.  Erasing the unique outside label of the triangle -/

/-- A triangle inside a four-edge selection leaves exactly one further label, and
erasing that label returns the triangle. -/
theorem erase_eq_of_triangle_subset {selected T : Finset (Fin 6)}
    (hcard : selected.card = 4) (htri : IsKFourTriangle T) (hsub : T ⊆ selected)
    {g : Fin 6} (hg : g ∈ selected) (hgnot : g ∉ T) :
    selected.erase g = T := by
  have hTcard : T.card = 3 := isKFourTriangle_card htri
  have hsubErase : T ⊆ selected.erase g := fun x hx =>
    Finset.mem_erase.mpr ⟨fun hxg => hgnot (hxg ▸ hx), hsub hx⟩
  have hEraseCard : (selected.erase g).card = 3 := by
    rw [Finset.card_erase_of_mem hg, hcard]
  exact (Finset.eq_of_subset_of_card_le hsubErase (by rw [hEraseCard, hTcard])).symm

/-! ## 3.  The automatic pivot -/

/-- **THE FREE PIVOT OF A TRIANGLE SELECTION.**  Let a four-edge selection carry
a triangle `T` and be strictly dominating.  Then the ladder pivot at its unique
non-triangle label reaches one, with NO stall hypothesis.

Erasing that label returns `T`, a triangle is never strict, and the erasure
equivalence converts that refusal into the pivot bound.  One of the four
conditions in the shared bottleneck is therefore free. -/
theorem chartLadderPivot_ge_one_of_triangle_of_posDef
    (point : DirectionChartPoint 6) {selected T : Finset (Fin 6)}
    (hcard : selected.card = 4) (htri : IsKFourTriangle T) (hsub : T ⊆ selected)
    {g : Fin 6} (hg : g ∈ selected) (hgnot : g ∉ T)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef) :
    1 ≤ chartLadderPivot kFourDirection point.mass point.weight selected g := by
  by_contra hlt
  push Not at hlt
  have hErasePd :
      (directionChartGap kFourDirection point.mass point.weight
        (selected.erase g)).PosDef :=
    (posDef_directionChartGap_erase_iff kFourDirection point.mass point.weight
      point.mass_pos point.weight_pos selected hg hpd).mpr hlt
  rw [erase_eq_of_triangle_subset hcard htri hsub hg hgnot] at hErasePd
  exact kFourTriangle_gap_not_posDef point T htri hErasePd

/-- The free pivot, stated against the ambient selection rather than a named
triangle label. -/
theorem exists_free_pivot_of_containsTriangle
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    (hcard : selected.card = 4) (hcontains : KFourContainsTriangle selected)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef) :
    ∃ T : Finset (Fin 6), IsKFourTriangle T ∧ T ⊆ selected ∧
      ∀ label ∈ selected, label ∉ T →
        1 ≤ chartLadderPivot kFourDirection point.mass point.weight
          selected label := by
  obtain ⟨T, htri, hsub⟩ := containsTriangle_iff_exists.mp hcontains
  exact ⟨T, htri, hsub, fun label hmem hnot =>
    chartLadderPivot_ge_one_of_triangle_of_posDef point hcard htri hsub hmem hnot hpd⟩

/-! ## 4.  The sharpened shared bottleneck -/

/-- **THE THREE-PIVOT FORM OF THE TRIANGLE STALL.**  The stall hypothesis is
carried only on the triangle's own three labels. -/
def KFourTriangleStallClosureSharp : Prop :=
  ∀ (point : DirectionChartPoint 6) (selected T : Finset (Fin 6)),
    selected.card = 4 →
    IsKFourTriangle T → T ⊆ selected →
    (directionChartGap kFourDirection point.mass point.weight selected).PosDef →
    (∀ label ∈ T,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        selected label) →
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- The three-pivot form implies the landed four-pivot form: the four-pivot
hypothesis restricts to the triangle. -/
theorem kFourTriangleStallClosure_of_sharp
    (hsharp : KFourTriangleStallClosureSharp) : KFourTriangleStallClosure := by
  intro point selected hcard hpd hstall hcontains
  obtain ⟨T, htri, hsub⟩ := containsTriangle_iff_exists.mp hcontains
  exact hsharp point selected T hcard htri hsub hpd
    fun label hmem => hstall label (hsub hmem)

/-- The landed four-pivot form implies the three-pivot form: the missing fourth
pivot is the free one. -/
theorem kFourTriangleStallClosureSharp_of_closure
    (hclose : KFourTriangleStallClosure) : KFourTriangleStallClosureSharp := by
  intro point selected T hcard htri hsub hpd hstallT
  refine hclose point selected hcard hpd (fun label hmem => ?_)
    (containsTriangle_iff_exists.mpr ⟨T, htri, hsub⟩)
  by_cases hmemT : label ∈ T
  · exact hstallT label hmemT
  · exact chartLadderPivot_ge_one_of_triangle_of_posDef point hcard htri hsub
      hmem hmemT hpd

/-- **THE SHARED BOTTLENECK NEEDS ONLY THREE PIVOTS.**  The four-pivot hypothesis
of `Gtz.KFourTriangleStallClosure` is interchangeable with a three-pivot
hypothesis carried on the triangle alone. -/
theorem kFourTriangleStallClosure_iff_sharp :
    KFourTriangleStallClosure ↔ KFourTriangleStallClosureSharp :=
  ⟨kFourTriangleStallClosureSharp_of_closure, kFourTriangleStallClosure_of_sharp⟩

/-! ## 5.  What the sharpened form already closes -/

/-- The three-pivot form closes the complete four-pivot window wall. -/
theorem kFourWindowAllPivotWallClosure_of_sharp
    (hsharp : KFourTriangleStallClosureSharp) : KFourWindowAllPivotWallClosure :=
  kFourWindowAllPivotWallClosure_of_triangleStallClosure
    (kFourPivotWallTriangleStallClosure_of_triangleStallClosure
      (kFourTriangleStallClosure_of_sharp hsharp))

/-- With the three-pivot form in hand the canonical gauge wall is exactly its
matching-complement branch. -/
theorem kFourGaugeStarCorankWallClosure_iff_typeA_of_sharp
    (hsharp : KFourTriangleStallClosureSharp) :
    KFourGaugeStarCorankWallClosure ↔ KFourGaugeWallTypeAStallClosure :=
  kFourGaugeStarCorankWallClosure_iff_typeAStallClosure
    (kFourTriangleStallClosure_of_sharp hsharp)

/-- **BOTH TERMINAL WALLS FROM THE THREE-PIVOT FORM AND THE TYPE-A BRANCH.** -/
theorem kFourGaugeAndPivotWallClosure_of_sharp_of_typeA
    (hsharp : KFourTriangleStallClosureSharp)
    (htypeA : KFourGaugeWallTypeAStallClosure) :
    KFourGaugeAndPivotWallClosure :=
  ⟨kFourWindowAllPivotWallClosure_of_sharp hsharp,
    (kFourGaugeStarCorankWallClosure_iff_typeA_of_sharp hsharp).mpr htypeA⟩

/-! ## 6.  What a stall forbids, at every size -/

/-- **A STALL ADMITS NO STRICT SUBSELECTION.**  Stated through the complement and
generic in the ambient size: if every label of a strictly dominating selection
carries pivot at least one, then no subset of it is strictly dominating. -/
theorem not_posDef_of_subset_of_stall {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {selected smaller : Finset (Fin size)}
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot direction mass weight selected label)
    (hsub : smaller ⊂ selected) :
    ¬ (directionChartGap direction mass weight smaller).PosDef :=
  (stall_iff_minimal_posDef direction mass weight hmass hweight selected hpd).mp
    hstall smaller hsub

/-- **A WINNER MUST USE AN OMITTED LABEL.**  At a `K4` stall every strictly
dominating spanning tree meets the complement of the stall.  A census over 15852
winners at triangle stalls records not one inside the stall. -/
theorem kFourTriangleStall_winner_meets_compl
    (point : DirectionChartPoint 6) {selected winner : Finset (Fin 6)}
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        selected label)
    (hwin : (directionChartGap kFourDirection point.mass point.weight
      winner).PosDef)
    (hne : winner ≠ selected) : ¬ winner ⊆ selected := by
  intro hsub
  exact not_posDef_of_subset_of_stall kFourDirection point.mass point.weight
    point.mass_pos point.weight_pos hpd hstall
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩) hwin

/-! ## 7.  A blind subset forces a spread bound -/

/-- **THE BLIND SUBSET CARRIES NOTHING.**  A subset of the selection whose
directions all miss a probe contributes zero to that probe's reading, so the
whole selected reading falls on the remaining labels. -/
theorem blindSubset_reading_eq {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {selected blind : Finset (Fin size)} (hsub : blind ⊆ selected)
    (probe : Fin 3 → ℝ)
    (hblind : ∀ label ∈ blind, direction label ⬝ᵥ probe = 0) :
    ∑ label ∈ selected, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
      = ∑ label ∈ selected \ blind,
          mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 := by
  classical
  rw [← Finset.sum_sdiff hsub]
  have hzero : ∑ label ∈ blind,
      mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 = 0 :=
    Finset.sum_eq_zero fun label hmem => by rw [hblind label hmem]; ring
  rw [hzero, add_zero]

/-- **THE SPREAD BOUND.**  A strictly dominating selection that carries a blind
subset must beat the WHOLE mass reading using only its non-blind labels.  The
blind labels are dead weight in that probe's direction, so the burden concentrates.

This is stratum free and generic in the ambient size.  At `K4` the blind subset is
a triangle and the surviving label is the single non-triangle edge. -/
theorem blindSubset_spread_bound {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {selected blind : Finset (Fin size)} (hsub : blind ⊆ selected)
    (probe : Fin 3 → ℝ) (hne : probe ≠ 0)
    (hblind : ∀ label ∈ blind, direction label ⬝ᵥ probe = 0)
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2
      < ∑ label ∈ selected \ blind,
          mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 := by
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hne
  rw [star_trivial, dotProduct_directionChartGap_mulVec_eq,
    blindSubset_reading_eq direction mass weight hsub probe hblind] at hform
  linarith

/-- **THE TRIANGLE SPREAD AT `K4`.**  A strictly dominating four-edge selection
built on the triangle `{0,1,2}` prices its single ground edge against the whole
ground star: the conductance of that edge exceeds the total mass of the three
edges at the ground vertex.

The probe is the triangle's own normal `(1,1,1)`, which every triangle edge
misses and every ground edge reads as a unit.  Measured at 33592 strictly
dominating triangle selections with zero violations, and the control that
replaces the conductance by the plain mass breaks at 19 percent. -/
theorem kFourTriangleSelection_spread (point : DirectionChartPoint 6)
    {g : Fin 6} (hg : g = 3 ∨ g = 4 ∨ g = 5)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      (insert g {0, 1, 2})).PosDef) :
    point.mass 3 + point.mass 4 + point.mass 5
      < point.mass g / point.weight g := by
  have hsub : ({0, 1, 2} : Finset (Fin 6)) ⊆ insert g {0, 1, 2} :=
    Finset.subset_insert _ _
  have hne : (![1, 1, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp at this
  have hblind : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      kFourDirection label ⬝ᵥ (![1, 1, 1] : Fin 3 → ℝ) = 0 := by
    intro label hmem
    fin_cases hmem <;> simp [kFourDirection, dotProduct, Fin.sum_univ_three]
  have hbound := blindSubset_spread_bound kFourDirection point.mass point.weight
    hsub _ hne hblind hpd
  have hdiff : (insert g {0, 1, 2} : Finset (Fin 6)) \ {0, 1, 2} = {g} := by
    rcases hg with rfl | rfl | rfl <;> decide
  rw [hdiff] at hbound
  rw [Finset.sum_singleton] at hbound
  have htotal : ∑ label, point.mass label
      * (kFourDirection label ⬝ᵥ (![1, 1, 1] : Fin 3 → ℝ)) ^ 2
      = point.mass 3 + point.mass 4 + point.mass 5 := by
    rw [Fin.sum_univ_six]
    simp [kFourDirection, dotProduct, Fin.sum_univ_three]
  rw [htotal] at hbound
  have hgread : (kFourDirection g ⬝ᵥ (![1, 1, 1] : Fin 3 → ℝ)) ^ 2 = 1 := by
    rcases hg with rfl | rfl | rfl <;>
      simp [kFourDirection, dotProduct, Fin.sum_univ_three]
  rw [hgread, mul_one] at hbound
  exact hbound

/-! ## 8.  The blind law at the DESIGN level, and the on-path classes

Sections 6 and 7 read a blind subset inside a CHART selection.  The same reading
works verbatim on a design, and there it constrains every on-path class at once.

A LINE of the residual patterns is a coplanar triple of atoms, so it is a blind
set with the line normal as probe.  A design with no line still has a blind PAIR
for every pair of atoms, namely the normal of the plane they span.  So the law
below applies at `U(3,6)`, at the one-line class, at the two-meeting-lines class,
at the three-lines class and at the graphic class, with no pattern hypothesis. -/

/-- The design reading of a selection at a probe drops its blind labels. -/
theorem blindSubset_design_reading {size rank : ℕ} (design : WeightedDesign size rank)
    {selected blind : Finset (Fin size)} (hsub : blind ⊆ selected)
    (probe : Fin rank → ℝ)
    (hblind : ∀ label ∈ blind, design.atom label ⬝ᵥ probe = 0) :
    probe ⬝ᵥ (subsetSum design selected *ᵥ probe)
      = ∑ label ∈ selected \ blind, (design.atom label ⬝ᵥ probe) ^ 2 := by
  classical
  have hreading : probe ⬝ᵥ (subsetSum design selected *ᵥ probe)
      = ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2 := by
    rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun label _ => dotProduct_atomMatrix_mulVec _ _
  rw [hreading, ← Finset.sum_sdiff hsub]
  have hzero : ∑ label ∈ blind, (design.atom label ⬝ᵥ probe) ^ 2 = 0 :=
    Finset.sum_eq_zero fun label hmem => by rw [hblind label hmem]; ring
  rw [hzero, add_zero]

/-- **THE BLIND LAW ON DESIGNS.**  A dominating selection carrying a blind subset
must overcover the probe with its NON-BLIND labels alone.  The blind labels are
dead weight in that direction. -/
theorem blindSubset_dominates_overcovers {size rank : ℕ}
    (design : WeightedDesign size rank)
    {selected blind : Finset (Fin size)} (hsub : blind ⊆ selected)
    (probe : Fin rank → ℝ)
    (hblind : ∀ label ∈ blind, design.atom label ⬝ᵥ probe = 0)
    (hdom : Dominates design selected) :
    probe ⬝ᵥ probe
      ≤ ∑ label ∈ selected \ blind, (design.atom label ⬝ᵥ probe) ^ 2 := by
  have hread := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdom).2 probe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    blindSubset_design_reading design hsub probe hblind] at hread
  linarith

/-- **A DOMINATING SELECTION IS NEVER FULLY BLIND.**  The design-level companion
of the chart blind-probe law, with no cardinality bound and no pattern. -/
theorem not_dominates_of_fully_blind {size rank : ℕ}
    (design : WeightedDesign size rank) {selected : Finset (Fin size)}
    (probe : Fin rank → ℝ) (hne : probe ≠ 0)
    (hblind : ∀ label ∈ selected, design.atom label ⬝ᵥ probe = 0) :
    ¬ Dominates design selected := by
  intro hdom
  have hbound := blindSubset_dominates_overcovers design (Finset.Subset.refl selected)
    probe hblind hdom
  rw [Finset.sdiff_self] at hbound
  simp only [Finset.sum_empty] at hbound
  exact absurd hbound (not_le.mpr (dotProduct_self_pos hne))

/-- **THE SURVIVING LABEL CARRIES THE WHOLE NORMAL.**  If a dominating selection
is blind to a probe at every label but one, that single label must overcover the
probe by itself.

At the one-line and two-meeting-lines classes the probe is a line normal and the
blind set is two line atoms, so a dominating triple that keeps two atoms of a
line forces its third atom past the normal.  At the line-free class every PAIR of
atoms spans a plane, so the law reads: in every dominating triple, the third atom
sticks out of the plane of the other two by more than unit length. -/
theorem single_survivor_overcovers {size rank : ℕ}
    (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} {survivor : Fin size}
    (hmem : survivor ∈ selected)
    (probe : Fin rank → ℝ)
    (hblind : ∀ label ∈ selected, label ≠ survivor →
      design.atom label ⬝ᵥ probe = 0)
    (hdom : Dominates design selected) :
    probe ⬝ᵥ probe ≤ (design.atom survivor ⬝ᵥ probe) ^ 2 := by
  classical
  have hsub : selected.erase survivor ⊆ selected := Finset.erase_subset _ _
  have hblindErase : ∀ label ∈ selected.erase survivor,
      design.atom label ⬝ᵥ probe = 0 := by
    intro label hlab
    exact hblind label (Finset.mem_of_mem_erase hlab)
      (Finset.ne_of_mem_erase hlab)
  have hbound := blindSubset_dominates_overcovers design hsub probe hblindErase hdom
  have hdiff : selected \ selected.erase survivor = {survivor} := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_sdiff, Finset.mem_erase] at hx
      rw [Finset.mem_singleton]
      by_contra hxne
      exact hx.2 ⟨hxne, hx.1⟩
    · intro hx
      rw [Finset.mem_singleton] at hx
      subst hx
      rw [Finset.mem_sdiff, Finset.mem_erase]
      exact ⟨hmem, fun hcon => hcon.1 rfl⟩
  rw [hdiff, Finset.sum_singleton] at hbound
  exact hbound

/-- **THE LINE LAW.**  A dominating selection never contains a whole coplanar
triple.  This is the pattern-generic obstruction the residual line classes use:
a strict dominator must avoid each line, so at the one-line pattern it is one of
the nineteen basis triples. -/
theorem not_dominates_of_coplanar_triple {size rank : ℕ}
    (design : WeightedDesign size rank) {selected line : Finset (Fin size)}
    (hsub : line ⊆ selected) (hcard : selected.card ≤ line.card)
    (probe : Fin rank → ℝ) (hne : probe ≠ 0)
    (hblind : ∀ label ∈ line, design.atom label ⬝ᵥ probe = 0) :
    ¬ Dominates design selected := by
  have heq : line = selected := Finset.eq_of_subset_of_card_le hsub hcard
  subst heq
  exact not_dominates_of_fully_blind design probe hne hblind

end Gtz
