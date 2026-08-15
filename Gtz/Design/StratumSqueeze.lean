import Gtz.Design.ChartDesignWhitening
import Gtz.Ties.ComplementJawWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The stratum squeeze

The whitening weld consumes a global strict selection, and the global
statement is false: the sharp extremal design has thirteen ties and no strict
triple.  This module lands the dischargeable form and the squeeze layer.

* `KFourFamilySelection` — the family form of the selection hypothesis: strict
  selection for every design that realizes a chart point through the
  whitening equivalence.
* `kFourKnifeBandRefinedTenthHeavy_of_familySelection` — the corrected weld:
  the family form alone discharges the committed A3 axiom.
* `kFourTree_compl_triangle_iff_star` — the complement dichotomy: a spanning
  tree has a triangle complement exactly when it is a vertex star.  The other
  twelve trees have spanning-tree complements.
* `kFourStar_compl_gap_not_posDef` — the star obstruction: the complement of
  a star is never strict on the chart.  The complement jaw cannot fire at a
  star, and this is the structural cause of the star exceptions in the atlas
  data.
* `one_le_squeeze_budget_of_noStrict` — the squeeze producer: at a design
  with no strict triple, every subset with a three-slot complement pays the
  jaw budget `1 <= tin * kappa + tout`.  No tie hypothesis is read.
* `exists_heavy_of_noStrict_of_floor` — the carrier law: a weighted energy
  floor on a non-strict subset forces a weight at least the floor inside the
  subset.
-/

namespace Gtz

open Matrix

/-! ## The family selection and the corrected weld -/

/-- **The family selection.**  Strict selection quantified over the whitened
family only: every design that realizes a chart point through the whitening
equivalence has a strict three-slot subset.  The global form of this
hypothesis is false at the sharp extremal design, and the family form is the
dischargeable one. -/
def KFourFamilySelection : Prop :=
  ∀ point : DirectionChartPoint 6, ∀ D : WeightedDesign 6 3,
    D.weight = point.weight →
    (∀ C : Finset (Fin 6),
      ((subsetSum D C - 1).PosDef
        ↔ (directionChartGap kFourDirection point.mass point.weight C).PosDef)) →
    ∃ C : Finset (Fin 6), C.card = 3 ∧ (subsetSum D C - 1).PosDef

/-- The global selection implies the family selection. -/
theorem kFourFamilySelection_of_designSelection
    (hsel : ∀ D : WeightedDesign 6 3, ∃ C : Finset (Fin 6),
      C.card = 3 ∧ (subsetSum D C - 1).PosDef) :
    KFourFamilySelection :=
  fun _ D _ _ => hsel D

/-- The family selection hands every chart point a strict spanning tree. -/
theorem kFourStrictTree_of_familySelection (hsel : KFourFamilySelection)
    (point : DirectionChartPoint 6) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨D, hweight, hiff⟩ := exists_kFourWhitenedDesign point
  obtain ⟨C, hcard, hpd⟩ := hsel point D hweight hiff
  have hchart := (hiff C).mp hpd
  refine ⟨C, mem_kFourSpanningTreeList_of_card_three C hcard ?_, hchart⟩
  intro htriangle
  exact kFourTriangle_gap_not_posDef point C htriangle hchart

/-- **The corrected weld.**  The family selection discharges the committed A3
axiom.  This is the dischargeable joint: its hypothesis quantifies over the
whitened family only, which the sharp extremal design does not inhabit. -/
theorem kFourKnifeBandRefinedTenthHeavy_of_familySelection
    (hsel : KFourFamilySelection) :
    KFourKnifeBandRefinedTenthHeavyWeakToStrict :=
  kFourKnifeBandRefinedTenthHeavy_of_strictTree
    (kFourStrictTree_of_familySelection hsel)

/-! ## The complement dichotomy -/

/-- The four vertex stars of K4 in the edge labeling of the chart. -/
def kFourStarList : List (Finset (Fin 6)) :=
  [{0, 1, 3}, {0, 2, 4}, {1, 2, 5}, {3, 4, 5}]

/-- Every star is a spanning tree. -/
theorem kFourStarList_subset_treeList :
    ∀ S ∈ kFourStarList, S ∈ kFourSpanningTreeList := by decide

/-- **The complement dichotomy.**  A spanning tree has a triangle complement
exactly when it is a vertex star. -/
theorem kFourTree_compl_triangle_iff_star :
    ∀ T ∈ kFourSpanningTreeList,
      ((Tᶜ = {0, 1, 2} ∨ Tᶜ = {0, 3, 4} ∨ Tᶜ = {1, 3, 5} ∨ Tᶜ = {2, 4, 5})
        ↔ T ∈ kFourStarList) := by decide

/-- The complement of a non-star spanning tree is a spanning tree. -/
theorem kFourTree_compl_tree_of_not_star :
    ∀ T ∈ kFourSpanningTreeList, T ∉ kFourStarList
      → Tᶜ ∈ kFourSpanningTreeList := by decide

/-- The complement of a star is its opposite triangle. -/
theorem kFourStar_compl_triangle :
    ∀ S ∈ kFourStarList,
      (Sᶜ = {0, 1, 2} ∨ Sᶜ = {0, 3, 4} ∨ Sᶜ = {1, 3, 5} ∨ Sᶜ = {2, 4, 5}) := by
  decide

/-- **The star obstruction.**  The complement of a vertex star is never
strict on the chart.  The complement jaw cannot fire at a star: this is the
structural cause of the star exceptions in every atlas corpus. -/
theorem kFourStar_compl_gap_not_posDef (point : DirectionChartPoint 6)
    (S : Finset (Fin 6)) (hS : S ∈ kFourStarList) :
    ¬ (directionChartGap kFourDirection point.mass point.weight Sᶜ).PosDef :=
  kFourTriangle_gap_not_posDef point Sᶜ (kFourStar_compl_triangle S hS)

/-- The star obstruction transfers to every realizing design: the complement
of a star is never a strict subset of the whitened design. -/
theorem whitenedDesign_star_compl_not_posDef (point : DirectionChartPoint 6)
    (D : WeightedDesign 6 3)
    (hiff : ∀ C : Finset (Fin 6),
      ((subsetSum D C - 1).PosDef
        ↔ (directionChartGap kFourDirection point.mass point.weight C).PosDef))
    (S : Finset (Fin 6)) (hS : S ∈ kFourStarList) :
    ¬ (subsetSum D Sᶜ - 1).PosDef := by
  intro hpd
  exact kFourStar_compl_gap_not_posDef point S hS ((hiff Sᶜ).mp hpd)

/-! ## The squeeze producers -/

variable {m k : ℕ}

/-- **The squeeze budget.**  At a design with no strict three-slot subset,
every slot set `T` with a three-slot complement pays the jaw budget: a
quadratic cap `kappa` on the atoms of `T`, a weight bound `tin` on `T`, and a
weight bound `tout` off `T` obey `1 <= tin * kappa + tout`.  No tie
hypothesis is read: only the absence of strict subsets. -/
theorem one_le_squeeze_budget_of_noStrict (D : WeightedDesign 6 3)
    (hns : ∀ C : Finset (Fin 6), C.card = 3 → ¬ (subsetSum D C - 1).PosDef)
    (T : Finset (Fin 6)) (hcompl : Tᶜ.card = 3)
    (tin tout kappa : ℝ) (htoutPos : 0 < tout) (htinNonneg : 0 ≤ tin)
    (hinW : ∀ label ∈ T, D.weight label ≤ tin)
    (houtW : ∀ label ∈ Tᶜ, D.weight label ≤ tout)
    (hcap : ∀ probe : Fin 3 → ℝ,
      ∑ label ∈ T, (D.atom label ⬝ᵥ probe) ^ 2 ≤ kappa * (probe ⬝ᵥ probe)) :
    1 ≤ tin * kappa + tout := by
  by_contra hcon
  push Not at hcon
  refine hns Tᶜ hcompl
    (posDef_subsetSum_of_offside_quadCap D Tᶜ tin tout kappa htoutPos htinNonneg
      ?_ houtW ?_ hcon)
  · intro label hmem
    rw [compl_compl] at hmem
    exact hinW label hmem
  · intro probe
    rw [compl_compl]
    exact hcap probe

/-- The squeeze budget at a three-slot set: a card-three `T` has a card-three
complement, so the budget applies to the twenty triples directly. -/
theorem one_le_squeeze_budget_of_noStrict_card (D : WeightedDesign 6 3)
    (hns : ∀ C : Finset (Fin 6), C.card = 3 → ¬ (subsetSum D C - 1).PosDef)
    (T : Finset (Fin 6)) (hcard : T.card = 3)
    (tin tout kappa : ℝ) (htoutPos : 0 < tout) (htinNonneg : 0 ≤ tin)
    (hinW : ∀ label ∈ T, D.weight label ≤ tin)
    (houtW : ∀ label ∈ Tᶜ, D.weight label ≤ tout)
    (hcap : ∀ probe : Fin 3 → ℝ,
      ∑ label ∈ T, (D.atom label ⬝ᵥ probe) ^ 2 ≤ kappa * (probe ⬝ᵥ probe)) :
    1 ≤ tin * kappa + tout :=
  one_le_squeeze_budget_of_noStrict D hns T
    (card_compl_three_of_card_three T hcard) tin tout kappa htoutPos htinNonneg
    hinW houtW hcap

/-- **The carrier law.**  A weighted energy floor on a subset that is not
strict forces a weight at least the floor inside the subset.  This is the
contrapositive of the landed weld rivet, packaged as a producer. -/
theorem exists_heavy_of_noStrict_of_floor (D : WeightedDesign m k)
    (C : Finset (Fin m)) (hne : C.Nonempty) (floor : ℝ)
    (hfloor : ∀ probe : Fin k → ℝ, floor * (probe ⬝ᵥ probe)
      ≤ ∑ label ∈ C, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2)
    (hns : ¬ (subsetSum D C - 1).PosDef) :
    ∃ label ∈ C, floor ≤ D.weight label := by
  by_contra hcon
  push Not at hcon
  set tmax : ℝ := C.sup' hne D.weight with htmax
  obtain ⟨label0, hmem0⟩ := hne
  have htmaxPos : 0 < tmax :=
    lt_of_lt_of_le (D.weight_pos label0) (Finset.le_sup' D.weight hmem0)
  have hbound : ∀ label ∈ C, D.weight label ≤ tmax :=
    fun label hmem => Finset.le_sup' D.weight hmem
  have hlt : tmax < floor := by
    rw [htmax, Finset.sup'_lt_iff]
    exact fun label hmem => hcon label hmem
  exact hns (posDef_subsetSum_of_floor_gt_weights D C floor tmax htmaxPos
    hbound hlt hfloor)

/-- The carrier law at a three-slot subset. -/
theorem exists_heavy_of_noStrict_of_floor_card (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) (hcard : C.card = 3) (floor : ℝ)
    (hfloor : ∀ probe : Fin 3 → ℝ, floor * (probe ⬝ᵥ probe)
      ≤ ∑ label ∈ C, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2)
    (hns : ¬ (subsetSum D C - 1).PosDef) :
    ∃ label ∈ C, floor ≤ D.weight label :=
  exists_heavy_of_noStrict_of_floor D C
    (Finset.card_pos.mp (by rw [hcard]; norm_num)) floor hfloor hns

end Gtz
